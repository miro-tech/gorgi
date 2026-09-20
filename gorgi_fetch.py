#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gorgi_fetch.py — один самодостаточный скрипт: сам забирает ВСЕ конфиги Gorgi VPN и расшифровывает их.

Внешних зависимостей НЕТ — только стандартная библиотека Python 3 (3.7+).

Что делает:
  1) находит API-хосты (список приложения на GitHub + встроенные фоллбэки);
  2) тянет /api/app_config и /api/v2/configs?t=main|spl;
  3) расшифровывает ответы: base64 -> AES-128-CBC -> PKCS#7 (ключ/IV добыты из APK 5.0.9);
  4) расшифровывает ID: base64url -> AES-128-CBC -> PKCS#7 -> UUID;
  5) пишет готовые JSON-конфиги и ссылки vless:// в каталог --out.

Использование:
    python3 gorgi_fetch.py --out gorgi_ready
    python3 gorgi_fetch.py --out gorgi_ready --test /path/to/xray      # ещё и проверить туннели
    python3 gorgi_fetch.py --out gorgi_ready --token <токен>           # если токен сменится

Откуда ключи (APK gorgivpn.gorgvpn.vpn 5.0.9):
  * ID:   key=4ff85d6b4af0be315cc51ecacc3424f1 iv=52934f280b7476d1869a91fe4dfa89b2
          (патч оператора в libgojni.so: modifyWithIDs -> d() -> base64url/AES-CBC/PKCS#7)
  * API:  key=e35588dbac4c5f88d83bfe0b4e938f55 iv=de52a535485dee99f66dec7d6a994d2d
          (lib2tun.so, функция c())
  Серверный app_config это подтверждает: force_id_encryption = true.
"""

import argparse
import base64
import json
import os
import re
import subprocess
import sys
import time
import urllib.parse
import urllib.request

# --------------------------------------------------------------------------- AES-128 (чистый Python)

def _build_tables():
    """Генерируем S-box, обратный S-box и Rcon математически (без таблиц-констант)."""
    def gmul(a, b):
        p = 0
        for _ in range(8):
            if b & 1:
                p ^= a
            hi = a & 0x80
            a = (a << 1) & 0xFF
            if hi:
                a ^= 0x1B
            b >>= 1
        return p

    def inverse(x):
        if x == 0:
            return 0
        for y in range(1, 256):          # мультипликативный обратный в GF(2^8)
            if gmul(x, y) == 1:
                return y
        return 0

    def rotl8(x, n):
        return ((x << n) | (x >> (8 - n))) & 0xFF

    sbox = [0] * 256
    for x in range(256):
        b = inverse(x)
        sbox[x] = b ^ rotl8(b, 1) ^ rotl8(b, 2) ^ rotl8(b, 3) ^ rotl8(b, 4) ^ 0x63
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    rcon = [0] * 11
    rcon[1] = 1
    for i in range(2, 11):
        rcon[i] = gmul(rcon[i - 1], 2)
    return sbox, inv, rcon, gmul


SBOX, ISBOX, RCON, GMUL = _build_tables()


class AES128:
    """AES-128: расширение ключа + дешифровка блока (для режима CBC)."""

    def __init__(self, key):
        if len(key) != 16:
            raise ValueError("нужен ключ 16 байт")
        self.rk = self._expand(key)

    @staticmethod
    def _expand(key):
        w = [list(key[4 * i:4 * i + 4]) for i in range(4)]
        for i in range(4, 44):
            t = list(w[i - 1])
            if i % 4 == 0:
                t = t[1:] + t[:1]                       # RotWord
                t = [SBOX[b] for b in t]                # SubWord
                t[0] ^= RCON[i // 4]
            w.append([w[i - 4][j] ^ t[j] for j in range(4)])
        return w

    def decrypt_block(self, block):
        s = list(block)
        self._add_round_key(s, 10)
        for r in range(9, 0, -1):
            s = self._inv_shift_rows(s)
            s = [ISBOX[b] for b in s]
            self._add_round_key(s, r)
            s = self._inv_mix_columns(s)
        s = self._inv_shift_rows(s)
        s = [ISBOX[b] for b in s]
        self._add_round_key(s, 0)
        return bytes(s)

    def _add_round_key(self, s, r):
        for c in range(4):
            word = self.rk[4 * r + c]
            for j in range(4):
                s[4 * c + j] ^= word[j]

    @staticmethod
    def _inv_shift_rows(s):
        o = [0] * 16
        for c in range(4):
            for r in range(4):
                o[4 * c + r] = s[4 * ((c - r) % 4) + r]
        return o

    @staticmethod
    def _inv_mix_columns(s):
        o = [0] * 16
        for c in range(4):
            a = s[4 * c:4 * c + 4]
            o[4 * c + 0] = GMUL(a[0], 14) ^ GMUL(a[1], 11) ^ GMUL(a[2], 13) ^ GMUL(a[3], 9)
            o[4 * c + 1] = GMUL(a[0], 9) ^ GMUL(a[1], 14) ^ GMUL(a[2], 11) ^ GMUL(a[3], 13)
            o[4 * c + 2] = GMUL(a[0], 13) ^ GMUL(a[1], 9) ^ GMUL(a[2], 14) ^ GMUL(a[3], 11)
            o[4 * c + 3] = GMUL(a[0], 11) ^ GMUL(a[1], 13) ^ GMUL(a[2], 9) ^ GMUL(a[3], 14)
        return o


def aes_cbc_decrypt(data, key, iv):
    if len(data) % 16:
        raise ValueError("длина шифртекста не кратна 16")
    c = AES128(key)
    out = bytearray()
    prev = iv
    for i in range(0, len(data), 16):
        blk = data[i:i + 16]
        dec = c.decrypt_block(blk)
        out += bytes(a ^ b for a, b in zip(dec, prev))
        prev = blk
    return bytes(out)


def pkcs7_unpad(data):
    if not data:
        raise ValueError("пустые данные")
    n = data[-1]
    if not (1 <= n <= 16) or data[-n:] != bytes([n]) * n:
        raise ValueError("неверный PKCS#7 padding")
    return data[:-n]


# --------------------------------------------------------------------------- ключи

API_KEY = bytes.fromhex("e35588dbac4c5f88d83bfe0b4e938f55")   # ответы API
API_IV = bytes.fromhex("de52a535485dee99f66dec7d6a994d2d")
ID_KEY = bytes.fromhex("4ff85d6b4af0be315cc51ecacc3424f1")    # id в конфигах
ID_IV = bytes.fromhex("52934f280b7476d1869a91fe4dfa89b2")
TOKEN = "7bb5ba0a0494cfdd6cf6c45965b2b32a"
FALLBACK_HOSTS = ["https://deeproid.org/api/", "https://sportlandglobal.com/api/",
                  "https://fitroid.website/api/"]
LIST_REPO = "https://raw.githubusercontent.com/hfkskxjfjeiccjjejffjf/thisistestrepo/main/"
UUID_RE = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$")


def api_decrypt(body):
    """base64 -> AES-128-CBC -> PKCS#7 -> текст"""
    blob = base64.b64decode(body.strip().strip(b'"'))
    return pkcs7_unpad(aes_cbc_decrypt(blob, API_KEY, API_IV)).decode("utf-8", "replace")


def decrypt_id(enc):
    """base64url -> AES-128-CBC -> PKCS#7 -> UUID"""
    raw = base64.urlsafe_b64decode(enc + "=" * (-len(enc) % 4))
    return pkcs7_unpad(aes_cbc_decrypt(raw, ID_KEY, ID_IV)).decode()


def fix_ids(text):
    """Заменяет все зашифрованные id (и в ссылках, и в JSON) на UUID."""
    pats = set(re.findall(r"vless://([^@]+)@", text)) | set(re.findall(r'"id"\s*:\s*"([^"]+)"', text))
    for enc in sorted(pats, key=len, reverse=True):
        if UUID_RE.match(enc):
            continue
        try:
            uuid = decrypt_id(enc)
        except Exception:
            continue
        if UUID_RE.match(uuid):
            text = text.replace(enc, uuid)
    return text


# --------------------------------------------------------------------------- сеть

def http(url, token, timeout=25):
    req = urllib.request.Request(url, headers={
        "Authorization": token, "User-Agent": "okhttp/4.9.3", "Accept": "*/*"})
    return urllib.request.urlopen(req, timeout=timeout).read()


def discover_hosts(token):
    hosts = []
    for fn in ("m", "b", "k"):
        try:
            txt = http(LIST_REPO + fn, token, timeout=15).decode("utf-8", "replace").strip()
            try:
                txt = base64.b64decode(txt + "=" * (-len(txt) % 4)).decode("utf-8", "replace")
            except Exception:
                pass
            for u in re.split(r"[^A-Za-z0-9:/._-]+", txt):
                if u.startswith("http"):
                    u = u.rstrip("/")
                    if not u.endswith("/api"):
                        u += "/api"
                    hosts.append(u + "/")
        except Exception:
            pass
    return list(dict.fromkeys(hosts + FALLBACK_HOSTS))


def test_tunnel(cfg_path, xray, port=10808):
    import tempfile
    c = json.load(open(cfg_path))
    c["log"] = {"loglevel": "warning"}
    ib = [i for i in c.get("inbounds", []) if i.get("protocol") == "socks"]
    if ib:
        ib[0]["port"], ib[0]["listen"] = port, "127.0.0.1"
        c["inbounds"] = [ib[0]]
    else:
        c["inbounds"] = [{"tag": "socks", "port": port, "listen": "127.0.0.1", "protocol": "socks",
                          "settings": {"auth": "noauth", "udp": False}}]
    f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
    json.dump(c, f)
    f.close()
    p = subprocess.Popen([xray, "run", "-c", f.name], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    time.sleep(2.5)
    r = subprocess.run(["curl", "-s", "-o", "/dev/null", "-w", "%{http_code}", "--max-time", "12",
                        "-x", "socks5h://127.0.0.1:%d" % port, "https://www.gstatic.com/generate_204"],
                       capture_output=True, text=True).stdout.strip()
    p.terminate()
    os.unlink(f.name)
    return r or "000"


# --------------------------------------------------------------------------- main

def selftest():
    """Проверка AES по тест-вектору FIPS-197 + расшифровка реальных данных."""
    import binascii
    key = binascii.unhexlify("000102030405060708090a0b0c0d0e0f")
    ct = binascii.unhexlify("69c4e0d86a7b0430d8cdb78070b4c55a")
    pt = AES128(key).decrypt_block(ct)
    ok = pt.hex() == "00112233445566778899aabbccddeeff"
    print("[selftest] AES-128 FIPS-197:", "OK" if ok else "ОШИБКА (%s)" % pt.hex())
    try:
        enc = "i4W3wzAbBAVJ5FtDIhLKtp-B_peE0iDVnQCu_FBxZ2L7OKMzK9ZnIIrGkSQzyfTf"
        uuid = decrypt_id(enc)
        good = uuid == "79b79414-c73d-4389-b4a1-cc38d795e9f4"
        print("[selftest] расшифровка id: %s %s" % (uuid, "OK" if good else "ОШИБКА"))
        ok = ok and good
    except Exception as e:
        print("[selftest] id: не удалось проверить (%s)" % e)
    return ok


def main():
    ap = argparse.ArgumentParser(description="Gorgi VPN: забрать и расшифровать все конфиги (без зависимостей)")
    ap.add_argument("--out", default="gorgi_ready", help="каталог для результатов")
    ap.add_argument("--host", action="append", default=[], help="добавить API-хост")
    ap.add_argument("--token", default=TOKEN, help="токен Authorization")
    ap.add_argument("--vc", default="509")
    ap.add_argument("--vn", default="5.0.9")
    ap.add_argument("--test", default=None, help="путь к xray, чтобы проверить туннели")
    ap.add_argument("--selftest", action="store_true", help="проверить AES и выйти")
    args = ap.parse_args()

    if args.selftest:
        sys.exit(0 if selftest() else 1)

    outdir = os.path.abspath(args.out)
    os.makedirs(os.path.join(outdir, "json"), exist_ok=True)

    hosts = discover_hosts(args.token) + [h if h.endswith("/") else h + "/" for h in args.host]
    hosts = list(dict.fromkeys(hosts))
    print("[*] хостов к опросу: %d" % len(hosts))

    links, jsons, seen = [], [], set()
    for h in hosts:
        try:
            ac = json.loads(api_decrypt(http(h + "app_config?vc=%s&vn=%s" % (args.vc, args.vn), args.token)))
            with open(os.path.join(outdir, "app_config.json"), "w") as f:
                json.dump(ac, f, ensure_ascii=False, indent=1)
            print("[+] %-34s app_config ok (force_id_encryption=%s)" % (h, ac.get("force_id_encryption")))
        except Exception as e:
            print("[-] %-34s app_config: %s" % (h, e))
            continue
        for t in ("main", "spl"):
            try:
                cj = json.loads(api_decrypt(http(h + "v2/configs?vc=%s&vn=%s&t=%s" % (args.vc, args.vn, t), args.token)))
            except Exception as e:
                print("[-] %-34s t=%s: %s" % (h, t, e))
                continue
            n_new = 0
            for c in cj.get("configs", []) or []:
                val = c.get("value")
                if not isinstance(val, str):
                    continue
                val = fix_ids(val).strip()
                if not val or val in seen:
                    continue
                seen.add(val)
                n_new += 1
                if val.startswith("{"):
                    try:
                        j = json.loads(val)
                    except Exception:
                        continue
                    jsons.append(j)
                    safe = re.sub(r"[^A-Za-z0-9_.-]", "_", "%s_%s_%s" % (urllib.parse.urlparse(h).netloc, t, c.get("name") or "cfg"))[:64]
                    with open(os.path.join(outdir, "json", safe + ".json"), "w") as f:
                        json.dump(j, f, ensure_ascii=False, indent=1)
                elif val.startswith("vless://"):
                    links.append(val)
            print("[+] %-34s t=%-4s +%d конфигов" % (h, t, n_new))

    with open(os.path.join(outdir, "links.txt"), "w") as f:
        f.write("\n".join(links) + ("\n" if links else ""))
    print("\n[*] итог: %d JSON-конфигов, %d ссылок vless://" % (len(jsons), len(links)))
    print("[*] всё в %s (json/, links.txt, app_config.json)" % outdir)

    if args.test:
        ok = 0
        working = []
        for p in sorted(os.listdir(os.path.join(outdir, "json"))):
            path = os.path.join(outdir, "json", p)
            try:
                r = test_tunnel(path, args.test)
            except Exception as e:
                r = "err %s" % e
            print("    %-52s %s" % (p[:52], r))
            if r == "204":
                ok += 1
                working.append(p)
        with open(os.path.join(outdir, "working.txt"), "w") as f:
            f.write("\n".join(working) + ("\n" if working else ""))
        print("[*] рабочих: %d из %d -> working.txt" % (ok, len(os.listdir(os.path.join(outdir, "json")))))


if __name__ == "__main__":
    main()
