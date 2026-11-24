#!/usr/bin/env python3
"""Runs inside GitHub Actions.
Records an HLS / MPEG-TS link with ffmpeg -c copy (no quality loss) in ONE continuous stream, cuts it into files at
keyframes every PART_MB megabytes (default 4000 = 4 GB, whatever time that takes) and uploads each finished
file to Gofile while the recording keeps going. Telegram gets the links, the Status / Split / Stop buttons.

Reconnect behaviour:
  * a reader thread + big memory queue keep ffmpeg's pipe empty, so a slow disk/upload never makes the server drop us
  * when ffmpeg has to reconnect, HLS restarts RECON_BACK segments behind live (old data is skipped, nothing is lost)
  * if the server restarts its clock on reconnect, the timestamps are shifted so the video continues smoothly in the
    SAME file. A new file is made only at PART_MB (or the Split button), never because of a reconnect.

  python cliprec.py            record
  python cliprec.py finish     upload anything left over (used by the always() step)"""
import math
import hashlib, os, re, sys, math, json, glob, time, html, queue, signal, shutil, socket, threading, subprocess, urllib.request, urllib.parse, urllib.error
try:
    import fcntl
except ImportError:
    fcntl = None

E = os.environ.get
TOKEN, CHAT = E("TG_TOKEN", ""), E("TG_CHAT", "")
ALSO = [c.strip() for c in (E("TG_ALSO") or "").split(",") if c.strip()]   # extra chats that get a copy of every message (e.g. the owner)
WORKER_URL = (E("WORKER_URL") or "").rstrip("/")   # optional Cloudflare Worker: gives us the link and the Stop/Status/Split presses
WORKER_KEY = E("WORKER_KEY") or ""
TICKET = (E("TICKET") or "").strip()               # the worker keeps the stream link under this ticket, so it never shows on GitHub
REPO, RUN = E("REPO", ""), E("RUN_ID", "local")
URL = E("URL", "")
NAME = re.sub(r"[^\w\-]+", "_", E("NAME") or "ClipByNaim")
MINUTES = float(E("MINUTES") or 0)             # 0 = until Stop
PART_MIN = float(E("PART_MIN") or 0)            # optional: also split every N minutes (0 = off, split by size only)
PART_MAX = min(float(E("PART_MB") or 4000), 5000) * 1e6   # a new file every N MB (4000 = 4 GB): the size of the finished MP4 file
MP4_RATIO = [min(1.0, max(0.8, float(E("MP4_RATIO") or 0.965)))]   # MP4 size / .ts size (a .ts file has about 3.5% more overhead). Measured again after every part.


def ts_limit():
    """.ts bytes at which a file is closed, so that the finished MP4 ends up at PART_MB."""
    return PART_MAX / MP4_RATIO[0]
PARALLEL = int(E("PARALLEL") or 16)             # heavy archive links: this many parallel connections (0 or 1 = off)
LIVE_PAR = E("LIVE_PAR") or "auto"             # live .m3u8: auto = parallel parts only if the normal way would skip some; 1 = always, 0 = never
HEAVY_MB = float(E("HEAVY_MB") or 300)          # a .ts archive at least this big counts as heavy
HEAVY_MIN = float(E("HEAVY_MIN") or 15)         # an .m3u8 archive at least this long (minutes) counts as heavy
BACK = E("BACK_SEGS") or "5"                    # start N segments behind live (safety)
PROXY = (E("PROXY") or "").strip()              # optional: http://user:pass@host:port - the stream is fetched through this proxy (e.g. a Bangladesh IP)


def normalize_proxy(p):
    """Accepts the usual ways a proxy is written: http://user:pass@host:port, socks5://..., host:port, user:pass@host:port,
    host:port:user:pass. Returns an http:// or socks5:// address (ffmpeg and urllib need the scheme)."""
    p = (p or "").strip().strip('"\'')
    if not p:
        return ""
    if "://" not in p:
        parts = p.split(":")
        if "@" not in p and len(parts) == 4 and parts[1].isdigit():          # host:port:user:pass
            p = "http://%s:%s@%s:%s" % (parts[2], parts[3], parts[0], parts[1])
        else:
            p = "http://" + p
    return p


PROXY = normalize_proxy(PROXY)
PROXY_NOTE = ""
PROXY_ORIG = PROXY
MODE = (E("MODE") or "auto").strip().lower()     # auto (finds out itself), live, or archive (a finished file: timeshift / catch-up .ts or .m3u8)
TEST_KILL_MB = float(E("TEST_KILL_MB") or 0)      # test only: cut the first HLS download after N MB to test resuming
ARCHIVE = False
TS_RAW = E("TS_RAW") != "0"                     # direct .ts links: download the bytes ourselves (no ffmpeg start/probe delay on reconnect)
RECON_BACK = E("RECON_BACK") or "12"            # after a reconnect (HLS): start N segments behind, repeated data is skipped
OUT = E("OUT_DIR") or "rec"
MP4_DIR = E("MP4_DIR") or OUT                    # finished .mp4 files (a different disk folder from the .ts files)
FAILED = E("FAILED_DIR") or "rec_failed"
DRY = E("DRY") == "1"                           # test mode: no uploads
TEST_ONCE = E("TEST_ONCE") == "1"               # test mode: do not restart when the input ends
GOFILE_URL = E("GOFILE_URL") or "https://upload.gofile.io/uploadfile"
IDLE_STOP = float(E("IDLE_STOP_MIN") or 10)     # stop the job when the stream sends no data for N minutes (saves GitHub minutes), 0 = off
ASKED = False                                   # True when the link came from Telegram (it is kept out of the GitHub page)
RETRY_BASE = float(E("RETRY_BASE") or 30)       # seconds, grows with every upload retry
GF = {"folder": "", "token": ""}
LIMIT = float(E("LIMIT_MIN") or 345) * 60         # one GitHub job runs ~6 h (345 min); on your own phone/PC set LIMIT_MIN=1440 or more
STAMP = time.strftime("%Y%m%d_%H%M%S")
RUN_URL = "https://github.com/%s/actions/runs/%s" % (REPO, RUN)
DEFAULT_UA = "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36"
UA = E("USER_AGENT") or E("UA") or DEFAULT_UA
REFERER = E("REFERER") or ""
HDR = ["-user_agent", UA]

M33 = 0x1FFFFFFFF                               # 33 bit timestamp mask (90 kHz clock)
JUMP_BACK = 90000                               # clock went back more than 1 s  -> source restarted
JUMP_FWD = 270000                               # clock jumped forward more than 3 s -> close the gap, keep it smooth
DUP_WINDOW = 90000 * 600                        # data up to 10 min older than what we saved counts as "already have it"

stop = threading.Event()
D = {"got": 0, "total": None, "secs": 0.0, "dur": None}   # archive download progress
S = {"proc": None, "t0": time.time(), "restarts": 0, "done": [], "page": "", "last_data": time.time(), "reason": "", "qmax": 0}
upq = queue.Queue()
SP = None


# ---------------- small helpers ----------------
def esc(t):
    return html.escape(str(t), quote=False)


def human(b):
    return "%.2f GB" % (b / 1e9) if b >= 1e9 else "%.0f MB" % (b / 1e6)


def hms(s):
    s = int(max(0, s))
    return "%02d:%02d:%02d" % (s // 3600, s % 3600 // 60, s % 60)


def mmss(s):
    s = int(max(0, s))
    return "%d:%02d:%02d" % (s // 3600, s % 3600 // 60, s % 60) if s >= 3600 else "%d:%02d" % (s // 60, s % 60)


def mask(t):
    t = t or ""
    for u in (URL_FULL, URL):
        if u:
            t = t.replace(u, "<link>")
    for kid, key in DASH_KEYS:
        t = t.replace(key, "<key>")
        if kid:
            t = t.replace(kid, "<kid>")
    for p in (PROXY_ORIG, PROXY):
        if p:
            t = t.replace(p, "<proxy>")
    return t


def fenv():
    """Environment for ffmpeg/ffprobe: only they get the proxy (Telegram and Gofile never go through it)."""
    e = dict(os.environ)
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "no_proxy", "NO_PROXY"):
        e.pop(k, None)
    if PROXY:
        e["http_proxy"] = PROXY; e["https_proxy"] = PROXY
    return e


def start_socks_bridge(upstream):
    """ffmpeg and urllib only speak HTTP proxies. For a socks5:// proxy a tiny local HTTP proxy is started that
    forwards everything to the SOCKS proxy. Returns the local http:// address."""
    import asyncio
    u = urllib.parse.urlparse(upstream)
    uh, up = u.hostname, u.port or 1080
    user, pw = urllib.parse.unquote(u.username or ""), urllib.parse.unquote(u.password or "")
    ready = threading.Event()
    box = {}

    async def socks_connect(thost, tport):
        r, w = await asyncio.open_connection(uh, up)
        w.write(b"\x05\x02\x00\x02" if user else b"\x05\x01\x00")
        resp = await r.readexactly(2)
        if resp[1] == 2:
            ub, pb = user.encode(), pw.encode()
            w.write(b"\x01" + bytes([len(ub)]) + ub + bytes([len(pb)]) + pb)
            if (await r.readexactly(2))[1] != 0:
                raise OSError("the SOCKS proxy refused the user name / password")
        elif resp[1] != 0:
            raise OSError("the SOCKS proxy wants a login method that is not supported")
        hb = thost.encode()
        w.write(b"\x05\x01\x00\x03" + bytes([len(hb)]) + hb + int(tport).to_bytes(2, "big"))
        rep = await r.readexactly(4)
        if rep[1] != 0:
            raise OSError("the SOCKS proxy could not connect (code %d)" % rep[1])
        n = {1: 4, 4: 16}.get(rep[3])
        if n is None:
            n = (await r.readexactly(1))[0]
        await r.readexactly(n + 2)
        return r, w

    async def pipe(r, w):
        try:
            while True:
                d = await r.read(65536)
                if not d:
                    break
                w.write(d)
                await w.drain()
        except Exception:
            pass
        finally:
            try: w.close()
            except Exception: pass

    async def handle(cr, cw):
        try:
            line = await cr.readline()
            method, target, _ver = line.decode("latin1").split()
            hdrs = []
            while True:
                h = await cr.readline()
                if h in (b"\r\n", b"\n", b""):
                    break
                if not h.lower().startswith((b"proxy-connection", b"proxy-authorization")):
                    hdrs.append(h)
            if method.upper() == "CONNECT":
                host, _, port = target.rpartition(":")
                r, w = await socks_connect(host.strip("[]"), int(port or 443))
                cw.write(b"HTTP/1.1 200 Connection established\r\n\r\n")
                await cw.drain()
            else:
                pu = urllib.parse.urlparse(target)
                r, w = await socks_connect(pu.hostname, pu.port or 80)
                path = (pu.path or "/") + ("?" + pu.query if pu.query else "")
                w.write(("%s %s HTTP/1.1\r\n" % (method, path)).encode() + b"".join(hdrs) + b"\r\n")
                await w.drain()
            await asyncio.gather(pipe(cr, w), pipe(r, cw))
        except Exception as e:
            try:
                cw.write(b"HTTP/1.1 502 Bad Gateway\r\n\r\n" + str(e).encode()[:200])
            except Exception:
                pass
        finally:
            try: cw.close()
            except Exception: pass

    def run():
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        srv = loop.run_until_complete(asyncio.start_server(handle, "127.0.0.1", 0))
        box["port"] = srv.sockets[0].getsockname()[1]
        ready.set()
        loop.run_forever()

    threading.Thread(target=run, daemon=True).start()
    ready.wait(10)
    return "http://127.0.0.1:%d" % box["port"]


def setup_proxy():
    global PROXY, PROXY_NOTE
    if PROXY.lower().startswith(("socks5://", "socks5h://", "socks://")):
        up = PROXY
        print("::add-mask::" + up, flush=True)
        PROXY = start_socks_bridge(up.replace("socks5h://", "socks5://").replace("socks://", "socks5://"))
        PROXY_NOTE = "socks"
        print("SOCKS proxy: a local bridge is used (%s)." % PROXY, flush=True)
    elif PROXY.lower().startswith("socks4"):
        print("::warning::socks4 proxies are not supported, use an HTTP or SOCKS5 proxy.", flush=True)


def stream_opener():
    """urllib opener for the stream: through PROXY if set, otherwise direct."""
    return urllib.request.build_opener(urllib.request.ProxyHandler({"http": PROXY, "https": PROXY} if PROXY else {}))


def _origin(u):
    m = re.match(r"^(https?://[^/]+)", u or "")
    return m.group(1) if m else ""


RUN = os.environ.get("GITHUB_RUN_ID", "")     # every run signs its own buttons, so two recordings never get mixed up
_s = ("@" + RUN) if RUN else ""
KB = {"inline_keyboard": [[{"text": "📊 Status", "callback_data": "status" + _s},
                           {"text": "✂️ Split", "callback_data": "split" + _s},
                           {"text": "⏹ Stop", "callback_data": "stop" + _s}]]}


TGB = {}                                            # method -> time until Telegram told us to wait (error 429 "retry after")
PENDING = []                                        # messages that could not be sent while Telegram said wait
_PL = threading.Lock()


def tg_wait_left(method):
    return max(0.0, TGB.get(method, 0) - time.time())


def tg_flood(method, body):
    """Error 429: remember how long Telegram wants us to wait, and stop calling that method until then."""
    try:
        ra = int(json.loads(body).get("parameters", {}).get("retry_after", 30))
    except Exception:
        ra = 30
    if tg_wait_left(method) <= 0:
        print("Telegram says: wait %d s (%.1f h) before %s again. Until then nothing is sent with it; messages are kept and sent later." % (ra, ra / 3600, method), flush=True)
    TGB[method] = time.time() + ra + 1
    return ra


def tg(method, **data):
    if not TOKEN or DRY:
        print("[telegram]", method, re.sub(r"<[^>]+>", "", str(data.get("text", ""))).replace("\n", " | "))
        return {}
    if tg_wait_left(method) > 0:
        return {"ok": False, "error_code": 429, "blocked": True}
    try:
        req = urllib.request.Request("%s/bot%s/%s" % (E("TG_API") or "https://api.telegram.org", TOKEN, method), urllib.parse.urlencode(data).encode())
        return json.load(urllib.request.urlopen(req, timeout=40))
    except urllib.error.HTTPError as e:
        try: body = e.read().decode()[:300]
        except Exception: body = ""
        if e.code == 429:
            tg_flood(method, body)
        else:
            print("Telegram error %s: %s" % (e.code, body[:200]), flush=True)
        return {"ok": False, "error_code": e.code, "description": body}
    except Exception as e:
        print("telegram error:", e)
        return {}


def say(text, buttons=False):
    if not (CHAT or DRY):
        print("[msg]", re.sub(r"<[^>]+>", "", re.sub(r'<a href="([^"]+)">([^<]*)</a>', r"\2 \1", text)))
        return
    for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
        d = dict(chat_id=cid, text=text, parse_mode="HTML", disable_web_page_preview="true")
        if buttons:
            d["reply_markup"] = json.dumps(KB)
        r = tg("sendMessage", **d)
        if r.get("error_code") == 429:                       # Telegram says wait: keep the message and send it when allowed
            with _PL:
                PENDING.append(d)
                del PENDING[:-30]
            start_flusher()


_FL = []


def start_flusher():
    if _FL:
        return
    _FL.append(1)
    threading.Thread(target=lambda: flush_pending(10 ** 9), daemon=True).start()


def flush_pending(max_wait):
    """Send the kept messages as soon as Telegram allows. Waits at most max_wait seconds."""
    end = time.time() + max_wait
    while True:
        with _PL:
            if not PENDING:
                return True
        left = tg_wait_left("sendMessage")
        if left <= 0:
            with _PL:
                d = PENDING.pop(0) if PENDING else None
            if d is not None:
                r = tg("sendMessage", **d)
                if r.get("error_code") == 429:
                    with _PL:
                        PENDING.insert(0, d)
                else:
                    time.sleep(1.2)
            continue
        if time.time() + left > end:
            return False
        time.sleep(min(left, 30))


def detect_chat():
    """If TG_CHAT is empty, use the chat of the latest message sent to the bot (send it 'hi' first)."""
    global CHAT
    if CHAT or not TOKEN or DRY:
        return
    r = tg("getUpdates", timeout=0)
    ids = [((u.get("message") or {}).get("chat") or {}).get("id") for u in r.get("result", [])]
    ids = [i for i in ids if i]
    if ids:
        CHAT = str(ids[-1]); print("Chat detected from the latest message sent to the bot.", flush=True)
    else:
        print("NO CHAT ID: send 'hi' to your bot in Telegram, then run again (within 24 hours).", flush=True)


def summary(text):
    p = E("GITHUB_STEP_SUMMARY")
    if p:
        try:
            with open(p, "a") as f:
                f.write(text + "\n")
        except OSError:
            pass


# ---------------- MPEG-TS splitter (cuts at keyframes, recording never stops) ----------------
def pes_times(pk):
    """(pts, dts) of the PES that starts in this packet; dts falls back to pts."""
    afc = (pk[3] >> 4) & 3
    if not afc & 1:
        return None, None
    p = 4 + ((1 + pk[4]) if afc & 2 else 0)
    if p + 14 > 188 or pk[p] or pk[p + 1] or pk[p + 2] != 1 or not (pk[p + 7] & 0x80):
        return None, None
    def ts(i):
        return ((pk[i] >> 1) & 7) * 1073741824 + ((pk[i + 1] << 22) | ((pk[i + 2] >> 1) << 15) | (pk[i + 3] << 7) | (pk[i + 4] >> 1))
    pts = ts(p + 9)
    dts = ts(p + 14) if (pk[p + 7] & 0x40) and p + 19 <= 188 else pts
    return pts, dts


def sdiff(a, b):
    """a - b on the 33 bit clock, as a signed number."""
    d = (a - b) & M33
    return d - (1 << 33) if d >= (1 << 32) else d


def shift_ts(pk, off):
    """Return a copy of the packet with PTS, DTS and PCR moved by off (90 kHz ticks)."""
    b = bytearray(pk)
    afc = (pk[3] >> 4) & 3
    if afc & 2 and pk[4] >= 7 and pk[5] & 0x10:                     # PCR in the adaptation field
        base = ((pk[6] << 25) | (pk[7] << 17) | (pk[8] << 9) | (pk[9] << 1) | (pk[10] >> 7))
        base = (base + off) & M33
        b[6] = (base >> 25) & 0xFF; b[7] = (base >> 17) & 0xFF; b[8] = (base >> 9) & 0xFF; b[9] = (base >> 1) & 0xFF
        b[10] = ((base & 1) << 7) | (pk[10] & 0x7F)
    if afc & 1 and (pk[1] & 0x40):                                   # PES header with PTS (and DTS)
        p = 4 + ((1 + pk[4]) if afc & 2 else 0)
        if p + 14 <= 188 and not pk[p] and not pk[p + 1] and pk[p + 2] == 1 and (pk[p + 7] & 0x80):
            def put(i):
                v = (((pk[i] >> 1) & 7) * 1073741824 + ((pk[i + 1] << 22) | ((pk[i + 2] >> 1) << 15) | (pk[i + 3] << 7) | (pk[i + 4] >> 1)) + off) & M33
                b[i] = (pk[i] & 0xF0) | (((v >> 30) & 7) << 1) | 1
                b[i + 1] = (v >> 22) & 0xFF
                b[i + 2] = (((v >> 15) & 0x7F) << 1) | 1
                b[i + 3] = (v >> 7) & 0xFF
                b[i + 4] = ((v & 0x7F) << 1) | 1
            put(p + 9)
            if (pk[p + 7] & 0x40) and p + 19 <= 188:
                put(p + 14)
    return b


def vsig(pk):
    """Fingerprint of a video picture: the first bytes of its data (after the PES header)."""
    afc = (pk[3] >> 4) & 3
    p = 4 + ((1 + pk[4]) if afc & 2 else 0)
    st = p + 9 + pk[p + 8]
    return bytes(pk[st:min(st + 24, 188)])


def same_sig(a, b):
    n = min(len(a), len(b) if b else 0)
    return b is not None and n >= 8 and a[:n] == b[:n]


def nal_key(pk, vtype):
    """Many servers do not set the random-access flag. Then look into the first packet of the picture for a keyframe
    marker: H.264 SPS/IDR, HEVC VPS/SPS/IRAP, MPEG-2 sequence header / I picture."""
    p = 4
    if (pk[3] >> 4) & 2:
        p += 1 + pk[4]
    if p + 10 >= 188 or pk[p] != 0 or pk[p + 1] != 0 or pk[p + 2] != 1:
        return False
    d = pk[p + 9 + pk[p + 8]:]
    i = 0
    while True:
        j = d.find(b"\x00\x00\x01", i)
        if j < 0 or j + 4 >= len(d):
            return False
        b = d[j + 3]
        if vtype == 0x1b and (b & 0x1f) in (5, 7):
            return True
        if vtype == 0x24 and ((b >> 1) & 0x3f) in (16, 17, 18, 19, 20, 21, 32, 33):
            return True
        if vtype in (0x02, 0x10) and (b == 0xB3 or (b == 0x00 and ((d[j + 5] >> 3) & 7) == 1)):
            return True
        i = j + 3


class Splitter:
    def __init__(self, on_done):
        self.on_done = on_done
        self.buf = b""
        self.f = None; self.path = ""
        self.part_no = 0; self.cur_bytes = 0; self.total = 0
        self.start_pts = None; self.last_pts = None
        self.pat = None; self.pmt = None; self.pmt_pid = None; self.vid = None
        self.want_split = False; self.manual_flag = False; self.on_manual = None
        self.hist = []
        self.aud = set(); self.cc = {}; self.last_wr = {}
        self.off = 0; self.last_out_v = None; self.fdur = 3600; self.rebased = 0     # timestamp shift so reconnects join smoothly
        self.gap_total = 0.0
        self.skip = None; self.dropping = set(); self.drop_bytes = 0; self.deduped = 0; self.last_write = time.time(); self.last_es = time.time()
        self.need_key = False; self.need_key_until = 0
        self.vtype = None; self.nokey_pes = 0; self.nokey_warned = False
        self.first_pts = None
        self.recent = {}; self.verify = False                # dts -> fingerprint of recently saved pictures

    def new_session(self, dedupe=True, verify=False):
        """ffmpeg was restarted: it re-sends some old data. Drop everything up to the last time we already wrote."""
        self.buf = b""
        marks = {k: v for k, v in self.last_wr.items() if v is not None}
        self.skip = dict(marks) if (marks and dedupe) else None
        self.dropping = set(); self.drop_bytes = 0
        # If we skip repeated data, the new data continues right after what is already saved (same picture group),
        # so no keyframe is needed. Otherwise wait for the next keyframe so there is no broken picture.
        self.verify = self.skip is not None and verify        # TS: the first old picture must really be one we saved (HLS replays many segments, no check)
        self.need_key = self.vid is not None and self.skip is None
        self.need_key_until = time.time() + 20
        print("New connection. Repeated data dropped so far: %.1f MB" % (self.deduped / 1e6), flush=True)

    def _write(self, pk):
        pid = ((pk[1] & 0x1f) << 8) | pk[2]
        b = bytearray(pk)
        if (pk[3] >> 4) & 1:                              # packet has payload: continue the counter without gaps
            c = (self.cc.get(pid, -1) + 1) & 15
            self.cc[pid] = c
        else:
            c = self.cc.get(pid, 0)
        b[3] = (b[3] & 0xF0) | c
        self.f.write(b)
        self.last_write = time.time()

    def media_total(self):
        if self.first_pts is None or self.last_pts is None:
            return 0.0
        return ((self.last_pts - self.first_pts) % (1 << 33)) / 90000.0

    def media_secs(self):
        if self.start_pts is None or self.last_pts is None:
            return 0.0
        return ((self.last_pts - self.start_pts) % (1 << 33)) / 90000.0

    def speed_mbps(self):
        now = time.time()
        self.hist = [h for h in self.hist if now - h[0] <= 12]
        if len(self.hist) < 2:
            return 0.0
        dt = self.hist[-1][0] - self.hist[0][0]
        return (self.hist[-1][1] - self.hist[0][1]) * 8 / dt / 1e6 if dt > 0.5 else 0.0

    def _open(self):
        self.part_no += 1
        self.path = os.path.join(OUT, "%s_%s_part%03d.ts" % (NAME, STAMP, self.part_no))
        self.f = open(self.path, "wb")
        self.wall0 = time.time()                       # when this file started (the live score feed is matched to the video with it)
        self.cur_bytes = 0
        self.start_pts = self.last_pts
        for p in (self.pat, self.pmt):                 # every file starts with PAT + PMT, then a keyframe
            if p:
                self._write(p); self.cur_bytes += 188

    def _close(self):
        if not self.f:
            return
        self.f.close(); self.f = None
        if self.cur_bytes > 188 * 40:
            self.on_done(self.path)
        else:
            try: os.remove(self.path)
            except OSError: pass

    def finish(self):
        self._close()

    def _pat(self, pk):
        self.pat = bytes(pk)
        p = 4 + ((1 + pk[4]) if (pk[3] >> 4) & 2 else 0)
        p += 1 + pk[p]
        sec = ((pk[p + 1] & 15) << 8) | pk[p + 2]
        q, end = p + 8, min(p + 3 + sec - 4, 188)
        while q + 4 <= end:
            if ((pk[q] << 8) | pk[q + 1]) != 0:
                self.pmt_pid = ((pk[q + 2] & 31) << 8) | pk[q + 3]
                break
            q += 4

    def _pmt(self, pk):
        self.pmt = bytes(pk)
        p = 4 + ((1 + pk[4]) if (pk[3] >> 4) & 2 else 0)
        p += 1 + pk[p]
        sec = ((pk[p + 1] & 15) << 8) | pk[p + 2]
        info = ((pk[p + 10] & 15) << 8) | pk[p + 11]
        q, end = p + 12 + info, min(p + 3 + sec - 4, 188)
        while q + 5 <= end:
            if pk[q] in (0x1b, 0x24, 0x02, 0x10) and self.vid is None:
                self.vid = ((pk[q + 1] & 31) << 8) | pk[q + 2]; self.vtype = pk[q]
            elif pk[q] in (0x0f, 0x11, 0x03, 0x04, 0x81, 0x87):
                self.aud.add(((pk[q + 1] & 31) << 8) | pk[q + 2])
            q += 5 + (((pk[q + 3] & 15) << 8) | pk[q + 4])

    def est(self):
        """Size the MP4 of the running file will have."""
        return self.cur_bytes * MP4_RATIO[0]

    def _should_split(self):
        # only: Split button, optional time limit, or the size limit. A reconnect / clock jump never splits a file.
        if self.want_split:
            self.want_split = False; self.manual_flag = True
            return True
        return (PART_MIN > 0 and self.media_secs() >= PART_MIN * 60) or self.cur_bytes >= ts_limit()

    def feed(self, data):
        self.buf += data
        buf = self.buf; n = len(buf); i = 0
        while i < n:                                      # find a start where the sync bytes line up (raw streams can begin mid-packet)
            if buf[i] == 0x47 and all(buf[i + 188 * j] == 0x47 for j in (1, 2) if i + 188 * j < n):
                break
            i += 1
        end = i + ((n - i) // 188) * 188
        for o in range(i, end, 188):
            pk = buf[o:o + 188]
            if pk[0] != 0x47:                             # lost sync: look for it again in the next data
                end = o + 1; break
            pid = ((pk[1] & 0x1f) << 8) | pk[2]
            if pid == 0x1fff or (pk[1] & 0x80):
                continue                                  # drop empty padding packets and damaged packets
            pusi = pk[1] & 0x40
            key = False
            is_es = pid == self.vid or pid in self.aud
            pts, dts = pes_times(pk) if (pusi and is_es) else (None, None)
            if self.skip is not None and is_es:          # after a reconnect: skip data we already have
                if pusi:
                    k = "v" if pid == self.vid else pid
                    last = self.skip.get(k)
                    fresh = False
                    if last is None or dts is None:
                        ahead = True
                    else:
                        d = sdiff(dts, last)
                        ahead = d > 0 or d < -DUP_WINDOW   # newer than what we saved, or the server clock restarted
                        if not ahead and pid == self.vid and self.verify:
                            self.verify = False
                            if not same_sig(vsig(pk), self.recent.get(dts)):
                                fresh = True               # not a picture we saved: new content with a restarted clock
                    if fresh:
                        print("Server restarted its clock with NEW content: nothing is dropped, timeline is joined instead", flush=True)
                        self.skip = None; self.dropping = set()
                        self.need_key = True; self.need_key_until = time.time() + 20
                    elif ahead:
                        if pid == self.vid and last is not None and dts is not None:
                            self.verify = False
                            if not (0 < sdiff(dts, last) <= max(3 * self.fdur, 9000)):
                                self.need_key = True; self.need_key_until = time.time() + 20   # not the very next picture: gap, wait for keyframe
                        self.skip.pop(k, None); self.dropping.discard(pid)
                        if not self.skip:
                            self.skip = None
                    else:
                        self.dropping.add(pid)
                if pid in self.dropping:
                    self.drop_bytes += 188; self.deduped += 188
                    if self.drop_bytes > 400_000_000:     # timestamps do not match: stop skipping, keep recording
                        self.skip = None; self.dropping = set()
                    continue
            if self.need_key and is_es:
                if pid == self.vid and pusi and (((pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40)) or nal_key(pk, self.vtype)):
                    self.need_key = False
                elif time.time() > self.need_key_until:
                    self.need_key = False
                else:
                    continue
            if pid == 0 and pusi:
                self._pat(pk)
                if self.vid is None and self.pmt:
                    key = True                            # audio-only stream: cut at PAT
            elif pid == self.pmt_pid and pusi:
                self._pmt(pk)
            elif pid == self.vid and pusi:
                if pts is not None:
                    lastv = self.last_wr.get("v")
                    if lastv is not None and self.skip is None:
                        dd = sdiff(dts, lastv)
                        if dd < -JUMP_BACK or dd > JUMP_FWD:
                            # the server clock jumped (reconnect / restart): shift all following timestamps so the
                            # picture continues one frame after the last one. Same file, no cut, no freeze.
                            if self.last_out_v is not None:
                                self.off = (self.last_out_v + self.fdur - dts) & M33
                                self.rebased += 1
                                if dd > 0:
                                    self.gap_total += dd / 90000.0
                                print("Clock jump %+.1fs: timeline joined smoothly (join #%d)" % (dd / 90000.0, self.rebased), flush=True)
                        elif 0 < dd <= 18000:
                            self.fdur = dd                # normal picture spacing, used to place the first picture after a join
                    self.last_pts = (pts + self.off) & M33
                    if self.first_pts is None:
                        self.first_pts = self.last_pts
                    self.last_out_v = (dts + self.off) & M33
                    self.last_wr["v"] = dts               # raw value, used to skip repeated data after a reconnect
                    self.recent[dts] = vsig(pk)
                    if len(self.recent) > 3000:
                        del self.recent[next(iter(self.recent))]
                if (pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40):
                    key = True                            # random access indicator = keyframe starts here
                elif nal_key(pk, self.vtype):
                    key = True                            # the server sets no flag: the picture data itself shows a keyframe
                elif self.f is None and self.pat and self.pmt:
                    self.nokey_pes += 1                   # no marker at all for a long time: start at an ordinary picture, never lose the whole recording
                    if self.nokey_pes > 400:
                        key = True
                        if not self.nokey_warned:
                            self.nokey_warned = True
                            print("No keyframe marker found in the stream: the file starts at an ordinary picture", flush=True)
                elif self.f is not None and self.cur_bytes >= ts_limit() + 64_000_000:
                    key = True                            # never a keyframe marker and the file is too big: cut here
            elif pid in self.aud and pusi and dts is not None:
                self.last_wr[pid] = dts
            if self.f is None:
                if (key or (self.vid is None and self.pmt and pid not in (0, self.pmt_pid))) and (self.pat and self.pmt):
                    self._open()
                else:
                    continue
            elif key and self._should_split():
                self._close(); self._open()
                if self.manual_flag:
                    self.manual_flag = False
                    if self.on_manual:
                        self.on_manual(self.part_no)
            if self.off and (pts is not None or ((pk[3] >> 4) & 2 and pk[4] >= 7 and pk[5] & 0x10)):
                pk = shift_ts(pk, self.off)
            self._write(pk); self.cur_bytes += 188
            if is_es:
                self.last_es = time.time()                # real video/audio data was saved (not just PAT/PMT)
        self.total += end - i
        self.buf = buf[end:]
        now = time.time()
        self.hist.append((now, self.total))
        if len(self.hist) > 1500:
            self.hist = [h for h in self.hist if now - h[0] <= 15]


# ---------------- messages ----------------
def status_text():
    """Status button: the same box panel plus time left and the next auto-split."""
    el = time.time() - S["t0"]
    left = max(0, MINUTES * 60 - el) if MINUTES else None
    sp = SP
    spd = sp.speed_mbps() if sp else 0
    extra = []
    if left is not None:
        extra.append("⏳ Limit left <code>%s</code>" % hms(left))
    if sp and sp.f and not ARCHIVE:
        t_left = (PART_MIN * 60 - sp.media_secs()) if PART_MIN > 0 else 1e12
        if spd > 0.1:
            t_left = min(t_left, (PART_MAX - sp.est()) * 8 / (spd * 1e6))
        if t_left < 1e11:
            extra.append("✂️ Next split <code>~%s</code> (at %s)" % (mmss(t_left), human(PART_MAX)))
    if S["reason"] and S["restarts"]:
        extra.append("<code>%s</code>" % esc(S["reason"][:160]))
    lines = live_text(int(time.time() / 3), stop.is_set(), HIST).split("\n")
    lines[-3:-3] = ["│ " + x for x in extra]
    return "\n".join(lines)



SPIN = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"
WAVE = "▁▂▃▄▅▆▇█▇▆▅▄▃▂"
LINE = "━" * 18


def bar(frac, n=20, head=True):
    k = max(0, min(n, int(frac * n)))
    if head and 0 < k < n:
        return "█" * (k - 1) + "▓" + "░" * (n - k)
    return "█" * k + "░" * (n - k)


def spark(vals):
    if not vals:
        return ""
    hi = max(max(vals), 0.1)
    return "".join(WAVE[:8][min(7, int(v / hi * 7.99))] for v in vals)


def clock(t=None):
    return time.strftime("%H:%M:%S", time.gmtime((t or time.time()) + float(E("TZ_HOURS") or 6) * 3600))


NAIM = "ℕ𝕒𝕚𝕞𝕏"
FIRE = ["🔥", "💥", "⚡", "🔥"]


def naim_sig(i):
    """The moving NaimX signature: a cursor runs through the letters, then a short glitch."""
    e = FIRE[i % len(FIRE)]
    return "%s <b>%s</b> %s" % (e, NAIM, e)


def note_box(title, *lines):
    V = "│ "
    return "\n".join([BOX_TOP, V + title + "  ·  <b>%s</b>" % esc(NAME), BOX_MID] + [V + x for x in lines]
                     + [BOX_MID, "%s%s  🕒 %s" % (V, naim_sig(int(time.time())), clock()), BOX_END])


def pbar(frac, n=20):
    return bar(frac, n)


BOX_TOP = "╭" + "─" * 22 + "╮"
BOX_MID = "├" + "─" * 22 + "┤"
BOX_END = "╰" + "─" * 22 + "╯"


def live_text(i, ended=False, hist=()):
    """Box style text panel, edited every few seconds (used when pictures are off or cannot be drawn)."""
    el = time.time() - S["t0"]
    sp = SP
    spd = sp.speed_mbps() if sp else 0
    saved = sum(d["size"] for d in S["done"])
    dot = "🔴" if i % 2 == 0 else "⭕"
    if ended:
        title = "✅ <b>𝗙𝗜𝗡𝗜𝗦𝗛𝗘𝗗</b>"
    elif ARCHIVE:
        title = "⬇️ <b>𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗</b> %s" % SPIN[i % len(SPIN)]
    else:
        title = "%s <b>𝗟𝗜𝗩𝗘 𝗥𝗘𝗖</b> %s" % (dot, SPIN[i % len(SPIN)])
    V = "│ "
    L = [BOX_TOP, "%s%s  ·  <b>%s</b>" % (V, title, esc(NAME)), BOX_MID]
    if ARCHIVE:
        frac, eta, txt = None, None, ""
        if KIND == "ts" and D["total"]:
            frac = D["got"] / max(1, D["total"])
            txt = "%s / %s" % (human(D["got"]), human(D["total"]))
            if spd > 0.1:
                eta = (D["total"] - D["got"]) * 8 / (spd * 1e6)
        elif D["dur"]:
            frac = D["secs"] / max(1, D["dur"])
            txt = "%s done · %s left" % (mmss(D["secs"]), mmss(max(0, D["dur"] - D["secs"])))
            if D["secs"] > 5:
                eta = (D["dur"] - D["secs"]) * el / D["secs"]
        if frac is not None:
            frac = min(1.0, frac)
            L.append("%s⬇️ Download  <code>%s</code> <b>%d%%</b>" % (V, pbar(frac), int(frac * 100)))
            L.append("%s💾 Done      <code>%s</code>" % (V, txt))
            if eta and not ended:
                L.append("%s⏳ Left      <code>~%s</code> · ends <b>%s</b>" % (V, hms(eta), clock(time.time() + eta)))
    elif sp:
        f = min(1.0, sp.est() / PART_MAX) if PART_MAX else 0
        tot = sum(x.get("secs", 0) for x in S["done"]) + sp.media_secs()
        L += ["%s📁 File %02d    <code>%s</code> <b>%d%%</b>" % (V, sp.part_no, pbar(f), int(f * 100)),
              "%s💾 Size       <code>%s / %s</code>" % (V, human(sp.est()), human(PART_MAX)),
              "%s🎞 Video      <code>%s</code> (total <code>%s</code>)" % (V, mmss(sp.media_secs()), hms(tot))]
    L.append("%s⚡ Speed      <code>%.1f Mbps</code>" % (V, spd))
    if hist and not ended:
        L.append("%s<code>%s</code>" % (V, spark(hist)))
    L.append("%s⏱ Time       <code>%s</code>" % (V, hms(el)))
    if sp and not ARCHIVE and not ended:
        idle = time.time() - sp.last_es
        L.append("%s%s" % (V, "🟢 Stream     online" if idle < 10 else ("🟡 Stream     waiting %ds" % idle if idle < 60 else "🔴 Stream     no data %s" % mmss(idle))))
    L.append("%s💿 Saved      <code>%d file(s) · %s</code>" % (V, len(S["done"]), human(saved)))
    if S["restarts"]:
        L.append("%s🔁 Reconnect  <code>%d</code> (no data lost)" % (V, S["restarts"]))
    if S["page"]:
        L.append('%s📂 <a href="%s">Open the download page</a>' % (V, S["page"]))
    L += [BOX_MID, "%s%s  🕒 %s" % (V, naim_sig(i), clock()), BOX_END]
    return "\n".join(L)



_PIL = []


PIC_WHY = []
_PIC_TOLD = []


def pic_off(why):
    """Tell the person (once) why the dashboard is text instead of a picture."""
    print("Picture dashboard off: %s" % why, flush=True)
    if not _PIC_TOLD:
        _PIC_TOLD.append(1)
        say("ℹ️ Picture dashboard is off, showing text instead.\nReason: <code>%s</code>" % esc(str(why)[:200]))


def _pil():
    """Pillow draws the picture card. Installed on the fly if the runner does not have it; None = use the text panel."""
    if _PIL:
        return _PIL[0]
    mods = None
    for attempt in (0, 1):
        try:
            from PIL import Image, ImageDraw, ImageFont
            mods = (Image, ImageDraw, ImageFont)
            break
        except Exception:
            if attempt == 0:
                try:
                    pr = subprocess.run([sys.executable, "-m", "pip", "install", "-q", "--break-system-packages", "pillow"],
                                        timeout=150, capture_output=True)
                    PIC_WHY[:] = [(pr.stderr or pr.stdout or b"").decode("utf-8", "ignore").strip()[-160:]]
                except Exception as e:
                    PIC_WHY[:] = [repr(e)[:160]]
            else:
                PIC_WHY[:] = PIC_WHY or ["import failed"]
    _PIL.append(mods)
    return mods


def _font(ImageFont, size, bold=False):
    import glob
    names = (["DejaVuSans-Bold.ttf", "LiberationSans-Bold.ttf", "FreeSansBold.ttf", "NotoSans-Bold.ttf"] if bold else
             ["DejaVuSans.ttf", "LiberationSans-Regular.ttf", "FreeSans.ttf", "NotoSans-Regular.ttf"])
    for f in names:
        for d in ("/usr/share/fonts/truetype/dejavu/", "/usr/share/fonts/truetype/liberation/", "/usr/share/fonts/dejavu/", ""):
            try:
                return ImageFont.truetype(d + f, size)
            except Exception:
                continue
    for f in sorted(glob.glob("/usr/share/fonts/**/*.ttf", recursive=True)):      # any font on the machine
        try:
            return ImageFont.truetype(f, size)
        except Exception:
            continue
    try:
        return ImageFont.load_default(size=size)                                # Pillow 10.1+: a scalable built-in font
    except Exception:
        return ImageFont.load_default()


POPPINS = "https://github.com/google/fonts/raw/main/ofl/poppins/Poppins-%s.ttf"
FONT_DIR = E("FONT_DIR") or "/tmp/recfonts"
_FFAIL = set()


def _poppins(weight):
    """Path of a Poppins font file. Downloaded once from GitHub when missing; None = use the normal font."""
    name = "Poppins-%s.ttf" % weight
    for dd in (FONT_DIR, "/usr/share/fonts/truetype/google-fonts"):
        p = os.path.join(dd, name)
        try:
            if os.path.getsize(p) > 50000:
                return p
        except OSError:
            pass
    if weight in _FFAIL:
        return None
    try:
        os.makedirs(FONT_DIR, exist_ok=True)
        req = urllib.request.Request(POPPINS % weight, headers={"User-Agent": "Mozilla/5.0"})
        data = urllib.request.urlopen(req, timeout=20).read()
        if len(data) > 50000 and data[:4] in (b"\x00\x01\x00\x00", b"true", b"OTTO"):
            p = os.path.join(FONT_DIR, name)
            with open(p, "wb") as f:
                f.write(data)
            return p
    except Exception as e:
        print("font download (%s): %s" % (weight, repr(e)[:80]), flush=True)
    _FFAIL.add(weight)
    return None


def _pf(ImageFont, size, weight="Bold"):
    p = _poppins(weight)
    if p:
        try:
            return ImageFont.truetype(p, size)
        except Exception:
            pass
    return _font(ImageFont, size, weight in ("Bold", "BoldItalic"))


def _hue(Image, ImageChops, w, h, shift):
    """A rainbow (RGB) gradient image; shift moves the colours along."""
    ramp = Image.linear_gradient("L").rotate(90).resize((w, h))
    ramp = ImageChops.offset(ramp, int((shift % 1.0) * w), 0)
    one = Image.new("L", (w, h), 255)
    return Image.merge("HSV", (ramp, one, one)).convert("RGB")


def live_card(i, ended=False, hist=(), note=None):
    """The picture dashboard (RGB ring + big rows). One design for live, archive, finished and the Status/Split/Stop answers."""
    mods = _pil()
    if not mods:
        return None
    Image, ImageDraw, ImageFont = mods
    from PIL import ImageChops, ImageFilter
    import io
    K, W, H = 2, 1000, 600
    shift = (i * 0.06) % 1.0
    img = Image.new("RGB", (W * K, H * K), (6, 5, 14))
    G = _hue(Image, ImageChops, W * K, H * K, shift)
    img = ImageChops.add(img, G.point(lambda v: int(v * 0.07)))
    d = ImageDraw.Draw(img)
    M = Image.new("L", (W * K, H * K), 0)                       # everything that gets the rainbow colour
    md = ImageDraw.Draw(M)
    P = lambda sz, w="Bold": _pf(ImageFont, sz * K, w)
    white, muted, mid, track = (255, 255, 255), (150, 155, 200), (190, 195, 230), (26, 24, 44)
    later = []                                                  # white text is drawn after the glow, so it stays white

    def MT(x, y, t, f, a="la"): md.text((x * K, y * K), t, font=f, fill=255, anchor=a)
    def LT(x, y, t, f, c=white, a="la"): later.append(lambda: d.text((x * K, y * K), t, font=f, fill=c, anchor=a))
    def spaced(x, y, t, f, c, sp=5, a="l"):
        wid = sum(d.textlength(ch, font=f) / K for ch in t) + sp * (len(t) - 1)
        cx = x - (wid if a == "r" else wid / 2 if a == "c" else 0)
        for ch in t:
            later.append(lambda ch=ch, cx=cx: d.text((cx * K, y * K), ch, font=f, fill=c))
            cx += d.textlength(ch, font=f) / K + sp

    el = time.time() - S["t0"]
    sp = SP
    spd = sp.speed_mbps() if sp else 0
    saved = sum(x["size"] for x in S["done"])
    rec_secs = sum(x.get("secs", 0) for x in S["done"]) + (sp.media_secs() if (sp and not ended) else 0)
    frac, sub, under, rows = 0.0, "", "", []
    if ended:
        title = "FINISHED"
        rows = [("TOTAL TIME", hms(el), 64), ("FILES", "%d file%s" % (len(S["done"]), "" if len(S["done"]) == 1 else "s"), 64),
                ("TOTAL SIZE", human(saved), 40), ("DOWNLOADED" if ARCHIVE else "RECORDED", hms(rec_secs), 40)]
        frac = 1.0
    elif ARCHIVE:
        title = "DOWNLOADING"
        eta, got = None, human(D["got"])
        if KIND == "ts" and D["total"]:
            frac = D["got"] / max(1, D["total"])
            got = "%s / %s" % (human(D["got"]), human(D["total"]))
            if spd > 0.1:
                eta = (D["total"] - D["got"]) * 8 / (spd * 1e6)
        elif D["dur"]:
            frac = D["secs"] / max(1, D["dur"])
            got = "%s / %s" % (mmss(D["secs"]), mmss(D["dur"]))
            if D["secs"] > 5:
                eta = (D["dur"] - D["secs"]) * el / D["secs"]
        sub = "DOWNLOADED"
        under = ("ends ~%s" % clock(time.time() + eta)) if eta else ""
        rows = [("TIME LEFT", ("~" + hms(eta)) if eta else "--", 64), ("SPEED", "%.1f" % spd, 64),
                ("DOWNLOADED", got, 40), ("ELAPSED", hms(el), 40)]
    else:
        title = "LIVE"
        frac = min(1.0, sp.est() / PART_MAX) if (sp and PART_MAX) else 0.0
        sub = "FILE #%02d" % (sp.part_no if sp else 0)
        if sp and sp.f:
            t_left = (PART_MIN * 60 - sp.media_secs()) if PART_MIN > 0 else 1e12
            if spd > 0.1:
                t_left = min(t_left, (PART_MAX - sp.est()) * 8 / (spd * 1e6))
            if t_left < 1e11:
                under = "split in ~%s" % mmss(t_left)
        rows = [("RECORDED", hms(rec_secs), 64), ("SPEED", "%.1f" % spd, 64),
                ("FILE #%02d" % (sp.part_no if sp else 0), "%s / %s" % (human(sp.est()) if sp else "0 MB", human(PART_MAX)), 40),
                ("SAVED", "%d file%s · %s" % (len(S["done"]), "" if len(S["done"]) == 1 else "s", human(saved)), 40)]
    frac = max(0.0, min(1.0, frac))

    # ring
    cx, cy, r, rw = 235, 322, 170, 38
    box = ((cx - r) * K, (cy - r) * K, (cx + r) * K, (cy + r) * K)
    d.arc(box, 0, 360, fill=track, width=rw * K)
    for a in range(0, 360, 15):
        ca, sa = math.cos(math.radians(a)), math.sin(math.radians(a))
        d.line(((cx + (r + 30) * ca) * K, (cy + (r + 30) * sa) * K, (cx + (r + 40) * ca) * K, (cy + (r + 40) * sa) * K), fill=(50, 48, 80), width=3 * K)
    if frac > 0.004:
        md.arc(box, -90, -90 + 360 * frac, fill=255, width=rw * K)
    if ended:
        md.line([(cx * K - 62 * K, cy * K + 4 * K), (cx * K - 18 * K, cy * K + 46 * K), (cx * K + 66 * K, cy * K - 52 * K)], fill=255, width=20 * K, joint="curve")
        spaced(cx, cy + 66, "COMPLETE", P(22, "Medium"), mid, 4, "c")
    else:
        txt = "%d" % int(frac * 100)
        nw = d.textlength(txt, font=P(140)) / K
        LT(cx - 22, cy - 16, txt, P(140), white, "mm")
        LT(cx - 22 + nw / 2 + 4, cy + 20, "%", P(54), mid, "lm")
        spaced(cx, cy + 64, sub, P(20, "Medium"), muted, 4, "c")
        if under:
            LT(cx, cy + 100, under, P(22, "Medium"), mid, "mm")

    # header
    if note:
        nt, nc = note
        fw = P(22)
        tw = d.textlength(nt, font=fw) / K
        d.rounded_rectangle((40 * K, 22 * K, (40 + tw + 40) * K, 66 * K), radius=22 * K, fill=nc)
        d.text(((40 + tw / 2 + 20) * K, 44 * K), nt, font=fw, fill=(12, 14, 30), anchor="mm")
    md.ellipse((502 * K, 34 * K, 530 * K, 62 * K), fill=255)
    MT(546, 20, title, P(52 if len(title) < 9 else 40), "la")
    nm = NAME if len(NAME) <= 30 else NAME[:29] + "…"
    LT(500, 82, nm, P(24, "Medium"), (235, 235, 250))

    # rows
    y = 118
    for k, (lab, val, fs) in enumerate(rows):
        spaced(500, y, lab, P(19, "Medium"), muted, 5)
        base = y + 34 + fs * 0.74
        LT(500, base, val, P(fs), white, "ls")
        if lab == "SPEED":
            vw = d.textlength(val, font=P(fs)) / K
            LT(500 + vw + 10, base, "Mbps", P(28), mid, "ls")
            vals = list(hist)[-10:]
            if len(vals) >= 2 and not ended:
                mx = max(max(vals), 0.5)
                for n_, v in enumerate(vals):
                    bh = max(4, int(v / mx * 44))
                    md.rounded_rectangle(((800 + n_ * 15) * K, (y + 90 - bh) * K, (808 + n_ * 15) * K, (y + 90) * K), radius=3 * K, fill=255)
        md.rounded_rectangle((500 * K, (y + 98) * K, 952 * K, (y + 102) * K), radius=2 * K, fill=255)
        y += 102

    # footer
    foot = ("Reconnects %d (no data lost)" % S["restarts"]) if S["restarts"] else "No reconnects"
    foot += "   ·   " + ("finished %s" % clock() if ended else "updated %s" % clock())
    LT(40, 584, foot, P(18, "Medium"), muted, "lm")
    MT(952, 592, "NaimX", P(76, "BoldItalic"), "rs")

    glow = M.filter(ImageFilter.GaussianBlur(13 * K)).point(lambda v: int(v * 0.8))
    img.paste(G, (0, 0), glow)
    img.paste(G, (0, 0), M)
    d = ImageDraw.Draw(img)
    for f_ in later:
        f_()
    out = img.resize((W, H), Image.LANCZOS)
    b = io.BytesIO()
    out.save(b, "PNG")
    return b.getvalue()


def live_caption(ended=False):
    L = ["✅ <b>Finished</b>" if ended else ("⬇️ <b>Downloading</b>" if ARCHIVE else "🔴 <b>Recording</b>"), "🎬 %s" % esc(NAME)]
    if ARCHIVE and not ended and KIND == "ts" and D["total"] and SP and SP.speed_mbps() > 0.1:
        eta = (D["total"] - D["got"]) * 8 / (SP.speed_mbps() * 1e6)
        L.append("⏳ ~%s left  ·  done around <b>%s</b>" % (hms(eta), clock(time.time() + eta)))
    if S["page"]:
        L.append('📂 <a href="%s">Open the download page</a>' % S["page"])
    return "\n".join(L)


def tg_photo(method, fields, png):
    """multipart upload of the card (sendPhoto / editMessageMedia)."""
    if not TOKEN or DRY:
        return {}
    if tg_wait_left(method) > 0:
        return {"ok": False, "error_code": 429, "blocked": True}
    bd = "----rec%x" % int(time.time() * 1000)
    body = b""
    for k, v in fields.items():
        body += ("--%s\r\nContent-Disposition: form-data; name=\"%s\"\r\n\r\n%s\r\n" % (bd, k, v)).encode()
    fld = "photo" if method == "sendPhoto" else "card"      # sendPhoto wants the file in a field named photo; editMessageMedia points to it with attach://card
    body += ("--%s\r\nContent-Disposition: form-data; name=\"%s\"; filename=\"card.png\"\r\nContent-Type: image/png\r\n\r\n" % (bd, fld)).encode() + png + ("\r\n--%s--\r\n" % bd).encode()
    try:
        req = urllib.request.Request("%s/bot%s/%s" % (E("TG_API") or "https://api.telegram.org", TOKEN, method), body,
                                     {"Content-Type": "multipart/form-data; boundary=" + bd})
        return json.load(urllib.request.urlopen(req, timeout=60))
    except urllib.error.HTTPError as e:
        try: body = e.read().decode()[:300]
        except Exception: body = ""
        if e.code == 429:
            tg_flood(method, body)
        else:
            print("Telegram error %s: %s" % (e.code, body[:200]), flush=True)
        return {"ok": False, "error_code": e.code, "description": body}
    except Exception as e:
        print("telegram error:", e)
        return {}


HIST = []


def pic_reply(note, caption):
    """Status / Split / Stop answer as a picture card (falls back to text when pictures are off)."""
    if E("LIVE_CARD") == "0" or DRY:
        return False
    try:
        png = live_card(int(time.time() / 3), False, HIST, note)
    except Exception as e:
        print("pic reply:", repr(e)[:120], flush=True)
        return False
    if not png:
        return False
    kb = json.dumps({"inline_keyboard": []} if stop.is_set() else KB)
    ok = False
    for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
        r = tg_photo("sendPhoto", {"chat_id": cid, "caption": caption, "parse_mode": "HTML", "reply_markup": kb}, png)
        ok = ok or bool(r.get("ok"))
    return ok


def live_loop():
    cids = list(dict.fromkeys([c for c in [CHAT] + ALSO if c]))
    if not cids:
        return
    ids, bad, hist = {}, {}, []
    TEXT_PANEL = E("LIVE_PANEL") == "text"                  # live message as the box text, everything else stays a picture
    use_img = E("LIVE_CARD") != "0" and not TEXT_PANEL and bool(_pil())    
    print("Live panel: %s" % ("picture card" if use_img else "text"), flush=True)
    if E("LIVE_CARD") == "0":
        pass
    elif not use_img and not TEXT_PANEL:
        pic_off("Pillow could not be loaded. %s" % ((PIC_WHY or [""])[0]))
    i = 0
    while True:
        ended = stop.is_set()
        png = text = None
        try:
            hist = (hist + [SP.speed_mbps() if SP else 0.0])[-16:]
            HIST[:] = hist
            if use_img:
                png = live_card(i, ended, hist)
            if not png:
                text = live_text(i, ended, hist)
        except Exception as e:
            print("live panel:", repr(e)[:120], flush=True)
            if use_img:
                pic_off("card drawing failed: %s" % repr(e)[:120])
                use_img = False; ids.clear(); bad.clear()           # picture failed: use the text panel instead
            if ended:
                return
            time.sleep(5); i += 1; continue
        kb = json.dumps({"inline_keyboard": []} if ended else KB)
        for cid in cids:
            if bad.get(cid, 0) >= 3:
                continue
            if png:
                cap = live_caption(ended)
                if cid in ids:
                    r = tg_photo("editMessageMedia", {"chat_id": cid, "message_id": ids[cid], "reply_markup": kb,
                                 "media": json.dumps({"type": "photo", "media": "attach://card", "caption": cap, "parse_mode": "HTML"})}, png)
                else:
                    r = tg_photo("sendPhoto", {"chat_id": cid, "caption": cap, "parse_mode": "HTML", "reply_markup": kb}, png)
            else:
                d = dict(chat_id=cid, text=text, parse_mode="HTML", disable_web_page_preview="true", reply_markup=kb)
                if cid in ids:
                    d["message_id"] = ids[cid]
                r = tg("editMessageText" if cid in ids else "sendMessage", **d)
            if r.get("error_code") == 429:
                pass                                                # tg() already knows how long to wait and skips the calls until then
            elif r.get("error_code") == 400 and "not modified" in str(r.get("description", "")):
                bad[cid] = 0
            elif r.get("error_code"):
                bad[cid] = bad.get(cid, 0) + 1
                if r.get("error_code") == 400:
                    ids.pop(cid, None)                              # message deleted: send a new one
                if bad[cid] >= 3 and use_img and not ids:
                    pic_off("Telegram refused the picture (error %s)" % r.get("error_code"))
                    use_img = False; ids.clear(); bad.clear()       # picture keeps failing: switch to text
                    break
            else:
                bad[cid] = 0
                mid = (r.get("result") or {}).get("message_id")
                if mid and cid not in ids:
                    ids[cid] = mid
        if ended:
            return
        i += 1
        for _ in range(20 if use_img else 10):
            if stop.is_set():
                break
            time.sleep(0.5)


def do_action(act, cq_id=None):
    global SP
    act = (act or "").split("@")[0]
    if act == "status":
        txt = "Status sent"
        if not pic_reply(("STATUS", (80, 165, 255)), "📊 <b>Status</b> · %s" % esc(NAME)):
            say(status_text(), buttons=True)
    elif act == "split":
        if SP and SP.f:
            SP.want_split = True; txt = "Split requested"
            if not pic_reply(("SPLIT REQUESTED", (255, 190, 60)), "✂️ <b>Split requested</b>\nThe file closes at the next keyframe. Recording continues in a new file."):
                say(note_box("✂️ <b>𝗦𝗣𝗟𝗜𝗧</b>", "The file closes at the next keyframe (a few seconds).", "Recording continues in a new file."), buttons=True)
        else:
            txt = "Not recording yet"; say("Recording has not started yet, nothing to split.")
    elif act == "stop":
        txt = "Stopping"
        if not pic_reply(("STOPPING", (255, 77, 94)), "⏹ <b>Stopping...</b>\nSaving the last file. This can take up to a minute."):
            say(note_box("⏹ <b>𝗦𝗧𝗢𝗣𝗣𝗜𝗡𝗚</b>", "Saving the last file.", "This can take up to a minute."))
        halt()
    else:
        return
    if cq_id:
        tg("answerCallbackQuery", callback_query_id=cq_id, text=txt)


def halt():
    stop.set()
    p = S["proc"]
    if p and p.poll() is None:
        p.send_signal(signal.SIGINT)                  # ffmpeg finishes cleanly
    r = S.get("resp")
    if r is not None:                                 # raw .ts download: cut the connection so the read stops now
        try: r.fp.raw._sock.shutdown(socket.SHUT_RDWR)
        except Exception: pass


def poll():
    off = 0
    r = tg("getUpdates", offset=-1, timeout=0)
    if r.get("error_code") == 409:
        return                                         # a webhook (worker) is active: it handles /stop
    for u in r.get("result", []):
        off = u["update_id"] + 1
    while not stop.is_set():
        r = tg("getUpdates", offset=off, timeout=15, allowed_updates=json.dumps(["message", "callback_query"]))
        if r.get("error_code") == 409:
            return
        for u in r.get("result", []):
            off = u["update_id"] + 1
            cq = u.get("callback_query")
            if cq:
                if str(((cq.get("message") or {}).get("chat") or {}).get("id")) == str(CHAT):
                    do_action(cq.get("data", ""), cq.get("id"))
                continue
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) != str(CHAT):
                continue
            t = (m.get("text") or "").strip().lower().split("@")[0]
            for key in ("status", "split", "stop"):
                if t.startswith("/" + key) or (key == "split" and t.startswith("/slipt")):
                    do_action(key); break
            else:
                if t.startswith("/start") or t.startswith("/help"):
                    say("🎬 <b>ClipByNaim recorder</b>\nUse the buttons or send /status, /split, /stop.", buttons=True)
        if not r:
            time.sleep(3)


# ---------------- upload (Gofile) ----------------
def gofile_upload(path):
    """Upload to Gofile (no account). All files of one recording go into the same folder page."""
    if DRY:
        print("[dry] would upload to gofile", path); return True, "https://gofile.io/d/DRYRUN", ""
    err = ""
    for attempt in range(6):
        cmd = ["nice", "-n", "10", "curl", "-sS", "-m", "3600", "-F", "file=@" + path]   # low priority: never starve the recorder
        if GF["folder"] and GF["token"]:
            cmd += ["-F", "folderId=" + GF["folder"], "-F", "token=" + GF["token"]]
        r = subprocess.run(cmd + [GOFILE_URL], capture_output=True, text=True)
        try:
            j = json.loads(r.stdout)
        except Exception:
            err = (r.stderr or r.stdout or "no answer from Gofile").strip()[:200]
            j = None
        if j is not None:
            if j.get("status") == "ok":
                d = j.get("data") or {}
                GF["folder"] = d.get("parentFolder") or GF["folder"]
                GF["token"] = d.get("guestToken") or GF["token"]
                return True, d.get("downloadPage") or "", ""
            err = json.dumps(j)[:200]
            GF["folder"] = GF["token"] = ""          # maybe the folder/token was the problem, start a new folder
        print("gofile upload failed (try %d): %s" % (attempt + 1, err), flush=True)
        time.sleep(RETRY_BASE * (attempt + 1))
    return False, "", err


def media_info(path):
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height:format=duration",
                            "-of", "json", path], capture_output=True, text=True, timeout=60)
        j = json.loads(r.stdout or "{}"); st = (j.get("streams") or [{}])[0]
        return float((j.get("format") or {}).get("duration") or 0), int(st.get("width") or 0), int(st.get("height") or 0)
    except Exception:
        return 0.0, 0, 0


def remux(ts, mp4):
    """.ts -> .mp4 without re-encoding. Tries a few ways because some streams carry data tracks or audio that mp4 cannot hold."""
    tries = [["-map", "0:v?", "-map", "0:a?", "-c", "copy"],
             ["-map", "0:v?", "-map", "0:a?", "-c:v", "copy", "-c:a", "aac", "-b:a", "160k"],
             ["-c", "copy"]]
    first = ""
    for extra in tries:
        r = subprocess.run(["nice", "-n", "10", "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", ts] + extra +
                           ["-avoid_negative_ts", "make_zero", "-movflags", "+faststart", mp4], capture_output=True, text=True)
        if r.returncode == 0 and os.path.exists(mp4) and os.path.getsize(mp4) > 0:
            return True, ""
        if not first:
            lines = [l for l in (r.stderr or "").strip().splitlines() if l.strip()]
            first = lines[-1] if lines else "ffmpeg exit code %s" % r.returncode
        try: os.remove(mp4)
        except OSError: pass
    return False, first


def process(ts):
    """remux the finished .ts to .mp4 (proper duration), upload it, tell Telegram, clean up."""
    clip_finish_part(ts)
    if CLIPS_ONLY:
        S["done"].append({"name": os.path.basename(ts), "size": os.path.getsize(ts) if os.path.exists(ts) else 0, "secs": 0})
        if not DRY:
            try: os.remove(ts)
            except OSError: pass
        return
    os.makedirs(MP4_DIR, exist_ok=True)
    base = os.path.basename(ts)[:-3] + ".mp4"
    mp4 = os.path.join(MP4_DIR, base)
    ok_mp4, why = remux(ts, mp4)
    note = ""
    try:                                              # learn the real MP4/.ts ratio of this stream for the next parts
        tsz = os.path.getsize(ts)
        if ok_mp4 and tsz > float(E("RATIO_MIN_MB") or 200) * 1e6:
            MP4_RATIO[0] = min(1.0, max(0.8, 0.5 * MP4_RATIO[0] + 0.5 * os.path.getsize(mp4) / tsz))
            print("MP4 is %.1f%% of the .ts size, next part is cut at %s of .ts" % (100 * os.path.getsize(mp4) / tsz, human(ts_limit())), flush=True)
    except OSError:
        pass
    if not ok_mp4:
        print("MP4 conversion failed, uploading the .ts instead:", why, flush=True)
        note = "\n⚠️ MP4 conversion failed, so this is the .ts file (it plays the same).\n<code>%s</code>" % esc(why[:150])
        mp4 = ts; base = os.path.basename(ts)
    elif not DRY:
        try: os.remove(ts)                           # free disk space right away
        except OSError: pass
    size = os.path.getsize(mp4)
    dur = media_info(mp4)[0]
    n = len(S["done"]) + 1
    ok, link, err = gofile_upload(mp4)
    head = "✅ <b>File %d saved</b>\n🎞 %s  ·  %s\n" % (n, mmss(dur), human(size)) + (note + "\n" if note else "")
    if ok:
        if link:
            S["page"] = link
        S["done"].append({"name": base, "size": size, "secs": dur})
        say(head + '⬇️ <a href="%s">Download page</a>  (all files of this recording are listed there)' % (link or S["page"]), buttons=True)
        if not DRY:
            for f in {ts, mp4}:
                try: os.remove(f)
                except OSError: pass
    else:
        os.makedirs(FAILED, exist_ok=True)
        try: shutil.move(mp4, os.path.join(FAILED, base))
        except OSError: pass
        S["done"].append({"name": base, "size": size, "secs": dur})
        say("⚠️ <b>Upload to Gofile failed</b> for %s (%s)\n<b>Reason:</b> <code>%s</code>\n\nThe file is still on the GitHub server until the run ends. If this keeps happening, try again later." %
            (esc(base), human(size), esc((err or "unknown")[:250])))


MIN_FREE_GB = float(E("MIN_FREE_GB") or 12)       # archive download pauses while the disk has less free space than this
MAX_PENDING = int(E("MAX_PENDING_PARTS") or 0)    # ... or (only if set, 0 = off) while this many finished parts wait for their upload
UPLOADING = [0]
_DW = [0.0, False]


def disk_wait():
    """Archive downloads can be much bigger than the disk (100 GB vs 70 GB). Finished parts are uploaded and deleted
    while the download goes on; if the download gets ahead of the uploads, it waits here (nothing is lost)."""
    if not ARCHIVE:
        return
    now = time.time()
    if now < _DW[0]:
        return
    _DW[0] = now + 1
    waited = False
    while not stop.is_set():
        try:
            free = shutil.disk_usage(OUT).free / 1e9
        except OSError:
            return
        pending = upq.qsize() + UPLOADING[0]
        if pending == 0 or (free >= MIN_FREE_GB and (MAX_PENDING <= 0 or upq.qsize() < MAX_PENDING)):
            break
        if not waited:
            waited = True
            print("Download waits for uploads: %.1f GB free, %d part(s) waiting" % (free, pending), flush=True)
            if not _DW[1]:
                _DW[1] = True
                say("⏸ <b>The download is ahead of the uploads.</b>\nThe disk is almost full (%.0f GB free, %d finished part(s) waiting for upload). It waits until parts are uploaded and deleted. Nothing is lost, it continues by itself." % (free, pending))
        try:
            SP.last_es = time.time()
        except Exception:
            pass
        time.sleep(2)
    _DW[0] = time.time() + 1


def uploader():
    while True:
        item = upq.get()
        if item is None:
            return
        UPLOADING[0] += 1
        try:
            process(item)
        except Exception as e:
            print("process error:", repr(e), flush=True)
            say("⚠️ Error while saving a file: <code>%s</code>" % esc(repr(e)[:200]))
        finally:
            UPLOADING[0] -= 1


# ---------------- link check + recording ----------------
def explain(err):
    e = (err or "").lower()
    if "403" in e or "forbidden" in e:
        return "403 Forbidden: the stream server refuses GitHub's server. Possible reasons: the account is already in use somewhere else (many providers allow only 1-2 connections per account, so stop the other download or player and try again), a country/IP block, or the link needs a login or an expired token."
    if "401" in e or "unauthorized" in e:
        return "401 Unauthorized: the link needs a login or its token is wrong or expired."
    if "404" in e or "not found" in e:
        return "404 Not found: the link has expired or is wrong. Copy a fresh link and try again."
    if "timed out" in e or "timeout" in e:
        return "Connection timed out: the server does not answer GitHub's server. Usually an IP/country block."
    if "could not resolve" in e or "name or service not known" in e or "nodename" in e:
        return "The website name in the link could not be found. Check the link for typing mistakes."
    if "invalid data found" in e:
        return "This link is not a video playlist (.m3u8). Open it in a browser: it should give a playlist, not a web page."
    if "connection refused" in e or "reset by peer" in e or "end of file" in e:
        return "The server closed the connection. Usually it blocks GitHub's server."
    return "Unknown reason. Read the ffmpeg line above."


KIND = "hls"                                       # "hls" (.m3u8 playlist) or "ts" (live MPEG-TS over HTTP)


URL_FULL = ""                                      # the link exactly as it was sent (with the key part), used to hand it to the next run
DASH_KEYS = []                                     # [(kid, key)] hex, for ClearKey / CENC protected .mpd links
DRM_TXT = []                                       # keys typed after the link in Telegram: "kid:key"
HEX32 = r"[0-9a-fA-F]{32}"


def is_dash():
    return ".mpd" in (URL or "").lower().split("?")[0]


def set_headers_from_pairs(t):
    """User-Agent / Referer / Origin / Cookie that came with the link."""
    global UA, REFERER
    for part in re.split(r"&(?=(?:user-?agent|referer?r?|origin|cookie|drm\w*)=)", t, flags=re.I):
        k, _, v = part.partition("=")
        k, v = k.strip().lower().replace("-", "").replace("_", ""), v.strip().strip('"\'')
        if k == "useragent" and v:
            UA = v; print("Using the User-Agent that came with the link.", flush=True)
        elif k in ("referer", "referrer") and v.startswith("http"):
            REFERER = v; print("Using the Referer that came with the link.", flush=True)
        elif k == "origin" and v.startswith("http"):
            EXTRA_HDR.append("Origin: " + v)
        elif k == "cookie" and v:
            EXTRA_HDR.append("Cookie: " + v)
            print("::add-mask::" + v, flush=True)


EXTRA_HDR = []


def parse_drm():
    """A .mpd link may carry its ClearKey in the link (Kodi style:  ...mpd?|drmScheme=clearkey&drmLicense=KID:KEY ).
    The key part is cut off the link and kept; ffmpeg gets it with -cenc_decryption_key."""
    global URL, URL_FULL
    URL_FULL = URL
    keys = list(DRM_TXT)
    m = re.search(r"drmLicense=([^&\s]+)", URL, re.I)
    if m:
        for part in urllib.parse.unquote(m.group(1)).split(","):
            part = part.strip()
            kk = re.fullmatch(r"(%s):(%s)" % (HEX32, HEX32), part)
            if kk:
                keys.append((kk.group(1).lower(), kk.group(2).lower()))
            elif re.fullmatch(HEX32, part):
                keys.append(("", part.lower()))
    cut = re.split(r"[?&]?(?:%7C|\|)(?=(?:drm|user-?agent|referer?r?|origin|cookie)\w*=)", URL, maxsplit=1, flags=re.I)
    u = cut[0]
    if len(cut) > 1:                                       # Kodi style header part:  |User-Agent=...&Referer=...
        set_headers_from_pairs(urllib.parse.unquote(cut[1]))
    if "?" in u:                                           # drop drm* parameters that sit in the normal query
        base, q = u.split("?", 1)
        q = "&".join(p for p in q.split("&") if p and not re.match(r"drm(Scheme|License|LicenseType)=", p, re.I))
        u = base + ("?" + q if q else "")
    seen, DASH_KEYS[:] = set(), []
    for kid, key in keys:
        if key not in seen:
            seen.add(key); DASH_KEYS.append((kid, key))
    for kid, key in DASH_KEYS:
        print("::add-mask::" + key, flush=True)
        if kid:
            print("::add-mask::" + kid, flush=True)
    if u != URL:
        URL = u
        print("::add-mask::" + URL, flush=True)
    if is_dash():
        print("MPEG-DASH link, %d decryption key(s) found." % len(DASH_KEYS), flush=True)
        if not DASH_KEYS:
            try:
                kids = mpd_kids()
            except Exception:
                kids = {}
            if kids:
                kl = ", ".join("%s %s" % (k, v) for k, v in kids.items())
                print("Note: the manifest names a key id (KID %s) but no key was given. If the picture cannot be read later, the stream is encrypted: send the link with kid:key after it." % kl, flush=True)


def mpd_text():
    return http_get(URL, None, 25)[2].decode("utf-8", "ignore")


def mpd_kids():
    """{"video": kid, "audio": kid} from the manifest (default_KID), to give every track its own key."""
    out = {}
    try:
        for blk in re.findall(r"<AdaptationSet.*?</AdaptationSet>", mpd_text(), re.S):
            kind = "video" if re.search(r'contentType="video"|mimeType="video', blk) else ("audio" if re.search(r'contentType="audio"|mimeType="audio', blk) else "")
            k = re.search(r'default_KID="([0-9a-fA-F-]{32,36})"', blk)
            if kind and k and kind not in out:
                out[kind] = k.group(1).replace("-", "").lower()
    except Exception:
        pass
    return out


def key_for(kind, order):
    """The key for the video or audio track. One key = used for everything. Several: matched by kid, else in the order given."""
    if len(DASH_KEYS) == 1:
        return DASH_KEYS[0][1]
    kid = mpd_kids().get(kind)
    for k, v in DASH_KEYS:
        if kid and k == kid:
            return v
    return DASH_KEYS[0 if kind == "video" else 1][1]


def src_args():
    """The input part of an ffmpeg command: '-i link', or for a protected .mpd the key option too."""
    if not (is_dash() and DASH_KEYS):
        return ["-i", URL]
    if len(DASH_KEYS) == 1:
        return ["-cenc_decryption_key", DASH_KEYS[0][1], "-i", URL]
    return ["-cenc_decryption_key", key_for("video", 0), "-i", URL, "-cenc_decryption_key", key_for("audio", 0), "-i", URL]


def map_args():
    if is_dash() and len(DASH_KEYS) > 1:
        return ["-map", "0:v?", "-map", "1:a?"]
    return ["-map", "0:v?", "-map", "0:a?"]


def kind_from_url():
    u = URL.lower()
    path = u.split("?")[0]
    if "m3u8" in u:
        return "hls"
    if is_dash():
        return "dash"
    if path.endswith((".ts", ".mpegts", ".mts", ".m2ts")):
        return "ts"
    return "?"


def probe_kind():
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-rw_timeout", "20000000"] + HDR + ["-show_entries", "format=format_name", "-of", "csv=p=0", URL],
                           capture_output=True, text=True, timeout=60, env=fenv())
        names = (r.stdout or "").lower()
    except Exception:
        names = ""
    return "dash" if "dash" in names else ("hls" if ("hls" in names or "applehttp" in names) else "ts")


MOBILE_UA = "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Mobile Safari/537.36"
CHROME_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Safari/537.36"


def header_sets():
    sets = []
    if REFERER:
        o = _origin(REFERER)
        sets.append(("the referer you gave", ["-user_agent", UA, "-referer", REFERER] + (["-headers", "Origin: %s\r\n" % o] if o else [])))
    sets.append(("a normal browser User-Agent", ["-user_agent", UA]))
    o0 = _origin(URL)
    for mob in (True, False):                          # phone Chrome first (the link plays in a phone browser), then desktop Chrome
        nm = "a phone Chrome" if mob else "a desktop Chrome"
        for label, ref in ((nm + " with full browser headers (no referer)", ""),
                           (nm + " with full browser headers and the stream's own site as referer", (o0 + "/") if o0 else ""),
                           (nm + " with full browser headers and the referer you gave", REFERER)):
            if label.endswith("you gave") and not REFERER:
                continue
            if label.endswith("referer") and not ref:
                continue
            ao = _origin(ref) if ref else ""
            hs = ["Accept: */*", "Accept-Language: en-US,en;q=0.9",
                  'sec-ch-ua: "Chromium";v="149", "Not.A/Brand";v="24", "Google Chrome";v="149"',
                  "sec-ch-ua-mobile: %s" % ("?1" if mob else "?0"), 'sec-ch-ua-platform: "%s"' % ("Android" if mob else "Windows"),
                  "Sec-Fetch-Dest: empty", "Sec-Fetch-Mode: cors",
                  "Sec-Fetch-Site: cross-site" if ao and ao != o0 else "Sec-Fetch-Site: same-origin"]
            if ao:
                hs.append("Origin: " + ao)
            hs += EXTRA_HDR
            sets.append((label, ["-user_agent", MOBILE_UA if mob else CHROME_UA] + (["-referer", ref] if ref else []) + ["-headers", "".join(x + "\r\n" for x in hs)]))
    if EXTRA_HDR:
        sets = [(l, h + ["-headers", "".join(x + "\r\n" for x in EXTRA_HDR)]) if "-headers" not in h else (l, h) for l, h in sets]
    o = _origin(URL)
    if o:
        sets.append(("browser headers with the stream's own site as referer", ["-user_agent", UA, "-referer", o + "/", "-headers", "Origin: %s\r\n" % o]))
    if kind_from_url() != "hls":
        sets.append(("a VLC player User-Agent", ["-user_agent", "VLC/3.0.20 LibVLC/3.0.20"]))   # IPTV servers often expect a player
        sets.append(("the default ffmpeg User-Agent", []))
    return sets


def precheck():
    global HDR
    last = ""
    slow_n = 0
    for label, hdr in header_sets():
        if is_dash():                                   # a .mpd is tested with our own reader: manifest, then an init and a media segment
            global KIND
            HDR = hdr
            try:
                P = dash_parse(mpd_text(), URL)
                for tr in P["tracks"].values():
                    if tr["init"]:
                        http_get(tr["init"], None, 25)
                    if tr["segs"]:
                        http_get(tr["segs"][-1].url, None, 25)
            except Exception as e:
                if isinstance(e, urllib.error.HTTPError):
                    last = "%d %s: the server refused (%s)" % (e.code, e.reason, "manifest or segment")
                else:
                    last = mask(repr(e))[:300]
                print("Could not open with %s: %s" % (label, last[-150:]), flush=True)
                HDR = ["-user_agent", UA]
                continue
            KIND = "dash"
            print("Link opened using: %s | stream type: MPEG-DASH (.mpd)" % label, flush=True)
            return True, ""
        try:
            r = subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "error"] + hdr + ["-rw_timeout", "20000000", "-t", "6"] + src_args() + ["-f", "null", "-"],
                               capture_output=True, text=True, timeout=60, env=fenv())
        except Exception as e:
            last = "Connection timed out (no answer from the server in 20 s)" if isinstance(e, subprocess.TimeoutExpired) else str(e)
            print("Could not open with %s: %s" % (label, last[-150:]), flush=True)
            slow_n += 1
            if slow_n >= 2:                              # the server does not answer at all: it blocks this IP, other headers cannot change that
                print("The server does not answer from here (no connection). Other headers cannot help, so the other sets are not tried now.", flush=True)
                return False, last
            continue
        if r.returncode == 0:
            HDR = hdr
            KIND = kind_from_url()
            if KIND == "?":
                KIND = probe_kind()
            forced = (E("STREAM_TYPE") or "auto").lower()
            if forced in ("hls", "ts"):
                KIND = forced
            print("Link opened using: %s | stream type: %s" % (label, "MPEG-TS (live)" if KIND == "ts" else ("MPEG-DASH (.mpd)" if KIND == "dash" else "HLS (.m3u8)")), flush=True)
            return True, ""
        last = mask((r.stderr or "").strip())[-400:]
        print("Could not open with %s: %s" % (label, last.splitlines()[-1] if last else "?"), flush=True)
        if re.search(r"timed out|no route|unreachable|connection refused", last.lower()):
            slow_n += 1
            if slow_n >= 2:
                print("The server does not answer from here (no connection). Other headers cannot help, so the other sets are not tried now.", flush=True)
                return False, last
        else:
            slow_n = 0
    return False, last


def worker_get(path):
    req = urllib.request.Request(WORKER_URL + path, headers={"X-Key": WORKER_KEY, "User-Agent": "recorder"})
    return json.load(urllib.request.urlopen(req, timeout=20))


def fetch_link():
    """The worker kept the stream link for us (so the link is never in the GitHub run page)."""
    global URL, ASKED
    for i in range(6):
        try:
            u = (worker_get("/link?ticket=" + urllib.parse.quote(TICKET)) or {}).get("url", "")
            if u:
                f = re.search(r"https?://\S+", u)
                URL = (f.group(0) if f else u).strip().strip("<>\"'"); ASKED = True
                set_mode_from_text(u)
                print("::add-mask::" + URL, flush=True)
                return True
        except Exception as e:
            print("link request failed:", mask(repr(e))[:120], flush=True)
        time.sleep(3)
    return False


def worker_poll():
    """Stop / Status / Split presses arrive through the worker (Telegram only allows one reader of the bot).
    Every poll costs the worker KV reads (the free plan has 100,000 a day), so it is slow when nothing happens:
    quick for a while after a press, then slower and slower (up to POLL_MAX seconds)."""
    chats = ",".join(dict.fromkeys([c for c in [CHAT] + ALSO if c]))
    fast = float(E("POLL_FAST") or 3)
    slow = float(E("POLL_MAX") or 20)
    gap, last_cmd = fast, time.time()
    while not stop.is_set():
        try:
            cmds = (worker_get("/cmd?chats=" + urllib.parse.quote(chats) + "&run=" + RUN + "&me=" + urllib.parse.quote(CHAT or "")) or {}).get("cmds", [])
            for c in cmds:
                do_action(c)
            if cmds:
                last_cmd = time.time()
        except Exception as e:
            print("worker poll failed:", repr(e)[:100], flush=True)
        idle = time.time() - last_cmd
        gap = fast if idle < 60 else (min(slow, 6) if idle < 300 else slow)
        t_end = time.time() + gap
        while time.time() < t_end:
            if stop.is_set():
                return
            time.sleep(0.5)


def preflight():
    """Personal bot: check the secrets and the bot BEFORE asking for the link, with clear errors."""
    if DRY:
        return
    if not TOKEN:
        print("::error title=Secret TG_TOKEN is empty::Repo > Settings > Secrets and variables > Actions > New repository secret. Name: TG_TOKEN, value: the token from BotFather.", flush=True)
        sys.exit(1)
    me = tg("getMe")
    if not me.get("ok"):
        print("::error title=Bot token is wrong::Telegram refused TG_TOKEN (error %s). Copy the token again from BotFather and save it in the secret." % me.get("error_code", "?"), flush=True)
        sys.exit(1)
    print("Bot: @%s" % (me.get("result") or {}).get("username", "?"), flush=True)
    wh = (tg("getWebhookInfo").get("result") or {})
    if wh.get("url"):
        # The personal workflow has no Worker, so a webhook on this bot only blocks reading your link: remove it.
        print("This bot had a webhook (%s). Removing it so the bot can read your link." % wh["url"].split("/")[2], flush=True)
        d = tg("deleteWebhook")
        if not d.get("ok"):
            print("::error title=This bot has a webhook::Could not remove it. Open https://api.telegram.org/bot<TOKEN>/deleteWebhook once, or use a new bot from BotFather.", flush=True)
            sys.exit(1)
    if not CHAT:
        detect_chat()
    if not CHAT:
        print("::error title=No chat id::Open your personal bot in Telegram, press Start and send 'hi', then run again. (Or add secret TG_CHAT = your chat id.)", flush=True)
        sys.exit(1)
    r = tg("sendMessage", chat_id=CHAT, text="⏳ Workflow started. Getting ready...")
    if r.get("error_code") in (400, 403):
        print("::error title=The bot cannot write to your chat::Open your personal bot in Telegram, press Start, and check that TG_CHAT is YOUR chat id (a number). Telegram error %s." % r.get("error_code"), flush=True)
        sys.exit(1)


def set_mode_from_text(t):
    """The word archive / live after the link chooses the mode."""
    global MODE
    global UA, REFERER
    m = re.search(r"user[_ -]?agent[\"']?\s*[:=]\s*[\"']?(Mozilla/[^\"'\n]+)", t or "", re.I)
    if m:
        UA = m.group(1).strip(); print("Using the User-Agent you sent.", flush=True)
    m = re.search(r"cookie[\"']?\s*[:=]\s*[\"']?([^\"'\n]+)", t or "", re.I)
    if m and m.group(1).strip():
        EXTRA_HDR.append("Cookie: " + m.group(1).strip())
        print("::add-mask::" + m.group(1).strip(), flush=True)
        print("Using the Cookie you sent.", flush=True)
    m = re.search(r"(?<![\w-])origin[\"']?\s*[:=]\s*[\"']?(https?://[^\s\"']+)", t or "", re.I)
    if m:
        EXTRA_HDR.append("Origin: " + m.group(1)); print("Using the Origin you sent.", flush=True)
    m = re.search(r"referr?er[\"']?\s*[:=]\s*[\"']?(https?://[^\s\"']+)", t or "", re.I)
    if m:
        REFERER = m.group(1); print("Using the Referer you sent.", flush=True)
    for kid, key in re.findall(r"(%s):(%s)" % (HEX32, HEX32), re.sub(r"https?://\S+", " ", t or "")):
        DRM_TXT.append((kid.lower(), key.lower()))
    clip_words(t)
    w = re.sub(r"https?://\S+", " ", t or "").lower()
    if re.search(r"\barchive\b|\bdownload\b", w):
        MODE = "archive"
    elif re.search(r"\blive\b", w):
        MODE = "live"


def ask_link():
    """URL = "ask": wait for the m3u8 link in Telegram, so a public repo never shows it."""
    global URL, ASKED
    r = tg("getUpdates", timeout=0)
    if r.get("error_code") == 409:
        print("::error title=Cannot read the link::A webhook is set on the bot. Paste the link in the Run workflow form instead.", flush=True)
        sys.exit(1)
    off = 0
    for u in r.get("result", []):
        off = u["update_id"] + 1
    say("🔗 <b>Send me the stream link</b> (.m3u8 or .ts address) as a normal message.\nI wait 15 minutes. The link stays only in this chat.")
    deadline = time.time() + 15 * 60
    while time.time() < deadline:
        r = tg("getUpdates", offset=off, timeout=20)
        for u in r.get("result", []):
            off = u["update_id"] + 1
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) != str(CHAT):
                continue
            f = re.search(r"https?://\S+", m.get("text") or "")
            if f:
                URL = f.group(0).strip("<>\"'"); ASKED = True
                set_mode_from_text(m.get("text") or "")
                print("::add-mask::" + URL, flush=True)      # hide it in every log line from now on
                say("✅ <b>Link received.</b> Checking it...")
                return
        if not r:
            time.sleep(3)
    say("⏰ No link came in 15 minutes, so I stopped. Run the workflow again when you are ready.")
    print("::error title=No link received::Nothing was sent in 15 minutes.", flush=True)
    sys.exit(1)


def where():
    """Place of the IP the stream server sees (the proxy's, if a proxy is set)."""
    try:
        d = json.load(stream_opener().open("https://ipinfo.io/json", timeout=10))
        return "%s, %s%s" % (d.get("city", "?"), d.get("country", "?"), " (via proxy)" if PROXY else "")
    except Exception:
        return "unknown" + (" (via proxy)" if PROXY else "")


def _ckey():
    return hashlib.sha256(("naimx-chain|" + (E("TG_TOKEN") or "")).encode()).digest()


def chain_text():
    """The link plus what came with it (User-Agent, Referer, typed keys), so the next run opens it the same way."""
    t = URL_FULL or URL
    if UA != DEFAULT_UA:
        t += '\nuser_agent: "%s"' % UA
    if REFERER:
        t += "\nreferer: " + REFERER
    for h in EXTRA_HDR:
        t += "\n" + h
    for kid, key in DRM_TXT:
        t += "\n%s:%s" % (kid, key)
    return t + clip_chain_text()


def seal_link(u):
    """Hide the link for the next run: only a scrambled text goes through the GitHub inputs (key = your bot token)."""
    import base64, hmac
    raw = u.encode(); n = os.urandom(12); k = _ckey()
    ks = b"".join(hashlib.sha256(k + n + i.to_bytes(4, "big")).digest() for i in range(len(raw) // 32 + 1))
    ct = bytes(a ^ b for a, b in zip(raw, ks))
    tag = hmac.new(k, n + ct, hashlib.sha256).digest()[:16]
    return "enc:" + base64.urlsafe_b64encode(n + ct + tag).decode()


def open_link(t):
    import base64, hmac
    try:
        b = base64.urlsafe_b64decode(t[4:].encode()); n, ct, tag = b[:12], b[12:-16], b[-16:]
        k = _ckey()
        if not hmac.compare_digest(tag, hmac.new(k, n + ct, hashlib.sha256).digest()[:16]):
            return None
        ks = b"".join(hashlib.sha256(k + n + i.to_bytes(4, "big")).digest() for i in range(len(ct) // 32 + 1))
        return bytes(a ^ b for a, b in zip(ct, ks)).decode()
    except Exception:
        return None


def chain(rem_minutes):
    time.sleep(LIMIT - 300)
    if stop.is_set() or not shutil.which("gh"):
        return
    say("⏳ The 6 hour job limit is near. Starting the next run to continue...")
    say("🔁 The next run starts by itself with the same link. You do not need to send it again.")
    wf = E("WORKFLOW_FILE") or "record.yml"                  # the personal workflow starts itself again, not the shared one
    cmd = ["gh", "workflow", "run", wf, "--repo", REPO, "-f", "url=" + seal_link(chain_text()), "-f", "minutes=%d" % rem_minutes,
           "-f", "name=" + NAME, "-f", "part_min=%s" % PART_MIN, "-f", "part_mb=%d" % (PART_MAX / 1e6)]
    if wf == "record.yml":
        cmd += ["-f", "ticket=" + TICKET, "-f", "chat=" + (CHAT or ""), "-f", "also=" + ",".join(ALSO)]
    if REFERER:
        cmd += ["-f", "referer=" + REFERER]
    subprocess.run(cmd)


def why_exit(rc, lines):
    text = [l.strip() for l in lines if l.strip()]
    key = re.compile(r"error|failed|timed out|timeout|refused|forbidden|not found|invalid data|end of file|server returned|reset", re.I)
    hit = [l for l in text if key.search(l)]
    reason = mask((hit or text or ["no message"])[-1])[:180]
    return "exit code %s: %s" % (rc, reason)


def stderr_reader(p, box):
    for line in iter(p.stderr.readline, b""):
        box.append(line.decode("utf-8", "ignore"))
        del box[:-30]


def hdr_dict():
    """The ffmpeg header options (HDR) as a normal dict for our own downloader."""
    h = {"User-Agent": UA, "Accept": "*/*"}
    a, i = HDR, 0
    while i + 1 < len(a):
        k, v = a[i], a[i + 1]
        if k == "-user_agent":
            h["User-Agent"] = v
        elif k == "-referer":
            h["Referer"] = v
        elif k == "-headers":
            for line in v.split("\r\n"):
                if ":" in line:
                    n, _, val = line.partition(":"); h[n.strip()] = val.strip()
        i += 2
    return h


def ts_pull(rq):
    """One connection to a direct MPEG-TS link. Bytes go straight into the queue. Returns (why it ended, bytes got)."""
    got = 0
    try:
        r = stream_opener().open(urllib.request.Request(URL, headers=hdr_dict()), timeout=20)
    except urllib.error.HTTPError as e:
        return "HTTP %s from the server" % e.code, 0
    except Exception as e:
        return mask(repr(e))[:150], 0
    S["resp"] = r
    try:
        while not stop.is_set():
            data = r.read1(1 << 16)
            if not data:
                return "server closed the connection", got
            got += len(data)
            rq.put(("d", data)); S["last_data"] = time.time()
            S["qmax"] = max(S["qmax"], rq.qsize())
        return "stopped", got
    except Exception as e:
        return mask(repr(e))[:150], got
    finally:
        S["resp"] = None
        try: r.close()
        except Exception: pass


ARCH_WHY = [""]
ARCH_URL = (r"timeshift|time-shift|catch-?up|tv_?archive|/archive|/vod|/record(ing)?s?/|[?&](utc|lutc|start|from)=\d"
            r"|/\d{4}-\d{2}-\d{2}[:T_ -]\d{2}[-:]\d{2}/")


def expect_secs():
    """Timeshift links carry the length in minutes (/timeshift/user/pass/460/...). 0 = unknown."""
    m = re.search(r"/timeshift/[^/]+/[^/]+/(\d+)/", URL or "", re.I)
    return int(m.group(1)) * 60 if m else 0


def hls_is_archive():
    """(True/False, reason) for an .m3u8: a finished file or a running stream?"""
    import urllib.parse as up
    def get(x):
        return http_get(x, None, 25)[2].decode("utf-8", "ignore")
    u = URL
    text = get(u)
    for _ in range(2):                                         # a master playlist: look at the real stream inside it
        if "#EXT-X-STREAM-INF" not in text:
            break
        lines, best = text.splitlines(), None
        for k, l in enumerate(lines):
            if l.startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", l)
                bw = int(m.group(1)) if m else 0
                for l2 in lines[k + 1:]:
                    if l2.strip() and not l2.startswith("#"):
                        if best is None or bw > best[0]:
                            best = (bw, up.urljoin(u, l2.strip()))
                        break
        if not best:
            break
        u = best[1]; text = get(u)
    if "#EXT-X-ENDLIST" in text:
        return True, "the playlist has an end tag"
    if re.search(r"#EXT-X-PLAYLIST-TYPE:\s*VOD", text):
        return True, "the playlist says it is a VOD"
    def sig(t):
        return [l.strip() for l in t.splitlines() if l.strip() and not l.startswith("#")]
    m = re.search(r"#EXT-X-TARGETDURATION:(\d+)", text)
    wait = min(15.0, max(6.0, 1.6 * float(m.group(1)))) if m else 8.0
    time.sleep(wait)                                           # a running stream adds new parts meanwhile, a finished file does not
    text2 = get(u)
    if "#EXT-X-ENDLIST" in text2:
        return True, "the playlist has an end tag"
    if sig(text) == sig(text2):
        return True, "the playlist did not change for %d seconds, so it is a finished file" % wait
    return False, "the playlist keeps getting new parts"


def dash_is_archive():
    t = mpd_text()
    if re.search(r'type="dynamic"', t):
        return False, "the manifest says it is a live stream (dynamic)"
    m = re.search(r'mediaPresentationDuration="PT(?:(\d+)H)?(?:(\d+)M)?(?:([\d.]+)S)?"', t)
    if m:
        D["dur"] = int(m.group(1) or 0) * 3600 + int(m.group(2) or 0) * 60 + float(m.group(3) or 0)
    return True, "the manifest says it is a finished recording (static)"


def detect_archive():
    """True if the link is a finished file (timeshift / catch-up), False if it is a live stream."""
    if MODE == "live":
        ARCH_WHY[0] = "you chose live"; return False
    if MODE == "archive":
        ARCH_WHY[0] = "you chose archive"; return True
    if re.search(ARCH_URL, URL, re.I):                            # decided by the link itself: no network check needed
        ARCH_WHY[0] = "the link looks like a timeshift / archive link"; return True
    try:
        if KIND == "dash":
            ok, why = dash_is_archive()
            ARCH_WHY[0] = why
            return ok
        if KIND != "ts":
            ok, why = hls_is_archive()
            ARCH_WHY[0] = why
            return ok
        try:                                                   # a file answers a Range request with 206 and its size, a live stream does not
            h = hdr_dict(); h["Range"] = "bytes=0-0"
            r = stream_opener().open(urllib.request.Request(URL, headers=h), timeout=20)
            try:
                cr = r.headers.get("Content-Range") or ""
                if r.status == 206 and cr.rsplit("/", 1)[-1].isdigit() and int(cr.rsplit("/", 1)[-1]) > 500_000:
                    ARCH_WHY[0] = "the server gives a file size (%s) and accepts Range" % human(int(cr.rsplit("/", 1)[-1])); return True
            finally:
                r.close()
        except Exception:
            pass
        r = stream_opener().open(urllib.request.Request(URL, headers=hdr_dict()), timeout=20)
        try:
            cl = r.headers.get("Content-Length")               # a live stream has no length, a file has
            if cl and cl.isdigit() and int(cl) > 500_000:
                ARCH_WHY[0] = "the server gives a file size (%s)" % human(int(cl)); return True
        finally:
            r.close()
        ARCH_WHY[0] = "the server gives no file size"
        return False
    except Exception as e:
        ARCH_WHY[0] = "could not check (%s)" % mask(repr(e))[:80]
        return False


def dl_ts_once(rq):
    """One connection of a .ts file download. Always continues exactly where the last one stopped."""
    start = D["got"]
    h = hdr_dict()
    if start:
        h["Range"] = "bytes=%d-" % start
    try:
        r = stream_opener().open(urllib.request.Request(URL, headers=h), timeout=30)
    except urllib.error.HTTPError as e:
        if e.code == 416 and D["total"] and start >= D["total"]:
            return True, "complete"
        return False, "HTTP %s from the server" % e.code
    except Exception as e:
        return False, mask(repr(e))[:150]
    S["resp"] = r
    skip = 0
    n0 = D["got"]
    try:
        cr = r.headers.get("Content-Range") or ""
        cl = r.headers.get("Content-Length")
        if r.status == 206 and cr.rsplit("/", 1)[-1].isdigit():
            D["total"] = int(cr.rsplit("/", 1)[-1])
        elif r.status == 200:
            if cl and cl.isdigit():
                D["total"] = int(cl)
            skip = start                                      # the server ignored Range: skip what we already have
        while not stop.is_set():
            data = r.read1(1 << 16)
            if not data:
                break
            if skip:
                if len(data) <= skip:
                    skip -= len(data); continue
                data = data[skip:]; skip = 0
            rq.put(("d", data)); D["got"] += len(data); S["last_data"] = time.time()
        else:
            return False, "stopped"
        if D["total"] and D["got"] < D["total"]:
            return False, "connection closed at %s of %s" % (human(D["got"]), human(D["total"]))
        ex = expect_secs()
        if not D["total"] and ex and D["got"] > n0 and SP and SP.media_total() < ex * 0.97:
            return False, "connection closed early (%s of about %s)" % (mmss(SP.media_total()), mmss(ex))
        return True, "complete"
    except Exception as e:
        return False, mask(repr(e))[:150]
    finally:
        S["resp"] = None
        try: r.close()
        except Exception: pass


def wait_drain(rq):
    t = time.time()
    while not rq.empty() and time.time() - t < 60:
        time.sleep(0.2)
    time.sleep(0.6)



# ---------------------------------------------------------------------------------------------------------------------
# MPEG-DASH (.mpd), also with ClearKey / CENC encryption.
# ffmpeg's own DASH reader repeats whole segments on some live streams, so the segments are fetched here (the way the
# HLS download works) and handed to ffmpeg on pipes: ffmpeg only decrypts (with your key) and converts to MPEG-TS.
# ---------------------------------------------------------------------------------------------------------------------
import xml.etree.ElementTree as ET


def _ns(tag):
    return tag.split("}")[-1]


def _kids(el, name):
    return [c for c in el if _ns(c.tag) == name]


def _iso_secs(v):
    m = re.fullmatch(r"P(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:([\d.]+)S)?)?", (v or "").strip())
    if not m:
        return None
    d, h, mi, sec = m.groups()
    return int(d or 0) * 86400 + int(h or 0) * 3600 + int(mi or 0) * 60 + float(sec or 0)


def _tmpl(t, rid, bw, num=None, tm=None):
    def f(m):
        name, fmt = m.group(1), m.group(2)
        if name == "":
            return "$"
        v = {"RepresentationID": rid, "Bandwidth": bw, "Number": num, "Time": tm}.get(name)
        if v is None:
            return m.group(0)
        if fmt:
            return ("%" + fmt[1:]) % int(v) if fmt.startswith("%") else str(v)
        return str(v)
    return re.sub(r"\$(\w*)(%0\d+d)?\$", f, t)


class DashSeg:
    __slots__ = ("key", "url", "dur", "init")

    def __init__(self, key, url, dur, init=None):
        self.key, self.url, self.dur, self.init = key, url, dur, init


_PER_NOTE = False
_AD_SEEN = set()


def _parse_period(root, per, pstart, pdur, live, ast_t, depth, mpd_url, merged):
    tracks_all = {}
    base0 = mpd_url
    for chain in (_kids(root, "BaseURL"), _kids(per, "BaseURL")):
        if chain and chain[0].text:
            base0 = urllib.parse.urljoin(base0, chain[0].text.strip())
    for aset in _kids(per, "AdaptationSet"):
        mime = (aset.get("contentType") or aset.get("mimeType") or "")
        reps = _kids(aset, "Representation")
        if not reps:
            continue
        kind = "video" if mime.startswith("video") else ("audio" if mime.startswith("audio") else "")
        if not kind:
            m2 = (reps[0].get("mimeType") or reps[0].get("codecs") or "")
            kind = "video" if (m2.startswith("video") or "avc" in m2 or "hev" in m2 or "hvc" in m2) else ("audio" if (m2.startswith("audio") or "mp4a" in m2 or "ec-3" in m2 or "ac-3" in m2) else "")
        if kind not in ("video", "audio"):
            continue
        cand = tracks_all.get(kind)
        best = max(reps, key=lambda r: int(r.get("bandwidth") or 0))
        if cand and cand["bw"] >= int(best.get("bandwidth") or 0):
            continue
        aid = None
        for cp in _kids(aset, "ContentProtection") + _kids(best, "ContentProtection"):
            for k, v in cp.attrib.items():
                if k.endswith("default_KID"):
                    aid = v.replace("-", "").lower()
        st = (_kids(best, "SegmentTemplate") or _kids(aset, "SegmentTemplate") or [None])[0]
        if st is None:
            raise ValueError("only SegmentTemplate manifests are supported (this one uses SegmentList / SegmentBase)")
        base = base0
        for el in (aset, best):
            b = _kids(el, "BaseURL")
            if b and b[0].text:
                base = urllib.parse.urljoin(base, b[0].text.strip())
        rid, bw = best.get("id") or "", best.get("bandwidth") or "0"
        ts = float(st.get("timescale") or 1)
        start_no = int(st.get("startNumber") or 1)
        init_t, media_t = st.get("initialization"), st.get("media")
        init_url = urllib.parse.urljoin(base, _tmpl(init_t, rid, bw)) if init_t else None
        segs = []
        tl = _kids(st, "SegmentTimeline")
        if tl:
            t, num = None, start_no
            for sx in _kids(tl[0], "S"):
                if sx.get("t") is not None:
                    t = int(sx.get("t"))
                elif t is None:
                    t = 0
                d, r = int(sx.get("d")), int(sx.get("r") or 0)
                reps_n = r + 1 if r >= 0 else max(1, int(((pdur or 0) * ts - t) // d) if pdur else 1)
                for _ in range(reps_n):
                    segs.append(DashSeg((pstart, t), urllib.parse.urljoin(base, _tmpl(media_t, rid, bw, num, t)), d / ts, init_url))
                    t += d; num += 1
        else:
            d = float(st.get("duration") or 0)
            if d <= 0:
                raise ValueError("the manifest gives no segment duration")
            sd = d / ts
            if live and ast_t:
                latest = int((time.time() - ast_t - pstart) // sd) - 1
                first = max(0, latest - int((depth or 60) // sd))
                for n_ in range(first, latest + 1):
                    segs.append(DashSeg((pstart, n_), urllib.parse.urljoin(base, _tmpl(media_t, rid, bw, start_no + n_, int(n_ * d))), sd, init_url))
            else:
                total = int(math.ceil((pdur or 0) / sd)) if pdur else 0
                for n_ in range(total):
                    segs.append(DashSeg((pstart, n_), urllib.parse.urljoin(base, _tmpl(media_t, rid, bw, start_no + n_, int(n_ * d))), sd, init_url))
        tracks_all[kind] = {"init": init_url, "segs": segs, "kid": aid, "bw": int(bw or 0), "id": rid,
                               "height": int(best.get("height") or aset.get("maxHeight") or 0)}
    for kind, tr in tracks_all.items():
        m = merged.get(kind)
        if m is None:
            merged[kind] = tr
        else:
            m["segs"].extend(tr["segs"])
            m["init"], m["kid"], m["bw"], m["id"], m["height"] = tr["init"], tr["kid"], tr["bw"], tr["id"], tr["height"]


def dash_parse(text, mpd_url):
    """-> {"live": bool, "update": secs, "dur": secs or None, "tracks": {"video"/"audio": {...}}}"""
    root = ET.fromstring(text)
    live = root.get("type") == "dynamic"
    out = {"live": live, "update": _iso_secs(root.get("minimumUpdatePeriod")) or 0, "dur": _iso_secs(root.get("mediaPresentationDuration")), "tracks": {}}
    ast = root.get("availabilityStartTime")
    ast_t = None
    if ast:
        import datetime
        try:
            ast_t = datetime.datetime.fromisoformat(ast.replace("Z", "+00:00")).timestamp()
        except Exception:
            ast_t = None
    depth = _iso_secs(root.get("timeShiftBufferDepth"))
    periods = _kids(root, "Period")
    if not periods:
        raise ValueError("no Period in the manifest")
    global _PER_NOTE
    if len(periods) > 1 and not _PER_NOTE:
        _PER_NOTE = True
        print("Note: the manifest has %d periods, all of them are used in order." % len(periods), flush=True)
    base_root = mpd_url
    tracks_all = {}
    run = 0.0
    info = []
    for per in periods:
        ps = _iso_secs(per.get("start"))
        pstart = ps if ps is not None else run
        pd = _iso_secs(per.get("duration"))
        if pd:
            run = pstart + pd
        info.append((per, pstart, pd))
    longest = max([x[2] or 0 for x in info] + [0])
    keep = []
    skipped_dur = 0.0
    for per, pstart, pd in info:
        ad = False
        if len(info) > 1 and not E("KEEP_ADS") == "1":
            blob = (per.get("id") or "") + " " + " ".join((e.text or "") for e in per.iter() if e.tag.endswith("BaseURL")) + " " + " ".join(
                (e.get("media") or "") + (e.get("initialization") or "") for e in per.iter() if e.tag.endswith("SegmentTemplate"))
            if re.search(r"(?i)(^|[/_\-\.\s])(ads?|advert\w*|adbreak|preroll|midroll|sponsor\w*|promo)([/_\-\.\s0-9]|$)", blob):
                ad = True
            elif pd and longest and pd < 180 and longest >= pd * 5:
                ad = True
            if per.get("{urn:mpeg:dash:schema:mpd:2011}assetIdentifier") is not None:
                pass
        if ad:
            skipped_dur += pd or 0
            if (per.get("id"), pstart) not in _AD_SEEN:
                _AD_SEEN.add((per.get("id"), pstart))
                print("Ad skipped: period %s (%s long)" % (per.get("id") or "?", ("%ds" % pd) if pd else "?"), flush=True)
        else:
            keep.append((per, pstart, pd))
    if not keep:
        keep, skipped_dur = info, 0.0
    for per, pstart, pd in keep:
        _parse_period(root, per, pstart, pd or out["dur"], live, ast_t, depth, mpd_url, tracks_all)
    out["tracks"] = tracks_all
    if out["dur"] and skipped_dur:
        out["dur"] = max(1.0, out["dur"] - skipped_dur)        # the length without the ads, so the "file is shorter" warning does not fire
    if out["dur"] is None and not live and run:
        out["dur"] = run
    if not out["tracks"]:
        raise ValueError("no video or audio found in the manifest")
    return out


class DashFetcher:
    """Fetches init + media segments (video and audio) in order, keeps them in small queues for the ffmpeg pipes."""

    def __init__(self, start_after=None):
        self.q, self.init, self.threads = {}, {}, []
        self.start_after = dict(start_after or {})         # a new fetcher continues after the last segment of the old one
        self.lastkey = dict(self.start_after)
        self.secs = float(D["secs"])
        self.ready = threading.Event()
        self.finished = False                    # every segment was fetched (finished recording) or the live stream ended
        self.error = None
        self.live = False
        self.dur = None
        self.skipped = 0
        self.fetched = 0
        self.kinds = []
        self.kid = {}
        self.last = {}                           # last segment given to ffmpeg, re-sent after a restart (the splitter removes the repeat)
        self.ended = {}

    def start(self):
        threading.Thread(target=self._boot, daemon=True).start()

    def _boot(self):
        try:
            P = dash_parse(mpd_text(), URL)
        except Exception as e:
            self.error = "manifest: " + mask(repr(e))[:150]; self.ready.set(); return
        self.live, self.dur = P["live"], P["dur"]
        if self.dur and not self.live and not D["dur"]:
            D["dur"] = self.dur
        self.kinds = [k for k in ("video", "audio") if k in P["tracks"]]
        for k in self.kinds:
            self.q[k] = queue.Queue(maxsize=int(E("DASH_QUEUE") or 40))
            self.kid[k] = P["tracks"][k]["kid"]
            self.ended[k] = False
            t = threading.Thread(target=self._track, args=(k,), daemon=True)
            t.start(); self.threads.append(t)
        print("DASH: %s, tracks: %s%s" % ("live" if self.live else "finished recording", ", ".join("%s%s" % (k, (" %dp" % P["tracks"][k]["height"]) if P["tracks"][k]["height"] else "") for k in self.kinds),
              (", %s long" % mmss(self.dur)) if self.dur else ""), flush=True)
        t0 = time.time()
        while time.time() - t0 < 60 and not self.error and not all(k in self.init for k in self.kinds):
            time.sleep(0.2)
        self.ready.set()

    def _get(self, url, tries=6):
        last = None
        for a in range(tries):
            if stop.is_set():
                raise RuntimeError("stopped")
            try:
                return http_get(url, None, 30)[2]
            except urllib.error.HTTPError as e:
                last = e
                if e.code == 404 and a >= 2 and self.live:
                    break                        # a live segment that is not there: not worth waiting long
            except Exception as e:
                last = e
            time.sleep(min(0.5 + a, 4))
        raise last

    def _put(self, k, item):
        while not stop.is_set():
            try:
                self.q[k].put(item, timeout=1); return True
            except queue.Full:
                continue
        return False

    def _track(self, k):
        last_key, first, seen_end = self.start_after.get(k), self.start_after.get(k) is None, False
        back = int(E("DASH_BACK") or 3)
        cur_init = {}
        try:
            while not stop.is_set():
                try:
                    P = dash_parse(mpd_text(), URL)
                except Exception as e:
                    if k not in self.init:
                        raise
                    print("DASH manifest refresh failed:", mask(repr(e))[:100], flush=True)
                    time.sleep(2); continue
                tr = P["tracks"].get(k)
                if tr is None:
                    raise ValueError("%s track disappeared from the manifest" % k)
                segs = tr["segs"]
                if first and self.live:
                    segs = segs[-back:]
                first = False
                new = [s for s in segs if last_key is None or s.key > last_key]
                if k not in self.init:
                    iu = (new[0].init if new else (segs[-1].init if segs else None)) or tr["init"]
                    if iu:
                        self.init[k] = self._get(iu)
                    cur_init[k] = iu
                for s in new:
                    if s.init and cur_init.get(k) and s.init != cur_init[k]:
                        if not self._put(k, {"init": self._get(s.init)}):      # new period with a different init segment
                            return
                        cur_init[k] = s.init
                    try:
                        data = self._get(s.url)
                    except Exception as e:
                        if self.live and any(x.key > s.key for x in segs):
                            self.skipped += 1
                            print("DASH: %s segment %s could not be fetched, skipped (%s)" % (k, s.key, mask(repr(e))[:80]), flush=True)
                            last_key = s.key; continue
                        raise
                    if not self._put(k, data):
                        return
                    self.fetched += 1
                    last_key = self.lastkey[k] = s.key
                    if k == self.kinds[0]:
                        self.secs += s.dur
                        D["secs"] = max(D["secs"], self.secs)
                if not P["live"]:
                    break
                self.live = True
                time.sleep(max(0.5, min(P["update"] or (new[-1].dur / 2 if new else 2), 4)) if new else 1.0)
        except Exception as e:
            self.error = "%s: %s" % (k, mask(repr(e))[:150])
            print("DASH fetch stopped:", self.error, flush=True)
        self.ended[k] = True
        self._put(k, None)
        if all(self.ended.get(x) for x in self.kinds):
            self.finished = not self.error


DF = [None]


def dash_session(rq, first):
    """One ffmpeg run fed from the fetcher. Returns (finished, reason)."""
    old = DF[0]
    if old is None or (old.error and (not old.kinds or all(old.ended.get(k) for k in old.kinds) and all(old.q[k].empty() for k in old.kinds))):
        DF[0] = DashFetcher(old.lastkey if old else None); DF[0].start()
    f = DF[0]
    f.ready.wait(90)
    if f.error and not f.kinds:
        return False, f.error
    if not all(k in f.init for k in f.kinds):
        return False, "the first segments could not be fetched from the server"
    cmd = ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-y", "-fflags", "+discardcorrupt+genpts"]
    pipes = []
    for k in f.kinds:
        r, w = os.pipe()
        pipes.append((k, r, w))
        key = None
        if DASH_KEYS:
            key = DASH_KEYS[0][1] if len(DASH_KEYS) == 1 else next((v for kk, v in DASH_KEYS if f.kid.get(k) and kk == f.kid[k]), DASH_KEYS[0 if k == "video" else min(1, len(DASH_KEYS) - 1)][1])
        cmd += (["-decryption_key", key] if key else []) + ["-i", "pipe:%d" % r]
    if len(f.kinds) == 2:
        cmd += ["-map", "0:v?", "-map", "1:a?"]
    else:
        cmd += ["-map", "0:v?", "-map", "0:a?"]
    cmd += ["-c", "copy", "-copyts", "-muxdelay", "0", "-muxpreload", "0", "-f", "mpegts", "-mpegts_flags", "+resend_headers", "pipe:1"]
    p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0, env=fenv(), pass_fds=[r for _, r, _ in pipes])
    for _, r, _ in pipes:
        os.close(r)
    dead = threading.Event()

    def pump(k, w):
        try:
            with os.fdopen(w, "wb", buffering=0) as o:
                o.write(f.init[k])
                if f.last.get(k):
                    o.write(f.last[k])                    # after a restart: the last segment again, so nothing between is missing
                while not dead.is_set() and not stop.is_set():
                    try:
                        item = f.q[k].get(timeout=0.5)
                    except queue.Empty:
                        continue
                    if item is None:
                        return
                    if isinstance(item, dict):                # new period: ffmpeg is restarted with the new init segment
                        f.init[k] = item["init"]; f.last[k] = None
                        return
                    f.last[k] = item
                    o.write(item)
        except (BrokenPipeError, OSError):
            pass

    pts = [threading.Thread(target=pump, args=(k, w), daemon=True) for k, _, w in pipes]
    for t in pts:
        t.start()
    err = []
    threading.Thread(target=stderr_reader, args=(p, err), daemon=True).start()
    while True:
        data = p.stdout.read(1 << 20)
        if not data:
            break
        rq.put(("d", data)); S["last_data"] = time.time()
        S["qmax"] = max(S["qmax"], rq.qsize())
    p.wait()
    dead.set()
    for t in pts:
        t.join(3)
    wait_drain(rq)
    if stop.is_set():
        return False, "stopped"
    if p.returncode == 0 and f.finished and all(f.q[k].empty() for k in f.kinds):
        return True, "complete"
    if p.returncode == 0 and not f.error and not f.finished:
        return False, "new period"
    return False, f.error or why_exit(p.returncode, err)


def dl_dash_once(rq, first):
    before = D["secs"]
    done, why = dash_session(rq, first)
    D["secs"] = max(D["secs"], SP.media_total() if SP else 0)
    if not first:
        pass
    return done, why



def dl_hls_once(rq, first):
    """One ffmpeg run over a finished .m3u8. After a failure it starts a few seconds before where it stopped."""
    before = D["secs"]
    ss = ["-ss", "%.1f" % (D["secs"] - 30)] if D["secs"] > 35 else []        # restart 30 s earlier, the repeated part is dropped
    if KIND == "dash":
        hopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000"]
    else:
        hopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000",
                 "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "15", "-seg_max_retry", "15", "-live_start_index", "0", "-max_reload", "3", "-m3u8_hold_counters", "3", "-http_persistent", "0"]
    cmd = ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-y"] + hopts + ss + HDR + src_args() + map_args() + [
           "-c", "copy", "-copyts", "-muxdelay", "0", "-muxpreload", "0",
           "-f", "mpegts", "-mpegts_flags", "+resend_headers", "pipe:1"]
    if not first:
        rq.put(("n", True, False))                           # the few repeated seconds are dropped (same clock)
    p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0, env=fenv())
    err = []
    threading.Thread(target=stderr_reader, args=(p, err), daemon=True).start()
    got = 0
    while True:
        data = p.stdout.read(1 << 16)
        if not data:
            break
        rq.put(("d", data)); got += len(data); S["last_data"] = time.time()
        if TEST_KILL_MB and first and got > TEST_KILL_MB * 1e6 and p.poll() is None:
            p.kill()
    p.wait()
    wait_drain(rq)
    D["secs"] = max(D["secs"], SP.media_total())
    if stop.is_set():
        return False, "stopped"
    if p.returncode == 0 and (D["dur"] is None or D["secs"] >= D["dur"] - 8 or D["secs"] - before < 2):
        return True, "complete"
    return False, why_exit(p.returncode, err)


def archive_report():
    """After an archive download: does the file have everything the playlist promised?"""
    try:
        if SP and SP.part_no == 0 and SP.total > 1_000_000:
            print("Archive report: data was read (%d MB) but no file was started" % (SP.total // 1_000_000), flush=True)
            say("⚠️ <b>The download ran but nothing could be saved.</b> The video data was not recognised. Tell the owner, with this run's log.")
            return
        got = D["secs"] if KIND != "ts" else (SP.media_total() if SP else 0)
        jumps = SP.rebased if SP else 0
        gap = SP.gap_total if SP else 0.0
        lines = []
        if KIND != "ts" and D["dur"]:
            miss = D["dur"] - got
            if miss > 15:
                lines.append("⚠️ <b>The file is %s shorter than the playlist</b> (playlist %s, file %s).\nSome parts could not be downloaded from the server." % (mmss(miss), mmss(D["dur"]), mmss(got)))
            else:
                lines.append("✅ <b>Complete:</b> the file is as long as the playlist (%s)." % mmss(D["dur"]))
        if jumps > 1:
            lines.append("ℹ️ The archive's own clock jumps %d times (%s skipped on its clock). If the length above matches, nothing was lost by the download: the provider's archive itself has these breaks." % (jumps, mmss(gap)))
        print("Archive report: playlist=%s file=%.1fs jumps=%d jump_total=%.1fs" % (D["dur"], got, jumps, gap), flush=True)
        if lines:
            say("\n".join(lines))
    except Exception as e:
        print("archive report failed:", repr(e)[:100], flush=True)


class NotParallel(Exception):
    """This link cannot be fetched in parallel pieces (server ignores Range, encrypted / fragmented playlist ...)."""


def qput(rq, item):
    while not stop.is_set():
        try:
            rq.put(item, timeout=1); return True
        except queue.Full:
            continue
    return False


def http_get(url, rng=None, timeout=40):
    h = hdr_dict()
    if rng:
        h["Range"] = rng
    r = stream_opener().open(urllib.request.Request(url, headers=h), timeout=timeout)
    try:
        return r.status, r.headers, r.read()
    finally:
        r.close()


_KA = threading.local()
KA_OK = [not PROXY]


def http_get_ka(url, rng):
    """Like http_get for one Range piece, but every download thread keeps its connection open between pieces
    (no new TCP + TLS handshake per piece). Anything unusual (redirect, error) falls back to the normal http_get."""
    if not KA_OK[0]:
        return http_get(url, rng)
    import http.client
    u = urllib.parse.urlsplit(url)
    key = (u.scheme, u.netloc)
    conns = getattr(_KA, "c", None)
    if conns is None:
        conns = _KA.c = {}
    c = conns.get(key)
    try:
        if c is None:
            c = conns[key] = (http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection)(u.netloc, timeout=40)
        h = hdr_dict(); h["Range"] = rng
        c.request("GET", (u.path or "/") + ("?" + u.query if u.query else ""), headers=h)
        r = c.getresponse()
        body = r.read()
        if r.status in (301, 302, 303, 307, 308):
            KA_OK[0] = False                                   # redirects: use the normal way from now on
            raise IOError("redirect")
        return r.status, r.headers, body
    except Exception:
        conns.pop(key, None)
        try: c.close()
        except Exception: pass
        return http_get(url, rng)


def retry(fn, tries=6):
    last = None
    for a in range(tries):
        if stop.is_set():
            raise RuntimeError("stopped")
        try:
            return fn()
        except NotParallel:
            raise
        except Exception as e:
            last = e
            time.sleep(min(1 + a, 5))
    raise last


def ordered_parallel(n, fetch, emit, workers):
    """Run fetch(i) for i in 0..n-1 on many threads, call emit(i, data) strictly in order.
    If the server refuses some of the connections, those workers step down and the piece goes to another one, so the
    download slows to what the server allows instead of failing. Only when the last connection fails too, it gives up.
    Returns None when all n are emitted, else a short error text (everything before the failed piece was emitted)."""
    res, cond = {}, threading.Condition()
    st = {"next": 0, "emit": 0, "fail": None, "redo": [], "alive": max(1, workers), "busy": 0}
    window = max(4, workers * 2)                               # at most this many pieces in memory ahead of the writer

    def worker():
        while True:
            with cond:
                while True:
                    if st["fail"] is not None or stop.is_set():
                        return
                    if st["redo"]:
                        i = st["redo"].pop(0); break
                    if st["next"] < n and st["next"] - st["emit"] < window:
                        i = st["next"]; st["next"] += 1; break
                    if st["next"] >= n and st["busy"] == 0:
                        return
                    cond.wait(1)
                st["busy"] += 1
            try:
                data = retry(lambda: fetch(i))
            except Exception as e:
                with cond:
                    st["busy"] -= 1
                    if not isinstance(e, NotParallel) and st["alive"] > 1:
                        st["alive"] -= 1                       # this connection is refused: step down, another one takes the piece
                        st["redo"].append(i); st["redo"].sort()
                        print("Server refuses some connections (%s): now %d connections" % (mask(repr(e))[:80], st["alive"]), flush=True)
                    elif st["fail"] is None or i < st["fail"][0]:
                        st["fail"] = (i, e)
                    cond.notify_all()
                return
            with cond:
                st["busy"] -= 1
                res[i] = data; cond.notify_all()

    ths = [threading.Thread(target=worker, daemon=True) for _ in range(max(1, workers))]
    for t in ths:
        t.start()
    err = None
    while st["emit"] < n:
        with cond:
            while st["emit"] not in res and not stop.is_set() and not (st["fail"] and st["fail"][0] <= st["emit"]):
                cond.wait(1)
            if stop.is_set():
                err = "stopped"; break
            if st["emit"] not in res:
                err = st["fail"][1]; break
            data = res.pop(st["emit"])
        if not emit(st["emit"], data):
            err = "stopped"; break
        with cond:
            st["emit"] += 1; cond.notify_all()
    with cond:
        if err is not None and st["fail"] is None:
            st["fail"] = (-1, err)
        cond.notify_all()
    for t in ths:
        t.join(3)
    if err is None:
        return None
    return mask(repr(err))[:150] if isinstance(err, Exception) else str(err)


def parallel_ts(rq):
    """Heavy .ts archive: pieces of 4 MB over many connections, written in order. True = file complete."""
    try:
        h = hdr_dict(); h["Range"] = "bytes=0-0"
        r = stream_opener().open(urllib.request.Request(URL, headers=h), timeout=30)
        try:
            cr = r.headers.get("Content-Range") or ""
            ok = r.status == 206 and cr.rsplit("/", 1)[-1].isdigit()
        finally:
            r.close()
    except Exception:
        return False
    if not ok:
        return False                                           # the server ignores Range: normal download
    total = int(cr.rsplit("/", 1)[-1])
    D["total"] = total
    if total < HEAVY_MB * 1e6:
        return False
    start, CH = D["got"], int(float(E("PAR_CHUNK_MB") or 8) * (1 << 20))
    n = -(-(total - start) // CH)
    say("⚡ <b>Heavy file (%s)</b>\nDownloading with %d parallel connections. If the server refuses, it continues the normal way." % (human(total), PARALLEL))
    print("Parallel download: %d pieces of %.1f MB, %d connections" % (n, CH / 1048576, PARALLEL), flush=True)

    def fetch(i):
        a = start + i * CH
        b = min(total, a + CH) - 1
        stt, _, data = http_get_ka(URL, "bytes=%d-%d" % (a, b))
        if stt != 206:
            raise NotParallel("server ignored Range")
        if len(data) != b - a + 1:
            raise IOError("short piece")
        return data

    def emit(i, data):
        for k in range(0, len(data), 1 << 16):
            if not qput(rq, ("d", data[k:k + (1 << 16)])):
                return False
        D["got"] += len(data); S["last_data"] = time.time()
        return True
    err = ordered_parallel(n, fetch, emit, PARALLEL)
    wait_drain(rq)
    if err:
        print("Parallel download stopped (%s), continuing the normal way" % err, flush=True)
        return False
    return D["got"] >= total


TS_RE = re.compile(r"^(?P<pre>.*?/timeshift/[^/]+/[^/]+/)(?P<dur>\d+)/(?P<date>\d{4}-\d{2}-\d{2})(?P<sep>%3A|%3a|:)(?P<hh>\d{2})-(?P<mm>\d{2})(?P<post>/.*)$")
TS_MIN = float(E("TS_MINUTE_SECS") or 60)                 # one minute in seconds (only changed by tests)
TS_SLICE = int(E("TS_SLICE_MIN") or 5)                    # minutes per piece
TS_FAST_OVER = float(E("TS_FAST_OVER") or 150)           # one connection already this fast (Mbps): pieces would only slow it down
TS_PAR = int(E("TS_PAR") or 8)                            # connections for a timeshift link (providers often allow only a few)


def ts_url(i, minutes, n_min):
    """The link for 'n_min minutes starting minutes after the original start'. None if the link has another shape."""
    import datetime as dt
    m = TS_RE.match(URL)
    if not m:
        return None
    t0 = dt.datetime.strptime("%s %s:%s" % (m["date"], m["hh"], m["mm"]), "%Y-%m-%d %H:%M") + dt.timedelta(minutes=minutes)
    return "%s%d/%s%s%s%s" % (m["pre"], n_min, t0.strftime("%Y-%m-%d"), m["sep"], t0.strftime("%H-%M"), m["post"])


def ts_fetch_file(url, path, limit=None):
    """Download one piece to a file; returns its size. Raises when the server sends nothing."""
    h = hdr_dict()
    r = stream_opener().open(urllib.request.Request(url, headers=h), timeout=40)
    n = 0
    try:
        with open(path, "wb") as f:
            while not stop.is_set():
                d = r.read1(1 << 16)
                if not d:
                    break
                f.write(d); n += len(d)
                S["last_data"] = time.time()
                if limit and time.time() > limit:
                    raise IOError("too slow")
    finally:
        try: r.close()
        except Exception: pass
    if n < 100_000:
        raise IOError("piece too small (%d bytes)" % n)
    return n


def ts_probe(tmp):
    """Does the server cut a timeshift into pieces that join without any loss? Test with 3 short downloads:
    minute 0-1, minute 1-2 and minute 0-2. Safe only if every piece starts on a keyframe and 0-1 plus 1-2 is as long as 0-2."""
    def info(p):
        o = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "packet=flags", "-read_intervals", "%+#1",
                            "-of", "csv=p=0", p], capture_output=True, text=True, timeout=60).stdout.strip().split("\n")[0]
        d = subprocess.run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", p],
                           capture_output=True, text=True, timeout=60).stdout.strip().split()[0]
        return ("K" in o), float(d)
    res, speed = [], [0.0]
    for k, (st, ln) in enumerate([(0, 1), (1, 1), (0, 2)]):
        p = os.path.join(tmp, "probe%d.ts" % k)
        t_a = time.time()
        nb = ts_fetch_file(ts_url(0, st, ln), p, time.time() + 240)
        if k == 2:
            speed[0] = nb * 8 / max(0.05, time.time() - t_a) / 1e6
        res.append(info(p))
        try: os.remove(p)
        except OSError: pass
    (ka, da), (kb, db), (kr, dr) = res
    ok = ka and kb and kr and abs((da + db) - dr) <= 1.0 and dr >= 2 * TS_MIN - 6
    print("Timeshift pieces test: starts on keyframe %s/%s/%s, lengths %.1f + %.1f vs %.1f s -> %s. One connection: %.0f Mbps" % (ka, kb, kr, da, db, dr, "safe" if ok else "NOT safe", speed[0]), flush=True)
    return ok, speed[0]


def parallel_timeshift(rq):
    """Timeshift .ts without file size or Range: download pieces of TS_SLICE minutes in parallel, join them in order.
    Only used when the test above proves the server cuts cleanly. True = complete, False = not used / could not finish
    (when some pieces were already written the rest continues piece by piece, so nothing is lost or repeated)."""
    if TS_SLICE <= 0 or TS_PAR <= 1:
        return False
    m = TS_RE.match(URL or "")
    if not m:
        return False
    total_min = int(m["dur"])
    if total_min < TS_SLICE * 2:
        return False
    tmp = os.path.join(OUT, "slices"); os.makedirs(tmp, exist_ok=True)
    try:
        ok, one = ts_probe(tmp)
        if not ok:
            return False
        if one >= TS_FAST_OVER:
            print("One connection already gives %.0f Mbps, so the normal download is used (pieces would be slower)." % one, flush=True)
            return False
    except Exception as e:
        print("Timeshift pieces test failed (%s): normal download" % mask(repr(e))[:120], flush=True)
        return False
    n = -(-total_min // TS_SLICE)
    D["dur"] = total_min * TS_MIN
    say("⚡ <b>Fast timeshift mode</b>\nThe server cuts this timeshift cleanly, so it is downloaded in %d pieces with %d connections and joined in order (nothing lost, nothing repeated)." % (n, TS_PAR))
    print("Timeshift parallel: %d pieces of %d min, %d connections" % (n, TS_SLICE, TS_PAR), flush=True)
    state = {"emitted": 0}

    def make(base):
        def fetch(i):
            k = base + i
            mins = TS_SLICE * k
            ln = min(TS_SLICE, total_min - mins)
            p = os.path.join(tmp, "piece%05d.ts" % k)
            ts_fetch_file(ts_url(0, mins, ln), p)
            return p
        def emit(i, p):
            k = base + i
            if k > 0:
                if not qput(rq, ("n", False, False)):
                    return False
            with open(p, "rb") as f:
                while True:
                    d = f.read(1 << 16)
                    if not d:
                        break
                    if not qput(rq, ("d", d)):
                        return False
                    D["got"] += len(d)
            try: os.remove(p)
            except OSError: pass
            state["emitted"] = k + 1
            D["secs"] = min(D["dur"], (k + 1) * TS_SLICE * TS_MIN)
            S["last_data"] = time.time()
            return True
        return fetch, emit
    for attempt in range(4):
        base = state["emitted"]
        if base >= n:
            break
        fetch, emit = make(base)
        err = ordered_parallel(n - base, fetch, emit, TS_PAR if attempt == 0 else 1)
        wait_drain(rq)
        if err is None:
            break
        if stop.is_set():
            return False
        S["restarts"] += 1; S["reason"] = str(err)[:150]
        print("Timeshift piece failed (%s): continuing with piece %d" % (mask(str(err))[:100], state["emitted"] + 1), flush=True)
        time.sleep(3)
    for fn in os.listdir(tmp):
        try: os.remove(os.path.join(tmp, fn))
        except OSError: pass
    return True if state["emitted"] >= n else (None if state["emitted"] > 0 else False)


def hls_plan():
    """For a simple finished .m3u8 (plain .ts segments, no encryption): [(url, seconds)...]. None if it needs ffmpeg."""
    import urllib.parse as up
    def get(u):
        stt, _, b = http_get(u, None, 30)
        return b.decode("utf-8", "ignore")
    u = URL
    text = get(u)
    if "#EXT-X-STREAM-INF" in text:                            # master playlist: take the best quality
        lines = text.splitlines(); best = None
        if "TYPE=AUDIO" in text and re.search(r"#EXT-X-MEDIA:[^\n]*URI=", text):
            return None                                        # separate audio playlist: let ffmpeg merge it
        for k, l in enumerate(lines):
            if l.startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", l)
                bw = int(m.group(1)) if m else 0
                for l2 in lines[k + 1:]:
                    if l2.strip() and not l2.startswith("#"):
                        if best is None or bw > best[0]:
                            best = (bw, up.urljoin(u, l2.strip()))
                        break
        if not best:
            return None
        u = best[1]; text = get(u)
    if "#EXT-X-STREAM-INF" in text or "#EXT-X-MAP" in text or "#EXT-X-BYTERANGE" in text:
        return None
    if re.search(r"#EXT-X-KEY:(?!METHOD=NONE)", text):
        return None                                            # encrypted
    segs, dur = [], 0.0
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("#EXTINF:"):
            try: dur = float(line[8:].split(",")[0])
            except ValueError: dur = 0.0
        elif line and not line.startswith("#"):
            segs.append((up.urljoin(u, line), dur)); dur = 0.0
    return segs or None


P = {"seg": 0}


def parallel_hls(rq):
    """Heavy .m3u8 archive: segments fetched on many connections, written in order. True = complete."""
    try:
        segs = hls_plan()
    except Exception as e:
        print("Parallel plan failed:", mask(repr(e))[:120], flush=True)
        return False
    if not segs:
        return False
    total = sum(d for _, d in segs)
    D["dur"] = total
    if total < HEAVY_MIN * 60 or len(segs) < 20:
        return False
    say("⚡ <b>Heavy archive (%s, %d parts)</b>\nDownloading with %d parallel connections. If the server refuses, it continues the normal way." % (hms(total), len(segs), PARALLEL))
    print("Parallel download: %d segments, %d connections" % (len(segs), PARALLEL), flush=True)
    fails = 0
    while P["seg"] < len(segs) and not stop.is_set():
        base = P["seg"]

        def fetch(i):
            stt, _, data = http_get(segs[base + i][0])
            if stt != 200 or len(data) < 188 or data[0] != 0x47:
                if base + i == 0:
                    raise NotParallel("segments are not MPEG-TS")
                raise IOError("bad segment")
            return data

        def emit(i, data):
            for k in range(0, len(data), 1 << 16):
                if not qput(rq, ("d", data[k:k + (1 << 16)])):
                    return False
            P["seg"] = base + i + 1
            D["secs"] += segs[base + i][1]; S["last_data"] = time.time()
            return True
        err = ordered_parallel(len(segs) - base, fetch, emit, PARALLEL)
        if err is None:
            break
        fails = 0 if P["seg"] > base else fails + 1
        if stop.is_set():
            return False
        S["restarts"] += 1; S["reason"] = err
        print("Parallel download interrupted (%s) at part %d of %d" % (err, P["seg"], len(segs)), flush=True)
        if "segments are not MPEG-TS" in err or fails >= 6:
            return False                                       # let ffmpeg continue from here
        time.sleep(min(2 * fails + 1, 15))
    if P["seg"] < len(segs):
        return False
    wait_drain(rq)
    D["secs"] = max(SP.media_total(), 0.0) if SP else D["secs"]
    return True


PAR_LIVE = [False]      # live .m3u8 is recorded with many parallel connections (set by the probe or when gaps show up)
PAR_OK = [True]         # False once we know this playlist cannot be fetched by hand (encrypted, fMP4 ...)


def hls_media(u):
    """Follow a master playlist to the best stream. Returns (media_url, text) or None if ffmpeg has to do it."""
    import urllib.parse as up
    def get(x):
        return http_get(x, None, 25)[2].decode("utf-8", "ignore")
    text = get(u)
    if "#EXT-X-STREAM-INF" in text:
        if "TYPE=AUDIO" in text and re.search(r"#EXT-X-MEDIA:[^\n]*URI=", text):
            return None
        lines = text.splitlines(); best = None
        for k, l in enumerate(lines):
            if l.startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", l)
                bw = int(m.group(1)) if m else 0
                for l2 in lines[k + 1:]:
                    if l2.strip() and not l2.startswith("#"):
                        if best is None or bw > best[0]:
                            best = (bw, up.urljoin(u, l2.strip()))
                        break
        if not best:
            return None
        u = best[1]; text = get(u)
    if "#EXT-X-STREAM-INF" in text or "#EXT-X-MAP" in text or "#EXT-X-BYTERANGE" in text or re.search(r"#EXT-X-KEY:(?!METHOD=NONE)", text):
        return None
    return u, text


def hls_parse(text, base):
    import urllib.parse as up
    m = re.search(r"#EXT-X-MEDIA-SEQUENCE:(\d+)", text)
    seq = int(m.group(1)) if m else 0
    segs, dur = [], 0.0
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("#EXTINF:"):
            try: dur = float(line[8:].split(",")[0])
            except ValueError: dur = 0.0
        elif line and not line.startswith("#"):
            segs.append((up.urljoin(base, line), dur)); dur = 0.0
    return seq, segs, "#EXT-X-ENDLIST" in text


def live_probe():
    """Is one segment slower to download than it is long? Then the normal way falls behind the live edge and skips parts."""
    try:
        r = hls_media(URL)
        if not r:
            PAR_OK[0] = False
            return False
        seq, segs, ended = hls_parse(r[1], r[0])
        if ended or len(segs) < 2:
            return False
        url, dur = segs[-2]
        t = time.time()
        http_get(url, None, 25)
        took = time.time() - t
        print("Speed check: one %.1fs part took %.1fs to download" % (dur, took), flush=True)
        return dur > 0 and took > 0.5 * dur
    except Exception as e:
        print("Speed check failed:", mask(repr(e))[:100], flush=True)
        return False


def live_hls_parallel(rq):
    """Live .m3u8: look at the playlist every second or two, fetch every new part at once on many connections,
    write them in order. A slow server can no longer make us fall behind the live edge."""
    try:
        r = hls_media(URL)
    except Exception as e:
        return "playlist: " + mask(repr(e))[:100]
    if not r:
        PAR_OK[0] = False
        return "fallback"
    media = r[0]
    jobs, res, cond = queue.Queue(), {}, threading.Condition()
    st = {"emit": None, "next": None, "end": False}
    my_stop = threading.Event()

    def worker():
        while not stop.is_set() and not my_stop.is_set():
            try:
                seq, url = jobs.get(timeout=1)
            except queue.Empty:
                continue
            data = None
            for a in range(3):
                try:
                    stt, _, b = http_get(url, None, 20)
                    if stt == 200 and len(b) >= 188:
                        data = b; break
                except Exception:
                    time.sleep(0.4)
            with cond:
                res[seq] = data; cond.notify_all()

    def emitter():
        while not stop.is_set() and not my_stop.is_set():
            with cond:
                while (st["emit"] is None or st["emit"] not in res) and not stop.is_set() and not my_stop.is_set():
                    cond.wait(1)
                if stop.is_set() or my_stop.is_set():
                    return
                data = res.pop(st["emit"]); n = st["emit"]; st["emit"] += 1
            if data is None:
                print("Part %d could not be downloaded (the server no longer has it)" % n, flush=True)
                continue
            for k in range(0, len(data), 1 << 16):
                if not qput(rq, ("d", data[k:k + (1 << 16)])):
                    return
            S["last_data"] = time.time()

    ths = [threading.Thread(target=worker, daemon=True) for _ in range(PARALLEL)] + [threading.Thread(target=emitter, daemon=True)]
    for t in ths:
        t.start()
    bad, why = 0, "stopped"
    back = int(BACK) if str(BACK).isdigit() else 3
    try:
        while not stop.is_set():
            try:
                text = http_get(media, None, 15)[2].decode("utf-8", "ignore")
                seq, segs, ended = hls_parse(text, media)
                bad = 0
            except Exception as e:
                bad += 1
                if bad >= 20:
                    why = "playlist not reachable: " + mask(repr(e))[:100]
                    break
                time.sleep(1); continue
            if segs:
                last = seq + len(segs) - 1
                if st["next"] is None:
                    avg = sum(d for _, d in segs if d) / max(1, len([1 for _, d in segs if d])) or 4.0
                    safe = max(back, int(-(-30 // avg)))          # start at least 30 seconds behind the live edge (repeats are dropped)
                    st["next"] = max(seq, last - safe + 1)
                    with cond:
                        st["emit"] = st["next"]
                for k, (url, _) in enumerate(segs):
                    if seq + k >= st["next"]:
                        jobs.put((seq + k, url)); st["next"] = seq + k + 1
                if st["next"] < seq:                            # we were so far behind that the server dropped parts
                    st["next"] = seq
            if ended:
                why = "playlist ended"
                break
            tgt = min((d for _, d in segs if d), default=4.0)
            time.sleep(max(0.7, min(2.0, tgt / 2.5)))
    finally:
        # let what is already downloaded go out, then end
        t_end = time.time()
        while time.time() - t_end < 15 and not stop.is_set():
            with cond:
                pending = [k for k in res] + [] if st["emit"] is not None else []
                if not pending and jobs.empty():
                    break
            time.sleep(0.3)
        my_stop.set()
        with cond:
            cond.notify_all()
    return why


def download_loop(rq):
    """Finished file (timeshift / catch-up): download everything, resume after every break. Returns True if complete."""
    if PARALLEL > 1 and KIND != "dash":
        try:
            if (parallel_ts(rq) if KIND == "ts" else parallel_hls(rq)):
                archive_report()
                return True
        except Exception as e:
            print("Parallel download failed, normal download instead:", mask(repr(e))[:150], flush=True)
    if KIND == "ts" and not D["got"]:
        try:
            res = parallel_timeshift(rq)
        except Exception as e:
            print("Timeshift fast mode error:", mask(repr(e))[:150], flush=True)
            res = None if D["got"] else False
        if res:
            archive_report()
            return True
        if res is None:                                          # some pieces are saved but not all: a normal download would not match them
            say("❌ <b>The fast timeshift download stopped</b> and could not continue.\n<code>%s</code>\nWhat was downloaded is saved. Start again to get the rest." % esc(S["reason"][:200]))
            return False
    if KIND != "ts" and not D["dur"]:
        try:
            r = subprocess.run(["ffprobe", "-v", "error"] + HDR + ["-show_entries", "format=duration", "-of", "csv=p=0", URL],
                               capture_output=True, text=True, timeout=90, env=fenv())
            D["dur"] = float((r.stdout or "").strip().split()[0])
        except Exception:
            D["dur"] = None
    fails = 0
    n = 1 if (D["got"] or D["secs"]) else 0                      # parallel part already wrote data: continue like after a break
    while not stop.is_set():
        before = D["got"] if KIND == "ts" else D["secs"]
        done, why = dl_ts_once(rq) if KIND == "ts" else (dl_dash_once(rq, n == 0) if KIND == "dash" else dl_hls_once(rq, n == 0))
        n += 1
        if done:
            wait_drain(rq)                                       # let the writer finish before the report counts the length
            archive_report()
            return True
        if stop.is_set():
            return False
        gain = (D["got"] if KIND == "ts" else D["secs"]) - before
        fails = 0 if gain > (1_000_000 if KIND == "ts" else 2) else fails + 1
        S["restarts"] += 1; S["reason"] = why
        print("Download interrupted (%s). Continuing where it stopped (try %d)" % (why, n), flush=True)
        if fails >= 8:
            say("❌ <b>The download stopped</b> and could not continue after several tries.\n<code>%s</code>" % esc(why[:200]))
            return False
        time.sleep(min(2 * fails + 1, 20))
    return False


# ======================= Cricket clips: 4 / 6 / wicket / 50 / 100 =======================
CLIP = {"on": E("CLIPS") == "1", "pre": 30, "post": 30, "wpre": 30, "wpost": 60, "mpre": 30, "mpost": 60, "after": 0, "maxlen": 180,
        "box": None, "wide": None, "tries": 0, "next_try": 0.0, "ready": False, "msg_fail": False}
CLIP_LOCK = threading.RLock()
CLIP_EV = []                                    # events waiting to be cut
CLIP_PART = {}                                  # part path -> seconds already analysed
CLIP_ST = {"conf": None, "pend": None, "t_ov": None, "n": 0, "last": {}, "sent": 0, "kinds": [], "frames": 0, "ok": 0, "bat": [], "bpend": {}, "seen": {}}
CLIP_Q = queue.Queue()                          # clips waiting to be sent (cutting and reading go on meanwhile)
CLIP_UP = [None]
CLIP_TAG = E("CLIP_TAG") or "🔥 ℕ𝕒𝕚𝕞𝕏 🔥"
SC_RE = re.compile(r"(?<![\d.])(\d{1,3})\s*[/\-–]\s*(10|\d)(?:(?!\d)|(?=\d{1,2}\.\d))(?![\d]*\.\d{2})")
SC_REV = re.compile(r"(?<![\d.])(10|\d)\s*[/\-–]\s*(\d{1,3})(?![\d.])")           # some boards show wickets first: 3-145
SC_LOOSE = re.compile(r"(?<![\d.])(\d{2,3})\s+(10|\d)(?![\d.])")                  # "145 3" when the slash was not read
OV_RE = re.compile(r"(?<![\d.])(\d{1,2})\.([0-5])(?!\d|\.\d)")
BAT_RE = re.compile(r"(?<![\d.])(\d{1,3})\s*\*?\s*\(\s*(\d{1,3})\s*\)")           # batsman: 49(36)
TESS_OK = [None]


def clip_reset():
    """Forget everything about the last video (the clip bot calls this before every video)."""
    CLIP["box"] = None; CLIP["wide"] = None; CLIP["tight_abs"] = None; CLIP["tries"] = 0; CLIP["next_try"] = 0.0; CLIP["fmt"] = None
    with CLIP_LOCK:
        CLIP_EV.clear(); CLIP_PART.clear()
    CLIP_ST.update({"conf": None, "pend": None, "t_ov": None, "n": 0, "last": {}, "sent": 0, "kinds": [], "frames": 0, "ok": 0, "bat": [], "bpend": {}, "seen": {}, "over": {"n": None, "syms": []}, "counts": {}, "lastev": "", "board": {}, "board_t": 0.0})


def clip_words(t):
    """Words in the Telegram message: clips, pre 30, post 30, wpre 30, wpost 60, after 0."""
    w = re.sub(r"https?://\S+", " ", t or "").lower()
    if re.search(r"\bclips?\b|\bcricket\b", w):
        CLIP["on"] = True
        for key in ("pre", "post", "wpre", "wpost", "mpre", "mpost"):
            m = re.search(r"(?<![\w])%s\s*[:=]?\s*(\d{1,3})\b" % key, w)
            if m:
                CLIP[key] = max(5, min(240, int(m.group(1))))
        m = re.search(r"(?<![\w])after\s*[:=]?\s*(\d)\b", w)
        if m:
            CLIP["after"] = max(0, min(6, int(m.group(1))))
        m = re.search(r"(?<![\w])box\s*[:=]?\s*(\d*\.?\d+)[\s,]+(\d*\.?\d+)[\s,]+(\d*\.?\d+)[\s,]+(\d*\.?\d+)", w)
        if m:                                                    # the score area given by hand: x y width height (0-1, or percent)
            v = [float(x) for x in m.groups()]
            if max(v) > 1.0:
                v = [x / 100.0 for x in v]
            x, y, bw, bh = v
            if bw > 0.05 and bh > 0.02 and x + bw <= 1.01 and y + bh <= 1.01:
                CLIP["manual"] = (max(0.0, x), max(0.0, y), min(bw, 1.0 - x), min(bh, 1.0 - y))


def clip_chain_text():
    if not CLIP["on"]:
        return ""
    return "\nclips pre %d post %d wpre %d wpost %d mpre %d mpost %d after %d" % (CLIP["pre"], CLIP["post"], CLIP["wpre"], CLIP["wpost"], CLIP["mpre"], CLIP["mpost"], CLIP["after"]) + (
        (" box %.3f %.3f %.3f %.3f" % CLIP["manual"]) if CLIP.get("manual") else "")


def ensure_tesseract():
    if TESS_OK[0] is not None:
        return TESS_OK[0]
    if not shutil.which("tesseract"):
        print("Installing tesseract (for the cricket clips)...", flush=True)
        for cmd in (["sudo", "-n", "apt-get", "update", "-qq"], ["sudo", "-n", "apt-get", "install", "-y", "-qq", "--no-install-recommends", "tesseract-ocr", "tesseract-ocr-eng"]):
            try:
                subprocess.run(cmd, capture_output=True, timeout=180)
            except Exception:
                pass
    TESS_OK[0] = bool(shutil.which("tesseract"))
    return TESS_OK[0]


# ---------------------------- reading the screen ----------------------------

def _variant(png, k):
    """Other looks of the same picture for the text reader: 0 = as it is, 1 = inverted + stretched, 2 = only the bright text, 3 = only the dark text."""
    if k == 0:
        return png
    try:
        from PIL import Image, ImageOps
        im = Image.open(png).convert("L")
        if k == 1:
            im = ImageOps.autocontrast(ImageOps.invert(im), cutoff=2)
        elif k == 2:
            im = ImageOps.invert(im.point(lambda p: 255 if p > 175 else 0))
        else:
            im = im.point(lambda p: 0 if p < 90 else 255)
        out = png[:-4] + "_v%d.png" % k
        im.save(out)
        return out
    except Exception:
        return png


def _ocr(png, tsv=False, psm="6"):
    cmd = ["nice", "-n", "4", "tesseract", png, "stdout", "--psm", "11" if tsv else psm]
    if tsv:
        cmd += ["tsv"]
    else:
        cmd += ["-c", "tessedit_char_whitelist=0123456789/-–.()* "]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=40, env=dict(os.environ, OMP_THREAD_LIMIT="1"))      # one thread per reading: several readings run side by side
        return r.stdout or ""
    except Exception:
        return ""


def _ocr_words(png, psm="6"):
    """The whole text of a picture (letters too): team, batsmen, bowler."""
    try:
        r = subprocess.run(["nice", "-n", "4", "tesseract", png, "stdout", "--psm", psm], capture_output=True, text=True, timeout=40, env=dict(os.environ, OMP_THREAD_LIMIT="1"))
        return r.stdout or ""
    except Exception:
        return ""


def scoreboard_text(path, t):
    """Everything readable on the score bar at a moment (the full width of the bar): lines of text, cleaned."""
    box = CLIP.get("wide") or CLIP.get("box")
    if not box or not os.path.exists(path):
        return []
    try:
        fr = _grab(path, max(0, t), 2, box, True, os.path.join(OUT, "_clipsb_%d" % int(t)), 1800)
        if not fr:
            return []
        png = fr[-1][1]
        best = []
        for k in (0, 1, 2):
            tx = _ocr_words(_variant(png, k))
            ls = []
            for l in tx.splitlines():
                l = re.sub(r"[|_~=\\\[\]{}<>]", " ", l)
                l = re.sub(r"\s+", " ", l).strip()
                if len(l) >= 3 and sum(c.isalnum() for c in l) >= 3:
                    ls.append(l[:90])
            if sum(len(x) for x in ls) > sum(len(x) for x in best):
                best = ls
        shutil.rmtree(os.path.dirname(png), ignore_errors=True) if os.path.isdir(os.path.dirname(png)) and os.path.dirname(png) != OUT else None
        return best[:8]
    except Exception:
        return []


def _sig(png):
    """A tiny fingerprint of a picture: an unchanged score bar is not read again."""
    try:
        from PIL import Image
        tt = _tight(png)
        im = Image.open(tt or png).convert("L").resize((160, 28))
        if tt:
            try: os.remove(tt)
            except OSError: pass
        return list(im.get_flattened_data() if hasattr(im, "get_flattened_data") else im.getdata())
    except Exception:
        return None


def _same(a, b):
    # unchanged = almost no pixel differs strongly (one changed digit shows as a small group of strongly different pixels)
    return bool(a and b and len(a) == len(b) and sum(1 for x, y in zip(a, b) if abs(x - y) > 28) < 4)


def _grab(path, ss, dur, box, full, outdir, width=1600, fps=1.0):
    """Pictures of an area of the screen: [(t, png)]. full=True one per second, False key frames only (fast; if they are rare, one per second)."""
    os.makedirs(outdir, exist_ok=True)
    for f in os.listdir(outdir):
        try: os.remove(os.path.join(outdir, f))
        except OSError: pass
    x, y, w, h = box
    crop = "crop=iw*%.4f:ih*%.4f:iw*%.4f:ih*%.4f,scale=%d:-2:flags=lanczos,format=gray,unsharp=5:5:0.8" % (w, h, x, y, width)
    for mode in ((True,) if full else (False, True)):
        for f in os.listdir(outdir):
            try: os.remove(os.path.join(outdir, f))
            except OSError: pass
        vf = (("fps=%g," % fps) if mode else "") + "showinfo," + crop
        cmd = ["nice", "-n", "4", "ffmpeg", "-hide_banner", "-loglevel", "info", "-y"]
        if not mode:
            cmd += ["-skip_frame", "nokey"]
        cmd += ["-ss", "%.2f" % max(0, ss), "-t", "%.2f" % dur, "-i", path, "-an", "-sn", "-vf", vf, "-fps_mode", "passthrough", os.path.join(outdir, "%06d.png")]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=max(180, dur * 2))
        except Exception:
            return []
        ts = [float(m) for m in re.findall(r"pts_time:\s*([\d.]+)", r.stderr or "")]
        files = sorted(f for f in os.listdir(outdir) if re.fullmatch(r"\d+\.png", f))
        out = [(max(0, ss) + ts[i], os.path.join(outdir, f)) for i, f in enumerate(files) if i < len(ts)]
        if mode or dur < 20 or len(out) >= dur / 4.0:
            return out                      # (key frames every 4 seconds or less are fine; rarer ones: look again with one picture per second)
    return out


def _cands(text):
    """All score guesses in a text: [(runs, wickets, kind)] kind 0 = normal, 1 = wickets first, 2 = loose."""
    text = text.replace("(", " ").replace(")", " ").replace("*", " ")
    text = re.sub(r"(?<![\d.])(\d) (\d) (\d) ?([/\-–]) ?(\d)(?!\d)", r"\1\2\3\4\5", text)          # big letters read digit by digit: "1 1 9 - 2" = 119-2
    text = re.sub(r"(?<![\d.])(\d) (\d) ?([/\-–]) ?(\d)(?!\d)", r"\1\2\3\4", text)
    text = re.sub(r"(?<![\d.\-/–])(\d{1,2})\s*OVERS?\b(?!\s*\d)", r"\1.0 ov", text, flags=re.I)          # "3 OVERS" (whole overs, no decimal) = 3.0
    sc = [(int(a), int(b), 0) for a, b in SC_RE.findall(text) if int(b) <= 10 and int(a) <= 800]
    sc += [(int(b), int(a), 1) for a, b in SC_REV.findall(text) if int(a) <= 10 and int(b) <= 800]
    sc = list(dict.fromkeys(sc))
    sc += [(int(a), int(b), 2) for a, b in SC_LOOSE.findall(text) if int(b) <= 10 and int(a) <= 800]
    return text, sc


def _pick(text, prev):
    """Text of the score area -> (runs, wickets, balls). What was seen before helps to ignore wrong numbers. None = not sure."""
    text, sc = _cands(text)
    if not sc:
        return None
    s = None
    jump_ov = None
    if prev:
        if prev[0] >= 100:                                    # the first digit of a big score is often not read (132 seen as 32): mend it with the last reading
            for c in list(sc):
                if c[2] != 2 and c[0] < prev[0] - 12:
                    for add in (100, 200, 300, 400):
                        if 0 <= c[0] + add - prev[0] <= 12:
                            sc.append((c[0] + add, c[1], c[2])); break
        good = [c for c in sc if 0 <= c[0] - prev[0] <= 12 and 0 <= c[1] - prev[1] <= 1]
        if good:
            s = min(good, key=lambda c: (c[2], (c[0] - prev[0]) + 10 * (c[1] - prev[1])))
        else:
            rest0 = SC_RE.sub(" ", SC_REV.sub(" ", text))
            ov0 = [int(x) * 6 + int(y) for x, y in OV_RE.findall(rest0) if int(x) <= 60]
            fit = []
            if prev[2] is not None:                    # many balls went by (video missing / slow reading): runs and wickets must fit the balls that passed
                for c in sc:
                    for ob in ov0:
                        nb_ = ob - prev[2]
                        if c[2] != 2 and 3 <= nb_ <= 150 and 0 <= c[0] - prev[0] <= 8 * nb_ and 0 <= c[1] - prev[1] <= min(10, nb_):
                            fit.append((c, ob))
            if fit:
                (s, jump_ov) = min(fit, key=lambda x: ((x[0][0] - prev[0]), x[0][2]))
            else:
                sc = [c for c in sc if c[2] == 0]          # a jump: only a clean "145/3" is believed (new innings)
                if not sc:
                    return None
                if prev[2] is not None and ov0 and min(ov0) >= prev[2] - 2:
                    return None                            # the overs did not start again: not a new innings, a wrong reading
    if s is None:
        nb = [int(x) * 6 + int(y) for x, y in OV_RE.findall(SC_RE.sub(" ", SC_REV.sub(" ", text))) if int(x) <= 60]
        balls = nb[0] if nb else None

        def plaus(c):
            if c[2] == 2:
                return 5
            bad = 0
            if balls is not None and c[1] > max(2, balls // 2):
                bad += 3                          # many wickets in a few balls: the numbers are the other way round
            if c[1] >= 10 and c[0] < 10:
                bad += 3
            if c[1] > c[0]:
                bad += 2                          # more wickets than runs: very rare, probably the other way round
            fm = CLIP.get("fmt")
            if fm is not None and c[2] != fm:
                bad += 2
            return bad + (0.1 if c[2] == 1 else 0)
        s = sorted(sc, key=plaus)[0]
        if s[2] == 2 and not prev:
            return None
        if s[2] in (0, 1) and any(c[2] != s[2] and c[2] != 2 for c in sc) and plaus(s) < 1:
            CLIP["fmt"] = s[2]
    rest = SC_RE.sub(" ", SC_REV.sub(" ", text))
    ov = [int(a) * 6 + int(b) for a, b in OV_RE.findall(rest) if int(a) <= 60]
    o = None
    if jump_ov is not None:
        o = jump_ov
    elif prev and prev[2] is not None:
        good = [c for c in ov if 0 <= c - prev[2] <= 2]
        if good:
            o = good[0]
    elif ov:
        o = ov[0]
    return (s[0], s[1], o)


def _continuous(rd, prev):
    return rd is not None and (prev is None or (0 <= rd[0] - prev[0] <= 12 and 0 <= rd[1] - prev[1] <= 1))


def _tight(png):
    """The small part of the picture around the score itself (found when the bar was located): the batting team's score and its overs,
    without the other numbers of the bar (the other team, the bowler's figures). None = not known."""
    ta, bx = CLIP.get("tight_abs"), CLIP.get("box")
    if not ta or not bx:
        return None
    try:
        from PIL import Image
        im = Image.open(png); W, H = im.size
        l, t, r, b = [(ta[0] - bx[0]) / bx[2], (ta[1] - bx[1]) / bx[3], (ta[2] - bx[0]) / bx[2], (ta[3] - bx[1]) / bx[3]]
        l, t, r, b = max(0, l), max(0, t), min(1, r), min(1, b)
        if r - l < 0.05 or b - t < 0.1:
            return None
        c = im.crop((int(l * W), int(t * H), int(r * W), int(b * H)))
        if c.size[0] < 700:
            f = 700.0 / c.size[0]; c = c.resize((700, max(20, int(c.size[1] * f))))
        try:
            from PIL import ImageOps
            c = ImageOps.expand(c, border=30, fill=c.getpixel((2, 2)))          # a margin around the text: the text reader is much steadier with it
        except Exception:
            pass
        out = png[:-4] + "_tt.png"
        c.save(out)
        return out
    except Exception:
        return None


def _read_frame(png, prev, text0=None):
    """One picture -> a score reading. Several looks of the picture are tried; when two looks agree (and fit the last reading) it is taken."""
    best, txt = None, ""
    tt = _tight(png)
    if tt:
        seen = {}
        balls_ = {}
        first = None
        for k, psm in ((0, "6"), (2, "6"), (1, "6"), (3, "6"), (0, "7"), (2, "7")):
            tx = _ocr(_variant(tt, k), psm=psm)
            rd = _pick(tx, prev)
            if rd is None:
                continue
            if first is None:
                first = (rd, tx)
            if prev is not None and not _continuous(rd, prev):
                continue
            key = (rd[0], rd[1])
            seen[key] = seen.get(key, 0) + 1
            if rd[2] is not None:
                balls_.setdefault(key, []).append(rd[2])
            if prev is not None and seen[key] >= 2:
                return rd, tx            # (the very first reading has no earlier one to check against: all the looks vote)
        if seen:
            key = max(seen, key=lambda x: (seen[x], x[0]))
            bl = balls_.get(key)
            return (key[0], key[1], max(set(bl), key=bl.count) if bl else None), ""
        if first and prev is None:
            best = first[0]
    for k in range(4):
        txt = text0 if (k == 0 and text0 is not None) else _ocr(_variant(png, k))
        rd = _pick(txt, prev)
        if rd is not None and best is None:
            best = rd
        if rd is not None and _continuous(rd, prev):
            return rd, txt
    rd = _pick(_ocr(png, psm="7"), prev)
    if rd is not None and _continuous(rd, prev):
        return rd, txt
    return best, txt


def _find_box(path, avail):
    """Find where the score is on the screen. -> (x, y, w, h) as fractions, or None. Looks at several moments with several looks,
    and if no score text is found anywhere it tries the usual places (the bottom and the top strip of the picture)."""
    CLIP["tight_abs"] = None
    tmp = os.path.join(OUT, "_clipdet")
    times = [t for t in (10, 25, 45, 70, 100, 150, 220, 300, 450, 700, 1000, 1500) if t < avail - 5][-6:]
    if len(times) < 3:
        return None
    frames = []
    for t in times:
        fr = _grab(path, t, 1.0, (0, 0, 1, 1), True, tmp + "_f", 1920)
        if fr:
            keep = "%s_%d.png" % (tmp, len(frames) + 1)
            try: shutil.copy(fr[0][1], keep); frames.append(keep)
            except OSError: pass
    try:
        from PIL import Image
    except Exception:
        return None
    hits = []
    regions = [(0.0, 0.60, 1.0, 0.40), (0.0, 0.0, 1.0, 0.30), (0.0, 0.0, 1.0, 1.0)]       # the bottom strip first (most boards), then the top strip, then the whole picture; enlarged (small score text)
    from concurrent.futures import ThreadPoolExecutor
    t_end = time.time() + 150                                  # never spend more than ~2.5 minutes looking

    seen_tok = []

    def look(job):
        src, rx, ry, rw, rh, n, k = job
        out = []
        for ln in _ocr(_variant(src, k), tsv=True).splitlines()[1:]:
            p = ln.split("\t")
            if len(p) < 12 or not p[11].strip():
                continue
            if len(seen_tok) < 400 and len(p[11].strip()) >= 2:
                seen_tok.append(p[11].strip())
            try:
                l, t_, wd, hh, txt = int(p[6]), int(p[7]), int(p[8]), int(p[9]), p[11].strip()
            except ValueError:
                continue
            tx_ = txt.replace(" ", "")
            m = SC_RE.fullmatch(tx_)
            rev = False
            if not m:
                m = SC_REV.fullmatch(tx_); rev = True
            if m and hh > 4:
                cw, ch = Image.open(src).size
                a_, b_ = int(m.group(1)), int(m.group(2))
                out.append((rx + rw * l / cw, ry + rh * t_ / ch, rx + rw * (l + wd) / cw, ry + rh * (t_ + hh) / ch, n, max(a_, b_), (b_ if rev else a_), (a_ if rev else b_)))
        return out

    def enough():
        if len({h[4] for h in hits}) < 3:
            return False
        return any(len({x[4] for x in hits if abs(x[0] - h[0]) < 0.12 and abs(x[1] - h[1]) < 0.04}) >= 3 for h in hits)
    for ri, (rx, ry, rw, rh) in enumerate(regions):
        jobs = []
        for n, png in enumerate(frames):
            im0 = Image.open(png); W, H = im0.size
            if (rw, rh) == (1.0, 1.0):
                src = png
            else:
                c = im0.crop((int(rx * W), int(ry * H), int((rx + rw) * W), int((ry + rh) * H)))
                f = 2400.0 / max(1, c.size[0])
                c = c.resize((2400, max(40, int(c.size[1] * f))))
                src = "%s_r%d.png" % (png[:-4], ri); c.save(src)
            for k in ((0, 2) if (rw, rh) != (1.0, 1.0) else (0, 1, 2)):
                jobs.append((src, rx, ry, rw, rh, n, k))
        with ThreadPoolExecutor(max_workers=int(E("CLIP_THREADS") or 3)) as ex:
            for res in ex.map(look, jobs):
                hits += res
        if enough() or time.time() > t_end:
            break
    by_feed = False
    fh = [h for h in hits if feed_match(h[6], h[7])]
    if fh:
        hits = fh                                          # only the numbers that agree with the live feed's score: that is the team score, not a bowler's figure
        by_feed = True
        print("Cricket clips: the score bar is the place that shows the feed's score (%s)" % feed_state_text(), flush=True)
    best, bn = None, 0
    groups = []
    for h in hits:
        near = {x[4] for x in hits if abs(x[0] - h[0]) < 0.12 and abs(x[1] - h[1]) < 0.04}
        groups.append((len(near), h))
    if groups:
        mx = max(g_[0] for g_ in groups)
        ok = [g_ for g_ in groups if g_[0] >= (1 if by_feed else 2)]
        top = max([g_[1][5] for g_ in ok] or [0])
        ok += [g_ for g_ in groups if g_[0] == 1 and g_[1][5] >= 40 and g_[1][5] >= 3 * max(top, 1) and g_[1][5] <= 800]     # a clearly bigger number seen once (a Test team score next to a bowler's figures that are read in every picture)                    # seen in at least two pictures; a Test board shows the team score and the bowler's figures: the biggest number wins
        if ok and by_feed:
            sts = FEED.get("states") or []
            bn, best = max(ok, key=lambda g_: (-min(abs(g_[1][6] - x[1]) + 5 * abs(g_[1][7] - x[2]) for x in sts), g_[0]))        # the reading closest to what the feed says: the team score
        elif ok:
            bn, best = max(ok, key=lambda g_: (g_[1][5], g_[0]))        # seen in nearly as many pictures: the biggest number is the team score (not a bowler's figure)
    if best is not None and bn == 1 and (best[5] >= 40 or by_feed):
        bn = 2                                           # chosen by the clearly-bigger-number rule above
    if best is not None and bn >= 2:
        x0, y0, x1, y1 = best[0], best[1], best[2], best[3]
        hh = max(0.03, y1 - y0)
        CLIP["tight_abs"] = (max(0.0, x0 - 0.03), max(0.0, y0 - 0.6 * hh), min(1.0, x1 + 0.25), min(1.0, y1 + 1.6 * hh))
        bx = max(0.0, x0 - 0.45); bw = min(1.0, x1 + 0.45) - bx
        by = max(0.0, y0 - 2.0 * hh); bh = min(1.0, y1 + 3.0 * hh) - by
        return (bx, by, bw, bh)
    # no score text found by itself: try the usual strips and keep the one where the score can be read in most pictures
    strips = [(0.0, 0.72, 1.0, 0.28), (0.0, 0.0, 1.0, 0.28), (0.0, 0.80, 1.0, 0.20), (0.0, 0.0, 1.0, 0.20), (0.0, 0.0, 0.6, 0.28), (0.0, 0.72, 0.6, 0.28)]
    score, pick = 0, None
    for st in strips:
        ok = 0
        for png in frames:
            im = Image.open(png); W, H = im.size
            c = im.crop((int(st[0] * W), int(st[1] * H), int((st[0] + st[2]) * W), int((st[1] + st[3]) * H)))
            c = c.resize((1600, max(40, int(1600 * c.size[1] / max(1, c.size[0])))))
            cp = png[:-4] + "_strip.png"
            c.save(cp)
            for k in (0, 1, 2):
                rd = _pick(_ocr(_variant(cp, k)), None)
                if rd and rd[2] is not None:
                    ok += 1; break
        if ok > score:
            score, pick = ok, st
    if pick and score >= 2:
        return pick
    try:
        words = list(dict.fromkeys(w for w in seen_tok if re.search(r"[A-Za-z0-9]", w)))[:30]
        print("Cricket clips: no score found in %d pictures. Text the bot could read: %s" % (len(frames), " | ".join(words) if words else "(nothing)"), flush=True)
    except Exception:
        pass
    return None


# ---------------------------- judging the readings ----------------------------

def _label(ev):
    return {"4": "FOUR", "6": "SIX", "W": "WICKET", "50": "FIFTY", "100": "CENTURY", "150": "150", "200": "DOUBLE CENTURY",
            "TOSS": "TOSS", "INN": "INNINGS BREAK", "BRK": (ev.get("xname") or "BREAK").upper(), "WIN": "MATCH RESULT"}.get(ev["kind"], ev["kind"])


def _sample(path, t, rd):
    """One reading is judged (it must be seen twice in a row); returns an event dict or None."""
    st = CLIP_ST
    conf = st["conf"]
    if rd is None:
        return None
    if conf is not None and rd[2] is None:
        rd = (rd[0], rd[1], conf[2])
    if conf is not None and rd == conf:
        st["pend"] = None
        return None
    pend = st["pend"]
    if pend and pend[0] == rd:
        pend[2] += 1
    else:
        pend = st["pend"] = [rd, (path, t), 1]
    cont = conf is None or (0 <= rd[0] - conf[0] <= 12 and 0 <= rd[1] - conf[1] <= 1)
    if not cont and conf[2] is not None and rd[2] is not None:
        nb_ = rd[2] - conf[2]
        if 3 <= nb_ <= 150 and 0 <= rd[0] - conf[0] <= 8 * nb_ and 0 <= rd[1] - conf[1] <= min(10, nb_):
            cont = True                                    # many balls went by: a real change, not a wrong reading
    if not cont and conf[2] is not None and rd[2] is not None and rd[2] >= conf[2] - 2:
        if pend[2] >= 8:                                   # the same "different" score again and again: the old reading was the wrong one, start again from this one
            print("Clips: the score reading is corrected %s -> %s" % (conf, rd), flush=True)
            st["conf"] = rd; st["pend"] = None; st["t_ov"] = None
            return None
        return None                                       # a different score at the same over count, seen only a few times: a wrong reading, ignore it
    if pend[2] < (2 if cont else 6):                       # a jump (new innings) must be seen many times before it is believed
        return None
    st["pend"] = None
    t0path, t0 = pend[1]
    old, st["conf"] = conf, rd
    if old is None:
        return None
    dr, dw = rd[0] - old[0], rd[1] - old[1]
    db = (rd[2] - old[2]) if (rd[2] is not None and old[2] is not None) else None
    if dr < 0 or dw < 0 or dr > 60 or dw > 4:
        st["t_ov"] = None                       # new innings or a wrong reading: start again
        return None
    jump = dr > 12 or dw > 1                    # several balls went by between two readings (an ad break, missing video, a slow reading)
    if jump:
        print("Clips: the score jumped %d/%d -> %d/%d between two readings (%d runs, %d wickets not seen ball by ball)" % (old[0], old[1], rd[0], rd[1], dr, dw), flush=True)
        if time.time() - st.get("jump_say", 0) > 90:
            st["jump_say"] = time.time()
            try:
                say("⚠️ <b>The score jumped</b> %d/%d → %d/%d between two readings.\nSome balls were not seen one by one (an ad break, missing video, or the bot was behind)%s." % (
                    old[0], old[1], rd[0], rd[1], ". A wicket clip is made for it" if dw >= 1 else ", so no clip for these runs"))
            except Exception:
                pass
    try:
        ob = st.setdefault("over", {"n": None, "syms": []})
        if old[2] is not None and rd[2] is not None and db is not None and db >= 1:
            oi = old[2] // 6
            if ob["n"] != oi:
                ob["n"] = oi; ob["syms"] = []
            if db == 1:
                ob["syms"].append("W" if dw else str(dr))
            else:
                ob["syms"] += ["?"] * min(db, 6)               # balls that were not seen one by one
            if rd[2] // 6 != oi and rd[2] % 6 != 0:              # a new over started inside this step
                ob["n"] = rd[2] // 6; ob["syms"] = ["?"] * (rd[2] % 6)
        elif db == 0 and dr > 0 and dw == 0:
            ob["syms"].append("+%d" % dr) if ob.get("n") is not None else None      # a wide / no ball / bye: the ball counter did not move
    except Exception:
        pass
    ov_txt = ("%d.%d" % divmod(rd[2], 6)) if rd[2] is not None else ""
    base = {"path": t0path, "t": t0, "ov": ov_txt, "score": "%d/%d" % (rd[0], rd[1]), "ball": rd[2], "runs": dr, "wk": rd[1]}
    ev = None
    if dw >= 1:
        gap = (t0 - st["t_ov"][1]) if (st["t_ov"] and st["t_ov"][0] == t0path) else None
        if gap is not None and 6 < gap < 240 and db == 0:
            ev = dict(base, kind="W", start=st["t_ov"][1] - 15, end=t0 + CLIP["post"], review=True)      # review: the ball was bowled long before the score changed
        else:
            ev = dict(base, kind="W", start=t0 - CLIP["wpre"] - (20 if jump else 0), end=t0 + CLIP["wpost"])
    elif dw == 0 and not jump and ((dr in (4, 6) and (db is None or db <= 2)) or (dr in (5, 7) and (db is None or db <= 1))):
        ev = dict(base, kind="4" if dr in (4, 5) else "6", start=t0 - CLIP["pre"], end=t0 + CLIP["post"])
        if db is not None and db >= 2:
            ev["strict"] = True                                   # 4 or 6 runs over two balls (4+2, 2+4...) : only the live feed can say if it was one boundary
    if db:
        st["t_ov"] = (t0path, t0)
    if rd[2] is not None:
        with CLIP_LOCK:
            for e in CLIP_EV:
                if e["path"] == t0path and e.get("until_ball") is not None and not e.get("end_known") and rd[2] >= e["until_ball"]:
                    e["end"] = max(t0, e["t"] + 5); e["end_known"] = True
    if ev:
        key = (ev["kind"], ev["score"])
        if key in st["seen"] and abs(st["seen"][key] - t0) < 300:
            return None                          # the same event twice (the same score can not happen twice)
        st["seen"][key] = t0
        try:
            cn = st.setdefault("counts", {}); cn[ev["kind"]] = cn.get(ev["kind"], 0) + 1
            st["lastev"] = "%s  %s%s" % (_label(ev), ev["score"], ("  (%s ov)" % ev["ov"]) if ev["ov"] else "")
        except Exception:
            pass
        if ev.get("ball") is not None and (ev["kind"], ev["ball"]) in EV_SEEN and ev["kind"] in ("4", "6", "W") and (ev["kind"], ev["ball"]) in FEED_MADE:
            return None                                              # the feed already made this clip
        last = st["last"].get((ev["path"], ev["kind"]))
        if last is not None and abs(last - ev["t"]) < 8:
            return None
        st["last"][(ev["path"], ev["kind"])] = ev["t"]
        if CLIP["after"] > 0 and ev.get("ball") is not None:
            ev["until_ball"] = ev["ball"] + CLIP["after"]            # the clip ends when the over counter shows this ball (1.1 + 2 = 1.3)
            ev["end_known"] = False
            ev["maxend"] = ev["t"] + CLIP["maxlen"]
    return ev


BAT2_RE = re.compile(r"(?<![A-Za-z])([A-Za-z][A-Za-z.'\-]{2,})\s*\*?\s+(\d{1,3})\s+(\d{1,3})(?![\d.])")
BAT2_SKIP = {"OVERS", "OVER", "CURRENT", "TARGET", "NEED", "RRR", "CRR", "REQ", "RUNS", "BALLS", "LEAD", "TRAIL", "TRAILS", "PARTNERSHIP", "EXTRAS", "TOSS"}


def bat_names_text(png):
    """Boards that show 'NAME 12 21' (runs, balls) without brackets: turned into '12(21)' so the same milestone logic works."""
    try:
        tx = _ocr_words(png)
        out = []
        for nm, a, b in BAT2_RE.findall(tx):
            if nm.upper() in BAT2_SKIP:
                continue
            if int(a) <= 400 and int(b) <= 400 and int(b) >= int(a) * 0.15 and int(b) <= int(a) * 4 + 8:
                out.append("%d(%d)" % (int(a), int(b)))
        return " ".join(out)
    except Exception:
        return ""


def _bat_sample(path, t, text):
    """A batsman's own figure 49(36): when it passes 50 / 100 / 150 / 200 a milestone event is made (it is seen again in the next picture
    first, so one wrong reading does not count). Best effort: it needs the batsmen's figures on the screen."""
    st = CLIP_ST
    pairs = [(int(a), int(b)) for a, b in BAT_RE.findall(text) if int(a) <= 400 and int(b) <= 400 and int(b) >= int(a) * 0.15]
    ev = None
    for m, (p0, t0, r_) in list(st["bpend"].items()):
        if any(m <= r <= r_ + 8 for r, b in pairs):
            del st["bpend"][m]
            if ("M", m) not in st["seen"] or abs(st["seen"][("M", m)] - t0) > 120:
                st["seen"][("M", m)] = t0
                sc = st["conf"]
                bb = next((b for (r, b) in pairs if m <= r <= r_ + 8), 0)
                ev = {"kind": str(m), "path": p0, "t": t0, "start": t0 - CLIP["mpre"], "end": t0 + CLIP["mpost"],
                      "ov": ("%d.%d" % divmod(sc[2], 6)) if sc and sc[2] is not None else "", "score": ("%d/%d" % (sc[0], sc[1])) if sc else "",
                      "ball": sc[2] if sc else None, "runs": 0, "wk": sc[1] if sc else 0, "bat": ("%d (%d balls)" % (r_, bb)) if bb else "%d" % r_}
        elif t - t0 > 12:
            del st["bpend"][m]
    hist = [p for h in st["bat"] for p in h]                       # the figures of the last few pictures (one wrong reading must not hide the batsman)
    for (r, b) in pairs:
        for (r0, b0) in hist:
            if r0 <= r <= r0 + 8 and b0 <= b <= b0 + 10 and r > r0:                                  # the same batsman a moment later
                for m in (50, 100, 150, 200):
                    if r0 < m <= r and m not in st["bpend"]:
                        st["bpend"][m] = (path, t, r)
    if pairs:
        st["bat"] = (st["bat"] + [pairs])[-5:]
    return ev


def _merge_milestones(path):
    """A 4 / 6 that makes the 50 / 100 is the same moment: only the milestone clip is kept and it names the shot."""
    with CLIP_LOCK:
        ms = [e for e in CLIP_EV if e["path"] == path and e["kind"] in ("50", "100", "150", "200")]
        for m in ms:
            for e in list(CLIP_EV):
                if e is not m and e["path"] == path and e["kind"] in ("4", "6") and abs(e["t"] - m["t"]) <= 6:
                    m["shot"] = e["kind"]; m["runs"] = e.get("runs", 0)
                    m["score"] = e["score"] or m["score"]; m["ov"] = e["ov"] or m["ov"]
                    CLIP_EV.remove(e)


BOARD_SKIP = BAT2_SKIP | {"AFTER", "FROM", "THE", "AND", "MATCH", "TOUR", "CUP", "WORLD", "ASIA", "STARS", "RISING", "SERIES", "LEAGUE", "STADIUM", "GROUND", "VS", "OVERS"}


def _split_rb(digits):
    """'317' -> (3, 17): runs and balls glued together: the split with a believable strike rate."""
    best = None
    for i in range(1, len(digits)):
        r, b = int(digits[:i]), int(digits[i:])
        if b < 1 or b > 300 or r > b * 4 + 6:
            continue
        sc = abs(math.log((r + 1.0) / b * 100 / 100.0 + 0.001))
        if best is None or sc < best[0]:
            best = (sc, r, b)
    return (best[1], best[2]) if best else None


def parse_board(texts, ev=None):
    """Several readings (different looks) of the score bar -> {team, score, overs, rr, bats, bowler, title}. The most common reading wins;
    whatever is not clear is left out."""
    from collections import Counter
    V = {"score": Counter(), "team": {}, "overs": Counter(), "rr": Counter(), "bowler": Counter(), "bat": {}}
    title = ""
    for tx in texts:
        t = re.sub(r"[|_~=\\\[\]{}<>°•*]", " ", tx)
        t = re.sub(r"[ \t]+", " ", t)
        flat = t.replace("\n", "  ")
        m = re.search(r"([A-Z][A-Za-z]*(?: ?[A-Z][A-Za-z]*){0,2}\.?)\s*(\d{1,3})\s*[-/]\s*(\d{1,2})(?!\d)", flat)
        if m and int(m.group(3)) <= 10:
            sc = "%s/%s" % (m.group(2), m.group(3))
            V["score"][sc] += 1
            nm = m.group(1).strip()
            if nm.upper() not in BOARD_SKIP and len(nm) >= 2:
                nm = re.sub(r"^([A-Z]{2,4})([A-Z])$", r"\1 \2", nm)
                V["team"].setdefault(sc, Counter())[nm] += 1
        m = re.search(r"(\d{1,2}\.\d)\s*(?:overs|ov)\b", flat, re.I)
        if m: V["overs"][m.group(1)] += 1
        m = re.search(r"(?:current|crr|rr)\D{0,6}(\d{1,2}\.\d{2})", flat, re.I) or re.search(r"(?<![\d.])(\d{1,2}\.\d{2})(?![\d.])", flat)
        if m: V["rr"][m.group(1)] += 1
        bw = None
        m = re.search(r"(?<![A-Za-z])([A-Z][A-Za-z.'\-]{2,})\s+(\d{1,2})\s*-\s*(\d{1,3})\s+(\d{1,2})(?:\.(\d))?(?![\d])", flat)
        if m and m.group(1).upper() not in BOARD_SKIP:
            ov = "%s.%s" % (m.group(4), m.group(5)) if m.group(5) else (("%s.%s" % (m.group(4)[0], m.group(4)[1])) if len(m.group(4)) == 2 and int(m.group(4)[1]) <= 5 else m.group(4))
            bw = m.group(1).upper()
            V["bowler"]["%s %s-%s (%s ov)" % (m.group(1), m.group(2), m.group(3), ov)] += 1
        for m in re.finditer(r"(?<![A-Za-z])([A-Z][A-Za-z.'\-]{2,})\s+(\d{1,3})(?:\s+(\d{1,3}))?(?![\d.\-])", flat):
            nm = m.group(1).upper()
            if nm in BOARD_SKIP or nm == bw:
                continue
            wgt = 1.0
            if m.group(3):
                r, b = int(m.group(2)), int(m.group(3))
            else:
                sp = _split_rb(m.group(2)) if len(m.group(2)) >= 2 else None
                if not sp: continue
                r, b = sp; wgt = 0.4                       # glued digits: a guess, counts less
            if b < 1 or b > 300 or r > 400 or r > b * 4 + 6:
                continue
            V["bat"].setdefault(nm, Counter())[(r, b)] += wgt
        if not title:
            for ln in t.splitlines():
                ln = ln.strip()
                if len(ln) > 22 and sum(c.isupper() for c in ln) > len(ln) * 0.5 and re.search(r"CUP|MATCH|SERIES|LEAGUE|TOUR|TROPHY|\bV\b|\bvs\b|WORLD|T20|ODI|TEST", ln, re.I):
                    mm = re.search(r"[A-Z0-9][A-Z0-9 :,.\-]{15,}[A-Za-z0-9]", ln)
                    title = (mm.group(0) if mm else ln)[:90]
                    break
    out = {"bats": []}
    top = lambda c: max(c, key=lambda k: (c[k], len(str(k)))) if c else None
    sc = top(V["score"])
    if sc:
        out["score"] = sc
        tm = top(V["team"].get(sc) or Counter())
        if tm and tm.upper() not in BOARD_SKIP:
            out["team"] = tm
    for k in ("overs", "rr", "bowler"):
        v = top(V[k])
        if v: out[k] = v
    teams = {t.replace(" ", "").upper() for c in V["team"].values() for t in c}
    for tn in list(V["bat"]):
        if tn in teams or any(tn.startswith(x) and len(tn) - len(x) <= 1 for x in teams if len(x) >= 3):
            V["bat"].pop(tn, None)
    for bwc in [b for b in V["bowler"] if b.split()[0].upper() in teams]:
        del V["bowler"][bwc]
    v = top(V["bowler"])
    if v: out["bowler"] = v
    else: out.pop("bowler", None)
    if out.get("bowler"):
        bwn = out["bowler"].split()[0].upper()
        V["bat"].pop(bwn, None)
    names = sorted(V["bat"], key=lambda n: -sum(V["bat"][n].values()))
    merged = []
    import difflib
    for n in names:                                         # one name read two ways (ALIKHIL / AvKHIL): the more common one is kept
        if any(difflib.SequenceMatcher(None, n, m).ratio() > 0.72 for m, _ in merged):
            continue
        merged.append((n, V["bat"][n]))
    used = set()
    for n, c in merged:
        r_b = top(c)
        if r_b in used:
            continue
        used.add(r_b)
        out["bats"].append((n, r_b[0], r_b[1]))
        if len(out["bats"]) == 2: break
    if title:
        title = re.sub(r"^(?:[A-Z0-9]{1,2}\s+)+", "", title)
        out["title"] = title
    return out


def scoreboard_info(path, t, ev=None):
    info = _scoreboard_info_screen(path, t, ev)
    try:
        fi = feed_info()
        if fi.get("title"):
            info["title"] = fi["title"]                 # the match name from the feed: the screen's ticker line is not a title
        if fi.get("team"):
            info["team"] = fi["team"]
    except Exception:
        pass
    return info


def board_card(info, ev=None):
    """The parsed bar as lines of text for the owner message / the caption."""
    L = []
    sc = (ev and ev.get("score")) or info.get("score") or ""
    ov = (ev and ev.get("ov")) or info.get("overs") or ""
    parts = [((info["team"] + "  ") if info.get("team") else "") + (("<b>%s</b>" % sc) if sc else "")]
    if ov: parts.append("%s ov" % ov)
    if info.get("rr"): parts.append("RR %s" % info["rr"])
    parts = [p.strip() for p in parts if p.strip()]
    if parts:
        L.append("📊 " + "  ·  ".join(parts))
    if info.get("bats"):
        L.append("🏏 " + "  ·  ".join("%s <b>%d</b> (%d)" % (esc(n), r, b) for n, r, b in info["bats"]))
    if info.get("bowler"):
        L.append("🎯 " + esc(info["bowler"]))
    if info.get("title"):
        L.append("🏆 <i>%s</i>" % esc(info["title"]))
    return L


def _scoreboard_info_screen(path, t, ev=None):
    box = CLIP.get("wide") or CLIP.get("box")
    if not box or not os.path.exists(path):
        return {"bats": []}
    d = os.path.join(OUT, "_clipsb_%d" % int(t))
    try:
        fr = _grab(path, max(0, t), 2, box, True, d, 1800)
        if not fr:
            return {"bats": []}
        png = fr[-1][1]
        texts = [_ocr_words(_variant(png, k)) for k in (2, 0, 1, 3)] + [_ocr_words(_variant(png, 2), psm="11"), _ocr_words(_variant(png, 1), psm="11")]
        return parse_board(texts, ev)
    except Exception:
        return {"bats": []}
    finally:
        shutil.rmtree(d, ignore_errors=True)


def clip_notice(ev):
    """Tells the owner what was detected, with everything the score bar shows at that moment (team, score, over, batsmen, bowler)."""
    try:
        em = {"4": "4️⃣", "6": "6️⃣", "W": "🔴"}.get(ev["kind"], "🏆")
        info = scoreboard_info(ev["path"], ev["t"] + 1, ev)
        lines = board_card(info, ev)
        # (batsman / bowler lines stay in the owner message only: a misread name must not go to the public channel)
        say("%s <b>%s detected</b>  ·  match time %s\n━━━━━━━━━━━━━━\n%s\n━━━━━━━━━━━━━━\n🎞 Clip %ds, ready after the end part is recorded." % (
            em, _label(ev), mmss(ev["t"]), "\n".join(lines) or "(the score bar text is not clear)", int(ev["end"] - ev["start"])))
    except Exception:
        pass


def clip_analyze(path, t_from, t_to, full, final=False, avail=None):
    """Reads the score between two moments of a video and queues clips for 4 / 6 / wicket / 50 / 100.
    avail = how much of the video exists (a finished file: all of it): clips that are ready are cut after every piece, not at the end."""
    if t_to - t_from < 3 or not CLIP["box"]:
        return
    tmp = os.path.join(OUT, "_clipfr")
    step = 30 if full else 150
    from concurrent.futures import ThreadPoolExecutor
    t = t_from
    while t < t_to and (final or not stop.is_set()):
        d = min(step, t_to - t)
        fps_ = CLIP.get("fps", 0.5) if CLIP.get("lag", 0) < 150 else 0.2          # far behind the live edge: look less often, catch up first
        frames = _grab(path, t, d, CLIP["box"], full, tmp, fps=fps_)
        wide = _grab(path, t, d, CLIP["wide"], full, tmp + "_w", 1800, fps=fps_) if CLIP["wide"] else []
        # the picture reading is done on several cores; unchanged pictures are not read again
        sigs, texts, todo = [], {}, []
        for i, (ft, png) in enumerate(frames):
            sg = _sig(png); sigs.append(sg)
            if i > 0 and _same(sg, sigs[i - 1]) and (i % 3) != 0:        # looks unchanged: not read again (but every third picture is read anyway)
                texts[i] = None
            else:
                todo.append(i)
        with ThreadPoolExecutor(max_workers=int(E("CLIP_THREADS") or 2)) as ex:
            res = list(ex.map(lambda i: _ocr(frames[i][1]), todo))
            for i, tx in zip(todo, res):
                texts[i] = tx
            wtexts = {}
            if wide and len(wide) == len(frames):
                wtodo = [i for i in todo if i % 4 == 0]                 # the wide band (batsmen) is heavy: only every fourth picture, the names every twelfth
                for i, tx in zip(wtodo, ex.map(lambda i: _ocr(wide[i][1]) + ((" " + bat_names_text(wide[i][1])) if i % 12 == 0 else ""), wtodo)):
                    wtexts[i] = tx
        last_txt, last_w = None, ""
        for i, (ft, png) in enumerate(frames):
            CLIP_ST["frames"] += 1
            if texts.get(i) is None and last_txt is not None:
                txt, rd = last_txt[0], last_txt[1]
            else:
                prev = CLIP_ST["conf"] or (CLIP_ST["pend"] and CLIP_ST["pend"][0])
                if CLIP_ST.get("none_run", 0) >= 8:
                    prev = None                                # nothing fits the last reading for a while: read the picture fresh
                rd, txt = _read_frame(png, prev, texts.get(i))
                rd = feed_fix(rd)
                CLIP_ST["none_run"] = 0 if rd is not None else CLIP_ST.get("none_run", 0) + 1
                last_txt = (txt, rd)
            if rd is not None:
                CLIP_ST["ok"] += 1
            if i in wtexts:
                last_w = wtexts[i]
            for ev in (_sample(path, ft, rd), (_bat_sample(path, ft, last_w) if wtexts else None)):
                if ev:
                    if ev.get("kind") in ("4", "6", "W") and feed_first():
                        _m = re.match(r"(\d+)/(\d+)", ev.get("score") or "")
                        known = feed_knows(int(_m.group(1)), int(_m.group(2))) if _m else True
                        if known:
                            feed_note_event(ev, mark=False)           # the live feed makes these clips; the screen only teaches the two clocks
                        if known and ev.get("ball") is not None:
                            SCREEN_T[(ev["kind"], ev["ball"])] = (ev["path"], ev["t"])
                        if known:
                            SCREEN_EVS.append({"kind": ev["kind"], "path": ev["path"], "t": ev["t"], "score": ev.get("score", ""), "used": False})
                            del SCREEN_EVS[:-60]
                        else:
                            print("Screen reading %s is not a score the feed had: not used" % ev.get("score", "?"), flush=True)
                        try:
                            cn = CLIP_ST.get("counts", {}); cn[ev["kind"]] = max(0, cn.get(ev["kind"], 0) - 1)
                            CLIP_ST["seen"].pop((ev["kind"], ev["score"]), None); CLIP_ST["last"].pop((ev["path"], ev["kind"]), None); CLIP_ST["lastev"] = ""
                        except Exception:
                            pass
                        print("Screen saw %s at %s (%s): the live feed makes this clip" % (_label(ev), mmss(ev["t"]), ev["score"]), flush=True)
                        continue
                    if feed_hold(ev):
                        continue                                  # held until the live feed has said what that ball was
                    clip_release(ev)
        try:
            sm = [(i, texts[i]) for i in sorted(texts) if texts[i]][:3]
            print("Clips: looked at %d-%ds: score read in %d of %d pictures | text seen: %s | last reading: %s" % (
                t, t + d, CLIP_ST["ok"], CLIP_ST["frames"], " ## ".join(repr(x[1].strip()[:40]) for x in sm) or "(nothing)",
                CLIP_ST["conf"]), flush=True)
        except Exception:
            pass
        t += d
        _merge_milestones(path)
        if avail:
            clip_flush(path, avail, final=False)


# ---------------------------- cutting and sending ----------------------------

CLIPS_ONLY = E("CLIPS_ONLY") == "1"            # clip bot: only the clips are kept, the recording itself is not uploaded
CLIP_CHAT = E("CLIP_CHAT") or (CHAT if CLIPS_ONLY else "")     # channel or group that gets the clips (the bot must be allowed to post there)
CLIP_MAX = int(float(E("CLIP_MAX_MB") or 49) * 1024 * 1024)       # Bot API video limit is 50 MB


def tg_post(chat, text):
    if not TOKEN or DRY:
        print("[clips chat]", text[:100]); return True
    try:
        data = urllib.parse.urlencode({"chat_id": chat, "text": text, "parse_mode": "HTML", "disable_web_page_preview": "true"}).encode()
        r = json.load(urllib.request.urlopen(urllib.request.Request("%s/bot%s/sendMessage" % (E("TG_API") or "https://api.telegram.org", TOKEN), data), timeout=60))
        return bool(r.get("ok"))
    except Exception as e:
        print("Message to the clips chat failed:", mask(repr(e))[:120], flush=True)
        return False


def video_info(path):
    """(seconds, display width, height) - the display width counts a non-square pixel shape, so the preview has the right ratio."""
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height,sample_aspect_ratio:format=duration", "-of", "json", path],
                           capture_output=True, text=True, timeout=60)
        j = json.loads(r.stdout or "{}"); st = (j.get("streams") or [{}])[0]
        w, h = int(st.get("width") or 0), int(st.get("height") or 0)
        sar = str(st.get("sample_aspect_ratio") or "1:1")
        try:
            a, b = sar.split(":"); f = float(a) / float(b) if float(b) else 1.0
        except Exception:
            f = 1.0
        if f > 0.1 and abs(f - 1.0) > 0.02:
            w = int(round(w * f / 2.0)) * 2
        return float((j.get("format") or {}).get("duration") or 0), w, h
    except Exception:
        return 0.0, 0, 0


def make_thumb(path, at):
    """A sharp picture from the moment of the event (not the first frame, which can be black)."""
    out = path[:-4] + "_thumb.jpg"
    for off in (at, at + 3, max(0.5, at - 3), 1.0):
        try:
            subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-ss", "%.2f" % max(0, off), "-t", "4", "-i", path, "-vf", "thumbnail=60,scale=320:-2", "-frames:v", "1", "-q:v", "5", out],
                           capture_output=True, timeout=60)
            if os.path.exists(out) and os.path.getsize(out) > 3000:
                return out
        except Exception:
            pass
    return None


def make_caption(ev, secs):
    shot = {"4": "FOUR", "6": "SIX"}.get(ev.get("shot", ""), "")
    kind = ev["kind"]
    if kind == "4":
        head, tags = "🏏 <b>FOUR!</b>", "#FOUR"
    elif kind == "6":
        head, tags = "🚀 <b>SIX!</b>", "#SIX"
    elif kind == "W":
        head, tags = ("☝️ <b>WICKET! (LBW)</b>", "#WICKET #LBW") if ev.get("lbw") else ("☝️ <b>WICKET!</b>", "#WICKET")
    elif kind == "TOSS":
        head, tags = "🪙 <b>TOSS</b>", "#Toss"
    elif kind == "INN":
        head, tags = "🏁 <b>INNINGS BREAK</b>", "#InningsBreak"
    elif kind == "BRK":
        head, tags = "☕ <b>%s</b>" % esc(ev.get("xname") or "BREAK").upper(), "#" + re.sub(r"\W", "", ev.get("xname") or "Break")
    elif kind == "WIN":
        head, tags = "🏆 <b>MATCH RESULT</b>", "#MatchResult"
    else:
        head = "🎯 <b>%s!</b>" % _label(ev)
        tags = "#" + _label(ev).replace(" ", "")
        if shot:
            head += "  <i>(with a %s)</i>" % shot.lower(); tags += " #" + shot
    ov = ev["ov"] or ""
    lines = [head + (("  ·  Over %s" % ov) if ov else ""), "━━━━━━━━━━━━━━"]
    if ev["score"]:
        extra = ""
        if kind in ("4", "6") and ev.get("runs"):
            extra = "  <i>(+%d)</i>" % ev["runs"]
        if kind == "W":
            extra = "  <i>(%d down)</i>" % ev["wk"] if ev.get("wk") else ""
        lines.append("📊 <b>Score</b>  %s%s" % (ev["score"], extra))
    for l in (ev.get("info") or [])[:2]:
        lines.append(l)
    if ev.get("feed_text"):
        lines.append("💬 <i>%s</i>" % esc(ev["feed_text"]))
    if ev.get("bat"):
        lines.append("🏏 <b>Batsman</b>  %s" % ev["bat"])
    if ev.get("review"):
        lines.append("📺 <b>Decision after review</b>")
    clip = "🎞 <b>Clip</b>  %s" % mmss(secs)
    if ARCHIVE or CLIPS_FILE[0]:
        clip += "  ·  ⏱ Video %s" % mmss(ev["t"])
    lines += [clip, "━━━━━━━━━━━━━━", tags + ("  #Over%s" % ov.replace(".", "_") if ov else ""), CLIP_TAG]
    return "\n".join(lines)[:1000]


CLIPS_FILE = [False]                            # set by the clip bot when the source is a video file (the video time is then shown)


def tg_send_video(chat, path, caption, secs, w=0, h=0, thumb=None):
    """Send a clip as a Telegram video (Bot API: up to 50 MB): with its size, length and a real preview picture."""
    if DRY or not TOKEN:
        print("[clips chat] video", os.path.basename(path), caption.replace("\n", " | ")[:120]); return True
    j, r = {}, None
    for attempt in range(3):
        cmd = ["curl", "-sS", "-m", "900", "-X", "POST", "%s/bot%s/sendVideo" % (E("TG_API") or "https://api.telegram.org", TOKEN),
               "--form-string", "chat_id=" + str(chat), "--form-string", "caption=" + caption, "--form-string", "parse_mode=HTML",
               "--form-string", "duration=%d" % int(secs), "--form-string", "supports_streaming=true"]
        if w and h:
            cmd += ["--form-string", "width=%d" % w, "--form-string", "height=%d" % h]
        cmd += ["-F", "video=@" + path]
        if thumb and os.path.exists(thumb):
            cmd += ["-F", "thumbnail=@" + thumb]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=920)
            j = json.loads(r.stdout or "{}")
        except Exception as e:
            j = {"description": repr(e)[:80]}
        if j.get("ok"):
            return True
        wait = (j.get("parameters") or {}).get("retry_after")
        print("sendVideo to the clips chat failed:", mask(str(j.get("description") or (r.stderr if r else "")))[:140], flush=True)
        time.sleep(min(int(wait), 60) if wait else 3 + attempt * 4)
    return False


TG_SESS = {"s": ""}
TG_LOCK = threading.Lock()


def tg_send_big(chat, path, caption, secs, w=0, h=0, thumb=None):
    """Original quality, up to 2 GB, as a normal video: through Telegram's own protocol (needs API_ID + API_HASH and telethon).
    Works for a public channel/group (@name) and for chats the bot can see; otherwise it returns False."""
    api_id, api_hash = E("API_ID"), E("API_HASH")
    if DRY or not (api_id and api_hash and TOKEN):
        return False
    try:
        from telethon import TelegramClient
        from telethon.sessions import StringSession
        from telethon.tl.types import DocumentAttributeVideo
    except Exception:
        print("Big clips: telethon is not installed", flush=True)
        return False
    import asyncio

    async def par_upload(c, conns):
        """The file in 512 KB parts, `conns` of them on their way at the same time (not one after another): original quality, a fraction of the time."""
        import random
        from telethon.tl.functions.upload import SaveBigFilePartRequest
        from telethon.tl.types import InputFileBig
        size = os.path.getsize(path)
        PART = 512 * 1024
        total = (size + PART - 1) // PART
        fid = random.randrange(-2 ** 63, 2 ** 63)
        sem = asyncio.Semaphore(conns)
        st = {"done": 0, "step": 0}
        t0 = time.time()
        f = open(path, "rb")

        async def one(i):
            async with sem:
                f.seek(i * PART); data = f.read(PART)
                for att in range(4):
                    try:
                        if await c(SaveBigFilePartRequest(fid, i, total, data)):
                            break
                    except Exception:
                        if att == 3:
                            raise
                    await asyncio.sleep(1 + att)
                else:
                    raise RuntimeError("part %d was not accepted" % i)
                st["done"] += len(data)
                if size and st["done"] * 10 // size > st["step"]:
                    st["step"] = st["done"] * 10 // size
                    print("Upload %s: %d%% (%s of %s, %.1f MB/s, %d in parallel)" % (os.path.basename(path), st["step"] * 10, human(st["done"]), human(size), st["done"] / 1e6 / max(1, time.time() - t0), conns), flush=True)
        tasks = [asyncio.ensure_future(one(i)) for i in range(total)]
        try:
            await asyncio.wait_for(asyncio.gather(*tasks), 90 + size / 1e6 * 4)         # slower than 0.25 MB/s: give up, the normal upload takes over
        except BaseException:
            for t in tasks:
                t.cancel()
            raise
        finally:
            f.close()
        return InputFileBig(fid, total, os.path.basename(path))

    async def tg_client():
        """One bot login for the whole run (the session is kept): a new login for every clip makes Telegram answer 'internal issues' (ImportBotAuthorization)."""
        s = TG_SESS["s"]
        if s:
            c = TelegramClient(StringSession(s), int(api_id), api_hash)
            await c.connect()
            if await c.is_user_authorized():
                return c
            await c.disconnect()
        last = None
        for att in range(6):
            c = TelegramClient(StringSession(), int(api_id), api_hash)
            try:
                await c.start(bot_token=TOKEN)
                TG_SESS["s"] = c.session.save()
                return c
            except Exception as e:
                last = e
                print("Telegram login try %d failed (%s), waiting" % (att + 1, mask(repr(e))[:100]), flush=True)
                try: await c.disconnect()
                except Exception: pass
                await asyncio.sleep(5 * (att + 1))
        raise last

    async def go():
        c = await tg_client()
        try:
            ent = chat if str(chat).startswith("@") else int(chat)
            peer = await c.get_input_entity(ent)
            _t0 = time.time(); _last = [0]
            def _prog(sent, total):
                if total and sent * 10 // total > _last[0]:
                    _last[0] = sent * 10 // total
                    print("Upload %s: %d%% (%s of %s, %.1f MB/s)" % (os.path.basename(path), _last[0] * 10, human(sent), human(total), sent / 1e6 / max(1, time.time() - _t0)), flush=True)
            try:
                import cryptg  # noqa
            except Exception:
                print("Upload: cryptg is missing, so the upload is slow", flush=True)
            handle = None
            conns = int(E("CLIP_CONNS") or 12)
            if conns > 1 and os.path.getsize(path) > 10 * 1024 * 1024:
                try:
                    handle = await par_upload(c, conns)
                except BaseException as e:
                    if isinstance(e, asyncio.CancelledError):
                        raise
                    print("Parallel upload did not work (%s): the normal upload is used" % mask(repr(e))[:120], flush=True)
            await c.send_file(peer, handle or path, caption=caption, parse_mode="html", supports_streaming=True, mime_type="video/mp4", progress_callback=None if handle else _prog,
                              thumb=thumb if thumb and os.path.exists(thumb) else None,
                              attributes=[DocumentAttributeVideo(duration=int(secs), w=w or 1280, h=h or 720, supports_streaming=True)])
        finally:
            await c.disconnect()
    for attempt in range(3):
        try:
            if not TG_SESS["s"]:
                with TG_LOCK:                                # the first login only once, even when several clips are waiting
                    if not TG_SESS["s"]:
                        async def _login():
                            c0 = await tg_client()
                            await c0.disconnect()
                        asyncio.run(_login())
            asyncio.run(asyncio.wait_for(go(), 1800))
            return True
        except Exception as e:
            print("Big clip upload failed (try %d of 3):" % (attempt + 1), mask(repr(e))[:160], flush=True)
            time.sleep(10 * (attempt + 1))
    return False


def shrink_clip(path, secs):
    """Last way to keep it a video: re-encode to fit the 50 MB limit."""
    out = path[:-4] + "_small.mp4"
    vb = max(300_000, int(CLIP_MAX * 8 / max(secs, 1) * 0.92) - 110_000)
    vf = ["-vf", "scale=-2:720,setsar=1"] if vb < 1_200_000 else ["-vf", "setsar=1"]
    cmd = ["nice", "-n", "10", "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", path, "-map", "0:v:0", "-map", "0:a:0?", "-c:v", "libx264", "-preset", "veryfast",
           "-b:v", str(vb), "-maxrate", str(int(vb * 1.3)), "-bufsize", str(vb * 2)] + vf + ["-c:a", "aac", "-b:a", "96k", "-movflags", "+faststart", out]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=1200)
    except Exception as e:
        print("Shrinking the clip failed:", repr(e)[:100], flush=True); return None
    if r.returncode != 0 or not os.path.exists(out) or os.path.getsize(out) > CLIP_MAX:
        print("Shrinking the clip failed:", (r.stderr or "")[-120:], flush=True)
        try: os.remove(out)
        except OSError: pass
        return None
    return out


def clip_to_chat(path, cap, secs, w=0, h=0, thumb=None):
    """A clip always goes as a real video: small = Bot API, big = original quality over MTProto, else shrunk to 50 MB."""
    if os.path.getsize(path) <= CLIP_MAX:
        return tg_send_video(CLIP_CHAT, path, cap, secs, w, h, thumb)
    if tg_send_big(CLIP_CHAT, path, cap, secs, w, h, thumb):
        return True
    small = shrink_clip(path, secs)
    if small:
        print("The clip was shrunk to %s to fit 50 MB" % human(os.path.getsize(small)), flush=True)
        ok = tg_send_video(CLIP_CHAT, small, cap + "\n<i>(compressed)</i>", secs, w, h, thumb)
        if not DRY:
            try: os.remove(small)
            except OSError: pass
        return ok
    return False


def clip_deliver(item):
    out, thumb, cap, secs, w, h, ev = item
    try:
        done = False
        if CLIP_CHAT:
            done = clip_to_chat(out, cap, secs, w, h, thumb)
            if done:
                print("Clip sent to the clips chat:", os.path.basename(out), flush=True)
            else:
                print("The clip could not be sent as a video, using a Gofile link as the last way", flush=True)
        if not done:
            ok, link, err = gofile_upload(out)
            if ok:
                text = "%s\n⬇️ <a href=\"%s\">Clip</a>  ·  %s" % (cap, link or S["page"], human(os.path.getsize(out)))
                (tg_post(CLIP_CHAT, text) if CLIP_CHAT else say(text))
                done = True
            else:
                print("Clip upload failed:", err, flush=True)
        if done:
            CLIP_ST["sent"] += 1
            CLIP_ST["kinds"].append(ev["kind"])
    except Exception as e:
        print("Clip delivery error:", mask(repr(e))[:150], flush=True)
    finally:
        if not DRY:
            for f in (out, thumb):
                try:
                    if f: os.remove(f)
                except OSError:
                    pass


def _uploader():
    while True:
        item = CLIP_Q.get()
        try:
            clip_deliver(item)
        finally:
            CLIP_Q.task_done()


def clip_cut(ev, avail):
    """Cut the clip (fast, no re-encoding), then hand it to the sender so the next clip can be cut at once."""
    path = ev["path"]
    start = max(0.0, ev["start"]); end = min(avail, ev["end"]) if avail else ev["end"]
    if end - start < 3 or not os.path.exists(path):
        return
    CLIP_ST["n"] += 1
    try:
        ev["feed_text"] = ev.get("feed_text") or feed_text_for(ev)
    except Exception:
        pass
    os.makedirs(os.path.join(OUT, "_clips"), exist_ok=True)
    out = os.path.join(OUT, "_clips", "%s_%02d_over_%s.mp4" % (_label(ev).replace(" ", ""), CLIP_ST["n"], (ev["ov"] or "x").replace(".", "-")))
    cmd = ["nice", "-n", "5", "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-ss", "%.2f" % start, "-i", path, "-t", "%.2f" % (end - start),
           "-map", "0:v:0", "-map", "0:a:0?", "-c:v", "copy", "-c:a", "aac", "-b:a", "128k", "-avoid_negative_ts", "make_zero", "-movflags", "+faststart", out]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    except Exception as e:
        print("Clip cut failed:", repr(e)[:100], flush=True); return
    if r.returncode != 0 or not os.path.exists(out) or os.path.getsize(out) < 20000:
        print("Clip cut failed:", (r.stderr or "")[-150:], flush=True); return
    secs, w, h = video_info(out)
    secs = secs or (end - start)
    thumb = make_thumb(out, min(max(0.5, ev["t"] - start), max(0.5, secs - 1)))
    CLIP_Q.put((out, thumb, make_caption(ev, secs), secs, w, h, ev))
    print("Clip cut: %s (%s, %d s), %d waiting to be sent" % (os.path.basename(out), human(os.path.getsize(out)), secs, CLIP_Q.qsize()), flush=True)
    if CLIP_UP[0] is None:
        CLIP_UP[0] = [threading.Thread(target=_uploader, daemon=True) for _ in range(max(1, E_INT("CLIP_UPLOADS", 3)))]
        for th in CLIP_UP[0]: th.start()


def clip_drain(limit=3600):
    """Wait until every clip has been sent."""
    t0 = time.time()
    while CLIP_Q.unfinished_tasks and time.time() - t0 < limit:
        time.sleep(1)


def clip_flush(path, avail, final=False):
    with CLIP_LOCK:
        for e in CLIP_EV:
            if e["path"] == path and e.get("until_ball") is not None and not e.get("end_known") and (final or avail >= e["maxend"]):
                e["end"] = min(e["maxend"], avail) if final else e["maxend"]; e["end_known"] = True      # the counter never got there: stop at the maximum
        ready = [e for e in CLIP_EV if e["path"] == path and (final or (e["end"] <= avail and e.get("end_known", True)))]
        for e in ready:
            CLIP_EV.remove(e)
    for e in sorted(ready, key=lambda x: x["t"]):
        clip_cut(e, avail)


def clip_diag(path):
    """Why can the bot not see a picture? What is in the file the recorder wrote (video track, picture errors)."""
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-show_entries", "stream=index,codec_type,codec_name,width,height,duration,nb_read_packets", "-count_packets",
                            "-of", "compact=p=0:nk=0", "-read_intervals", "%+30", path], capture_output=True, text=True, timeout=60)
        print("Clips: the file has: " + " ; ".join((r.stdout or "?").strip().splitlines()[:4]), flush=True)
        r2 = subprocess.run(["ffmpeg", "-v", "error", "-t", "20", "-i", path, "-map", "0:v:0", "-f", "null", "-"], capture_output=True, text=True, timeout=90)
        err = (r2.stderr or "").strip().splitlines()
        print("Clips: reading 20 s of the picture: %s" % (mask(err[-1])[:200] if err else "no error"), flush=True)
        return (r2.stderr or "")
    except Exception as e:
        print("Clips: file check failed:", mask(repr(e))[:120], flush=True)
        return ""


def clip_detect(path, avail):
    if CLIP["box"] or time.time() < CLIP["next_try"] or CLIP["tries"] >= 10:
        return
    if E("FEED_URL").startswith("http") and not FEED.get("states"):
        for _ in range(20):                                # the live feed tells where the real score is: give it a few seconds to answer
            if FEED.get("states") or stop.is_set():
                break
            time.sleep(1)
    CLIP["tries"] += 1
    CLIP["next_try"] = time.time() + (60 if CLIP["tries"] < 6 else 180)
    box = CLIP.get("manual") or _find_box(path, avail)
    if CLIP.get("manual"):
        CLIP["tight_abs"] = None
    if not box:
        print("Cricket clips: score bar not found yet (try %d)" % CLIP["tries"], flush=True)
        if CLIP["tries"] in (2, 5):
            clip_diag(path)
        if CLIP["tries"] >= 10 and not CLIP["msg_fail"]:
            CLIP["msg_fail"] = True
            say("🏏 <b>Clips: I could not find the score on the screen.</b>\nThe recording is not affected, only the clips are off for this run. (The score must be visible as text like <code>145/3</code> and <code>12.3</code>.)\nYou can show me the place by hand: start again and write <code>box 0 85 50 12</code> with the link = from the left 0%, from the top 85%, width 50%, height 12% of the picture.")
        return
    CLIP["box"] = box
    x, y, w, h = box
    CLIP["wide"] = (0.0, y, 1.0, min(1.0 - y, h)) if w < 0.95 else None          # the same band over the whole width: the batsmen's figures (50 / 100)
    for d in glob.glob(os.path.join(OUT, "_clipdet*")):
        shutil.rmtree(d, ignore_errors=True) if os.path.isdir(d) else os.remove(d)
    print("Cricket clips: score area found at x=%.2f y=%.2f w=%.2f h=%.2f" % box, flush=True)
    if CLIP.get("announced"):
        return                                                # found again later (the picture changed): no new pictures in the chat
    CLIP["announced"] = True
    try:
        fr = _grab(path, max(0, avail - 8), 3, box, True, os.path.join(OUT, "_clipfr"))
        rd = _read_frame(fr[-1][1], None)[0] if fr else None
        full = ""
        try:
            wf = _grab(path, max(0, avail - 8), 3, CLIP["wide"] or box, True, os.path.join(OUT, "_clipfw"), 1800)
            full = ""
            for k in (0, 1, 2, 3):                     # the box itself, the look with the cleanest text
                tx = _ocr(_variant(fr[-1][1], k)) if fr else ""
                if sum(c.isalnum() for c in tx) > sum(c.isalnum() for c in full) and len(tx.strip()) < 120:
                    full = tx
            if not full.strip():
                full = _ocr(wf[-1][1]) if wf else ""
            if fr and TOKEN and not DRY:
                for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
                    with open(fr[-1][1], "rb") as fh:
                        tg_photo("sendPhoto", {"chat_id": cid, "caption": "What the bot looks at for the score (this is the area it reads)."}, fh.read())
        except Exception:
            pass
        lines = [l.strip() for l in (full or "").splitlines() if l.strip()][:8]
        fi = feed_info()
        card = board_card(fi if fi.get("score") else scoreboard_info(path, max(0, avail - 6)))          # the live feed knows the real team names and figures
        try:
            if TOKEN and not DRY:
                ff = _grab(path, max(0, avail - 6), 2, (0, 0, 1, 1), True, os.path.join(OUT, "_clipfull"), 1280)
                if ff:
                    from PIL import Image, ImageDraw
                    im = Image.open(ff[-1][1]).convert("RGB"); W_, H_ = im.size
                    dr = ImageDraw.Draw(im)
                    dr.rectangle((box[0] * W_, box[1] * H_, (box[0] + box[2]) * W_, (box[1] + box[3]) * H_), outline=(255, 40, 40), width=4)
                    fp = os.path.join(OUT, "_clipfull", "shot.png"); im.save(fp)
                    for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
                        with open(fp, "rb") as fh:
                            tg_photo("sendPhoto", {"chat_id": cid, "caption": "Full screen. The red box is where the bot reads the score."}, fh.read())
        except Exception:
            pass
        say("🏏 <b>Clips are on</b>  ·  score bar found\n━━━━━━━━━━━━━━\n%s\n━━━━━━━━━━━━━━\n"
            "4 / 6: %ds before, %ds after\nWicket: %ds before, %ds after\n50 / 100: %ds before, %ds after\n"
            "I will tell you here every time a 4, 6, wicket, 50 or 100 is detected." % (
                "\n".join(card) or (("📊 <b>%d/%d</b>" % (rd[0], rd[1])) if rd else "(the numbers are not clear yet - send me a screenshot)"),
                CLIP["pre"], CLIP["post"], CLIP["wpre"], CLIP["wpost"], CLIP["mpre"], CLIP["mpost"]))
    except Exception:
        pass


def E_INT(k, d):
    try: return int(float(E(k) or d))
    except Exception: return d


def clip_worker():
    if not ensure_tesseract():
        say("🏏 Clips need the text reader (tesseract) and it could not be installed, so clips are off. The recording is not affected.")
        return
    while not stop.is_set():
        time.sleep(2)
        try:
            sp = SP
            hist_note()
            if sp is None or not sp.path or not os.path.exists(sp.path):
                continue
            path = sp.path
            avail = sp.media_secs() - 4
            if avail < 30:
                continue
            if E("FEED_URL").startswith("http") and not ARCHIVE:
                bl = feed_break()
                if bl != CLIP.get("break", ""):
                    old_bl = CLIP.get("break", "")
                    CLIP["break"] = bl
                    if bl == "Finished":
                        say("🏁 <b>The match is finished</b> on the live feed. Clips are made for what is left of the recording.")
                    elif bl:
                        say("⏸ <b>%s</b>  ·  nothing to look at now. Clips start again when play is on." % esc(bl))
                    elif old_bl:
                        with CLIP_LOCK:
                            CLIP_PART[path] = max(CLIP_PART.get(path, 0.0), avail - 20)         # the break itself is not read
                            CLIP_ST["conf"] = None; CLIP_ST["pend"] = None; CLIP_ST["t_ov"] = None; CLIP["chk"] = time.time()
                            CLIP["lag"] = 0.0
                        say("▶️ <b>Play is on again.</b> Clips are on.")
                if bl and bl != "Finished" and avail - CLIP_PART.get(path, 0.0) < 60 and time.time() - CLIP.get("brk_t", 0) < 90:
                    with CLIP_LOCK:
                        clip_flush(path, avail, final=False)      # a clip that is waiting for its last seconds is still cut
                    continue
                CLIP["brk_t"] = time.time()
            with CLIP_LOCK:
                done = CLIP_PART.get(path, 0.0)
                if CLIP["box"] and not ARCHIVE and not CLIP.get("manual") and FEED.get("states") and time.time() - FEED["t"] < 45 and time.time() - CLIP.get("chk", 0) > 90:
                    CLIP["chk"] = time.time()                      # is the place we read still the score of the feed? (the picture can change: a new graphic, a new innings)
                    cf = CLIP_ST.get("conf")
                    if cf is not None and not feed_match(cf[0], cf[1]):
                        CLIP["bad_n"] = CLIP.get("bad_n", 0) + 1
                    else:
                        CLIP["bad_n"] = 0
                    if CLIP.get("bad_n", 0) >= 3:
                        print("Clips: what the bot reads (%s) does not fit the live feed (%s): looking for the score again" % (cf, feed_state_text()), flush=True)
                        CLIP["box"] = None; CLIP["tries"] = 0; CLIP["next_try"] = 0; CLIP["bad_n"] = 0
                        CLIP_ST["conf"] = None; CLIP_ST["pend"] = None
                if not CLIP["box"] and feed_waiting_first_ball():
                    CLIP_PART[path] = max(CLIP_PART.get(path, 0.0), avail - 20)          # toss, anthems: nothing to read, start from the live edge
                    if not CLIP.get("wb_msg"):
                        CLIP["wb_msg"] = True
                        print("Cricket clips: waiting for the first ball on the live feed (the score bar is looked for when play starts)", flush=True)
                    continue
                if not CLIP["box"]:
                    clip_detect(path, avail)
                    continue
                if avail - done >= (E_INT("CLIP_EVERY", 6) if not ARCHIVE else 60):
                    if not ARCHIVE and avail - done > 900:                  # hopelessly behind: go to the live edge (a few minutes back) instead of reading old video for an hour
                        print("Clips: the reading was %d s behind the live video, going to %d s from the end" % (avail - done, 240), flush=True)
                        done = avail - 240
                    upto = min(avail, done + 60) if not ARCHIVE else avail     # a minute at a time: the clips ready in between are cut at once
                    CLIP["lag"] = avail - upto
                    clip_analyze(path, done, upto, full=not ARCHIVE)
                    CLIP_PART[path] = upto
                    _merge_milestones(path)
            clip_flush(path, avail)
        except Exception as e:
            print("Clips error:", mask(repr(e))[:150], flush=True)


def clip_finish_part(ts):
    """A part is complete: read the rest of it and cut every waiting clip before the file is converted and deleted."""
    if not CLIP["on"] or not CLIP["ready"]:
        return
    try:
        dur = media_info(ts)[0] or 0
        print("Clips: reading the end of %s (%s long)" % (os.path.basename(ts), mmss(dur)), flush=True)
        with FEED_LOCK:
            hl = [h for h in FEED_HOLD if h["path"] == ts]
            for h in hl:
                FEED_HOLD.remove(h)
        for h in hl:
            if not h.get("strict"):
                clip_release(h)
        with CLIP_LOCK:
            if not CLIP["box"]:
                clip_detect(ts, dur)
            if CLIP["box"]:
                CLIP["lag"] = max(0.0, dur - CLIP_PART.get(ts, 0.0))
                clip_analyze(ts, CLIP_PART.get(ts, 0.0), dur, full=not ARCHIVE, final=True, avail=dur)
                CLIP["lag"] = 0
        _merge_milestones(ts)
        clip_flush(ts, dur, final=True)
        with FEED_LOCK:
            fe = [e for e in FEED_EV if e["path"] == ts]
            for e in fe:
                FEED_EV.remove(e)
        for e in fe:
            clip_cut(e, dur)
        clip_drain()
    except Exception as e:
        print("Clips error at the end of a part:", mask(repr(e))[:150], flush=True)
    CLIP_PART.pop(ts, None)
    with CLIP_LOCK:
        CLIP_EV[:] = [e for e in CLIP_EV if e["path"] != ts]


def match_card(info, thumb=None, syms_override=None):
    """The match dashboard picture: the live frame, the score, the batsmen, the bowler, the balls of this over, and what the bot found."""
    mods = _pil()
    if not mods:
        return None
    Image, ImageDraw, ImageFont = mods
    import io
    K, W, H = 2, 1000, 620
    img = Image.new("RGB", (W * K, H * K), (9, 11, 24))
    d = ImageDraw.Draw(img)
    P = lambda sz, w="Bold": _pf(ImageFont, sz * K, w)

    def T(x, y, t, f, c=(255, 255, 255), a="la"): d.text((x * K, y * K), t, font=f, fill=c, anchor=a)

    def rr(x0, y0, x1, y1, fill, r=14): d.rounded_rectangle((x0 * K, y0 * K, x1 * K, y1 * K), radius=r * K, fill=fill)
    st = CLIP_ST
    conf = st.get("conf")
    if info.get("score"):                                    # the live feed (when there is one) is the better source
        sc, ov = info["score"], info.get("overs") or ""
    else:
        sc = ("%d/%d" % (conf[0], conf[1])) if conf else "--"
        ov = ("%d.%d" % divmod(conf[2], 6)) if (conf and conf[2] is not None) else ""
    # header
    rr(24, 20, 976, 84, (20, 24, 48))
    d.ellipse((44 * K, 44 * K, 60 * K, 60 * K), fill=(255, 80, 96))
    T(72, 52, "LIVE", P(24), (255, 80, 96), "lm")
    T(150, 52, (info.get("team") or "MATCH").upper(), P(30), (235, 238, 255), "lm")
    hr = ("RR  %s" % info["rr"]) if info.get("rr") else ""
    if info.get("target"):
        hr += ("   ·   " if hr else "") + "TARGET  %s" % info["target"]
    if info.get("rrr"):
        hr += "   ·   REQ  %s" % info["rrr"]
    if hr:
        T(956, 52, hr, P(24, "Medium"), (160, 168, 215), "rm")
    # frame
    fx, fy, fw, fh = 24, 104, 440, 248
    rr(fx, fy, fx + fw, fy + fh, (18, 20, 36))
    if thumb:
        try:
            im = Image.open(thumb).convert("RGB")
            bw_, bh_ = fw * K - 8 * K, fh * K - 8 * K
            sc_ = min(bw_ / im.width, bh_ / im.height)
            im = im.resize((max(1, int(im.width * sc_)), max(1, int(im.height * sc_))))
            img.paste(im, ((fx + 4) * K + (bw_ - im.width) // 2, (fy + 4) * K + (bh_ - im.height) // 2))
        except Exception:
            pass
    else:
        T(fx + fw / 2, fy + fh / 2, "waiting for the picture", P(22, "Medium"), (120, 126, 170), "mm")
    # score block
    T(490, 112, "SCORE", P(18, "Medium"), (130, 137, 190))
    T(490, 132, sc, P(88), (255, 255, 255))
    T(490, 236, ("%s OVERS" % ov) if ov else "", P(28), (255, 196, 70))
    bats = info.get("bats") or []
    y = 268
    for nm, r_, b_ in bats[:2]:
        T(490, y, nm[:15], P(24, "Medium"), (225, 229, 250))
        T(956, y, "%d" % r_, P(28), (255, 255, 255), "ra")
        T(956 - 52, y + 6, "(%d)" % b_, P(20, "Medium"), (150, 157, 205), "ra")
        y += 32
    if info.get("bowler"):
        bt_ = info["bowler"].split(" (")[0]
        try:
            bn_, bf_ = bt_.rsplit(" ", 1)
        except ValueError:
            bn_, bf_ = bt_, ""
        T(490, 335, ("BOWL  %s  %s" % (bn_[:14], bf_)).strip(), P(20, "Medium"), (170, 178, 230))
        if info.get("pship"):
            T(956, 335, "P'SHIP  " + info["pship"], P(18, "Medium"), (130, 137, 190), "ra")
    if not bats and not info.get("bowler"):
        T(490, 284, "batsmen / bowler: not clear on the screen", P(20, "Medium"), (120, 126, 170))
    # this over
    rr(24, 372, 976, 452, (20, 24, 48))
    T(44, 412, "THIS OVER", P(20, "Medium"), (130, 137, 190), "lm")
    cols = {"4": (60, 130, 255), "6": (190, 90, 255), "W": (255, 70, 90), "0": (62, 68, 100), "?": (62, 68, 100)}
    x = 220
    syms = syms_override if syms_override is not None else ((st.get("over") or {}).get("syms") or [])
    for sy in syms[-9:]:
        c = cols.get(sy, (46, 160, 110) if sy.isdigit() or sy.startswith("+") else (62, 68, 100))
        d.ellipse((x * K, 384 * K, (x + 56) * K, 440 * K), fill=c)
        T(x + 28, 412, sy, P(26), (255, 255, 255), "mm")
        x += 68
    if not syms:
        T(220, 412, "starts with the next ball", P(20, "Medium"), (120, 126, 170), "lm")
    # counters
    cn = st.get("counts") or {}
    for i, (k, nm, c) in enumerate((("4", "FOURS", (60, 130, 255)), ("6", "SIXES", (190, 90, 255)), ("W", "WICKETS", (255, 70, 90)), ("S", "CLIPS SENT", (46, 190, 120)))):
        x0 = 24 + i * 240
        rr(x0, 472, x0 + 228, 552, (20, 24, 48))
        T(x0 + 114, 498, nm, P(16, "Medium"), c, "mm")
        T(x0 + 114, 531, str(st.get("sent", 0) if k == "S" else cn.get(k, 0)), P(40), (255, 255, 255), "mm")
    T(24, 584, ("BREAK: %s - clips start again when play starts" % CLIP["break"]) if CLIP.get("break") and CLIP["break"] != "Finished" else (("LAST:  " + st["lastev"]) if st.get("lastev") else "waiting for the first 4 / 6 / wicket"), P(20, "Medium"), (200, 205, 240), "lm")
    T(976, 584, time.strftime("%H:%M:%S", time.gmtime()) + " UTC", P(16, "Medium"), (110, 117, 160), "rm")
    out = io.BytesIO()
    img.resize((W, H)).save(out, "PNG", optimize=False)
    return out.getvalue()


def match_loop():
    """The live match dashboard: one picture message in the owner chat, edited every ~20 s. It shows the match all the time, not only at a 4 / 6 / wicket."""
    cids = list(dict.fromkeys([c for c in [E("DASH_CHAT") or CHAT] + ALSO if c]))
    if not cids or DRY or not _pil():
        return
    mid = {}
    info, info_t, i, keep = {}, 0.0, 0, {}
    while not stop.is_set():
        for _ in range(40):
            if stop.is_set(): return
            time.sleep(0.5)
        try:
            sp = SP
            if sp is None or not sp.path or not os.path.exists(sp.path) or not CLIP["box"]:
                continue
            avail = sp.media_secs() - 4
            if avail < 20:
                continue
            fi = feed_info() if E("FEED_URL").startswith("http") else {}
            if fi:
                info = fi; info_t = time.time()
            elif time.time() - info_t > 45:
                new = scoreboard_info(sp.path, max(0, avail - 3)) or {"bats": []}
                for k in ("bats", "bowler", "team", "rr", "title"):        # what is not on the screen right now is kept for 3 minutes
                    if new.get(k):
                        keep[k] = (new[k], time.time())
                info = dict(new)
                for k, (v, tk) in keep.items():
                    if not info.get(k) and time.time() - tk < 180:
                        info[k] = v
                info_t = time.time()
            thumb = None
            try:
                tf = _grab(sp.path, max(0, avail - 2), 2, (0, 0, 1, 1), True, os.path.join(OUT, "_dash"), 640)
                thumb = tf[-1][1] if tf else None
            except Exception:
                pass
            png = match_card(info, thumb, feed_over_syms() if fi else None)
            if not png:
                continue
            conf = CLIP_ST.get("conf")
            if fi and fi.get("score"):
                cap = "🏏 <b>LIVE MATCH</b> · %s  <b>%s</b>%s" % (esc(fi.get("team") or ""), esc(fi["score"]), (" (%s ov)" % fi["overs"]) if fi.get("overs") else "")          # the feed knows the real score; the screen is a little behind
            else:
                cap = "🏏 <b>LIVE MATCH</b>" + ((" · %s  <b>%d/%d</b>%s" % (esc(info.get("team") or ""), conf[0], conf[1], (" (%d.%d ov)" % divmod(conf[2], 6)) if conf[2] is not None else "")) if conf else "")
            for cid in cids:
                if cid in mid:
                    r = tg_photo("editMessageMedia", {"chat_id": cid, "message_id": mid[cid],
                                 "media": json.dumps({"type": "photo", "media": "attach://card", "caption": cap, "parse_mode": "HTML"})}, png)
                    if r.get("error_code") == 400 and "not modified" not in str(r.get("description", "")):
                        mid.pop(cid, None)
                else:
                    r = tg_photo("sendPhoto", {"chat_id": cid, "caption": cap, "parse_mode": "HTML"}, png)
                    m = (r.get("result") or {}).get("message_id")
                    if m: mid[cid] = m
        except Exception as e:
            print("Match card error:", mask(repr(e))[:150], flush=True)


# ---------------------------- live score feed (Cricbuzz page) ----------------------------

FEED = {"n": 0, "url": "", "t": 0.0, "mini": None, "hdr": None, "comm": [], "err": "", "first": True, "seen": {}, "cal": []}
FEED_MADE = set()
EV_SEEN = set()                                  # (kind, ball) of every 4 / 6 / wicket that already has a clip (from the screen or from the feed)
FEED_LOCK = threading.RLock()
FEED_UA = "Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Mobile Safari/537.36"


def _feed_obj(t, key):
    i = t.find('"%s":{' % key)
    if i < 0:
        return None
    try:
        return json.JSONDecoder().raw_decode(t[i + len(key) + 3:])[0]
    except Exception:
        return None


def _balls(x):
    """ballMetric 2.3 (over 3, ball 3 -> 2 overs and 3 balls) -> 15."""
    try:
        o = int(x); b = int(round((float(x) - o) * 10))
        return o * 6 + b
    except Exception:
        return None


def feed_parse(html):
    t = html.replace('\\"', '"').replace('\\\\', '\\')
    mini, hdr = _feed_obj(t, "miniscore"), _feed_obj(t, "matchHeader")
    comm = []
    dec = json.JSONDecoder()
    for mm in re.finditer(r'"(\d{13})":\{"matchId"', t):
        try:
            o = dec.raw_decode(t[mm.start() + 16:])[0]
        except Exception:
            continue
        if o.get("commType") == "commentary" or "commText" in o:
            comm.append(o)
    comm.sort(key=lambda o: o.get("timestamp", 0), reverse=True)
    uniq, seen = [], set()
    for o in comm:
        k = (o.get("timestamp"), o.get("commText"))
        if k not in seen:
            seen.add(k); uniq.append(o)
    return mini, hdr, uniq


def _ctext(o):
    tx = re.sub(r"<[^>]+>", "", str(o.get("commText") or ""))
    return re.sub(r"\s+", " ", tx).strip()


def feed_kind(o):
    ev = " ".join(str(x).lower() for x in (o.get("event") or []))
    if "wicket" in ev: return "W"
    if "six" in ev: return "6"
    if "four" in ev: return "4"
    return None


def feed_sym(o):
    k = feed_kind(o)
    if k: return k
    tx = _ctext(o).lower()
    if "no ball" in tx: return "nb"
    if "wide" in tx: return "wd"
    if "leg bye" in tx: return "lb"
    if " bye" in tx: return "b"
    m = re.search(r"(\d) runs?", tx)
    if m: return m.group(1)
    return "0" if "no run" in tx else "?"


def feed_fix(rd):
    """A reading whose first digit was not read (132 seen as 32) is mended with the live feed: the feed score is the check."""
    try:
        if rd is not None and FEED_BALLS:
            rg = FEED_BALLS.get((rd[0], rd[1]))
            if rg and rd[2] is not None and not (rg[0] - 1 <= rd[2] <= rg[1] + 1):
                rd = (rd[0], rd[1], min(max(rd[2], rg[0]), rg[1]))      # the over counter was misread: the feed knows the balls of this score
        if rd is None or not FEED.get("states") or time.time() - FEED.get("t", 0) > 60 or feed_match(rd[0], rd[1]):
            return rd
        for add in (100, 200, 300, 400):
            if rd[0] + add <= 800 and feed_match(rd[0] + add, rd[1]):
                return (rd[0] + add, rd[1], rd[2])
    except Exception:
        pass
    return rd


def feed_state_text():
    st = FEED.get("states") or []
    return "%d/%d" % (st[-1][1], st[-1][2]) if st else "?"


def feed_match(runs, wk):
    """Does a score read on the screen fit the live feed? The feed is a little late, so the screen may be ahead by a few balls."""
    st = FEED.get("states") or []
    if not st or runs is None:
        return False
    rr = [x[1] for x in st]; ww = [x[2] for x in st]
    return (min(rr) - 3 <= runs <= max(rr) + 20) and (min(ww) <= wk <= max(ww) + 1)


def feed_fetch():
    url = FEED["url"] + ("&" if "?" in FEED["url"] else "?") + "_=%d" % int(time.time() * 1000)          # a new address each time: the site's cache gives a fresh page
    t_req = time.time()
    try:
        r = subprocess.run(["curl", "-sS", "-L", "-m", "12", "--compressed", "-A", FEED_UA, "-H", "Accept-Language: en-US,en;q=0.9",
                            "-H", "Cache-Control: no-cache", "-H", "Pragma: no-cache", url], capture_output=True, text=True, timeout=20)
        html = r.stdout or ""
    except Exception as e:
        FEED["err"] = repr(e)[:80]; return False
    if len(html) < 20000:
        FEED["err"] = "short page (%d bytes)" % len(html); return False
    mini, hdr, comm = feed_parse(html)
    if not mini:
        FEED["err"] = "no score data in the page"; return False
    with FEED_LOCK:
        if t_req < FEED.get("t_req", 0):
            return True                                  # an older answer that arrived late: the newer one is already in
        FEED["t_req"] = t_req
        FEED["mini"], FEED["hdr"], FEED["comm"], FEED["t"], FEED["err"] = mini, hdr or FEED["hdr"], comm, time.time(), ""
        now = time.time()
        for o in comm:
            k = (o.get("timestamp"), o.get("commText"))
            if k not in FEED["seen"]:
                FEED["seen"][k] = {"first": now, "old": FEED["first"], "done": False}
        FEED["first"] = False
        try:
            sc_ = (mini.get("batTeam") or {})
            if sc_.get("teamScore") is not None:
                stt = (time.time(), int(sc_.get("teamScore") or 0), int(sc_.get("teamWkts") or 0))
                sl = FEED.setdefault("states", [])
                if not sl:
                    FEED["init"] = (stt[1], stt[2])
                if not sl or sl[-1][1:] != stt[1:]:
                    sl.append(stt)
                del sl[:-12]
                bt_ = (mini.get("batTeamScoreObj") or {})
                inn_ = (bt_.get("teamInningsArray") or [{}])[-1]
                if inn_.get("ballNbr") is not None and (stt[1], stt[2]) != FEED.get("init"):          # the state the feed started with: its first ball is not known
                    bn_ = int(inn_["ballNbr"])
                    rg = FEED_BALLS.setdefault((stt[1], stt[2]), [bn_, bn_])        # the balls at which the team had this score: the over counter of the screen is checked against it
                    rg[0] = min(rg[0], bn_); rg[1] = max(rg[1], bn_)
                if inn_.get("ballNbr") is not None:
                    FEED_SCORE_AT[(mini.get("inningsId"), int(inn_["ballNbr"]))] = (stt[1], stt[2])       # what the feed's own score was after each ball: a FOUR must have added 4 runs
        except Exception:
            pass
        try:
            feed_ms_note(mini)
        except Exception:
            pass
    return True


def feed_info():
    """The feed as the same kind of dictionary the screen reading gives (names, run, balls, bowler, rate), or {} when there is no fresh feed."""
    with FEED_LOCK:
        mini, hdr, comm = FEED["mini"], FEED["hdr"], FEED["comm"]
        if not mini or time.time() - FEED["t"] > 45:
            return {}
    out = {"bats": []}
    try:
        bt = (mini.get("batTeamScoreObj") or {})
        inn = (bt.get("teamInningsArray") or [{}])[-1]
        out["team"] = bt.get("teamName") or ""
        sc = mini.get("batTeam") or {}
        if sc.get("teamScore") is not None:
            out["score"] = "%d/%d" % (sc.get("teamScore", 0), sc.get("teamWkts", 0))
        if inn.get("ballNbr") is not None:
            out["overs"] = "%d.%d" % divmod(int(inn["ballNbr"]), 6)
        for key in ("batsmanStriker", "batsmanNonStriker"):
            b = mini.get(key) or {}
            if b.get("name") and b.get("runs") is not None:
                out["bats"].append((("%s%s" % (b["name"], "*" if key == "batsmanStriker" else "")).upper(), int(b["runs"]), int(b.get("balls") or 0)))
        bw = mini.get("bowlerStriker") or {}
        if bw.get("name"):
            out["bowler"] = "%s %s-%s (%s ov)" % (bw["name"].upper(), bw.get("wickets", 0), bw.get("runs", 0), bw.get("overs", ""))
        if mini.get("currentRunRate") not in (None, "", 0):
            out["rr"] = "%.2f" % float(mini["currentRunRate"])
        if mini.get("target"):
            out["target"] = str(mini["target"])
        if mini.get("requiredRunRate"):
            out["rrr"] = "%.2f" % float(mini["requiredRunRate"])
        ps = mini.get("partnerShip") or {}
        if ps.get("runs") is not None:
            out["pship"] = "%s (%s)" % (ps.get("runs"), ps.get("balls"))
        if mini.get("lastWicket"):
            out["lastwk"] = re.sub(r"\s+", " ", str(mini["lastWicket"]))[:90]
        if hdr:
            out["title"] = ("%s - %s" % (hdr.get("seriesName", ""), hdr.get("matchDescription", ""))).strip(" -")[:90]
    except Exception:
        pass
    return out


def _bm(o):
    try:
        return float(o.get("ballMetric"))
    except Exception:
        return None


def feed_over_syms():
    """The balls of the over in progress, from the commentary (oldest first)."""
    with FEED_LOCK:
        comm = [o for o in FEED["comm"] if _bm(o) is not None]
        fresh = time.time() - FEED["t"] < 45
    if not comm or not fresh:
        return None
    try:
        cur = int(_bm(comm[0]))
        rows = [o for o in comm if int(_bm(o)) == cur]
        rows.sort(key=lambda o: o.get("timestamp", 0))
        return [feed_sym(o) for o in rows][-9:]
    except Exception:
        return None


def feed_text_for(ev):
    """The commentary line of this 4 / 6 / wicket ('Lucy Hamilton to Laura Wolvaardt, FOUR, to fine leg'), or ''."""
    if ev.get("ball") is None:
        return ""
    with FEED_LOCK:
        for o in FEED["comm"]:
            if feed_kind(o) == ev["kind"] and _balls(o.get("ballMetric")) == ev["ball"]:
                return _ctext(o)[:160]
    return ""


FEED_BALLS = {}                                  # (runs, wickets) -> [first ball, last ball] seen on the feed
FEED_EV = []
FEED_HIST = []                                    # (wall clock, seconds of video written so far): ads are cut out, so the video clock falls behind the wall clock; this keeps the two together


def hist_note():
    sp = SP
    if sp is None or not sp.path:
        return
    try:
        m = sp.media_secs()
    except Exception:
        return
    if m <= 0:
        return
    now = time.time()
    with FEED_LOCK:
        if FEED_HIST and FEED_HIST[-1][2] != sp.path:
            FEED_HIST.clear()
        if not FEED_HIST or now - FEED_HIST[-1][0] >= 1.0:
            FEED_HIST.append((now, m, sp.path))
            if len(FEED_HIST) > 30000:
                del FEED_HIST[:5000]


def wall_to_media(w):
    """Video second that was written at wall-clock time w (None when unknown)."""
    with FEED_LOCK:
        h = list(FEED_HIST)
    if not h:
        return None
    if w <= h[0][0]:
        return h[0][1] - (h[0][0] - w)
    if w >= h[-1][0]:
        return h[-1][1] + (w - h[-1][0])
    lo, hi = 0, len(h) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if h[mid][0] <= w: lo = mid
        else: hi = mid
    (w0, m0, _), (w1, m1, _) = h[lo], h[hi]
    return m0 + (m1 - m0) * (w - w0) / max(1e-6, w1 - w0)


def media_to_wall(m):
    with FEED_LOCK:
        h = list(FEED_HIST)
    if not h:
        return None
    if m <= h[0][1]:
        return h[0][0] - (h[0][1] - m)
    if m >= h[-1][1]:
        return h[-1][0] + (m - h[-1][1])
    lo, hi = 0, len(h) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if h[mid][1] <= m: lo = mid
        else: hi = mid
    (w0, m0, _), (w1, m1, _) = h[lo], h[hi]
    return w0 + (w1 - w0) * (m - m0) / max(1e-6, m1 - m0)


def feed_first():
    """True while the live feed is the source of the 4 / 6 / wicket clips: it is set, and it answered in the last 25 seconds. When it is lost the screen reading takes over."""
    return (E("FEED_URL").startswith("http") and E("FEED_FIRST") != "0" and not ARCHIVE and bool(FEED.get("comm"))
            and time.time() - FEED.get("t", 0) < 25)


def feed_knows(runs, wk):
    """Did the feed ever show this score? A reading of the screen that the feed never had is a misread, it must not teach the clocks."""
    if (runs, wk) in FEED_BALLS:
        return True
    return any(x[1] == runs and x[2] == wk for x in (FEED.get("states") or []))


def feed_note_event(ev, mark=True):
    """An event the screen reading found: remember it, and learn how the feed time and the video time relate."""
    if mark and ev.get("ball") is not None and ev["kind"] in ("4", "6", "W"):
        EV_SEEN.add((ev["kind"], ev["ball"]))
    try:
        sp = SP
        if sp is None or ev.get("path") != sp.path or ev.get("ball") is None or ev["kind"] not in ("4", "6", "W"):
            return
        with FEED_LOCK:
            for o in FEED["comm"]:
                if feed_kind(o) == ev["kind"] and _balls(o.get("ballMetric")) == ev["ball"]:
                    w_ev = media_to_wall(ev["t"])
                    off = o["timestamp"] / 1000.0 - (w_ev if w_ev is not None else sp.wall0 + ev["t"])
                    FEED["cal"] = (FEED["cal"] + [(sp.wall0, off)])[-8:]
                    break
    except Exception:
        pass


def feed_calibration():
    """(offset) when at least two matched events agree within 25 s, else None."""
    cal = [c[1] for c in FEED["cal"]]
    if len(cal) == 1:
        return cal[0]                                  # one event seen on both: the same ball number and kind, that is already a good clock
    if len(cal) < 2:
        return None
    cal.sort()
    med = cal[len(cal) // 2]
    ok = [c for c in cal if abs(c - med) < 25]
    return med if len(ok) >= 2 else None


def feed_fallback():
    """A 4 / 6 / wicket that the feed shows but the screen reading never found: made from the feed time (only when the two clocks are known)."""
    sp = SP
    off = feed_calibration()
    guess = off is None
    if guess:
        off = float(E("FEED_LAG") or -15)              # not learned yet: the feed shows a ball about this many seconds after the video does
    if sp is None or not sp.path or not os.path.exists(sp.path):
        return
    pad = 15 if guess else 6
    avail = sp.media_secs() - 4
    now = time.time()
    with FEED_LOCK:
        todo = []
        for o in FEED["comm"]:
            k = feed_kind(o)
            st = FEED["seen"].get((o.get("timestamp"), o.get("commText")))
            if not k or not st or st["done"] or st["old"]:
                continue
            ball = _balls(o.get("ballMetric"))
            if ball is None:
                continue
            if (k, ball) in EV_SEEN:
                st["done"] = True; continue
            if any(h["kind"] == k and h.get("ball") == ball for h in FEED_HOLD):
                continue                                        # the screen has it and waits for this very line
            if not feed_selfcheck(k, ball, o.get("inningsId")):
                st["done"] = True
                print("Feed line ignored: %s over %d.%d - the feed's own score did not move that much" % (k, ball // 6, ball % 6), flush=True)
                continue
            if now - st["first"] < (3 if feed_first() else (10 if guess else 40)):              # the feed makes the clip at once; without the feed the screen reading gets its time first
                continue
            st["done"] = True
            rows = sorted(x.get("timestamp", 0) for x in FEED["comm"] if x.get("ballMetric") is not None and x.get("timestamp"))
            older = [x for x in rows if x < o.get("timestamp", 0) - 1500]
            gap = (o["timestamp"] - older[-1]) / 1000.0 if older else None      # seconds since the ball before: that ball's result is where the clip should begin
            todo.append((o, k, ball, gap))
    pre, post = int(E("FEED_PRE") or 35), int(E("FEED_POST") or 60)          # feed clips: the clip starts 35 s before the ball, 60 s after it
    for o, k, ball, gap in todo:
        lbw = k == "W" and bool(re.search(r"\blbw\b|leg before", _ctext(o), re.I))
        pre_k = int(E("FEED_PRE_LBW") or 60) if lbw else pre             # an LBW goes to the review: a longer clip (60 s before, 60 s after)
        post_k = int(E("FEED_POST_LBW") or 60) if lbw else post
        pad_s = 8 if guess else 4
        pre_e = max(10, pre_k - pad_s)                      # the clip starts exactly `pre_k` s before the ball: pre_e + pad_s
        tm = wall_to_media(o["timestamp"] / 1000.0 - off)
        t = tm if tm is not None else o["timestamp"] / 1000.0 - off - sp.wall0
        if t < 3:
            continue                                    # it happened before this recording started: no video of it
        ev = {"kind": k, "path": sp.path, "t": t, "start": max(0, t - pre_e - pad_s), "end": t + post_k + pad, "ov": "%d.%d" % divmod(ball, 6), "score": "", "ball": ball, "lbw": lbw,
              "runs": 4 if k == "4" else (6 if k == "6" else 0), "wk": 0, "end_known": True, "from_feed": True, "feed_text": _ctext(o)[:160], "created": time.time(), "pre": pre_k - 2, "post": post_k, "pad": pad, "ts": o.get("timestamp"), "inn": o.get("inningsId")}
        with FEED_LOCK:
            FEED_EV.append(ev)                         # cut by its own thread: the screen reading can be busy for a minute and must not hold these back
        EV_SEEN.add((k, ball)); FEED_MADE.add((k, ball))
        cn = CLIP_ST.setdefault("counts", {}); cn[k] = cn.get(k, 0) + 1
        CLIP_ST["lastev"] = "%s  (%s ov, from the feed)" % (_label(ev), ev["ov"])
        print("Clip event from the feed: %s over %s at %s" % (_label(ev), ev["ov"], mmss(t)), flush=True)
        try:
            say("🛰 <b>%s found by the live feed</b>  ·  over %s\n%s\n<i>%s</i>" % (_label(ev), ev["ov"], ("The clip is made from the live feed.  ⏱ %d s before the ball, %d s after%s (time %s)." % (pre_k, post_k + pad, " (LBW: DRS review)" if lbw else "", ("guessed, FEED_LAG=%g" % off) if guess else ("learned from the screen, %d ball(s)" % len(FEED["cal"])))) if feed_first() else "The screen reading did not see it, the clip is made from the feed time (a little wider than usual).", esc(_ctext(o))))
        except Exception:
            pass



CLIP_VERSION = "2026-11-24 lbw-extras-12conn-1login"
SCREEN_EVS = []                                  # 4 / 6 / wickets the screen saw (also on boards where the over cannot be read): kind, file, video second, score
SCREEN_T = {}                                    # (kind, ball) -> (file, video second) of a 4 / 6 / wicket that the screen saw: the exact time
FEED_SCORE_AT = {}                                # (innings, balls) -> (runs, wickets) as the feed says
FEED_BAT = {}                                     # (innings, batsman) -> runs the last time
FEED_MS = {}                                      # (innings, batsman, 50/100/...) -> {"first": time, "done": bool}


def feed_ms_note(mini):
    """A batsman's runs on the feed passing 50 / 100 / 150 / 200: a milestone that does not need the batsmen's figures to be readable on the screen."""
    inn = mini.get("inningsId")
    for key in ("batsmanStriker", "batsmanNonStriker"):
        b = mini.get(key) or {}
        nm, r = b.get("name"), b.get("runs")
        if not nm or r is None:
            continue
        r = int(r)
        prev = FEED_BAT.get((inn, nm))
        FEED_BAT[(inn, nm)] = r
        if prev is None:
            continue                                 # first look at this batsman (the feed started late): no milestone from a jump we did not see
        for m in (50, 100, 150, 200, 250, 300):
            if prev < m <= r and (inn, nm, m) not in FEED_MS:
                FEED_MS[(inn, nm, m)] = {"first": time.time(), "name": nm, "m": m, "runs": r, "balls": b.get("balls"), "done": False}


def feed_ms_make():
    sp = SP
    if sp is None or not sp.path or not os.path.exists(sp.path):
        return
    now = time.time()
    with FEED_LOCK:
        todo = [v for v in FEED_MS.values() if not v["done"] and now - v["first"] >= 12]
        comm = list(FEED["comm"])
    if not todo:
        return
    off = feed_calibration()
    guess = off is None
    off = float(E("FEED_LAG") or -15) if guess else off
    pad = 15 if guess else 6
    avail = sp.media_secs() - 4
    for v in todo:
        v["done"] = True
        row = next((o for o in comm if (o.get("batsmanDetails") or {}).get("playerName") == v["name"] and abs(o.get("timestamp", 0) / 1000.0 - v["first"]) < 90), None)
        wall = (row["timestamp"] / 1000.0) if row else v["first"] - 6
        tm = wall_to_media(wall - off)
        t = tm if tm is not None else wall - off - sp.wall0
        if t < 3:
            continue
        seen = CLIP_ST["seen"].get(("M", v["m"]))
        if seen is not None and abs(seen - t) < 120:
            continue                                 # the screen has already made this milestone
        CLIP_ST["seen"][("M", v["m"])] = t
        ev = {"kind": str(v["m"]), "path": sp.path, "t": t, "start": max(0, t - CLIP["mpre"] - pad), "end": t + CLIP["mpost"] + pad, "ov": "", "score": "", "ball": None,
              "runs": 0, "wk": 0, "end_known": True, "from_feed": True, "feed_text": ("%s %d (%s balls)" % (v["name"], v["runs"], v["balls"])) if v.get("balls") else "%s %d" % (v["name"], v["runs"]),
              "bat": ("%d (%s balls)" % (v["runs"], v["balls"])) if v.get("balls") else "%d" % v["runs"]}
        with FEED_LOCK:
            FEED_EV.append(ev)
        print("Clip event from the feed: %s %s at %s" % (_label(ev), v["name"], mmss(t)), flush=True)
        try:
            say("🛰 <b>%s found by the live feed</b>\n%s" % (_label(ev), esc(ev["feed_text"])))
        except Exception:
            pass


def feed_selfcheck(k, ball, inn):
    """The feed's commentary says FOUR / SIX / WICKET: the feed's own score must have gone up by that much on that ball (or the line is wrong or was corrected)."""
    a, b = FEED_SCORE_AT.get((inn, ball)), FEED_SCORE_AT.get((inn, ball - 1))
    if not a or not b:
        return True                                  # one of the two scores was not seen: cannot tell, believe the line
    dr, dw = a[0] - b[0], a[1] - b[1]
    if k == "4": return dr >= 4
    if k == "6": return dr >= 6
    if k == "W": return dw >= 1
    return True


def feed_break():
    """'' while play is on, else the reason (Innings break, Lunch, Tea, Stumps, Rain...) from the feed's match state."""
    with FEED_LOCK:
        hdr, mini, t = FEED["hdr"] or {}, FEED["mini"] or {}, FEED["t"]
    if not hdr or time.time() - t > 90:
        return ""
    state = str(hdr.get("state") or "").lower()
    tx = " ".join(str(x) for x in (hdr.get("state"), hdr.get("status"), mini.get("status"))).lower()
    if hdr.get("complete") or state == "complete" or re.search(r"\b(won by|match tied|no result|abandoned)\b", tx):
        return "Finished"
    if state in ("in progress", ""):
        return ""
    for pat, name in ((r"innings break", "Innings break"), (r"\blunch\b", "Lunch"), (r"\btea\b", "Tea"), (r"\bdinner\b", "Dinner"), (r"\bstumps\b", "Stumps"),
                      (r"\brain\b|bad light|\bdelay|interrupt|weather|\bwet\b", "Delay"), (r"\bbreak\b", "Break"), (r"\bdrinks\b", "Drinks")):
        if re.search(pat, tx):
            return name
    return ""


XST = {}                                           # toss / break / innings / result tracking


def _hdr_text():
    with FEED_LOCK:
        hdr, mini = FEED["hdr"] or {}, FEED["mini"] or {}
    return re.sub(r"\s+", " ", " ".join(str(x) for x in (hdr.get("status"), mini.get("status")) if x)).strip(), hdr


def feed_extra():
    """Toss, innings break, tea / lunch / stumps and the match result: a clip each, from the feed's match state (CLIP_EXTRA=0 turns it off)."""
    if E("CLIP_EXTRA") == "0" or ARCHIVE or not E("FEED_URL").startswith("http"):
        return
    with FEED_LOCK:
        fresh = FEED["hdr"] and time.time() - FEED["t"] <= 90
    if not fresh:
        return
    status, hdr = _hdr_text()
    toss = ""
    tr = hdr.get("tossResults") or {}
    if isinstance(tr, dict) and tr.get("tossWinnerName"):
        dec = str(tr.get("decision") or "").lower().replace("batting", "bat").replace("bowling", "bowl")
        toss = ("%s won the toss and chose to %s" % (tr["tossWinnerName"], dec)).strip() if dec else "%s won the toss" % tr["tossWinnerName"]
    elif re.search(r"won the toss|\bopt(?:s|ed)? to\b|elected to|chose to", status, re.I):
        toss = status
    brk = feed_break()
    if "init" not in XST:
        XST.update({"init": True, "toss": bool(toss), "brk": brk, "n": 0})
        return                                              # what was already there when the bot started is old news: no clip for it
    if toss and not XST["toss"]:
        XST["toss"] = True
        feed_extra_make("TOSS", toss, 35, 60, 45)
    if brk != XST["brk"]:
        old, XST["brk"] = XST["brk"], brk
        if brk == "Finished":
            feed_extra_make("WIN", status or "Match finished", 60, 90, 10)
        elif old == "" and brk == "Innings break":
            feed_extra_make("INN", status or "Innings break", 60, 30, 15)
        elif old == "" and brk in ("Lunch", "Tea", "Dinner", "Stumps", "Break"):
            feed_extra_make("BRK", status or brk, 30, 30, 15, name=brk)


def feed_extra_make(kind, text, pre, post, lagx, name=""):
    sp = SP
    if sp is None or not sp.path or not os.path.exists(sp.path):
        return
    off = feed_calibration()
    guess = off is None
    if guess:
        off = float(E("FEED_LAG") or -15)
    wall = time.time() - lagx                               # the feed shows it a few seconds after it happened
    tm = wall_to_media(wall - off)
    t = tm if tm is not None else wall - off - sp.wall0
    t = min(t, sp.media_secs() - 4)
    if t < 3:
        return
    fi = feed_info()
    score = ("%s %s" % (fi.get("team", ""), fi.get("score", ""))).strip() if fi.get("score") else ""
    pad = 15 if guess else 6
    ev = {"kind": kind, "path": sp.path, "t": t, "start": max(0, t - pre - 4), "end": t + post + pad, "ov": "", "score": score, "ball": None, "runs": 0, "wk": 0,
          "end_known": True, "from_feed": True, "feed_text": text[:160], "created": time.time(), "xname": name, "pre": pre, "post": post}
    with FEED_LOCK:
        FEED_EV.append(ev)
    print("Clip event from the feed: %s at %s (%s)" % (_label(ev), mmss(t), text[:80]), flush=True)
    try:
        say("🛰 <b>%s found by the live feed</b>\nThe clip is made from the live feed.  ⏱ %d s before, %d s after.\n<i>%s</i>" % (_label(ev).title(), pre, post + pad, esc(text[:160])))
    except Exception:
        pass


def feed_waiting_first_ball():
    """True while the live feed says no ball has been bowled yet (toss, anthems): the score bar is not looked for until play starts."""
    if not E("FEED_URL").startswith("http") or ARCHIVE or E("CLIP_WAIT_BALL") == "0":
        return False
    with FEED_LOCK:
        mini, comm, t = FEED["mini"], FEED["comm"], FEED["t"]
    if not mini or time.time() - t > 45 or FEED.get("n", 0) <= 0:
        return False                                        # no feed: the screen looks as before
    if any(o.get("ballMetric") is not None for o in comm):
        return False
    try:
        bt = mini.get("batTeam") or {}
        inn = ((mini.get("batTeamScoreObj") or {}).get("teamInningsArray") or [{}])[-1]
        if (bt.get("teamScore") or 0) > 0 or (inn.get("ballNbr") or 0) > 0:
            return False
    except Exception:
        return False
    return True


FEED_HOLD = []                                    # screen events that wait for the live feed to say what the ball was


def clip_release(ev):
    with CLIP_LOCK:
        CLIP_EV.append(ev)
    print("Clip event: %s at %s (%s)" % (_label(ev), mmss(ev["t"]), ev["score"]), flush=True)
    feed_note_event(ev)
    threading.Thread(target=clip_notice, args=(ev,), daemon=True).start()


def _metrics(ball):
    """The ball counter after a ball (77 = 12.5) as the feed writes it; the last ball of an over is 12.6 in the feed while the screen shows 13.0."""
    o, b = divmod(ball, 6)
    return [round(o + b / 10.0, 1)] + ([round(o - 1 + 0.6, 1)] if b == 0 and o > 0 else [])


def feed_verdict(ev):
    """'ok' (the feed says the same), 'bad' (the feed says something else), 'wait' (the feed has not got to this ball) or 'none' (cannot tell)."""
    try:
        if ev.get("ball") is None:
            return "none"
        with FEED_LOCK:
            comm = list(FEED["comm"]); fresh = time.time() - FEED.get("t", 0) < 60
        if not fresh or not comm:
            return "none"
        want = _metrics(ev["ball"])
        rows = [o for o in comm if _bm(o) is not None and round(_bm(o), 1) in want]
        if rows:
            ks = [feed_kind(o) for o in rows]
            if ev["kind"] in ks:
                return "ok"
            return "bad"
        newest = max([_bm(o) for o in comm if _bm(o) is not None] or [0])
        if newest + 0.05 < max(want):
            return "wait"
        return "none"
    except Exception:
        return "none"


def feed_hold(ev):
    """True when the event is held back to be checked with the feed. Without a fresh feed nothing is held."""
    if ev.get("kind") not in ("4", "6", "W") or ev.get("review") or not E("FEED_URL").startswith("http"):
        return False
    if time.time() - FEED.get("t", 0) > 60 or not FEED.get("comm"):
        return False
    v = feed_verdict(ev)
    if v == "ok":
        return False
    if v == "bad":
        feed_reject(ev, "feed")
        return True
    ev["vt"] = time.time()
    with FEED_LOCK:
        FEED_HOLD.append(ev)
    return True


def feed_reject(ev, why):
    st = CLIP_ST
    try:
        cn = st.get("counts", {}); cn[ev["kind"]] = max(0, cn.get(ev["kind"], 0) - 1)
        st["seen"].pop((ev["kind"], ev["score"]), None)
        st["last"].pop((ev["path"], ev["kind"]), None)
        st["lastev"] = ""
    except Exception:
        pass
    print("Clip event dropped: the screen read %s at %s (%s) but the live feed says it was not" % (_label(ev), mmss(ev["t"]), ev["score"]), flush=True)
    try:
        say("↩️ <b>Not a %s.</b> The score went to %s at %s, but the live feed says that ball was not a %s. No clip." % (_label(ev), ev["score"], mmss(ev["t"]), _label(ev)))
    except Exception:
        pass


def feed_hold_check():
    now = time.time()
    with FEED_LOCK:
        held = list(FEED_HOLD)
    for ev in held:
        v = feed_verdict(ev)
        late = now - ev["vt"] > 20
        if v == "ok":
            go = True
        elif v == "bad":
            go = False
        elif late:
            go = not ev.get("strict")                     # two balls with 4 or 6 runs, and the feed could not say: not a boundary
        else:
            continue
        with FEED_LOCK:
            if ev not in FEED_HOLD:
                continue
            FEED_HOLD.remove(ev)
        if go:
            clip_release(ev)
        else:
            feed_reject(ev, "feed")


def feed_flush_loop():
    while not stop.is_set():
        time.sleep(2)
        try:
            ff = feed_first()
            if E("FEED_URL").startswith("http") and E("FEED_FIRST") != "0" and not ARCHIVE and FEED.get("n", 0) > 0:
                if ff != FEED.get("was_first", True):
                    FEED["was_first"] = ff
                    say("🛰 <b>The live feed is back.</b> Clips come from the feed again." if ff else
                        "⚠️ <b>The live feed is lost.</b> The screen reading makes the 4 / 6 / wicket clips now, until the feed is back.")
            feed_hold_check()
            feed_ms_make()
            feed_extra()
        except Exception as ex:
            print("Feed check error:", mask(repr(ex))[:150], flush=True)
        try:
            sp = SP
            if sp is None or not sp.path or not os.path.exists(sp.path):
                continue
            avail = sp.media_secs() - 4
            nowt = time.time()
            with FEED_LOCK:
                for e in FEED_EV:
                    if e["path"] != sp.path or e.get("refined") or e.get("kind") not in ("4", "6", "W"):
                        continue
                    hit = SCREEN_T.get((e["kind"], e.get("ball")))
                    if not hit:
                        sc_at = FEED_SCORE_AT.get((e.get("inn"), e.get("ball")))
                        cands = [x for x in SCREEN_EVS if not x["used"] and x["kind"] == e["kind"] and x["path"] == e["path"] and abs(x["t"] - e["t"]) <= 100
                                 and (sc_at is None or not x["score"] or x["score"] == "%d/%d" % sc_at)]
                        if cands:                                  # the same kind (and score) close in time: the board shows no readable over, but it is this ball
                            x = min(cands, key=lambda c_: abs(c_["t"] - e["t"])); x["used"] = True
                            hit = (x["path"], x["t"])
                    if hit and hit[0] == e["path"]:                # the screen saw this very ball: its time is exact, the feed's time is only a guess
                        try:
                            if e.get("ts"):
                                w_ev = media_to_wall(hit[1])
                                if w_ev is not None:
                                    FEED["cal"] = (FEED["cal"] + [(sp.wall0, e["ts"] / 1000.0 - w_ev)])[-8:]          # the two clocks, learned from this ball
                        except Exception:
                            pass
                        e["t"] = hit[1]; e["start"] = max(0, hit[1] - e["pre"] - 2); e["end"] = hit[1] + e["post"] + 2; e["refined"] = True
                        print("Clip time of %s over %s taken from the screen (%s)" % (_label(e), e["ov"], mmss(hit[1])), flush=True)
                def _waits(e):
                    # the screen reading is a little behind the live picture: give it a moment to find this ball before the feed's own guess is used
                    return (not e.get("refined") and e.get("kind") in ("4", "6", "W") and CLIP.get("box") and not CLIP.get("manual_off")
                            and CLIP_PART.get(e["path"], 0.0) < e["t"] + 45 and nowt - e.get("created", 0) < 100)
                ready = [e for e in FEED_EV if e["path"] == sp.path and e["end"] <= avail and not _waits(e)]
                for e in ready:
                    FEED_EV.remove(e)
            for e in sorted(ready, key=lambda x: x["t"]):
                print("Clip from the feed: cutting %s over %s (%s to %s)" % (_label(e), e["ov"], mmss(e["start"]), mmss(e["end"])), flush=True)
                clip_cut(e, avail)
        except Exception as ex:
            print("Feed clip error:", mask(repr(ex))[:150], flush=True)


def feed_loop(second=False):
    FEED["url"] = E("FEED_URL")
    if second:
        time.sleep(float(E_INT("FEED_EVERY", 2)) / 2.0)           # a second reader, half a step later: the page is read twice as often even when one answer is slow
    bad = 0
    while not stop.is_set():
        hist_note()
        try:
            ok = feed_fetch()
        except Exception as e:
            ok = False; FEED["err"] = repr(e)[:80]
        if not ok:
            bad += 1
            if bad in (1, 5, 30) and not second:
                print("Live feed: %s" % FEED["err"], flush=True)
                if bad == 5:
                    try: say("⚠️ The live score feed does not answer (%s). The clips continue from the screen reading." % esc(FEED["err"]))
                    except Exception: pass
        else:
            if (bad or FEED["n"] == 0) and not second:
                print("Live feed: reading the page (%d commentary lines)" % len(FEED["comm"]), flush=True)
                if FEED["n"] == 0:
                    try:
                        fi = feed_info()
                        last = next((o for o in FEED["comm"] if feed_kind(o)), None)
                        say("🛰 <b>Live feed connected</b>  ·  %s %s%s\nEvery new 4 / 6 / wicket on the feed is cut as a clip%s.\n<i>Last one on the feed: %s</i>" % (
                            esc(fi.get("team", "")), esc(fi.get("score", "?")), ("  ·  %s ov" % fi["overs"]) if fi.get("overs") else "",
                            " (the screen reading goes first)", esc(_ctext(last)[:120]) if last else "none yet"))
                    except Exception:
                        pass
            if not second and time.time() - FEED.get("hb", 0) > 60:
                FEED["hb"] = time.time()
                try:
                    fi = feed_info()
                    print("Live feed: ok · %s %s %s ov · %d lines · events seen %d" % (fi.get("team", ""), fi.get("score", "?"), fi.get("overs", "?"), len(FEED["comm"]), len(EV_SEEN)), flush=True)
                except Exception:
                    pass
            bad = 0; FEED["n"] += 1
            try: feed_fallback()
            except Exception as e: print("Live feed error:", repr(e)[:100], flush=True)
        for _ in range(int(E_INT("FEED_EVERY", 2)) * 2):
            if stop.is_set(): return
            time.sleep(0.5)


def clip_start():
    if CLIP["on"] and not DRY or (CLIP["on"] and E("CLIPS_TEST") == "1"):
        CLIP["ready"] = True
        threading.Thread(target=clip_worker, daemon=True).start()
        if E("DASH") != "0":
            threading.Thread(target=match_loop, daemon=True).start()
        if E("FEED_URL").startswith("http"):
            threading.Thread(target=feed_loop, daemon=True).start()
            threading.Thread(target=feed_loop, args=(True,), daemon=True).start()
            threading.Thread(target=feed_flush_loop, daemon=True).start()
        print("Cricket clips: on (4/6 %ds before %ds after, wicket %ds before %ds after, 50/100 %ds before %ds after)" % (CLIP["pre"], CLIP["post"], CLIP["wpre"], CLIP["wpost"], CLIP["mpre"], CLIP["mpost"]), flush=True)
        print("Version: %s | feed clips: start %s s before the ball, %s s after" % (CLIP_VERSION, E("FEED_PRE") or 35, E("FEED_POST") or 60), flush=True)


def record():
    global SP, HDR, ARCHIVE
    os.makedirs(OUT, exist_ok=True)
    detect_chat()
    if PROXY:
        print("::add-mask::" + PROXY, flush=True)
        setup_proxy()
    global URL
    lt = E("LINK_TEXT")
    if lt and not URL.startswith("http") and not URL.startswith("enc:"):          # the clip bot hands over the whole message
        f = re.search(r"https?://\S+", lt)
        if f:
            URL = f.group(0).strip("<>\"'")
            set_mode_from_text(lt)
            print("::add-mask::" + URL, flush=True)
    if URL.startswith("enc:"):
        u = open_link(URL)
        if u:
            f = re.search(r"https?://\S+", u)
            URL = f.group(0) if f else u
            set_mode_from_text(u)
            print("::add-mask::" + URL, flush=True)
            print("Link taken over from the previous run.", flush=True)
        else:
            URL = "ask"                                      # could not unlock it: ask again
    if URL.startswith("http"):
        TICK_OK = True
    else:
        TICK_OK = False
    if not TICK_OK and TICKET and WORKER_URL and not fetch_link():
        say("❌ <b>Could not get the stream link from the worker.</b> Send the link again.")
        print("::error title=No link::The worker did not return the link for this ticket.", flush=True)
        sys.exit(1)
    if URL.strip().lower() in ("", "ask", "telegram"):
        preflight()
        ask_link()
    parse_drm()
    ok, err = precheck()
    tries = int(E("PRECHECK_TRIES") or 8)
    n = 1
    while not ok and n < tries and re.search(r"403|forbidden|429|too many|401|timed out|timeout|refused|reset by peer|end of file|50\d", (err or "").lower()):
        if n == 1:
            last_line = esc(((err or "?").strip().splitlines() or ["?"])[-1][:160])
            say("⏳ <b>The server refused the link for now.</b>\n<b>Reason:</b> <code>%s</code>\nPossible causes: the server blocks GitHub's country/IP (a player on your phone works because it uses your own IP), the link or its token expired, it needs a special header (Referer), or the account has too many connections.\nI keep trying for a few minutes." % last_line)
        print("Link refused, trying again in 25 s (%d/%d)" % (n, tries), flush=True)
        time.sleep(float(E("PRECHECK_WAIT") or 25))
        ok, err = precheck(); n += 1
    if not ok:
        why = explain(err)
        print("PRECHECK FAILED. ffmpeg said:\n" + err, flush=True)
        print("::error title=Link could not be opened from GitHub::" + why, flush=True)
        summary("## Recording did not start\n**Reason:** " + why + "\n\n```\n" + err + "\n```")
        try:
            ip = where()
        except Exception:
            ip = "?"
        say("❌ <b>The link could not be opened from GitHub's server</b>\n<b>Reason:</b> %s\n📍 The server sees an IP in: %s\n\n<code>%s</code>" % (esc(why), esc(ip) + ("" if PROXY else " (no proxy set)"), esc(err[-300:])))
        sys.exit(1)
    ARCHIVE = detect_archive()
    print("Link type: %s (%s)" % ("finished file (archive): it is downloaded completely" if ARCHIVE else "live stream", ARCH_WHY[0]), flush=True)
    plan = ("stops after %d min" % MINUTES) if MINUTES else "runs until you press Stop"
    kind_txt = "📡 <b>MPEG-TS live stream</b> (starts now, no rewind)" if KIND == "ts" else ("📡 <b>MPEG-DASH stream</b> (.mpd)%s" % (" · 🔑 decrypted with your key" if DASH_KEYS else "") if KIND == "dash" else "📡 HLS stream")
    every = "every %s%s" % (human(PART_MAX), (" or %g min" % PART_MIN) if PART_MIN > 0 else "")
    if ARCHIVE:
        say("⬇️ <b>Archive download started</b>\n🎬 %s\n📡 %s\n✂️ New file every %s\n📍 Stream server sees an IP in: %s\nEach file is uploaded when it is full. Use Status to see the progress.\n🔎 Detected as an archive: %s." %
            (esc(NAME), "finished .ts file" if KIND == "ts" else ("finished .mpd manifest" if KIND == "dash" else "finished .m3u8 playlist"), human(PART_MAX), esc(where()), esc(ARCH_WHY[0])), buttons=True)
    else:
        say("🔴 <b>Recording started</b>\n🎬 %s\n%s\n⏱ %s\n✂️ New file %s (whichever comes first)\n📍 Stream server sees an IP in: %s\nThe first download link comes after the first file is full.\n🔎 Detected as a live stream: %s.%s" %
            (esc(NAME), kind_txt, plan, every, esc(where()), esc(ARCH_WHY[0]),
             "" if MODE != "auto" else "\nIf this is a finished archive, send the link again with the word <b>archive</b> after it."), buttons=True)
    signal.signal(signal.SIGINT, lambda *a: halt())
    signal.signal(signal.SIGTERM, lambda *a: halt())
    total = MINUTES * 60
    if (not total or total > LIMIT) and not ARCHIVE:
        threading.Thread(target=chain, args=(int((total - LIMIT) / 60) if total else 0,), daemon=True).start()
    if WORKER_URL and not DRY:
        threading.Thread(target=worker_poll, daemon=True).start()
    elif TOKEN and CHAT and not DRY:
        threading.Thread(target=poll, daemon=True).start()
    up = threading.Thread(target=uploader)
    up.start()
    SP = Splitter(upq.put)
    clip_start()
    SP.on_manual = lambda n: say("✂️ <b>Split done</b>\nFile #%d started. Recording continues." % n, buttons=True)
    end_at = S["t0"] + (min(total, LIMIT) if total else LIMIT)

    # The reader (below) only moves bytes from ffmpeg into this queue. The splitter works on the other side.
    # So a slow disk, a busy CPU or an upload can never make the pipe full and the server drop the connection.
    rq = queue.Queue(maxsize=4000)

    def consumer():
        while True:
            it = rq.get()
            if it is None:
                return
            try:
                if it[0] == "d":
                    disk_wait()
                    SP.feed(it[1])
                else:
                    SP.new_session(dedupe=it[1], verify=it[2])
            except Exception as e:
                print("splitter error:", repr(e), flush=True)
                SP.buf = b""
    ct = threading.Thread(target=consumer)
    ct.start()

    def watchdog():
        while not stop.is_set():
            if time.time() >= end_at:
                halt(); return
            if IDLE_STOP > 0 and time.time() - SP.last_es > IDLE_STOP * 60:
                say("⏹ <b>The stream sent no data for %g minutes</b>, so the match has probably ended.\nSaving what I have and ending the job to save your GitHub minutes." % IDLE_STOP)
                halt(); return
            time.sleep(2)
    threading.Thread(target=watchdog, daemon=True).start()

    def stream_monitor():
        warned, since = False, 0
        while not stop.is_set():
            idle = time.time() - SP.last_es
            if not warned and idle > 90:
                warned, since = True, time.time() - idle
                say("⚠️ <b>The stream has not sent data for %s.</b>\nStill trying. Short breaks are repaired automatically." % mmss(idle))
            elif warned and idle < 15:
                warned = False
                say("✅ <b>Stream is back</b> after %s. Recording continues in the same file." % mmss(time.time() - since))
            time.sleep(5)
    threading.Thread(target=stream_monitor, daemon=True).start()
    if not DRY:
        threading.Thread(target=live_loop, daemon=True).start()

    last_err = []; first = True; consec = 0; hi = [0]
    dl_ok = True
    if ARCHIVE:
        dl_ok = download_loop(rq)
        stop.set()                                             # nothing more to fetch (also quiets the stream monitor)
    if KIND == "hls" and not ARCHIVE and PARALLEL > 1 and LIVE_PAR != "0":
        if LIVE_PAR == "1" or live_probe():
            PAR_LIVE[0] = True
            say("⚡ <b>Fast mode</b>\nThis link is slower than real time, so I record it with %d parallel connections. No parts are skipped." % PARALLEL)

        def gap_watch():
            while not stop.is_set():
                time.sleep(2)
                if PAR_OK[0] and not PAR_LIVE[0] and SP and SP.gap_total >= float(E("GAP_SWITCH") or 8):
                    PAR_LIVE[0] = True
                    say("⚡ <b>Parts are being skipped</b>, so I switch to %d parallel connections now." % PARALLEL)
                    pr = S["proc"]
                    if pr and pr.poll() is None:
                        pr.send_signal(signal.SIGINT)
        if LIVE_PAR != "1":
            threading.Thread(target=gap_watch, daemon=True).start()
    while not stop.is_set() and not ARCHIVE:
        if KIND == "hls" and PAR_LIVE[0] and PAR_OK[0]:
            t_run = time.time()
            why = live_hls_parallel(rq)
            first = False
            if stop.is_set() or TEST_ONCE:
                break
            if why == "fallback":
                PAR_LIVE[0] = False
                print("Parallel mode is not possible for this playlist, normal recording instead", flush=True)
            S["restarts"] += 1
            rq.put(("n", True, False))
            S["reason"] = why
            consec = 0 if time.time() - t_run > 30 else consec + 1
            print("Reconnect %d (parallel mode): %s" % (S["restarts"], why), flush=True)
            time.sleep(min(0.5 + 0.5 * consec, 5))
            continue
        if KIND == "ts" and TS_RAW:
            # Direct download of the MPEG-TS bytes: reconnect takes milliseconds (no ffmpeg start, no probing), so even a
            # server that drops the link every second costs (almost) nothing. The splitter joins / de-duplicates as before.
            t_run = time.time()
            reason, got = ts_pull(rq)
            first = False
            if stop.is_set() or TEST_ONCE:
                break
            S["restarts"] += 1
            rq.put(("n", True, True))
            S["reason"] = reason
            consec = 0 if got > 0 else consec + 1
            print("Reconnect %d: lasted %.1fs, got %.1f MB: %s" % (S["restarts"], time.time() - t_run, got / 1e6, reason), flush=True)
            if got == 0 and consec % 3 == 0:               # the server keeps refusing: try another set of headers (browser / referer / VLC ...)
                sets = header_sets(); hi[0] = (hi[0] + 1) % len(sets)
                HDR = sets[hi[0]][1]
                print("Server keeps refusing: now trying %s" % sets[hi[0]][0], flush=True)
            time.sleep(0.2 if got > 0 else min(0.5 + 0.5 * consec, 5))
            continue
        if KIND == "dash":
            t_run = time.time()
            done, why = dash_session(rq, first)
            first = False
            if stop.is_set() or TEST_ONCE:
                break
            if done:                                         # the live stream ended on the server (manifest turned static)
                break
            S["restarts"] += 1
            rq.put(("n", True, False))
            S["reason"] = why
            consec = 0 if time.time() - t_run > 30 else consec + 1
            print("Reconnect %d (DASH): %s" % (S["restarts"], why), flush=True)
            time.sleep(min(0.5 + 0.5 * consec, 5))
            continue
        if KIND == "ts":
            # no ffmpeg-internal reconnect: after a drop a NEW ffmpeg starts quickly (small probe), and the splitter
            # joins the timeline, so a restarted server clock does not matter
            inopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "20000000",
                      "-probesize", "2000000", "-analyzeduration", "1500000"]
        elif KIND == "dash":
            inopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000"]
        else:
            inopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000", "-reconnect", "1", "-reconnect_streamed", "1",
                      "-reconnect_delay_max", "15", "-seg_max_retry", "15", "-max_reload", "1000", "-m3u8_hold_counters", "1000",
                      "-http_persistent", "0", "-live_start_index", ("-" + BACK) if first else ("-" + RECON_BACK)]
        cmd = ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-y"] + inopts + HDR + src_args() + map_args() + [
               "-c", "copy", "-copyts", "-muxdelay", "0", "-muxpreload", "0",
               "-f", "mpegts", "-mpegts_flags", "+resend_headers", "pipe:1"]
        first = False
        t_run = time.time()
        p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0, env=fenv())
        if fcntl:
            try: fcntl.fcntl(p.stdout.fileno(), 1031, 1 << 20)       # F_SETPIPE_SZ: 1 MB pipe
            except Exception: pass
        last_err = []
        threading.Thread(target=stderr_reader, args=(p, last_err), daemon=True).start()
        while True:
            data = p.stdout.read(1 << 20)
            if not data:
                break
            rq.put(("d", data)); S["last_data"] = time.time()
            S["qmax"] = max(S["qmax"], rq.qsize())
        p.wait()
        if stop.is_set() or TEST_ONCE:
            break
        S["restarts"] += 1
        rq.put(("n", True, KIND == "ts"))                    # processed in order, after the data already queued
        S["reason"] = why_exit(p.returncode, last_err)
        consec = 0 if time.time() - t_run > 30 else consec + 1
        print("Reconnect %d (queue peak %d): %s" % (S["restarts"], S["qmax"], S["reason"]), flush=True)   # log only, no Telegram spam
        time.sleep(min(0.5 + 0.5 * consec, 5))
    rq.put(None)
    ct.join()
    SP.finish()
    upq.put(None)
    up.join()
    saved = sum(d["size"] for d in S["done"])
    page = S["page"]
    word = "Download" if ARCHIVE else "Recording"
    summary("## %s finished\n%d file(s), %s. %s" % (word, len(S["done"]), human(saved), ("[Download page](%s)" % page) if page else ""))
    rows = "\n".join("%d.  %s  ·  %s" % (i + 1, human(d["size"]), mmss(d["secs"])) for i, d in enumerate(S["done"][:30]))
    link = ('\n\n📂 <a href="%s">Download all files (one page)</a>' % page) if page else "\n\n⚠️ No file could be uploaded. See the run log."
    V = "│ "
    head = "\n".join([BOX_TOP, "%s%s <b>%s %s</b>%s  ·  <b>%s</b>" % (V, "🏁" if dl_ok else "⚠️", word, "𝗙𝗜𝗡𝗜𝗦𝗛𝗘𝗗", "" if dl_ok else " (NOT complete)", esc(NAME)), BOX_MID,
                       "%s📁 Files   <code>%d</code>" % (V, len(S["done"])), "%s💾 Size    <code>%s</code>" % (V, human(saved)),
                       "%s⏱ Time    <code>%s</code>" % (V, hms(time.time() - S["t0"])), BOX_MID,
                       "%s%s  🕒 %s" % (V, naim_sig(int(time.time())), clock()), BOX_END])
    sent = False
    if E("LIVE_CARD") != "0" and not DRY and _pil():
        try:
            png = live_card(len(HIST), True, HIST)
        except Exception as e:
            png = None
            print("final card:", repr(e)[:120], flush=True)
        if png:
            cap = head + "\n\n" + rows + link
            long = len(cap) > 1000
            if long:
                cap = head + link
            for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
                r = tg_photo("sendPhoto", {"chat_id": cid, "caption": cap, "parse_mode": "HTML"}, png)
                sent = sent or bool(r.get("ok"))
            if sent and long:
                say("📁 <b>Files</b>\n" + rows)
    if not sent:
        say("%s\n\n%s%s" % (head, rows, link))
    if PENDING and not flush_pending(20 * 60):                  # Telegram still says wait: the messages cannot go out, put them in the log
        print("Telegram was still blocking the bot at the end. The last messages:", flush=True)
        for d in PENDING:
            print(re.sub(r"<[^>]+>", "", d.get("text", "")), flush=True)


def finish():
    """always() step: upload leftovers if the main step was cancelled or killed."""
    leftovers = sorted(glob.glob(os.path.join(OUT, "*.ts")))
    if not leftovers:
        return
    for f in leftovers:
        process(f)
    if CLIPS_ONLY:
        say("⚠️ <b>The recording was interrupted.</b> Start the workflow again with the link to continue.")
        return
    say("⚠️ <b>Recording was interrupted.</b> Saved %d leftover file(s).%s" % (len(leftovers), ('\n📂 <a href="%s">Download page</a>' % S["page"]) if S["page"] else ""))


if __name__ == "__main__":
    finish() if len(sys.argv) > 1 and sys.argv[1] == "finish" else record()
