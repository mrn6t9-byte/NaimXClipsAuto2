#!/usr/bin/env python3
"""Cricket clip bot (separate from the recording bot).

Send it (in Telegram): a live stream link, an archive link (.m3u8 / .mpd / .ts), a Gofile link or a video file link.
For every 4, 6, wicket and 50 / 100 it cuts a clip and sends it as a video to the channel (CLIP_CHAT).

The stream reading is done by cliprec.py (the same folder); this file only talks to Telegram and downloads video files.
Caption words (all optional):  pre 30  post 30  wpre 30  wpost 60  mpre 30  mpost 60  after 0
"""
import os, sys, re, json, time, subprocess, asyncio

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def E(k, d=""):
    return os.environ.get(k, d) or d


import cliprec as R                                   # the clip engine (reads the score, cuts, sends)

TOKEN = E("TG_TOKEN"); CHAT = E("CHAT") or E("TG_CHAT"); MSG = E("MSG"); FILE_ID = E("FILE_ID"); FILE_SIZE = int(E("FILE_SIZE") or 0)
CAPTION = E("CAPTION"); API_ID = E("API_ID"); API_HASH = E("API_HASH")
TG_API = E("TG_API") or "https://api.telegram.org"
LOCAL_FILE = E("LOCAL_FILE")                          # test only: use this file instead of downloading
OUT = E("OUT_DIR") or "/mnt/rec"
DRY = E("DRY") == "1"
FILE_EXT = re.compile(r"\.(mp4|mkv|mov|webm|avi|m4v)(\?|$)", re.I)


def say(text):
    R.CHAT = CHAT                                      # the chat that sent the video (or the owner)
    return R.say(text)


mask = R.mask
human, mmss = R.human, R.mmss


def esc(t):
    return str(t).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def api(method, fields=None, files=None, timeout=120):
    """Telegram Bot API call (curl handles the file upload)."""
    if not TOKEN or DRY:
        print("[tg]", method, {k: str(v)[:80] for k, v in (fields or {}).items()}, list((files or {}).keys())); return {"ok": True, "result": []}
    cmd = ["curl", "-sS", "-m", str(timeout), "-X", "POST", "%s/bot%s/%s" % (TG_API, TOKEN, method)]
    for k, v in (fields or {}).items():
        cmd += ["--form-string", "%s=%s" % (k, v)]
    for k, v in (files or {}).items():
        cmd += ["-F", "%s=@%s" % (k, v)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 10)
        return json.loads(r.stdout or "{}")
    except Exception as e:
        return {"ok": False, "description": repr(e)[:100]}


def send_photo(chat, path, caption):
    api("sendPhoto", {"chat_id": chat, "caption": caption, "parse_mode": "HTML"}, {"photo": path})


def telethon_download(dest):
    """A video sent to the bot (up to 2 GB) through Telegram's own protocol; the Bot API itself stops at 20 MB.
    The message is fetched by its number (works in the private chat with the bot); the old file-id way is the backup."""
    if not (API_ID and API_HASH):
        raise RuntimeError("API_ID / API_HASH secrets are not set")
    try:
        from telethon import TelegramClient, utils
        from telethon.sessions import MemorySession
    except Exception:
        raise RuntimeError("telethon is not installed")

    async def go():
        c = TelegramClient(MemorySession(), int(API_ID), API_HASH)
        await c.start(bot_token=TOKEN)
        try:
            media, size, why = None, FILE_SIZE, []
            if MSG:
                try:
                    m = await c.get_messages(None, ids=int(MSG))
                    if m is not None and getattr(m, "media", None):
                        media = m.media
                        size = getattr(getattr(m, "document", None), "size", 0) or size
                    else:
                        why.append("message not found")
                except Exception as e:
                    why.append("message: " + repr(e)[:80])
            if media is None and FILE_ID:
                try:
                    media = utils.resolve_bot_file_id(FILE_ID)
                    if media is None:
                        why.append("file id not understood")
                except Exception as e:
                    why.append("file id: " + repr(e)[:80])
            if media is None:
                raise RuntimeError("could not find the video through Telegram (%s). Send it in a private chat with the bot" % "; ".join(why))
            got, last = 0, time.time()
            with open(dest, "wb") as f:
                async for chunk in c.iter_download(media, request_size=1024 * 1024, file_size=size or None):
                    f.write(chunk); got += len(chunk)
                    if time.time() - last > 30:
                        last = time.time(); print("Downloaded %s of %s" % (human(got), human(size or got)), flush=True)
            if got < 100000:
                raise RuntimeError("Telegram sent an empty file")
        finally:
            await c.disconnect()
    asyncio.run(go())


def gofile_resolve(url):
    """Best effort (Gofile changes this now and then): gofile.io/d/<id> -> [(direct link, name)] and the cookie the download needs."""
    import hashlib
    m = re.search(r"gofile\.io/d/([A-Za-z0-9]+)", url)
    if not m:
        return [], ""
    cid = m.group(1)
    ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Safari/537.36"

    def j(cmd):
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        try:
            return json.loads(r.stdout or "{}")
        except Exception:
            return {}
    tk = j(["curl", "-sS", "-A", ua, "-X", "POST", "-H", "Content-Type: application/json", "-d", "{}", "https://api.gofile.io/accounts"])
    tok = (tk.get("data") or {}).get("token", "")
    secrets = [E("GOFILE_WT_SECRET")] if E("GOFILE_WT_SECRET") else []
    secrets += ["12af056dacea0b"]          # the value in use in the public gofile downloader tools; it can change: then set the GOFILE_WT_SECRET secret
    d, err = {}, ""
    for sec in secrets:
        wt = hashlib.sha256(("%s::en-US::%s::%d::%s" % (ua, tok, int(time.time()) // 14400, sec)).encode()).hexdigest()
        r = j(["curl", "-sS", "-A", ua, "-H", "Authorization: Bearer " + tok, "-H", "X-Website-Token: " + wt, "-H", "X-BL: en-US",
               "https://api.gofile.io/contents/%s?cache=true&sortField=createTime&sortDirection=1" % cid])
        if r.get("status") == "ok":
            d = r.get("data") or {}; break
        err = str(r.get("status") or "no answer")
        if "password" in err.lower():
            break
    if not d:
        raise RuntimeError("Gofile said: %s" % err)
    files = []

    def walk(node):
        for ch in (node.get("children") or node.get("contents") or {}).values():
            if ch.get("type") == "file" and ch.get("link") and (str(ch.get("mimetype") or "").startswith("video") or FILE_EXT.search(ch.get("name") or "")):
                files.append((ch["link"], ch.get("name") or "video.mp4"))
            elif ch.get("type") == "folder":
                walk(ch)
    if d.get("type") == "file" and d.get("link"):
        files.append((d["link"], d.get("name") or "video.mp4"))
    walk(d)
    if not files:
        raise RuntimeError("Gofile page has no video file")
    return files, "accountToken=" + tok


def link_download(url, dest):
    cookie = ""
    if "gofile.io/d/" in url:
        try:
            files, cookie = gofile_resolve(url)
        except RuntimeError as e:
            raise RuntimeError("%s. Gofile changes its download system often; send a direct video link (.mp4) instead" % e)
        url = files[0][0]
    cmd = ["curl", "-L", "-sS", "--fail", "--retry", "3", "--connect-timeout", "30", "-A", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Safari/537.36", "-o", dest, url]
    if cookie:
        cmd[1:1] = ["-H", "Cookie: " + cookie, "-H", "Authorization: Bearer " + cookie.split("=", 1)[1]]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError("download failed: " + (r.stderr or "").strip()[-150:])


def is_file_link(url):
    """A plain video file (or a gofile page) is downloaded; everything else (m3u8, mpd, ts, live, archive ...) goes to the recorder."""
    return bool(FILE_EXT.search(url) or "gofile.io/d/" in url)


def run_recorder(text, chat, env_extra=None):
    """Live streams and every stream type of the recorder (HLS .m3u8, MPEG-DASH .mpd, MPEG-TS .ts, timeshift / archive, headers, proxy, ClearKey):
    the same recorder program runs, but only the clips are kept and sent."""
    here = os.path.dirname(os.path.abspath(__file__))
    rec = os.path.join(here, "cliprec.py")
    if not os.path.exists(rec):
        say("❌ cliprec.py is missing in this repository (the clip bot needs it for stream links).")
        return False
    env = dict(os.environ)
    env.update({"CLIPS": "1", "CLIPS_ONLY": "1", "TG_CHAT": str(chat), "CLIP_CHAT": E("CLIP_CHAT") or str(chat),
                "WORKFLOW_FILE": "clipbot.yml", "URL": "ask", "LINK_TEXT": text + " clips", "MINUTES": E("MINUTES") or "0"})
    env.update(env_extra or {})
    print("Starting the recorder for a stream link", flush=True)
    return subprocess.run([sys.executable, rec], env=env).returncode == 0


def process_one(link=None):
    """One video (FILE_ID) or one link (a video file or a Gofile page). True when it ended well."""
    os.makedirs(OUT, exist_ok=True)
    R.clip_reset()
    R.CLIP["on"] = True
    R.clip_words(CAPTION + " clips")
    R.CLIPS_FILE[0] = True; R.ARCHIVE = True
    R.CHAT = CHAT; R.CLIP_CHAT = E("CLIP_CHAT") or CHAT
    path = LOCAL_FILE or os.path.join(OUT, "input.mp4")
    if not LOCAL_FILE:
        try:
            if os.path.exists(path):
                os.remove(path)
            if FILE_ID:
                say(("⏳ <b>Video received.</b> Downloading it (%s)..." % human(FILE_SIZE)) if FILE_SIZE else "⏳ <b>Video received.</b> Downloading it...")
                telethon_download(path)
            elif link:
                if re.search(r"\.(m3u8|mpd)(\?|$)", link, re.I):
                    run_recorder(link + " " + CAPTION, CHAT)
                    return True
                say("⏳ <b>Link received.</b> Downloading the file...")
                link_download(link, path)
            else:
                return False
        except Exception as e:
            say("❌ <b>Could not get the video.</b>\n<code>%s</code>" % esc(mask(str(e))[:300]))
            return False
    if not os.path.exists(path) or os.path.getsize(path) < 100000:
        say("❌ The video file is empty or missing."); return False
    dur = R.media_info(path)[0]
    if dur < 30:
        say("❌ I could not read this video (length %ss)." % int(dur)); return False
    if not R.ensure_tesseract():
        say("❌ The text reader (tesseract) could not be installed."); return False
    say("🔎 Video is ready (%s, %s). Looking for the score on the screen..." % (mmss(dur), human(os.path.getsize(path))))
    box = None
    for _ in range(2):
        box = R._find_box(path, dur)
        if box:
            break
    tmp = os.path.join(OUT, "_look")
    if not box:
        try:
            fr = R._grab(path, dur * 0.3, 1.0, (0, 0, 1, 1), True, tmp, 1280)
            if fr:
                send_photo(CHAT, fr[0][1], "👀 This is what I saw.")
        except Exception:
            pass
        say("❌ <b>I could not find the score on the screen.</b>\nIt must be visible as text like <code>145/3</code> and the over like <code>12.3</code>. No clips were made.")
        return False
    R.CLIP["box"] = box
    R.CLIP["wide"] = (0.0, box[1], 1.0, min(1.0 - box[1], box[3])) if box[2] < 0.95 else None
    try:
        fr = R._grab(path, dur * 0.3, 1.0, box, True, tmp)
        rd = R._pick(R._ocr(fr[0][1]), None) if fr else None
        if fr:
            send_photo(CHAT, fr[0][1], "🔎 <b>Score area found.</b> I read: <code>%s</code>" % (("%d/%d  over %s" % (rd[0], rd[1], ("%d.%d" % divmod(rd[2], 6)) if rd[2] is not None else "?")) if rd else "nothing yet"))
    except Exception:
        pass
    R.clip_analyze(path, 0, dur, False, final=True, avail=dur)
    n = len(R.CLIP_EV)
    R._merge_milestones(path)
    R.clip_flush(path, dur, final=True)
    R.clip_drain()
    k = R.CLIP_ST.get("kinds", [])
    fr_, ok_ = R.CLIP_ST["frames"], R.CLIP_ST["ok"]
    rate = ("\nScore read in %d%% of the pictures." % (100 * ok_ // max(1, fr_))) if fr_ else ""
    ms = sum(1 for x in k if x in ("50", "100", "150", "200"))
    if R.CLIP_ST["sent"]:
        say("✅ <b>Done.</b> %d clip(s): %d × FOUR, %d × SIX, %d × WICKET%s.%s" % (R.CLIP_ST["sent"], k.count("4"), k.count("6"), k.count("W"), (", %d × 50/100" % ms) if ms else "", rate))
    elif fr_ and ok_ * 100 // max(1, fr_) < 40:
        say("⚠️ <b>I could not read the score well</b> (only %d%% of the pictures). The score text may be too small or blurry here.%s" % (100 * ok_ // max(1, fr_), rate))
    else:
        say("ℹ️ Score read, but no 4, 6, wicket or 50/100 was seen in this video.%s" % rate)
    if not LOCAL_FILE:
        try: os.remove(path)
        except OSError: pass
    return True


def listen():
    """No video was given to the job: wait in Telegram for videos / links from the owner (also the ones sent before the job started),
    cut the clips for each, and stop after WAIT_MIN quiet minutes. The owner can go offline after sending."""
    global CHAT, MSG, FILE_ID, FILE_SIZE, CAPTION
    owner = E("OWNER_ID") or E("TG_CHAT")
    wait = float(E("WAIT_MIN") or 20) * 60
    if not owner:
        print("::error title=Owner missing::Secret TG_CHAT (your Telegram id) is not set.", flush=True); return 1
    r = api("getUpdates", {"timeout": "0", "limit": "1"})
    if r.get("error_code") == 409:
        api("deleteWebhook", {"drop_pending_updates": "false"})
    CHAT = owner
    say("🏏 <b>Clip bot is on.</b> Send me a <b>video</b> (up to 2 GB) or a <b>link to a video file</b>. You can go offline after sending.\nI stop after %d quiet minutes.\nOptional words in the caption: <code>pre 30</code> <code>wpre 30</code> <code>post 15</code>" % int(wait / 60))
    off, last_job, t_start, jobs = 0, time.time(), time.time(), 0
    while time.time() - t_start < 5 * 3600 + 40 * 60:
        if time.time() - last_job > wait:
            break
        r = api("getUpdates", {"offset": str(off), "timeout": "25", "allowed_updates": '["message"]'}, timeout=45)
        for u in r.get("result", []) or []:
            off = u["update_id"] + 1
            m = u.get("message") or {}
            if str((m.get("from") or {}).get("id")) != str(owner) and str((m.get("chat") or {}).get("id")) != str(owner):
                continue
            text = (m.get("text") or m.get("caption") or "").strip()
            vid = m.get("video") or (m.get("document") if str((m.get("document") or {}).get("mime_type", "")).startswith("video/") else None) or m.get("animation")
            lk = (re.search(r"https?://\S+", text) or [None])[0]
            if not vid and not lk:
                if re.match(r"/(start|help)", text):
                    say("Send me a video or a link to a video file. I send a clip for every 4, 6 and wicket.")
                continue
            CHAT = str((m.get("chat") or {}).get("id"))
            MSG = str(m.get("message_id") or "")
            FILE_ID = vid["file_id"] if vid else ""
            FILE_SIZE = int(vid.get("file_size") or 0) if vid else 0
            CAPTION = re.sub(r"https?://\S+", " ", text)
            if lk and not vid and not is_file_link(lk):
                say("🎥 <b>Stream link received.</b> Recording it, the clips come here as they happen.\nThis run stays busy with it; for another video start the workflow again.")
                run_recorder(text, CHAT)
                jobs += 1
                break                                                    # a recording can run for hours: after it this run is done
            process_one(lk if not vid else None)
            jobs += 1
            last_job = time.time()
        if not r.get("ok", True) and not r.get("result"):
            time.sleep(3)
    CHAT = owner; MSG = ""
    say("💤 <b>Clip bot stopped</b> (%d video(s) done). Start the workflow again when you have more." % jobs)
    return 0


def feed_test(url):
    """Test only: can this machine read a live-score page? Tells the owner what was found (no clips depend on it yet)."""
    ua = "Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Mobile Safari/537.36"
    os.makedirs(OUT, exist_ok=True)
    out = os.path.join(OUT, "feed_test.html")
    try:
        r = subprocess.run(["curl", "-sS", "-L", "-m", "40", "-A", ua, "-H", "Accept-Language: en-US,en;q=0.9", "-o", out, "-w", "%{http_code} %{url_effective}", url],
                           capture_output=True, text=True, timeout=60)
        code, _, final = (r.stdout or "").partition(" ")
    except Exception as e:
        say("🧪 <b>Score page test</b>\ncould not connect: <code>%s</code>" % esc(repr(e)[:150])); return
    html = ""
    try:
        html = open(out, encoding="utf-8", errors="ignore").read()
    except Exception:
        pass
    text = re.sub(r"<script.*?</script>|<style.*?</style>", " ", html, flags=re.S | re.I)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s+", " ", text)
    low = html.lower()
    marks = {k: (k in low) for k in ("commentary", "batsman", "bowler", "overs", "miniscore", "ballbyball", "captcha", "consent", "unusual traffic")}
    balls = len(re.findall(r"(?<![\d.])\d{1,2}\.[1-6](?![\d.])", text))
    found = [k for k, v in marks.items() if v and k not in ("captcha", "consent", "unusual traffic")]
    blocked = [k for k in ("captcha", "consent", "unusual traffic") if marks[k]]
    verdict = "✅ readable" if (code == "200" and balls >= 5 and found) else ("⚠️ page opens but has little score data (it is probably loaded by JavaScript)" if code == "200" else "❌ blocked or error")
    if E("FEED_DEBUG") == "1":
        try:
            api("sendDocument", {"chat_id": CHAT, "caption": "The page as the bot received it"}, {"document": out})
        except Exception:
            pass
    say("🧪 <b>Score page test</b>\n%s\nHTTP %s · %d KB · over numbers like 12.3 seen: %d\nWords found: %s%s\n<pre>%s</pre>" % (
        verdict, esc(code), len(html) // 1024, balls, esc(", ".join(found) or "none"), ("\nBlock signs: " + esc(", ".join(blocked))) if blocked else "", esc(text[:350])))


def main():
    global CAPTION
    os.makedirs(OUT, exist_ok=True)
    u = E("URL")
    if E("FEED_URL").startswith("http") and E("FEED_DEBUG") == "1":
        try:
            globals()["CHAT"] = E("CHAT") or E("TG_CHAT")
            feed_test(E("FEED_URL"))
        except Exception as e:
            print("Feed test error:", repr(e)[:120], flush=True)
    if u.startswith("enc:") or u.startswith("http"):                      # started by a link: first start of a stream, or the next run of a long recording
        say("🔁 <b>Continuing the recording</b> (new run)." if u.startswith("enc:") else "🎥 <b>Recording the stream.</b>")
        env = {"URL": u} if u.startswith("enc:") or u.startswith("http") else {}
        return 0 if run_recorder(E("LINK_TEXT") or u, E("CHAT") or E("TG_CHAT"), env) else 1
    link = (re.search(r"https?://\S+", E("LINK") or "") or [None])[0]
    if link and not is_file_link(link):
        return 0 if run_recorder(E("LINK") + " " + CAPTION, E("CHAT") or E("TG_CHAT")) else 1
    if FILE_ID or link or LOCAL_FILE:
        return 0 if process_one(link) else 1
    return listen()


if __name__ == "__main__":
    sys.exit(main())
