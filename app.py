"""Nzeru AI: speech data collection API.

Contributors create an account (email and password), read prompts and upload
16 kHz mono WAV clips, and can later play, re-record or delete their own clips. The admin panel is unlocked with a one-time code emailed to ADMIN_EMAIL
and lets the admin review clips and download all or part of the dataset.
"""
import csv
import hashlib
import hmac
import io
import os
import re
import secrets
import smtplib
import sqlite3
import tempfile
import time
import wave
import zipfile
from datetime import datetime, timezone
from email.message import EmailMessage
from pathlib import Path

from flask import Flask, Response, abort, g, jsonify, request, send_file
from itsdangerous import BadSignature, SignatureExpired, URLSafeTimedSerializer
from werkzeug.security import check_password_hash, generate_password_hash

BASE_DIR = Path(__file__).resolve().parent


def load_env(path):
    if not path.exists():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            key, value = line.split("=", 1)
            os.environ.setdefault(key.strip(), value.strip().strip('"').strip("'"))


load_env(BASE_DIR / ".env")

DATA_DIR = Path(os.environ.get("DATA_DIR", BASE_DIR / "data"))
AUDIO_DIR = DATA_DIR / "audio"
PHOTO_DIR = DATA_DIR / "photos"
DB_PATH = DATA_DIR / "speech.db"
ADMIN_EMAIL = os.environ.get("ADMIN_EMAIL", "patrickphandera@gmail.com")
SECRET_KEY = os.environ.get("SECRET_KEY") or secrets.token_hex(32)
FRONTEND_ORIGIN = os.environ.get("FRONTEND_ORIGIN", "http://localhost:3000")
SMTP_HOST = os.environ.get("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT = int(os.environ.get("SMTP_PORT", "587"))
SMTP_USER = os.environ.get("SMTP_USER", "")
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD", "")
DEFAULT_LANGUAGE = os.environ.get("DEFAULT_LANGUAGE", "ny")

CODE_TTL = 10 * 60          # login code valid for 10 minutes
CODE_COOLDOWN = 60          # one code request per minute
CODE_MAX_ATTEMPTS = 5
TOKEN_TTL = 12 * 60 * 60    # admin session lasts 12 hours
SPEAKER_TOKEN_TTL = 30 * 24 * 60 * 60  # contributors stay signed in for 30 days
MIN_PASSWORD = 8
LOGIN_WINDOW, LOGIN_MAX_FAILS = 15 * 60, 8   # lock an email after 8 bad passwords in 15 minutes
EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")
MIN_SECONDS, MAX_SECONDS = 1.0, 30.0
MIN_OWN_TEXT, MAX_OWN_TEXT = 3, 300  # characters, for a contributor's own sentence
MAX_PHOTO_BYTES = 1024 * 1024  # the browser sends a small, square JPEG
STATUSES = ("pending", "validated", "rejected")

AUDIO_DIR.mkdir(parents=True, exist_ok=True)
PHOTO_DIR.mkdir(parents=True, exist_ok=True)

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 20 * 1024 * 1024
serializer = URLSafeTimedSerializer(SECRET_KEY, salt="admin-session")
speaker_serializer = URLSafeTimedSerializer(SECRET_KEY, salt="speaker-session")
failed_logins = {}  # email -> timestamps of recent failed attempts (in memory)

SCHEMA = """
CREATE TABLE IF NOT EXISTS prompts (
    prompt_id TEXT PRIMARY KEY,
    text TEXT NOT NULL,
    domain TEXT DEFAULT '',
    source TEXT DEFAULT '',
    language TEXT NOT NULL,
    active INTEGER DEFAULT 1
);
CREATE TABLE IF NOT EXISTS speakers (
    speaker_id TEXT PRIMARY KEY,
    gender TEXT, age_group TEXT, region TEXT, dialect TEXT,
    native_language TEXT,
    consent_id TEXT NOT NULL,
    consented_at TEXT NOT NULL,
    photo TEXT DEFAULT '',
    show_photo INTEGER DEFAULT 1,
    preferred_name TEXT DEFAULT '',
    country TEXT DEFAULT '',
    record_language TEXT DEFAULT '',
    email TEXT DEFAULT '',
    password_hash TEXT DEFAULT ''
);
CREATE TABLE IF NOT EXISTS recordings (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    file_path TEXT NOT NULL UNIQUE,
    speaker_id TEXT NOT NULL REFERENCES speakers(speaker_id),
    prompt_id TEXT NOT NULL REFERENCES prompts(prompt_id),
    transcript TEXT NOT NULL,
    language TEXT NOT NULL,
    duration_sec REAL NOT NULL,
    recorded_at TEXT NOT NULL,
    device TEXT, environment TEXT,
    status TEXT NOT NULL DEFAULT 'pending',
    origin TEXT NOT NULL DEFAULT 'prompt'  -- 'prompt' (read a given sentence) or 'own' (contributor's text)
);
CREATE TABLE IF NOT EXISTS login_codes (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    code_hash TEXT NOT NULL,
    created_at REAL NOT NULL,
    attempts INTEGER DEFAULT 0,
    used INTEGER DEFAULT 0
);
"""

SAMPLE_PROMPTS = [
    ("Muli bwanji lero?", "greetings"),
    ("Ndikupita ku msika kukagula zipatso.", "daily_life"),
    ("Mvula yambiri inagwa usiku watha.", "weather"),
    ("Ana akupita ku sukulu m'mawa uliwonse.", "daily_life"),
    ("Tikumane pa ola la khumi ndi chimodzi.", "time"),
]


def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA foreign_keys = ON")
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.executescript(SCHEMA)
    columns = {r[1] for r in conn.execute("PRAGMA table_info(speakers)")}
    for name, kind in (("photo", "TEXT DEFAULT ''"), ("show_photo", "INTEGER DEFAULT 1"),
                       ("preferred_name", "TEXT DEFAULT ''"), ("country", "TEXT DEFAULT ''"),
                       ("record_language", "TEXT DEFAULT ''"), ("email", "TEXT DEFAULT ''"),
                       ("password_hash", "TEXT DEFAULT ''")):
        if name not in columns:
            conn.execute(f"ALTER TABLE speakers ADD COLUMN {name} {kind}")
    conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS speakers_email ON speakers(email) WHERE email != ''")
    if "origin" not in {r[1] for r in conn.execute("PRAGMA table_info(recordings)")}:
        conn.execute("ALTER TABLE recordings ADD COLUMN origin TEXT NOT NULL DEFAULT 'prompt'")
    if conn.execute("SELECT COUNT(*) FROM prompts").fetchone()[0] == 0:
        for i, (text, domain) in enumerate(SAMPLE_PROMPTS, 1):
            conn.execute(
                "INSERT INTO prompts VALUES (?, ?, ?, 'sample', ?, 1)",
                (f"P{i:04d}", text, domain, DEFAULT_LANGUAGE),
            )
    conn.commit()
    conn.close()


def now_iso():
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def hash_code(code):
    return hmac.new(SECRET_KEY.encode(), code.encode(), hashlib.sha256).hexdigest()


def body():
    return request.get_json(silent=True) or {}


@app.after_request
def cors(resp):
    resp.headers["Access-Control-Allow-Origin"] = FRONTEND_ORIGIN
    resp.headers["Access-Control-Allow-Headers"] = "Content-Type, Authorization"
    resp.headers["Access-Control-Allow-Methods"] = "GET, POST, PATCH, DELETE, OPTIONS"
    resp.headers["Access-Control-Expose-Headers"] = "Content-Disposition"
    return resp


@app.before_request
def preflight():
    if request.method == "OPTIONS":
        return Response(status=204)


@app.errorhandler(400)
@app.errorhandler(401)
@app.errorhandler(403)
@app.errorhandler(404)
@app.errorhandler(413)
@app.errorhandler(429)
def json_error(err):
    return jsonify(error=getattr(err, "description", str(err))), err.code


def require_admin():
    header = request.headers.get("Authorization", "")
    token = header[7:] if header.startswith("Bearer ") else request.args.get("token", "")
    try:
        data = serializer.loads(token, max_age=TOKEN_TTL)
    except (BadSignature, SignatureExpired):
        abort(401, "Admin session expired, please sign in again.")
    if data.get("email") != ADMIN_EMAIL:
        abort(401, "Not authorised.")


def speaker_token(speaker_id):
    return speaker_serializer.dumps({"sid": speaker_id})


def require_speaker():
    """The signed-in contributor's row, or 401."""
    header = request.headers.get("Authorization", "")
    token = header[7:] if header.startswith("Bearer ") else request.args.get("token", "")
    try:
        data = speaker_serializer.loads(token, max_age=SPEAKER_TOKEN_TTL)
    except (BadSignature, SignatureExpired):
        abort(401, "Please sign in to continue.")
    row = db().execute("SELECT * FROM speakers WHERE speaker_id = ?", (data.get("sid"),)).fetchone()
    if not row:
        abort(401, "Please sign in to continue.")
    return row


def require_complete_speaker():
    row = require_speaker()
    if not profile_complete(row):
        abort(403, "Please complete your profile before recording.")
    return row


PROFILE_FIELDS = ("gender", "age_group", "region", "dialect", "native_language",
                  "preferred_name", "country")


# A contributor must fill these in (on their dashboard) before recording.
REQUIRED_PROFILE = ("preferred_name", "country", "region", "native_language", "gender", "age_group")


def profile_complete(row):
    return all(row[k] for k in REQUIRED_PROFILE) and bool(row["record_language"])


def clean_profile(data):
    return {k: str(data.get(k, "")).strip()[:64] for k in PROFILE_FIELDS if k in data}


def valid_record_language(code):
    """Speakers can only record in a language that has sentences to read."""
    code = str(code or "").strip()
    found = db().execute("SELECT 1 FROM prompts WHERE active = 1 AND language = ?", (code,)).fetchone()
    return code if found else DEFAULT_LANGUAGE


def delete_photo(name):
    if name and (PHOTO_DIR / name).is_file():
        (PHOTO_DIR / name).unlink()


# ---------------------------------------------------------------- contributors

@app.get("/api/health")
def health():
    return jsonify(ok=True)


def save_photo(upload):
    raw = upload.read(MAX_PHOTO_BYTES + 1)
    if len(raw) > MAX_PHOTO_BYTES:
        abort(400, "Photo is too large.")
    if not raw.startswith(b"\xff\xd8\xff"):
        abort(400, "Photo must be a JPEG image.")
    # A random name, so the photo URL can't be tied back to a speaker ID.
    name = f"{secrets.token_hex(16)}.jpg"
    (PHOTO_DIR / name).write_bytes(raw)
    return name


@app.post("/api/speakers")
def create_speaker():
    """Create a contributor account. JSON, or multipart form data when a photo is attached."""
    data = request.form if request.files or request.form else body()
    if data.get("consent") not in (True, "true"):
        abort(400, "Consent is required before recording.")
    email = str(data.get("email", "")).strip().lower()
    password = str(data.get("password", ""))
    if not EMAIL_RE.match(email) or len(email) > 254:
        abort(400, "Enter a valid email address.")
    if len(password) < MIN_PASSWORD:
        abort(400, f"Password must be at least {MIN_PASSWORD} characters.")
    conn = db()
    if conn.execute("SELECT 1 FROM speakers WHERE email = ?", (email,)).fetchone():
        abort(400, "An account with this email already exists. Sign in instead.")
    count = conn.execute("SELECT COUNT(*) FROM speakers").fetchone()[0]
    speaker_id = f"spk{count + 1:03d}"
    while conn.execute("SELECT 1 FROM speakers WHERE speaker_id = ?", (speaker_id,)).fetchone():
        count += 1
        speaker_id = f"spk{count + 1:03d}"
    profile = {k: "" for k in PROFILE_FIELDS} | clean_profile(data)
    photo = save_photo(request.files["photo"]) if request.files.get("photo") else ""
    show_photo = 0 if data.get("show_photo") in (False, "false", "0") else 1
    conn.execute(
        """INSERT INTO speakers (speaker_id, gender, age_group, region, dialect,
               native_language, preferred_name, country, consent_id, consented_at,
               photo, show_photo, record_language, email, password_hash)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (speaker_id, *(profile[k] for k in PROFILE_FIELDS), f"C{speaker_id[3:]}", now_iso(),
         photo, show_photo, valid_record_language(data.get("record_language")),
         email, generate_password_hash(password)),
    )
    conn.commit()
    return jsonify(speaker_id=speaker_id, token=speaker_token(speaker_id)), 201


@app.post("/api/auth/login")
def login():
    data = body()
    email = str(data.get("email", "")).strip().lower()
    now = time.time()
    recent = [t for t in failed_logins.get(email, []) if now - t < LOGIN_WINDOW]
    if len(recent) >= LOGIN_MAX_FAILS:
        abort(429, "Too many attempts. Please wait 15 minutes and try again.")
    row = db().execute("SELECT speaker_id, password_hash FROM speakers WHERE email = ?",
                       (email,)).fetchone()
    if not row or not row["password_hash"] or \
            not check_password_hash(row["password_hash"], str(data.get("password", ""))):
        failed_logins[email] = recent + [now]
        abort(401, "Incorrect email or password.")
    failed_logins.pop(email, None)
    return jsonify(speaker_id=row["speaker_id"], token=speaker_token(row["speaker_id"]))


def me_json(row):
    done = db().execute("SELECT COUNT(*) FROM recordings WHERE speaker_id = ?",
                        (row["speaker_id"],)).fetchone()[0]
    return {**{k: row[k] for k in PROFILE_FIELDS}, "speaker_id": row["speaker_id"],
            "email": row["email"], "record_language": row["record_language"],
            "show_photo": bool(row["show_photo"]), "has_photo": bool(row["photo"]),
            "profile_complete": profile_complete(row), "recorded": done}


@app.get("/api/me")
def get_me():
    return jsonify(me_json(require_speaker()))


@app.patch("/api/me")
def update_me():
    """Update the profile. Multipart when a new photo is attached."""
    row = require_speaker()
    data = request.form if request.files or request.form else body()
    updates = clean_profile(data)
    if "record_language" in data:
        updates["record_language"] = valid_record_language(data.get("record_language"))
    if "show_photo" in data:
        updates["show_photo"] = 0 if data.get("show_photo") in (False, "false", "0") else 1
    if request.files.get("photo"):
        updates["photo"] = save_photo(request.files["photo"])
        delete_photo(row["photo"])
    elif data.get("remove_photo") in (True, "true"):
        updates["photo"] = ""
        delete_photo(row["photo"])
    if updates:
        conn = db()
        conn.execute(f"UPDATE speakers SET {', '.join(f'{k} = ?' for k in updates)} WHERE speaker_id = ?",
                     (*updates.values(), row["speaker_id"]))
        conn.commit()
    fresh = db().execute("SELECT * FROM speakers WHERE speaker_id = ?", (row["speaker_id"],)).fetchone()
    return jsonify(me_json(fresh))


@app.get("/api/me/photo")
def my_photo():
    row = require_speaker()
    if not row["photo"] or not (PHOTO_DIR / row["photo"]).is_file():
        abort(404, "No photo.")
    return send_file(PHOTO_DIR / row["photo"], mimetype="image/jpeg", max_age=0)


def my_recording(row, rec_id):
    rec = db().execute("SELECT * FROM recordings WHERE id = ? AND speaker_id = ?",
                       (rec_id, row["speaker_id"])).fetchone()
    if not rec:
        abort(404, "Recording not found.")
    return rec


MY_RECORDING_FIELDS = ("id", "prompt_id", "transcript", "language", "duration_sec", "recorded_at",
                       "status", "origin")


@app.get("/api/me/recordings")
def my_recordings():
    row = require_speaker()
    rows = db().execute("SELECT * FROM recordings WHERE speaker_id = ? ORDER BY id DESC",
                        (row["speaker_id"],)).fetchall()
    return jsonify(recordings=[{k: r[k] for k in MY_RECORDING_FIELDS} for r in rows])


@app.get("/api/me/recordings/<int:rec_id>")
def my_recording_detail(rec_id):
    rec = my_recording(require_speaker(), rec_id)
    return jsonify({k: rec[k] for k in MY_RECORDING_FIELDS})


@app.get("/api/me/recordings/<int:rec_id>/audio")
def my_recording_audio(rec_id):
    rec = my_recording(require_speaker(), rec_id)
    return send_file(DATA_DIR / rec["file_path"], mimetype="audio/wav", max_age=0)


@app.delete("/api/me/recordings/<int:rec_id>")
def delete_my_recording(rec_id):
    rec = my_recording(require_speaker(), rec_id)
    conn = db()
    conn.execute("DELETE FROM recordings WHERE id = ?", (rec["id"],))
    conn.commit()
    path = DATA_DIR / rec["file_path"]
    if path.is_file():
        path.unlink()
    return jsonify(deleted=rec["id"])


@app.get("/api/community")
def community():
    """Public, anonymous totals and recent contributors for the home page."""
    conn = db()
    totals = conn.execute(
        """SELECT COUNT(DISTINCT speaker_id) AS contributors, COUNT(*) AS clips,
                  COALESCE(SUM(duration_sec), 0) AS seconds
           FROM recordings WHERE status != 'rejected'""").fetchone()
    regions = conn.execute(
        """SELECT COUNT(DISTINCT LOWER(TRIM(s.region))) FROM speakers s
           JOIN recordings r ON r.speaker_id = s.speaker_id
           WHERE TRIM(s.region) != '' AND r.status != 'rejected'""").fetchone()[0]
    me_id = request.args.get("speaker_id", "")
    # Every contributor's totals, best first. Only an avatar seed, region, counts
    # and the photo (if the speaker chose to show it) leave the server: no IDs,
    # gender or age.
    rows = conn.execute(
        """SELECT s.speaker_id, s.region, s.photo, s.show_photo, COUNT(r.id) AS clips,
                  SUM(r.duration_sec) AS seconds, MAX(r.recorded_at) AS last_at
           FROM speakers s JOIN recordings r ON r.speaker_id = s.speaker_id
           WHERE r.status != 'rejected'
           GROUP BY s.speaker_id ORDER BY clips DESC, seconds DESC""").fetchall()

    def public(r, rank=None):
        return {"seed": int(hashlib.md5(r["speaker_id"].encode()).hexdigest()[:6], 16),
                "region": r["region"] or "", "clips": r["clips"],
                "photo": f"/api/photos/{r['photo']}" if r["photo"] and r["show_photo"] else None,
                "seconds": round(r["seconds"] or 0, 1), "last_at": r["last_at"],
                "rank": rank, "is_you": bool(me_id) and r["speaker_id"] == me_id}

    ranked = [public(r, i + 1) for i, r in enumerate(rows)]
    top = ranked[:5]
    me = next((c for c in ranked if c["is_you"]), None)
    recent = sorted(ranked, key=lambda c: c["last_at"], reverse=True)[:40]
    return jsonify(contributors=totals["contributors"], clips=totals["clips"],
                   seconds=totals["seconds"], regions=regions, recent=recent, top=top, me=me)


@app.get("/api/photos/<name>")
def photo(name):
    row = db().execute("SELECT 1 FROM speakers WHERE photo = ? AND show_photo = 1 AND photo != ''",
                       (name,)).fetchone()
    if not row or not (PHOTO_DIR / name).is_file():
        abort(404, "Photo not found.")
    return send_file(PHOTO_DIR / name, mimetype="image/jpeg", max_age=86400)


@app.get("/api/prompt-languages")
def prompt_languages():
    """Languages that have sentences to read, most sentences first."""
    rows = db().execute(
        """SELECT language, COUNT(*) AS prompts FROM prompts WHERE active = 1
           GROUP BY language ORDER BY prompts DESC""").fetchall()
    return jsonify(languages=[dict(r) for r in rows])


@app.get("/api/prompts/next")
def next_prompt():
    speaker = require_complete_speaker()
    speaker_id = speaker["speaker_id"]
    skip = [s for s in request.args.get("skip", "").split(",") if s]
    conn = db()
    # Older speakers have no recording language; they see every prompt.
    language = speaker["record_language"] or None
    lang_sql, lang_args = ("AND language = ?", (language,)) if language else ("", ())
    total = conn.execute(f"SELECT COUNT(*) FROM prompts WHERE active = 1 {lang_sql}",
                         lang_args).fetchone()[0]
    done = conn.execute(
        f"""SELECT COUNT(*) FROM recordings WHERE speaker_id = ?
            AND prompt_id IN (SELECT prompt_id FROM prompts WHERE active = 1 {lang_sql})""",
        (speaker_id, *lang_args)).fetchone()[0]
    placeholders = ",".join("?" * len(skip))
    skip_sql = f"AND prompt_id NOT IN ({placeholders})" if skip else ""
    # Prefer prompts this speaker hasn't read and that have the fewest recordings overall.
    row = conn.execute(
        f"""SELECT p.*, (SELECT COUNT(*) FROM recordings r WHERE r.prompt_id = p.prompt_id) AS n
            FROM prompts p
            WHERE active = 1 {lang_sql} {skip_sql}
              AND prompt_id NOT IN (SELECT prompt_id FROM recordings WHERE speaker_id = ?)
            ORDER BY n, RANDOM() LIMIT 1""",
        (*lang_args, *skip, speaker_id),
    ).fetchone()
    prompt = None
    if row:
        prompt = {k: row[k] for k in ("prompt_id", "text", "domain", "language")}
    return jsonify(prompt=prompt, recorded=done, total=total)


def new_prompt_id(conn):
    n = conn.execute("SELECT COUNT(*) FROM prompts").fetchone()[0] + 1
    while conn.execute("SELECT 1 FROM prompts WHERE prompt_id = ?", (f"P{n:04d}",)).fetchone():
        n += 1
    return f"P{n:04d}"


def read_wav(raw):
    try:
        with wave.open(io.BytesIO(raw)) as w:
            channels, width, rate, frames = (w.getnchannels(), w.getsampwidth(),
                                             w.getframerate(), w.getnframes())
    except (wave.Error, EOFError):
        abort(400, "Audio must be a WAV file.")
    if channels != 1 or width != 2 or rate != 16000:
        abort(400, "Audio must be 16 kHz, 16-bit, mono WAV.")
    return frames / rate


@app.post("/api/recordings")
def upload_recording():
    """Save a new clip, or replace one of the speaker's own clips when replace_id is given.

    Instead of prompt_id, a contributor may send own_text: their own sentence. It is stored as
    an inactive prompt (never served to others) and the clip is marked origin='own' for review.
    """
    speaker = require_complete_speaker()
    speaker_id = speaker["speaker_id"]
    audio = request.files.get("audio")
    prompt_id = request.form.get("prompt_id", "")
    if not audio:
        abort(400, "No audio uploaded.")
    conn = db()
    old = None
    own_text = " ".join(request.form.get("own_text", "").split())
    if request.form.get("replace_id"):
        old = my_recording(speaker, int(request.form["replace_id"]))
        prompt_id = old["prompt_id"]
    elif own_text:
        if not MIN_OWN_TEXT <= len(own_text) <= MAX_OWN_TEXT:
            abort(400, f"Your text must be between {MIN_OWN_TEXT} and {MAX_OWN_TEXT} characters.")
        prompt_id = None  # created below, once the audio has passed its checks
    prompt = None if prompt_id is None else conn.execute("SELECT * FROM prompts WHERE prompt_id = ?", (prompt_id,)).fetchone()
    if prompt_id is not None and not prompt:
        abort(400, "Unknown prompt.")

    raw = audio.read()
    duration = read_wav(raw)
    if not MIN_SECONDS <= duration <= MAX_SECONDS:
        abort(400, f"Clips must be between {MIN_SECONDS:.0f} and {MAX_SECONDS:.0f} seconds.")

    device = request.form.get("device", "")[:32]
    environment = request.form.get("environment", "")[:32]
    if old:
        # Re-record: overwrite the file in place and send it back for review.
        (DATA_DIR / old["file_path"]).write_bytes(raw)
        conn.execute(
            """UPDATE recordings SET duration_sec = ?, recorded_at = ?, device = ?, environment = ?,
                   status = 'pending' WHERE id = ?""",
            (round(duration, 2), now_iso(), device, environment, old["id"]))
        conn.commit()
        return jsonify(id=old["id"], file_path=old["file_path"], duration_sec=round(duration, 2))

    origin = "prompt"
    if prompt is None:
        prompt_id = new_prompt_id(conn)
        language = speaker["record_language"] or DEFAULT_LANGUAGE
        conn.execute("INSERT INTO prompts VALUES (?, ?, 'contributed', ?, ?, 0)",
                     (prompt_id, own_text, f"contributor:{speaker_id}", language))
        prompt = {"text": own_text, "language": language}
        origin = "own"

    speaker_dir = AUDIO_DIR / speaker_id
    speaker_dir.mkdir(exist_ok=True)
    n = conn.execute("SELECT COUNT(*) FROM recordings WHERE speaker_id = ?",
                     (speaker_id,)).fetchone()[0] + 1
    while (speaker_dir / f"{speaker_id}_{n:06d}.wav").exists():
        n += 1
    rel_path = f"audio/{speaker_id}/{speaker_id}_{n:06d}.wav"
    (DATA_DIR / rel_path).write_bytes(raw)

    conn.execute(
        """INSERT INTO recordings (file_path, speaker_id, prompt_id, transcript, language,
               duration_sec, recorded_at, device, environment, origin)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
        (rel_path, speaker_id, prompt_id, prompt["text"], prompt["language"],
         round(duration, 2), now_iso(), device, environment, origin),
    )
    conn.commit()
    return jsonify(file_path=rel_path, duration_sec=round(duration, 2)), 201


# ----------------------------------------------------------------------- admin

def send_code_email(code):
    if not (SMTP_USER and SMTP_PASSWORD):
        print(f"\n*** SMTP not configured. Admin login code for {ADMIN_EMAIL}: {code} ***\n",
              flush=True)
        return
    msg = EmailMessage()
    msg["Subject"] = f"Your Nzeru AI admin code: {code}"
    msg["From"] = f"Nzeru AI <{SMTP_USER}>"
    msg["To"] = ADMIN_EMAIL
    msg.set_content(
        f"Your admin login code is {code}\n\n"
        "It expires in 10 minutes. If you didn't request it, you can ignore this email."
    )
    with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=20) as smtp:
        smtp.starttls()
        smtp.login(SMTP_USER, SMTP_PASSWORD)
        smtp.send_message(msg)


def masked_email():
    name, domain = ADMIN_EMAIL.split("@")
    return f"{name[:2]}{'•' * max(len(name) - 2, 1)}@{domain}"


@app.post("/api/admin/request-code")
def request_code():
    conn = db()
    last = conn.execute("SELECT created_at FROM login_codes ORDER BY id DESC LIMIT 1").fetchone()
    if last and time.time() - last["created_at"] < CODE_COOLDOWN:
        abort(429, "A code was just sent. Please wait a minute before requesting another.")
    code = f"{secrets.randbelow(1_000_000):06d}"
    conn.execute("UPDATE login_codes SET used = 1 WHERE used = 0")
    conn.execute("INSERT INTO login_codes (code_hash, created_at) VALUES (?, ?)",
                 (hash_code(code), time.time()))
    conn.commit()
    try:
        send_code_email(code)
    except (smtplib.SMTPException, OSError) as exc:
        app.logger.error("Failed to send code email: %s", exc)
        abort(400, "Could not send the verification email. Check the SMTP settings.")
    return jsonify(sent_to=masked_email())


@app.post("/api/admin/verify")
def verify_code():
    code = str(body().get("code", "")).strip()
    conn = db()
    row = conn.execute(
        "SELECT * FROM login_codes WHERE used = 0 ORDER BY id DESC LIMIT 1").fetchone()
    if not row or time.time() - row["created_at"] > CODE_TTL:
        abort(401, "Code expired. Request a new one.")
    if row["attempts"] >= CODE_MAX_ATTEMPTS:
        abort(401, "Too many attempts. Request a new code.")
    if not hmac.compare_digest(row["code_hash"], hash_code(code)):
        conn.execute("UPDATE login_codes SET attempts = attempts + 1 WHERE id = ?", (row["id"],))
        conn.commit()
        abort(401, "Incorrect code.")
    conn.execute("UPDATE login_codes SET used = 1 WHERE id = ?", (row["id"],))
    conn.commit()
    return jsonify(token=serializer.dumps({"email": ADMIN_EMAIL}), email=ADMIN_EMAIL)


@app.get("/api/admin/stats")
def stats():
    require_admin()
    conn = db()
    totals = conn.execute(
        "SELECT COUNT(*) AS clips, COALESCE(SUM(duration_sec), 0) AS seconds FROM recordings"
    ).fetchone()
    by_status = {s: {"clips": 0, "seconds": 0} for s in STATUSES}
    for r in conn.execute("SELECT status, COUNT(*) c, SUM(duration_sec) s FROM recordings "
                          "GROUP BY status"):
        by_status[r["status"]] = {"clips": r["c"], "seconds": r["s"] or 0}
    speakers = [dict(r) for r in conn.execute(
        """SELECT s.speaker_id, s.gender, s.age_group, s.region,
                  COUNT(r.id) AS clips, COALESCE(SUM(r.duration_sec), 0) AS seconds
           FROM speakers s LEFT JOIN recordings r ON r.speaker_id = s.speaker_id
           GROUP BY s.speaker_id ORDER BY s.speaker_id""")]
    prompts = conn.execute("SELECT COUNT(*) FROM prompts WHERE active = 1").fetchone()[0]
    languages = [r[0] for r in conn.execute("SELECT DISTINCT language FROM recordings")]
    return jsonify(clips=totals["clips"], seconds=totals["seconds"], by_status=by_status,
                   speakers=speakers, prompts=prompts, languages=languages)


def filtered_recordings(args):
    where, params = [], []
    statuses = [s for s in args.get("status", "").split(",") if s in STATUSES]
    if statuses:
        where.append(f"status IN ({','.join('?' * len(statuses))})")
        params += statuses
    speakers = [s for s in args.get("speakers", "").split(",") if s]
    if speakers:
        where.append(f"speaker_id IN ({','.join('?' * len(speakers))})")
        params += speakers
    if args.get("language"):
        where.append("language = ?")
        params.append(args["language"])
    if args.get("origin") in ("prompt", "own"):
        where.append("origin = ?")
        params.append(args["origin"])
    if args.get("date_from"):
        where.append("recorded_at >= ?")
        params.append(args["date_from"])
    if args.get("date_to"):
        where.append("recorded_at < date(?, '+1 day')")
        params.append(args["date_to"])
    sql = "SELECT * FROM recordings"
    if where:
        sql += " WHERE " + " AND ".join(where)
    sql += " ORDER BY id DESC"
    return [dict(r) for r in db().execute(sql, params)]


@app.get("/api/admin/recordings")
def list_recordings():
    require_admin()
    rows = filtered_recordings(request.args)
    limit = min(int(request.args.get("limit", 100)), 500)
    seconds = round(sum(r["duration_sec"] for r in rows), 2)
    return jsonify(total=len(rows), seconds=seconds, recordings=rows[:limit])


@app.patch("/api/admin/recordings/<int:rec_id>")
def review_recording(rec_id):
    """Set a clip's review status, and for a contributor's own text, optionally correct the text."""
    require_admin()
    data = body()
    conn = db()
    rec = conn.execute("SELECT * FROM recordings WHERE id = ?", (rec_id,)).fetchone()
    if not rec:
        abort(404, "Recording not found.")
    updates = {}
    if "status" in data:
        if data["status"] not in STATUSES:
            abort(400, "Invalid status.")
        updates["status"] = data["status"]
    if "transcript" in data:
        if rec["origin"] != "own":
            abort(400, "Only a contributor's own text can be edited.")
        text = " ".join(str(data["transcript"]).split())
        if not MIN_OWN_TEXT <= len(text) <= MAX_OWN_TEXT:
            abort(400, f"Text must be between {MIN_OWN_TEXT} and {MAX_OWN_TEXT} characters.")
        updates["transcript"] = text
        conn.execute("UPDATE prompts SET text = ? WHERE prompt_id = ?", (text, rec["prompt_id"]))
    if not updates:
        abort(400, "Nothing to change.")
    conn.execute(f"UPDATE recordings SET {', '.join(f'{k} = ?' for k in updates)} WHERE id = ?",
                 (*updates.values(), rec_id))
    conn.commit()
    return jsonify(id=rec_id, **updates)


@app.get("/api/admin/audio/<int:rec_id>")
def play_audio(rec_id):
    require_admin()
    row = db().execute("SELECT file_path FROM recordings WHERE id = ?", (rec_id,)).fetchone()
    if not row:
        abort(404, "Recording not found.")
    return send_file(DATA_DIR / row["file_path"], mimetype="audio/wav")


@app.post("/api/admin/prompts")
def add_prompts():
    require_admin()
    data = body()
    lines = [l.strip() for l in str(data.get("text", "")).splitlines() if l.strip()]
    if not lines:
        abort(400, "Add at least one sentence.")
    language = str(data.get("language") or DEFAULT_LANGUAGE).strip()[:16]
    domain = str(data.get("domain", "")).strip()[:32]
    source = str(data.get("source", "")).strip()[:64]
    conn = db()
    # Contributors' own sentences are inactive prompts; they don't block adding the same text.
    existing = {r[0] for r in conn.execute("SELECT text FROM prompts WHERE active = 1")}
    added = 0
    for line in lines:
        if line in existing:
            continue
        conn.execute("INSERT INTO prompts VALUES (?, ?, ?, ?, ?, 1)",
                     (new_prompt_id(conn), line, domain, source, language))
        existing.add(line)
        added += 1
    conn.commit()
    return jsonify(added=added, skipped=len(lines) - added)


def to_csv(rows, columns):
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=columns, extrasaction="ignore")
    writer.writeheader()
    writer.writerows(rows)
    return buf.getvalue()


def speaker_split(speaker_ids):
    """Deterministic ~80/10/10 split by speaker so no voice appears in two splits."""
    ordered = sorted(speaker_ids, key=lambda s: hashlib.md5(s.encode()).hexdigest())
    n = len(ordered)
    n_test = max(1, round(n * 0.1)) if n >= 3 else 0
    n_dev = max(1, round(n * 0.1)) if n >= 3 else 0
    split = {s: "test" for s in ordered[:n_test]}
    split.update({s: "dev" for s in ordered[n_test:n_test + n_dev]})
    split.update({s: "train" for s in ordered[n_test + n_dev:]})
    return split


METADATA_COLUMNS = ["file_path", "speaker_id", "prompt_id", "transcript", "language",
                    "duration_sec", "recorded_at", "device", "environment", "status", "origin"]


@app.get("/api/admin/export")
def export():
    require_admin()
    rows = filtered_recordings(request.args)
    include_audio = request.args.get("audio", "1") == "1"
    conn = db()
    speaker_ids = sorted({r["speaker_id"] for r in rows})
    prompt_ids = sorted({r["prompt_id"] for r in rows})
    speakers = [dict(r) for r in conn.execute(
        f"SELECT * FROM speakers WHERE speaker_id IN ({','.join('?' * len(speaker_ids))})",
        speaker_ids)] if speaker_ids else []
    prompts = [dict(r) for r in conn.execute(
        f"SELECT * FROM prompts WHERE prompt_id IN ({','.join('?' * len(prompt_ids))})",
        prompt_ids)] if prompt_ids else []

    stamp = datetime.now().strftime("%Y%m%d_%H%M")
    root = f"nzeru_ai_dataset_{stamp}"
    buf = tempfile.TemporaryFile()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr(f"{root}/metadata.csv", to_csv(rows, METADATA_COLUMNS))
        z.writestr(f"{root}/speakers.csv", to_csv(speakers, [
            "speaker_id", "gender", "age_group", "country", "region", "dialect",
            "native_language", "record_language", "consent_id"]))
        z.writestr(f"{root}/prompts.csv", to_csv(prompts, [
            "prompt_id", "text", "domain", "source", "language"]))
        split = speaker_split(speaker_ids)
        for name in ("train", "dev", "test"):
            part = [r for r in rows if split.get(r["speaker_id"]) == name]
            z.writestr(f"{root}/{name}.csv", to_csv(part, METADATA_COLUMNS))
        hours = sum(r["duration_sec"] for r in rows) / 3600
        filters = {k: v for k, v in request.args.items() if k != "token" and v} or "none"
        z.writestr(f"{root}/README.md", (
            f"# Nzeru AI dataset export\n\nExported: {now_iso()}\n\n"
            f"- Clips: {len(rows)}\n- Hours: {hours:.2f}\n- Speakers: {len(speaker_ids)}\n"
            f"- Audio: 16 kHz, 16-bit, mono WAV\n- Filters: {filters}\n\n"
            "Splits are made by speaker, so no voice appears in more than one split.\n"))
        if include_audio:
            for r in rows:
                path = DATA_DIR / r["file_path"]
                if path.exists():
                    # WAV is already PCM, so store instead of compressing.
                    z.write(path, f"{root}/{r['file_path']}", compress_type=zipfile.ZIP_STORED)
    buf.seek(0)
    return send_file(buf, mimetype="application/zip", as_attachment=True,
                     download_name=f"{root}.zip")


init_db()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)
