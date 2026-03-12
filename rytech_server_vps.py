"""
Rytech SummarAI - VPS Server
Author: Daniel Ryan
Version: 3.2.0 (VPS + Multi-User Auth)
"""

import sys, os, json, shutil, threading, time, socket, mimetypes, logging
import smtplib, ssl
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from datetime import datetime, timedelta
import urllib.parse, urllib.request, urllib.error
import hashlib, base64, sqlite3
import hmac as _hmac
import secrets as _secrets
import struct, hashlib, time as _time_mod
from datetime import datetime, timedelta
from http.server import HTTPServer, BaseHTTPRequestHandler

# ── Paths ──────────────────────────────────────────────────────────
BASE_DIR   = os.path.dirname(os.path.abspath(__file__))
CONFIG_DIR = BASE_DIR

HTML_FILE    = os.path.join(BASE_DIR,   'rytech-meeting-manager.html')
CONFIG_FILE  = os.path.join(CONFIG_DIR, 'config.json')
DATA_FILE    = os.path.join(CONFIG_DIR, 'meetings_data.json')
DATA_V2_FILE = os.path.join(CONFIG_DIR, 'v2_data.json')
DB_FILE      = os.path.join(CONFIG_DIR, 'rytech_auth.db')
JWT_KEY_FILE = os.path.join(CONFIG_DIR, 'jwt_secret.key')

CUSTOMERS_BASE = os.path.join(CONFIG_DIR, 'customers')
TEMPLATES_SRC       = '/opt/rytech/Templates'
CUSTOMERS_BASE_DIR  = '/opt/rytech/Customers'   # Base dir for local customer folders

# ── Role/permission definitions ────────────────────────────────────
ALL_SECTIONS  = {'dashboard','calendar','finance','monzo','xero','zoho',
                 'action1','datto','notes','admin'}
ROLE_DEFAULTS = {
    'superadmin': ALL_SECTIONS,
    'admin':      ALL_SECTIONS - {'admin'},
    'manager':    ALL_SECTIONS - {'admin'},
    'staff':      {'dashboard','calendar','zoho','notes'},
}


# ══════════════════════════════════════════════════════════════════
#  DATA HELPERS
# ══════════════════════════════════════════════════════════════════

def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception:
            pass
    return {}


def load_meetings():
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
                if isinstance(data, list):
                    return data
        except Exception:
            pass
    return []


def save_meetings(meetings):
    tmp = DATA_FILE + '.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(meetings, f, ensure_ascii=False, indent=2)
        os.replace(tmp, DATA_FILE)
        return True
    except Exception as e:
        print(f"  [WARN] Could not save meetings: {e}")
        try: os.unlink(tmp)
        except Exception: pass
        return False


def load_v2_data():
    if os.path.exists(DATA_V2_FILE):
        try:
            with open(DATA_V2_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception:
            pass
    return {}


def save_v2_data(data):
    tmp = DATA_V2_FILE + '.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, DATA_V2_FILE)
        return True
    except Exception as e:
        print(f"  [WARN] Could not save v2 data: {e}")
        try: os.unlink(tmp)
        except Exception: pass
        return False


def find_free_port(start=8765, end=8900):
    for port in range(start, end):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind(('0.0.0.0', port))
                return port
            except OSError:
                continue
    raise RuntimeError("No free port found in range.")


def _sec_headers(h):
    h.send_header('X-Frame-Options',        'SAMEORIGIN')
    h.send_header('X-Content-Type-Options', 'nosniff')
    h.send_header('Referrer-Policy',        'strict-origin-when-cross-origin')
    h.send_header('Permissions-Policy',     'geolocation=(), camera=(), microphone=()')
    # Content Security Policy
    # unsafe-inline required: app uses extensive inline styles and onclick handlers in the single-file SPA
    # blob: and data: required: pdf.js workers, canvas export, ICS/vCard generation
    csp = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline' 'unsafe-eval' "
            "https://cdnjs.cloudflare.com "
            "https://cdn.jsdelivr.net; "
        "style-src 'self' 'unsafe-inline' "
            "https://fonts.googleapis.com; "
        "font-src 'self' "
            "https://fonts.gstatic.com "
            "data:; "
        "img-src 'self' data: blob: "
            "https://ipapi.co "
            "https://*.tile.openstreetmap.org; "
        "connect-src 'self' "
            "https://graph.microsoft.com "
            "https://login.microsoftonline.com "
            "https://api.xero.com "
            "https://identity.xero.com "
            "https://login.xero.com "
            "https://api.monzo.com "
            "https://accounts.zoho.eu "
            "https://www.zohoapis.eu "
            "https://api.open-meteo.com "
            "https://ipapi.co "
            "https://app.eu.action1.com "
            "https://merlot-api.centrastage.net "
            "https://auth.datto.com "
            "https://api.groq.com "
            "https://api.anthropic.com "
            "blob:; "
        "worker-src 'self' blob: "
            "https://cdnjs.cloudflare.com "
            "https://cdn.jsdelivr.net; "
        "frame-src 'self' "
            "https://login.microsoftonline.com "
            "https://login.xero.com "
            "https://accounts.zoho.eu; "
        "frame-ancestors 'self'; "
        "object-src 'none'; "
        "base-uri 'self'; "
        "form-action 'self';"
    )
    h.send_header('Content-Security-Policy', csp)

# Allowed origins for CORS.  Add your production domain(s) here.
# Falls back to same-origin only if the request origin is not in this list.
_ALLOWED_ORIGINS = {
    'http://localhost:8765',
    'http://127.0.0.1:8765',
    'https://summarai.rytech-support.com',
    'https://rytech-support.com',
    'https://www.rytech-support.com',
}

def _cors_origin(handler):
    """Return the request origin if it is explicitly allowed, otherwise None."""
    origin = handler.headers.get('Origin', '')
    if origin in _ALLOWED_ORIGINS:
        return origin
    return None

def _send_cors(handler):
    """Send a strict Access-Control-Allow-Origin header (never wildcard on auth endpoints)."""
    origin = _cors_origin(handler)
    if origin:
        handler.send_header('Access-Control-Allow-Origin', origin)
        handler.send_header('Vary', 'Origin')

def json_response(handler, payload, status=200, extra_headers=None):
    body = json.dumps(payload, ensure_ascii=False).encode('utf-8')
    handler.send_response(status)
    handler.send_header('Content-Type', 'application/json')
    handler.send_header('Content-Length', str(len(body)))
    handler.send_header('Cache-Control', 'no-cache')
    _send_cors(handler)
    _sec_headers(handler)
    if extra_headers:
        for k, v in extra_headers.items():
            handler.send_header(k, v)
    handler.end_headers()
    handler.wfile.write(body)


# ══════════════════════════════════════════════════════════════════
#  AUTH -- JWT
# ══════════════════════════════════════════════════════════════════

def _get_jwt_secret():
    if os.path.exists(JWT_KEY_FILE):
        return open(JWT_KEY_FILE, 'rb').read()
    s = _secrets.token_bytes(32)
    open(JWT_KEY_FILE, 'wb').write(s)
    return s


def _b64u(data):
    if isinstance(data, str): data = data.encode()
    return base64.urlsafe_b64encode(data).rstrip(b'=').decode()


def _b64u_dec(s):
    s += '=' * (4 - len(s) % 4)
    return base64.urlsafe_b64decode(s)


def jwt_create(payload, expires_in=28800):
    hdr = _b64u(json.dumps({'alg': 'HS256', 'typ': 'JWT'}))
    p   = dict(payload)
    p['exp'] = int(time.time()) + expires_in
    p['iat'] = int(time.time())
    bdy = _b64u(json.dumps(p))
    sec = _get_jwt_secret()
    sig = _b64u(_hmac.new(sec, f'{hdr}.{bdy}'.encode(), hashlib.sha256).digest())
    return f'{hdr}.{bdy}.{sig}'


def jwt_verify(token):
    try:
        h, b, s = token.split('.')
        sec = _get_jwt_secret()
        expected = _b64u(_hmac.new(sec, f'{h}.{b}'.encode(), hashlib.sha256).digest())
        if not _hmac.compare_digest(s, expected):
            return None
        p = json.loads(_b64u_dec(b))
        if p.get('exp', 0) < time.time():
            return None
        return p
    except Exception:
        return None


# ══════════════════════════════════════════════════════════════════
#  AUTH -- PASSWORDS
# ══════════════════════════════════════════════════════════════════

def hash_password(pw):
    salt = _secrets.token_hex(16)
    dk   = hashlib.pbkdf2_hmac('sha256', pw.encode(), salt.encode(), 260000)
    return f'pbkdf2:{salt}:{dk.hex()}'

# ══════════════════════════════════════════════════════════════════
#  TOTP 2FA  (RFC 6238 - no external libs needed)
# ══════════════════════════════════════════════════════════════════

def totp_generate_secret():
    """Generate a random 20-byte base32 secret."""
    alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'
    return ''.join(_secrets.choice(alphabet) for _ in range(32))

def _base32_decode(s):
    s = s.upper().strip()
    pad = (8 - len(s) % 8) % 8
    s += '=' * pad
    import base64
    return base64.b32decode(s)

def totp_generate_code(secret, t=None):
    """Generate current TOTP code (30s window)."""
    if t is None:
        t = int(_time_mod.time()) // 30
    key = _base32_decode(secret)
    msg = struct.pack('>Q', t)
    h = _hmac.new(key, msg, hashlib.sha1).digest()
    offset = h[-1] & 0x0f
    code = struct.unpack('>I', h[offset:offset+4])[0] & 0x7fffffff
    return str(code % 1000000).zfill(6)

def totp_verify(secret, code, window=1):
    """Verify TOTP code allowing +/- window steps."""
    t = int(_time_mod.time()) // 30
    for delta in range(-window, window + 1):
        if _hmac.compare_digest(totp_generate_code(secret, t + delta), str(code).strip()):
            return True
    return False

def totp_provisioning_uri(secret, email, issuer='Rytech SummarAI'):
    """Generate otpauth:// URI for QR code."""
    import urllib.parse
    params = urllib.parse.urlencode({
        'secret': secret,
        'issuer': issuer,
        'algorithm': 'SHA1',
        'digits': 6,
        'period': 30,
    })
    return f'otpauth://totp/{urllib.parse.quote(issuer)}:{urllib.parse.quote(email)}?{params}'

def totp_generate_backup_codes():
    """Generate 8 one-time backup codes."""
    return [_secrets.token_hex(4).upper() for _ in range(8)]

def totp_check_backup(stored_json, code):
    """Check and consume a backup code. Returns updated list or None if invalid."""
    try:
        codes = json.loads(stored_json)
    except:
        return None
    code = code.upper().strip()
    if code in codes:
        codes.remove(code)
        return codes
    return None


# ══════════════════════════════════════════════════════════════════
#  TOKEN ENCRYPTION  (AES-256-GCM -- authenticated encryption)
# ══════════════════════════════════════════════════════════════════

_ENC_KEY_FILE = os.path.join(CONFIG_DIR, 'token_enc.key')

def _get_enc_key():
    # Priority 1: environment variable (key never touches filesystem)
    env_key = os.environ.get('RYTECH_MASTER_KEY', '').strip()
    if env_key:
        try:
            raw = base64.b64decode(env_key)
            if len(raw) == 32:
                return raw
        except Exception:
            pass
        # Also accept hex-encoded
        try:
            raw = bytes.fromhex(env_key)
            if len(raw) == 32:
                return raw
        except Exception:
            pass
        logging.warning('[ENC] RYTECH_MASTER_KEY set but not valid 32-byte base64/hex — falling back to file')
    # Priority 2: key file (legacy / fallback)
    if os.path.exists(_ENC_KEY_FILE):
        raw = open(_ENC_KEY_FILE, 'rb').read()
        if len(raw) == 32:
            return raw
    # Generate new key and save to file (first-run only)
    k = _secrets.token_bytes(32)
    os.makedirs(CONFIG_DIR, exist_ok=True)
    open(_ENC_KEY_FILE, 'wb').write(k)
    logging.warning('[ENC] Generated new encryption key at %s — set RYTECH_MASTER_KEY env var to eliminate file dependency', _ENC_KEY_FILE)
    return k

def encrypt_token(plaintext):
    """Encrypt a string with AES-256-GCM → base64url-encoded (nonce + ciphertext + tag)."""
    try:
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        key   = _get_enc_key()
        nonce = _secrets.token_bytes(12)          # 96-bit nonce, GCM standard
        ct_tag = AESGCM(key).encrypt(nonce, plaintext.encode('utf-8'), None)
        return base64.urlsafe_b64encode(nonce + ct_tag).rstrip(b'=').decode()
    except ImportError:
        # Fallback: HMAC-SHA256 envelope (no confidentiality, but integrity preserved)
        # Install 'cryptography' package for proper AES-GCM encryption
        key  = _get_enc_key()
        data = plaintext.encode('utf-8')
        nonce = _secrets.token_bytes(12)
        tag  = _hmac.new(key, nonce + data, hashlib.sha256).digest()
        payload = nonce + tag + data
        return base64.urlsafe_b64encode(payload).rstrip(b'=').decode()

def decrypt_token(ciphertext):
    """Decrypt an AES-256-GCM encrypted token. Returns None if invalid/tampered."""
    try:
        payload = base64.urlsafe_b64decode(ciphertext + '==')
        try:
            from cryptography.hazmat.primitives.ciphers.aead import AESGCM
            key   = _get_enc_key()
            nonce = payload[:12]
            ct_tag = payload[12:]
            plaintext = AESGCM(key).decrypt(nonce, ct_tag, None)
            return plaintext.decode('utf-8')
        except ImportError:
            key   = _get_enc_key()
            nonce = payload[:12]
            tag   = payload[12:44]
            data  = payload[44:]
            expected = _hmac.new(key, nonce + data, hashlib.sha256).digest()
            if not _hmac.compare_digest(tag, expected):
                return None
            return data.decode('utf-8')
    except Exception:
        return None




def check_password(pw, hashed):
    try:
        _, salt, dk_hex = hashed.split(':')
        dk = hashlib.pbkdf2_hmac('sha256', pw.encode(), salt.encode(), 260000)
        return _hmac.compare_digest(dk.hex(), dk_hex)
    except Exception:
        return False


# ══════════════════════════════════════════════════════════════════
#  OAUTH TOKEN PERSISTENCE  (encrypted at rest, per user/provider)
# ══════════════════════════════════════════════════════════════════

_ALLOWED_PROVIDERS = {'xero', 'zoho', 'monzo'}

def oauth_save(user_id, provider, token_dict):
    """Encrypt and persist an OAuth token dict for a user/provider."""
    if provider not in _ALLOWED_PROVIDERS:
        raise ValueError(f'Unknown provider: {provider}')
    encrypted = encrypt_token(json.dumps(token_dict))
    conn = get_db()
    conn.execute(
        '''INSERT INTO oauth_tokens (user_id, provider, token_enc, updated_at)
           VALUES (?,?,?,datetime('now'))
           ON CONFLICT(user_id, provider) DO UPDATE SET
               token_enc=excluded.token_enc,
               updated_at=excluded.updated_at''',
        (user_id, provider, encrypted)
    )
    conn.commit()
    conn.close()

def oauth_load(user_id, provider):
    """Load and decrypt a stored OAuth token dict, or None if absent."""
    if provider not in _ALLOWED_PROVIDERS:
        return None
    conn = get_db()
    c = conn.cursor()
    c.execute('SELECT token_enc FROM oauth_tokens WHERE user_id=? AND provider=?',
              (user_id, provider))
    row = c.fetchone()
    conn.close()
    if not row:
        return None
    return json.loads(decrypt_token(row['token_enc']) or 'null')

def oauth_delete(user_id, provider):
    """Remove stored OAuth tokens for a user/provider."""
    if provider not in _ALLOWED_PROVIDERS:
        return
    conn = get_db()
    conn.execute('DELETE FROM oauth_tokens WHERE user_id=? AND provider=?',
                 (user_id, provider))
    conn.commit()
    conn.close()


# ── OAuth credentials (hardcoded, matching frontend) ─────────────
_XERO_CLIENT_ID     = 'F313172A62AA4641A8EF5AC59F3AB2BC'
_XERO_CLIENT_SECRET = 'EU0w9yY1AZ03VQYDWxf0FlZJRzSc1sdSUOxN9BtFZxrdPVgh'
_ZOHO_CLIENT_ID     = '1000.A7MGE295RVYJSEW6SVWFQ6M8SDUWQM'
_ZOHO_CLIENT_SECRET = '265d50d621afa9333af877693f127d9002e570459d'

def _oauth_http_post(url, params):
    """Simple URL-encoded POST, returns parsed JSON or raises."""
    body = urllib.parse.urlencode(params).encode()
    req  = urllib.request.Request(url, data=body,
           headers={'Content-Type': 'application/x-www-form-urlencoded'})
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read())

def oauth_refresh_xero(user_id, tokens):
    """Server-side Xero token refresh. Returns updated token dict or None."""
    refresh_token = tokens.get('refresh_token')
    if not refresh_token:
        return None
    try:
        data = _oauth_http_post('https://identity.xero.com/connect/token', {
            'grant_type':    'refresh_token',
            'refresh_token': refresh_token,
            'client_id':     _XERO_CLIENT_ID,
            'client_secret': _XERO_CLIENT_SECRET,
        })
        updated = dict(tokens)
        updated['access_token']  = data['access_token']
        updated['refresh_token'] = data.get('refresh_token', refresh_token)
        updated['expires_at']    = int(time.time() * 1000) + int(data.get('expires_in', 1800)) * 1000
        oauth_save(user_id, 'xero', updated)
        return updated
    except Exception as e:
        logging.warning(f'Server-side Xero refresh failed: {e}')
        return None

def oauth_refresh_zoho(user_id, tokens):
    """Server-side Zoho token refresh. Returns updated token dict or None."""
    refresh_token = tokens.get('refresh_token')
    if not refresh_token:
        return None
    try:
        data = _oauth_http_post('https://accounts.zoho.eu/oauth/v2/token', {
            'grant_type':    'refresh_token',
            'refresh_token': refresh_token,
            'client_id':     _ZOHO_CLIENT_ID,
            'client_secret': _ZOHO_CLIENT_SECRET,
        })
        if 'error' in data:
            raise Exception(data['error'])
        updated = dict(tokens)
        updated['access_token']  = data['access_token']
        updated['refresh_token'] = data.get('refresh_token', refresh_token)
        updated['expires_at']    = int(time.time() * 1000) + int(data.get('expires_in', 3600)) * 1000
        oauth_save(user_id, 'zoho', updated)
        return updated
    except Exception as e:
        logging.warning(f'Server-side Zoho refresh failed: {e}')
        return None

def oauth_refresh_monzo(user_id, tokens):
    """Server-side Monzo token refresh. Returns updated token dict or None."""
    refresh_token = tokens.get('refresh_token')
    client_id     = tokens.get('client_id')
    client_secret = tokens.get('client_secret')
    if not (refresh_token and client_id and client_secret):
        return None
    try:
        data = _oauth_http_post('https://api.monzo.com/oauth2/token', {
            'grant_type':    'refresh_token',
            'client_id':     client_id,
            'client_secret': client_secret,
            'refresh_token': refresh_token,
        })
        updated = dict(tokens)
        updated['access_token']  = data['access_token']
        updated['refresh_token'] = data.get('refresh_token', refresh_token)
        updated['expires_at']    = int(time.time() * 1000) + int(data.get('expires_in', 21600)) * 1000
        oauth_save(user_id, 'monzo', updated)
        return updated
    except Exception as e:
        logging.warning(f'Server-side Monzo refresh failed: {e}')
        return None

# Token is considered expired if expires_at (JS ms epoch) is within 5 min of now
def _token_expired(tokens):
    exp = tokens.get('expires_at')
    if not exp:
        return True
    return int(time.time() * 1000) > (int(exp) - 300_000)  # 5 min buffer


# ══════════════════════════════════════════════════════════════════
#  AUTH -- DATABASE
# ══════════════════════════════════════════════════════════════════

def get_db():
    conn = sqlite3.connect(DB_FILE, check_same_thread=False, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute('PRAGMA journal_mode=WAL')   # concurrent reads + writes
    conn.execute('PRAGMA busy_timeout=10000') # 10s retry before giving up
    conn.execute('PRAGMA synchronous=NORMAL') # safe + faster than FULL
    return conn


def init_db():
    conn = get_db()
    conn.executescript('''
        CREATE TABLE IF NOT EXISTS users (
            id                   INTEGER PRIMARY KEY AUTOINCREMENT,
            email                TEXT UNIQUE NOT NULL,
            name                 TEXT NOT NULL,
            password_hash        TEXT NOT NULL,
            role                 TEXT NOT NULL DEFAULT 'staff',
            active               INTEGER NOT NULL DEFAULT 1,
            created_at           TEXT NOT NULL DEFAULT (datetime('now')),
            last_login           TEXT,
            must_change_password INTEGER NOT NULL DEFAULT 0,
            totp_secret          TEXT,
            totp_enabled         INTEGER NOT NULL DEFAULT 0,
            totp_backup_codes    TEXT
        );
        -- Add columns if upgrading existing DB
        CREATE TABLE IF NOT EXISTS _users_migration_done (id INTEGER PRIMARY KEY);
        CREATE TABLE IF NOT EXISTS sessions (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id     INTEGER NOT NULL,
            token       TEXT UNIQUE NOT NULL,
            expires_at  TEXT NOT NULL,
            ip_address  TEXT,
            user_agent  TEXT,
            created_at  TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(user_id) REFERENCES users(id)
        );
        CREATE TABLE IF NOT EXISTS login_attempts (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            email        TEXT NOT NULL,
            ip_address   TEXT,
            success      INTEGER NOT NULL DEFAULT 0,
            attempted_at TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS audit_log (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id    INTEGER,
            action     TEXT NOT NULL,
            detail     TEXT,
            ip_address TEXT,
            created_at TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS permissions (
            user_id  INTEGER NOT NULL,
            section  TEXT NOT NULL,
            can_view INTEGER NOT NULL DEFAULT 1,
            PRIMARY KEY(user_id, section),
            FOREIGN KEY(user_id) REFERENCES users(id)
        );
        CREATE TABLE IF NOT EXISTS role_permissions (
            role     TEXT NOT NULL,
            section  TEXT NOT NULL,
            can_view INTEGER NOT NULL DEFAULT 1,
            PRIMARY KEY(role, section)
        );
        CREATE TABLE IF NOT EXISTS notes (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            owner_id     INTEGER NOT NULL,
            title        TEXT NOT NULL DEFAULT 'Untitled',
            content      TEXT NOT NULL DEFAULT '',
            color        TEXT NOT NULL DEFAULT '#1e2830',
            pinned       INTEGER NOT NULL DEFAULT 0,
            drawing_data TEXT NOT NULL DEFAULT '',
            created_at   TEXT NOT NULL DEFAULT (datetime('now')),
            updated_at   TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(owner_id) REFERENCES users(id)
        );
        CREATE TABLE IF NOT EXISTS notes_meta (
            key TEXT PRIMARY KEY,
            val TEXT NOT NULL DEFAULT ''
        );
        -- Migration: add drawing_data if missing
        BEGIN;
        INSERT OR IGNORE INTO notes_meta(key,val) VALUES('drawing_migrated','0');
        COMMIT;
        CREATE TABLE IF NOT EXISTS assigned_tasks (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            creator_id   INTEGER NOT NULL,
            assignee_id  INTEGER NOT NULL,
            title        TEXT NOT NULL,
            description  TEXT NOT NULL DEFAULT '',
            priority     TEXT NOT NULL DEFAULT 'medium',
            due_date     TEXT,
            remind_days  INTEGER,
            recur        TEXT,
            status       TEXT NOT NULL DEFAULT 'pending',
            created_at   TEXT NOT NULL DEFAULT (datetime('now')),
            updated_at   TEXT NOT NULL DEFAULT (datetime('now')),
            completed_at TEXT,
            archived     INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY(creator_id)  REFERENCES users(id),
            FOREIGN KEY(assignee_id) REFERENCES users(id)
        );
        -- Add columns if upgrading from older schema
        CREATE TABLE IF NOT EXISTS _migration_dummy (id INTEGER);

        CREATE TABLE IF NOT EXISTS task_notes (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            task_id    INTEGER NOT NULL,
            author_id  INTEGER NOT NULL,
            body       TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(task_id)   REFERENCES assigned_tasks(id) ON DELETE CASCADE,
            FOREIGN KEY(author_id) REFERENCES users(id)
        );
        CREATE TABLE IF NOT EXISTS subtasks (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            task_id    INTEGER NOT NULL,
            title      TEXT NOT NULL,
            done       INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(task_id) REFERENCES assigned_tasks(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS workflow_config (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            workflow_id  TEXT NOT NULL UNIQUE,
            enabled      INTEGER NOT NULL DEFAULT 0,
            last_run     TEXT,
            next_run     TEXT,
            run_hour     INTEGER NOT NULL DEFAULT 8,
            updated_at   TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS workflow_log (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            workflow_id  TEXT NOT NULL,
            recipient    TEXT NOT NULL,
            subject      TEXT NOT NULL,
            status       TEXT NOT NULL DEFAULT 'sent',
            error        TEXT,
            sent_at      TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS smtp_config (
            id           INTEGER PRIMARY KEY CHECK (id=1),
            host         TEXT NOT NULL DEFAULT 'smtp.office365.com',
            port         INTEGER NOT NULL DEFAULT 587,
            username     TEXT NOT NULL DEFAULT '',
            password_enc TEXT NOT NULL DEFAULT '',
            from_addr    TEXT NOT NULL DEFAULT '',
            from_name    TEXT NOT NULL DEFAULT 'Rytech Support',
            updated_at   TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS oauth_tokens (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id      INTEGER NOT NULL,
            provider     TEXT NOT NULL,
            token_enc    TEXT NOT NULL,
            updated_at   TEXT NOT NULL DEFAULT (datetime('now')),
            UNIQUE(user_id, provider),
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS groq_config (
            id         INTEGER PRIMARY KEY CHECK (id=1),
            key_enc    TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS app_credentials (
            key        TEXT PRIMARY KEY,
            value_enc  TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS notifications (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id     INTEGER NOT NULL,
            type        TEXT NOT NULL,
            title       TEXT NOT NULL,
            body        TEXT NOT NULL DEFAULT '',
            link        TEXT NOT NULL DEFAULT '',
            read_at     TEXT,
            created_at  TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS ticket_events (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            ticket_id   TEXT NOT NULL,
            event_type  TEXT NOT NULL,
            detail      TEXT NOT NULL DEFAULT '',
            actor       TEXT NOT NULL DEFAULT '',
            created_at  TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS client_activity (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            client_id   TEXT NOT NULL,
            event_type  TEXT NOT NULL,
            title       TEXT NOT NULL,
            detail      TEXT NOT NULL DEFAULT '',
            actor       TEXT NOT NULL DEFAULT '',
            created_at  TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE TABLE IF NOT EXISTS user_widget_prefs (
            user_id     INTEGER PRIMARY KEY,
            prefs_json  TEXT NOT NULL DEFAULT '{}',
            updated_at  TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        );
    ''')
    conn.commit()
    # Migrate existing DB - add new columns if they don't exist
    try:
        conn.execute("ALTER TABLE users ADD COLUMN must_change_password INTEGER NOT NULL DEFAULT 0")
    except: pass
    try:
        conn.execute("ALTER TABLE users ADD COLUMN totp_secret TEXT")
    except: pass
    try:
        conn.execute("ALTER TABLE users ADD COLUMN totp_enabled INTEGER NOT NULL DEFAULT 0")
    except: pass
    try:
        conn.execute("ALTER TABLE users ADD COLUMN totp_backup_codes TEXT")
    except: pass
    try:
        conn.execute("ALTER TABLE users ADD COLUMN avatar TEXT DEFAULT NULL")
        conn.commit()
    except: pass
    try:
        conn.execute("ALTER TABLE assigned_tasks ADD COLUMN archived INTEGER NOT NULL DEFAULT 0")
        conn.commit()
    except: pass
    try:
        conn.execute("ALTER TABLE assigned_tasks ADD COLUMN remind_days INTEGER")
        conn.commit()
    except: pass
    try:
        conn.execute("ALTER TABLE assigned_tasks ADD COLUMN recur TEXT")
        conn.commit()
    except: pass
    try:
        conn.execute("ALTER TABLE workflow_config ADD COLUMN lead_days INTEGER NOT NULL DEFAULT 30")
        conn.commit()
    except: pass
    try:
        conn.execute("ALTER TABLE sessions ADD COLUMN user_agent TEXT")
    except: pass
    # oauth_tokens migration
    # Detect actual column name and normalise to token_enc
    try:
        c_mg = conn.cursor()
        c_mg.execute("PRAGMA table_info(oauth_tokens)")
        cols = [r[1] for r in c_mg.fetchall()]
        if 'token_enc' not in cols and 'token' not in cols:
            # Table exists but has neither column — drop and recreate
            conn.execute("DROP TABLE oauth_tokens")
            conn.execute('''CREATE TABLE oauth_tokens (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id    INTEGER NOT NULL,
                provider   TEXT NOT NULL,
                token_enc  TEXT NOT NULL,
                updated_at TEXT NOT NULL DEFAULT (datetime('now')),
                UNIQUE(user_id, provider),
                FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
            )''')
            conn.commit()
        elif 'token_enc' not in cols and 'token' in cols:
            # Old schema: rename token -> token_enc
            conn.execute("ALTER TABLE oauth_tokens RENAME COLUMN token TO token_enc")
            conn.commit()
        elif 'token_enc' not in cols:
            conn.execute("ALTER TABLE oauth_tokens ADD COLUMN token_enc TEXT NOT NULL DEFAULT ''")
            conn.commit()
    except Exception as _mg_e:
        import sys
        print(f'[DB] oauth_tokens migration warning: {_mg_e}', file=sys.stderr)
    # notes drawing_data migration
    try:
        conn.execute("ALTER TABLE notes ADD COLUMN drawing_data TEXT NOT NULL DEFAULT ''")
    except: pass
    conn.commit()
    # Create default superadmin if no users exist
    c = conn.cursor()
    c.execute('SELECT COUNT(*) FROM users')
    if c.fetchone()[0] == 0:
        # Use RYTECH_ADMIN_PASSWORD env var, or generate a random password
        import os as _os
        default_pw = _os.environ.get('RYTECH_ADMIN_PASSWORD', '')
        if not default_pw:
            default_pw = _secrets.token_urlsafe(16)
            print(f'  [AUTH] No RYTECH_ADMIN_PASSWORD set -- generated: {default_pw}')
            print(f'  [AUTH] *** SAVE THIS PASSWORD -- it will not be shown again ***')
        c.execute(
            'INSERT INTO users (email, name, password_hash, role) VALUES (?,?,?,?)',
            ('admin@rytech-support.com', 'Administrator',
             hash_password(default_pw), 'superadmin')
        )
        conn.commit()
        print('  [AUTH] Default superadmin created: admin@rytech-support.com')
        print('  [AUTH] *** PLEASE CHANGE THIS PASSWORD AFTER FIRST LOGIN ***')
    # Pre-seed Groq API key if not already stored
    _groq_key = 'gsk_REPLACE_WITH_NEW_KEY_AFTER_ROTATING'
    try:
        _gc = conn.cursor()
        _gc.execute('SELECT key_enc FROM groq_config WHERE id=1')
        _grow = _gc.fetchone()
        if not _grow or not _grow['key_enc']:
            _enc = encrypt_token(_groq_key)
            conn.execute('''INSERT INTO groq_config (id, key_enc) VALUES (1, ?)
                            ON CONFLICT(id) DO UPDATE SET key_enc=excluded.key_enc,
                            updated_at=datetime('now')''', (_enc,))
            conn.commit()
            print('  [GROQ] API key seeded into database')
    except Exception as _ge:
        print(f'  [GROQ] Key seed warning: {_ge}', file=sys.stderr)
    # Pre-seed task_reminder workflow as enabled if not already configured
    try:
        _wc = conn.cursor()
        _wc.execute("SELECT workflow_id, enabled FROM workflow_config WHERE workflow_id='task_reminder'")
        _wrow = _wc.fetchone()
        if not _wrow:
            conn.execute("""INSERT INTO workflow_config (workflow_id, enabled, run_hour, lead_days, updated_at)
                            VALUES ('task_reminder', 1, 8, 1, datetime('now'))""")
            conn.commit()
            print('  [WF] task_reminder workflow auto-enabled (run daily at 08:00)')
        elif not _wrow['enabled']:
            print('  [WF] task_reminder exists but is disabled — enable it via Admin › Email Workflows')
    except Exception as _we:
        print(f'  [WF] task_reminder seed warning: {_we}', file=sys.stderr)
    conn.close()

def is_rate_limited(email, ip):
    conn = get_db()
    c    = conn.cursor()
    c.execute("""
        SELECT COUNT(*) FROM login_attempts
        WHERE (email=? OR ip_address=?) AND success=0
        AND attempted_at > datetime('now', '-15 minutes')
    """, (email, ip))
    n = c.fetchone()[0]
    conn.close()
    return n >= 5


def record_attempt(email, ip, success):
    conn = get_db()
    conn.execute(
        'INSERT INTO login_attempts (email, ip_address, success) VALUES (?,?,?)',
        (email, ip, 1 if success else 0)
    )
    conn.commit()
    conn.close()


def db_audit(user_id, action, detail=None, ip=None):
    try:
        conn = get_db()
        conn.execute(
            'INSERT INTO audit_log (user_id, action, detail, ip_address) VALUES (?,?,?,?)',
            (user_id, action, detail, ip)
        )
        conn.commit()
        conn.close()
    except Exception as e:
        import sys
        print(f'[AUDIT] db_audit failed: {e}', file=sys.stderr)


def auth_login(email, password, ip, remember=False, user_agent='', totp_code=None):
    """
    Returns (token, None) on full success.
    Returns (None, '2fa_required') if password OK but 2FA needed.
    Returns (None, 'error message') on failure.
    """
    email = email.lower().strip()
    if is_rate_limited(email, ip):
        return None, 'Too many failed attempts. Try again in 15 minutes.'
    conn = get_db()
    c    = conn.cursor()
    c.execute('SELECT * FROM users WHERE email=? AND active=1', (email,))
    user = c.fetchone()
    if not user or not check_password(password, user['password_hash']):
        record_attempt(email, ip, False)
        conn.close()
        return None, 'Invalid email or password.'
    # ── 2FA check ────────────────────────────────────────────────
    if user['totp_enabled']:
        if totp_code is None:
            conn.close()
            return None, '2fa_required'
        code = str(totp_code).strip()
        # Check TOTP
        if not totp_verify(user['totp_secret'], code):
            # Try backup code
            if user['totp_backup_codes']:
                remaining = totp_check_backup(user['totp_backup_codes'], code)
                if remaining is not None:
                    conn.execute('UPDATE users SET totp_backup_codes=? WHERE id=?',
                                 (json.dumps(remaining), user['id']))
                    conn.commit()
                else:
                    record_attempt(email, ip, False)
                    conn.close()
                    return None, 'Invalid 2FA code.'
            else:
                record_attempt(email, ip, False)
                conn.close()
                return None, 'Invalid 2FA code.'
    # Session token: short-lived, lives in cookie
    session_expires = 90 * 24 * 3600  # Always 90 days -- cookie controls actual browser persistence
    session_tok = jwt_create({
        'user_id': user['id'],
        'email':   user['email'],
        'name':    user['name'],
        'role':    user['role'],
        'type':    'session',
    }, session_expires)
    exp = (datetime.utcnow() + timedelta(seconds=session_expires)).strftime('%Y-%m-%d %H:%M:%S')
    conn.execute(
        'INSERT INTO sessions (user_id, token, expires_at, ip_address, user_agent) VALUES (?,?,?,?,?)',
        (user['id'], session_tok, exp, ip, user_agent[:200] if user_agent else '')
    )
    conn.execute("UPDATE users SET last_login=datetime('now') WHERE id=?", (user['id'],))
    conn.commit()
    record_attempt(email, ip, True)
    db_audit(user['id'], 'login', f'from {ip}', ip)
    conn.close()
    import sys
    print(f"[AUTH] auth_login: SUCCESS for {email} (user_id={user['id']})", file=sys.stderr)
    return session_tok, None

def auth_login_token(email, ip, user_agent=''):
    """Create a fresh 30-day session for a verified user (no password needed -- caller already verified)."""
    conn = get_db()
    c    = conn.cursor()
    c.execute('SELECT * FROM users WHERE email=? AND active=1', (email,))
    user = c.fetchone()
    conn.close()
    if not user:
        return None, 'User not found'
    expires_in = 90 * 24 * 3600
    jwt_tok = jwt_create({
        'user_id': user['id'],
        'email':   user['email'],
        'name':    user['name'],
        'role':    user['role'],
    }, expires_in)
    token = jwt_tok
    exp   = (datetime.utcnow() + timedelta(seconds=expires_in)).strftime('%Y-%m-%d %H:%M:%S')
    conn2 = get_db()
    conn2.execute(
        'INSERT INTO sessions (user_id, token, expires_at, ip_address, user_agent) VALUES (?,?,?,?,?)',
        (user['id'], token, exp, ip, user_agent[:200] if user_agent else '')
    )
    conn2.commit()
    conn2.close()
    return token, None

def auth_logout(token):
    if not token:
        return
    conn = get_db()
    conn.execute('DELETE FROM sessions WHERE token=?', (token,))
    conn.commit()
    conn.close()


def verify_session(token):
    import sys
    if not token:
        print("[AUTH] verify_session: no token", file=sys.stderr)
        return None
    jwt_ok = jwt_verify(token)
    if not jwt_ok:
        print(f"[AUTH] verify_session: JWT verify FAILED", file=sys.stderr)
        return None
    print(f"[AUTH] verify_session: JWT OK for user_id={jwt_ok.get('user_id')}", file=sys.stderr)
    conn = get_db()
    c    = conn.cursor()
    c.execute("""
        SELECT u.id, u.email, u.name, u.role, u.active
        FROM sessions s
        JOIN users u ON s.user_id = u.id
        WHERE s.token=? AND s.expires_at > datetime('now')
    """, (token,))
    row = c.fetchone()
    conn.close()
    if not row:
        print(f"[AUTH] verify_session: no active session found in DB", file=sys.stderr)
        # Check if token exists but expired
        conn2 = get_db()
        c2 = conn2.cursor()
        c2.execute("SELECT expires_at FROM sessions WHERE token=?", (token,))
        exp_row = c2.fetchone()
        conn2.close()
        if exp_row:
            print(f"[AUTH] Session exists but expired at: {exp_row[0]}", file=sys.stderr)
        else:
            print(f"[AUTH] Token not found in sessions table at all", file=sys.stderr)
        return None
    if not row['active']:
        print(f"[AUTH] verify_session: user {row['email']} is inactive", file=sys.stderr)
        return None
    print(f"[AUTH] verify_session: SUCCESS for user_id={row['id']}", file=sys.stderr)
    return dict(row)


def get_permissions(user_id, role):
    # Superadmin/admin always get everything
    if role in ('superadmin', 'admin'):
        return list(ALL_SECTIONS)
    # Start from role_permissions table (admin-configured)
    conn = get_db()
    c    = conn.cursor()
    c.execute('SELECT section, can_view FROM role_permissions WHERE role=?', (role,))
    role_rows = c.fetchall()
    if role_rows:
        base = set(row['section'] for row in role_rows if row['can_view'])
    else:
        # Fall back to ROLE_DEFAULTS if nothing configured yet
        base = set(ROLE_DEFAULTS.get(role, {'dashboard'}))
    # Apply per-user overrides
    c.execute('SELECT section, can_view FROM permissions WHERE user_id=?', (user_id,))
    for row in c.fetchall():
        if row['can_view']:
            base.add(row['section'])
        else:
            base.discard(row['section'])
    conn.close()
    return list(base)


def auth_get_token(handler):
    """Extract session token from ry_session cookie (preferred) or Authorization header fallback."""
    import sys
    # Always try cookie first - proxy routes send their own Authorization headers
    # for downstream services (Xero, Zoho etc), not for session auth
    cookie = handler.headers.get('Cookie', '')
    for part in cookie.split(';'):
        part = part.strip()
        if part.startswith('ry_session='):
            tok = urllib.parse.unquote(part[11:])
            return tok
    # Fallback: Authorization header (used by non-browser clients / API access)
    auth = handler.headers.get('Authorization', '')
    if auth.startswith('Bearer '):
        # Only trust if it looks like a JWT (our tokens), not a short service key
        candidate = auth[7:]
        if candidate.count('.') == 2:   # JWT has 3 parts separated by dots
            return candidate
    return None


def require_auth(handler):
    """Returns user dict or sends 401 and returns None."""
    token = auth_get_token(handler)
    user  = verify_session(token)
    if not user:
        json_response(handler, {'ok': False, 'error': 'Unauthorized'}, status=401)
        return None
    return user


def get_client_ip(handler):
    """Get real client IP, respecting X-Forwarded-For from Nginx."""
    forwarded = handler.headers.get('X-Forwarded-For', '')
    if forwarded:
        return forwarded.split(',')[0].strip()
    return handler.client_address[0]


# ══════════════════════════════════════════════════════════════════
#  LOGIN PAGE HTML
# ══════════════════════════════════════════════════════════════════

LOGIN_PAGE = b"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Rytech SummarAI &mdash; Sign In</title>
<style>
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  :root {
    --bg:      #0a0d10;
    --surface: #111518;
    --border:  #1e2730;
    --accent:  #2196f3;
    --accent2: #1565c0;
    --text:    #e8eef2;
    --muted:   #5a7080;
    --error:   #ef5350;
    --success: #4caf50;
  }
  body {
    background: var(--bg);
    color: var(--text);
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    min-height: 100vh;
    display: flex;
    align-items: center;
    justify-content: center;
    padding: 20px;
  }
  .card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 16px;
    padding: 48px 40px 40px;
    width: 100%;
    max-width: 420px;
    box-shadow: 0 24px 80px rgba(0,0,0,0.5);
  }
  .logo {
    text-align: center;
    margin-bottom: 32px;
  }
  .logo-icon {
    width: 56px;
    height: 56px;
    background: linear-gradient(135deg, #1565c0, #2196f3);
    border-radius: 14px;
    display: inline-flex;
    align-items: center;
    justify-content: center;
    font-size: 26px;
    margin-bottom: 14px;
    box-shadow: 0 8px 24px rgba(33,150,243,0.3);
  }
  .logo h1 {
    font-size: 1.4rem;
    font-weight: 700;
    letter-spacing: -0.3px;
    color: var(--text);
  }
  .logo p {
    font-size: 0.8rem;
    color: var(--muted);
    margin-top: 4px;
    letter-spacing: 0.5px;
    text-transform: uppercase;
  }
  .field { margin-bottom: 18px; }
  label {
    display: block;
    font-size: 0.8rem;
    font-weight: 500;
    color: var(--muted);
    margin-bottom: 7px;
    letter-spacing: 0.3px;
  }
  input[type=email], input[type=password] {
    width: 100%;
    background: rgba(255,255,255,0.04);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 11px 14px;
    color: var(--text);
    font-size: 0.95rem;
    outline: none;
    transition: border-color 0.2s;
  }
  input[type=email]:focus, input[type=password]:focus {
    border-color: var(--accent);
    background: rgba(33,150,243,0.05);
  }
  .remember {
    display: flex;
    align-items: center;
    gap: 8px;
    margin-bottom: 24px;
    font-size: 0.85rem;
    color: var(--muted);
    cursor: pointer;
    user-select: none;
  }
  .remember input { width: 16px; height: 16px; accent-color: var(--accent); cursor: pointer; }
  .btn {
    width: 100%;
    background: linear-gradient(135deg, var(--accent2), var(--accent));
    border: none;
    border-radius: 8px;
    padding: 12px;
    color: #fff;
    font-size: 0.95rem;
    font-weight: 600;
    cursor: pointer;
    transition: opacity 0.2s, transform 0.1s;
    letter-spacing: 0.2px;
  }
  .btn:hover { opacity: 0.9; }
  .btn:active { transform: scale(0.99); }
  .btn:disabled { opacity: 0.5; cursor: not-allowed; }
  .alert {
    padding: 10px 14px;
    border-radius: 8px;
    font-size: 0.85rem;
    margin-bottom: 18px;
    display: none;
  }
  .alert.error   { background: rgba(239,83,80,0.12); border: 1px solid rgba(239,83,80,0.3); color: #ef9a9a; }
  .alert.success { background: rgba(76,175,80,0.12); border: 1px solid rgba(76,175,80,0.3); color: #a5d6a7; }
  .footer {
    text-align: center;
    font-size: 0.75rem;
    color: var(--muted);
    margin-top: 28px;
  }
  .spinner {
    display: inline-block;
    width: 16px; height: 16px;
    border: 2px solid rgba(255,255,255,0.3);
    border-top-color: #fff;
    border-radius: 50%;
    animation: spin 0.7s linear infinite;
    vertical-align: middle;
    margin-right: 6px;
  }
  @keyframes spin { to { transform: rotate(360deg); } }
</style>
</head>
<body>
<div id="loginForm">
<div class="card">
  <div class="logo">
    <img src="data:image/jpeg;base64,/9j/4AAQSkZJRgABAQAAAQABAAD/4gHYSUNDX1BST0ZJTEUAAQEAAAHIAAAAAAQwAABtbnRyUkdCIFhZWiAH4AABAAEAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAACRyWFlaAAABFAAAABRnWFlaAAABKAAAABRiWFlaAAABPAAAABR3dHB0AAABUAAAABRyVFJDAAABZAAAAChnVFJDAAABZAAAAChiVFJDAAABZAAAAChjcHJ0AAABjAAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAAgAAAAcAHMAUgBHAEJYWVogAAAAAAAAb6IAADj1AAADkFhZWiAAAAAAAABimQAAt4UAABjaWFlaIAAAAAAAACSgAAAPhAAAts9YWVogAAAAAAAA9tYAAQAAAADTLXBhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABtbHVjAAAAAAAAAAEAAAAMZW5VUwAAACAAAAAcAEcAbwBvAGcAbABlACAASQBuAGMALgAgADIAMAAxADb/2wBDAAUDBAQEAwUEBAQFBQUGBwwIBwcHBw8LCwkMEQ8SEhEPERETFhwXExQaFRERGCEYGh0dHx8fExciJCIeJBweHx7/2wBDAQUFBQcGBw4ICA4eFBEUHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh7/wAARCADMAfQDASIAAhEBAxEB/8QAHQABAAIDAAMBAAAAAAAAAAAAAAcIBQYJAQMEAv/EAGEQAAEDAgMDAwsMDQcLAgcAAAEAAgMEBQYHEQgSIRcxQRMYIlFXYXGTldHSCRQyN1ZydYGRlLGzFSM0OEJSVXSCkqGy0xYzNViiwcIlNkVHU1RiZXN2hSdjJCZDRmSD4f/EABQBAQAAAAAAAAAAAAAAAAAAAAD/xAAUEQEAAAAAAAAAAAAAAAAAAAAA/9oADAMBAAIRAxEAPwCmSIiApQ2ZstrZmnmWMM3e4VdDSijlqXPpg3qhLNNAN4EDn7XQovVh/U/fb8HwTU/4EEz9ZLgfU/8AzbiPTwQ+gvPWS4H91uI/kh9BWpRBVXrJcEe67EX6sPop1kuB/ddiL9WH0VapEFVeskwR7rsRfqw+ivHWSYJ912Iv1YfRVq0QVV6yTBHuuxF+rD6KdZLgj3XYi/Vh9FWqRBVXrJcD+63EfyQ+gnWS4H91uI/kh9BWqRBU6r2I8JOjIpMZ3yJ+nAywxPHyAN+laZfdiTEkLC6y41tlYehtVSPgPytL1eREHLPMXIjNDApklvGGKieiZqfXtCfXEOg6SW8W/pAKM12XIB5woQzw2bMDZh01TX0FJFYMQv1c2upIw1kr/wD3Yxwdr2xo7vnmQc10W1Zo4AxJlxiqfD2JaIwzsJMMzdTFUM6Hxu04g/KOY6FaqgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiArD+p+j/18HwTU/wCBV4UwbJGPMNZdZr/yhxTUVEFD6wmgD4YTIQ927pqBx04FB04RQN12uS/5auXk2XzJ122S/wCWbl5Nl8yCeUUDddrkv+Wrj5Nl8y8ddtkv+WLl5Nl8yCekUDDa1yX/AC1cR/42XzLz12mS35buPk2bzIJ4RQP12mS35buHkybzJ12mS35cuHkybzIJ4RQP12uS/wCWrj5Nl8y/J2tsl/yxcj/42XzIJ6RQvY9qHJe6y9SGKjRu1AHryjliB/S3dP2qVsO3+y4itzbjYrrRXOkdwE1LM2Rmva1aeB7yDJIiII9z4ytsmamCp7Lco44q6Npfbq3TsqaXTgeHO06aOHSO+Bpy8xXYbphjEdfh+9UxprhQTOhnjPHRw6QekHnB6QQuwqpb6orgCGCW0ZiUFK1jpnesLk9g9k7QmJ7u/oHN17zQgpyiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiIC2rLPMDFOXeIYr1he5y0krXNM0OusVQ0H2EjeZwPyjoIK1VEHV7IvMe3Zo5e0eJ6GMU8riYaym3t4087QN5mva4gg9ohb0qKepxX+pp8eYgw2ZCaWsoBVhhPASRPDdQO2WyH5Ar1oCjfacsDMR5E4tt7ow97Le+qj4akPh+2DTv8AYftUkL5rtSR19sqqGZodHUQvieD0hwII/ag44IvdWw+t6yaDn6nI5nyHRelAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREFkfU87dV1OddZXxB3rektMomcObV7mBoPxg/Iug6q96n5l7XYdwPcMZXNkkMt/cwUsLm6aU8eu68++c46d4A9KtCgLw7gF5WnZ2YhfhXKbE9/imME9JbZnQSDnbKWlsZHf3i1BzuvWQ+cEl3rJWZf3pzHzvc0tjBBBce0V8fILnH3Pb34kedYd2auZpOpzAxP5Um9JeeVfM3ugYn8qTekgzHIJnH3Pb34oedeOQXOLue3zxI86xPKxmd3QMT+U5fSTlYzP7oGJ/KcvpIMtyC5xdz2+eJHnTkFzj7nt78SPOsTysZn90DE/lOX0k5Wcz+6DifynL6SDL8gmcfc9vfih505BM4+57e/FDzrE8rOZ/dBxP5Tl9JOVnM/ug4n8py+kgy3IJnH3Pb34oedOQTOPue3vxQ86xPKzmf3QcT+U5fSTlZzP7oOJ/KcvpIMtyCZx9z29+KHnXjkFzj7nt78SPOsVys5n90HE/lOX0k5Ws0O6DifynL6SDK8gucXc9vniR505Bc4+57e/EjzrF8reaHdBxP5Tl9JOVvNDug4n8py+kgynILnF3Pb54kedOQXOLue3zxI86xXK1mh3QcT+U5fSTlazQ7oOJ/KcvpIMryC5xdz2+eJHnTkFzi7nt88SPOsVytZod0HE/lOX0k5Ws0O6DifynL6SDK8gucXc9vniR505Bc4u57fPEjzrFcrWaHdBxP5Tl9JOVvNDug4n8py+kgyvILnF3Pb54kedOQXOLue3zxI86xfK3mh3QcT+U5fSTlbzQ7oOJ/KcvpIMpyC5xdz2+eJHnTkFzi7nt88SPOsXyt5od0HE/lOX0l45Ws0O6DifynL6SDK8gmcfc9vfih5155BM4+57e/FDzrE8rWaHdBxP5Tl9JOVrNDug4n8py+kgy3IJnH3Pb34oedOQPOPue3vxQ86xPK1mh3QcT+U5fSTlazP7oOJ/KcvpIMtyB5x9z29+KHnTkEzj7nt78UPOsRys5n90HE/lOX0k5V8ztdeUDE/lOb0kGX5BM4+57e/FDzpyB5x9z29+KHnWIGbOZ4/wBYOJ/KcvpLzytZn90HE/lOX0kGW5A84+57e/FDzpyB5x9z29+KHnWJ5Wcz+6DifynL6ScrWaHdBxP5Tl9JBluQPOPue3vxQ86cgecfc9vfih51ieVrNDug4n8py+knK1mh3QcT+U5fSQZfkDzj7nt68WPOnIHnH3Pb14sedYnlbzQ7oOJ/KcvpLwc2s0Dz5g4n8py+kg+bFOWuYGFoTPiDBt8t0A55pqN/Uh+mBu/tWpqXcG7R2bWG5xv4nmvVGeEtJdWioZIOkau7IfEQt2xHhfBmeuD6/GWXFrhsGNrZF1e8YeiI6lVMHPLANBx4cwA1PAjUgkK2IvJBBIIII5wV4QEREBERAREQFkLTZLzdpBFarRX17zzNpqZ8p+RoKtfsl7M9DerTS46zDpXTUtQGy221u1aHs5xLL0lp4aN6RxPAgK59uttvt1O2nt9FTUkLRutjgibG0DtAAAIOVsOTea8sbZI8u8TFrhqD9jpB/cv2Mlc2zzZdYl8nyeZdWdB2gmg7QQcqBknm4f8AV1iT5g/zLzyI5u9zrEnzF/mXVbQdoJoO0EHKnkRzd7nWJPmL/MnIjm73OsSfMX+ZdVtB2gmg7QQcqDklm4P9XWJPmL/MvHIpm33OsS/MH+ZdWNB2gmg7QQctbNkBnFdaptPBgG7wEn2dVGIGDwueQFYLIjZBlo7pBfMzaimmbA8PitNM/fa9wOv21/MR/wALefpPQrkaDtBEH4gijghZFExscbGhrWtGgaBzADoC/aIgKq3qiGODa8C2zBFJMG1F5n9cVQB4iniOoH6T9P1CrK4rv1swxh2uv15qW01BQwumnkd0NA6B0k8wHSSAuWGduYFfmXmNcsU1pkZFM/qdHA469Qp2+wZ8nE98koNKREQEREBERAREQERbrlplZjnMdlc/B1kNybQ7gqD64jiDS7XdHZuGvMeZBpSKUMW5A5sYUw1WYiv2FjSW2iaH1EvryB5Y0kDXda8k8SOYKL0BERAREQEREBERAREQEREBERAREQFcbCuxfb7xhm13abH1VE+to4ah0bLa0hpewOIBMnEDVU6HOuu+Wvtd4b+CaX6liDmptI5XQZSY+gwzT3iS7RzUEdX1aSAREFz3t3dA4/ic+vSoyVkvVEhpnlQHt2KD66ZVtQEREBERAREQFuuR+Mq7AeaNjxFRSljYqlsdUzolged2RpHvSfAQD0LSl7aT7qi9+PpQSltZ4Vo8I56X2jt0QhoaxzK+CNvsWiYbxA729vaDtKKFP23d7dFGe3YaM/seoBQEREBERAW45KYW/lpmvhvDJbvRVtcwTj/2m9nJ/Ya5acp12E4I5toy0PeNTDSVcjO8eouH0EoOj9NFHBTxwwsbHHG0NY1o0DQBoAF7ERARF6ZqumhOk08cZPQ5wCD3Ivl+yND/AL3B4wedPsjQf75B4wedB9SL5fsjQf75B4wLwblbxz1tOP8A9g86D60Xqp6iCoYXwTRytB01Y4Ea/EvagIiFAWMxNf7PhqzVF4vtxp7fQ07S6WaZ+60AfSe8OJVdc29r3DeGK+5WPDlhr7rdqOV9O59U008DJGktOoPZuAI5tG69tU5zUzSxrmXcm1mKru+ojjJMFJENyng1/FZza986nvoJA2ps/a/NS5/YazdWosJ0km9DE7VslW8a/bJB2uPYt6Oc8eaCkRARWA2MMJZb48xPdsL43tTquvkgFTbn+uHxghnCRnYkcdCHeAFWWxnsp5X1WErpTYfsb6G7vpn+sqg1krhHNodzUF2hGugPeQc6UXtrKeakq5qWpjdFNC90cjHDi1wOhB+NepAREQEV0Nk7Z1wZifKuHFOOLRNW1dzmdJStM74mxwN7FpAaRqXEOOp6NF42ssqMncs8q56+14cfFe66ZlNbnevJXbjtd57yC4ggNB+MhBTBXW9TVH+SMZfnFL+7Ioc2M8usLZk5hXO1YspJqqkpra6ojjjmdH2fVGN1Jbx5nFXtyqyqwZllFXx4RoJqVte9jqjqlQ+XeLQQ3TePDnKDAbXX3uuMPzNv1rFy+XX/ABrhm04wwxW4bvsDp7dXMEc8bXlhcAQeBHEcQFEfWn5L/kGu8oy+dBzcRWi21cncC5aYfw7XYRoKmjmrKqWGcSVLpWua1gI9lzHVVdQEU/ZC7MOKcyLbDf7rWDD1ilOsMkkJfPUt6XMZqNG9pxPgBVkbVseZSUkLG1X2er5AOyfLXBup8DGjRBzwRdIxsn5Lj/QNcf8AyMvnQ7J+S/5BrvKMvnQc3EXQ287HWU9ZA9tE+/W6UjsHxVoeGnvh7Tr8qrDtAbOOKcrKQ3uCqbfcP7+66rhiLJKfXm6qzU6A828CRr2tQghBERARSbklknjTNere6y07KS1Qu3Z7lVaiFh/Fbpxe7vDm6SFazCWxhl/Q0TP5R3m9Xes07N0MjaaLXvNAc7+0goMi6QxbJuTDGhpslweR0uuMmv7Cv0dk/Jc/6Crh/wCRl86Dm4i6RDZOyY11+wdf5Rl86r5trZP4GyzsmHKzCNBUUktbUzRT9UqXShzWtaR7LmPEoKwjnXXfLX2vMOfBVL9SxciBzrrvlt7XmHPgql+pago36omP/XC3H/kMP106rWup2Z+R+XmZF/hvmKrXUVNdFTimbJFVvi+1hznAENOnO4/KtVbsoZLj/QFafDcZfOg5toukM+ybkxI3RtkuEXfZcZNf26rAX/YzyyrKZ4tVyxBa5z7F/rhkzAe+1zQT+sEHP1FP+b2yrj7BFDNdbTJFie2Q8ZHUkZZURt/GMRJJHvS5QCQWkgggjgQUHhERAXtpfumL34+lepeyl+6Y/fD6UE87dnty0PwBRfQ9QEp927Pbkof+36L6HqAkBERAREQFPWwZ98TbvzCr+rKgVT1sG/fE278wq/qyg6PIiIPDvYrkNjy/3fEOL7pdrvX1FXVVFVI575JCdOyOgHaAHADoC68v9iVxzvQ0vFaO1USfvFB83VJPx3fKnVJPx3fKvyiD9b7/AMd3ypvv/Gd8q/KIJz2Os135d5kRW66Vr2YdvTm09WHHVkMhOkc3e0J0J7RPaC6SMcHsDmkEEaghcaBwXRjYnzVOPMuxYbvViW/2FrYJd49nPT80cnf0A3Se2ATzoLAIeIREFG/VAcrPsZe4My7RCRS3Bzae6Ma3gycDsJfA8cD32j8ZVLXX7HOG7bi/CVzw1d4hLRXGndDKNNSNeZw74IBHfAXKXM3B1zwDjm6YUuwBqKCYsEjQQ2ZnOyRuvQ5uh+NBraIiDaMqMXVGBMxbJiuna6T7H1TZJIwdDJGeD2/G0uHxrrNaq6lulrprhRyiamqoWzRPHM5jgCD8hXHFdFdhLHb8V5PMslZLv12HpfWZJPF0B1dEfiGrf0EFYNt3AjcHZ0VVwpIty339nr+EAcGyE6StH6XZfphQSuje3NgZmK8mKm7U9N1S44fk9exOaOy6jppM3wbujj7wLnIgLZsrcJVuOcwbLhWgjc6SvqmxvcB/NxDjI895rQ4/EtZVyfU6sAEvu+Y1dFwGtvt2o8BleP7Lf1kFw7LbqSz2ajtdDC2Gko4GQQxtHBrGNDWj5AFzz26MfPxZm/LYaWp6pbMOtNJG1p7EznjM7w6hrf0FeLPHG9Pl7lfesUTOAlpoCylaf/qTv7GNv6xBPeBXKKsqJqurmqqmR0s0z3SSPcdS5xOpJPbJKCU9mXNmkyhxdcL5WWae6Mq6E0wjimEZad9rtdSD+KrzbO2dlDnFT3eWjsVVavsY+NrhNM2Tf3w4jTQDTTdK5gq6nqan9GYz/wCvS/uyILOZrYwhwDgC7YtqKOStit0IkdBG4Nc/VwboCeb2SrZ179j9wdy+fM9FTJtdfe64w/M2/WsXL5BPe1Fn5b84bLZbfQ4dqrWbdUSTPfNO2Tf3mhoAAA7S0DZ/wdDjzN/D2GqoONFUVQfV7vOYWAveO9qGka99aGp72DGNftC0JI13bfVEeHcA/vQdF6Sngo6SKmpomQwQsDI2MGjWNA0AA6AAq8ZnbXOBcJYiqbHa7dXYhmpH9TnnpntjgDx7JrXO4u0PDUDTtEqdMc1EtJgu91cDt2WG31EjHdpzY3EH5QuQUjnPkc9xLnOOpJ6Sgu3179j9wdy+fM9FOvfsfuDuXz5noqkSIOj+S+0/grMbEkOHH0dZYrpUaimZVOa6Od34jXt/C05gQNejjwU13+1UV8slZaLlC2ejrYHwTxnmcxw0I+Qrlvs64dveI848NQWSkmnfTXGCpnkY3sYImPDnPcegAD4zwXVQew07yDkJj2wS4Vxve8NzP6o+2V81Lv8A44Y8tDvjAB+NZTJzBNVmHmRZ8J0znxtrZvt8rRr1KFo3pH/E0HTv6L79oqqgrc9ca1FO4PjN5qGhw5iWvLT+0FTv6m5Y4J8W4oxDI0OmpKOKliJHseqPLnH5IwPjQXOwnYLThbDlDYLJSMpLdQxCKCJnM0ds9sk6knpJJUX5x7RuX2WtxdaKueou14Z/O0VA0OMP/UeSGtPe4nvLec4cTvwZljiHE8O71e30EksAdzGXTRmve3iFybuNZVXG4VFfXTyVFVUSOlmledXPe46kk9skoLrO237FvHdwJcyOjWtj9FeOvfsfuDuXz1noqkSILu9e/Y/cHcvnrPRUN7UOfVBnFarLQ0WHqm1G3TyyufNUNk399rRoAANOZQMiDyOddd8tfa7w38E0v1LFyIHOuu+W3teYcH/KqX6lqCKM/to+15S4yp8NVeGq26SzUTavqsVQ2NrQ572gaEHU9gflUd9e/Y/cHcvnrPRUaeqJe3lQfAUH10yragu8Nt+xa8cCXMDvVsforcsB7XeWWIbhFQXVtxw7LKQ1stbG10Gp6C9hO74SAO+ud6IOyVLUU9bSxVNNNHNBK0PjkjcHNe08QQRzhUb28cnqPDtdDmLhyiZT0FfP1G6QxDRsdQ7UtlA6A/Qg98D8Zbv6nZji5XXDt7wXcaqSoitBjnod86mOKQuDmA/ihwBA6N4qZdqm1R3bZ+xjA9m8Ybc+qb3nRaSA/wBlBy1REQF7Kb7pj98PpXrXspvuiP3wQTzt1+3JQ/8Ab9F9D1ASn3br9uSh/wC36L6HqAkBERAREQFPOwb98TbvzCr+qKgZT1sG/fE278wq/qig6PIiIPD/AGJXHS9/0zXfnEn7xXYt/sCuOd6/pmt/OJP3ig+RERAREQFu2SGYFflpmNbcUUWr4on9TrINeE0DuD2+HTiO0QFpKIOxWH7tQ32yUV4tlQypoq2Bk8ErDqHscNQf2r7lTf1PrNTqkM+V12l7OPfqrQ9zudvPLD8XF48Lu0rkICq9t7ZVnEeEI8fWeka+6WVm7Whg7Oak11175YTr4C7tK0K9VXTw1dLLTVETJYZWFkkbxq17SNCCOkEIONiKUtpzLKbK/M+stcEL22as1qrXIeIMLj7DXtsOre3wB6VFqApz2JMbvwjnbQ0M1R1O335v2Pna46N6oTrE7wh/D9IqDF7KaaWmqI6iCR0csTw9j2nQtcDqCD29UHY2upoK2hmpKmNssE0bo5GOGoc1w0IPeIK5O5y4OqcBZm33C1QwtbR1TvW7j+HC7so3DwtI/aummR2M4MfZW2LE8cjXS1VMG1IH4E7OxkB/SBPgIVavVGMBudHZsw6KIaM/ydX6DjodXROP9tvxtQU7tNBU3S60lsoonS1NXMyCFjRqXPe4NaPlIXWXKbCFFgTLyzYWoWgMoaVrJH9Mkp4yPPvnFx+NUh2BMBOxHmlLiuspg+34ej32OcNWmpfqIwO+0bzu8Q1X1xTeKPD2G7jfLhII6S30slTM4nTRrGlx+hBTH1RLH/r2+2rLyif9qoWiuryDwMrwRGz9Fup/THaVR1ncf4lr8Y40u2J7nIX1Vyqnzu7TQT2LR3mt0aO8FgkBXU9TU/ozGf8A16X92RUrV0vU1JG+scZxaje6tSu0727IEE4bXP3u2MPzNv1rFy9XUPa3a5+ztjANBJFED8QkYuXiAp+2CPvg6T4Oqv3QoBU+bBTg3aEogTpvW+qA/VCDozPFHPC+GZjZI3tLXtcNQ4EaEEdpaScosrj/APYOGvJsXorZMYmsbhO7m3Oe2tFDMacs9kJOpu3dO/rouWMmauZrXua7HeJA4HQg3GXh/aQdKeSDK33A4a8nReZOSDK33A4a8nReZc1eVjMz3e4j8oy+knKxmZ7vcR+UZfSQdT8PYdsGHKQ0ths1vtcBOrmUlO2Jrj2yGgaqINpDaCwxl7hytt1muVNcsUzMdFT01PIHimcR/OSkcG7vQ3nJ04aakUCu2YOO7tTup7ljG/VULho6OW4SuafCN7QrWSSTqUH6nlknnknmkdJLI4ue9x1LiTqST21dX1NXqf2ExidR1T11Ta+Dcf8A/wBVJ1bj1Nu8wRYoxVYZHBs1RSQ1UQ19kI3lrvrAgsFtjFw2c8V7v+wi18HVo9VzFXWnObDEmM8rcRYZgDTUV9BJHBvc3VdNWf2gFydr6SpoK2eirIJIKmnkdFLE8aOY5p0II7YIQehERAREQeRzrrvlv7XuHfgql+pauRA5113y29r3DnwVS/UtQUa9UT9vK3/AMH106rYrJ+qJe3lQfAUH10yrYgIiILYeptf594q+DYvrQrbZ5tDsl8atPMbDW/UPVSfU2v8APvFXwbF9arcZ3e03jT4BrfqHoOS6IiAvZTfdEfvgvWvZS/dMfvh9KCeduv25KH/t+i+h6gJT7t2e3JQ/AFF9D1ASAiIgIiICnnYN++Jt35hV/VFQMp52Dfvibd+YVf1RQdH0REHh/sSuOd6/pit/OJP3iuxj/Ylcc7z/AEvW/nEn7xQfIiIgIiICIiDI4ZvNww7iCgvtqndT11BOyeCRp5nNOo+LoI6Quq2TWPLdmPl5a8VW/RnrmPdqIddTBO3hJGfAebtgg9K5MKxGw9mqMEZgnDF3q3Msd+e2Ibx1ZBVc0b9OgO13Sfek8yDogiA6hEEP7V+VseZ2WVRBRwF19tmtVbHN9k94HZReB44e+DSuZMjHxyOjka5j2khzXDQgjoIXZYjULntt1ZWfyPx63GNqhLbPiCQulaG6Ngq+d7fA4dmO/vdpBXBERBcP1OnH0cFZeMvK6bdM/wDlC37x4FwAbKwd8jdd+i5W6xxhax40wxWYcxDRist1Yzdlj3i08DqHAjiCCAQR2lyTw1fLrhu+0l8sddLQ3GjkEsE8Z0LXD6R0EHgRwKvFsvbRONcz8bRYXumG7d1KKlfPV19M57NwNAAJYdRxcQOfp7yCdcpsuMM5ZYcfYcLwTx0sk7p5Hzy9Uke86DUnQcwAA8Cgn1QvHrbRgSgwNRz6Vl6k6tVNaeLaaNwI198/T9Qq0k0jIonSPcGtaCXE8wC5X7SGPH5iZu3m/MJ9Ysl9a0DSeaCMlrT+lxd+kgjlERAVp/U58SUtvzDvuHKmVkcl0oWy028dC98LtS0d/dc4+BpVWFksM3y6YbxBRX6y1T6S4UMwmglbztcPpHQR0glB11xLZrfiKwV1jusAnoa+B8E8eum8xw0PHoPfVQrzsPvdXyOs+Pmx0hOrGVVvLpGjtFzXgHw6BbBlrtm4WrbdHBju0VtquDdA6eij6tTydt2moczwdl4Vv42qclyNf5SVA8Nvm9FBTnaNyKrcm4LNNU4ip7uy6OlY0R0zojGYw09JOoO9+xa5s8YxgwHnFh7Eda5zaGGp6lVkDXdhkBY93xB2vxKXdtzNjA+ZVuwvFhG5yVslDNUOqA6nfHuh4jDfZAa+xPMqxIOydPNDVU0c0MjJYpWB7HtOoc0jUEdsFVwzO2QsFYqxHU3uzXWtw9JVvMk1NDE2WDfPsnNBILdTx0107QCgPILakxHl7a6bDmIKF2ILFAd2EmXdqaZn4rHHUOaOhp5uYEBWUtO1vk7WwCSe43S3v04x1FA4kfGwuCCOesft3u+q/J7fTXnrH7d7vqvye301KXXU5L+6So+YTeinXU5L+6So+YTeigi3rH7d7vqvye301g8wdjygwxga9YhhxtVVEttopapsT6FrWv3Gl26SH8NdOdTd11OS/ukqPmE3orWM2NpPKS+5ZYks9tv881ZW22eCCP1lK3ee5hAGpboOJQc/VuWS2OKjLvMuz4sga+SOkm0qYmHQywuG7I39UnTvgLTUQdhcMXy14lw/RXyzVcdXb62ISwTM5nNP0EcxHQQVE+cuzXgDMi6PvUramy3iQ6zVVCWgTntyMcCCe+ND2yVSXIzPPGWU9Q+C1yR3CzzO3prbVE9T3vxmEcWO744HpBVssI7Y+WlzpIvs7R3ix1ZH2xpgE8QPeew6keFoQam/YgtW92GPa4D/AIqBh/xr89Y/bfd9WeT2+mpS66nJf3Sz/MJvRTrqcl/dJUfMJvRQRb1j9u931X5Pb6ah7aeyFpMnbTZa6mxHPdjcp5InMkphHubjWnUEOOvOrZ9dTkv7pKj5hN6KrzttZuYFzKsOG6XCN0krZqKqmknDqd8e61zWgeyA14goKujnXXjLj2vsO/BdL9U1chhzrongvabyft2DbLQ1WI5o6imt8EUrPWMx3XtjaCNQ3TgQUEAeqJ+3jbvgGH66dVrU2bZOPsM5i5pUd7wpWPq6KG0xUz5HROj+2CSVxGjgDzOChNAREQWw9Ta/z7xV8GxfWhW3zwOmTWND/wAhrfqHqjOxRmRhHLfFl/rsXXB9FBV0LI4HthfJvOEgJGjQSOCsJmptLZR3nLXE1nt9+qKisrrVU00EYopRvyPic1o1LQBxI4lBz6REQF7KX7pj98PpXrXtpfumL34+lBPO3Z7ctD8AUX0PUAqftu325aH4Aov8agFAREQEREBT1sG/fE278wq/qyoFW1ZWY7vmXGMIMUYf9bGuhjkiAqI99ha9uh1GoQdbkXPyybXmatXfKGmmjsPUZqmON7RREdiXAHjvd9b/ALSe0hmDl9m1ccL2OGzmgpooXxmemL3nfjDjqd4dJQXDd7ErjneRpeK0f/kSfvFWBO2NmuWkdQw+Dpz+sncP7artPK+eeSaQ6vkcXOPbJOpQfhERAREQEREBfpjnMe17HFrmnUEHQgr8og6X7IeajMycs4YrhVtlxDaA2muDT7OQafa5tP8AiAOp/GDlNK5L5T5j4nyyxI6+4XqYo55IjDNFNHvxSsPHRze8QCDzhS514ubH+ww/8yd6aDoYtSzdwRbsxMv7phS47rWVcX2mYt3jBKOLJB4D8o1HSqQdeLmx/scP/MnemnXjZsafzGHvmTvTQQNiqxXLDOI7hh+7wGCvoJ3QTs7Tmno7YPOD2isYtuzYx/d8ycU/ykvtJboK90DIZHUcHUhLu66OdxOrtDpr2gB0LUUBdCdgbAT8M5Vy4mrqfqddiKUTM3m9kKZmoj+Ikud3wQqQZSYOq8e5i2XClJq011S1ssmmvUohxkf8TQSuslpoaa12ult1HGIqalhZDCwD2LGtAA+QIIf2y8fvwNkxXsopxFc7yTb6U69k0PB6q4eBmo16CQuaKn7bnx43F2cUtnoqnq1uw8w0bN09iZydZiPA4Bv6CgFAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQF7aX7pi9+PpXqXtpPuqL34+lBPO3b7c1F8AUf8AjUAqftu725qL4Ao/8agFAREQEREBERB9FtqPWlxpqrTXqMrZPkIKnbbmoS/NegxVS/bbXiGz01XSVDeLJAG7pAPbADT+kFAKsllVXWPOjKKDJ/EFwht2KbK502F66d+jJmnnp3a/GNB0bpA7HQhW1Fn8c4OxLgm+z2XE9pqLdWQuLdJG9g8D8Jjhwc09sEhYBAREQEREBERAREQERbLlfhOfHOYNlwlT1DaZ9zqmw9WcNRG3QlztOnQA8EGtIrAYjrNm/DF+rcKSYIxZdvWE76We6/ZMRyPexxa5zY9ANNQdNdFDWOmYZjxVXNwdPXzWIua6kdXNDZwC0Etdpw1DtRr06aoMIiIg2jLPHmIsusRuxBhienguBgdT9UmgbKAxxBOgcOB7EcfCpLdtXZ0OY5v2eoRvAjUW6LUeDgtSyhwXZ8U4Xx/crmaoTWCwur6PqLw1vVQ8Ab3DiO9wUcoPbV1E1XVzVVTI6WeZ7pJHuOpc4nUk+ElepSNfMG2aj2fMO44h9c/Za4Xqpop96TWLqbG6t0bpwPf1UcoCIvsslNHWXqho5t7qc9RHG/dPHRzgDp8qD40Vmc08IbPuUmNK203WDEeKq3sHstsFUIY6NhaOEkvO554nQcwIWBGBMs81LDc6rKaO7WPE1rp3VcthuMombWQt9l1B447w7R5+0OdBAiLyRodCvCAiKwOXmW2VTsgaXMvH10vFI5t1lpXwUT2l1XujsIo2kcD0l2vAA8yCvyKeLfcNmvE1UyxSYaxRhEznqUF3NeKlsbjwa6Vh/B159P2c6jLNfAl2y6xrV4Zu7opnxBskFTCdY6iFw1ZI3vEdHQdR0INUREQEW75M5d1+ZGLDaKerht1DSwOq7lXz/wA3S07PZPPbPQB/dqt9nvWzRaql1ogwdi2/UzDuOu7riIZJOgvbFoBp0gHRBBaKUc5Mt7TYLFasdYIus13wZenujppJ27tRSTNGroJgOG8NDoRz6fGYuQERfZZaeKrvNFSzlwhmqI45C08d0uAOnf0QfGiszmtg7Z+yjxpW2q6RYhxVW9g9lrp6tsUdGwtHCWXTVzz7LQcwIUJ5nV+A7ldKWpwFY7pZaUw6VNLW1Qn0k3jxY7n0005+lBqSIiDNYSwriDFdTV02H7bJXy0dLJWVDWOaNyFg1c46kc3a51hVajYvrct2Ut5p5rXfTiMWGtdc5xK31u+lGhLWDXUO3dBx6dVGeJLns+PsNdHYcMY2iuroXCklqK6Ixtk07EuA5xrzhBEaIiAiIgIiICIiAsphG11F7xVarPSRuknrayKnja0cSXvDf718FLT1FVUMp6WCSeaQ7rI42lznHtADiVZnKnCdHkLhs5tZjxNjxFNA+PDdheAZ+qOaR1WQfg6A+FoJ17IgINU246+nq8+6ukp3h4ttvpaN5B10c1m8R/aUGL7sQXauvt8rr1c53VFbXVD6ieRx4ue9xJPylfCgIiICIiAiIgL9wySQytlhkdHIwhzXtOhaRzEHoK/CIJtw7tJ4zhs0dixlarHjm1MG71K90vVJdO9Jz699wJX3R5y5RvO9U7PFg3jz9TuL2j4hucFAiIJ+OceTY5tnizfHdH/w14OceTv9XiyeU3/w1ASIJ75Y8n/6vFk8pv8AQXnljye/q8WTym/0FAaIJ75Y8n/6vFk8pv8AQTljyf8A6vFj8pv9BQIiCfhnJk5px2eLL5Tf/DX6bnJkz+Fs72b4ro7+Gq/ogmPMDM7LG+4SrrVh/JW12C4VDWiG4Mr3SPgIcCSBuDXUAjn6VFeHrxccP3yjvVoqn0tfRTNmp5mc7HtOoK+BZXCN4ZYMSUN4ltVBdo6WTffR10XVIJxoQWvb0jQ/EdCgmKPOHLvGUzn5r5XUVTcZj9uvNilNJUPP474/Yvd39fiWnZ+Zf2/AOKKBtiuclysN6t8d0tc0rd2UQSE6NkGg7IaHjoNeHALaY8yMkNfX78jR6/HZdRF7k9bb3vd32Pe0Ud5qY8vOYmKnX68Mp4NyFtPS0lMzdhpYGa7kbB0Aan4yUGqIiIJv2XopLhhzNayUg6pXVmD53U8I9lIWOBIA6TxUIHgdFsWXWMr5gLFtHifD07Iq6lJ0Ejd5kjCNHMeOlpHAqS6rM7JytqJLxW5IQm7yEySRQ3mRlG6Q8SephvAE/goPzi1srNjrBXVI3Na/E1a5hI9kNzTUfHr8ihRStm5nVcsxsEWbC9Zh21WmC0Vb5qf7HtMcbYy3dZE2PoDR068e8opQFksK/wCdFq/PYf3wsaslhYb2J7U3m1rYR/bCCTtsqKSLaLxR1Rjm78kL26jTUGFnEL2bGdvuNVtAWGvpA5lLbBNV18+ujIacRPa4uPQCXAfGpQ2kszsLNzkvmGcwsvKDEtFbXxsoKunndS1kLDG1xY57dd9uriQDppqVFWLM46CLCtbhLLPB1Lgy03Fu5cpmzmorKxv4jpXDVrOJ7Eds8eJQRpi6oo6vFd3qreAKOaumkpwBppGXkt/YQsWiICnLEkEr9irCs7GOcyLFtSHkDg3WJ2mvyKDVZ3C2N3YJ2QbA6osFrv8AarniSqprhQV7CWyxhm8N1w4scC0EO46IKywxvllZHGxz3vcGta0akk8wCnXbDYaSvwBZ6x4debdhKjhuIPsmyaahru+B9K9NHm5lhhmYXjBGTtLSYgj7KmqbncpKuGlf0PbGQNSOjiNFEGKb9dsT4grb/fK2WtuNbKZZ5pDqXH+4AaADmAACDGIiIJ42aYZrllVnDY7UT9mqqxwy07G+zkhjkcZmt8LSBp3woHWdwHi2/YIxRSYkw5XOo7hSk7rhxa5p4Fjh+E0jgQVKc2aeUV2qnXrEGSdNJepCZJxQ3WSnpJpDxLupAHdBPHTig+izwutOxTfn3ppjZesSwGyxv53Oja3qsjR2t1rm695QOt4zYzLveYddRisgpLZaLbH1G2WmhZuU1HHw4NHSdANSe10cy0dAWQw2NcRW0duri/fCx699uqXUVwp6xjQ50ErZADzEtIP9yCTdrZpbtG4zBOv/AMa0/LExRWtpzYxhJj7MS8YwloWUD7nMJDTtk3xHoxrdN7Qa+x7S1ZAREQTpsbgvxXi+JnGSTCVe1jRzk7reZQWeB0Wz5X43vGXuNKPFFk6k+op95j4Zm6xzxuGj43DtEfJzrd8X5g5UXC0XE2LJ6G3Xmvjc31xLdZJYaVzud8cYAGo14DgBw8CCMcOVlFbr/QV9xtzLnR09QySeje8tbOwOBLCRzajhqpvfnHkwRo3Z4tHx3R/8NQAiCfRnFk1/V4s/lR/8NfoZx5MdOzxaPKjv4agBEFgOWPJf+rxaPKjv4aDOPJf+rvaPKjv4ar+iCwXLJkt/V3tHlR38Nfk5yZMdGzvZ/jujv4ar+iCfTtHU9ha7k1yswjhGd43XVnUfXNRp3nEN0+PVQ5jPFWIcY32a94mutTcq+XgZZna7o6GtHM1o7Q0CwqICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiICIiAiIgIiIC+m11PrK50tZul3UJmS6A6a7rgdP2L5kQbnnZjODMDM28YtpqKWihr5GubBI8OcwNY1vEjh+CtMREBERAW9XTHkVZkjaMuxQSNlt95muJqjIN1wezdDQ3TXUanitFRAREQEREBERAREQEREBERAREQEREBERAREQEREBERAREQEREBERB//2Q==" alt="Rytech Support" style="width:200px;height:auto;display:block;margin:0 auto 12px;">
    <h1>Rytech SummarAI</h1>
  </div>
  <div class="alert error"   id="errMsg"></div>
  <div class="alert success" id="okMsg"></div>
  <div class="field">
    <label for="email">Email Address</label>
    <input type="email" id="email" placeholder="you@rytech-support.com" autocomplete="email" autofocus>
  </div>
  <div class="field">
    <label for="password">Password</label>
    <input type="password" id="password" placeholder="&bull;&bull;&bull;&bull;&bull;&bull;&bull;&bull;" autocomplete="current-password">
  </div>
  <label class="remember">
    <input type="checkbox" id="remember"> Keep me signed in for 30 days
  </label>
  <button class="btn" id="loginBtn" onclick="doLogin()">Sign In</button>
  <div class="footer">Rytech SummarAI v6.5.0 -- Secure access</div>
</div>
</div><!-- end loginForm -->

<!-- 2FA Panel -->
<div id="totpForm" style="display:none;">
<div class="card">
  <div class="logo" style="text-align:center;margin-bottom:8px;font-size:2rem;">&#x1F512;</div>
  <h2 style="text-align:center;font-size:1rem;font-weight:700;margin-bottom:6px;">Two-Factor Authentication</h2>
  <p style="text-align:center;font-size:0.82rem;color:var(--muted,#5a7080);margin-bottom:20px;">Enter the 6-digit code from your authenticator app, or a backup code.</p>
  <div class="field">
    <div id="totpErr" class="error" style="display:none;margin-bottom:12px;"></div>
    <input id="totpInput" type="text" inputmode="numeric" autocomplete="one-time-code" maxlength="8"
      placeholder="000000"
      style="text-align:center;font-size:1.5rem;letter-spacing:10px;padding:14px;"
      onkeydown="if(event.key==='Enter')submitTotp()">
  </div>
  <button class="btn" onclick="submitTotp()">Verify Code</button>
  <button class="btn" style="margin-top:8px;background:transparent;border:1px solid var(--border,#2a3340);color:var(--muted,#5a7080);" onclick="cancelTotp()">&#8592; Back</button>
</div>
</div>

<script>
window._totpCode = null;
function submitTotp() {
  var code = document.getElementById('totpInput').value.trim();
  var errEl = document.getElementById('totpErr');
  if (!code) { errEl.textContent='Please enter your code.'; errEl.style.display='block'; return; }
  errEl.style.display='none';
  window._totpCode = code;
  doLogin();
}
function cancelTotp() {
  window._totpCode = null;
  document.getElementById('totpForm').style.display = 'none';
  document.getElementById('loginForm').style.display = '';
  document.getElementById('totpInput').value = '';
}
</script>
<script>
document.addEventListener('keydown', function(e) {
  if (e.key === 'Enter') doLogin();
});
async function doLogin() {
  var email    = document.getElementById('email').value.trim();
  var password = document.getElementById('password').value;
  var remember = document.getElementById('remember').checked;
  var btn      = document.getElementById('loginBtn');
  var errEl    = document.getElementById('errMsg');
  var okEl     = document.getElementById('okMsg');
  errEl.style.display = 'none';
  okEl.style.display  = 'none';
  if (!email || !password) {
    errEl.textContent = 'Please enter your email and password.';
    errEl.style.display = 'block';
    return;
  }
  btn.disabled = true;
  btn.innerHTML = '<span class="spinner"></span>Signing in&#8230;';
  try {
    var resp = await fetch('/auth/login', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ email: email, password: password, remember: remember, totp_code: window._totpCode || null })
    });
    var data = await resp.json();
    if (data.ok) {
      okEl.textContent = 'Signed in! Loading&#8230;';
      okEl.style.display = 'block';
      // Store session token in localStorage -- used for reauth if cookie is lost
      console.log('[RYTECH LOGIN] data.ok=', data.ok, 'data.token type=', typeof data.token, 'token start=', (data.token||'').substring(0,20));
      localStorage.setItem('ry_remember_token', data.token);
      console.log('[RYTECH LOGIN] localStorage set, value=', localStorage.getItem('ry_remember_token') ? 'OK' : 'NULL');
      window._totpCode = null;
      setTimeout(function() { window.location.href = '/'; }, 400);
    } else if (data['2fa_required']) {
      // Show 2FA input panel
      document.getElementById('loginForm').style.display = 'none';
      document.getElementById('totpForm').style.display = '';
      document.getElementById('totpInput').focus();
      btn.disabled = false;
      btn.textContent = 'Sign In';
    } else {
      errEl.textContent = data.error || 'Login failed.';
      errEl.style.display = 'block';
      window._totpCode = null;
      btn.disabled = false;
      btn.textContent = 'Sign In';
    }
  } catch(e) {
    errEl.textContent = 'Connection error. Please try again.';
    errEl.style.display = 'block';
    btn.disabled = false;
    btn.textContent = 'Sign In';
  }
}
</script>
</body>
</html>"""


# ══════════════════════════════════════════════════════════════════
#  HTTP HANDLER
# ══════════════════════════════════════════════════════════════════

USER_MGMT_PAGE = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Rytech SummarAI &mdash; User Management</title>
<style>
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  :root {
    --bg:#0a0d10; --surface:#111518; --surface2:#161b20; --border:#1e2730;
    --accent:#2196f3; --accent2:#1565c0; --text:#e8eef2; --muted:#5a7080;
    --error:#ef5350; --warn:#ff9800; --success:#4caf50; --danger:#f44336;
  }
  body { background:var(--bg); color:var(--text);
    font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;
    min-height:100vh; padding:0; }
  .topbar { background:var(--surface); border-bottom:1px solid var(--border);
    padding:0 24px; height:60px; display:flex; align-items:center; justify-content:space-between; }
  .topbar-left { display:flex; align-items:center; gap:16px; }
  .topbar-left h1 { font-size:1.05rem; font-weight:700; }
  .topbar-left .back { color:var(--accent); text-decoration:none; font-size:0.85rem;
    display:flex; align-items:center; gap:5px; padding:6px 12px; border:1px solid var(--border);
    border-radius:6px; transition:background 0.2s; }
  .topbar-left .back:hover { background:rgba(33,150,243,0.1); }
  .topbar-right { display:flex; align-items:center; gap:12px; font-size:0.85rem; color:var(--muted); }
  .main { max-width:1200px; margin:0 auto; padding:28px 24px; }

  /* Tabs */
  .tabs { display:flex; gap:0; border-bottom:1px solid var(--border); margin-bottom:28px; }
  .tab-btn { padding:11px 22px; font-size:0.88rem; font-weight:600; background:none; border:none;
    color:var(--muted); cursor:pointer; border-bottom:2px solid transparent; margin-bottom:-1px;
    transition:all 0.2s; }
  .tab-btn:hover { color:var(--text); }
  .tab-btn.active { color:var(--accent); border-bottom-color:var(--accent); }
  .tab-panel { display:none; }
  .tab-panel.active { display:block; }

  .section-header { display:flex; align-items:center; justify-content:space-between; margin-bottom:20px; }
  .section-header h2 { font-size:1.05rem; font-weight:600; }
  .btn { display:inline-flex; align-items:center; gap:7px; border:none; border-radius:7px;
    padding:9px 16px; font-size:0.85rem; font-weight:600; cursor:pointer; transition:all 0.2s; }
  .btn-primary { background:linear-gradient(135deg,var(--accent2),var(--accent)); color:#fff; }
  .btn-primary:hover { opacity:0.9; }
  .btn-danger  { background:rgba(244,67,54,0.15); color:#ef9a9a; border:1px solid rgba(244,67,54,0.3); }
  .btn-danger:hover { background:rgba(244,67,54,0.25); }
  .btn-warn    { background:rgba(255,152,0,0.15); color:#ffcc80; border:1px solid rgba(255,152,0,0.3); }
  .btn-warn:hover { background:rgba(255,152,0,0.25); }
  .btn-ghost   { background:transparent; color:var(--muted); border:1px solid var(--border); }
  .btn-ghost:hover { background:rgba(255,255,255,0.05); color:var(--text); }
  .btn-sm { padding:5px 11px; font-size:0.78rem; }
  .btn-success { background:rgba(76,175,80,0.15); color:#a5d6a7; border:1px solid rgba(76,175,80,0.3); }
  .btn-success:hover { background:rgba(76,175,80,0.25); }
  .card { background:var(--surface); border:1px solid var(--border); border-radius:12px; overflow:hidden; }
  table { width:100%; border-collapse:collapse; }
  th { padding:11px 16px; text-align:left; font-size:0.75rem; font-weight:600; color:var(--muted);
    letter-spacing:0.4px; text-transform:uppercase; background:rgba(255,255,255,0.02);
    border-bottom:1px solid var(--border); }
  td { padding:13px 16px; font-size:0.875rem; border-bottom:1px solid rgba(30,39,48,0.7); vertical-align:middle; }
  tr:last-child td { border-bottom:none; }
  tr:hover td { background:rgba(255,255,255,0.02); }
  .badge { display:inline-block; padding:3px 9px; border-radius:100px; font-size:0.72rem; font-weight:600; }
  .badge-superadmin { background:rgba(156,39,176,0.2); color:#ce93d8; border:1px solid rgba(156,39,176,0.3); }
  .badge-admin   { background:rgba(33,150,243,0.15); color:#90caf9; border:1px solid rgba(33,150,243,0.3); }
  .badge-manager { background:rgba(255,152,0,0.15); color:#ffcc80; border:1px solid rgba(255,152,0,0.3); }
  .badge-staff   { background:rgba(96,125,139,0.2); color:#90a4ae; border:1px solid rgba(96,125,139,0.3); }
  .badge-active   { background:rgba(76,175,80,0.15); color:#a5d6a7; border:1px solid rgba(76,175,80,0.3); }
  .badge-inactive { background:rgba(239,83,80,0.1); color:#ef9a9a; border:1px solid rgba(239,83,80,0.2); }
  .badge-mustchange { background:rgba(255,152,0,0.15); color:#ffcc80; border:1px solid rgba(255,152,0,0.3); font-size:0.68rem; }
  .actions { display:flex; gap:7px; }
  .empty { text-align:center; padding:48px; color:var(--muted); font-size:0.9rem; }

  /* Modal */
  .modal-bg { display:none; position:fixed; inset:0; background:rgba(0,0,0,0.7);
    z-index:1000; align-items:center; justify-content:center; padding:20px; }
  .modal-bg.open { display:flex; }
  .modal { background:var(--surface); border:1px solid var(--border); border-radius:14px;
    padding:32px; width:100%; max-width:460px; box-shadow:0 24px 80px rgba(0,0,0,0.6); }
  .modal h3 { font-size:1.05rem; font-weight:700; margin-bottom:22px; }
  .field { margin-bottom:16px; }
  .field label { display:block; font-size:0.8rem; font-weight:500; color:var(--muted); margin-bottom:6px; }
  .field input, .field select {
    width:100%; background:rgba(255,255,255,0.04); border:1px solid var(--border);
    border-radius:7px; padding:10px 12px; color:var(--text); font-size:0.9rem; outline:none; }
  .field input:focus, .field select:focus { border-color:var(--accent); }
  .field select option { background:#1a2028; }
  .modal-footer { display:flex; gap:10px; justify-content:flex-end; margin-top:24px; }
  .alert { padding:10px 14px; border-radius:8px; font-size:0.83rem; margin-bottom:14px; display:none; }
  .alert.error { background:rgba(239,83,80,0.12); border:1px solid rgba(239,83,80,0.3); color:#ef9a9a; }
  .alert.success { background:rgba(76,175,80,0.12); border:1px solid rgba(76,175,80,0.3); color:#a5d6a7; }
  .spinner { display:inline-block; width:14px; height:14px;
    border:2px solid rgba(255,255,255,0.3); border-top-color:#fff;
    border-radius:50%; animation:spin 0.7s linear infinite; vertical-align:middle; margin-right:5px; }
  @keyframes spin { to { transform:rotate(360deg); } }
  .toast { position:fixed; bottom:24px; right:24px; background:#1e2730;
    border:1px solid var(--border); border-radius:9px; padding:12px 18px;
    font-size:0.85rem; box-shadow:0 8px 32px rgba(0,0,0,0.4);
    transform:translateY(80px); opacity:0; transition:all 0.3s; z-index:2000; }
  .toast.show { transform:translateY(0); opacity:1; }
  .toast.ok   { border-left:3px solid var(--success); }
  .toast.err  { border-left:3px solid var(--error); }
  .confirm-bg { display:none; position:fixed; inset:0; background:rgba(0,0,0,0.75);
    z-index:2000; align-items:center; justify-content:center; padding:20px; }
  .confirm-bg.open { display:flex; }
  .confirm-box { background:var(--surface); border:1px solid var(--border); border-radius:12px;
    padding:28px; max-width:380px; width:100%; }
  .confirm-box h4 { font-size:1rem; font-weight:600; margin-bottom:10px; }
  .confirm-box p  { font-size:0.85rem; color:var(--muted); line-height:1.6; margin-bottom:22px; }
  .confirm-footer { display:flex; gap:10px; justify-content:flex-end; }

  /* Role Permissions */
  .perms-grid { background:var(--surface); border:1px solid var(--border); border-radius:12px; overflow:hidden; }
  .perms-grid table { width:100%; border-collapse:collapse; }
  .perms-grid th { padding:12px 18px; font-size:0.72rem; font-weight:700; color:var(--muted);
    text-transform:uppercase; letter-spacing:0.5px; background:rgba(255,255,255,0.02);
    border-bottom:1px solid var(--border); text-align:center; }
  .perms-grid th.section-col { text-align:left; min-width:180px; }
  .perms-grid td { padding:11px 18px; border-bottom:1px solid rgba(30,39,48,0.5);
    text-align:center; vertical-align:middle; }
  .perms-grid td.section-name { text-align:left; font-size:0.88rem; font-weight:500; }
  .perms-grid td.section-name .icon { margin-right:8px; font-size:1rem; }
  .perms-grid tr:last-child td { border-bottom:none; }
  .perms-grid tr:hover td { background:rgba(255,255,255,0.02); }

  /* Toggle switch */
  .toggle { position:relative; display:inline-block; width:40px; height:22px; }
  .toggle input { opacity:0; width:0; height:0; }
  .toggle-slider { position:absolute; cursor:pointer; inset:0; background:#1e2730;
    border-radius:22px; transition:0.25s; border:1px solid #2a3540; }
  .toggle-slider:before { position:absolute; content:''; height:16px; width:16px;
    left:2px; bottom:2px; background:#5a7080; border-radius:50%; transition:0.25s; }
  .toggle input:checked + .toggle-slider { background:rgba(33,150,243,0.3); border-color:var(--accent); }
  .toggle input:checked + .toggle-slider:before { transform:translateX(18px); background:var(--accent); }
  .toggle input:disabled + .toggle-slider { opacity:0.4; cursor:not-allowed; }

  .role-col-header { display:flex; flex-direction:column; align-items:center; gap:3px; }
  .role-col-header .role-badge { font-size:0.7rem; padding:2px 8px; border-radius:100px; font-weight:700; }

  .perms-save-bar { display:flex; align-items:center; justify-content:space-between;
    padding:16px 0 0 0; margin-top:16px; }
  .perms-note { font-size:0.78rem; color:var(--muted); }
  .perms-note strong { color:var(--warn); }
  .unsaved-dot { display:inline-block; width:7px; height:7px; background:var(--warn);
    border-radius:50%; margin-right:6px; display:none; }
  .unsaved-dot.show { display:inline-block; }
</style>
</head>
<body>

<div class="topbar">
  <div class="topbar-left">
    <a href="/" class="back">&#8592; Back to App</a>
    <h1>&#x1F464; User Management</h1>
  </div>
  <div class="topbar-right" id="currentUserInfo">Loading...</div>
</div>

<div class="main">
  <div class="tabs">
    <button class="tab-btn active" onclick="switchTab('users')">&#x1F465; Users</button>
    <button class="tab-btn" onclick="switchTab('roles')">&#x1F6E1; Role Permissions</button>
    <button class="tab-btn" onclick="switchTab('my2fa')">&#x1F512; My 2FA</button>
  </div>

  <!-- USERS TAB -->
  <div class="tab-panel active" id="tab-users">
    <div class="section-header">
      <h2 id="userCount">Users</h2>
      <button class="btn btn-primary" onclick="openCreate()">&#x2B; Add User</button>
    </div>
    <div class="card">
      <div id="tableWrap"><div class="empty">Loading users...</div></div>
    </div>
  </div>

  <!-- MY 2FA TAB -->
  <div class="tab-panel" id="tab-my2fa">
    <div class="section-header">
      <h2>My Two-Factor Authentication</h2>
    </div>
    <div class="card" style="max-width:520px;padding:28px;" id="twoFaCard">
      <div id="twoFaStatus">Loading...</div>
    </div>
  </div>

  <!-- ROLE PERMISSIONS TAB -->
  <div class="tab-panel" id="tab-roles">
    <div class="section-header">
      <h2>Role Permissions</h2>
      <div style="display:flex;align-items:center;gap:10px;">
        <span class="unsaved-dot" id="unsavedDot"></span>
        <button class="btn btn-success" onclick="savePerms()">&#x2713; Save Changes</button>
      </div>
    </div>
    <p style="font-size:0.83rem;color:var(--muted);margin-bottom:20px;">
      Control which sections each role can see. <strong style="color:#ce93d8">Superadmin</strong> and <strong style="color:#90caf9">Admin</strong> always have full access.
    </p>
    <div class="perms-grid">
      <table id="permsTable">
        <thead><tr>
          <th class="section-col">Section</th>
          <th><div class="role-col-header"><span class="role-badge badge-manager">Manager</span></div></th>
          <th><div class="role-col-header"><span class="role-badge badge-staff">Staff</span></div></th>
        </tr></thead>
        <tbody id="permsTbody"><tr><td colspan="3" class="empty">Loading...</td></tr></tbody>
      </table>
    </div>
    <div class="perms-save-bar">
      <span class="perms-note">Changes take effect on next login. <strong>Superadmin & Admin always have full access.</strong></span>
    </div>
  </div>
</div>

<!-- Create/Edit Modal -->
<div class="modal-bg" id="userModal">
  <div class="modal">
    <h3 id="modalTitle">Add User</h3>
    <div class="alert error" id="modalErr"></div>
    <div class="field">
      <label>Full Name</label>
      <input type="text" id="f-name" placeholder="John Smith">
    </div>
    <div class="field">
      <label>Email Address</label>
      <input type="email" id="f-email" placeholder="john@rytech-support.com">
    </div>
    <div class="field" id="f-pw-wrap">
      <label id="f-pw-label">Password</label>
      <input type="password" id="f-password" placeholder="Min 8 characters" autocomplete="new-password">
    </div>
    <div class="field">
      <label>Role</label>
      <select id="f-role">
        <option value="staff">Staff</option>
        <option value="manager">Manager</option>
        <option value="admin">Admin</option>
        <option value="superadmin">Superadmin</option>
      </select>
    </div>
    <div class="field">
      <label>Status</label>
      <select id="f-active">
        <option value="1">Active</option>
        <option value="0">Inactive</option>
      </select>
    </div>
    <div class="modal-footer">
      <button class="btn btn-ghost" onclick="closeModal()">Cancel</button>
      <button class="btn btn-primary" id="modalSaveBtn" onclick="saveUser()">Create User</button>
    </div>
  </div>
</div>

<!-- Confirm Delete -->
<div class="confirm-bg" id="confirmDel">
  <div class="confirm-box">
    <h4>Delete User?</h4>
    <p id="confirmDelMsg">This will permanently delete the user.</p>
    <div class="confirm-footer">
      <button class="btn btn-ghost" onclick="closeConfirm()">Cancel</button>
      <button class="btn btn-danger" id="confirmDelBtn">Delete</button>
    </div>
  </div>
</div>

<!-- Confirm Reset PW -->
<div class="confirm-bg" id="confirmReset">
  <div class="confirm-box">
    <h4>Reset Password?</h4>
    <p id="confirmResetMsg"></p>
    <div class="field" style="margin-top:16px">
      <label>New Password</label>
      <input type="password" id="resetPwInput" placeholder="Min 8 characters" autocomplete="new-password">
    </div>
    <div class="alert error" id="resetErr" style="margin-top:8px"></div>
    <div class="confirm-footer" style="margin-top:16px">
      <button class="btn btn-ghost" onclick="closeReset()">Cancel</button>
      <button class="btn btn-warn" id="confirmResetBtn" onclick="doReset()">Reset Password</button>
    </div>
  </div>
</div>

<div class="toast" id="toast"></div>

<script>
var _users = [];
var _me = null;
var _editId = null;
var _deleteId = null;
var _resetId = null;
var _permsData = {};  // {role: {section: bool}}
var _permsChanged = false;

var SECTIONS = [
  { key:'dashboard',  label:'Dashboard',       icon:'🏠' },
  { key:'meetings',   label:'Meetings',         icon:'📋' },
  { key:'tasks',      label:'Tasks',            icon:'✅' },
  { key:'contacts',   label:'Contacts',         icon:'🏢' },
  { key:'contracts',  label:'Contracts',        icon:'📄' },
  { key:'finance',    label:'Finance',          icon:'💰' },
  { key:'monzo',      label:'Monzo',            icon:'🏦' },
  { key:'support',    label:'Rytech Support',   icon:'🎧' },
  { key:'analytics',  label:'Analytics',        icon:'📊' },
  { key:'rmm',        label:'RMM',              icon:'🖥' },
  { key:'patches',    label:'Patch Management', icon:'🔧' }
];
var MANAGED_ROLES = ['manager', 'staff'];

function switchTab(tab) {
  document.querySelectorAll('.tab-btn').forEach(function(b,i) {
    b.classList.toggle('active',
      (i===0 && tab==='users') || (i===1 && tab==='roles') || (i===2 && tab==='my2fa'));
  });
  document.getElementById('tab-users').classList.toggle('active', tab==='users');
  document.getElementById('tab-roles').classList.toggle('active', tab==='roles');
  document.getElementById('tab-my2fa').classList.toggle('active', tab==='my2fa');
  if (tab==='roles') loadPerms();
  if (tab==='my2fa') load2faStatus();
}

async function disable2fa(id) {
  var uObj = _users.find(function(u){ return u.id === id; });
  var name = uObj ? (uObj.name || uObj.email) : 'this user';
  if (!confirm('Disable 2FA for ' + name + '? They will need to set it up again.')) return;
  try {
    var r = await fetch('/auth/2fa/admin-disable', {
      method: 'POST', credentials: 'include',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({user_id: id})
    });
    var d = await r.json();
    if (d.ok) { showToast('2FA disabled for ' + name, 'ok'); await loadAll(); }
    else showToast(d.error || 'Failed', 'err');
  } catch(e) { showToast('Error: ' + e.message, 'err'); }
}

async function loadAll() {
  try {
    var r1 = await fetch('/auth/me', {credentials:'include'});
    var r2 = await fetch('/admin/users', {credentials:'include'});
    if (!r1.ok) {
      document.getElementById('userTableBody').innerHTML = '<tr><td colspan="7" style="color:#ef5350;padding:20px">/auth/me returned ' + r1.status + ' - session may not be passing. Try closing and reopening this tab from the main app.</td></tr>';
      document.getElementById('userCount').textContent = 'Error';
      return;
    }
    if (!r2.ok) {
      document.getElementById('userTableBody').innerHTML = '<tr><td colspan="7" style="color:#ef5350;padding:20px">/admin/users returned ' + r2.status + '</td></tr>';
      document.getElementById('userCount').textContent = 'Error';
      return;
    }
    var meResp = await r1.json();
    _me = (meResp && meResp.user) ? meResp.user : meResp;
    var d = await r2.json();
    if (_me && _me.name) {
      document.getElementById('currentUserInfo').textContent = _me.name + ' (' + _me.role + ')';
    }
    if (!d.ok) { showToast(d.error || 'Failed to load users', 'err'); return; }
    _users = d.users;
    renderTable();
  } catch(e) {
    document.getElementById('userTableBody').innerHTML = '<tr><td colspan="7" style="color:#ef5350;padding:20px">JS Error: ' + e.message + '</td></tr>';
    document.getElementById('userCount').textContent = 'Error';
  }
}

function renderTable() {
  var isSuper = _me && _me.role === 'superadmin';
  document.getElementById('userCount').textContent = 'Users (' + _users.length + ')';
  var html = '<table><thead><tr>'
    + '<th>Name</th><th>Email</th><th>Role</th><th>2FA</th><th>Status</th>'
    + '<th>Last Login</th><th>Actions</th></tr></thead><tbody>';
  _users.forEach(function(u) {
    var roleBadge = '<span class="badge badge-' + u.role + '">' + u.role + '</span>';
    var statusBadge = u.active
      ? '<span class="badge badge-active">Active</span>'
      : '<span class="badge badge-inactive">Inactive</span>';
    if (u.must_change_password) statusBadge += ' <span class="badge badge-mustchange">Must Change PW</span>';
    var twoFaBadge = u.totp_enabled
      ? '<span class="badge badge-active" style="font-size:0.7rem;">2FA ON</span>'
      : '<span class="badge badge-inactive" style="font-size:0.7rem;">2FA OFF</span>';
    var canEdit = _me && (_me.role === 'superadmin' || (_me.role === 'admin' && u.role !== 'superadmin'));
    var actionsHtml = '';
    if (canEdit) {
      actionsHtml = '<div class="actions">'
        + '<button class="btn btn-ghost btn-sm" onclick="openEdit(' + u.id + ')">Edit</button>'
        + '<button class="btn btn-warn btn-sm" onclick="openReset(' + u.id + ')">Reset PW</button>'
        + (u.totp_enabled ? '<button class="btn btn-ghost btn-sm" onclick="disable2fa(' + u.id + ')">Disable 2FA</button>' : '')
        + (isSuper && u.id !== (_me && _me.id)
           ? '<button class="btn btn-danger btn-sm" onclick="openDelete(' + u.id + ')">Delete</button>'
           : '')
        + '</div>';
    }
    html += '<tr>'
      + '<td>' + esc(u.name || '') + '</td>'
      + '<td style="color:var(--muted);font-size:0.82rem">' + esc(u.email) + '</td>'
      + '<td>' + roleBadge + '</td>'
      + '<td>' + twoFaBadge + '</td>'
      + '<td>' + statusBadge + '</td>'
      + '<td style="color:var(--muted);font-size:0.78rem">' + (u.last_login ? u.last_login.slice(0,16).replace('T',' ') : '&mdash;') + '</td>'
      + '<td>' + actionsHtml + '</td>'
      + '</tr>';
  });
  html += '</tbody></table>';
  document.getElementById('tableWrap').innerHTML = html;
}

function esc(s) { return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }

function openCreate() {
  _editId = null;
  document.getElementById('modalTitle').textContent = 'Add User';
  document.getElementById('modalSaveBtn').textContent = 'Create User';
  document.getElementById('f-name').value = '';
  document.getElementById('f-email').value = '';
  document.getElementById('f-password').value = '';
  document.getElementById('f-role').value = 'staff';
  document.getElementById('f-active').value = '1';
  document.getElementById('f-pw-wrap').style.display = '';
  document.getElementById('f-pw-label').textContent = 'Password';
  document.getElementById('modalErr').style.display = 'none';
  document.getElementById('userModal').classList.add('open');
  setTimeout(function(){ document.getElementById('f-name').focus(); }, 100);
}

function openEdit(id) {
  var u = _users.find(function(x){ return x.id === id; });
  if (!u) return;
  _editId = id;
  document.getElementById('modalTitle').textContent = 'Edit User';
  document.getElementById('modalSaveBtn').textContent = 'Save Changes';
  document.getElementById('f-name').value = u.name || '';
  document.getElementById('f-email').value = u.email;
  document.getElementById('f-password').value = '';
  document.getElementById('f-role').value = u.role;
  document.getElementById('f-active').value = u.active ? '1' : '0';
  document.getElementById('f-pw-wrap').style.display = 'none';
  document.getElementById('modalErr').style.display = 'none';
  document.getElementById('userModal').classList.add('open');
}

function closeModal() { document.getElementById('userModal').classList.remove('open'); }

async function saveUser() {
  var name   = document.getElementById('f-name').value.trim();
  var email  = document.getElementById('f-email').value.trim();
  var pw     = document.getElementById('f-password').value;
  var role   = document.getElementById('f-role').value;
  var active = document.getElementById('f-active').value === '1';
  var errEl  = document.getElementById('modalErr');
  errEl.style.display = 'none';
  if (!name || !email) { errEl.textContent = 'Name and email are required.'; errEl.style.display='block'; return; }
  if (!_editId && pw.length < 8) { errEl.textContent = 'Password must be at least 8 characters.'; errEl.style.display='block'; return; }
  var btn = document.getElementById('modalSaveBtn');
  btn.innerHTML = '<span class="spinner"></span>Saving...';
  btn.disabled = true;
  try {
    var url = _editId ? '/admin/users/update' : '/admin/users/create';
    var body = _editId
      ? { id:_editId, name:name, email:email, role:role, active:active }
      : { name:name, email:email, password:pw, role:role };
    var r = await fetch(url, { method:'POST', credentials:'include',
      headers:{'Content-Type':'application/json'}, body:JSON.stringify(body) });
    var d = await r.json();
    if (d.ok) {
      closeModal();
      showToast(_editId ? 'User updated.' : 'User created.', 'ok');
      await loadAll();
    } else {
      errEl.textContent = d.error || 'Something went wrong.';
      errEl.style.display = 'block';
    }
  } catch(e) { errEl.textContent = 'Error: ' + e.message; errEl.style.display='block'; }
  btn.innerHTML = _editId ? 'Save Changes' : 'Create User';
  btn.disabled = false;
}

function openDelete(id) {
  var u = _users.find(function(x){ return x.id === id; });
  if (!u) return;
  _deleteId = id;
  document.getElementById('confirmDelMsg').textContent = 'This will permanently delete ' + (u.name || u.email) + '. This cannot be undone.';
  var btn = document.getElementById('confirmDelBtn');
  btn.onclick = doDelete;
  document.getElementById('confirmDel').classList.add('open');
}

function closeConfirm() { document.getElementById('confirmDel').classList.remove('open'); }

async function doDelete() {
  if (!_deleteId) return;
  var btn = document.getElementById('confirmDelBtn');
  btn.innerHTML = '<span class="spinner"></span>Deleting...';
  btn.disabled = true;
  try {
    var r = await fetch('/admin/users/delete', { method:'POST', credentials:'include',
      headers:{'Content-Type':'application/json'}, body:JSON.stringify({id:_deleteId}) });
    var d = await r.json();
    if (d.ok) {
      closeConfirm();
      showToast('User deleted.', 'ok');
      await loadAll();
    } else { showToast(d.error || 'Delete failed.', 'err'); }
  } catch(e) { showToast('Error: ' + e.message, 'err'); }
  btn.innerHTML = 'Delete'; btn.disabled = false;
}

function openReset(id) {
  var u = _users.find(function(x){ return x.id === id; });
  if (!u) return;
  _resetId = id;
  document.getElementById('confirmResetMsg').textContent = 'Set a new password for ' + (u.name || u.email) + '.';
  document.getElementById('resetPwInput').value = '';
  document.getElementById('resetErr').style.display = 'none';
  document.getElementById('confirmReset').classList.add('open');
  setTimeout(function(){ document.getElementById('resetPwInput').focus(); }, 100);
}

function closeReset() { document.getElementById('confirmReset').classList.remove('open'); }

async function doReset() {
  var pw = document.getElementById('resetPwInput').value;
  var errEl = document.getElementById('resetErr');
  errEl.style.display = 'none';
  if (pw.length < 8) { errEl.textContent = 'Password must be at least 8 characters.'; errEl.style.display='block'; return; }
  var btn = document.getElementById('confirmResetBtn');
  btn.innerHTML = '<span class="spinner"></span>Resetting...';
  btn.disabled = true;
  try {
    var r = await fetch('/admin/users/update', { method:'POST', credentials:'include',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({id:_resetId, password:pw}) });
    var d = await r.json();
    if (d.ok) { closeReset(); showToast('Password reset successfully.', 'ok'); }
    else { errEl.textContent = d.error || 'Reset failed.'; errEl.style.display='block'; }
  } catch(e) { errEl.textContent = 'Error: ' + e.message; errEl.style.display='block'; }
  btn.innerHTML = 'Reset Password'; btn.disabled = false;
}

// -- 2FA Management -------------------------------------------------
var _2faSecret = null;

async function load2faStatus() {
  var r = await fetch('/auth/2fa/status', {credentials:'include'});
  var d = await r.json();
  var card = document.getElementById('twoFaStatus');
  if (!d.ok) { card.innerHTML = '<p style="color:var(--error)">Failed to load.</p>'; return; }
  if (d.enabled) {
    card.innerHTML = '<p><strong style="color:var(--success)">&#x2705; 2FA Enabled</strong> &mdash; '
      + d.backup_codes_remaining + ' backup codes remaining</p>'
      + '<button class="btn btn-danger" id="btnDis2fa" style="margin-top:12px;">Disable 2FA</button>'
      + '<div id="disableForm" style="display:none;margin-top:16px;">'
      + '<p style="font-size:0.83rem;margin-bottom:8px;color:var(--muted);">Enter your authenticator code:</p>'
      + '<input id="disableCode" type="text" inputmode="numeric" maxlength="8" placeholder="000000"'
      + ' style="width:140px;text-align:center;letter-spacing:6px;padding:10px;border:1px solid var(--border);border-radius:7px;background:rgba(255,255,255,0.04);color:var(--text);outline:none;margin-right:8px;">'
      + '<button class="btn btn-danger btn-sm" id="btnConfDis2fa">Confirm Disable</button>'
      + '<button class="btn btn-ghost btn-sm" id="btnCancDis2fa" style="margin-left:6px;">Cancel</button>'
      + '<div id="disableErr" style="color:var(--error);font-size:0.82rem;margin-top:8px;display:none;"></div></div>';
    document.getElementById('btnDis2fa').onclick = show2faDisable;
    document.getElementById('btnConfDis2fa').onclick = confirm2faDisable;
    document.getElementById('btnCancDis2fa').onclick = function(){ document.getElementById('disableForm').style.display='none'; };
  } else {
    card.innerHTML = '<p><strong style="color:var(--warn)">&#x26A0; 2FA Not Enabled</strong></p>'
      + '<p style="font-size:0.83rem;color:var(--muted);margin:8px 0 16px;">Protect your account with an authenticator app.</p>'
      + '<button class="btn" id="btnSup2fa">Set Up 2FA</button>'
      + '<div id="setupSteps" style="display:none;margin-top:24px;"></div>';
    document.getElementById('btnSup2fa').onclick = start2faSetup;
  }
}

async function start2faSetup() {
  document.getElementById('setupSteps').style.display = '';
  document.getElementById('setupSteps').innerHTML = '<p style="color:var(--muted);font-size:0.85rem;">Loading setup...</p>';
  var r = await fetch('/auth/2fa/setup', {credentials:'include'});
  var d = await r.json();
  if (!d.ok) { document.getElementById('setupSteps').innerHTML = '<p style="color:var(--error)">Error: ' + (d.error||'Failed') + '</p>'; return; }
  _2faSecret = d.secret;
  document.getElementById('setupSteps').innerHTML =
    '<div style="margin-bottom:16px;">'
    + '<p style="font-size:0.85rem;font-weight:600;margin-bottom:10px;">Step 1: Scan this QR code with your authenticator app</p>'
    + '<img src="' + d.qr_url + '" style="border-radius:8px;background:#fff;padding:8px;display:block;margin-bottom:10px;" width="180" height="180">'
    + '<p style="font-size:0.75rem;color:var(--muted);">Or enter this code manually: <code style="background:rgba(255,255,255,0.08);padding:3px 8px;border-radius:4px;font-size:0.78rem;letter-spacing:2px;">' + d.secret + '</code></p>'
    + '</div>'
    + '<div style="margin-bottom:16px;">'
    + '<p style="font-size:0.85rem;font-weight:600;margin-bottom:10px;">Step 2: Enter the 6-digit code to verify</p>'
    + '<input id="setupCode" type="text" inputmode="numeric" maxlength="6" placeholder="000000" '
    + 'style="background:rgba(255,255,255,0.04);border:1px solid var(--border);border-radius:7px;padding:10px 12px;color:var(--text);font-size:1.1rem;width:160px;text-align:center;letter-spacing:6px;outline:none;">'
    + '</div>'
    + '<div id="setupErr" style="color:var(--error);font-size:0.82rem;margin-bottom:10px;display:none;"></div>'
    + '<button class="btn btn-primary" id="btnEnb2fa">Enable 2FA</button>';
    var b=document.getElementById('btnEnb2fa'); if(b) b.onclick=confirm2faEnable;
}

async function confirm2faEnable() {
  var code = document.getElementById('setupCode').value.trim();
  var errEl = document.getElementById('setupErr');
  errEl.style.display = 'none';
  if (!code || code.length < 6) { errEl.textContent='Enter the 6-digit code.'; errEl.style.display='block'; return; }
  var r = await fetch('/auth/2fa/enable', {
    method:'POST', credentials:'include',
    headers:{'Content-Type':'application/json'},
    body: JSON.stringify({secret: _2faSecret, code: code})
  });
  var d = await r.json();
  if (d.ok) {
    // Show backup codes
    var codesHtml = d.backup_codes.map(function(c){ return '<code style="background:rgba(255,255,255,0.08);padding:4px 10px;border-radius:4px;font-family:monospace;font-size:0.85rem;letter-spacing:2px;">'+c+'</code>'; }).join(' ');
    document.getElementById('twoFaStatus').innerHTML =
      '<div style="color:var(--success);font-size:1rem;font-weight:700;margin-bottom:16px;">&#x2705; 2FA enabled successfully!</div>'
      + '<div style="background:rgba(255,152,0,0.08);border:1px solid rgba(255,152,0,0.3);border-radius:8px;padding:16px;margin-bottom:16px;">'
      + '<p style="font-size:0.85rem;font-weight:600;color:var(--warn);margin-bottom:10px;">&#x26A0; Save these backup codes now - they won&#39;t be shown again:</p>'
      + '<div style="display:flex;flex-wrap:wrap;gap:8px;margin-bottom:10px;">' + codesHtml + '</div>'
      + '<p style="font-size:0.75rem;color:var(--muted);">Each code can only be used once.</p></div>'
      + '<button class="btn btn-ghost" id="btn2faDone">Done</button>';
    showToast('2FA enabled!','ok'); setTimeout(function(){var b=document.getElementById('btn2faDone');if(b)b.onclick=load2faStatus;},100);
  } else {
    errEl.textContent = d.error || 'Verification failed.';
    errEl.style.display = 'block';
  }
}

function show2faDisable() {
  document.getElementById('disableForm').style.display = '';
  setTimeout(function(){ document.getElementById('disableCode').focus(); }, 100);
}

async function confirm2faDisable() {
  var code = document.getElementById('disableCode').value.trim();
  var errEl = document.getElementById('disableErr');
  errEl.style.display = 'none';
  if (!code) { errEl.textContent='Enter your authenticator code.'; errEl.style.display='block'; return; }
  var r = await fetch('/auth/2fa/disable', {
    method:'POST', credentials:'include',
    headers:{'Content-Type':'application/json'},
    body: JSON.stringify({code: code})
  });
  var d = await r.json();
  if (d.ok) { showToast('2FA disabled.', 'ok'); load2faStatus(); }
  else { errEl.textContent = d.error || 'Invalid code.'; errEl.style.display='block'; }
}

// -- Role Permissions ----------------------------------------------------------

async function loadPerms() {
  var r = await fetch('/admin/role-permissions', {credentials:'include'});
  var d = await r.json();
  // Build _permsData: default all ON
  _permsData = {};
  MANAGED_ROLES.forEach(function(role) {
    _permsData[role] = {};
    SECTIONS.forEach(function(s) { _permsData[role][s.key] = true; });
  });
  if (d.ok && d.permissions) {
    d.permissions.forEach(function(p) {
      if (_permsData[p.role]) _permsData[p.role][p.section] = p.can_view === 1;
    });
  }
  renderPerms();
  _permsChanged = false;
  document.getElementById('unsavedDot').classList.remove('show');
}

function renderPerms() {
  var rows = '';
  SECTIONS.forEach(function(s) {
    rows += '<tr><td class="section-name"><span class="icon">' + s.icon + '</span>' + s.label + '</td>';
    MANAGED_ROLES.forEach(function(role) {
      var checked = _permsData[role][s.key] !== false;
      rows += '<td><label class="toggle">'
        + '<input type="checkbox" data-role="' + role + '" data-section="' + s.key + '"' + (checked ? ' checked' : '')
        + ' onchange="togglePermEl(this)">'
        + '<span class="toggle-slider"></span></label></td>';
    });
    rows += '</tr>';
  });
  document.getElementById('permsTbody').innerHTML = rows;
}

function togglePermEl(el) { togglePerm(el.dataset.role, el.dataset.section, el.checked); }
function togglePerm(role, section, val) {
  _permsData[role][section] = val;
  _permsChanged = true;
  document.getElementById('unsavedDot').classList.add('show');
}

async function savePerms() {
  var perms = [];
  MANAGED_ROLES.forEach(function(role) {
    SECTIONS.forEach(function(s) {
      perms.push({role:role, section:s.key, can_view:_permsData[role][s.key] ? 1 : 0});
    });
  });
  var btn = document.querySelector('[onclick="savePerms()"]');
  btn.innerHTML = '<span class="spinner"></span>Saving...';
  btn.disabled = true;
  try {
    var r = await fetch('/admin/role-permissions', {
      method:'POST', credentials:'include',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({permissions:perms})
    });
    var d = await r.json();
    if (d.ok) {
      showToast('Permissions saved.', 'ok');
      _permsChanged = false;
      document.getElementById('unsavedDot').classList.remove('show');
    } else { showToast(d.error || 'Save failed.', 'err'); }
  } catch(e) { showToast('Error: ' + e.message, 'err'); }
  btn.innerHTML = '&#x2713; Save Changes'; btn.disabled = false;
}

function showToast(msg, type) {
  var t = document.getElementById('toast');
  t.textContent = msg;
  t.className = 'toast ' + type + ' show';
  setTimeout(function(){ t.className = 'toast ' + type; }, 3000);
}

loadAll();
</script>
</body>
</html>
"""


AUDIT_LOG_PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Audit Log — Rytech SummarAI</title>
<style>
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  body { font-family: 'Segoe UI', Arial, sans-serif; background: #0a0d10; color: #e8eef2; min-height: 100vh; }
  .top-bar { background: #111518; border-bottom: 1px solid #1e2830; padding: 14px 28px; display: flex; align-items: center; justify-content: space-between; }
  .top-bar h1 { font-size: 1.1rem; font-weight: 700; color: #008CBB; }
  .top-bar .meta { font-size: 0.78rem; color: #5a7080; }
  .controls { background: #111518; border-bottom: 1px solid #1e2830; padding: 12px 28px; display: flex; gap: 12px; align-items: center; flex-wrap: wrap; }
  .controls input, .controls select { background: #0a0d10; border: 1px solid #1e2830; border-radius: 7px; padding: 7px 12px; color: #e8eef2; font-size: 0.82rem; outline: none; font-family: inherit; }
  .controls input:focus, .controls select:focus { border-color: #008CBB; }
  .controls input { min-width: 220px; }
  .btn { padding: 7px 16px; border-radius: 7px; border: none; cursor: pointer; font-size: 0.82rem; font-weight: 600; font-family: inherit; background: #008CBB; color: #fff; }
  .btn:hover { opacity: 0.85; }
  .btn-sec { background: transparent; color: #5a7080; border: 1px solid #1e2830; }
  .btn-sec:hover { background: #1e2830; color: #e8eef2; }
  .stat-row { display: flex; gap: 16px; padding: 14px 28px; flex-wrap: wrap; }
  .stat-card { background: #111518; border: 1px solid #1e2830; border-radius: 10px; padding: 12px 20px; min-width: 140px; }
  .stat-card .val { font-size: 1.6rem; font-weight: 700; color: #008CBB; }
  .stat-card .lbl { font-size: 0.72rem; color: #5a7080; margin-top: 2px; }
  .table-wrap { padding: 0 28px 28px; overflow-x: auto; }
  table { width: 100%; border-collapse: collapse; font-size: 0.82rem; margin-top: 16px; }
  thead th { background: #141a1f; color: #5a7080; font-weight: 600; padding: 10px 14px; text-align: left; border-bottom: 2px solid #1e2830; white-space: nowrap; }
  tbody tr { border-bottom: 1px solid #1a2030; }
  tbody tr:hover { background: rgba(0,140,187,0.05); }
  tbody td { padding: 9px 14px; vertical-align: top; }
  .action-badge { display: inline-block; padding: 2px 8px; border-radius: 4px; font-size: 0.72rem; font-weight: 600; }
  .action-login    { background: rgba(76,175,80,.15);  color: #4caf50; }
  .action-logout   { background: rgba(90,112,128,.15); color: #5a7080; }
  .action-failed   { background: rgba(240,106,106,.15); color: #f06a6a; }
  .action-admin    { background: rgba(255,193,7,.15);  color: #ffc107; }
  .action-password { background: rgba(0,140,187,.15);  color: #008CBB; }
  .action-default  { background: rgba(90,112,128,.1);  color: #5a7080; }
  .ip { font-family: monospace; font-size: 0.75rem; color: #5a7080; }
  .ts { font-size: 0.75rem; color: #5a7080; white-space: nowrap; }
  .user-name { font-weight: 600; }
  .user-email { font-size: 0.72rem; color: #5a7080; }
  .detail { color: #a0b4c0; max-width: 300px; word-break: break-word; }
  .empty, .loading { text-align: center; padding: 60px; color: #5a7080; }
  .page-info { font-size: 0.78rem; color: #5a7080; margin-left: auto; }
</style>
</head>
<body>
<div class="top-bar">
  <h1>&#128269; Audit Log &#8212; Rytech SummarAI</h1>
  <span class="meta" id="loadedAt"></span>
</div>
<div class="controls">
  <input type="text" id="filterInput" placeholder="Filter by user, action, IP, or detail&hellip;" oninput="applyFilter()">
  <select id="actionFilter" onchange="applyFilter()">
    <option value="">All actions</option>
    <option value="login">Logins</option>
    <option value="logout">Logouts</option>
    <option value="failed">Failed attempts</option>
    <option value="password">Password changes</option>
    <option value="admin">Admin actions</option>
  </select>
  <select id="limitSel" onchange="loadLog()">
    <option value="100">Last 100</option>
    <option value="250">Last 250</option>
    <option value="500">Last 500</option>
    <option value="1000">Last 1000</option>
  </select>
  <button class="btn" onclick="loadLog()">&#8635; Refresh</button>
  <button class="btn btn-sec" onclick="exportCSV()">&#11015; Export CSV</button>
  <span class="page-info" id="pageInfo"></span>
</div>
<div class="stat-row" id="statRow"></div>
<div class="table-wrap">
  <div class="loading" id="loadingMsg">Loading audit log&hellip;</div>
  <table id="auditTable" style="display:none">
    <thead><tr>
      <th>#</th><th>When</th><th>User</th><th>Action</th><th>Detail</th><th>IP Address</th>
    </tr></thead>
    <tbody id="auditBody"></tbody>
  </table>
  <div class="empty" id="emptyMsg" style="display:none">No matching entries.</div>
</div>
<script>
let allRows = [];
function actionClass(action) {
  if (!action) return 'action-default';
  const a = action.toLowerCase();
  if (a.includes('login') && !a.includes('fail')) return 'action-login';
  if (a.includes('logout')) return 'action-logout';
  if (a.includes('fail') || a.includes('locked') || a.includes('invalid')) return 'action-failed';
  if (a.includes('password') || a.includes('2fa') || a.includes('totp')) return 'action-password';
  if (a.includes('admin') || a.includes('create') || a.includes('delete') || a.includes('update')) return 'action-admin';
  return 'action-default';
}
function fmtDate(s) {
  if (!s) return '&mdash;';
  const d = new Date(s.replace(' ','T') + 'Z');
  return d.toLocaleString('en-GB',{day:'2-digit',month:'short',year:'numeric',hour:'2-digit',minute:'2-digit',second:'2-digit'});
}
async function loadLog() {
  const limit = document.getElementById('limitSel').value;
  document.getElementById('loadingMsg').style.display = 'block';
  document.getElementById('loadingMsg').textContent = 'Loading audit log\u2026';
  document.getElementById('auditTable').style.display = 'none';
  document.getElementById('emptyMsg').style.display = 'none';
  try {
    const headers = {'Content-Type': 'application/json'};
    if (typeof _SESSION_TOKEN !== 'undefined' && _SESSION_TOKEN) {
      headers['Authorization'] = 'Bearer ' + _SESSION_TOKEN;
    }
    const r = await fetch('/admin/audit?limit=' + limit, {credentials:'include', headers});
    if (!r.ok) {
      document.getElementById('loadingMsg').textContent = 'HTTP ' + r.status + ': ' + (r.statusText||'error') + ' — try refreshing or logging in again.';
      return;
    }
    const d = await r.json();
    if (!d.ok) {
      document.getElementById('loadingMsg').textContent = 'Server error: ' + (d.error || 'unknown');
      return;
    }
    allRows = d.log || [];
    document.getElementById('loadedAt').textContent = 'Loaded ' + allRows.length + ' entries at ' + new Date().toLocaleTimeString('en-GB');
    renderStats();
    applyFilter();
  } catch(e) {
    document.getElementById('loadingMsg').textContent = 'Network error: ' + e.message;
  }
}
function renderStats() {
  const logins    = allRows.filter(r => r.action && r.action.toLowerCase().includes('login') && !r.action.toLowerCase().includes('fail')).length;
  const failures  = allRows.filter(r => r.action && (r.action.toLowerCase().includes('fail') || r.action.toLowerCase().includes('invalid'))).length;
  const pwChanges = allRows.filter(r => r.action && r.action.toLowerCase().includes('password')).length;
  const adminActs = allRows.filter(r => r.action && (r.action.toLowerCase().includes('admin') || r.action.toLowerCase().includes('create') || r.action.toLowerCase().includes('delete'))).length;
  const uniqueIPs = new Set(allRows.map(r => r.ip_address).filter(Boolean)).size;
  document.getElementById('statRow').innerHTML = [
    {val: allRows.length, lbl: 'Total events'},
    {val: logins,         lbl: 'Successful logins'},
    {val: failures,       lbl: 'Failed attempts'},
    {val: pwChanges,      lbl: 'Password changes'},
    {val: adminActs,      lbl: 'Admin actions'},
    {val: uniqueIPs,      lbl: 'Unique IPs'},
  ].map(s => '<div class="stat-card"><div class="val">' + s.val + '</div><div class="lbl">' + s.lbl + '</div></div>').join('');
}
function applyFilter() {
  const q  = document.getElementById('filterInput').value.toLowerCase();
  const af = document.getElementById('actionFilter').value.toLowerCase();
  const filtered = allRows.filter(r => {
    const al = (r.action||'').toLowerCase();
    if (af) {
      if (af === 'failed' && !al.includes('fail') && !al.includes('invalid') && !al.includes('locked')) return false;
      else if (af !== 'failed' && !al.includes(af)) return false;
    }
    if (!q) return true;
    return (r.user_name||'').toLowerCase().includes(q)||(r.user_email||'').toLowerCase().includes(q)||al.includes(q)||(r.detail||'').toLowerCase().includes(q)||(r.ip_address||'').toLowerCase().includes(q);
  });
  renderTable(filtered);
}
function renderTable(rows) {
  document.getElementById('loadingMsg').style.display = 'none';
  document.getElementById('pageInfo').textContent = rows.length + ' of ' + allRows.length + ' entries';
  if (!rows.length) {
    document.getElementById('auditTable').style.display = 'none';
    document.getElementById('emptyMsg').style.display = 'block';
    return;
  }
  document.getElementById('emptyMsg').style.display = 'none';
  document.getElementById('auditTable').style.display = 'table';
  document.getElementById('auditBody').innerHTML = rows.map(r =>
    '<tr>' +
    '<td class="ts">' + r.id + '</td>' +
    '<td class="ts">' + fmtDate(r.created_at) + '</td>' +
    '<td><div class="user-name">' + (r.user_name || '<span style="color:#5a7080">System</span>') + '</div><div class="user-email">' + (r.user_email||'') + '</div></td>' +
    '<td><span class="action-badge ' + actionClass(r.action) + '">' + (r.action||'&mdash;') + '</span></td>' +
    '<td class="detail">' + (r.detail ? String(r.detail).replace(/</g,'&lt;') : '&mdash;') + '</td>' +
    '<td class="ip">' + (r.ip_address||'&mdash;') + '</td>' +
    '</tr>'
  ).join('');
}
function exportCSV() {
  const q  = document.getElementById('filterInput').value.toLowerCase();
  const af = document.getElementById('actionFilter').value.toLowerCase();
  const rows = allRows.filter(r => {
    const al = (r.action||'').toLowerCase();
    if (af) { if (af==='failed' && !al.includes('fail') && !al.includes('invalid')) return false; else if (af!=='failed' && !al.includes(af)) return false; }
    if (!q) return true;
    return (r.user_name||'').toLowerCase().includes(q)||(r.user_email||'').toLowerCase().includes(q)||al.includes(q)||(r.detail||'').toLowerCase().includes(q)||(r.ip_address||'').toLowerCase().includes(q);
  });
  const esc = v => '"' + String(v||'').replace(/"/g,'""') + '"';
  const csv = ['ID,Timestamp,User Name,User Email,Action,Detail,IP Address',
    ...rows.map(r => [r.id,r.created_at,r.user_name||'',r.user_email||'',r.action||'',r.detail||'',r.ip_address||''].map(esc).join(','))
  ].join('\n');
  const a = document.createElement('a');
  a.href = 'data:text/csv;charset=utf-8,' + encodeURIComponent(csv);
  a.download = 'rytech_audit_' + new Date().toISOString().slice(0,10) + '.csv';
  a.click();
}
loadLog();
</script>
</body>
</html>"""



class RytechHandler(BaseHTTPRequestHandler):
    html_content = None
    config       = {}

    def log_message(self, format, *args):
        pass  # suppress default access log

    def do_OPTIONS(self):
        self.send_response(204)
        _send_cors(self)
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers',
            'Content-Type, Authorization, Xero-tenant-id, orgId, '
            'X-Action1-Token, X-Datto-Token, X-Datto-Url, X-Monzo-Token')
        self.send_header('Access-Control-Allow-Credentials', 'true')
        self.end_headers()

    # ── GET ───────────────────────────────────────────────────────
    def do_GET(self):
        global _monzo_pending, _monzo_sessions
        parsed = urllib.parse.urlparse(self.path)
        path   = parsed.path
        params = urllib.parse.parse_qs(parsed.query)

        # ── Login page (unauthenticated) ──────────────────────────
        if path == '/login':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(LOGIN_PAGE)))
            self.send_header('Cache-Control', 'no-cache')
            self.end_headers()
            self.wfile.write(LOGIN_PAGE)
            return

        # ── Auth: whoami ──────────────────────────────────────────
        if path == '/auth/me':
            user = require_auth(self)
            if not user: return
            perms = get_permissions(user['id'], user['role'])
            conn = get_db()
            row = conn.execute("SELECT avatar FROM users WHERE id=?", (user['id'],)).fetchone()
            avatar = row['avatar'] if row and row['avatar'] else None
            json_response(self, {
                'ok': True, 'user': {
                    'id':    user['id'],
                    'name':  user['name'],
                    'email': user['email'],
                    'role':  user['role'],
                    'avatar': avatar,
                    'permissions': perms,
                }
            })
            return

        if path == '/auth/csrf':
            user = require_auth(self)
            if not user: return
            token = csrf_issue(user['id'])
            json_response(self, {'csrf_token': token})
            return
            user = require_auth(self)
            if not user: return
            token = csrf_issue(user['id'])
            json_response(self, {'csrf_token': token})
            return

        # ── Auth: logout ──────────────────────────────────────────
        if path == '/auth/logout':
            token = auth_get_token(self)
            if token:
                user = verify_session(token)
                if user:
                    db_audit(user['id'], 'logout', ip=get_client_ip(self))
                auth_logout(token)
            self.send_response(302)
            self.send_header('Set-Cookie', 'ry_session=; path=/; max-age=0; SameSite=Lax; Secure')
            self.send_header('Location', '/login')
            self.end_headers()
            return

        # ── Protected: main app ───────────────────────────────────
        if path in ('/', '/index.html', '/rytech-meeting-manager.html'):
            user = verify_session(auth_get_token(self))
            if not user:
                self.send_response(302)
                self.send_header('Location', '/login')
                self.end_headers()
                return
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(RytechHandler.html_content)))
            self.send_header('Cache-Control', 'no-cache')
            _sec_headers(self)
            self.end_headers()
            self.wfile.write(RytechHandler.html_content)
            return

        # ── Protected: config ─────────────────────────────────────
        if path == '/groq/key':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c    = conn.cursor()
            c.execute('SELECT key_enc FROM groq_config WHERE id=1')
            row = c.fetchone()
            conn.close()
            has_key = bool(row and row['key_enc'])
            json_response(self, {'ok': True, 'has_key': has_key})
            return

        if path == '/config':
            user = require_auth(self)
            if not user: return
            json_response(self, {
                'api_key':     RytechHandler.config.get('api_key', ''),
                'totp_secret': RytechHandler.config.get('totp_secret', '')
            })
            return

        # ── Protected: load data ──────────────────────────────────
        if path == '/load':
            user = require_auth(self)
            if not user: return
            json_response(self, {'ok': True, 'meetings': load_meetings()})
            return

        if path == '/load_v2':
            user = require_auth(self)
            if not user: return
            data = load_v2_data()
            json_response(self, {
                'ok':        True,
                'customers': data.get('customers', []),
                'suppliers': data.get('suppliers', []),
                'contracts': data.get('contracts', []),
                'taskLists': data.get('taskLists', []),
                'shortcuts': data.get('shortcuts', []),
                'navLayout': data.get('navLayout', None),
            })
            return

                # ── 2FA: get setup info ───────────────────────────────────
        if path == '/auth/2fa/setup':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c    = conn.cursor()
            c.execute('SELECT totp_enabled, totp_secret FROM users WHERE id=?', (user['id'],))
            row = c.fetchone()
            conn.close()
            if row and row['totp_enabled']:
                json_response(self, {'ok': True, 'enabled': True})
                return
            # Generate new secret for setup
            secret = totp_generate_secret()
            uri    = totp_provisioning_uri(secret, user['email'])
            # Generate QR code as SVG (simple URL approach)
            qr_url = f'https://api.qrserver.com/v1/create-qr-code/?size=200x200&data={urllib.parse.quote(uri)}'
            json_response(self, {
                'ok':     True,
                'enabled': False,
                'secret': secret,
                'uri':    uri,
                'qr_url': qr_url,
            })
            return

        # ── 2FA: get current status ───────────────────────────────
        if path == '/auth/2fa/status':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c    = conn.cursor()
            c.execute('SELECT totp_enabled, totp_backup_codes FROM users WHERE id=?', (user['id'],))
            row = c.fetchone()
            conn.close()
            backup_count = 0
            if row and row['totp_backup_codes']:
                try: backup_count = len(json.loads(row['totp_backup_codes']))
                except: pass
            json_response(self, {
                'ok':      True,
                'enabled': bool(row and row['totp_enabled']),
                'backup_codes_remaining': backup_count,
            })
            return

        # ── Admin: list users ─────────────────────────────────────
        if path == '/admin/users':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            conn = get_db()
            c    = conn.cursor()
            c.execute('SELECT id,email,name,role,active,created_at,last_login,totp_enabled FROM users ORDER BY id')
            rows = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'users': rows})
            return

        # ── Admin: get role permissions ───────────────────────────
        if path == '/admin/role-permissions':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            conn = get_db()
            c    = conn.cursor()
            c.execute('SELECT role, section, can_view FROM role_permissions')
            rows = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'permissions': rows})
            return

        # ── Admin: audit log ──────────────────────────────────────
        if path == '/admin/audit':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            limit = int(params.get('limit', ['100'])[0])
            conn  = get_db()
            c     = conn.cursor()
            c.execute("""
                SELECT a.id, a.action, a.detail, a.ip_address, a.created_at,
                       u.name as user_name, u.email as user_email
                FROM audit_log a
                LEFT JOIN users u ON a.user_id = u.id
                ORDER BY a.id DESC LIMIT ?
            """, (limit,))
            rows = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'log': rows})
            return

        if path == '/admin/credentials':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            # Return which keys are set (never the values)
            status = cred_load_all()
            KNOWN_KEYS = [
                'xero_client_id', 'xero_client_secret',
                'zoho_client_id', 'zoho_client_secret',
                'a1_client_id', 'a1_client_secret',
                'datto_api_key', 'datto_api_secret',
                'groq_api_key',
            ]
            result = {k: status.get(k, {'set': False}) for k in KNOWN_KEYS}
            json_response(self, {'ok': True, 'credentials': result})
            return

        # ── Notifications ─────────────────────────────────────────
        if path == '/notifications':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            rows = conn.execute(
                'SELECT * FROM notifications WHERE user_id=? ORDER BY created_at DESC LIMIT 50',
                (user['id'],)
            ).fetchall()
            unread = conn.execute(
                'SELECT COUNT(*) as n FROM notifications WHERE user_id=? AND read_at IS NULL',
                (user['id'],)
            ).fetchone()['n']
            conn.close()
            json_response(self, {'ok': True, 'notifications': [dict(r) for r in rows], 'unread': unread})
            return

        if path == '/notifications/unread-count':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            n = conn.execute(
                'SELECT COUNT(*) as n FROM notifications WHERE user_id=? AND read_at IS NULL',
                (user['id'],)
            ).fetchone()['n']
            conn.close()
            json_response(self, {'ok': True, 'unread': n})
            return

        # ── Ticket events (timeline) ──────────────────────────────
        if path.startswith('/ticket/events/'):
            user = require_auth(self)
            if not user: return
            ticket_id = path[len('/ticket/events/'):]
            conn = get_db()
            rows = conn.execute(
                'SELECT * FROM ticket_events WHERE ticket_id=? ORDER BY created_at ASC',
                (ticket_id,)
            ).fetchall()
            conn.close()
            json_response(self, {'ok': True, 'events': [dict(r) for r in rows]})
            return

        # ── Client activity feed ──────────────────────────────────
        if path.startswith('/client/activity/'):
            user = require_auth(self)
            if not user: return
            client_id = path[len('/client/activity/'):]
            conn = get_db()
            rows = conn.execute(
                'SELECT * FROM client_activity WHERE client_id=? ORDER BY created_at DESC LIMIT 100',
                (client_id,)
            ).fetchall()
            conn.close()
            json_response(self, {'ok': True, 'activity': [dict(r) for r in rows]})
            return

        # ── Widget prefs ──────────────────────────────────────────
        if path == '/widget/prefs':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            row = conn.execute(
                'SELECT prefs_json FROM user_widget_prefs WHERE user_id=?', (user['id'],)
            ).fetchone()
            conn.close()
            prefs = json.loads(row['prefs_json']) if row else {}
            json_response(self, {'ok': True, 'prefs': prefs})
            return

        # ── Admin: per-user section permissions ───────────────────
        if path.startswith('/admin/user-permissions/'):
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            target_id = int(path.split('/')[-1])
            conn = get_db()
            rows = conn.execute(
                'SELECT section, can_view FROM permissions WHERE user_id=?', (target_id,)
            ).fetchall()
            conn.close()
            json_response(self, {'ok': True, 'permissions': [dict(r) for r in rows]})
            return


        if path == '/xero-callback':
            code  = params.get('code',  [''])[0]
            state = params.get('state', [''])[0]
            error = params.get('error', [''])[0]
            html_cb = (
                '<!DOCTYPE html><html><head><title>Xero Auth</title></head><body>'
                '<script>'
                '(function(){'
                'var p={type:"xero_callback",code:"' + code + '",state:"' + state + '",error:"' + error + '"};'
                'if(window.opener){'
                '  window.opener.postMessage(p,window.location.origin);'
                '  setTimeout(function(){window.close();},800);'
                '} else {'
                # Mobile: no opener -- redirect back to the app with code in query string
                '  var qs="?xero_code="+encodeURIComponent("' + code + '")+"&xero_state="+encodeURIComponent("' + state + '")'
                '      +("' + error + '"?"&xero_error="+encodeURIComponent("' + error + '"):"");'
                '  window.location.replace("/"+qs);'
                '}'
                '})();'
                '</script><p>Authorising&hellip;</p></body></html>'
            ).encode()
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(html_cb)))
            _send_cors(self)
            self.end_headers()
            self.wfile.write(html_cb)
            return

        if path == '/zoho-callback':
            code  = params.get('code',  [''])[0]
            state = params.get('state', [''])[0]
            error = params.get('error', [''])[0]
            html_cb = (
                '<!DOCTYPE html><html><head><title>Zoho Auth</title></head><body>'
                '<script>'
                '(function(){'
                'var p={type:"zoho_callback",code:"' + code + '",state:"' + state + '",error:"' + error + '"};'
                'if(window.opener){'
                '  window.opener.postMessage(p,window.location.origin);'
                '  setTimeout(function(){window.close();},800);'
                '} else {'
                '  var qs="?zoho_code="+encodeURIComponent("' + code + '")+"&zoho_state="+encodeURIComponent("' + state + '")'
                '      +("' + error + '"?"&zoho_error="+encodeURIComponent("' + error + '"):"");'
                '  window.location.replace("/"+qs);'
                '}'
                '})();'
                '</script><p>Authorising&hellip;</p></body></html>'
            ).encode()
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(html_cb)))
            _send_cors(self)
            self.end_headers()
            self.wfile.write(html_cb)
            return

        if path.startswith('/oauth_callback'):
            page = b"""<!DOCTYPE html>
<html><head><meta charset="UTF-8">
<script>
(function() {
  var params = new URLSearchParams(window.location.search);
  var payload = { type: 'oauth_callback' };
  if (params.get('code'))  { payload.code=params.get('code'); payload.state=params.get('state'); }
  if (params.get('error')) { payload.error=params.get('error'); payload.error_description=params.get('error_description')||''; }
  if (window.opener) { window.opener.postMessage(payload, window.location.origin); }
  window.close();
})();
</script>
</head><body style="background:#0a0d10;color:#e8eef2;font-family:sans-serif">
<p>Signing in&hellip;</p></body></html>"""
            self.send_response(200)
            self.send_header('Content-Type', 'text/html')
            self.send_header('Content-Length', str(len(page)))
            self.send_header('Cache-Control', 'no-cache')
            self.end_headers()
            self.wfile.write(page)
            return

        # ── Notes API ────────────────────────────────────────────
        if path == '/notes':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            c.execute('SELECT * FROM notes WHERE owner_id=? ORDER BY pinned DESC, updated_at DESC', (user['id'],))
            rows = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'notes': rows})
            return

        # ── Workflow status + log ────────────────────────────────────
        if path == '/workflows/status':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            c.execute("SELECT * FROM workflow_config")
            configs = {row['workflow_id']: dict(row) for row in c.fetchall()}
            conn.close()
            json_response(self, {'ok': True, 'configs': configs})
            return

        if path == '/workflows/log':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            c.execute("SELECT * FROM workflow_log ORDER BY sent_at DESC LIMIT 200")
            rows = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'log': rows})
            return

        if path == '/smtp/config':
            user = require_auth(self)
            if not user: return
            cfg = smtp_load()
            if cfg:
                cfg.pop('password', None)
                cfg.pop('password_enc', None)
            json_response(self, {'ok': True, 'config': cfg or {}})
            return

        # ── OAuth token persistence ───────────────────────────────
        if path == '/oauth/tokens':
            user = require_auth(self)
            if not user: return
            # Load tokens for each provider; auto-refresh if expired
            result = {}
            refresh_fns = {
                'xero':  oauth_refresh_xero,
                'zoho':  oauth_refresh_zoho,
                'monzo': oauth_refresh_monzo,
            }
            for provider in _ALLOWED_PROVIDERS:
                t = oauth_load(user['id'], provider)
                if not t:
                    continue
                if _token_expired(t):
                    refreshed = refresh_fns[provider](user['id'], t)
                    if refreshed:
                        t = refreshed
                        logging.info(f'Server auto-refreshed {provider} token for user {user["id"]}')
                    else:
                        logging.warning(f'Server could not refresh {provider} token for user {user["id"]}')
                result[provider] = t
            json_response(self, {'ok': True, 'tokens': result})
            return

        # ── Assigned Tasks API ────────────────────────────────────
        if path == '/tasks/assigned':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            # Tasks assigned TO me (inbox)
            c.execute('''SELECT t.*, u.name as creator_name, u.email as creator_email
                         FROM assigned_tasks t JOIN users u ON t.creator_id=u.id
                         WHERE t.assignee_id=? AND t.archived=0 ORDER BY
                         CASE t.priority WHEN 'high' THEN 1 WHEN 'medium' THEN 2 ELSE 3 END,
                         t.due_date ASC NULLS LAST, t.created_at DESC''', (user['id'],))
            inbox = [dict(r) for r in c.fetchall()]
            # Tasks I assigned to others (outbox)
            c.execute('''SELECT t.*, u.name as assignee_name, u.email as assignee_email
                         FROM assigned_tasks t JOIN users u ON t.assignee_id=u.id
                         WHERE t.creator_id=? AND t.assignee_id!=?
                         ORDER BY t.created_at DESC''', (user['id'], user['id']))
            outbox = [dict(r) for r in c.fetchall()]
            # Attach subtasks + notes to all tasks
            all_ids = [t['id'] for t in inbox + outbox]
            subtasks_map, notes_map = {}, {}
            if all_ids:
                placeholders = ','.join('?' * len(all_ids))
                c.execute(f'SELECT * FROM subtasks WHERE task_id IN ({placeholders}) ORDER BY id', all_ids)
                for s in c.fetchall():
                    subtasks_map.setdefault(s['task_id'], []).append(dict(s))
                c.execute(f'''SELECT tn.*, u.name as author_name FROM task_notes tn
                              JOIN users u ON tn.author_id=u.id
                              WHERE tn.task_id IN ({placeholders}) ORDER BY tn.created_at''', all_ids)
                for n in c.fetchall():
                    notes_map.setdefault(n['task_id'], []).append(dict(n))
            for t in inbox + outbox:
                t['subtasks'] = subtasks_map.get(t['id'], [])
                t['notes']    = notes_map.get(t['id'], [])
            conn.close()
            json_response(self, {'ok': True, 'inbox': inbox, 'outbox': outbox})
            return

        if path == '/tasks/users':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            c.execute('SELECT id, name, email, role FROM users WHERE active=1 ORDER BY name')
            rows = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'users': rows})
            return

        if path == '/tasks/archived':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            # Archived tasks assigned TO me
            c.execute('''SELECT t.*, u.name as creator_name, u.email as creator_email
                         FROM assigned_tasks t JOIN users u ON t.creator_id=u.id
                         WHERE t.assignee_id=? AND t.archived=1
                         ORDER BY t.updated_at DESC''', (user['id'],))
            inbox = [dict(r) for r in c.fetchall()]
            # Archived tasks I assigned to others
            c.execute('''SELECT t.*, u.name as assignee_name, u.email as assignee_email
                         FROM assigned_tasks t JOIN users u ON t.assignee_id=u.id
                         WHERE t.creator_id=? AND t.assignee_id!=? AND t.archived=1
                         ORDER BY t.updated_at DESC''', (user['id'], user['id']))
            outbox = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'inbox': inbox, 'outbox': outbox})
            return

        # ── Protected proxy routes ────────────────────────────────
        user = require_auth(self)
        if not user: return

        if path.startswith('/proxy/xero/raw'):
            raw_path = params.get('q', ['/'])[0]
            url = 'https://api.xero.com/api.xro/2.0' + raw_path
            self._proxy_get(url, extra_headers={
                'Authorization':  self.headers.get('Authorization', ''),
                'Xero-tenant-id': self.headers.get('Xero-tenant-id', ''),
            })
        elif path.startswith('/proxy/xero/connections'):
            self._proxy_get('https://api.xero.com/connections',
                            extra_headers={'Authorization': self.headers.get('Authorization', '')})
        elif path.startswith('/proxy/zoho/organizations'):
            self._proxy_get('https://desk.zoho.eu/api/v1/organizations',
                            extra_headers={'Authorization': self.headers.get('Authorization', '')})
        elif path.startswith('/proxy/xero/api'):
            api_path = params.get('path', ['/'])[0]
            extra_qs = {k: v[0] for k, v in params.items() if k != 'path'}
            url = 'https://api.xero.com/api.xro/2.0' + api_path
            if extra_qs:
                url += '?' + urllib.parse.urlencode(extra_qs, quote_via=urllib.parse.quote)
            self._proxy_get(url, extra_headers={
                'Authorization':  self.headers.get('Authorization', ''),
                'Xero-tenant-id': self.headers.get('Xero-tenant-id', ''),
            })
        elif path.startswith('/proxy/zoho/api'):
            api_path = params.get('path', ['/'])[0]
            extra_qs = {k: v[0] for k, v in params.items() if k != 'path'}
            url = 'https://desk.zoho.eu/api/v1' + api_path
            if extra_qs:
                url += '?' + urllib.parse.urlencode(extra_qs)
            self._proxy_get(url, extra_headers={
                'Authorization': self.headers.get('Authorization', ''),
                'orgId':         self.headers.get('orgId', ''),
            })
        elif path.startswith('/proxy/action1/'):
            try:
                token    = self.headers.get('X-Action1-Token', '')
                api_path = path.replace('/proxy/action1/', '')
                qs       = parsed.query
                url      = f'https://app.eu.action1.com/api/3.0/{api_path}'
                if qs: url += '?' + qs
                req = urllib.request.Request(url, headers={
                    'Authorization': f'Bearer {token}',
                    'Content-Type':  'application/json'
                })
                with urllib.request.urlopen(req, timeout=20) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body)
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif path.startswith('/proxy/datto/'):
            try:
                datto_url = self.headers.get('X-Datto-Url', '')
                api_token = self.headers.get('X-Datto-Token', '')
                api_path  = path.replace('/proxy/datto', '')
                qs        = parsed.query
                # Datto API requires /api prefix: https://region-api.centrastage.net/api/v2/...
                url       = f'{datto_url}/api{api_path}'
                if qs: url += '?' + qs
                req = urllib.request.Request(url, headers={
                    'Authorization': f'Bearer {api_token}',
                    'Content-Type':  'application/json'
                })
                with urllib.request.urlopen(req, timeout=20) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body)
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif path == '/monzo-callback':
            import json as _json, time as _time
            code           = params.get('code',  [''])[0]
            state          = params.get('state', [''])[0]
            error          = params.get('error', [''])[0]
            token_data     = None
            exchange_error = error or None
            if code and state and not error:
                session = _monzo_sessions.pop(state, None)
                if session:
                    try:
                        token_body = urllib.parse.urlencode({
                            'grant_type':    'authorization_code',
                            'client_id':     session['client_id'],
                            'client_secret': session['client_secret'],
                            'redirect_uri':  session['redirect_uri'],
                            'code':          code,
                        }).encode()
                        req = urllib.request.Request(
                            'https://api.monzo.com/oauth2/token',
                            data=token_body,
                            headers={'Content-Type': 'application/x-www-form-urlencoded'}
                        )
                        with urllib.request.urlopen(req, timeout=20) as resp:
                            token_data = _json.loads(resp.read())
                    except urllib.error.HTTPError as e:
                        exchange_error = e.read().decode(errors='replace')
                    except Exception as e:
                        exchange_error = str(e)
                else:
                    exchange_error = 'Session expired - please try again'
            _monzo_pending[state] = {
                'tokens': token_data,
                'error':  exchange_error,
                'ts':     time.time()
            }
            dest = '/?monzo_state=' + urllib.parse.quote(state)
            self.send_response(302)
            self.send_header('Location', dest)
            _send_cors(self)
            self.end_headers()

        elif path == '/monzo-result':
            state  = params.get('state', [''])[0]
            result = _monzo_pending.pop(state, None)
            if result:
                json_response(self, {'ready': True, 'tokens': result['tokens'], 'error': result['error']})
            else:
                json_response(self, {'ready': False, 'error': 'No result - session may have expired'})

        elif path.startswith('/proxy/monzo/api'):
            try:
                token    = self.headers.get('X-Monzo-Token', '')
                api_path = path.replace('/proxy/monzo/api', '')
                qs_str   = parsed.query
                url      = f'https://api.monzo.com{api_path}'
                if qs_str: url += '?' + qs_str
                req = urllib.request.Request(url, headers={
                    'Authorization': f'Bearer {token}',
                    'Content-Type':  'application/json',
                })
                with urllib.request.urlopen(req, timeout=30) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body if resp_body else b'{}')
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body or b'{}')
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif path == '/diagnostic':
            json_response(self, {
                'server': 'Rytech SummarAI v6.5.0 VPS',
                'python': sys.version,
                'user':   user['email'],
                'role':   user['role'],
            })

        elif path == '/admin/users-page':
            user = verify_session(auth_get_token(self))
            if not user:
                self.send_response(302)
                self.send_header('Location', '/login')
                self.end_headers()
                return
            if user['role'] not in ('superadmin', 'admin'):
                self.send_response(403)
                self.end_headers()
                self.wfile.write(b'Forbidden')
                return
            try:
                _umpage = USER_MGMT_PAGE.encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(_umpage)))
                self.send_header('Cache-Control', 'no-cache')
                _send_cors(self)
                _sec_headers(self)
                self.end_headers()
                self.wfile.write(_umpage)
            except Exception as e:
                try:
                    self.send_response(500)
                    self.end_headers()
                    self.wfile.write(b'Internal Server Error')
                except Exception:
                    pass
                logging.error(f'[users-page] {e}')
            return

        elif path == '/admin/audit-page':
            user = verify_session(auth_get_token(self))
            if not user:
                self.send_response(302)
                self.send_header('Location', '/login')
                self.end_headers()
                return
            if user['role'] not in ('superadmin', 'admin'):
                self.send_response(403)
                self.end_headers()
                self.wfile.write(b'Forbidden')
                return
            try:
                # Inject the session token so the page can use Bearer auth
                # (cookie may not be sent on HTTPS if Secure flag not yet set)
                session_tok = auth_get_token(self) or ''
                _aupage = AUDIT_LOG_PAGE.replace(
                    'let allRows = [];',
                    f'let allRows = []; const _SESSION_TOKEN = {json.dumps(session_tok)};'
                ).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(_aupage)))
                self.send_header('Cache-Control', 'no-cache')
                _send_cors(self)
                _sec_headers(self)
                self.end_headers()
                self.wfile.write(_aupage)
            except Exception as e:
                try:
                    self.send_response(500)
                    self.end_headers()
                    self.wfile.write(b'Internal Server Error')
                except Exception:
                    pass
                logging.error(f'[audit-page] {e}')
            return

        elif path == '/local/get-template':
            user = require_auth(self)
            if not user: return
            try:
                import urllib.parse as _up2
                qs     = _up2.parse_qs(_up2.urlparse(self.path).query)
                fname  = qs.get('name', [''])[0].strip()
                # Sanitise -- no path separators
                fname  = os.path.basename(fname)
                fpath  = os.path.join(TEMPLATES_SRC, fname)
                if not fname or not os.path.isfile(fpath):
                    self.send_response(404)
                    self.end_headers()
                    self.wfile.write(b'Not found')
                    return
                mime, _ = mimetypes.guess_type(fpath)
                mime    = mime or 'application/octet-stream'
                with open(fpath, 'rb') as fh:
                    data = fh.read()
                self.send_response(200)
                self.send_header('Content-Type', mime)
                self.send_header('Content-Length', str(len(data)))
                self.send_header('Content-Disposition', 'attachment; filename="' + fname + '"')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(data)
            except Exception as e:
                self.send_response(500)
                self.end_headers()
                self.wfile.write(str(e).encode())

        elif path == '/local/list-templates':
            user = require_auth(self)
            if not user: return
            try:
                if not os.path.isdir(TEMPLATES_SRC):
                    json_response(self, {'ok': True, 'files': [], 'note': 'Templates dir not found: ' + TEMPLATES_SRC})
                    return
                files = sorted(
                    f for f in os.listdir(TEMPLATES_SRC)
                    if os.path.isfile(os.path.join(TEMPLATES_SRC, f))
                )
                json_response(self, {'ok': True, 'files': files})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)

        else:
            self.send_response(404)
            _send_cors(self)
            self.end_headers()
            self.wfile.write(b'Not found')

    # ── POST ──────────────────────────────────────────────────────
    def do_POST(self):
        length = int(self.headers.get('Content-Length', 0))
        body   = self.rfile.read(length) if length else b'{}'

        # ── CSRF gate ─────────────────────────────────────────────
        if not csrf_verify(self):
            json_response(self, {'ok': False, 'error': 'CSRF token required'}, status=403)
            return

        # ── Auth: login (unprotected) ─────────────────────────────
        if self.path == '/auth/login':
            try:
                data      = json.loads(body.decode('utf-8'))
                email     = data.get('email', '')
                password  = data.get('password', '')
                remember  = bool(data.get('remember', False))
                totp_code = data.get('totp_code', None)
                ip        = get_client_ip(self)
                ua        = self.headers.get('User-Agent', '')
                session_tok, err = auth_login(email, password, ip, remember, ua, totp_code)
                if err == '2fa_required':
                    json_response(self, {'ok': False, 'error': '2fa_required', '2fa_required': True})
                elif err:
                    json_response(self, {'ok': False, 'error': err}, status=401)
                else:
                    # 90-day persistent cookie -- survives browser close on all devices
                    max_age = 90 * 24 * 3600
                    cookie_val = ('ry_session=' + urllib.parse.quote(session_tok)
                        + '; Path=/; Max-Age=' + str(max_age)
                        + '; SameSite=Lax; HttpOnly; Secure')
                    import sys
                    print(f'[AUTH] 90-day session cookie set for {email}', file=sys.stderr)
                    self.send_response(200)
                    self.send_header('Content-Type', 'application/json')
                    self.send_header('Set-Cookie', cookie_val)
                    resp_body = json.dumps({'ok': True, 'token': session_tok}).encode()
                    self.send_header('Content-Length', str(len(resp_body)))
                    self.end_headers()
                    self.wfile.write(resp_body)
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Auth: reauth -- restore session cookie from remember_token ─
        # remember_token is a long-lived JWT (90d) stored in localStorage.
        # It is verified by signature ONLY -- no DB lookup required.
        # This lets users stay connected across browser closes.
        if self.path == '/auth/reauth':
            try:
                auth_header = self.headers.get('Authorization', '')
                if not auth_header.startswith('Bearer '):
                    json_response(self, {'ok': False, 'error': 'No token'}, status=401)
                    return
                candidate = auth_header[7:]
                # Verify JWT signature + expiry only -- stateless, no DB session lookup
                claims = jwt_verify(candidate)
                if not claims:
                    json_response(self, {'ok': False, 'error': 'expired'}, status=401)
                    return
                # Confirm user is still active
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT id, email, name, role, active FROM users WHERE id=? AND active=1',
                          (claims.get('user_id'),))
                user_row = c.fetchone()
                conn.close()
                if not user_row:
                    json_response(self, {'ok': False, 'error': 'User not found'}, status=401)
                    return
                ip = get_client_ip(self)
                ua = self.headers.get('User-Agent', '')
                # Issue a fresh 90-day session
                new_tok, err = auth_login_token(user_row['email'], ip, ua)
                if err or not new_tok:
                    json_response(self, {'ok': False, 'error': err or 'reauth failed'}, status=500)
                    return
                max_age = 90 * 24 * 3600
                cookie_val = ('ry_session=' + urllib.parse.quote(new_tok)
                    + '; Path=/; Max-Age=' + str(max_age)
                    + '; SameSite=Lax; HttpOnly; Secure')
                import sys; print(f'[REAUTH] OK for user_id={user_row["id"]}', file=sys.stderr)
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Set-Cookie', cookie_val)
                resp_body = json.dumps({'ok': True, 'token': new_tok}).encode()
                self.send_header('Content-Length', str(len(resp_body)))
                self.end_headers()
                self.wfile.write(resp_body)
            except Exception as e:
                import sys; print(f'[REAUTH] error: {e}', file=sys.stderr)
                json_response(self, {'ok': False, 'error': str(e)}, status=500)
            return

        # ── Auth: logout ─────────────────────────────────────────


        # ── Auth: 2FA management ─────────────────────────────────
        # ── 2FA: enable (verify code then save secret) ───────────
        if self.path == '/auth/2fa/enable':
            user = require_auth(self)
            if not user: return
            try:
                data   = json.loads(body.decode('utf-8'))
                secret = data.get('secret', '').strip()
                code   = data.get('code', '').strip()
                if not secret or not code:
                    json_response(self, {'ok': False, 'error': 'Secret and code required.'}, status=400)
                    return
                if not totp_verify(secret, code):
                    json_response(self, {'ok': False, 'error': 'Invalid code. Check your authenticator app.'}, status=400)
                    return
                backup = totp_generate_backup_codes()
                conn = get_db()
                conn.execute(
                    'UPDATE users SET totp_secret=?, totp_enabled=1, totp_backup_codes=? WHERE id=?',
                    (secret, json.dumps(backup), user['id'])
                )
                conn.commit()
                conn.close()
                db_audit(user['id'], '2fa_enabled', 'TOTP 2FA enabled', get_client_ip(self))
                json_response(self, {'ok': True, 'backup_codes': backup})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── 2FA: disable ──────────────────────────────────────────
        if self.path == '/auth/2fa/disable':
            user = require_auth(self)
            if not user: return
            try:
                data = json.loads(body.decode('utf-8'))
                code = data.get('code', '').strip()
                conn = get_db()
                c    = conn.cursor()
                c.execute('SELECT totp_secret, totp_backup_codes FROM users WHERE id=?', (user['id'],))
                row = c.fetchone()
                # Verify current code before disabling
                valid = False
                if row and row['totp_secret']:
                    if totp_verify(row['totp_secret'], code):
                        valid = True
                    elif row['totp_backup_codes']:
                        remaining = totp_check_backup(row['totp_backup_codes'], code)
                        if remaining is not None:
                            valid = True
                if not valid:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Invalid code.'}, status=400)
                    return
                conn.execute(
                    'UPDATE users SET totp_secret=NULL, totp_enabled=0, totp_backup_codes=NULL WHERE id=?',
                    (user['id'],)
                )
                conn.commit()
                conn.close()
                db_audit(user['id'], '2fa_disabled', 'TOTP 2FA disabled', get_client_ip(self))
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── 2FA: admin force-disable for a user ───────────────────
        if self.path == '/auth/2fa/admin-disable':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            try:
                data    = json.loads(body.decode('utf-8'))
                user_id = data.get('user_id')
                conn    = get_db()
                conn.execute(
                    'UPDATE users SET totp_secret=NULL, totp_enabled=0, totp_backup_codes=NULL WHERE id=?',
                    (user_id,)
                )
                conn.commit()
                conn.close()
                db_audit(user['id'], '2fa_admin_disabled', f'Admin disabled 2FA for user {user_id}', get_client_ip(self))
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return



        # ── Auth: change own password ─────────────────────────────
        if self.path == '/auth/change-password':
            user = require_auth(self)
            if not user: return
            try:
                data        = json.loads(body.decode('utf-8'))
                current_pw  = data.get('current_password', '')
                new_pw      = data.get('new_password', '')
                if len(new_pw) < 8:
                    json_response(self, {'ok': False, 'error': 'Password must be at least 8 characters'}, status=400)
                    return
                conn = get_db()
                c    = conn.cursor()
                c.execute('SELECT password_hash FROM users WHERE id=?', (user['id'],))
                row = c.fetchone()
                if not row or not check_password(current_pw, row['password_hash']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Current password is incorrect'}, status=400)
                    return
                conn.execute('UPDATE users SET password_hash=? WHERE id=?',
                             (hash_password(new_pw), user['id']))
                # Invalidate all other sessions
                conn.execute('DELETE FROM sessions WHERE user_id=? AND token!=?',
                             (user['id'], auth_get_token(self)))
                conn.commit()
                conn.close()
                db_audit(user['id'], 'password_change', ip=get_client_ip(self))
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Admin: create user ────────────────────────────────────
        if self.path == '/admin/users/create':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            try:
                data     = json.loads(body.decode('utf-8'))
                email    = data.get('email', '').lower().strip()
                name     = data.get('name', '').strip()
                password = data.get('password', '')
                role     = data.get('role', 'staff')
                if not email or not name or not password:
                    json_response(self, {'ok': False, 'error': 'email, name and password are required'}, status=400)
                    return
                if role not in ('superadmin', 'admin', 'manager', 'staff'):
                    json_response(self, {'ok': False, 'error': 'Invalid role'}, status=400)
                    return
                if user['role'] == 'admin' and role == 'superadmin':
                    json_response(self, {'ok': False, 'error': 'Admins cannot create superadmins'}, status=403)
                    return
                if len(password) < 8:
                    json_response(self, {'ok': False, 'error': 'Password must be at least 8 characters'}, status=400)
                    return
                conn = get_db()
                try:
                    conn.execute('INSERT INTO users (email,name,password_hash,role) VALUES (?,?,?,?)',
                                 (email, name, hash_password(password), role))
                    conn.commit()
                    db_audit(user['id'], 'user_create', f'Created {email} ({role})', get_client_ip(self))
                    json_response(self, {'ok': True})
                except sqlite3.IntegrityError:
                    json_response(self, {'ok': False, 'error': 'Email already exists'}, status=400)
                finally:
                    conn.close()
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Admin: update user ────────────────────────────────────
        if self.path == '/admin/users/update':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            try:
                data       = json.loads(body.decode('utf-8'))
                target_id  = int(data.get('id', 0))
                new_name   = data.get('name', '').strip()
                new_role   = data.get('role', '')
                new_active = data.get('active', None)
                new_pw     = data.get('password', '')
                conn = get_db()
                c    = conn.cursor()
                c.execute('SELECT role FROM users WHERE id=?', (target_id,))
                target = c.fetchone()
                if not target:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'User not found'}, status=404)
                    return
                if user['role'] == 'admin' and target['role'] == 'superadmin':
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Cannot modify superadmin'}, status=403)
                    return
                if new_name:
                    conn.execute('UPDATE users SET name=? WHERE id=?', (new_name, target_id))
                if new_role and new_role in ('superadmin', 'admin', 'manager', 'staff'):
                    if not (user['role'] == 'admin' and new_role == 'superadmin'):
                        conn.execute('UPDATE users SET role=? WHERE id=?', (new_role, target_id))
                if new_active is not None:
                    conn.execute('UPDATE users SET active=? WHERE id=?', (1 if new_active else 0, target_id))
                if new_pw and len(new_pw) >= 8:
                    conn.execute('UPDATE users SET password_hash=? WHERE id=?',
                                 (hash_password(new_pw), target_id))
                    conn.execute('DELETE FROM sessions WHERE user_id=?', (target_id,))
                conn.commit()
                conn.close()
                db_audit(user['id'], 'user_update', f'Updated user id={target_id}', get_client_ip(self))
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Admin: delete user ────────────────────────────────────
        if self.path == '/admin/users/delete':
            user = require_auth(self)
            if not user: return
            if user['role'] != 'superadmin':
                json_response(self, {'ok': False, 'error': 'Only superadmins can delete users'}, status=403)
                return
            try:
                data      = json.loads(body.decode('utf-8'))
                target_id = int(data.get('id', 0))
                if target_id == user['id']:
                    json_response(self, {'ok': False, 'error': 'Cannot delete your own account'}, status=400)
                    return
                conn = get_db()
                conn.execute('DELETE FROM sessions WHERE user_id=?', (target_id,))
                conn.execute('DELETE FROM permissions WHERE user_id=?', (target_id,))
                conn.execute('DELETE FROM users WHERE id=?', (target_id,))
                conn.commit()
                conn.close()
                db_audit(user['id'], 'user_delete', f'Deleted user id={target_id}', get_client_ip(self))
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # All routes below require authentication
        user = require_auth(self)
        if not user: return

        # ── Admin: save role permissions ─────────────────────────
        if self.path == '/admin/role-permissions':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            try:
                data = json.loads(body.decode('utf-8'))
                perms = data.get('permissions', [])  # [{role, section, can_view}]
                conn = get_db()
                for p in perms:
                    conn.execute(
                        'INSERT OR REPLACE INTO role_permissions (role, section, can_view) VALUES (?,?,?)',
                        (p['role'], p['section'], 1 if p['can_view'] else 0)
                    )
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        if self.path == '/save':
            try:
                data     = json.loads(body.decode('utf-8'))
                meetings = data.get('meetings', [])
                if not isinstance(meetings, list):
                    raise ValueError("meetings must be a list")
                ok = save_meetings(meetings)
                json_response(self, {'ok': ok, 'count': len(meetings)})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)

        elif self.path == '/profile/update':
            user = require_auth(self)
            if not user: return
            try:
                data = json.loads(body.decode('utf-8'))
                name   = str(data.get('name', '')).strip()
                avatar = data.get('avatar', None)  # base64 data URL or null
                if not name:
                    json_response(self, {'ok': False, 'error': 'Name required'}, status=400)
                    return
                # Validate avatar size (max ~500KB base64)
                if avatar and len(avatar) > 700000:
                    json_response(self, {'ok': False, 'error': 'Avatar too large (max 500KB)'}, status=400)
                    return
                conn = get_db()
                conn.execute("UPDATE users SET name=?, avatar=? WHERE id=?", (name, avatar, user['id']))
                conn.commit()
                db_audit(user['id'], 'profile_update', ip=get_client_ip(self))
                json_response(self, {'ok': True, 'name': name, 'avatar': avatar})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)

        elif self.path == '/save_v2':
            try:
                incoming = json.loads(body.decode('utf-8'))
                # Always merge incoming data with existing — never do a blind overwrite.
                # This means a shortcuts-only POST won't erase customers/contracts etc.
                existing = load_v2_data()
                merged = dict(existing)  # start from what's on disk
                # Only update keys that are explicitly present AND non-empty in the request
                for key in ('customers', 'suppliers', 'contracts', 'taskLists', 'shortcuts', 'navLayout'):
                    if key in incoming and incoming[key] is not None:
                        # Accept empty list only if incoming explicitly contains the key
                        # AND the existing value is also empty (never shrink to empty)
                        val = incoming[key]
                        if isinstance(val, list) and len(val) == 0 and isinstance(existing.get(key), list) and len(existing.get(key, [])) > 0:
                            pass  # refuse to overwrite non-empty with empty
                        else:
                            merged[key] = val
                ok = save_v2_data(merged)
                json_response(self, {'ok': ok})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)

        # ── /sp/token -- OAuth2 client-credentials token fetch (server proxy) ──
        elif self.path == '/sp/test':
            # Diagnostic: test certificate auth and return raw Microsoft response
            user = require_auth(self)
            if not user: return
            try:
                data      = json.loads(body.decode('utf-8'))
                tenant_id = str(data.get('tenant_id', ''))
                cid       = data.get('client_id', '')
                PFX_PATH  = '/opt/rytech/rytech_spo.pfx'
                PFX_PASS  = b'RytechCert123'
                THUMBPRINT= '4a7ea3a287cd5289c21c6065d1b9cc8781be4962'
                diag = {'pfx_exists': os.path.exists(PFX_PATH), 'steps': []}

                if not os.path.exists(PFX_PATH):
                    json_response(self, {'ok': False, 'error': 'PFX file not found at ' + PFX_PATH, 'diag': diag})
                    return

                from cryptography.hazmat.primitives.serialization import pkcs12
                from cryptography.hazmat.primitives import hashes
                from cryptography.hazmat.primitives.asymmetric import padding as _pad

                with open(PFX_PATH, 'rb') as fh:
                    pfx_data = fh.read()
                priv_key, certificate, _ = pkcs12.load_key_and_certificates(pfx_data, PFX_PASS)
                diag['steps'].append('PFX loaded OK')
                diag['cert_subject'] = str(certificate.subject)

                thumb_bytes = bytes.fromhex(THUMBPRINT)
                x5t = base64.urlsafe_b64encode(thumb_bytes).rstrip(b'=').decode()
                token_url = f'https://login.microsoftonline.com/{tenant_id}/oauth2/v2.0/token'
                now = int(time.time())

                def _b64(d):
                    if isinstance(d, dict): d = json.dumps(d, separators=(',', ':')).encode()
                    return base64.urlsafe_b64encode(d).rstrip(b'=').decode()

                hdr     = _b64({'alg': 'RS256', 'typ': 'JWT', 'x5t': x5t})
                payload = _b64({'aud': token_url, 'iss': cid, 'sub': cid,
                                'jti': base64.urlsafe_b64encode(os.urandom(16)).decode(),
                                'nbf': now, 'exp': now + 600})
                msg     = f'{hdr}.{payload}'.encode()
                sig     = priv_key.sign(msg, _pad.PKCS1v15(), hashes.SHA256())
                assertion = f'{hdr}.{payload}.{_b64(sig)}'
                diag['steps'].append('JWT assertion built OK')

                fields = {
                    'grant_type': 'client_credentials', 'client_id': cid,
                    'scope': 'https://graph.microsoft.com/.default',
                    'client_assertion_type': 'urn:ietf:params:oauth:client-assertion-type:jwt-bearer',
                    'client_assertion': assertion,
                }
                req = urllib.request.Request(token_url,
                    data=urllib.parse.urlencode(fields).encode(),
                    headers={'Content-Type': 'application/x-www-form-urlencoded'})
                try:
                    with urllib.request.urlopen(req, timeout=20) as r:
                        result = json.loads(r.read().decode())
                    diag['steps'].append('Token request succeeded')
                    json_response(self, {'ok': True, 'token_type': result.get('token_type'),
                                         'expires_in': result.get('expires_in'), 'diag': diag})
                except urllib.error.HTTPError as e:
                    raw = e.read().decode(errors='replace')
                    diag['steps'].append('Token request failed: HTTP ' + str(e.code))
                    json_response(self, {'ok': False, 'http_status': e.code,
                                         'microsoft_response': raw, 'diag': diag})
            except Exception as e:
                import traceback
                json_response(self, {'ok': False, 'error': str(e),
                                     'traceback': traceback.format_exc()}, status=500)

        elif self.path == '/sp/token':
            user = require_auth(self)
            if not user: return
            try:
                data      = json.loads(body.decode('utf-8'))
                tenant_id = str(data.get('tenant_id', 'common'))
                cid       = data.get('client_id', '')
                # Allow caller to specify scope -- default to Graph, but SP REST needs sharepoint scope
                scope     = data.get('scope', 'https://graph.microsoft.com/.default')
                if not cid:
                    json_response(self, {'error': 'invalid_request',
                        'error_description': 'client_id is required'}, status=400)
                    return

                # ── Build client_assertion JWT signed with PFX certificate ──
                # This replaces the retired Azure ACS / client_secret flow.
                PFX_PATH   = '/opt/rytech/rytech_spo.pfx'
                PFX_PASS   = b'RytechCert123'
                THUMBPRINT = '4a7ea3a287cd5289c21c6065d1b9cc8781be4962'

                from cryptography.hazmat.primitives.serialization import pkcs12
                from cryptography.hazmat.primitives import hashes
                from cryptography.hazmat.primitives.asymmetric import padding as _pad

                with open(PFX_PATH, 'rb') as fh:
                    pfx_data = fh.read()
                priv_key, certificate, _ = pkcs12.load_key_and_certificates(
                    pfx_data, PFX_PASS)

                # x5t = base64url(SHA-1 of DER-encoded cert) -- same as thumbprint bytes
                thumb_bytes = bytes.fromhex(THUMBPRINT)
                x5t = base64.urlsafe_b64encode(thumb_bytes).rstrip(b'=').decode()

                token_url = f'https://login.microsoftonline.com/{tenant_id}/oauth2/v2.0/token'
                now = int(time.time())

                def _b64(d):
                    if isinstance(d, dict):
                        d = json.dumps(d, separators=(',', ':')).encode()
                    return base64.urlsafe_b64encode(d).rstrip(b'=').decode()

                hdr     = _b64({'alg': 'RS256', 'typ': 'JWT', 'x5t': x5t})
                payload = _b64({'aud': token_url, 'iss': cid, 'sub': cid,
                                'jti': base64.urlsafe_b64encode(os.urandom(16)).decode(),
                                'nbf': now, 'exp': now + 600})
                msg     = f'{hdr}.{payload}'.encode()
                sig     = priv_key.sign(msg, _pad.PKCS1v15(), hashes.SHA256())
                assertion = f'{hdr}.{payload}.{_b64(sig)}'

                fields = {
                    'grant_type':            'client_credentials',
                    'client_id':             cid,
                    'scope':                 scope,
                    'client_assertion_type': 'urn:ietf:params:oauth:client-assertion-type:jwt-bearer',
                    'client_assertion':      assertion,
                }
                encoded = urllib.parse.urlencode(fields).encode()
                req = urllib.request.Request(token_url, data=encoded,
                          headers={'Content-Type': 'application/x-www-form-urlencoded'})
                with urllib.request.urlopen(req, timeout=20) as r:
                    result = json.loads(r.read().decode())
                json_response(self, result)
            except urllib.error.HTTPError as e:
                raw = e.read()
                try:    err_body = json.loads(raw.decode())
                except: err_body = {'error': 'http_'+str(e.code),
                                    'error_description': raw.decode(errors='replace')[:500]}
                json_response(self, err_body, status=e.code)
            except Exception as e:
                import traceback
                json_response(self, {'error': 'server_error',
                                     'error_description': str(e),
                                     'traceback': traceback.format_exc()}, status=500)

        # ── /sp/proxy -- reverse-proxy GET/POST to Microsoft Graph API ────────
        elif self.path == '/sp/proxy':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode('utf-8'))
                token   = data.get('token', '')
                url     = data.get('url', '')
                method  = data.get('method', 'GET').upper()
                payload = data.get('body')
                allowed = (url.startswith('https://graph.microsoft.com/') or
                           ('.sharepoint.com/' in url and url.startswith('https://')))
                if not allowed:
                    json_response(self, {'error': 'Only graph.microsoft.com or sharepoint.com URLs allowed'}, status=400)
                    return
                req_body = json.dumps(payload).encode() if payload else None
                # SharePoint REST needs odata=verbose or odata=nometadata to get JSON
                accept_hdr = 'application/json;odata=nometadata' if '.sharepoint.com/' in url else 'application/json'
                req = urllib.request.Request(url, data=req_body, method=method,
                          headers={'Authorization': f'Bearer {token}',
                                   'Content-Type':  'application/json',
                                   'Accept':         accept_hdr})
                with urllib.request.urlopen(req, timeout=20) as r:
                    raw_bytes = r.read()
                    content_type = r.headers.get('Content-Type', '')
                raw_text = raw_bytes.decode('utf-8', errors='replace')
                if not raw_text.strip():
                    json_response(self, {'_raw': '', '_empty': True})
                    return
                try:
                    result = json.loads(raw_text)
                except Exception:
                    # Return raw text so client can see what SP actually sent
                    json_response(self, {'_raw': raw_text[:2000], '_content_type': content_type})
                    return
                json_response(self, result)
            except urllib.error.HTTPError as e:
                raw = e.read()
                raw_text = raw.decode('utf-8', errors='replace')
                try:
                    err_body = json.loads(raw_text)
                except Exception:
                    err_body = {'_raw': raw_text[:1000], '_content_type': e.headers.get('Content-Type','')}
                err_body['_http_status'] = e.code
                json_response(self, err_body, status=200)  # always 200 so client reads body
            except Exception as e:
                json_response(self, {'error': {'message': str(e)}, '_http_status': 500}, status=200)

        # ── /sp/create-folder -- create customer folder + subfolders + copy templates ─
        elif self.path == '/sp/create-folder':
            user = require_auth(self)
            if not user: return
            try:
                data        = json.loads(body.decode('utf-8'))
                token       = data.get('token', '')
                site_id     = data.get('siteId', '')
                drive_id    = data.get('driveId', '')
                parent_id   = data.get('parentId')    # None = drive root
                folder_name = data.get('folderName', '').strip()
                safe_name   = ''.join(c for c in folder_name if c not in '/:*?\"<>|\\').strip()
                if not safe_name:
                    raise ValueError('folderName is required')

                auth_hdr = {'Authorization': f'Bearer {token}',
                            'Content-Type':  'application/json',
                            'Accept':        'application/json'}

                def graph_post(url, payload):
                    req = urllib.request.Request(
                        url, data=json.dumps(payload).encode(), method='POST', headers=auth_hdr)
                    with urllib.request.urlopen(req, timeout=20) as r:
                        return json.loads(r.read().decode() or '{}'), r.status

                base = f'https://graph.microsoft.com/v1.0/sites/{site_id}/drives/{drive_id}'
                parent_url = (f'{base}/items/{parent_id}/children'
                              if parent_id else f'{base}/root/children')

                # Create root customer folder
                folder_data, status = graph_post(parent_url,
                    {'name': safe_name, 'folder': {},
                     '@microsoft.graph.conflictBehavior': 'rename'})
                if status not in (200, 201):
                    raise ValueError(folder_data.get('error',{}).get('message', f'Graph HTTP {status}'))
                root_id = folder_data['id']

                # Create standard subfolders
                sub_url = f'{base}/items/{root_id}/children'
                for sub in ['Quotes', 'Proposals', 'Meetings', 'Contracts']:
                    try:
                        graph_post(sub_url,
                            {'name': sub, 'folder': {},
                             '@microsoft.graph.conflictBehavior': 'rename'})
                    except Exception:
                        pass

                # Upload templates from /opt/rytech/Templates
                templates_copied = 0
                if os.path.isdir(TEMPLATES_SRC):
                    for fname in os.listdir(TEMPLATES_SRC):
                        src_path = os.path.join(TEMPLATES_SRC, fname)
                        if not os.path.isfile(src_path):
                            continue
                        try:
                            with open(src_path, 'rb') as fh:
                                file_bytes = fh.read()
                            up_url = f'{base}/items/{root_id}:/{urllib.parse.quote(fname)}:/content'
                            up_req = urllib.request.Request(
                                up_url, data=file_bytes, method='PUT',
                                headers={'Authorization': f'Bearer {token}',
                                         'Content-Type':  'application/octet-stream'})
                            with urllib.request.urlopen(up_req, timeout=30):
                                templates_copied += 1
                        except Exception:
                            pass  # don't abort if one template fails

                json_response(self, {
                    'ok': True, 'folderId': root_id,
                    'folderName': safe_name, 'templatesCopied': templates_copied
                })
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)

        # ── /local/copy-templates -- create customer folder on VPS + copy templates ──
        elif self.path == '/local/copy-templates':
            user = require_auth(self)
            if not user: return
            try:
                data          = json.loads(body.decode('utf-8'))
                customer_name = data.get('customer_name', '').strip()
                if not customer_name:
                    json_response(self, {'ok': False, 'error': 'customer_name required'}, status=400)
                    return
                # Sanitise name -- strip path separators to prevent traversal
                safe_name   = customer_name.replace('/', '').replace('\\', '').replace('..', '')
                folder_path = os.path.join(CUSTOMERS_BASE_DIR, safe_name)
                os.makedirs(folder_path, exist_ok=True)
                # Copy templates
                copied = 0
                errors = []
                if os.path.isdir(TEMPLATES_SRC):
                    for fname in os.listdir(TEMPLATES_SRC):
                        src = os.path.join(TEMPLATES_SRC, fname)
                        dst = os.path.join(folder_path, fname)
                        if os.path.isfile(src):
                            try:
                                shutil.copy2(src, dst)
                                copied += 1
                            except Exception as ex:
                                errors.append(fname + ': ' + str(ex))
                json_response(self, {
                    'ok': True,
                    'folder': folder_path,
                    'copied': copied,
                    'errors': errors
                })
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)

        # ── OAuth token persistence ───────────────────────────────
        elif self.path == '/oauth/tokens/save':
            user = require_auth(self)
            if not user: return
            try:
                data     = json.loads(body.decode())
                provider = data.get('provider', '').lower().strip()
                tokens   = data.get('tokens')
                if provider not in _ALLOWED_PROVIDERS or not isinstance(tokens, dict):
                    json_response(self, {'ok': False, 'error': 'Invalid provider or tokens'}, status=400)
                    return
                oauth_save(user['id'], provider, tokens)
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)

        elif self.path == '/oauth/tokens/delete':
            user = require_auth(self)
            if not user: return
            try:
                data     = json.loads(body.decode())
                provider = data.get('provider', '').lower().strip()
                if provider not in _ALLOWED_PROVIDERS:
                    json_response(self, {'ok': False, 'error': 'Invalid provider'}, status=400)
                    return
                oauth_delete(user['id'], provider)
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)

        elif self.path == '/proxy/action1/token':
            try:
                # Inject A1 credentials server-side — browser sends no secrets
                a1_client_id     = cred_load('a1_client_id')
                a1_client_secret = cred_load('a1_client_secret')
                if not a1_client_id or not a1_client_secret:
                    json_response(self, {'error': 'Action1 credentials not configured on server'}, status=503)
                    return
                token_body = urllib.parse.urlencode({
                    'client_id':     a1_client_id,
                    'client_secret': a1_client_secret
                }).encode()
                req = urllib.request.Request(
                    'https://app.eu.action1.com/api/3.0/oauth2/token',
                    data=token_body,
                    headers={'Content-Type': 'application/x-www-form-urlencoded'}
                )
                with urllib.request.urlopen(req, timeout=20) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body)
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif self.path == '/proxy/datto/token':
            try:
                params_d = urllib.parse.parse_qs(body.decode())
                api_url  = params_d.get('api_url', [''])[0]
                # Inject Datto credentials server-side
                api_key    = cred_load('datto_api_key')
                api_secret = cred_load('datto_api_secret')
                if not api_key or not api_secret:
                    json_response(self, {'error': 'Datto credentials not configured on server'}, status=503)
                    return
                import base64 as _b64
                creds      = _b64.b64encode(b'public-client:public').decode()
                token_body = urllib.parse.urlencode({
                    'grant_type': 'password',
                    'username':   api_key,
                    'password':   api_secret
                }).encode()
                req = urllib.request.Request(
                    f'{api_url}/auth/oauth/token',
                    data=token_body,
                    headers={
                        'Content-Type':  'application/x-www-form-urlencoded',
                        'Authorization': f'Basic {creds}'
                    }
                )
                with urllib.request.urlopen(req, timeout=20) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body)
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif self.path == '/proxy/xero/token':
            try:
                # Parse incoming body — client sends everything except client_secret
                params = urllib.parse.parse_qs(body.decode('utf-8', errors='replace'))
                client_id = params.get('client_id', [''])[0]
                # Inject server-side secret — never exposed to browser
                client_secret = cred_load('xero_client_secret')
                if not client_secret:
                    json_response(self, {'ok': False, 'error': 'Xero client secret not configured on server'}, status=503)
                    return
                # Rebuild body with injected secret
                new_params = {k: v[0] for k, v in params.items()}
                new_params['client_id']     = client_id
                new_params['client_secret'] = client_secret
                req_body = urllib.parse.urlencode(new_params).encode()
                req = urllib.request.Request(
                    'https://identity.xero.com/connect/token',
                    data=req_body,
                    headers={'Content-Type': 'application/x-www-form-urlencoded'}
                )
                with urllib.request.urlopen(req, timeout=15) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(resp_body)))
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(err_body)))
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body)
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)

        elif self.path == '/proxy/zoho/token':
            try:
                params = urllib.parse.parse_qs(body.decode('utf-8', errors='replace'))
                client_id = params.get('client_id', [''])[0]
                client_secret = cred_load('zoho_client_secret')
                if not client_secret:
                    json_response(self, {'ok': False, 'error': 'Zoho client secret not configured on server'}, status=503)
                    return
                new_params = {k: v[0] for k, v in params.items()}
                new_params['client_id']     = client_id
                new_params['client_secret'] = client_secret
                req_body = urllib.parse.urlencode(new_params).encode()
                req = urllib.request.Request(
                    'https://accounts.zoho.eu/oauth/v2/token',
                    data=req_body,
                    headers={'Content-Type': 'application/x-www-form-urlencoded'}
                )
                with urllib.request.urlopen(req, timeout=15) as resp:
                    resp_body = resp.read()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(resp_body)))
                _send_cors(self)
                self.end_headers()
                self.wfile.write(resp_body)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self.send_response(e.code)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(err_body)))
                _send_cors(self)
                self.end_headers()
                self.wfile.write(err_body)
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)

        elif self.path == '/monzo-start':
            try:
                req_data      = json.loads(body)
                client_id     = req_data.get('client_id', '')
                client_secret = req_data.get('client_secret', '')
                redirect_uri  = req_data.get('redirect_uri', '')
                state         = _secrets.token_urlsafe(16)
                _monzo_sessions[state] = {
                    'client_id':     client_id,
                    'client_secret': client_secret,
                    'redirect_uri':  redirect_uri,
                    'ts':            time.time()
                }
                auth_url = (
                    f'https://auth.monzo.com/?client_id={urllib.parse.quote(client_id)}'
                    f'&redirect_uri={urllib.parse.quote(redirect_uri)}'
                    f'&response_type=code&state={state}'
                )
                json_response(self, {'auth_url': auth_url, 'state': state})
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif self.path == '/proxy/monzo/token':
            try:
                req_data   = json.loads(body)
                token_body = urllib.parse.urlencode({
                    'grant_type':    'authorization_code',
                    'client_id':     req_data['client_id'],
                    'client_secret': req_data['client_secret'],
                    'redirect_uri':  req_data['redirect_uri'],
                    'code':          req_data['code'],
                }).encode()
                req = urllib.request.Request(
                    'https://api.monzo.com/oauth2/token',
                    data=token_body,
                    headers={'Content-Type': 'application/x-www-form-urlencoded'}
                )
                with urllib.request.urlopen(req, timeout=20) as resp:
                    resp_body = resp.read()
                json_response(self, json.loads(resp_body))
            except urllib.error.HTTPError as e:
                err_body = e.read()
                json_response(self, {'error': str(e), 'detail': err_body.decode(errors='replace')},
                              status=e.code)
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        elif self.path == '/proxy/monzo/refresh':
            try:
                req_data   = json.loads(body)
                token_body = urllib.parse.urlencode({
                    'grant_type':    'refresh_token',
                    'client_id':     req_data['client_id'],
                    'client_secret': req_data['client_secret'],
                    'refresh_token': req_data['refresh_token'],
                }).encode()
                req = urllib.request.Request(
                    'https://api.monzo.com/oauth2/token',
                    data=token_body,
                    headers={'Content-Type': 'application/x-www-form-urlencoded'}
                )
                with urllib.request.urlopen(req, timeout=20) as resp:
                    resp_body = resp.read()
                json_response(self, json.loads(resp_body))
            except urllib.error.HTTPError as e:
                err_body = e.read()
                json_response(self, {'error': str(e), 'detail': err_body.decode(errors='replace')},
                              status=e.code)
            except Exception as e:
                json_response(self, {'error': str(e)}, status=500)

        # ── Subtasks: create ─────────────────────────────────────
        elif self.path == '/tasks/subtask/create':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                task_id = int(data.get('task_id', 0))
                title   = data.get('title', '').strip()
                if not title:
                    json_response(self, {'ok': False, 'error': 'Title required'}, status=400)
                    return
                conn = get_db()
                c = conn.cursor()
                # Only creator or assignee can add subtasks
                c.execute('SELECT creator_id, assignee_id FROM assigned_tasks WHERE id=?', (task_id,))
                row = c.fetchone()
                if not row or (row['creator_id'] != user['id'] and row['assignee_id'] != user['id']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                    return
                c.execute('INSERT INTO subtasks (task_id, title) VALUES (?,?)', (task_id, title))
                sub_id = c.lastrowid
                conn.commit()
                conn.close()
                json_response(self, {'ok': True, 'id': sub_id})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/subtask/toggle':
            user = require_auth(self)
            if not user: return
            try:
                data   = json.loads(body.decode())
                sub_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('''SELECT s.*, t.creator_id, t.assignee_id FROM subtasks s
                             JOIN assigned_tasks t ON s.task_id=t.id WHERE s.id=?''', (sub_id,))
                row = c.fetchone()
                if not row or (row['creator_id'] != user['id'] and row['assignee_id'] != user['id']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                    return
                new_done = 0 if row['done'] else 1
                conn.execute('UPDATE subtasks SET done=? WHERE id=?', (new_done, sub_id))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True, 'done': new_done})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/subtask/delete':
            user = require_auth(self)
            if not user: return
            try:
                data   = json.loads(body.decode())
                sub_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('''SELECT s.*, t.creator_id FROM subtasks s
                             JOIN assigned_tasks t ON s.task_id=t.id WHERE s.id=?''', (sub_id,))
                row = c.fetchone()
                if not row or row['creator_id'] != user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                    return
                conn.execute('DELETE FROM subtasks WHERE id=?', (sub_id,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Task notes: add ───────────────────────────────────────
        elif self.path == '/tasks/note/add':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                task_id = int(data.get('task_id', 0))
                body_txt= data.get('body', '').strip()
                if not body_txt:
                    json_response(self, {'ok': False, 'error': 'Note body required'}, status=400)
                    return
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT creator_id, assignee_id FROM assigned_tasks WHERE id=?', (task_id,))
                row = c.fetchone()
                if not row or (row['creator_id'] != user['id'] and row['assignee_id'] != user['id']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                    return
                c.execute('INSERT INTO task_notes (task_id, author_id, body) VALUES (?,?,?)',
                          (task_id, user['id'], body_txt))
                note_id = c.lastrowid
                conn.commit()
                conn.close()
                json_response(self, {'ok': True, 'id': note_id,
                                     'author_name': user['name'],
                                     'created_at': 'just now'})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/note/delete':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                note_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT author_id FROM task_notes WHERE id=?', (note_id,))
                row = c.fetchone()
                if not row or row['author_id'] != user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                    return
                conn.execute('DELETE FROM task_notes WHERE id=?', (note_id,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Notes: create ────────────────────────────────────────
        elif self.path == '/notes/create':
            user = require_auth(self)
            if not user: return
            try:
                data         = json.loads(body.decode())
                title        = data.get('title', 'Untitled').strip() or 'Untitled'
                content      = data.get('content', '')
                color        = data.get('color', '#1e2830')
                pinned       = 1 if data.get('pinned') else 0
                drawing_data = data.get('drawing_data', '')
                conn = get_db()
                c = conn.cursor()
                c.execute('INSERT INTO notes (owner_id,title,content,color,pinned,drawing_data) VALUES (?,?,?,?,?,?)',
                          (user['id'], title, content, color, pinned, drawing_data))
                note_id = c.lastrowid
                conn.commit()
                c.execute('SELECT * FROM notes WHERE id=?', (note_id,))
                note = dict(c.fetchone())
                conn.close()
                json_response(self, {'ok': True, 'note': note})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/notes/update':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                note_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT owner_id FROM notes WHERE id=?', (note_id,))
                row = c.fetchone()
                if not row or row['owner_id'] != user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not found'}, status=404)
                    return
                fields, vals = [], []
                for f in ('title', 'content', 'color', 'drawing_data'):
                    if f in data:
                        fields.append(f'{f}=?')
                        vals.append(data[f])
                if 'pinned' in data:
                    fields.append('pinned=?')
                    vals.append(1 if data['pinned'] else 0)
                fields.append("updated_at=datetime('now')")
                vals.append(note_id)
                conn.execute(f'UPDATE notes SET {", ".join(fields)} WHERE id=?', vals)
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/notes/delete':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                note_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT owner_id FROM notes WHERE id=?', (note_id,))
                row = c.fetchone()
                if not row or row['owner_id'] != user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not found'}, status=404)
                    return
                conn.execute('DELETE FROM notes WHERE id=?', (note_id,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Groq: save API key ───────────────────────────────────
        elif self.path == '/groq/key/save':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                api_key = data.get('api_key', '').strip()
                if not api_key.startswith('gsk_'):
                    json_response(self, {'ok': False, 'error': 'Invalid Groq API key (must start with gsk_)'}, status=400)
                    return
                enc = encrypt_token(api_key)
                conn = get_db()
                conn.execute('''INSERT INTO groq_config (id, key_enc) VALUES (1, ?)
                                ON CONFLICT(id) DO UPDATE SET key_enc=excluded.key_enc,
                                updated_at=datetime('now')''', (enc,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/admin/credentials/save':
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            try:
                data = json.loads(body.decode())
                ALLOWED_KEYS = {
                    'xero_client_id', 'xero_client_secret',
                    'zoho_client_id', 'zoho_client_secret',
                    'a1_client_id', 'a1_client_secret',
                    'datto_api_key', 'datto_api_secret',
                    'groq_api_key',
                }
                saved = []
                for key, value in data.items():
                    if key not in ALLOWED_KEYS:
                        continue
                    if value and isinstance(value, str) and value.strip():
                        cred_save(key, value.strip())
                        saved.append(key)
                        db_audit(user['id'], 'credential_saved', f'Saved credential: {key}', get_client_ip(self))
                        # Sync Groq API key to groq_config table so /groq/ask picks it up
                        if key == 'groq_api_key':
                            try:
                                gc = get_db()
                                enc = encrypt_token(value.strip())
                                gc.execute(
                                    "INSERT INTO groq_config (id, key_enc) VALUES (1, ?) "
                                    "ON CONFLICT(id) DO UPDATE SET key_enc=excluded.key_enc",
                                    (enc,)
                                )
                                gc.commit()
                                gc.close()
                            except Exception as ge:
                                import sys
                                print(f'[GROQ] groq_config sync failed: {ge}', file=sys.stderr)
                json_response(self, {'ok': True, 'saved': saved})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Notifications: mark read ──────────────────────────────
        elif self.path == '/notifications/read-all':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            conn.execute(
                "UPDATE notifications SET read_at=datetime('now') WHERE user_id=? AND read_at IS NULL",
                (user['id'],)
            )
            conn.commit()
            conn.close()
            json_response(self, {'ok': True})
            return

        elif self.path.startswith('/notifications/read/'):
            user = require_auth(self)
            if not user: return
            nid = int(self.path.split('/')[-1])
            conn = get_db()
            conn.execute(
                "UPDATE notifications SET read_at=datetime('now') WHERE id=? AND user_id=?",
                (nid, user['id'])
            )
            conn.commit()
            conn.close()
            json_response(self, {'ok': True})
            return

        # ── Ticket events: log ────────────────────────────────────
        elif self.path == '/ticket/event':
            user = require_auth(self)
            if not user: return
            try:
                data = json.loads(body.decode())
                ticket_id  = str(data.get('ticket_id', ''))
                event_type = data.get('event_type', 'status_change')
                detail     = data.get('detail', '')
                actor      = user.get('name') or user.get('email', '')
                ticket_event_log(ticket_id, event_type, detail, actor)
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Client activity: log ──────────────────────────────────
        elif self.path == '/client/activity':
            user = require_auth(self)
            if not user: return
            try:
                data = json.loads(body.decode())
                client_id  = str(data.get('client_id', ''))
                event_type = data.get('event_type', 'note')
                title      = data.get('title', '')
                detail     = data.get('detail', '')
                actor      = user.get('name') or user.get('email', '')
                client_activity_log(client_id, event_type, title, detail, actor)
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Widget prefs: save ────────────────────────────────────
        elif self.path == '/widget/prefs':
            user = require_auth(self)
            if not user: return
            try:
                data = json.loads(body.decode())
                prefs_json = json.dumps(data.get('prefs', {}))
                conn = get_db()
                conn.execute(
                    '''INSERT INTO user_widget_prefs (user_id, prefs_json, updated_at)
                       VALUES (?, ?, datetime('now'))
                       ON CONFLICT(user_id) DO UPDATE SET
                         prefs_json=excluded.prefs_json,
                         updated_at=excluded.updated_at''',
                    (user['id'], prefs_json)
                )
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Admin: save per-user permissions ─────────────────────
        elif self.path.startswith('/admin/user-permissions/'):
            user = require_auth(self)
            if not user: return
            if user['role'] not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                return
            try:
                target_id = int(self.path.split('/')[-1])
                data = json.loads(body.decode())
                perms = data.get('permissions', {})  # {section: bool}
                conn = get_db()
                # Delete existing overrides then re-insert
                conn.execute('DELETE FROM permissions WHERE user_id=?', (target_id,))
                for section, can_view in perms.items():
                    conn.execute(
                        'INSERT INTO permissions (user_id, section, can_view) VALUES (?,?,?)',
                        (target_id, section, 1 if can_view else 0)
                    )
                conn.commit()
                conn.close()
                db_audit(user['id'], 'permissions_updated', f'Updated permissions for user {target_id}', get_client_ip(self))
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return



        # ── Groq: proxy ask ─────────────────────────────────────
        elif self.path == '/groq/ask':
            user = require_auth(self)
            if not user: return
            try:
                data     = json.loads(body.decode())
                messages = data.get('messages', [])
                model    = data.get('model', 'llama-3.3-70b-versatile')
                conn = get_db()
                c    = conn.cursor()
                c.execute('SELECT key_enc FROM groq_config WHERE id=1')
                row = c.fetchone()
                conn.close()
                # Fall back to app_credentials table (set via Integration Credentials panel)
                if row and row['key_enc']:
                    api_key = decrypt_token(row['key_enc'])
                else:
                    api_key = cred_load('groq_api_key')
                if not api_key:
                    json_response(self, {'ok': False, 'error': 'no_key'}, status=400)
                    return
                payload = json.dumps({
                    'model':    model,
                    'messages': messages,
                    'max_tokens': 2000
                }).encode()
                req = urllib.request.Request(
                    'https://api.groq.com/openai/v1/chat/completions',
                    data=payload,
                    headers={
                        'Content-Type':  'application/json',
                        'Authorization': f'Bearer {api_key}',
                        'User-Agent':    'RytechSummarAI/6.5 (server-side; +https://rytech-support.com)',
                        'Accept':        'application/json',
                    }
                )
                with urllib.request.urlopen(req, timeout=60) as resp:
                    result = json.loads(resp.read())
                reply = result['choices'][0]['message']['content']
                json_response(self, {'ok': True, 'reply': reply})
            except urllib.error.HTTPError as e:
                try:
                    err_body = e.read().decode('utf-8', errors='replace')
                    # Try to parse JSON error from Groq
                    err_json = json.loads(err_body)
                    err_msg  = err_json.get('error', {}).get('message', err_body) if isinstance(err_json.get('error'), dict) else err_body
                except Exception:
                    err_msg = f'HTTP {e.code}'
                json_response(self, {'ok': False, 'error': f'Groq API error {e.code}: {err_msg}'}, status=502)
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=500)
            return

        # ── Tasks: create ─────────────────────────────────────────
        elif self.path == '/tasks/create':
            user = require_auth(self)
            if not user: return
            try:
                data        = json.loads(body.decode())
                assignee_id = int(data.get('assignee_id', user['id']))
                title       = data.get('title', '').strip()
                description = data.get('description', '').strip()
                priority    = data.get('priority', 'medium')
                due_date    = data.get('due_date') or None
                recur       = data.get('recur') or None
                remind_days = int(data['remind_days']) if data.get('remind_days') else None
                if not title:
                    json_response(self, {'ok': False, 'error': 'Title required'}, status=400)
                    return
                # Verify assignee exists
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT id FROM users WHERE id=? AND active=1', (assignee_id,))
                if not c.fetchone():
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Assignee not found'}, status=400)
                    return
                c.execute('INSERT INTO assigned_tasks (creator_id,assignee_id,title,description,priority,due_date,recur,remind_days) VALUES (?,?,?,?,?,?,?,?)',
                          (user['id'], assignee_id, title, description, priority, due_date, recur, remind_days))
                task_id = c.lastrowid
                conn.commit()
                # Fetch assignee details for email (do before close)
                c.execute('SELECT id, name, email FROM users WHERE id=?', (assignee_id,))
                assignee_row = c.fetchone()
                conn.close()
                # Fire task assignment email in background thread
                if assignee_id != user['id'] and assignee_row:
                    threading.Thread(
                        target=send_task_assignment_email,
                        args=(task_id, dict(user), dict(assignee_row), title, description, priority, due_date),
                        daemon=True
                    ).start()
                json_response(self, {'ok': True, 'id': task_id})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/update':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                task_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT creator_id, assignee_id, status FROM assigned_tasks WHERE id=?', (task_id,))
                row = c.fetchone()
                if not row:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not found'}, status=404)
                    return
                # Assignee can update status; creator can update everything
                is_creator  = row['creator_id'] == user['id']
                is_assignee = row['assignee_id'] == user['id']
                if not is_creator and not is_assignee:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Forbidden'}, status=403)
                    return
                fields, vals = ["updated_at=datetime('now')"], []
                new_status = data.get('status')
                if new_status and new_status in ('pending','in_progress','done'):
                    fields.append('status=?'); vals.append(new_status)
                    if new_status == 'done':
                        fields.append("completed_at=datetime('now')")
                    elif row['status'] == 'done':
                        fields.append('completed_at=NULL')
                if is_creator:
                    for f in ('title', 'description', 'priority', 'due_date'):
                        if f in data:
                            fields.append(f'{f}=?'); vals.append(data[f])
                vals.append(task_id)
                conn.execute(f'UPDATE assigned_tasks SET {", ".join(fields)} WHERE id=?', vals)
                conn.commit()
                # Fire task completion email if transitioning to done
                if new_status == 'done' and row['status'] != 'done':
                    c2 = conn.cursor()
                    c2.execute('SELECT id, name, email FROM users WHERE id=?', (row['creator_id'],))
                    creator_row = c2.fetchone()
                    c2.execute('SELECT id, name, email FROM users WHERE id=?', (row['assignee_id'],))
                    assignee_row = c2.fetchone()
                    c2.execute('SELECT title FROM assigned_tasks WHERE id=?', (task_id,))
                    task_row = c2.fetchone()
                    conn.close()
                    if creator_row and assignee_row and task_row and row['creator_id'] != row['assignee_id']:
                        completed_date = datetime.utcnow().strftime('%d %B %Y')
                        threading.Thread(
                            target=send_task_completion_email,
                            args=(task_id, dict(creator_row), dict(assignee_row), task_row['title'], completed_date),
                            daemon=True
                        ).start()
                else:
                    conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/delete':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                task_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT creator_id, assignee_id FROM assigned_tasks WHERE id=?', (task_id,))
                row = c.fetchone()
                if not row or (row['creator_id'] != user['id'] and row['assignee_id'] != user['id']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not authorised to delete this task'}, status=403)
                    return
                conn.execute('DELETE FROM assigned_tasks WHERE id=?', (task_id,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/archive':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                task_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT creator_id, assignee_id, status FROM assigned_tasks WHERE id=?', (task_id,))
                row = c.fetchone()
                if not row or (row['creator_id'] != user['id'] and row['assignee_id'] != user['id']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not authorised'}, status=403)
                    return
                conn.execute("UPDATE assigned_tasks SET archived=1 WHERE id=?", (task_id,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/tasks/unarchive':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                task_id = int(data.get('id', 0))
                conn = get_db()
                c = conn.cursor()
                c.execute('SELECT creator_id, assignee_id FROM assigned_tasks WHERE id=?', (task_id,))
                row = c.fetchone()
                if not row or (row['creator_id'] != user['id'] and row['assignee_id'] != user['id']):
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not authorised'}, status=403)
                    return
                conn.execute("UPDATE assigned_tasks SET archived=0 WHERE id=?", (task_id,))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/workflows/config':
            user = require_auth(self)
            if not user: return
            try:
                data = json.loads(body.decode())
                wf_id    = data.get('workflow_id', '')
                enabled  = int(bool(data.get('enabled', False)))
                run_hour = int(data.get('run_hour', 8))
                lead_days = int(data.get('lead_days', 30))
                conn = get_db()
                conn.execute("""INSERT INTO workflow_config (workflow_id,enabled,run_hour,lead_days,updated_at)
                    VALUES (?,?,?,?,datetime('now'))
                    ON CONFLICT(workflow_id) DO UPDATE SET
                        enabled=excluded.enabled, run_hour=excluded.run_hour,
                        lead_days=excluded.lead_days,
                        updated_at=excluded.updated_at""",
                    (wf_id, enabled, run_hour, lead_days))
                conn.commit()
                conn.close()
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/workflows/run':
            user = require_auth(self)
            if not user: return
            if user.get('role') not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Admin only'}, status=403)
                return
            try:
                data = json.loads(body.decode())
                wf_id = data.get('workflow_id', '')
                if wf_id not in WF_TEMPLATES and wf_id not in SCHEDULED_WORKFLOWS:
                    json_response(self, {'ok': False, 'error': 'Unknown workflow'}, status=400)
                    return
                def _run():
                    sent, failed = run_workflow(wf_id)
                    logging.info(f'[WF MANUAL] {wf_id}: {sent} sent, {failed} failed')
                threading.Thread(target=_run, daemon=True).start()
                json_response(self, {'ok': True, 'message': f'Workflow {wf_id} triggered in background'})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/smtp/save':
            user = require_auth(self)
            if not user: return
            if user.get('role') not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Admin only'}, status=403)
                return
            try:
                data = json.loads(body.decode())
                smtp_save(
                    host      = data.get('host', 'smtp.office365.com'),
                    port      = data.get('port', 587),
                    username  = data.get('username', ''),
                    password  = data.get('password', ''),
                    from_addr = data.get('from_addr', ''),
                    from_name = data.get('from_name', 'Rytech Support')
                )
                json_response(self, {'ok': True})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/smtp/test':
            user = require_auth(self)
            if not user: return
            if user.get('role') not in ('superadmin', 'admin'):
                json_response(self, {'ok': False, 'error': 'Admin only'}, status=403)
                return
            try:
                data = json.loads(body.decode())
                test_to = data.get('test_to', user.get('email', ''))
                ok, err = smtp_send(test_to, 'Rytech SummarAI -- SMTP Test', 'This is a test email from Rytech SummarAI. Your SMTP configuration is working correctly.')
                json_response(self, {'ok': ok, 'error': err})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        else:
            self.send_response(404)
            self.end_headers()
            self.wfile.write(b'Not found')

    # ── Proxy GET helper ──────────────────────────────────────────
    def _proxy_get(self, url, extra_headers=None):
        import re as _re
        url = _re.sub(r'[&?]_cb=\d+', '', url).rstrip('?&')
        try:
            headers = {'Accept': 'application/json', 'Cache-Control': 'no-cache'}
            if extra_headers:
                headers.update({k: v for k, v in extra_headers.items() if v})
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=20) as resp:
                body   = resp.read()
                status = resp.status
            if status == 204 or not body:
                body = b'{}'
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(body)))
            _send_cors(self)
            self.end_headers()
            self.wfile.write(body)
        except urllib.error.HTTPError as e:
            body = e.read()
            self.send_response(e.code)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(body)))
            _send_cors(self)
            self.end_headers()
            self.wfile.write(body)
        except Exception as ex:
            body = json.dumps({'error': str(ex)}).encode()
            self.send_response(500)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(body)))
            _send_cors(self)
            self.end_headers()
            self.wfile.write(body)


# ══════════════════════════════════════════════════════════════════
#  CSRF TOKEN STORE
# ══════════════════════════════════════════════════════════════════

_csrf_tokens = {}   # token -> {uid, issued}
_CSRF_TTL    = 7200

def csrf_issue(uid):
    tok = _secrets.token_hex(32)
    _csrf_tokens[tok] = {'uid': uid, 'issued': time.time()}
    # prune expired
    cutoff = time.time() - _CSRF_TTL
    for t in list(_csrf_tokens):
        if _csrf_tokens[t]['issued'] < cutoff:
            del _csrf_tokens[t]
    return tok

def csrf_verify(handler):
    """CSRF check. GET/HEAD/OPTIONS always pass.
    Only specific well-known integration endpoints are exempt -- each must be
    individually listed here. The blanket /proxy/ wildcard has been removed
    to avoid accidentally exempting future endpoints.
    """
    if handler.command in ('GET', 'HEAD', 'OPTIONS'):
        return True
    import urllib.parse as _up
    path = _up.urlparse(handler.path).path
    # Exempt: login + specific integration proxy/token endpoints
    # These are called by integration scripts that cannot carry a CSRF header
    # and are protected by require_auth() instead.
    _EXEMPT = {
        '/auth/login', '/auth/reauth',
        '/sp/token', '/sp/proxy', '/sp/create-folder', '/sp/test',
        '/proxy/action1/token',
        '/proxy/datto/token',
        '/proxy/xero/token',
        '/proxy/zoho/token',
        '/monzo-start', '/proxy/monzo/token', '/proxy/monzo/refresh',
        '/local/list-templates', '/local/copy-templates',
        '/oauth/tokens/save', '/oauth/tokens/delete', '/tasks/archive', '/tasks/unarchive', '/workflows/config', '/workflows/run', '/smtp/save', '/smtp/test', '/groq/key/save', '/groq/ask', '/groq/key',
    }
    if path in _EXEMPT:
        return True
    token = handler.headers.get('X-CSRF-Token', '')
    entry = _csrf_tokens.get(token)
    if not entry:
        return False
    if time.time() - entry['issued'] > _CSRF_TTL:
        del _csrf_tokens[token]
        return False
    return True

# ══════════════════════════════════════════════════════════════════
#  SERVER STATE & STARTUP
# ══════════════════════════════════════════════════════════════════

_http_server    = None
_monzo_pending  = {}   # state -> {tokens, error, ts}
_monzo_sessions = {}   # state -> {client_id, client_secret, redirect_uri, ts}



# ══════════════════════════════════════════════════════════════════
#  SMTP + EMAIL HELPERS
# ══════════════════════════════════════════════════════════════════

def smtp_load():
    """Load SMTP config from DB, returns dict or None."""
    try:
        conn = get_db()
        c = conn.cursor()
        c.execute("SELECT * FROM smtp_config WHERE id=1")
        row = c.fetchone()
        conn.close()
        if not row:
            return None
        d = dict(row)
        if d.get('password_enc'):
            try:
                d['password'] = decrypt_token(d['password_enc']) or ''
            except Exception:
                d['password'] = ''
        else:
            d['password'] = ''
        return d
    except Exception as e:
        logging.error(f'[SMTP] load error: {e}')
        return None


def smtp_save(host, port, username, password, from_addr, from_name):
    """Save SMTP config, encrypting the password."""
    password_enc = encrypt_token(password) if password else ''
    conn = get_db()
    conn.execute("""INSERT INTO smtp_config (id,host,port,username,password_enc,from_addr,from_name,updated_at)
        VALUES (1,?,?,?,?,?,?,datetime('now'))
        ON CONFLICT(id) DO UPDATE SET
            host=excluded.host, port=excluded.port, username=excluded.username,
            password_enc=excluded.password_enc, from_addr=excluded.from_addr,
            from_name=excluded.from_name, updated_at=excluded.updated_at""",
        (host, int(port), username, password_enc, from_addr, from_name))
    conn.commit()
    conn.close()


# ── App credential store ────────────────────────────────────────────────
# Stores integration secrets (client_secret, api_key, etc.) AES-256-GCM
# encrypted in the app_credentials table. Never in HTML source.

def cred_save(key, value):
    """Save an integration credential (encrypted). key is e.g. 'xero_client_secret'."""
    enc = encrypt_token(value) if value else ''
    conn = get_db()
    conn.execute("""INSERT INTO app_credentials (key, value_enc, updated_at)
        VALUES (?, ?, datetime('now'))
        ON CONFLICT(key) DO UPDATE SET value_enc=excluded.value_enc, updated_at=excluded.updated_at""",
        (key, enc))
    conn.commit()
    conn.close()

def cred_load(key):
    """Load and decrypt an integration credential. Returns '' if not set."""
    try:
        conn = get_db()
        row = conn.execute('SELECT value_enc FROM app_credentials WHERE key=?', (key,)).fetchone()
        conn.close()
        if not row or not row['value_enc']:
            return ''
        return decrypt_token(row['value_enc']) or ''
    except Exception as e:
        logging.error(f'[CRED] load error for {key}: {e}')
        return ''

def cred_load_all():
    """Load all credential keys (not values) for UI display."""
    try:
        conn = get_db()
        rows = conn.execute('SELECT key, updated_at FROM app_credentials').fetchall()
        conn.close()
        return {r['key']: {'set': True, 'updated_at': r['updated_at']} for r in rows}
    except Exception:
        return {}


# ─────────────────────────────────────────────────────────────────
#  NOTIFICATION HELPERS
# ─────────────────────────────────────────────────────────────────

def notif_create(user_id, ntype, title, body='', link=''):
    """Create a notification for a user."""
    try:
        conn = get_db()
        conn.execute(
            'INSERT INTO notifications (user_id, type, title, body, link) VALUES (?,?,?,?,?)',
            (user_id, ntype, title, body, link)
        )
        conn.commit()
        conn.close()
    except Exception as e:
        logging.error(f'[NOTIF] create error: {e}')


def notif_broadcast(ntype, title, body='', link='', roles=None):
    """Create a notification for all users (optionally filtered by role list)."""
    try:
        conn = get_db()
        if roles:
            rows = conn.execute(
                'SELECT id FROM users WHERE role IN ({})'.format(','.join('?' for _ in roles)),
                roles
            ).fetchall()
        else:
            rows = conn.execute('SELECT id FROM users').fetchall()
        for r in rows:
            conn.execute(
                'INSERT INTO notifications (user_id, type, title, body, link) VALUES (?,?,?,?,?)',
                (r['id'], ntype, title, body, link)
            )
        conn.commit()
        conn.close()
    except Exception as e:
        logging.error(f'[NOTIF] broadcast error: {e}')


def notif_check_contracts():
    """Push notifications for contracts expiring in ≤14 days. Called from scheduler."""
    try:
        v2 = load_v2_data()
        customers = v2.get('customers', [])
        contracts = v2.get('contracts', [])
        custmap   = {c.get('id'): c for c in customers}
        today     = datetime.utcnow().date()
        for ct in contracts:
            renewal_str = ct.get('renewal') or ct.get('endDate')
            if not renewal_str:
                continue
            for fmt in ('%Y-%m-%d', '%d/%m/%Y'):
                try:
                    end = datetime.strptime(str(renewal_str)[:10], fmt).date()
                    break
                except Exception:
                    end = None
            if not end:
                continue
            days = (end - today).days
            if 0 <= days <= 14:
                cust = custmap.get(ct.get('customerId'))
                company = cust.get('company', 'Unknown') if cust else 'Unknown'
                notif_broadcast(
                    'contract_expiry',
                    f'Contract expiring: {company}',
                    f'{ct.get("supportType","")} contract expires in {days} day(s) ({end.strftime("%d %b %Y")})',
                    link='contracts',
                    roles=['superadmin', 'admin', 'manager']
                )
    except Exception as e:
        logging.error(f'[NOTIF] contract check error: {e}')


def notif_check_overdue_tasks():
    """Push notifications for overdue tasks. Called from scheduler."""
    try:
        v2 = load_v2_data()
        today = datetime.utcnow().date()
        for tl in v2.get('taskLists', []):
            for t in tl.get('tasks', []):
                if t.get('done'):
                    continue
                due_str = t.get('due', '')
                if not due_str:
                    continue
                try:
                    due = datetime.strptime(due_str[:10], '%Y-%m-%d').date()
                except Exception:
                    continue
                if due < today:
                    assigned_to = t.get('assignedTo')
                    if assigned_to:
                        notif_create(
                            assigned_to,
                            'overdue_task',
                            f'Overdue task: {t.get("name","")}',
                            f'Due {due_str} in list "{tl.get("name","")}"',
                            link='tasks'
                        )
    except Exception as e:
        logging.error(f'[NOTIF] overdue task check error: {e}')


# ─────────────────────────────────────────────────────────────────
#  CLIENT ACTIVITY HELPERS
# ─────────────────────────────────────────────────────────────────

def client_activity_log(client_id, event_type, title, detail='', actor=''):
    """Append an entry to the client activity feed."""
    try:
        conn = get_db()
        conn.execute(
            'INSERT INTO client_activity (client_id, event_type, title, detail, actor) VALUES (?,?,?,?,?)',
            (str(client_id), event_type, title, detail, actor)
        )
        conn.commit()
        conn.close()
    except Exception as e:
        logging.error(f'[ACTIVITY] log error: {e}')


def ticket_event_log(ticket_id, event_type, detail='', actor=''):
    """Append an event to a ticket's timeline."""
    try:
        conn = get_db()
        conn.execute(
            'INSERT INTO ticket_events (ticket_id, event_type, detail, actor) VALUES (?,?,?,?)',
            (str(ticket_id), event_type, detail, actor)
        )
        conn.commit()
        conn.close()
    except Exception as e:
        logging.error(f'[TICKET EVENT] log error: {e}')


def smtp_send(to_addr, subject, body, cfg=None, html=False):
    """Send an email via M365 SMTP. Returns (ok, error_str).
    If html=True, body is treated as raw HTML; otherwise plain text with auto HTML wrap."""
    if cfg is None:
        cfg = smtp_load()
    if not cfg or not cfg.get('from_addr') or not cfg.get('username'):
        return False, 'SMTP not configured'
    try:
        msg = MIMEMultipart('alternative')
        msg['Subject'] = subject
        msg['From']    = f"{cfg.get('from_name','Rytech Support')} <{cfg['from_addr']}>"
        msg['To']      = to_addr
        if html:
            # Provide plain-text fallback by stripping tags
            import re as _re
            plain = _re.sub(r'<[^>]+>', '', body).strip()
            msg.attach(MIMEText(plain, 'plain', 'utf-8'))
            msg.attach(MIMEText(body, 'html', 'utf-8'))
        else:
            # Plain text
            msg.attach(MIMEText(body, 'plain', 'utf-8'))
            # HTML version (simple wrapping)
            html_body = '<pre style="font-family:Arial,sans-serif;font-size:14px;white-space:pre-wrap">' + body.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;') + '</pre>'
            msg.attach(MIMEText(html_body, 'html', 'utf-8'))
        context = ssl.create_default_context()
        with smtplib.SMTP(cfg['host'], int(cfg.get('port', 587)), timeout=20) as server:
            server.ehlo()
            server.starttls(context=context)
            server.ehlo()
            server.login(cfg['username'], cfg['password'])
            server.sendmail(cfg['from_addr'], to_addr, msg.as_string())
        return True, None
    except Exception as e:
        return False, str(e)


def wf_log(workflow_id, recipient, subject, status, error=None):
    try:
        conn = get_db()
        conn.execute("INSERT INTO workflow_log (workflow_id,recipient,subject,status,error) VALUES (?,?,?,?,?)",
                     (workflow_id, recipient, subject, status, error))
        conn.commit()
        conn.close()
    except Exception as e:
        logging.error(f'[WF LOG] {e}')


# ══════════════════════════════════════════════════════════════════
#  WORKFLOW ENGINE
# ══════════════════════════════════════════════════════════════════

WF_TEMPLATES = {
    'lost_followup_3m': {
        'subject': 'Checking In – {company}',
        'body': """Hi {first_name},

I hope you're doing well. It's been a little while since we last spoke and I wanted to reach out to see how things are going at {company}.

We've been busy expanding our services and I'd love to catch up and explore whether there might be a good fit for us to work together again.

Would you be open to a quick 15-minute call at your convenience?

Best regards,
Rytech Support"""
    },
    'lost_followup_6m': {
        'subject': 'Reconnecting – {company}',
        'body': """Hi {first_name},

I hope all is well with you and the team at {company}. It's been some time since we last connected and I wanted to get back in touch.

A lot has changed on our end -- we've enhanced our service offering and I think there could be real value in reconnecting to see if we can support you better this time around.

Would you be open to a brief conversation?

Best regards,
Rytech Support"""
    },
    'account_checkin': {
        'subject': 'Quarterly Check-In -- {company}',
        'body': """Hi {first_name},

I wanted to touch base and check how everything is going with your IT systems at {company}.

As part of our proactive support, we like to check in every quarter to make sure everything is running smoothly and to address any concerns before they become issues.

Is there anything on your radar that we should be aware of or could help with?

Best regards,
Rytech Support"""
    },
    'contract_expiry': {
        'subject': 'Your Support Contract Renewal -- {company}',
        'body': """Hi {first_name},

I'm writing to let you know that your current support contract with Rytech is due to expire on {expiry_date}.

We'd love to continue supporting {company} and ensure you have uninterrupted coverage. I'll be in touch shortly to discuss renewal options, but please don't hesitate to reach out in the meantime.

Thank you for your continued trust in Rytech.

Best regards,
Rytech Support"""
    },
    'task_assignment': {
        'subject': 'Task Assigned: {task_title}',
        'body': """Hi {first_name},

A task has been assigned to you in Rytech SummarAI.

Task:        {task_title}
Description: {task_description}
Due Date:    {due_date}
Priority:    {priority}
Assigned by: {creator_name}

Please log in to Rytech SummarAI to view and manage your tasks.

Best regards,
Rytech Support"""
    },
    'task_completion': {
        'subject': 'Task Completed: {task_title}',
        'body': """Hi {first_name},

The following task has been marked as completed in Rytech SummarAI.

Task:        {task_title}
Completed:   {completed_date}
Completed by:{assignee_name}

Best regards,
Rytech Support"""
    },
    'task_reminder': {
        'subject': '🔔 Task Reminder: {task_name} — due {due_date}',
        'body': """This is an automated reminder from Rytech SummarAI.

Task:     {task_name}
List:     {list_name}
Owner:    {owner}
Due:      {due_date}
Days Left: {days_left}

Please log in to Rytech SummarAI to review and complete this task.

Best regards,
Rytech SummarAI"""
    },
    'contract_reminder': {
        'subject': '📋 Contract Renewal Reminder: {company} — renews {renewal_date}',
        'body': """This is an automated contract renewal reminder from Rytech SummarAI.

Client:       {company}
Contract:     {support_type}
Renewal Date: {renewal_date}
Days Until Renewal: {days_left}

Please review and take appropriate action.

Best regards,
Rytech SummarAI"""
    },
}

# Workflow IDs that run on a schedule (others are event-driven)
SCHEDULED_WORKFLOWS = ['lost_followup_3m', 'lost_followup_6m', 'account_checkin', 'contract_expiry', 'task_reminder', 'contract_reminder', 'daily_digest']


def wf_get_config(workflow_id):
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM workflow_config WHERE workflow_id=?", (workflow_id,))
    row = c.fetchone()
    conn.close()
    return dict(row) if row else None


def wf_set_last_run(workflow_id):
    now = datetime.utcnow()
    cfg = wf_get_config(workflow_id)
    run_hour = cfg['run_hour'] if cfg else 8
    # Next run: same time tomorrow
    next_run = (now + timedelta(days=1)).replace(hour=run_hour, minute=0, second=0, microsecond=0)
    conn = get_db()
    conn.execute("""INSERT INTO workflow_config (workflow_id,last_run,next_run,run_hour)
        VALUES (?,datetime('now'),?,?)
        ON CONFLICT(workflow_id) DO UPDATE SET
            last_run=datetime('now'), next_run=excluded.next_run""",
        (workflow_id, next_run.strftime('%Y-%m-%d %H:%M:%S'), run_hour))
    conn.commit()
    conn.close()


def run_workflow(workflow_id, smtp_cfg=None):
    """Execute a single workflow, send emails, log results. Returns (sent, failed)."""
    if smtp_cfg is None:
        smtp_cfg = smtp_load()
    if not smtp_cfg or not smtp_cfg.get('from_addr'):
        logging.warning(f'[WF] {workflow_id}: SMTP not configured, skipping')
        return 0, 0

    v2 = load_v2_data()
    customers  = v2.get('customers', [])
    contracts  = v2.get('contracts', [])
    tmpl = WF_TEMPLATES.get(workflow_id)
    if not tmpl:
        return 0, 0

    targets = []  # list of dicts with keys for template

    import calendar as _cal

    def _parse_date(ds):
        if not ds:
            return None
        for fmt in ('%Y-%m-%d', '%d/%m/%Y', '%Y-%m-%dT%H:%M:%S.%f', '%Y-%m-%dT%H:%M:%S'):
            try:
                return datetime.strptime(str(ds)[:19], fmt).date()
            except Exception:
                continue
        return None

    def _add_months(d, months):
        month = (d.month - 1 + months) % 12 + 1
        year  = d.year + (d.month - 1 + months) // 12
        day   = min(d.day, _cal.monthrange(year, month)[1])
        return d.replace(year=year, month=month, day=day)

    today = datetime.utcnow().date()

    if workflow_id in ('lost_followup_3m', 'lost_followup_6m'):
        status = 'Lost - Follow Up 3M' if workflow_id == 'lost_followup_3m' else 'Lost - Follow Up 6M'
        months = 3 if workflow_id == 'lost_followup_3m' else 6
        for c in customers:
            if c.get('status') != status or not c.get('email'):
                continue
            status_date = _parse_date(c.get('statusDate'))
            if not status_date:
                logging.warning(f'[WF] {workflow_id}: skipping {c.get("company")} -- no statusDate')
                continue
            target = _add_months(status_date, months)
            if abs((today - target).days) <= 3:
                targets.append({
                    'to':         c['email'],
                    'company':    c.get('company', ''),
                    'first_name': c.get('name', '').split()[0] if c.get('name') else 'there',
                })

    elif workflow_id == 'account_checkin':
        # Fire on each 3-month anniversary of statusDate (±3 day window catches weekends)
        for c in customers:
            if c.get('status') != 'Active' or not c.get('email'):
                continue
            base_date = _parse_date(c.get('statusDate'))
            if not base_date:
                continue
            # Find the nearest upcoming 3-month anniversary
            months_elapsed = (today.year - base_date.year) * 12 + (today.month - base_date.month)
            # Round down to nearest multiple of 3
            nearest_quarter = (months_elapsed // 3) * 3
            if nearest_quarter < 3:
                continue  # not yet 3 months since becoming Active
            target = _add_months(base_date, nearest_quarter)
            if abs((today - target).days) <= 3:
                targets.append({
                    'to':         c['email'],
                    'company':    c.get('company', ''),
                    'first_name': c.get('name', '').split()[0] if c.get('name') else 'there',
                })

    elif workflow_id == 'contract_expiry':
        # Fire once, on the day exactly 30 days before the renewal date (±3 day window)
        for ct in contracts:
            renewal_str = ct.get('renewal') or ct.get('endDate')
            end = _parse_date(renewal_str)
            if not end:
                continue
            target_notify = end - timedelta(days=30)
            if abs((today - target_notify).days) <= 3:
                cust = next((c for c in customers if c.get('id') == ct.get('customerId')), None)
                if cust and cust.get('email'):
                    targets.append({
                        'to':          cust['email'],
                        'company':     cust.get('company', ''),
                        'first_name':  cust.get('name', '').split()[0] if cust.get('name') else 'there',
                        'expiry_date': end.strftime('%d %B %Y'),
                    })

    # ── Task due-date reminders ────────────────────────────────────────────
    elif workflow_id == 'task_reminder':
        # Check assigned_tasks table (DB-backed tasks with assignee emails)
        conn_r = get_db()
        db_tasks = conn_r.execute('''
            SELECT t.id, t.title, t.due_date, t.remind_days,
                   u.name as assignee_name, u.email as assignee_email
            FROM assigned_tasks t
            JOIN users u ON u.id = t.assignee_id
            WHERE t.status != 'done' AND t.due_date IS NOT NULL AND t.remind_days IS NOT NULL
        ''').fetchall()
        conn_r.close()
        for row in db_tasks:
            due_date_r = _parse_date(row['due_date'])
            if not due_date_r:
                continue
            days_left = (due_date_r - today).days
            remind = int(row['remind_days'])
            logging.info(f'[WF] task_reminder DB check: "{row["title"]}" due {due_date_r}, days_left={days_left}, remind={remind}')
            if days_left == remind and row['assignee_email']:
                targets.append({
                    'task_name': row['title'],
                    'list_name': '',
                    'owner':     row['assignee_name'],
                    'due_date':  due_date_r.strftime('%d %B %Y'),
                    'days_left': str(days_left),
                    '_to_email': row['assignee_email'],
                    '_to_name':  row['assignee_name'],
                })
        # Also check v2 taskLists
        # Look up all users by name for email resolution
        conn_u = get_db()
        user_rows = conn_u.execute('SELECT name, email FROM users').fetchall()
        conn_u.close()
        user_email_map = {u['name'].strip().lower(): u['email'] for u in user_rows if u['name'] and u['email']}
        task_lists = v2.get('taskLists', [])
        for tl in task_lists:
            for task in tl.get('tasks', []):
                if task.get('done'):
                    continue
                remind_days = task.get('remind_days')
                due_str     = task.get('due', '')
                task_name   = task.get('name') or task.get('title', 'Unnamed task')
                owner_name  = task.get('owner', '')
                if not remind_days or not due_str:
                    continue
                due_date = _parse_date(due_str)
                if not due_date:
                    continue
                days_left = (due_date - today).days
                remind = int(remind_days)
                logging.info(f'[WF] task_reminder v2 check: "{task_name}" due {due_date}, days_left={days_left}, remind={remind}, owner="{owner_name}"')
                # Fire when days_left matches remind_days exactly, or within 1 day window
                if abs(days_left - remind) <= 1:
                    # Try to resolve owner email from users table
                    owner_email = user_email_map.get(owner_name.strip().lower(), '')
                    # Fall back to servicedesk if no match
                    to_email = owner_email or 'servicedesk@rytech-support.com'
                    to_name  = owner_name or 'Team'
                    targets.append({
                        'task_name': task_name,
                        'list_name': tl.get('name', ''),
                        'owner':     owner_name or 'Unassigned',
                        'due_date':  due_date.strftime('%d %B %Y'),
                        'days_left': str(days_left),
                        '_to_email': to_email,
                        '_to_name':  to_name,
                    })
                    logging.info(f'[WF] task_reminder: queued reminder for "{task_name}" → {to_email}')

    # ── Contract renewal reminders (configurable lead time) ────────────────
    elif workflow_id == 'daily_digest':
        # Daily digest: summary of open tasks, expiring contracts, stale tickets
        INTERNAL_RECIPIENT = 'servicedesk@rytech-support.com'
        task_lists = v2.get('taskLists', [])
        all_tasks  = []
        for tl in task_lists:
            for t in tl.get('tasks', []):
                if not t.get('done'):
                    all_tasks.append({**t, 'list_name': tl.get('name', '')})
        overdue_tasks = [t for t in all_tasks if t.get('due') and _parse_date(t.get('due','')) and _parse_date(t.get('due','')) < today]
        upcoming_tasks = [t for t in all_tasks if t.get('due') and _parse_date(t.get('due','')) and 0 <= (_parse_date(t.get('due',''))-today).days <= 7]

        # Contracts expiring this month
        expiring = []
        for ct in contracts:
            renewal_str = ct.get('renewal') or ct.get('endDate')
            end = _parse_date(renewal_str)
            if end and 0 <= (end - today).days <= 30:
                custmap = {c.get('id'): c for c in customers}
                cust = custmap.get(ct.get('customerId'))
                expiring.append({
                    'company': cust.get('company','Unknown') if cust else 'Unknown',
                    'type': ct.get('supportType',''),
                    'date': end.strftime('%d %B %Y'),
                    'days': (end - today).days,
                })

        if not all_tasks and not expiring:
            wf_set_last_run(workflow_id)
            return 0, 0

        # Build email body
        lines = ['<div style="font-family:sans-serif;color:#222;max-width:600px;">']
        lines.append('<h2 style="color:#008CBB;margin-bottom:4px;">☀️ Rytech Daily Digest</h2>')
        lines.append(f'<p style="color:#666;margin-top:0;">{today.strftime("%A, %d %B %Y")}</p><hr/>')

        # Open tasks summary
        lines.append(f'<h3>📌 Open Tasks ({len(all_tasks)} total)</h3>')
        if overdue_tasks:
            lines.append(f'<p style="color:#c00;font-weight:bold;">⚠️ {len(overdue_tasks)} overdue task(s):</p><ul>')
            for t in overdue_tasks[:5]:
                lines.append(f'<li><b>{t.get("name","")}</b> — due {t.get("due","")} [{t.get("list_name","")}]</li>')
            lines.append('</ul>')
        if upcoming_tasks:
            lines.append(f'<p>📅 {len(upcoming_tasks)} task(s) due in the next 7 days:</p><ul>')
            for t in upcoming_tasks[:5]:
                lines.append(f'<li><b>{t.get("name","")}</b> — due {t.get("due","")} [{t.get("list_name","")}]</li>')
            lines.append('</ul>')

        # Expiring contracts
        if expiring:
            lines.append(f'<h3>📄 Contracts Expiring This Month ({len(expiring)})</h3><ul>')
            for e in expiring:
                lines.append(f'<li><b>{e["company"]}</b> ({e["type"]}) — {e["date"]} <span style="color:#c00;">({e["days"]} days)</span></li>')
            lines.append('</ul>')

        lines.append('<hr/><p style="color:#999;font-size:12px;">Rytech SummarAI Daily Digest · summarai.rytech-support.com</p></div>')
        body = '\n'.join(lines)

        subject = f'Rytech Daily Digest — {today.strftime("%d %B %Y")}'
        ok, err = smtp_send(INTERNAL_RECIPIENT, subject, body, cfg=smtp_cfg, html=True)
        wf_log(workflow_id, INTERNAL_RECIPIENT, subject, 'sent' if ok else 'failed', err)
        wf_set_last_run(workflow_id)
        return (1, 0) if ok else (0, 1)


        conn_r = get_db()
        lead_row = conn_r.execute(
            "SELECT lead_days FROM workflow_config WHERE workflow_id='contract_reminder'"
        ).fetchone()
        conn_r.close()
        lead_days = int(lead_row['lead_days']) if lead_row and lead_row['lead_days'] else 30
        custmap   = {c.get('id'): c for c in customers}
        for ct in contracts:
            renewal_str = ct.get('renewal') or ct.get('endDate')
            end = _parse_date(renewal_str)
            if not end:
                continue
            days_left = (end - today).days
            # Fire on the configured lead day (±1 day window)
            if abs(days_left - lead_days) <= 1:
                cust = custmap.get(ct.get('customerId'))
                company = cust.get('company', 'Unknown') if cust else 'Unknown'
                targets.append({
                    'company':      company,
                    'support_type': ct.get('supportType', ''),
                    'renewal_date': end.strftime('%d %B %Y'),
                    'days_left':    str(days_left),
                })

    # ── Recurring task cloning ──────────────────────────────────────────────
    # When a recurring task's due date passes, clone it with the next due date
    if workflow_id in ('task_reminder', 'contract_reminder'):
        # Piggyback: also advance any overdue recurring tasks
        task_lists = v2.get('taskLists', [])
        changed = False
        for tl in task_lists:
            for task in tl.get('tasks', []):
                recur = task.get('recur', '')
                due_str = task.get('due', '')
                if not recur or not due_str or not task.get('done'):
                    continue
                due_date = _parse_date(due_str)
                if not due_date or due_date > today:
                    continue
                # Compute next due date
                delta_map = {
                    'daily':        timedelta(days=1),
                    'weekly':       timedelta(weeks=1),
                    'fortnightly':  timedelta(weeks=2),
                }
                if recur in delta_map:
                    next_due = due_date + delta_map[recur]
                elif recur == 'monthly':
                    next_due = _add_months(due_date, 1)
                elif recur == 'quarterly':
                    next_due = _add_months(due_date, 3)
                else:
                    continue
                # Clone the task (new id, reset done, advance due date)
                import copy as _copy
                new_task = _copy.deepcopy(task)
                new_task['id'] = int(datetime.utcnow().timestamp() * 1000)
                new_task['done'] = False
                new_task['due'] = next_due.strftime('%Y-%m-%d')
                tl['tasks'].append(new_task)
                changed = True
                logging.info(f'[WF] recurring task cloned: "{task.get("name")}" → next due {next_due}')
        if changed:
            # Reload full v2, merge updated taskLists, save back atomically
            full_v2 = load_v2_data()
            full_v2['taskLists'] = task_lists
            if save_v2_data(full_v2):
                logging.info('[WF] recurring task clones saved to v2_data.json')
            else:
                logging.error('[WF] failed to save recurring task clones')

    # ── Standard scheduled-workflow email dispatch ───────────────────────────
    # task_reminder sends to assignee/owner email; contract_reminder sends to servicedesk
    if workflow_id in ('task_reminder', 'contract_reminder'):
        INTERNAL_RECIPIENT = 'servicedesk@rytech-support.com'
        sent = failed = 0
        if not targets:
            logging.info(f'[WF] {workflow_id}: no matching targets found — no emails sent')
        for t in targets:
            recipient = t.get('_to_email') or INTERNAL_RECIPIENT
            try:
                subject  = tmpl['subject'].format(**{k: v for k, v in t.items() if not k.startswith('_')})
                body_txt = tmpl['body'].format(**{k: v for k, v in t.items() if not k.startswith('_')})
            except KeyError as fe:
                logging.error(f'[WF] {workflow_id}: template key error {fe} for task "{t.get("task_name")}"')
                failed += 1
                continue
            ok, err = smtp_send(recipient, subject, body_txt, cfg=smtp_cfg)
            wf_log(workflow_id, recipient, subject, 'sent' if ok else 'failed', err)
            if ok:
                sent += 1
                logging.info(f'[WF] {workflow_id}: reminder sent to {recipient} ({t.get("task_name","")})')
            else:
                failed += 1
                logging.error(f'[WF] {workflow_id}: failed to send to {recipient}: {err}')
        wf_set_last_run(workflow_id)
        return sent, failed

    INTERNAL_RECIPIENT = 'servicedesk@rytech-support.com'
    sent = failed = 0
    for t in targets:
        subject = tmpl['subject'].format(**{k: t.get(k, '') for k in t})
        body    = tmpl['body'].format(**{k: t.get(k, '') for k in t})
        # Prefix body with customer context so servicedesk knows who it's about
        internal_body = f"[Customer: {t.get('company','Unknown')} | Contact: {t.get('to','')}]\n\n" + body
        ok, err = smtp_send(INTERNAL_RECIPIENT, subject, internal_body, cfg=smtp_cfg)
        wf_log(workflow_id, INTERNAL_RECIPIENT, subject, 'sent' if ok else 'failed', err)
        if ok:
            sent += 1
            logging.info(f'[WF] {workflow_id}: sent to {INTERNAL_RECIPIENT} (re: {t["to"]})')
        else:
            failed += 1
            logging.error(f'[WF] {workflow_id}: failed: {err}')

    wf_set_last_run(workflow_id)
    return sent, failed


def send_task_assignment_email(task_id, creator, assignee, title, description, priority, due_date):
    """Send task assignment email. Called from /tasks/create."""
    smtp_cfg = smtp_load()
    if not smtp_cfg or not smtp_cfg.get('from_addr'):
        return
    # Check workflow enabled
    cfg = wf_get_config('task_assignment')
    if cfg and not cfg.get('enabled', 0):
        return
    if not assignee.get('email'):
        logging.warning(f'[WF] task_assignment: assignee has no email, skipping')
        return
    first_name = (assignee.get('name') or 'there').split()[0]
    due_str = due_date or 'Not set'
    tmpl = WF_TEMPLATES['task_assignment']
    subject = tmpl['subject'].format(task_title=title)
    body = tmpl['body'].format(
        first_name=first_name, task_title=title,
        task_description=description or 'No description provided.',
        due_date=due_str, priority=priority.capitalize(),
        creator_name=creator.get('name', 'A colleague')
    )
    ok, err = smtp_send(assignee['email'], subject, body, cfg=smtp_cfg)
    wf_log('task_assignment', assignee['email'], subject, 'sent' if ok else 'failed', err)


def send_task_completion_email(task_id, creator, assignee, title, completed_date):
    """Send task completion email. Called from /tasks/update when status->done."""
    smtp_cfg = smtp_load()
    if not smtp_cfg or not smtp_cfg.get('from_addr'):
        return
    cfg = wf_get_config('task_completion')
    if cfg and not cfg.get('enabled', 0):
        return
    if not creator.get('email'):
        logging.warning(f'[WF] task_completion: creator has no email, skipping')
        return
    first_name = (creator.get('name') or 'there').split()[0]
    tmpl = WF_TEMPLATES['task_completion']
    subject = tmpl['subject'].format(task_title=title)
    body = tmpl['body'].format(
        first_name=first_name, task_title=title,
        completed_date=completed_date or datetime.utcnow().strftime('%d %B %Y'),
        assignee_name=assignee.get('name', 'A team member')
    )
    ok, err = smtp_send(creator['email'], subject, body, cfg=smtp_cfg)
    wf_log('task_completion', creator['email'], subject, 'sent' if ok else 'failed', err)


# ══════════════════════════════════════════════════════════════════
#  DAILY SCHEDULER THREAD
# ══════════════════════════════════════════════════════════════════

def scheduler_loop():
    """Background thread -- checks every 5 minutes if any scheduled workflow is due."""
    logging.info('[SCHEDULER] Started')
    while True:
        try:
            now = datetime.utcnow()
            smtp_cfg = smtp_load()
            conn = get_db()
            c = conn.cursor()
            for wf_id in SCHEDULED_WORKFLOWS:
                c.execute("SELECT * FROM workflow_config WHERE workflow_id=?", (wf_id,))
                row = c.fetchone()
                if not row or not row['enabled']:
                    continue
                run_hour = row['run_hour'] if row else 8
                last_run = row['last_run'] if row else None
                # Check if we've already run today
                if last_run:
                    try:
                        last_dt = datetime.strptime(last_run, '%Y-%m-%d %H:%M:%S')
                        if last_dt.date() == now.date():
                            continue  # already ran today
                    except Exception:
                        pass
                # Check if we've passed the scheduled run hour
                if now.hour >= run_hour:
                    logging.info(f'[SCHEDULER] Running workflow: {wf_id}')
                    conn.close()
                    try:
                        sent, failed = run_workflow(wf_id, smtp_cfg)
                        logging.info(f'[SCHEDULER] {wf_id} complete: {sent} sent, {failed} failed')
                    except Exception as e:
                        logging.error(f'[SCHEDULER] {wf_id} error: {e}')
                    conn = get_db()
                    c = conn.cursor()
            conn.close()
            # Notification checks (run every scheduler cycle regardless of workflow config)
            try:
                notif_check_contracts()
            except Exception as e:
                logging.error(f'[SCHEDULER] notif_check_contracts error: {e}')
            try:
                notif_check_overdue_tasks()
            except Exception as e:
                logging.error(f'[SCHEDULER] notif_check_overdue_tasks error: {e}')
        except Exception as e:
            logging.error(f'[SCHEDULER] loop error: {e}')
        time.sleep(300)  # check every 5 minutes


def main():
    global _http_server

    port = int(os.environ.get('RYTECH_PORT', 8765))

    # Initialise auth database
    init_db()

    # Start workflow scheduler background thread
    _sched = threading.Thread(target=scheduler_loop, daemon=True, name='WFScheduler')
    _sched.start()

    # Load app content
    with open(HTML_FILE, 'rb') as f:
        RytechHandler.html_content = f.read()
    RytechHandler.config = load_config()

    cfg  = load_config()
    v2   = load_v2_data()
    mtgs = load_meetings()

    print('=' * 56)
    print('  Rytech SummarAI  v6.5.0  [VPS + Auth]')
    print('=' * 56)
    print(f'  Listening on port : {port}')
    print(f'  API key           : {"Loaded" if cfg.get("api_key","").startswith("sk-ant-") else "Not set"}')
    print(f'  Meetings          : {len(mtgs)}')
    print(f'  Customers         : {len(v2.get("customers", []))}')
    print(f'  Contracts         : {len(v2.get("contracts", []))}')
    print(f'  Auth DB           : {DB_FILE}')
    print('=' * 56)

    _http_server = HTTPServer(('0.0.0.0', port), RytechHandler)
    _http_server.serve_forever()


if __name__ == '__main__':
    main()
