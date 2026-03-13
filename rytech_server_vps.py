"""
Rytech SummarAI - VPS Server
Author: Daniel Ryan
Version: 3.2.0 (VPS + Multi-User Auth)
"""

import sys, os, json, shutil, threading, time, socket, mimetypes, logging
import smtplib, ssl
import threading
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
        CREATE TABLE IF NOT EXISTS note_shares (
            id                  INTEGER PRIMARY KEY AUTOINCREMENT,
            note_id             INTEGER NOT NULL,
            shared_with_user_id INTEGER NOT NULL,
            shared_by_user_id   INTEGER NOT NULL,
            created_at          TEXT NOT NULL DEFAULT (datetime('now')),
            FOREIGN KEY(note_id)             REFERENCES notes(id) ON DELETE CASCADE,
            FOREIGN KEY(shared_with_user_id) REFERENCES users(id) ON DELETE CASCADE,
            UNIQUE(note_id, shared_with_user_id)
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
        CREATE TABLE IF NOT EXISTS user_prefs (
            user_id         INTEGER PRIMARY KEY,
            prefs_json      TEXT NOT NULL DEFAULT '{}',
            updated_at      TEXT NOT NULL DEFAULT (datetime('now')),
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
    <img src="data:image/png;base64,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" alt="Rytech Support" style="width:200px;height:auto;display:block;margin:0 auto 12px;">
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
            # Own notes
            c.execute('SELECT n.*, 0 as shared_with_me, NULL as shared_by_name FROM notes n WHERE n.owner_id=? ORDER BY n.pinned DESC, n.updated_at DESC', (user['id'],))
            own_notes = [dict(r) for r in c.fetchall()]
            # Notes shared with this user
            c.execute('''
                SELECT n.*, 1 as shared_with_me, u.name as shared_by_name
                FROM notes n
                JOIN note_shares ns ON ns.note_id = n.id
                JOIN users u ON u.id = ns.shared_by_user_id
                WHERE ns.shared_with_user_id = ?
                ORDER BY n.pinned DESC, n.updated_at DESC
            ''', (user['id'],))
            shared_notes = [dict(r) for r in c.fetchall()]
            # Get share lists for own notes
            own_ids = [n['id'] for n in own_notes]
            shares_map = {}
            if own_ids:
                placeholders = ','.join('?' * len(own_ids))
                c.execute(f'''
                    SELECT ns.note_id, u.id, u.name, u.email
                    FROM note_shares ns JOIN users u ON u.id = ns.shared_with_user_id
                    WHERE ns.note_id IN ({placeholders})
                ''', own_ids)
                for row in c.fetchall():
                    shares_map.setdefault(row['note_id'], []).append({
                        'id': row['id'], 'name': row['name'], 'email': row['email']
                    })
            for n in own_notes:
                n['shared_with'] = shares_map.get(n['id'], [])
                n['shared_with_me'] = 0
            for n in shared_notes:
                n['shared_with'] = []
            conn.close()
            all_notes = own_notes + shared_notes
            json_response(self, {'ok': True, 'notes': all_notes})
            return

        # ── Notes: shares list for a note ───────────────────────────
        if path == '/notes/shares':
            user = require_auth(self)
            if not user: return
            note_id = int(qs.get('note_id', ['0'])[0])
            conn = get_db()
            c = conn.cursor()
            c.execute('SELECT owner_id FROM notes WHERE id=?', (note_id,))
            row = c.fetchone()
            if not row or row['owner_id'] != user['id']:
                conn.close()
                json_response(self, {'ok': False, 'error': 'Not authorised'}, status=403)
                return
            c.execute('SELECT u.id, u.name, u.email FROM note_shares ns JOIN users u ON u.id=ns.shared_with_user_id WHERE ns.note_id=?', (note_id,))
            shares = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'shares': shares})
            return

        # ── Users: list for share picker ─────────────────────────────
        if path == '/users/list':
            user = require_auth(self)
            if not user: return
            conn = get_db()
            c = conn.cursor()
            c.execute("SELECT id, name, email, role FROM users WHERE id != ? ORDER BY name", (user['id'],))
            users = [dict(r) for r in c.fetchall()]
            conn.close()
            json_response(self, {'ok': True, 'users': users})
            return

        # ── User notification prefs (GET) ────────────────────────────
        if path == '/user/prefs':
            user = require_auth(self)
            if not user: return
            prefs = user_prefs_get(user['id'])
            prefs.setdefault('digest_enabled', False)
            prefs.setdefault('note_share_email', True)
            json_response(self, {'ok': True, 'prefs': prefs})
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
                if not row:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not found'}, status=404)
                    return
                # Allow owner OR shared users to edit
                if row['owner_id'] != user['id']:
                    c.execute('SELECT id FROM note_shares WHERE note_id=? AND shared_with_user_id=?', (note_id, user['id']))
                    if not c.fetchone():
                        conn.close()
                        json_response(self, {'ok': False, 'error': 'Not authorised'}, status=403)
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

        # ── User notification prefs (POST) ───────────────────────────
        if self.path == '/user/prefs':
            user = require_auth(self)
            if not user: return
            try:
                data  = json.loads(body.decode())
                prefs = user_prefs_get(user['id'])
                # Only allow known pref keys
                if 'digest_enabled' in data:
                    prefs['digest_enabled'] = bool(data['digest_enabled'])
                if 'note_share_email' in data:
                    prefs['note_share_email'] = bool(data['note_share_email'])
                user_prefs_set(user['id'], prefs)
                json_response(self, {'ok': True, 'prefs': prefs})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Notes: share / unshare ───────────────────────────────
        elif self.path == '/notes/share':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                note_id = int(data.get('note_id', 0))
                with_id = int(data.get('user_id', 0))
                if not note_id or not with_id:
                    json_response(self, {'ok': False, 'error': 'Missing note_id or user_id'}, status=400)
                    return
                conn = get_db()
                c = conn.cursor()
                # Only owner can share
                c.execute('SELECT owner_id FROM notes WHERE id=?', (note_id,))
                row = c.fetchone()
                if not row or row['owner_id'] != user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not authorised'}, status=403)
                    return
                if with_id == user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Cannot share with yourself'}, status=400)
                    return
                c.execute('INSERT OR IGNORE INTO note_shares (note_id, shared_with_user_id, shared_by_user_id) VALUES (?,?,?)',
                          (note_id, with_id, user['id']))
                conn.commit()
                # Return updated share list
                c.execute('SELECT u.id, u.name, u.email FROM note_shares ns JOIN users u ON u.id=ns.shared_with_user_id WHERE ns.note_id=?', (note_id,))
                shares = [dict(r) for r in c.fetchall()]
                conn.close()
                # Send email notification to recipient (non-blocking)
                threading.Thread(
                    target=send_note_share_email,
                    args=(note_id, with_id, user['id']),
                    daemon=True
                ).start()
                json_response(self, {'ok': True, 'shares': shares})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        elif self.path == '/notes/unshare':
            user = require_auth(self)
            if not user: return
            try:
                data    = json.loads(body.decode())
                note_id = int(data.get('note_id', 0))
                with_id = int(data.get('user_id', 0))
                conn = get_db()
                c = conn.cursor()
                # Only owner can unshare
                c.execute('SELECT owner_id FROM notes WHERE id=?', (note_id,))
                row = c.fetchone()
                if not row or row['owner_id'] != user['id']:
                    conn.close()
                    json_response(self, {'ok': False, 'error': 'Not authorised'}, status=403)
                    return
                c.execute('DELETE FROM note_shares WHERE note_id=? AND shared_with_user_id=?', (note_id, with_id))
                conn.commit()
                c.execute('SELECT u.id, u.name, u.email FROM note_shares ns JOIN users u ON u.id=ns.shared_with_user_id WHERE ns.note_id=?', (note_id,))
                shares = [dict(r) for r in c.fetchall()]
                conn.close()
                json_response(self, {'ok': True, 'shares': shares})
            except Exception as e:
                json_response(self, {'ok': False, 'error': str(e)}, status=400)
            return

        # ── Notes: list shares for a note ────────────────────────────
        # ── Users: list all users (for share picker) ─────────────────
        # (handled in GET section below)

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

def user_prefs_get(user_id):
    """Return notification prefs dict for a user."""
    conn = get_db()
    row = conn.execute('SELECT prefs_json FROM user_prefs WHERE user_id=?', (user_id,)).fetchone()
    conn.close()
    if row:
        try:
            return json.loads(row['prefs_json'])
        except Exception:
            return {}
    return {}

def user_prefs_set(user_id, prefs):
    """Save notification prefs dict for a user."""
    conn = get_db()
    conn.execute('''
        INSERT INTO user_prefs (user_id, prefs_json, updated_at)
        VALUES (?, ?, datetime('now'))
        ON CONFLICT(user_id) DO UPDATE SET prefs_json=excluded.prefs_json, updated_at=excluded.updated_at
    ''', (user_id, json.dumps(prefs)))
    conn.commit()
    conn.close()

def send_note_share_email(note_id, shared_with_user_id, shared_by_user_id, smtp_cfg=None):
    """Send an email to a user when a note is shared with them."""
    try:
        if smtp_cfg is None:
            smtp_cfg = smtp_load()
        if not smtp_cfg or not smtp_cfg.get('from_addr'):
            return
        conn = get_db()
        recipient_row = conn.execute('SELECT name, email FROM users WHERE id=?', (shared_with_user_id,)).fetchone()
        sharer_row    = conn.execute('SELECT name FROM users WHERE id=?', (shared_by_user_id,)).fetchone()
        note_row      = conn.execute('SELECT title FROM notes WHERE id=?', (note_id,)).fetchone()
        conn.close()
        if not recipient_row or not sharer_row or not note_row:
            return
        # Check recipient has note share emails enabled (default: on)
        prefs = user_prefs_get(shared_with_user_id)
        if prefs.get('note_share_email', True) is False:
            return
        to_email   = recipient_row['email']
        to_name    = recipient_row['name'] or to_email
        from_name  = sharer_row['name'] or 'A colleague'
        note_title = note_row['title'] or 'Untitled'
        subject = f'{from_name} shared a note with you — {note_title}'
        body = f'''<div style="font-family:sans-serif;color:#222;max-width:600px;">
  <h2 style="color:#008CBB;margin-bottom:4px;">👥 Note Shared With You</h2>
  <p style="color:#666;margin-top:0;">{datetime.now().strftime("%A, %d %B %Y")}</p>
  <hr/>
  <p>Hi {to_name},</p>
  <p><b>{from_name}</b> has shared a note with you in <b>Rytech SummarAI</b>:</p>
  <div style="background:#f4f8fb;border-left:4px solid #008CBB;padding:12px 16px;border-radius:6px;margin:16px 0;">
    <b style="font-size:1.05em;">📝 {note_title}</b>
  </div>
  <p>Log in to Rytech SummarAI to view and edit this note.</p>
  <hr/>
  <p style="color:#999;font-size:12px;">Rytech SummarAI · summarai.rytech-support.com<br>
  You are receiving this because a note was shared with your account.<br>
  To stop these emails, update your notification preferences in your profile.</p>
</div>'''
        smtp_send(to_email, subject, body, cfg=smtp_cfg, html=True)
    except Exception as e:
        logging.warning(f'[NOTE SHARE EMAIL] Failed: {e}')

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
        # Daily digest: send one email per user who has digest_enabled=True
        # Each user gets their own tasks assigned to them
        conn_d = get_db()
        all_users = [dict(r) for r in conn_d.execute(
            "SELECT id, name, email FROM users WHERE active=1"
        ).fetchall()]
        conn_d.close()

        # Contracts expiring this month (shared across all digests)
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

        sent_count, fail_count = 0, 0
        subject = f'Rytech Daily Digest — {today.strftime("%d %B %Y")}'

        for u in all_users:
            prefs = user_prefs_get(u['id'])
            if not prefs.get('digest_enabled', False):
                continue
            if not u.get('email'):
                continue

            # Get tasks assigned to this user
            conn_t = get_db()
            user_tasks_rows = conn_t.execute(
                "SELECT * FROM assigned_tasks WHERE assigned_to=? AND done=0",
                (u['id'],)
            ).fetchall()
            conn_t.close()
            user_tasks = [dict(r) for r in user_tasks_rows]

            overdue_tasks  = [t for t in user_tasks if t.get('due_date') and _parse_date(t.get('due_date','')) and _parse_date(t.get('due_date','')) < today]
            upcoming_tasks = [t for t in user_tasks if t.get('due_date') and _parse_date(t.get('due_date','')) and 0 <= (_parse_date(t.get('due_date',''))-today).days <= 7]

            # Also get notes shared with this user
            conn_n = get_db()
            shared_notes = [dict(r) for r in conn_n.execute('''
                SELECT n.title, u2.name as shared_by
                FROM note_shares ns
                JOIN notes n ON n.id = ns.note_id
                JOIN users u2 ON u2.id = ns.shared_by_user_id
                WHERE ns.shared_with_user_id = ?
                ORDER BY ns.created_at DESC LIMIT 5
            ''', (u['id'],)).fetchall()]
            conn_n.close()

            if not user_tasks and not expiring and not shared_notes:
                continue

            # Build personalised email body
            blines = [f'<div style="font-family:sans-serif;color:#222;max-width:600px;">']
            blines.append('<h2 style="color:#008CBB;margin-bottom:4px;">☀️ Rytech Daily Digest</h2>')
            blines.append(f'<p style="color:#666;margin-top:0;">{today.strftime("%A, %d %B %Y")}</p>')
            blines.append(f'<p>Hi {u["name"] or u["email"]},</p><hr/>')

            # Assigned tasks
            if user_tasks:
                blines.append(f'<h3>📌 Your Open Tasks ({len(user_tasks)} total)</h3>')
                if overdue_tasks:
                    blines.append(f'<p style="color:#c00;font-weight:bold;">⚠️ {len(overdue_tasks)} overdue:</p><ul>')
                    for t in overdue_tasks[:5]:
                        blines.append(f'<li><b>{t.get("title","")}</b> — due {t.get("due_date","")} [{t.get("priority","")}]</li>')
                    blines.append('</ul>')
                if upcoming_tasks:
                    blines.append(f'<p>📅 {len(upcoming_tasks)} due in next 7 days:</p><ul>')
                    for t in upcoming_tasks[:5]:
                        blines.append(f'<li><b>{t.get("title","")}</b> — due {t.get("due_date","")} [{t.get("priority","")}]</li>')
                    blines.append('</ul>')
            else:
                blines.append('<p style="color:#666;">✅ No open tasks assigned to you.</p>')

            # Notes shared with this user
            if shared_notes:
                blines.append(f'<h3>📝 Notes Shared With You ({len(shared_notes)})</h3><ul>')
                for sn in shared_notes:
                    blines.append(f'<li><b>{sn["title"] or "Untitled"}</b> — shared by {sn["shared_by"]}</li>')
                blines.append('</ul>')

            # Expiring contracts (shown to all digest recipients)
            if expiring:
                blines.append(f'<h3>📄 Contracts Expiring This Month ({len(expiring)})</h3><ul>')
                for e in expiring:
                    blines.append(f'<li><b>{e["company"]}</b> ({e["type"]}) — {e["date"]} <span style="color:#c00;">({e["days"]} days)</span></li>')
                blines.append('</ul>')

            blines.append('<hr/><p style="color:#999;font-size:12px;">Rytech SummarAI Daily Digest · summarai.rytech-support.com<br>')
            blines.append('To unsubscribe, go to Profile → Notifications and disable the daily digest.</p></div>')
            body = '\n'.join(blines)

            ok, err = smtp_send(u['email'], subject, body, cfg=smtp_cfg, html=True)
            wf_log(workflow_id, u['email'], subject, 'sent' if ok else 'failed', err)
            if ok:
                sent_count += 1
            else:
                fail_count += 1

        wf_set_last_run(workflow_id)
        return sent_count, fail_count


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
