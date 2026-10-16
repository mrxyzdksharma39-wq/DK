#!/usr/bin/env python3
"""Livegram Clone Manager - single-file edition for Render's free web service.

One process, one HTTP listener, many Telegram bots (webhook mode):
  * the main Livegram relay bot (user <-> admin message forwarding, broadcasts,
    statistics, bans, maintenance mode, auto-delete, backup/restore, ...)
  * the clone system (permission requests, token vault, per-clone Livegram
    instances, start/stop/unregister, admin reassignment)

Persistence is an external PostgreSQL database (Render's disk is ephemeral).
Each bot owns one schema named ``livegram_<bot_id>``; the clone registry lives
in the main bot's schema.

Required environment variables:
  BOT_TOKEN, OWNER_ID, DATABASE_URL, MULTIBOT_SECRET
Optional:
  MAX_CHILD_BOTS (default 3, max 10), WEBHOOK_BASE_URL (defaults to Render's
  RENDER_EXTERNAL_URL), KEEP_ALIVE (default 1), PORT (set by Render)

Run:  python bot.py
"""
from __future__ import annotations

import asyncio
import base64
import csv
import hashlib
import hmac
import html
import json
import logging
import os
import re
import signal
import sqlite3
import sys
import tempfile
import time
import traceback
import uuid
import zipfile
from contextlib import asynccontextmanager
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Awaitable, Callable, Optional

import asyncpg
from aiohttp import ClientSession, ClientTimeout, web
from cryptography.fernet import Fernet
from telegram import Bot, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import (
    BadRequest,
    Forbidden,
    NetworkError,
    RetryAfter,
    TelegramError,
    TimedOut,
)
from telegram.ext import (
    AIORateLimiter,
    Application,
    ApplicationBuilder,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)

# =====================================================================
# 1. CONSTANTS
# =====================================================================
ACTIVE_DAYS = 30
BROADCAST_PAGE = 64
DEFAULT_AUTO_DELETE_MINUTES = 20
DEFAULT_START = "Hello, Welcome to our bot!"
DEFAULT_MAINTENANCE = "The bot is temporarily under maintenance. Please try again later."
MAX_BACKUP_BYTES = 25 * 1024 * 1024
MAX_BACKUP_ROWS = 100_000
MAX_UPDATE_ATTEMPTS = 3          # webhook retries before a poison update is dropped
UPDATE_TIMEOUT = 50.0            # seconds one update may take inside the webhook
SWEEP_INTERVAL = 20              # seconds between maintenance passes per bot
SUPERVISE_INTERVAL = 60          # seconds between recovery passes
WEBHOOK_CHECK_INTERVAL = 600     # seconds between webhook self-healing checks
KEEPALIVE_INTERVAL = 600         # Render free services sleep after 15 idle minutes
TOKEN_RE = re.compile(r"(?<![0-9])\d{6,12}:[A-Za-z0-9_-]{30,}")
TOKEN_FULL_RE = re.compile(r"\d{6,12}:[A-Za-z0-9_-]{30,}")

log = logging.getLogger("livegram")


# =====================================================================
# 2. CONFIGURATION
# =====================================================================
class ConfigError(RuntimeError):
    pass


@dataclass(frozen=True)
class Config:
    token: str
    owner_id: int
    database_url: str
    base_url: str
    secret: str
    max_child_bots: int
    port: int
    keepalive: bool

    @property
    def main_id(self) -> int:
        return int(self.token.split(":")[0])


def load_config(env=os.environ) -> Config:
    problems: list[str] = []
    token = env.get("BOT_TOKEN", "").strip()
    if not TOKEN_FULL_RE.fullmatch(token):
        problems.append("BOT_TOKEN is missing or not a valid BotFather token")
    try:
        owner = int(env.get("OWNER_ID", "").strip())
        if owner <= 0:
            raise ValueError
    except ValueError:
        owner = 0
        problems.append("OWNER_ID must be your numeric Telegram user ID")
    database_url = env.get("DATABASE_URL", "").strip()
    if not database_url.startswith(("postgres://", "postgresql://")):
        problems.append("DATABASE_URL must be a postgres:// or postgresql:// URL")
    base_url = (env.get("WEBHOOK_BASE_URL") or env.get("RENDER_EXTERNAL_URL") or "").strip().rstrip("/")
    if not base_url.startswith("https://"):
        problems.append("WEBHOOK_BASE_URL (or Render's RENDER_EXTERNAL_URL) must be an https:// URL")
    secret = env.get("MULTIBOT_SECRET", "").strip()
    if len(secret) < 16:
        problems.append(
            "MULTIBOT_SECRET is missing/too short. Generate one with: "
            "python -c \"from cryptography.fernet import Fernet; print(Fernet.generate_key().decode())\""
        )
    try:
        limit = max(1, min(10, int(env.get("MAX_CHILD_BOTS", "3"))))
    except ValueError:
        limit = 3
    try:
        port = int(env.get("PORT", "10000"))
    except ValueError:
        port = 10000
    keepalive = env.get("KEEP_ALIVE", "1").strip().lower() not in {"0", "false", "no", "off"}
    if problems:
        raise ConfigError("Invalid configuration:\n - " + "\n - ".join(problems))
    return Config(token, owner, database_url, base_url, secret, limit, port, keepalive)


def make_vault(secret: str) -> Fernet:
    """Accepts a real Fernet key (preferred, keeps existing deployments working)
    or any long passphrase, from which a stable key is derived."""
    try:
        return Fernet(secret.encode())
    except (ValueError, TypeError):
        derived = base64.urlsafe_b64encode(hashlib.sha256(secret.encode()).digest())
        return Fernet(derived)


def webhook_secret(secret: str, bot_id: int) -> str:
    return hmac.new(secret.encode(), f"webhook:{bot_id}".encode(), hashlib.sha256).hexdigest()


# =====================================================================
# 3. LOGGING (tokens are redacted from every line, tracebacks included)
# =====================================================================
def redact(text: str) -> str:
    return TOKEN_RE.sub("[REDACTED]", text)


class RedactingFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        return redact(super().format(record))


def setup_logging() -> None:
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(RedactingFormatter("%(asctime)s %(levelname)s %(name)s: %(message)s"))
    root = logging.getLogger()
    root.handlers[:] = [handler]
    root.setLevel(logging.INFO)
    for noisy in ("httpx", "httpcore", "aiohttp.access"):
        logging.getLogger(noisy).setLevel(logging.WARNING)


# =====================================================================
# 4. SMALL UTILITIES
# =====================================================================
def utcnow() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def today() -> str:
    return datetime.now(timezone.utc).date().isoformat()


def esc(value: object) -> str:
    return html.escape(str(value or ""))


def human_duration(seconds: float) -> str:
    seconds = max(0, int(seconds))
    days, seconds = divmod(seconds, 86400)
    hours, seconds = divmod(seconds, 3600)
    minutes, seconds = divmod(seconds, 60)
    parts = []
    if days:
        parts.append(f"{days}d")
    if hours or days:
        parts.append(f"{hours}h")
    if minutes or hours or days:
        parts.append(f"{minutes}m")
    parts.append(f"{seconds}s")
    return " ".join(parts)


def message_kind(message) -> str:
    for name in ("text", "photo", "video", "document", "voice", "audio", "sticker",
                 "animation", "video_note", "contact", "location", "venue", "poll", "dice"):
        if getattr(message, name, None) is not None:
            return name
    return "other"


def parse_id(text: str) -> Optional[int]:
    text = (text or "").strip()
    if text.isdigit() and 0 < int(text) < 2 ** 63:
        return int(text)
    return None


def csv_safe(value: Any) -> Any:
    """Neutralise spreadsheet formula injection in exported text."""
    if isinstance(value, str) and value[:1] in ("=", "+", "-", "@", "\t", "\r"):
        return "'" + value
    return value


def kb(rows) -> InlineKeyboardMarkup:
    """rows: [[(label, callback_data), ...], ...]"""
    return InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) for t, d in row] for row in rows])


# =====================================================================
# 5. DATABASE LAYER (PostgreSQL via asyncpg, one connection per bot)
# =====================================================================
# The schema is kept in SQLite dialect because the SQLite ZIP backup format
# (compatible with backups from the original bot) needs exactly this DDL.
SQLITE_SCHEMA = """
PRAGMA journal_mode=WAL;
CREATE TABLE IF NOT EXISTS users (
    user_id INTEGER PRIMARY KEY,
    username TEXT,
    first_name TEXT,
    last_name TEXT,
    language_code TEXT,
    is_banned INTEGER NOT NULL DEFAULT 0,
    is_active INTEGER NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL,
    last_seen TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_users_last_seen ON users(last_seen);
CREATE INDEX IF NOT EXISTS idx_users_banned ON users(is_banned);
CREATE TABLE IF NOT EXISTS owners (
    user_id INTEGER PRIMARY KEY,
    added_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS admins (
    user_id INTEGER PRIMARY KEY,
    added_at TEXT NOT NULL,
    added_by INTEGER
);
CREATE TABLE IF NOT EXISTS settings (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS message_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    direction TEXT NOT NULL,
    user_id INTEGER,
    admin_id INTEGER,
    message_type TEXT NOT NULL,
    telegram_chat_id INTEGER,
    telegram_message_id INTEGER,
    related_message_id INTEGER,
    created_at TEXT NOT NULL,
    UNIQUE(direction, telegram_chat_id, telegram_message_id)
);
CREATE INDEX IF NOT EXISTS idx_message_log_user ON message_log(user_id, created_at DESC);
CREATE INDEX IF NOT EXISTS idx_message_log_date ON message_log(created_at);
CREATE TABLE IF NOT EXISTS forward_map (
    admin_chat_id INTEGER NOT NULL,
    admin_message_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL,
    user_message_id INTEGER NOT NULL,
    created_at TEXT NOT NULL,
    PRIMARY KEY(admin_chat_id, admin_message_id)
);
CREATE TABLE IF NOT EXISTS pending_deletes (
    admin_chat_id INTEGER NOT NULL,
    admin_message_id INTEGER NOT NULL,
    delete_at REAL NOT NULL,
    PRIMARY KEY(admin_chat_id, admin_message_id)
);
CREATE TABLE IF NOT EXISTS processed_updates (
    update_id INTEGER PRIMARY KEY,
    processed_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS broadcasts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    admin_id INTEGER NOT NULL,
    source_chat_id INTEGER NOT NULL,
    source_message_id INTEGER NOT NULL,
    status TEXT NOT NULL,
    total INTEGER NOT NULL DEFAULT 0,
    success INTEGER NOT NULL DEFAULT 0,
    failed INTEGER NOT NULL DEFAULT 0,
    started_at TEXT NOT NULL,
    finished_at TEXT,
    error TEXT
);
CREATE TABLE IF NOT EXISTS broadcast_deliveries (
    broadcast_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL,
    status TEXT NOT NULL,
    error TEXT,
    delivered_at TEXT,
    PRIMARY KEY(broadcast_id, user_id),
    FOREIGN KEY(broadcast_id) REFERENCES broadcasts(id) ON DELETE CASCADE
);
CREATE INDEX IF NOT EXISTS idx_broadcast_deliveries_status ON broadcast_deliveries(broadcast_id, status);
CREATE TABLE IF NOT EXISTS daily_stats (
    day TEXT PRIMARY KEY,
    new_users INTEGER NOT NULL DEFAULT 0,
    incoming INTEGER NOT NULL DEFAULT 0,
    outgoing INTEGER NOT NULL DEFAULT 0,
    admin_replies INTEGER NOT NULL DEFAULT 0,
    broadcast_success INTEGER NOT NULL DEFAULT 0,
    broadcast_failed INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS errors (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    context TEXT NOT NULL,
    error TEXT NOT NULL,
    traceback TEXT,
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_errors_date ON errors(created_at DESC);
"""

# Clone registry (lives in the main bot's schema).
REGISTRY_SCHEMA = """
CREATE TABLE IF NOT EXISTS bot_creators (user_id BIGINT PRIMARY KEY, max_bots BIGINT NOT NULL, granted_by BIGINT NOT NULL, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS clone_requests (user_id BIGINT PRIMARY KEY, status TEXT NOT NULL, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS child_bots (bot_id BIGINT PRIMARY KEY, username TEXT NOT NULL, encrypted_token TEXT NOT NULL, admin_id BIGINT NOT NULL, created_by BIGINT NOT NULL, enabled BIGINT NOT NULL DEFAULT 1, status TEXT NOT NULL, last_error TEXT NOT NULL DEFAULT '', created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS master_audit (id BIGSERIAL PRIMARY KEY, actor BIGINT NOT NULL, bot_id BIGINT, action TEXT NOT NULL, created_at TEXT NOT NULL);
"""

BACKUP_TABLES = ("users", "owners", "admins", "settings", "message_log", "forward_map",
                 "pending_deletes", "processed_updates", "broadcasts", "broadcast_deliveries",
                 "daily_stats", "errors")
SERIAL_TABLES = ("message_log", "broadcasts", "errors")


def split_statements(script: str) -> list[str]:
    return [s.strip() for s in script.split(";") if s.strip()]


def to_pg_ddl(sqlite_schema: str) -> list[str]:
    out = []
    for stmt in split_statements(sqlite_schema):
        if stmt.upper().startswith("PRAGMA"):
            continue
        stmt = re.sub(r"INTEGER PRIMARY KEY AUTOINCREMENT", "BIGSERIAL PRIMARY KEY", stmt, flags=re.I)
        stmt = re.sub(r"\bINTEGER\b", "BIGINT", stmt, flags=re.I)
        stmt = re.sub(r"\bREAL\b", "DOUBLE PRECISION", stmt, flags=re.I)
        out.append(stmt)
    return out


PG_DDL = to_pg_ddl(SQLITE_SCHEMA)
# Backup exports use plain rollback-journal SQLite (no WAL side files), so the
# single .db file placed in the ZIP is always complete.
SQLITE_EXPORT_DDL = ";\n".join(s for s in split_statements(SQLITE_SCHEMA) if not s.upper().startswith("PRAGMA"))


def qmarks(sql: str) -> str:
    """Convert '?' placeholders to PostgreSQL $1, $2, ... (no literal '?' in our SQL)."""
    count = 0

    def repl(_):
        nonlocal count
        count += 1
        return f"${count}"

    return re.sub(r"\?", repl, sql)


def rowcount_of(status: str) -> int:
    last = (status or "").split()[-1:] or ["0"]
    return int(last[0]) if last[0].isdigit() else 0


def is_connection_error(exc: BaseException) -> bool:
    if isinstance(exc, (asyncpg.PostgresConnectionError, asyncpg.InterfaceError,
                        ConnectionError, OSError, asyncio.TimeoutError)):
        return True
    state = getattr(exc, "sqlstate", None) or ""
    return state.startswith(("08", "57P0"))


class LockNotAcquired(RuntimeError):
    """Another process/deployment is already serving this bot's schema."""


class Tx:
    """Query helpers bound to one raw asyncpg connection (no locking here)."""

    def __init__(self, raw):
        self.raw = raw

    async def execute(self, sql: str, params=()) -> int:
        return rowcount_of(await self.raw.execute(qmarks(sql), *params, timeout=25))

    async def fetchall(self, sql: str, params=()):
        return await self.raw.fetch(qmarks(sql), *params, timeout=25)

    async def fetchone(self, sql: str, params=()):
        return await self.raw.fetchrow(qmarks(sql), *params, timeout=25)

    async def fetchval(self, sql: str, params=()):
        return await self.raw.fetchval(qmarks(sql), *params, timeout=25)


class Database:
    """One serialized, self-healing connection to one PostgreSQL schema.

    * every operation takes ``self.lock`` (asyncpg connections are not concurrent)
    * a dead connection is discarded and transparently re-opened (one retry)
    * a session advisory lock stops overlapping deployments from serving the same bot
    """

    def __init__(self, url: str, schema: str, lock_key: int):
        if not re.fullmatch(r"livegram_\d+", schema):
            raise ValueError("Invalid instance schema")
        self.url, self.schema, self.lock_key = url, schema, lock_key
        self.lock = asyncio.Lock()
        self._raw: Optional[asyncpg.Connection] = None

    async def _connection(self) -> asyncpg.Connection:
        if self._raw is not None and not self._raw.is_closed():
            return self._raw
        self._raw = None
        raw = await asyncpg.connect(
            self.url, timeout=20, command_timeout=25, statement_cache_size=0,
            server_settings={"search_path": self.schema, "application_name": self.schema},
        )
        try:
            await raw.execute(f'CREATE SCHEMA IF NOT EXISTS "{self.schema}"')
            # After a dropped connection the server may still hold the old session's
            # lock for a moment, so retry briefly before giving up.
            for attempt in range(4):
                if await raw.fetchval("SELECT pg_try_advisory_lock($1)", self.lock_key):
                    break
                if attempt == 3:
                    raise LockNotAcquired("Another deployment is serving this bot")
                await asyncio.sleep(1.5)
        except BaseException:
            raw.terminate()
            raise
        self._raw = raw
        return raw

    def _discard(self) -> None:
        if self._raw is not None:
            try:
                self._raw.terminate()
            except Exception:
                pass
            self._raw = None

    async def _run(self, op: Callable[[Tx], Awaitable[Any]]):
        async with self.lock:
            for attempt in (1, 2):
                try:
                    return await op(Tx(await self._connection()))
                except asyncpg.UniqueViolationError:
                    raise
                except Exception as exc:
                    if is_connection_error(exc):
                        self._discard()
                        if attempt == 1:
                            continue
                    raise

    async def execute(self, sql: str, params=()) -> int:
        return await self._run(lambda tx: tx.execute(sql, params))

    async def insert_id(self, sql: str, params=()) -> int:
        """Run an INSERT ... RETURNING id statement and return the id."""
        return await self._run(lambda tx: tx.fetchval(sql, params))

    async def fetchone(self, sql: str, params=()):
        return await self._run(lambda tx: tx.fetchone(sql, params))

    async def fetchall(self, sql: str, params=()):
        return await self._run(lambda tx: tx.fetchall(sql, params))

    async def fetchval(self, sql: str, params=()):
        return await self._run(lambda tx: tx.fetchval(sql, params))

    async def executescript(self, statements: list[str]) -> None:
        async def op(tx: Tx):
            for stmt in statements:
                await tx.raw.execute(stmt, timeout=25)
        await self._run(op)

    @asynccontextmanager
    async def transaction(self):
        async with self.lock:
            raw = await self._connection()
            try:
                async with raw.transaction():
                    yield Tx(raw)
            except Exception as exc:
                if is_connection_error(exc):
                    self._discard()
                raise

    async def close(self) -> None:
        async with self.lock:
            if self._raw is not None:
                try:
                    await self._raw.close(timeout=5)
                except Exception:
                    self._discard()
                self._raw = None

    # ---- bulk helpers used by backup / restore ------------------------
    async def snapshot(self) -> dict[str, list[dict]]:
        """Consistent read-only export of all Livegram tables (size-limited)."""
        snap: dict[str, list[dict]] = {}
        approx = 0
        async with self.lock:
            raw = await self._connection()
            async with raw.transaction(isolation="repeatable_read", readonly=True):
                for table in BACKUP_TABLES:
                    rows = await raw.fetch(f"SELECT * FROM {table} LIMIT {MAX_BACKUP_ROWS + 1}", timeout=25)
                    if len(rows) > MAX_BACKUP_ROWS:
                        raise ValueError("In-app backup limit exceeded; use your PostgreSQL provider's backup tools")
                    snap[table] = [dict(r) for r in rows]
                    approx += sum(len(json.dumps(r, default=str)) for r in snap[table])
                    if approx > MAX_BACKUP_BYTES:
                        raise ValueError("In-app backup exceeds 25 MB; use a provider-level backup")
        return snap

    async def replace_all(self, data: dict[str, list[dict]]) -> None:
        async with self.lock:
            raw = await self._connection()
            async with raw.transaction():
                for table in reversed(BACKUP_TABLES):
                    await raw.execute(f"DELETE FROM {table}")
                for table in BACKUP_TABLES:
                    rows = data[table]
                    expected = [r["column_name"] for r in await raw.fetch(
                        "SELECT column_name FROM information_schema.columns "
                        "WHERE table_schema=current_schema() AND table_name=$1 ORDER BY ordinal_position", table)]
                    if rows:
                        if set(rows[0]) != set(expected):
                            raise ValueError("Backup schema does not match this version")
                        await raw.copy_records_to_table(
                            table, columns=expected,
                            records=[tuple(r[c] for c in expected) for r in rows])
                    if table in SERIAL_TABLES:
                        await raw.execute(
                            f"SELECT setval(pg_get_serial_sequence('{table}','id'), "
                            f"COALESCE((SELECT MAX(id) FROM {table}),0)+1, false)")
                await raw.execute(
                    "UPDATE broadcasts SET status='interrupted' WHERE status IN ('running','queued','cancelling')")



# =====================================================================
# 6. TELEGRAM SAFETY HELPERS
# =====================================================================
async def safe_answer(query, text: Optional[str] = None, show_alert: bool = False) -> None:
    try:
        await query.answer(text=text, show_alert=show_alert)
    except TelegramError as exc:
        log.debug("Callback answer ignored: %s", exc)


async def safe_reply_text(message, text: str, **kwargs):
    try:
        return await message.reply_text(text, **kwargs)
    except RetryAfter as exc:
        await asyncio.sleep(float(exc.retry_after) + 0.5)
        try:
            return await message.reply_text(text, **kwargs)
        except TelegramError as exc2:
            log.warning("reply_text failed after retry: %s", exc2)
            return None
    except TelegramError as exc:
        log.warning("reply_text failed: %s", exc)
        return None


async def safe_edit(query, text: str, keyboard=None, parse_mode=ParseMode.HTML) -> None:
    for attempt in (1, 2):
        try:
            await query.edit_message_text(text, reply_markup=keyboard, parse_mode=parse_mode)
            return
        except RetryAfter as exc:
            if attempt == 2:
                return
            await asyncio.sleep(float(exc.retry_after) + 0.5)
        except BadRequest as exc:
            if "Message is not modified" not in str(exc):
                log.warning("safe_edit BadRequest: %s", exc)
            return
        except TelegramError as exc:
            log.warning("safe_edit failed: %s", exc)
            return


def back_keyboard(target: str = "panel") -> InlineKeyboardMarkup:
    return kb([[("⬅️ Back", target), ("❌ Cancel", "cancel")]])


def autodelete_keyboard() -> InlineKeyboardMarkup:
    return kb([
        [(f"{m}m", f"autodelete_set:{m}") for m in (1, 2, 5, 10)],
        [(f"{m}m", f"autodelete_set:{m}") for m in (15, 20, 30, 60)],
        [("🔴 Turn OFF (Never Delete)", "autodelete_set:0")],
        [("⬅️ Back", "panel")],
    ])


# =====================================================================
# 7. LIVEGRAM CORE (one instance per bot: main bot and every clone)
# =====================================================================
class Cache:
    """In-memory mirror of hot data for zero-latency routing."""

    def __init__(self, owner_id: int):
        self.initial_owner = owner_id
        self.owners: set[int] = {owner_id}
        self.admins: set[int] = {owner_id}
        self.banned_users: set[int] = set()
        self.settings: dict[str, str] = {
            "start_message": DEFAULT_START,
            "maintenance_mode": "0",
            "maintenance_message": DEFAULT_MAINTENANCE,
            "auto_delete_minutes": str(DEFAULT_AUTO_DELETE_MINUTES),
        }
        self.forward_map: dict[tuple[int, int], tuple[int, int]] = {}
        self.seen_updates: dict[int, None] = {}

    @property
    def auto_delete_minutes(self) -> int:
        try:
            return max(0, int(self.settings.get("auto_delete_minutes", str(DEFAULT_AUTO_DELETE_MINUTES))))
        except ValueError:
            return DEFAULT_AUTO_DELETE_MINUTES

    def remember_update(self, update_id: int) -> None:
        self.seen_updates[update_id] = None
        if len(self.seen_updates) > 5000:
            for key in list(self.seen_updates)[:2500]:
                self.seen_updates.pop(key, None)


class LivegramCore:
    """Everything the original Livegram bot did, scoped to a single bot."""

    DAILY_COLUMNS = frozenset({"new_users", "incoming", "outgoing", "admin_replies",
                               "broadcast_success", "broadcast_failed"})

    def __init__(self, token: str, owner_id: int, bot_id: int, database_url: str):
        self.token, self.owner_id, self.bot_id = token, owner_id, bot_id
        self.db = Database(database_url, f"livegram_{bot_id}", bot_id)
        self.cache = Cache(owner_id)
        self.app: Optional[Application] = None
        self.started_at = time.monotonic()
        self.broadcast_tasks: dict[int, asyncio.Task] = {}
        self.bg_tasks: set[asyncio.Task] = set()
        self.extra_owner_rows: list[list[tuple[str, str]]] = []
        self.last_update_failed = False
        self.backup_dir = Path(tempfile.gettempdir()) / "livegram" / str(bot_id) / "backups"

    # ---------------------------------------------------------------- tasks
    def spawn(self, coro) -> None:
        """Run non-critical work in the background without losing exceptions."""
        task = asyncio.create_task(coro)
        self.bg_tasks.add(task)

        def done(t: asyncio.Task) -> None:
            self.bg_tasks.discard(t)
            if not t.cancelled() and t.exception():
                log.error("Background task failed: %s", type(t.exception()).__name__)

        task.add_done_callback(done)

    async def cancel_tasks(self) -> None:
        tasks = list(self.broadcast_tasks.values()) + list(self.bg_tasks)
        for task in tasks:
            task.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)

    # ------------------------------------------------------------- database
    async def init_db(self) -> None:
        await self.db.executescript(PG_DDL)
        # Early versions stored epoch seconds in REAL (float4) which loses precision.
        dtype = await self.db.fetchval(
            "SELECT data_type FROM information_schema.columns WHERE table_schema=current_schema() "
            "AND table_name='pending_deletes' AND column_name='delete_at'")
        if dtype == "real":
            await self.db.execute("ALTER TABLE pending_deletes ALTER COLUMN delete_at TYPE DOUBLE PRECISION")
        now = utcnow()
        async with self.db.transaction() as tx:
            for key, value in {
                "start_message": DEFAULT_START,
                "maintenance_mode": "0",
                "maintenance_message": DEFAULT_MAINTENANCE,
                "auto_delete_minutes": str(DEFAULT_AUTO_DELETE_MINUTES),
            }.items():
                await tx.execute("INSERT INTO settings(key,value,updated_at) VALUES(?,?,?) ON CONFLICT DO NOTHING",
                                 (key, value, now))
            await tx.execute("INSERT INTO owners(user_id,added_at) VALUES(?,?) ON CONFLICT DO NOTHING",
                             (self.owner_id, now))
        await self.reload_cache()

    async def reload_cache(self) -> None:
        owners = await self.db.fetchall("SELECT user_id FROM owners")
        admins = await self.db.fetchall("SELECT user_id FROM admins")
        banned = await self.db.fetchall("SELECT user_id FROM users WHERE is_banned=1")
        settings = await self.db.fetchall("SELECT key, value FROM settings")
        recent = await self.db.fetchall(
            "SELECT admin_chat_id, admin_message_id, user_id, user_message_id "
            "FROM forward_map ORDER BY created_at DESC LIMIT 2000")
        c = self.cache
        c.owners = {r["user_id"] for r in owners} | {self.owner_id}
        c.admins = c.owners | {r["user_id"] for r in admins}
        c.banned_users = {r["user_id"] for r in banned}
        for r in settings:
            c.settings[r["key"]] = r["value"]
        c.forward_map = {(r["admin_chat_id"], r["admin_message_id"]): (r["user_id"], r["user_message_id"])
                         for r in recent}

    async def set_setting(self, key: str, value: str) -> None:
        await self.db.execute(
            "INSERT INTO settings(key,value,updated_at) VALUES(?,?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
            (key, value, utcnow()))
        self.cache.settings[key] = value

    async def _daily_inc(self, tx: Tx, column: str, amount: int = 1) -> None:
        if column not in self.DAILY_COLUMNS:
            raise ValueError("Invalid counter")
        await tx.execute(
            f"INSERT INTO daily_stats(day,{column}) VALUES(?,?) "
            f"ON CONFLICT(day) DO UPDATE SET {column}=daily_stats.{column}+excluded.{column}",
            (today(), amount))

    async def upsert_user(self, user) -> bool:
        now = utcnow()
        async with self.db.transaction() as tx:
            is_new = await tx.fetchval(
                "INSERT INTO users(user_id,username,first_name,last_name,language_code,created_at,last_seen) "
                "VALUES(?,?,?,?,?,?,?) ON CONFLICT(user_id) DO UPDATE SET "
                "username=excluded.username, first_name=excluded.first_name, last_name=excluded.last_name, "
                "language_code=excluded.language_code, last_seen=excluded.last_seen, is_active=1 "
                "RETURNING (xmax = 0)",
                (user.id, user.username, user.first_name, user.last_name, user.language_code, now, now))
            if is_new:
                await self._daily_inc(tx, "new_users")
            return bool(is_new)

    async def log_message(self, direction: str, user_id, admin_id, message_type: str,
                          chat_id, message_id, related_message_id=None) -> bool:
        async with self.db.transaction() as tx:
            row_id = await tx.fetchval(
                "INSERT INTO message_log(direction,user_id,admin_id,message_type,telegram_chat_id,"
                "telegram_message_id,related_message_id,created_at) VALUES(?,?,?,?,?,?,?,?) "
                "ON CONFLICT DO NOTHING RETURNING id",
                (direction, user_id, admin_id, message_type, chat_id, message_id, related_message_id, utcnow()))
            if row_id is None:
                return False
            counter = {"incoming": "incoming", "outgoing": "outgoing", "admin_reply": "admin_replies"}.get(direction)
            if counter:
                await self._daily_inc(tx, counter)
            if direction == "admin_reply":
                await self._daily_inc(tx, "outgoing")
            return True

    async def save_forward_mapping(self, admin_id: int, admin_msg_id: int, user_id: int,
                                   user_msg_id: int, delete_at: Optional[float]) -> None:
        fm = self.cache.forward_map
        fm[(admin_id, admin_msg_id)] = (user_id, user_msg_id)
        if len(fm) > 5000:
            fm.pop(next(iter(fm)), None)
        async with self.db.transaction() as tx:
            await tx.execute(
                "INSERT INTO forward_map(admin_chat_id,admin_message_id,user_id,user_message_id,created_at) "
                "VALUES(?,?,?,?,?) ON CONFLICT(admin_chat_id,admin_message_id) DO UPDATE SET "
                "user_id=excluded.user_id, user_message_id=excluded.user_message_id, created_at=excluded.created_at",
                (admin_id, admin_msg_id, user_id, user_msg_id, utcnow()))
            if delete_at is not None:
                await tx.execute(
                    "INSERT INTO pending_deletes(admin_chat_id,admin_message_id,delete_at) VALUES(?,?,?) "
                    "ON CONFLICT(admin_chat_id,admin_message_id) DO UPDATE SET delete_at=excluded.delete_at",
                    (admin_id, admin_msg_id, delete_at))

    async def remove_deleted_mapping(self, admin_id: int, admin_msg_id: int) -> None:
        self.cache.forward_map.pop((admin_id, admin_msg_id), None)
        async with self.db.transaction() as tx:
            await tx.execute("DELETE FROM pending_deletes WHERE admin_chat_id=? AND admin_message_id=?",
                             (admin_id, admin_msg_id))
            await tx.execute("DELETE FROM forward_map WHERE admin_chat_id=? AND admin_message_id=?",
                             (admin_id, admin_msg_id))

    async def mark_delivery(self, bid: int, user_id: int, success: bool, error: Optional[str]) -> None:
        status = "success" if success else "failed"
        async with self.db.transaction() as tx:
            current = await tx.fetchval(
                "SELECT status FROM broadcast_deliveries WHERE broadcast_id=? AND user_id=?", (bid, user_id))
            if current == "success":
                return
            await tx.execute(
                "INSERT INTO broadcast_deliveries(broadcast_id,user_id,status,error,delivered_at) "
                "VALUES(?,?,?,?,?) ON CONFLICT(broadcast_id,user_id) DO UPDATE SET "
                "status=excluded.status,error=excluded.error,delivered_at=excluded.delivered_at",
                (bid, user_id, status, error, utcnow()))
            column = "success" if success else "failed"
            await tx.execute(f"UPDATE broadcasts SET {column}={column}+1 WHERE id=?", (bid,))
            await self._daily_inc(tx, "broadcast_success" if success else "broadcast_failed")
            if success:
                await self._daily_inc(tx, "outgoing")

    async def record_error(self, context: str, error: BaseException) -> None:
        text = redact(f"{type(error).__name__}: {error}")[:4000]
        tb = redact("".join(traceback.format_exception(type(error), error, error.__traceback__)))[-12000:]
        try:
            await self.db.execute(
                "INSERT INTO errors(context,error,traceback,created_at) VALUES(?,?,?,?)",
                (context[:250], text, tb, utcnow()))
        except Exception:
            log.warning("Could not persist error record")

    async def interrupt_broadcasts(self) -> None:
        await self.db.execute(
            "UPDATE broadcasts SET status='interrupted',finished_at=? "
            "WHERE status IN ('queued','running','cancelling')", (utcnow(),))

    # ------------------------------------------------------------ keyboards
    def owner_keyboard(self) -> InlineKeyboardMarkup:
        rows = [[("🛡 Manage Admins", "admins")], [("⚙️ Open Admin Panel", "panel")]]
        return kb(rows + self.extra_owner_rows)

    def main_keyboard(self) -> InlineKeyboardMarkup:
        mins = self.cache.auto_delete_minutes
        label = f"⏳ Auto-Delete ({mins}m)" if mins > 0 else "⏳ Auto-Delete (OFF)"
        return kb([
            [("📊 Statistics", "stats"), ("📣 Broadcast", "broadcast")],
            [("👥 Users", "users"), ("✏️ Messages", "messages")],
            [(label, "autodelete"), ("🛠 Maintenance", "maintenance")],
            [("💾 Backup / Restore", "backup"), ("🩺 System", "system")],
        ])

    # --------------------------------------------------------------- guards
    async def ensure_owner(self, update: Update) -> bool:
        user = update.effective_user
        if user and user.id in self.cache.owners:
            return True
        if update.callback_query:
            await safe_answer(update.callback_query, "Owner access required.", show_alert=True)
        elif update.effective_message:
            await safe_reply_text(update.effective_message, "Owner access required.")
        return False

    async def ensure_admin(self, update: Update) -> bool:
        user = update.effective_user
        if user and user.id in self.cache.admins:
            return True
        if update.callback_query:
            await safe_answer(update.callback_query, "Not authorized.", show_alert=True)
        elif update.effective_message:
            await safe_reply_text(update.effective_message, "Not authorized.")
        return False

    # ----------------------------------------------------------------- text
    async def panel_text(self) -> str:
        total = await self.db.fetchval("SELECT COUNT(*) FROM users")
        cutoff = (datetime.now(timezone.utc) - timedelta(days=ACTIVE_DAYS)).isoformat(timespec="seconds")
        active = await self.db.fetchval("SELECT COUNT(*) FROM users WHERE last_seen>=?", (cutoff,))
        mins = self.cache.auto_delete_minutes
        return (
            "<b>⚙️ Administration Panel</b>\n\n"
            f"👥 Users: <b>{total:,}</b>\n"
            f"🟢 Active ({ACTIVE_DAYS}d): <b>{active:,}</b>\n"
            f"⏳ Auto-Delete: <b>{f'{mins} minutes' if mins > 0 else 'OFF'}</b>\n\n"
            "Choose a section:"
        )

    def autodelete_text(self) -> str:
        mins = self.cache.auto_delete_minutes
        status = f"<b>{mins} minutes</b>" if mins > 0 else "<b>OFF (Never Delete)</b>"
        return (
            "<b>⏳ Auto-Delete User Messages (Admin Side)</b>\n\n"
            f"Current Timer: {status}\n\n"
            "• यूजर का फॉरवर्ड किया गया मैसेज तय समय के बाद एडमिन की तरफ से अपने-आप डिलीट हो जाएगा (यूजर की चैट में मैसेज रहेगा)।\n"
            "• नीचे दिए गए किसी भी बटन को चुनें, या <b>सीधे चैट में मिनट लिखकर भेजें</b> "
            "(जैसे <code>5</code>, <code>2</code>, <code>1</code>, <code>20</code> या बंद करने के लिए <code>0</code>):"
        )

    async def statistics_text(self) -> str:
        now = datetime.now(timezone.utc)
        periods = {
            "Today": now.date().isoformat(),
            "7 days": (now - timedelta(days=6)).date().isoformat(),
            "30 days": (now - timedelta(days=29)).date().isoformat(),
        }
        cutoff = (now - timedelta(days=ACTIVE_DAYS)).isoformat(timespec="seconds")
        u = await self.db.fetchone(
            "SELECT COUNT(*) AS total, COALESCE(SUM(CASE WHEN is_banned=1 THEN 1 ELSE 0 END),0)::BIGINT AS banned, "
            "COALESCE(SUM(CASE WHEN last_seen>=? THEN 1 ELSE 0 END),0)::BIGINT AS active FROM users", (cutoff,))
        m = await self.db.fetchone(
            "SELECT COALESCE(SUM(CASE WHEN direction='incoming' THEN 1 ELSE 0 END),0)::BIGINT AS incoming, "
            "COALESCE(SUM(CASE WHEN direction IN ('outgoing','admin_reply') THEN 1 ELSE 0 END),0)::BIGINT AS outgoing, "
            "COALESCE(SUM(CASE WHEN direction='admin_reply' THEN 1 ELSE 0 END),0)::BIGINT AS replies, "
            "COUNT(*) AS stored FROM message_log")
        b = await self.db.fetchone(
            "SELECT COUNT(*) AS total, COALESCE(SUM(success),0)::BIGINT AS success, "
            "COALESCE(SUM(failed),0)::BIGINT AS failed FROM broadcasts")
        lines = [
            "<b>📊 Advanced Statistics</b>", "",
            f"👥 Total users: <b>{u['total']:,}</b>",
            f"🟢 Active users ({ACTIVE_DAYS}d): <b>{u['active']:,}</b>",
            f"🚫 Banned users: <b>{u['banned']:,}</b>",
            f"📥 Messages received: <b>{m['incoming']:,}</b>",
            f"📤 Messages sent: <b>{m['outgoing']:,}</b>",
            f"💬 Admin replies: <b>{m['replies']:,}</b>",
            f"📣 Broadcasts: <b>{b['total']:,}</b>",
            f"✅ Broadcast deliveries: <b>{b['success']:,}</b>",
            f"❌ Failed deliveries: <b>{b['failed']:,}</b>", "",
            "<b>Period breakdown</b>",
        ]
        for label, start_day in periods.items():
            r = await self.db.fetchone(
                "SELECT COALESCE(SUM(new_users),0)::BIGINT AS new_users, COALESCE(SUM(incoming),0)::BIGINT AS incoming, "
                "COALESCE(SUM(outgoing),0)::BIGINT AS outgoing, COALESCE(SUM(broadcast_success),0)::BIGINT AS bs "
                "FROM daily_stats WHERE day>=?", (start_day,))
            lines.append(f"{label}: +{r['new_users']} users | ↓{r['incoming']} | ↑{r['outgoing']} | 📣{r['bs']}")
        errors = await self.db.fetchval("SELECT COUNT(*) FROM errors")
        lines += [
            "", "<b>System</b>",
            f"⏱ Uptime: <b>{human_duration(time.monotonic() - self.started_at)}</b>",
            f"⏳ Auto-Delete Timer: <b>{self.cache.auto_delete_minutes}m</b>",
            f"🗃 Stored users/messages: <b>{u['total']:,} / {m['stored']:,}</b>",
            "💾 Storage: <b>external PostgreSQL</b>",
            f"⚠️ Logged errors: <b>{errors:,}</b>",
        ]
        return "\n".join(lines)

    async def users_text(self) -> str:
        row = await self.db.fetchone(
            "SELECT COUNT(*) AS total, COALESCE(SUM(CASE WHEN is_banned=1 THEN 1 ELSE 0 END),0)::BIGINT AS banned, "
            "COALESCE(SUM(CASE WHEN is_active=1 THEN 1 ELSE 0 END),0)::BIGINT AS reachable FROM users")
        recent = await self.db.fetchall(
            "SELECT user_id,username,first_name,last_seen,is_banned FROM users ORDER BY last_seen DESC LIMIT 8")
        lines = ["<b>👥 User Management</b>", "",
                 f"Total: <b>{row['total']}</b> | Reachable: <b>{row['reachable']}</b> | Banned: <b>{row['banned']}</b>",
                 "", "<b>Recently active</b>"]
        for r in recent:
            label = f"@{r['username']}" if r["username"] else (r["first_name"] or "Unknown")
            lines.append(f"{'🚫' if r['is_banned'] else '👤'} <code>{r['user_id']}</code> - {esc(label)}")
        return "\n".join(lines)

    async def user_detail_text(self, user_id: int) -> Optional[str]:
        u = await self.db.fetchone("SELECT * FROM users WHERE user_id=?", (user_id,))
        if not u:
            return None
        m = await self.db.fetchone(
            "SELECT COUNT(*) AS total, "
            "COALESCE(SUM(CASE WHEN direction='incoming' THEN 1 ELSE 0 END),0)::BIGINT AS incoming, "
            "COALESCE(SUM(CASE WHEN direction IN ('outgoing','admin_reply') THEN 1 ELSE 0 END),0)::BIGINT AS outgoing "
            "FROM message_log WHERE user_id=?", (user_id,))
        return (
            "<b>👤 User Details</b>\n\n"
            f"ID: <code>{u['user_id']}</code>\n"
            f"Name: {esc((u['first_name'] or '') + ' ' + (u['last_name'] or ''))}\n"
            f"Username: {('@' + esc(u['username'])) if u['username'] else '-'}\n"
            f"Language: {esc(u['language_code'] or '-')}\n"
            f"Status: <b>{'Banned' if u['is_banned'] else 'Active'}</b>\n"
            f"Joined: {esc(u['created_at'])}\n"
            f"Last seen: {esc(u['last_seen'])}\n"
            f"Messages: {m['total']} ({m['incoming']} in / {m['outgoing']} out)"
        )

    # -------------------------------------------------------- backup/restore
    async def backup_database(self) -> Path:
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        snapshot = await self.db.snapshot()
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        archive = self.backup_dir / f"bot_backup_{stamp}_{uuid.uuid4().hex[:6]}.zip"
        db_path = archive.with_suffix(".db")
        bot_id = self.bot_id

        def write() -> None:
            conn = sqlite3.connect(db_path)
            try:
                conn.executescript(SQLITE_EXPORT_DDL)
                for table, rows in snapshot.items():
                    if rows:
                        cols = list(rows[0])
                        conn.executemany(
                            f"INSERT INTO {table} ({','.join(cols)}) VALUES ({','.join('?' for _ in cols)})",
                            [tuple(r[c] for c in cols) for r in rows])
                conn.commit()
            finally:
                conn.close()
            try:
                with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as z:
                    z.write(db_path, "bot.db")
                    z.writestr("manifest.json", json.dumps({
                        "database": "bot.db", "schema": 1, "bot_id": bot_id, "created_at": utcnow(),
                        "note": "Livegram data only. Clone registry is not included."}, indent=2))
            finally:
                db_path.unlink(missing_ok=True)

        await asyncio.to_thread(write)
        return archive

    async def restore_database(self, archive_path: Path) -> Path:
        if self.broadcast_tasks:
            raise ValueError("Cancel active broadcasts before restoring")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        bot_id = self.bot_id
        backup_dir = self.backup_dir

        def read() -> dict[str, list[dict]]:
            with zipfile.ZipFile(archive_path) as z:
                if sum(i.file_size for i in z.infolist()) > MAX_BACKUP_BYTES:
                    raise ValueError("Expanded backup exceeds 25 MB")
                manifest = json.loads(z.read("manifest.json"))
                name = manifest.get("database", "")
                if Path(name).name != name or not name.endswith(".db") or name not in z.namelist():
                    raise ValueError("Invalid backup manifest")
                if manifest.get("bot_id", bot_id) != bot_id:
                    raise ValueError("Backups can only be restored to their original bot")
                content = z.read(name)
            temp = backup_dir / f"check_{uuid.uuid4().hex}.db"
            temp.write_bytes(content)
            conn = sqlite3.connect(temp)  # private temp copy; also handles WAL-mode backups of the old bot
            conn.row_factory = sqlite3.Row
            try:
                if conn.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
                    raise ValueError("Invalid SQLite backup")
                result: dict[str, list[dict]] = {}
                for table in BACKUP_TABLES:
                    rows = conn.execute(f"SELECT * FROM {table} LIMIT {MAX_BACKUP_ROWS + 1}").fetchall()
                    if len(rows) > MAX_BACKUP_ROWS:
                        raise ValueError("Too many backup rows")
                    result[table] = [dict(r) for r in rows]
                return result
            except sqlite3.DatabaseError as exc:
                raise ValueError("Invalid SQLite backup") from exc
            finally:
                conn.close()
                temp.unlink(missing_ok=True)

        try:
            data = await asyncio.to_thread(read)
        except (zipfile.BadZipFile, KeyError, json.JSONDecodeError) as exc:
            raise ValueError("Invalid backup archive") from exc
        safety = await self.backup_database()
        # Never import another deployment's administrator identities or update IDs.
        data["owners"] = [{"user_id": self.owner_id, "added_at": utcnow()}]
        data["admins"] = []
        data["processed_updates"] = []
        await self.db.replace_all(data)
        await self.reload_cache()
        self.cache.seen_updates.clear()
        return safety

    # ------------------------------------------------------------- commands
    async def owner_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if not await self.ensure_owner(update):
            return
        context.user_data.clear()
        owners = len(self.cache.owners)
        admins = await self.db.fetchval("SELECT COUNT(*) FROM admins")
        text = ("<b>👑 Owner Panel</b>\n\n"
                f"Owners: <b>{owners}</b>\nManaged admins: <b>{admins}</b>\n\n"
                "Use this panel to add or remove administrators.")
        await safe_reply_text(update.effective_message, text, reply_markup=self.owner_keyboard(),
                              parse_mode=ParseMode.HTML)

    async def admin_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if not await self.ensure_admin(update):
            return
        context.user_data.clear()
        await safe_reply_text(update.effective_message, await self.panel_text(),
                              reply_markup=self.main_keyboard(), parse_mode=ParseMode.HTML)

    async def start_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        user, message = update.effective_user, update.effective_message
        if not user or not message:
            return
        c = self.cache
        if user.id in c.admins:
            await self.upsert_user(user)
            await safe_reply_text(message, await self.panel_text(),
                                  reply_markup=self.main_keyboard(), parse_mode=ParseMode.HTML)
            return
        if user.id in c.banned_users:
            return
        if c.settings.get("maintenance_mode") == "1":
            text = c.settings.get("maintenance_message", DEFAULT_MAINTENANCE)
        else:
            text = c.settings.get("start_message", DEFAULT_START)
        sent = await safe_reply_text(message, text)
        await self.upsert_user(user)
        if sent:
            await self.log_message("outgoing", user.id, None, "start", sent.chat_id, sent.message_id)

    # ------------------------------------------------------- callback router
    async def callback_router(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        q = update.callback_query
        if not q:
            return
        data = q.data or ""
        if data in {"admins", "admin_add", "admin_remove"}:
            if not await self.ensure_owner(update):
                return
        elif not await self.ensure_admin(update):
            return
        if not data.startswith(("toggle_ban:", "broadcast_cancel:", "autodelete_set:")):
            await safe_answer(q)

        ud = context.user_data
        c = self.cache

        if data in {"panel", "cancel"}:
            ud.clear()
            await safe_edit(q, await self.panel_text(), self.main_keyboard())
        elif data == "stats":
            await safe_edit(q, await self.statistics_text(),
                            kb([[("🔄 Refresh Statistics", "stats")], [("⬅️ Back", "panel")]]))
        elif data == "autodelete":
            ud["state"] = "auto_delete_minutes"
            await safe_edit(q, self.autodelete_text(), autodelete_keyboard())
        elif data.startswith("autodelete_set:"):
            mins = max(0, min(10080, int(data.split(":", 1)[1])))
            await self.set_setting("auto_delete_minutes", str(mins))
            ud["state"] = "auto_delete_minutes"
            await safe_answer(q, f"Auto-Delete set to {mins} minutes!" if mins > 0 else "Auto-Delete turned OFF!")
            await safe_edit(q, self.autodelete_text(), autodelete_keyboard())
        elif data == "users":
            ud.clear()
            await safe_edit(q, await self.users_text(), kb([
                [("🔎 Search", "user_search"), ("🚫 Ban / Unban", "ban_prompt")],
                [("📤 Export Users", "export_users")],
                [("⬅️ Back", "panel")]]))
        elif data == "user_search":
            ud["state"] = "user_search"
            await safe_edit(q, "<b>🔎 Search Users</b>\n\nSend a Telegram ID or exact username.", back_keyboard("users"))
        elif data == "ban_prompt":
            ud["state"] = "ban_target"
            await safe_edit(q, "<b>🚫 Ban / Unban User</b>\n\nSend the user's Telegram ID.", back_keyboard("users"))
        elif data.startswith("toggle_ban:"):
            uid = int(data.split(":", 1)[1])
            row = await self.db.fetchone("SELECT is_banned FROM users WHERE user_id=?", (uid,))
            if not row:
                await safe_answer(q, "User not found.", show_alert=True)
                return
            await safe_answer(q)
            new = 0 if row["is_banned"] else 1
            await self.db.execute("UPDATE users SET is_banned=? WHERE user_id=?", (new, uid))
            (c.banned_users.add if new else c.banned_users.discard)(uid)
            await safe_edit(q, await self.user_detail_text(uid), kb([
                [("✅ Unban" if new else "🚫 Ban", f"toggle_ban:{uid}")],
                [("⬅️ Back", "users")]]))
        elif data == "export_users":
            await self._export_users(context, q)
        elif data == "messages":
            await safe_edit(q, "<b>✏️ Configurable Messages</b>\n\nChoose the message to edit.", kb([
                [("👋 Welcome Message", "edit_start")],
                [("🛠 Maintenance Notice", "edit_maintenance")],
                [("⬅️ Back", "panel")]]))
        elif data in {"edit_start", "edit_maintenance"}:
            key = "start_message" if data == "edit_start" else "maintenance_message"
            ud["state"] = key
            current = c.settings.get(key, "")
            await safe_edit(q, f"<b>Edit Message</b>\n\nCurrent:\n<blockquote>{esc(current)}</blockquote>\n\n"
                               "Send the new message.", back_keyboard("messages"))
        elif data == "maintenance":
            enabled = c.settings.get("maintenance_mode") == "1"
            await safe_edit(q, f"<b>🛠 Maintenance Mode</b>\n\nStatus: <b>{'ON' if enabled else 'OFF'}</b>", kb([
                [("🔴 Disable" if enabled else "🟢 Enable", "maintenance_toggle")],
                [("✏️ Edit Notice", "edit_maintenance")],
                [("⬅️ Back", "panel")]]))
        elif data == "maintenance_toggle":
            enabled = c.settings.get("maintenance_mode") == "1"
            ud["confirm_action"] = "maintenance_toggle"
            await safe_edit(q, f"Confirm turning maintenance mode <b>{'OFF' if enabled else 'ON'}</b>?", kb([
                [("✅ Confirm", "confirm_maintenance"), ("❌ Cancel", "maintenance")]]))
        elif data == "confirm_maintenance":
            enabled = c.settings.get("maintenance_mode") == "1"
            await self.set_setting("maintenance_mode", "0" if enabled else "1")
            await safe_edit(q, f"✅ Maintenance mode is now <b>{'OFF' if enabled else 'ON'}</b>.", back_keyboard("panel"))
        elif data == "admins":
            admins = [r["user_id"] for r in await self.db.fetchall("SELECT user_id FROM admins ORDER BY added_at")]
            lines = ["<b>🛡 Admin Management</b>", "", "<b>Owners</b>"]
            lines += [f"👑 <code>{x}</code>" for x in sorted(c.owners)]
            lines += ["", "<b>Admins</b>"]
            lines += [f"🛡 <code>{x}</code>" for x in admins] or ["No managed admins."]
            await safe_edit(q, "\n".join(lines), kb([
                [("➕ Add Admin", "admin_add"), ("➖ Remove Admin", "admin_remove")],
                [("⬅️ Back", "panel")]]))
        elif data in {"admin_add", "admin_remove"}:
            ud["state"] = data
            await safe_edit(q, f"<b>{'Add' if data == 'admin_add' else 'Remove'} Admin</b>\n\nSend the Telegram user ID.",
                            back_keyboard("admins"))
        elif data == "broadcast":
            ud["state"] = "broadcast_content"
            await safe_edit(q, "<b>📣 New Broadcast</b>\n\nSend or forward one message containing the text/media to broadcast.",
                            back_keyboard("panel"))
        elif data == "broadcast_confirm":
            if self.broadcast_tasks:
                await safe_edit(q, "A broadcast is already running. Cancel it or wait for completion.", back_keyboard())
                return
            payload = ud.get("broadcast_payload")
            if not payload:
                await safe_edit(q, "The broadcast draft expired.", back_keyboard("panel"))
                return
            await safe_edit(q, "Preparing broadcast...", kb([[("⬅️ Panel", "panel")]]))
            bid = await self.db.insert_id(
                "INSERT INTO broadcasts(admin_id,source_chat_id,source_message_id,status,started_at) "
                "VALUES(?,?,?,?,?) RETURNING id",
                (q.from_user.id, payload["chat_id"], payload["message_id"], "queued", utcnow()))
            task = asyncio.create_task(self.run_broadcast(
                bid, payload["chat_id"], payload["message_id"], q.message.chat.id, q.message.message_id))
            self.broadcast_tasks[bid] = task
            ud.clear()
        elif data == "broadcast_discard":
            ud.clear()
            await safe_edit(q, "Broadcast cancelled before sending.", back_keyboard("panel"))
        elif data.startswith("broadcast_cancel:"):
            bid = int(data.split(":", 1)[1])
            await self.db.execute("UPDATE broadcasts SET status='cancelling' WHERE id=? AND status IN ('queued','running')", (bid,))
            await safe_answer(q, "Cancellation requested.", show_alert=True)
        elif data == "backup":
            recent = await self.db.fetchall("SELECT id,status,success,failed FROM broadcasts ORDER BY id DESC LIMIT 3")
            suffix = "\n".join(f"#{r['id']} {r['status']} ✅{r['success']} ❌{r['failed']}" for r in recent) or "No broadcasts yet."
            await safe_edit(q, f"<b>💾 Backup / Restore</b>\n\nRecent broadcasts:\n{suffix}", kb([
                [("💾 Create Backup", "backup_create")],
                [("♻️ Restore Backup", "restore_prompt")],
                [("⬅️ Back", "panel")]]))
        elif data == "backup_create":
            await safe_edit(q, "Creating a consistent backup...", back_keyboard("backup"))
            try:
                path = await self.backup_database()
                try:
                    with path.open("rb") as f:
                        await context.bot.send_document(q.from_user.id, document=f, caption="✅ Database and settings backup")
                finally:
                    path.unlink(missing_ok=True)
                await safe_edit(q, "✅ Backup created and sent.", back_keyboard("backup"))
            except ValueError as exc:
                await safe_edit(q, f"❌ {esc(exc)}", back_keyboard("backup"))
        elif data == "restore_prompt":
            ud["state"] = "restore_upload"
            await safe_edit(q, "<b>♻️ Restore Backup</b>\n\nUpload a backup ZIP created by this bot. It will be validated "
                               "before replacement, and a safety backup will be created.", back_keyboard("backup"))
        elif data == "restore_confirm":
            path = ud.get("restore_path")
            if not path or not Path(path).exists():
                await safe_edit(q, "The uploaded backup is no longer available.", back_keyboard("backup"))
                return
            await safe_edit(q, "Validating and restoring backup...", back_keyboard("backup"))
            try:
                safety = await self.restore_database(Path(path))
            except ValueError as exc:
                await safe_edit(q, f"❌ Restore failed: {esc(exc)}", back_keyboard("backup"))
                return
            finally:
                Path(path).unlink(missing_ok=True)
            ud.clear()
            try:
                with safety.open("rb") as f:
                    await context.bot.send_document(q.from_user.id, document=f, caption="Safety backup taken before restore")
            except (TelegramError, OSError):
                pass
            finally:
                safety.unlink(missing_ok=True)
            await safe_edit(q, "✅ Restore completed successfully!\nManaged admins were reset; re-add them if needed.",
                            back_keyboard("panel"))
        elif data == "system":
            errors = await self.db.fetchall("SELECT context,error,created_at FROM errors ORDER BY id DESC LIMIT 5")
            running = await self.db.fetchval("SELECT COUNT(*) FROM broadcasts WHERE status IN ('queued','running','cancelling')")
            lines = ["<b>🩺 System Status</b>", "",
                     f"Uptime: <b>{human_duration(time.monotonic() - self.started_at)}</b>",
                     "Database: <b>external PostgreSQL</b>",
                     f"Running broadcasts: <b>{running}</b>", "", "<b>Recent errors</b>"]
            lines += [f"{esc(r['created_at'])} - {esc(r['context'])}: {esc(r['error'][:120])}" for r in errors] or ["No recorded errors."]
            await safe_edit(q, "\n".join(lines), kb([[("🔄 Refresh", "system")], [("⬅️ Back", "panel")]]))

    async def _export_users(self, context, q) -> None:
        rows = await self.db.fetchall("SELECT * FROM users ORDER BY created_at")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        path = self.backup_dir / f"users_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.csv"
        header = ["user_id", "username", "first_name", "last_name", "language_code",
                  "is_banned", "is_active", "created_at", "last_seen"]
        try:
            with path.open("w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(header)
                writer.writerows([[csv_safe(r[h]) for h in header] for r in rows])
            with path.open("rb") as doc:
                await context.bot.send_document(q.from_user.id, document=doc, caption=f"Exported {len(rows)} users.")
        finally:
            path.unlink(missing_ok=True)

    # ------------------------------------------------- admin text-state input
    async def admin_state_message(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
        user, message = update.effective_user, update.effective_message
        c = self.cache
        if not user or user.id not in c.admins:
            return False
        ud = context.user_data
        state = ud.get("state")
        if not state:
            return False
        if state in {"admin_add", "admin_remove"} and user.id not in c.owners:
            ud.clear()
            await safe_reply_text(message, "Owner access required.")
            return True
        text = message.text.strip() if message.text else ""

        if state in {"start_message", "maintenance_message"}:
            if not text:
                await safe_reply_text(message, "Send a text message.", reply_markup=back_keyboard("messages"))
                return True
            await self.set_setting(state, text)
            ud.clear()
            await safe_reply_text(message, "✅ Message updated.", reply_markup=back_keyboard("messages"))
        elif state == "auto_delete_minutes":
            if not text.isdigit():
                await safe_reply_text(message, "कृपया केवल मिनट का नंबर लिखकर भेजें (जैसे 5, 2, 1, 20 या बंद करने के लिए 0):",
                                      reply_markup=autodelete_keyboard())
                return True
            mins = max(0, min(10080, int(text)))
            await self.set_setting("auto_delete_minutes", str(mins))
            ud.clear()
            msg = (f"✅ Auto-Delete समय <b>{mins} मिनट</b> सेट कर दिया गया है।" if mins > 0
                   else "✅ Auto-Delete <b>बंद (OFF)</b> कर दिया गया है।")
            await safe_reply_text(message, msg, parse_mode=ParseMode.HTML, reply_markup=self.main_keyboard())
        elif state == "user_search":
            if text.startswith("@"):
                row = await self.db.fetchone("SELECT user_id FROM users WHERE lower(username)=lower(?)", (text[1:],))
                uid = row["user_id"] if row else None
            else:
                uid = parse_id(text)
            detail = await self.user_detail_text(uid) if uid is not None else None
            if not detail:
                await safe_reply_text(message, "User not found. Send an exact ID or username.", reply_markup=back_keyboard("users"))
            else:
                ud.clear()
                banned = await self.db.fetchval("SELECT is_banned FROM users WHERE user_id=?", (uid,))
                await safe_reply_text(message, detail, parse_mode=ParseMode.HTML, reply_markup=kb([
                    [("✅ Unban" if banned else "🚫 Ban", f"toggle_ban:{uid}")], [("⬅️ Back", "users")]]))
        elif state == "ban_target":
            uid = parse_id(text)
            if uid is None:
                await safe_reply_text(message, "Send a numeric Telegram ID.")
                return True
            banned = await self.db.fetchval("SELECT is_banned FROM users WHERE user_id=?", (uid,))
            if banned is None:
                await safe_reply_text(message, "User not found.", reply_markup=back_keyboard("users"))
            else:
                ud.clear()
                await safe_reply_text(message, f"Confirm {'unbanning' if banned else 'banning'} <code>{uid}</code>?",
                                      parse_mode=ParseMode.HTML,
                                      reply_markup=kb([[("✅ Confirm", f"toggle_ban:{uid}"), ("❌ Cancel", "users")]]))
        elif state in {"admin_add", "admin_remove"}:
            uid = parse_id(text)
            if uid is None:
                await safe_reply_text(message, "Send a numeric Telegram ID.")
                return True
            if state == "admin_add":
                await self.db.execute("INSERT INTO admins(user_id,added_at,added_by) VALUES(?,?,?) ON CONFLICT DO NOTHING",
                                      (uid, utcnow(), user.id))
                c.admins.add(uid)
                result = "✅ Admin added."
            else:
                if uid in c.owners:
                    await safe_reply_text(message, "Owners cannot be removed from the admin manager.",
                                          reply_markup=back_keyboard("admins"))
                    return True
                await self.db.execute("DELETE FROM admins WHERE user_id=?", (uid,))
                c.admins.discard(uid)
                result = "✅ Admin removed."
            ud.clear()
            await safe_reply_text(message, result, reply_markup=back_keyboard("admins"))
        elif state == "broadcast_content":
            ud["broadcast_payload"] = {"chat_id": message.chat_id, "message_id": message.message_id}
            ud.pop("state", None)
            count = await self.db.fetchval("SELECT COUNT(*) FROM users WHERE is_banned=0 AND is_active=1")
            await safe_reply_text(
                message, f"<b>Confirm Broadcast</b>\n\nRecipients: <b>{count:,}</b>\n"
                         "The broadcast runs in the background and can be cancelled.",
                parse_mode=ParseMode.HTML,
                reply_markup=kb([[("🚀 Start Broadcast", "broadcast_confirm")], [("❌ Discard", "broadcast_discard")]]))
        elif state == "restore_upload":
            doc = message.document
            if not doc or not (doc.file_name or "").lower().endswith(".zip"):
                await safe_reply_text(message, "Upload a ZIP backup created by this bot.", reply_markup=back_keyboard("backup"))
                return True
            if doc.file_size and doc.file_size > MAX_BACKUP_BYTES:
                await safe_reply_text(message, "Backup is too large (maximum 25 MB).")
                return True
            self.backup_dir.mkdir(parents=True, exist_ok=True)
            path = self.backup_dir / f"uploaded_{uuid.uuid4().hex}.zip"
            try:
                tg_file = await doc.get_file()
                await tg_file.download_to_drive(path)
                with zipfile.ZipFile(path) as zf:
                    if "manifest.json" not in zf.namelist():
                        raise ValueError("no manifest")
            except (TelegramError, zipfile.BadZipFile, ValueError, OSError):
                path.unlink(missing_ok=True)
                await safe_reply_text(message, "Invalid backup archive.", reply_markup=back_keyboard("backup"))
                return True
            ud["restore_path"] = str(path)
            ud.pop("state", None)
            await safe_reply_text(
                message, "⚠️ Restoring replaces current data. A safety backup will be created first. Confirm?",
                reply_markup=kb([[("♻️ Restore Now", "restore_confirm"), ("❌ Cancel", "cancel")]]))
        return True

    # ------------------------------------------------------------ broadcasts
    async def _deliver(self, bid: int, uid: int, src_chat: int, src_msg: int) -> None:
        bot = self.app.bot
        for attempt in (1, 2):
            try:
                await bot.copy_message(chat_id=uid, from_chat_id=src_chat, message_id=src_msg)
                await self.mark_delivery(bid, uid, True, None)
                return
            except RetryAfter as exc:
                if attempt == 2:
                    await self.mark_delivery(bid, uid, False, str(exc)[:500])
                    return
                await asyncio.sleep(float(exc.retry_after) + 0.5)
            except (TimedOut, NetworkError) as exc:
                if attempt == 2:
                    await self.mark_delivery(bid, uid, False, str(exc)[:500])
                    return
                await asyncio.sleep(2)
            except Forbidden as exc:
                await self.db.execute("UPDATE users SET is_active=0 WHERE user_id=?", (uid,))
                await self.mark_delivery(bid, uid, False, str(exc)[:500])
                return
            except BadRequest as exc:
                if any(s in str(exc).lower() for s in ("chat not found", "user is deactivated", "bot was blocked")):
                    await self.db.execute("UPDATE users SET is_active=0 WHERE user_id=?", (uid,))
                await self.mark_delivery(bid, uid, False, str(exc)[:500])
                return
            except TelegramError as exc:
                await self.mark_delivery(bid, uid, False, str(exc)[:500])
                return

    async def _broadcast_progress(self, bid: int, chat_id: int, message_id: int) -> None:
        last_text = ""
        while True:
            await asyncio.sleep(4)
            row = await self.db.fetchone("SELECT total,success,failed,status FROM broadcasts WHERE id=?", (bid,))
            if not row:
                return
            remaining = max(0, row["total"] - row["success"] - row["failed"])
            text = (f"<b>📣 Broadcast #{bid}</b>\n\nTotal: {row['total']:,}\n✅ Success: {row['success']:,}\n"
                    f"❌ Failed: {row['failed']:,}\n⏳ Remaining: {remaining:,}\nStatus: <b>{esc(row['status'])}</b>")
            if text != last_text:
                try:
                    await self.app.bot.edit_message_text(
                        text, chat_id=chat_id, message_id=message_id, parse_mode=ParseMode.HTML,
                        reply_markup=kb([[("🛑 Cancel", f"broadcast_cancel:{bid}")]]))
                    last_text = text
                except RetryAfter as exc:
                    await asyncio.sleep(float(exc.retry_after) + 0.5)
                except TelegramError as exc:
                    if "Message is not modified" not in str(exc):
                        log.debug("Progress edit skipped: %s", exc)
            if row["status"] not in {"queued", "running", "cancelling"}:
                return

    async def run_broadcast(self, bid: int, src_chat: int, src_msg: int, progress_chat: int, progress_msg: int) -> None:
        ptask: Optional[asyncio.Task] = None
        try:
            total = await self.db.fetchval("SELECT COUNT(*) FROM users WHERE is_banned=0 AND is_active=1")
            await self.db.execute("UPDATE broadcasts SET status='running',total=? WHERE id=?", (total, bid))
            ptask = asyncio.create_task(self._broadcast_progress(bid, progress_chat, progress_msg))
            last, sent = 0, 0
            while True:
                status = await self.db.fetchval("SELECT status FROM broadcasts WHERE id=?", (bid,))
                if status != "running":
                    break
                page = await self.db.fetchall(
                    "SELECT user_id FROM users WHERE is_banned=0 AND is_active=1 AND user_id>? "
                    "ORDER BY user_id LIMIT ?", (last, BROADCAST_PAGE))
                if not page:
                    break
                for row in page:
                    last = row["user_id"]
                    sent += 1
                    if sent % 10 == 0 and await self.db.fetchval("SELECT status FROM broadcasts WHERE id=?", (bid,)) != "running":
                        break
                    await self._deliver(bid, last, src_chat, src_msg)
            status = await self.db.fetchval("SELECT status FROM broadcasts WHERE id=?", (bid,))
            final = "cancelled" if status == "cancelling" else "completed"
            await self.db.execute("UPDATE broadcasts SET status=?,finished_at=? WHERE id=?", (final, utcnow(), bid))
            if ptask:
                ptask.cancel()
                await asyncio.gather(ptask, return_exceptions=True)
                ptask = None
            row = await self.db.fetchone("SELECT total,success,failed,status FROM broadcasts WHERE id=?", (bid,))
            if row:
                try:
                    await self.app.bot.edit_message_text(
                        f"<b>📣 Broadcast #{bid} {esc(row['status'])}</b>\n\nTotal: {row['total']:,}\n"
                        f"✅ Success: {row['success']:,}\n❌ Failed: {row['failed']:,}\n"
                        f"Not attempted: {max(0, row['total'] - row['success'] - row['failed']):,}",
                        chat_id=progress_chat, message_id=progress_msg, parse_mode=ParseMode.HTML,
                        reply_markup=kb([[("⬅️ Panel", "panel")]]))
                except TelegramError:
                    pass
        except asyncio.CancelledError:
            try:
                await asyncio.shield(self.db.execute(
                    "UPDATE broadcasts SET status='interrupted',finished_at=? WHERE id=?", (utcnow(), bid)))
            except Exception:
                pass
            raise
        except Exception as exc:
            await self.record_error(f"broadcast:{bid}", exc)
            try:
                await self.db.execute("UPDATE broadcasts SET status='failed',finished_at=?,error=? WHERE id=?",
                                      (utcnow(), str(exc)[:1000], bid))
                await self.app.bot.edit_message_text(f"❌ Broadcast #{bid} failed: {esc(exc)}", chat_id=progress_chat,
                                                     message_id=progress_msg, parse_mode=ParseMode.HTML)
            except Exception:
                pass
        finally:
            if ptask:
                ptask.cancel()
                await asyncio.gather(ptask, return_exceptions=True)
            self.broadcast_tasks.pop(bid, None)

    # --------------------------------------------------- user <-> admin relay
    async def forward_user_message(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        user, message = update.effective_user, update.effective_message
        if not user or not message:
            return
        c = self.cache
        if user.id in c.admins:
            if await self.admin_state_message(update, context):
                return
            await self.admin_reply(update, context)
            return
        if user.id in c.banned_users:
            return
        if c.settings.get("maintenance_mode") == "1":
            sent = await safe_reply_text(message, c.settings.get("maintenance_message", DEFAULT_MAINTENANCE))
            if sent:
                self.spawn(self.log_message("outgoing", user.id, None, "maintenance", sent.chat_id, sent.message_id))
            return
        delay = c.auto_delete_minutes * 60
        delete_at = (time.time() + delay) if delay > 0 else None

        async def to_one(admin_id: int) -> None:
            try:
                # Direct forward: shows the user's clickable profile on top.
                fwd = await context.bot.forward_message(chat_id=admin_id, from_chat_id=message.chat_id,
                                                        message_id=message.message_id)
                c.forward_map[(admin_id, fwd.message_id)] = (user.id, message.message_id)
                await self.save_forward_mapping(admin_id, fwd.message_id, user.id, message.message_id, delete_at)
            except TelegramError as exc:
                self.spawn(self.record_error(f"forward_to_admin:{admin_id}", exc))

        await asyncio.gather(*(to_one(a) for a in list(c.admins)))
        await self.upsert_user(user)
        await self.log_message("incoming", user.id, None, message_kind(message), message.chat_id, message.message_id)

    async def admin_reply(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        message = update.effective_message
        if not message or not message.reply_to_message:
            return
        key = (message.chat_id, message.reply_to_message.message_id)
        cached = self.cache.forward_map.get(key)
        if cached:
            uid, user_msg_id = cached
        else:
            row = await self.db.fetchone(
                "SELECT user_id,user_message_id FROM forward_map WHERE admin_chat_id=? AND admin_message_id=?", key)
            if not row:
                return
            uid, user_msg_id = row["user_id"], row["user_message_id"]
        try:
            sent = await context.bot.copy_message(uid, message.chat_id, message.message_id)
            await self.log_message("admin_reply", uid, update.effective_user.id, message_kind(message),
                                   uid, sent.message_id, user_msg_id)
        except Forbidden as exc:
            self.spawn(self.db.execute("UPDATE users SET is_active=0 WHERE user_id=?", (uid,)))
            self.spawn(self.record_error(f"admin_reply:{uid}", exc))
            await safe_reply_text(message, "❌ Delivery failed: the user blocked or stopped the bot.")
        except TelegramError as exc:
            self.spawn(self.record_error(f"admin_reply:{uid}", exc))
            await safe_reply_text(message, f"❌ Delivery failed: {esc(exc)}", parse_mode=ParseMode.HTML)

    async def message_router(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if update.effective_message and update.effective_user:
            await self.forward_user_message(update, context)

    async def error_handler(self, update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
        exc = context.error or RuntimeError("Unknown error")
        log.error("Unhandled error in bot %s: %s: %s", self.bot_id, type(exc).__name__, exc,
                  exc_info=exc if not isinstance(exc, (TimedOut, NetworkError)) else None)
        if isinstance(update, Update):
            self.last_update_failed = True
        self.spawn(self.record_error("update_handler", exc))
        if (isinstance(update, Update) and update.effective_message and update.effective_user
                and update.effective_user.id in self.cache.admins):
            await safe_reply_text(update.effective_message, "❌ The operation failed. Details were logged.")

    # ----------------------------------------------------------- application
    def build_application(self) -> Application:
        app = (
            ApplicationBuilder()
            .token(self.token)
            .updater(None)                 # webhook mode: updates are pushed in by our HTTP server
            .concurrent_updates(False)
            .connection_pool_size(4)
            .connect_timeout(10.0)
            .read_timeout(15.0)
            .write_timeout(15.0)
            .pool_timeout(10.0)
            .rate_limiter(AIORateLimiter(overall_max_rate=15, max_retries=1))
            .build()
        )
        app.add_handler(CommandHandler("start", self.start_command), group=0)
        app.add_handler(CommandHandler("dkboss", self.owner_command), group=0)
        app.add_handler(CommandHandler("admin", self.admin_command), group=0)
        app.add_handler(CallbackQueryHandler(self.callback_router), group=0)
        app.add_handler(MessageHandler(filters.ALL & ~filters.COMMAND, self.message_router), group=1)
        app.add_error_handler(self.error_handler)
        self.app = app
        return app


# =====================================================================
# 8. BOT INSTANCE (lifecycle of one hosted bot: main or clone)
# =====================================================================
class Instance:
    def __init__(self, manager: "Manager", bot_id: int, token: str, owner: int):
        self.manager, self.id = manager, bot_id
        self.is_main = bot_id == manager.cfg.main_id
        self.core = LivegramCore(token, owner, bot_id, manager.cfg.database_url)
        if self.is_main:
            # Management entry points are shown in the main owner's panel only.
            self.core.extra_owner_rows = [[("Bot Manager", "cm:list")], [("Bot Creators", "cm:creators")]]
        self.ready = False
        self.sweeper: Optional[asyncio.Task] = None
        self.lock = asyncio.Lock()
        self.failures: dict[int, int] = {}
        self.last_error = ""

    @property
    def webhook_url(self) -> str:
        return f"{self.manager.cfg.base_url}/telegram/{self.id}"

    async def set_webhook(self) -> None:
        await self.core.app.bot.set_webhook(
            url=self.webhook_url, secret_token=webhook_secret(self.manager.cfg.secret, self.id),
            allowed_updates=["message", "callback_query"], drop_pending_updates=False, max_connections=1)

    async def verify_webhook(self) -> None:
        """Self-healing: re-register the webhook if Telegram lost or changed it."""
        info = await self.core.app.bot.get_webhook_info()
        if info.url != self.webhook_url:
            log.warning("Bot %s webhook mismatch; re-registering", self.id)
            await self.set_webhook()

    async def start(self) -> None:
        async with self.lock:
            if self.ready:
                return
            try:
                await self.core.init_db()
                await self.core.interrupt_broadcasts()
                app = self.core.build_application()
                app.add_handler(TypeHandler(Update, self.guard), group=-10)
                await app.initialize()
                await app.start()
                await self.set_webhook()
                self.ready = True
                self.last_error = ""
                self.sweeper = asyncio.create_task(self.sweep(), name=f"sweep-{self.id}")
                log.info("Bot %s started (%s)", self.id, "main" if self.is_main else "clone")
            except BaseException as exc:
                self.last_error = type(exc).__name__
                await self.cleanup()
                raise

    async def cleanup(self) -> None:
        self.ready = False
        if self.sweeper:
            self.sweeper.cancel()
            await asyncio.gather(self.sweeper, return_exceptions=True)
            self.sweeper = None
        await self.core.cancel_tasks()
        app = self.core.app
        if app:
            try:
                if app.running:
                    await asyncio.wait_for(app.stop(), timeout=10)
                await asyncio.wait_for(app.shutdown(), timeout=10)
            except Exception:
                log.warning("Bot %s shutdown incomplete", self.id)
            self.core.app = None
            self.core.started_at = time.monotonic()
        await self.core.db.close()

    async def stop(self) -> None:
        async with self.lock:
            # The webhook is kept on purpose: stopped clones acknowledge and drop
            # updates, and restarting reuses the same stable endpoint.
            await self.cleanup()

    async def sweep(self) -> None:
        """Per-bot maintenance: due deletions, retention, temp files, idle state."""
        core = self.core
        while True:
            try:
                rows = await core.db.fetchall(
                    "SELECT admin_chat_id,admin_message_id FROM pending_deletes WHERE delete_at<=? "
                    "ORDER BY delete_at LIMIT 30", (time.time(),))
                for row in rows:
                    try:
                        await core.app.bot.delete_message(row["admin_chat_id"], row["admin_message_id"])
                    except (BadRequest, Forbidden):
                        pass  # already gone / too old: nothing more to do
                    except TelegramError:
                        continue  # temporary problem: stays pending for the next pass
                    await core.remove_deleted_mapping(row["admin_chat_id"], row["admin_message_id"])
                cutoff = (datetime.now(timezone.utc) - timedelta(days=7)).isoformat(timespec="seconds")
                await core.db.execute("DELETE FROM processed_updates WHERE processed_at<?", (cutoff,))
                await core.db.execute(
                    "DELETE FROM errors WHERE id NOT IN (SELECT id FROM errors ORDER BY id DESC LIMIT 300)")
                if core.backup_dir.exists():
                    for path in core.backup_dir.glob("*"):
                        if path.is_file() and path.stat().st_mtime < time.time() - 3600:
                            path.unlink(missing_ok=True)
                now = time.time()
                for uid, state in list(core.app.user_data.items()):
                    if state.get("cm_time", now) < now - 600:
                        state.clear()
                    if state.get("_last_seen", 0) < now - 3600:
                        core.app.drop_user_data(uid)
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                log.warning("Maintenance for bot %s: %s", self.id, type(exc).__name__)
            await asyncio.sleep(SWEEP_INTERVAL)

    async def guard(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        chat = update.effective_chat
        if not chat or chat.type != "private":
            raise ApplicationHandlerStop
        context.user_data["_last_seen"] = time.time()
        if not self.is_main:
            return
        try:
            handled = await self.manager.manage(update, context)
        except Exception as exc:
            log.error("Clone manager failure: %s: %s", type(exc).__name__, exc)
            self.core.last_update_failed = True
            await self.core.record_error("clone_manager", exc)
            raise ApplicationHandlerStop
        if handled:
            raise ApplicationHandlerStop


# =====================================================================
# 9. CLONE MANAGER (registry, permissions, token vault, management UI)
# =====================================================================
class Req:
    """Small per-update helper used by the clone-management UI."""

    def __init__(self, manager: "Manager", update: Update, context: ContextTypes.DEFAULT_TYPE):
        self.manager, self.update, self.context = manager, update, context
        self.message = update.effective_message
        self.uid = update.effective_user.id
        self.query = update.callback_query
        self.text = self.message.text.strip() if self.message and self.message.text else ""
        self.command = self.text.split()[0].split("@")[0].lower() if self.text.startswith("/") else ""
        self.data = (self.query.data or "") if self.query else ""
        self.state = context.user_data

    async def show(self, body: str, rows=None) -> None:
        markup = kb(rows) if rows else None
        if self.query:
            await safe_answer(self.query)
            await safe_edit(self.query, body, markup, parse_mode=None)
        elif self.message:
            await safe_reply_text(self.message, body, reply_markup=markup)


class Manager:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.vault = make_vault(cfg.secret)
        self.main = Instance(self, cfg.main_id, cfg.token, cfg.owner_id)
        self.instances: dict[int, Instance] = {cfg.main_id: self.main}
        self.creation_lock = asyncio.Lock()
        self.loaded = False
        self.stopping = False
        self.registry_ready = False
        self.retry_at: dict[int, tuple[float, int]] = {}
        self.next_webhook_check = 0.0

    # ---------------------------------------------------------------- basics
    @property
    def db(self) -> Database:
        return self.main.core.db

    def decrypt(self, row) -> str:
        return self.vault.decrypt(row["encrypted_token"].encode()).decode()

    async def audit(self, actor: int, bot_id: Optional[int], action: str) -> None:
        await self.db.execute("INSERT INTO master_audit(actor,bot_id,action,created_at) VALUES(?,?,?,?)",
                              (actor, bot_id, action, utcnow()))

    async def creator(self, uid: int):
        if uid == self.cfg.owner_id:
            return {"max_bots": self.cfg.max_child_bots}
        return await self.db.fetchone("SELECT * FROM bot_creators WHERE user_id=?", (uid,))

    async def allowed(self, uid: int, row) -> bool:
        return uid == self.cfg.owner_id or (row["created_by"] == uid and bool(await self.creator(uid)))

    async def set_status(self, bot_id: int, status: str, error: str = "") -> None:
        await self.db.execute("UPDATE child_bots SET status=?,last_error=? WHERE bot_id=?", (status, error, bot_id))

    # ------------------------------------------------------------- recovery
    async def supervise(self) -> None:
        """Background loop: start the main bot, recover clones, heal webhooks."""
        delay = 2
        while not self.stopping:
            try:
                if not self.main.ready:
                    await self.main.start()
                if not self.registry_ready:
                    await self.db.executescript(split_statements(REGISTRY_SCHEMA))
                    self.registry_ready = True
                for row in await self.db.fetchall("SELECT bot_id FROM child_bots ORDER BY created_at"):
                    await self.recover_child(row["bot_id"])
                self.loaded = True
                delay = 2
                if time.time() >= self.next_webhook_check:
                    self.next_webhook_check = time.time() + WEBHOOK_CHECK_INTERVAL
                    await self.heal_webhooks()
                await asyncio.sleep(SUPERVISE_INTERVAL)
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                log.warning("Startup/recovery: %s: %s; retrying in %ss", type(exc).__name__, exc, delay)
                await asyncio.sleep(delay)
                delay = min(60, delay * 2)

    async def heal_webhooks(self) -> None:
        for inst in list(self.instances.values()):
            if inst.ready:
                try:
                    await inst.verify_webhook()
                except Exception as exc:
                    log.warning("Webhook check for %s failed: %s", inst.id, type(exc).__name__)

    async def recover_child(self, bot_id: int, force: bool = False) -> None:
        async with self.creation_lock:
            row = await self.db.fetchone("SELECT * FROM child_bots WHERE bot_id=?", (bot_id,))
            if not row or not row["enabled"]:
                return
            inst = self.instances.get(bot_id)
            if inst is not None and inst.ready:
                return
            when, streak = self.retry_at.get(bot_id, (0.0, 0))
            if not force and time.time() < when:
                return
            try:
                if inst is None:
                    inst = Instance(self, bot_id, self.decrypt(row), row["admin_id"])
                    self.instances[bot_id] = inst
                await inst.start()
                await self.set_status(bot_id, "live")
                self.retry_at.pop(bot_id, None)
            except Exception as exc:
                streak += 1
                self.retry_at[bot_id] = (time.time() + min(600, 30 * 2 ** min(streak, 5)), streak)
                await self.set_status(bot_id, "error", type(exc).__name__)
                log.warning("Clone %s could not start: %s", bot_id, type(exc).__name__)

    # ------------------------------------------------------------ UI entry
    async def bot_list(self, uid: int):
        if uid == self.cfg.owner_id:
            rows = await self.db.fetchall("SELECT * FROM child_bots ORDER BY bot_id")
        else:
            if not await self.creator(uid):
                return "You need creator permission. Use /requestclone.", []
            rows = await self.db.fetchall("SELECT * FROM child_bots WHERE created_by=? ORDER BY bot_id", (uid,))
        buttons = [[(f"@{r['username']} - {r['status']}", f"cm:view:{r['bot_id']}")] for r in rows]
        buttons.append([("Create Bot", "cm:create")])
        return f"Bot Manager: {len(rows)} registered clone(s).", buttons

    async def manage(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
        """Handle clone-management traffic for the main bot. True = consumed."""
        r = Req(self, update, context)
        if r.command == "/cancel" or r.data == "cm:cancel":
            r.state.clear()
            await r.show("Cancelled.")
            return True
        if r.command == "/requestclone":
            await self.request_clone(r)
            return True
        if r.command in ("/grantcreator", "/revokecreator", "/setcloneadmin"):
            await self.owner_command(r)
            return True
        if r.command in ("/create", "/bots", "/creators") or r.data.startswith("cm:"):
            await self.menu(r)
            return True
        if r.state.get("cm_state"):
            return await self.wizard(r)
        return False

    async def begin_creation(self, r: Req) -> None:
        if not await self.creator(r.uid):
            await r.show("Admin approval is required. Use /requestclone.")
            return
        r.state.clear()
        r.state.update(cm_state="token", cm_time=time.time())
        await r.show("Send your BotFather token here in private chat. The service will host your bot and "
                     "therefore needs access to this token. Use /cancel to exit.")

    async def request_clone(self, r: Req) -> None:
        if await self.creator(r.uid):
            await r.show("You already have permission. Use /create.")
            return
        existing = await self.db.fetchone("SELECT * FROM clone_requests WHERE user_id=?", (r.uid,))
        if existing:
            await r.show(f"Your request status: {existing['status']}. Contact the owner for changes.")
            return
        await self.db.execute("INSERT INTO clone_requests(user_id,status,created_at) VALUES(?,?,?) ON CONFLICT DO NOTHING",
                              (r.uid, "pending", utcnow()))
        try:
            await r.context.bot.send_message(
                self.cfg.owner_id, f"Clone permission request from Telegram user {r.uid}",
                reply_markup=kb([[("Approve (1 bot)", f"cm:approve:{r.uid}"), ("Deny", f"cm:deny:{r.uid}")]]))
        except TelegramError:
            log.warning("Could not notify the owner of a clone request (owner must press Start on the main bot)")
        await r.show("Permission request sent to the main owner.")

    async def owner_command(self, r: Req) -> None:
        if r.uid != self.cfg.owner_id:
            await r.show("Main owner access required.")
            return
        usage = "Usage: /grantcreator USER_ID LIMIT; /revokecreator USER_ID; /setcloneadmin BOT_ID USER_ID"
        parts = r.text.split()
        restart: Optional[int] = None
        try:
            target = int(parts[1])
            if target <= 0:
                raise ValueError
            if r.command == "/grantcreator":
                limit = int(parts[2]) if len(parts) > 2 else 1
                if not 1 <= limit <= self.cfg.max_child_bots:
                    raise ValueError
                await self.db.execute(
                    "INSERT INTO bot_creators(user_id,max_bots,granted_by,created_at) VALUES(?,?,?,?) "
                    "ON CONFLICT(user_id) DO UPDATE SET max_bots=excluded.max_bots,granted_by=excluded.granted_by",
                    (target, limit, r.uid, utcnow()))
                await self.db.execute("UPDATE clone_requests SET status='approved' WHERE user_id=?", (target,))
            elif r.command == "/revokecreator":
                await self.db.execute("DELETE FROM bot_creators WHERE user_id=?", (target,))
                await self.db.execute("UPDATE clone_requests SET status='revoked' WHERE user_id=?", (target,))
            else:
                new_owner = int(parts[2])
                if new_owner <= 0:
                    raise ValueError
                await self.reassign_admin(target, new_owner)
                restart = target
            await self.audit(r.uid, target, r.command[1:])
        except (ValueError, IndexError):
            await r.show(usage)
            return
        if restart is not None:
            await self.recover_child(restart, force=True)
        await r.show("Updated. Revoking creator permission does not stop existing clones. "
                     "Admin reassignment removes previous clone admins.")

    async def reassign_admin(self, bot_id: int, new_owner: int) -> None:
        async with self.creation_lock:
            row = await self.db.fetchone("SELECT * FROM child_bots WHERE bot_id=?", (bot_id,))
            if not row:
                raise ValueError("unknown clone")
            inst = self.instances.pop(bot_id, None)
            if inst:
                async with inst.lock:
                    await inst.cleanup()
            temp = Instance(self, bot_id, self.decrypt(row), new_owner)
            try:
                await temp.core.init_db()
                async with temp.core.db.transaction() as tx:
                    await tx.execute("DELETE FROM owners WHERE user_id<>?", (new_owner,))
                    await tx.execute("DELETE FROM admins")
            finally:
                await temp.core.db.close()
            await self.db.execute("UPDATE child_bots SET admin_id=? WHERE bot_id=?", (new_owner, bot_id))

    async def menu(self, r: Req) -> None:
        uid, data, cmd = r.uid, r.data, r.command
        owner = self.cfg.owner_id
        if cmd == "/create" or data == "cm:create":
            await self.begin_creation(r)
        elif cmd == "/creators" or data == "cm:creators":
            if uid != owner:
                await r.show("Main owner access required.")
                return
            rows = await self.db.fetchall("SELECT * FROM bot_creators ORDER BY user_id")
            pending = await self.db.fetchall(
                "SELECT user_id FROM clone_requests WHERE status='pending' ORDER BY created_at LIMIT 20")
            body = "Approved creators:\n" + "\n".join(f"{x['user_id']} - limit {x['max_bots']}" for x in rows)
            body += "\n\n/grantcreator USER_ID LIMIT\n/revokecreator USER_ID\n/setcloneadmin BOT_ID USER_ID"
            buttons = [[(f"Approve {x['user_id']}", f"cm:approve:{x['user_id']}"), ("Deny", f"cm:deny:{x['user_id']}")]
                       for x in pending]
            await r.show(body[:3900], buttons)
        elif data.startswith(("cm:approve:", "cm:deny:")):
            if uid != owner:
                await r.show("Main owner access required.")
                return
            try:
                target = int(data.rsplit(":", 1)[1])
            except ValueError:
                await r.show("Invalid request.")
                return
            approve = data.startswith("cm:approve:")
            if approve:
                await self.db.execute(
                    "INSERT INTO bot_creators(user_id,max_bots,granted_by,created_at) VALUES(?,?,?,?) "
                    "ON CONFLICT(user_id) DO NOTHING", (target, 1, uid, utcnow()))
            await self.db.execute("UPDATE clone_requests SET status=? WHERE user_id=?",
                                  ("approved" if approve else "denied", target))
            await self.audit(uid, None, f"creator_{'approved' if approve else 'denied'}:{target}")
            await r.show("Permission request updated.")
            try:
                await r.context.bot.send_message(
                    target, "Clone permission approved. Use /create." if approve else "Clone permission request denied.")
            except TelegramError:
                pass
        elif data == "cm:confirm":
            await self.confirm(r)
        elif data.startswith(("cm:view:", "cm:start:", "cm:stop:", "cm:delete:", "cm:remove:")):
            await self.clone_action(r)
        else:
            body, buttons = await self.bot_list(uid)
            await r.show(body, buttons)

    async def clone_action(self, r: Req) -> None:
        try:
            _, action, raw_id = r.data.split(":")
            bot_id = int(raw_id)
        except ValueError:
            await r.show("Invalid request.")
            return
        row = await self.db.fetchone("SELECT * FROM child_bots WHERE bot_id=?", (bot_id,))
        if not row or not await self.allowed(r.uid, row):
            await r.show("Not authorized or bot no longer registered.")
            return
        if action == "delete":
            await r.show("Unregister this clone? Its Livegram data is retained in PostgreSQL. "
                         "This does not delete the bot account in BotFather.",
                         [[("Confirm unregister", f"cm:remove:{bot_id}"), ("Cancel", f"cm:view:{bot_id}")]])
            return
        if action in ("stop", "remove"):
            async with self.creation_lock:
                await self.db.execute("UPDATE child_bots SET enabled=0,status='stopped' WHERE bot_id=?", (bot_id,))
                inst = self.instances.get(bot_id)
                if inst:
                    await inst.stop()
                if action == "remove":
                    await self.db.execute("DELETE FROM child_bots WHERE bot_id=?", (bot_id,))
                    self.instances.pop(bot_id, None)
                    self.retry_at.pop(bot_id, None)
            await self.audit(r.uid, bot_id, action)
        elif action == "start":
            await self.db.execute("UPDATE child_bots SET enabled=1,status='starting' WHERE bot_id=?", (bot_id,))
            await self.recover_child(bot_id, force=True)
            await self.audit(r.uid, bot_id, action)
        row = await self.db.fetchone("SELECT * FROM child_bots WHERE bot_id=?", (bot_id,))
        if not row:
            await r.show("Clone unregistered.")
            return
        inst = self.instances.get(bot_id)
        stats = ""
        if inst and inst.ready:
            try:
                stats = f"\nUsers: {await inst.core.db.fetchval('SELECT COUNT(*) FROM users')}"
            except Exception:
                stats = ""
        body = (f"@{row['username']}\nBot ID: {bot_id}\nAdmin: {row['admin_id']}\nCreator: {row['created_by']}\n"
                f"Status: {row['status']}\nLast error: {row['last_error'] or '-'}{stats}\n"
                f"Open: https://t.me/{row['username']}")
        await r.show(body, [[("Start", f"cm:start:{bot_id}"), ("Stop", f"cm:stop:{bot_id}")],
                            [("Unregister", f"cm:delete:{bot_id}")], [("Back", "cm:list")]])

    async def wizard(self, r: Req) -> bool:
        """Two-step creation dialog: token, then administrator ID."""
        state = r.state
        if time.time() - state.get("cm_time", 0) > 600 or not await self.creator(r.uid):
            state.clear()
            await r.show("Creation session expired or permission was revoked. Use /create.")
            return True
        if r.command:
            state.clear()
            return False
        step = state["cm_state"]
        if step == "token":
            if not TOKEN_FULL_RE.fullmatch(r.text):
                await r.show("Send a valid BotFather token, or /cancel.")
                return True
            try:
                async with Bot(r.text) as bot:
                    me = await bot.get_me()
            except TelegramError:
                await r.show("Telegram could not validate that token. Check it with BotFather and try again.")
                return True
            if me.id == self.cfg.main_id:
                await r.show("The main bot cannot be registered as a clone.")
                return True
            state.update(cm_token=self.vault.encrypt(r.text.encode()).decode(), cm_bot_id=me.id,
                         cm_username=me.username, cm_state="admin", cm_time=time.time())
            try:
                await r.message.delete()
            except TelegramError:
                pass
            await r.show(f"Validated @{me.username}. Send the numeric Telegram ID of its administrator. "
                         f"Send {r.uid} to administer it yourself.")
        elif step == "admin":
            admin = parse_id(r.text)
            if admin is None:
                await r.show("Send a positive numeric Telegram user ID.")
            else:
                state.update(cm_admin=admin, cm_state="confirm", cm_time=time.time())
                await r.show(f"Create @{state['cm_username']} with admin {admin}?",
                             [[("Confirm", "cm:confirm"), ("Cancel", "cm:cancel")]])
        else:
            await r.show("Use the confirmation buttons or /cancel.")
        return True

    async def confirm(self, r: Req) -> None:
        state = r.state
        if state.get("cm_state") != "confirm" or time.time() - state.get("cm_time", 0) > 600:
            state.clear()
            await r.show("Creation session expired. Use /create.")
            return
        async with self.creation_lock:
            creator = await self.creator(r.uid)
            total = await self.db.fetchval("SELECT COUNT(*) FROM child_bots")
            own = await self.db.fetchval("SELECT COUNT(*) FROM child_bots WHERE created_by=?", (r.uid,))
            if not creator or total >= self.cfg.max_child_bots or own >= creator["max_bots"]:
                state.clear()
                await r.show("Permission revoked or clone limit reached.")
                return
            bot_id = state["cm_bot_id"]
            if await self.db.fetchone("SELECT bot_id FROM child_bots WHERE bot_id=?", (bot_id,)):
                state.clear()
                await r.show("That bot is already registered.")
                return
            admin, encrypted, username = state["cm_admin"], state["cm_token"], state["cm_username"]
            await self.db.execute(
                "INSERT INTO child_bots(bot_id,username,encrypted_token,admin_id,created_by,enabled,status,created_at) "
                "VALUES(?,?,?,?,?,?,?,?)", (bot_id, username, encrypted, admin, r.uid, 1, "starting", utcnow()))
            state.clear()
            await self.audit(r.uid, bot_id, "created")
            inst = Instance(self, bot_id, self.vault.decrypt(encrypted.encode()).decode(), admin)
            self.instances[bot_id] = inst
            try:
                await inst.core.init_db()
                async with inst.core.db.transaction() as tx:
                    await tx.execute("DELETE FROM owners WHERE user_id<>?", (admin,))
                    await tx.execute("DELETE FROM admins")
                await inst.start()
                await self.set_status(bot_id, "live")
                await r.show(f"Clone started: https://t.me/{username}\n"
                             "Its administrator must open it and press Start. Use /bots to manage it.")
            except Exception as exc:
                await self.set_status(bot_id, "error", type(exc).__name__)
                await r.show("Clone registered, but startup failed. Use /bots to inspect or retry. "
                             "Automatic recovery will also retry.")

    # --------------------------------------------------------------- webhook
    async def webhook(self, request: web.Request) -> web.Response:
        try:
            bot_id = int(request.match_info["bot_id"])
        except ValueError:
            raise web.HTTPNotFound()
        sent = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "").encode()
        if not hmac.compare_digest(sent, webhook_secret(self.cfg.secret, bot_id).encode()):
            raise web.HTTPForbidden()
        if not self.loaded:
            raise web.HTTPServiceUnavailable()
        if bot_id != self.cfg.main_id:
            row = await self.db.fetchone("SELECT enabled FROM child_bots WHERE bot_id=?", (bot_id,))
            if not row or not row["enabled"]:
                return web.Response(text="stopped")
        inst = self.instances.get(bot_id)
        if not inst or not inst.ready:
            raise web.HTTPServiceUnavailable()
        async with inst.lock:
            if not inst.ready:
                raise web.HTTPServiceUnavailable()
            core = inst.core
            try:
                update = Update.de_json(await request.json(), core.app.bot)
                if update is None or not isinstance(update.update_id, int):
                    raise ValueError("Missing update ID")
            except (ValueError, TypeError, KeyError, AttributeError):
                raise web.HTTPBadRequest()
            uid = update.update_id
            if uid in core.cache.seen_updates or await core.db.fetchval(
                    "SELECT 1 FROM processed_updates WHERE update_id=?", (uid,)):
                return web.Response(text="duplicate")
            core.last_update_failed = False
            try:
                await asyncio.wait_for(core.app.process_update(update), UPDATE_TIMEOUT)
                if core.last_update_failed:
                    raise RuntimeError("Update handler failed")
            except Exception as exc:
                attempts = inst.failures.get(uid, 0) + 1
                if len(inst.failures) > 500:
                    inst.failures.clear()
                inst.failures[uid] = attempts
                if attempts < MAX_UPDATE_ATTEMPTS:
                    raise web.HTTPServiceUnavailable()
                # Poison update: acknowledge it so Telegram can deliver the ones behind it.
                log.error("Bot %s dropped update %s after %s failed attempts", bot_id, uid, attempts)
                inst.failures.pop(uid, None)
                await core.record_error("dropped_update", exc)
            else:
                inst.failures.pop(uid, None)
            try:
                await core.db.execute(
                    "INSERT INTO processed_updates(update_id,processed_at) VALUES(?,?) ON CONFLICT DO NOTHING",
                    (uid, utcnow()))
            except Exception as exc:
                log.warning("Could not persist update id for bot %s: %s", bot_id, type(exc).__name__)
            core.cache.remember_update(uid)
        return web.Response(text="ok")

    async def shutdown(self) -> None:
        self.stopping = True
        self.loaded = False
        for inst in list(self.instances.values()):
            try:
                await asyncio.wait_for(inst.stop(), timeout=12)
            except Exception:
                log.warning("Bot %s did not stop cleanly", inst.id)


# =====================================================================
# 10. HTTP SERVER, KEEP-ALIVE AND ENTRY POINT
# =====================================================================
async def keepalive(cfg: Config) -> None:
    """Best-effort ping of our own public URL so Render's free tier stays awake."""
    async with ClientSession(timeout=ClientTimeout(total=15)) as session:
        while True:
            await asyncio.sleep(KEEPALIVE_INTERVAL)
            try:
                async with session.get(f"{cfg.base_url}/healthz") as resp:
                    await resp.read()
            except Exception as exc:
                log.debug("Keep-alive ping failed: %s", type(exc).__name__)


def build_web_app(manager: Manager) -> web.Application:
    @web.middleware
    async def isolate_errors(request, handler):
        try:
            return await handler(request)
        except web.HTTPException:
            raise
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            log.warning("Request failed: %s: %s", type(exc).__name__, exc)
            raise web.HTTPServiceUnavailable()

    async def health(_request):
        return web.json_response({"status": "ok"})

    async def ready(_request):
        ok = manager.loaded and manager.main.ready
        if ok:
            try:
                await asyncio.wait_for(manager.db.fetchval("SELECT 1"), timeout=3)
            except Exception:
                ok = False
        return web.json_response({"ready": ok}, status=200 if ok else 503)

    app = web.Application(client_max_size=1024 * 1024, middlewares=[isolate_errors])
    app.router.add_get("/", health)
    app.router.add_get("/healthz", health)
    app.router.add_get("/readyz", ready)
    app.router.add_post("/telegram/{bot_id:\\d+}", manager.webhook)
    return app


async def run(cfg: Config) -> None:
    manager = Manager(cfg)
    runner = web.AppRunner(build_web_app(manager), access_log=None)
    await runner.setup()
    # Bind the port first so Render's health check passes while bots start in the background.
    await web.TCPSite(runner, "0.0.0.0", cfg.port).start()
    log.info("HTTP listener on port %s", cfg.port)
    tasks = [asyncio.create_task(manager.supervise(), name="supervise")]
    if cfg.keepalive:
        tasks.append(asyncio.create_task(keepalive(cfg), name="keepalive"))
    stop = asyncio.Event()
    loop = asyncio.get_running_loop()
    for sig in (signal.SIGTERM, signal.SIGINT):
        try:
            loop.add_signal_handler(sig, stop.set)
        except NotImplementedError:  # e.g. Windows development
            pass
    try:
        await stop.wait()
    finally:
        log.info("Shutting down")
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        await manager.shutdown()
        await runner.cleanup()


def main() -> None:
    setup_logging()
    try:
        cfg = load_config()
    except ConfigError as exc:
        log.critical("%s", exc)
        sys.exit(1)
    asyncio.run(run(cfg))


if __name__ == "__main__":
    main()
