import os
import sys
import fcntl
import asyncio
import sqlite3
import math
import random
import logging
import time
import aiohttp
from aiohttp import web
import hmac
import hashlib
import urllib.parse
import json
import re
import html
import socket
import subprocess
import tempfile
import shutil
import zipfile
import io
from types import SimpleNamespace
from datetime import datetime, timedelta
from typing import Optional, List, Tuple, Dict, Any

try:
    from PIL import Image
except Exception:
    Image = None
try:
    import pytesseract
except Exception:
    pytesseract = None

from aiogram import Bot, Dispatcher, F, BaseMiddleware
from aiogram.exceptions import TelegramBadRequest
from aiogram.client.default import DefaultBotProperties
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import StatesGroup, State
from aiogram.types import (
    FSInputFile, ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove,
    InlineKeyboardMarkup, InlineKeyboardButton, CallbackQuery, Message, Dice, BufferedInputFile
)

# ==============================================================================
# SINGLE-INSTANCE LOCK (PREVENTS DUPLICATE BOT POLLING GLITCHES)
# ==============================================================================
_lock_fp = None
def acquire_single_instance_lock():
    global _lock_fp
    if _lock_fp is not None:
        return True
    lock_file_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".bot.lock")
    try:
        _lock_fp = open(lock_file_path, "w")
        fcntl.flock(_lock_fp, fcntl.LOCK_EX | fcntl.LOCK_NB)
        _lock_fp.write(f"{os.getpid()}\n")
        _lock_fp.flush()
        return True
    except (IOError, BlockingIOError):
        print(f"[FATAL] Another instance of RajuConfig Bot is already running! (Lock held by another process). Exiting PID {os.getpid()} immediately.")
        sys.exit(0)

# ==============================================================================
# 1. BOT CONFIGURATION & CONSTANTS
# ==============================================================================
# Persistent database storage:
# Railway's app filesystem is ephemeral across redeploys unless a Volume is mounted.
# Configure a Railway Volume mounted at /data and set DATA_DIR=/data.
_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
_IS_RAILWAY = any(os.getenv(k) for k in ("RAILWAY_ENVIRONMENT", "RAILWAY_PROJECT_ID", "RAILWAY_SERVICE_ID"))
DATA_DIR = os.getenv("DATA_DIR", "/data" if _IS_RAILWAY else _SCRIPT_DIR).strip() or ("/data" if _IS_RAILWAY else _SCRIPT_DIR)
os.makedirs(DATA_DIR, exist_ok=True)
DB_PATH = os.getenv("DB_PATH", os.path.join(DATA_DIR, "yp_shop.db")).strip()
if not DB_PATH:
    DB_PATH = os.path.join(DATA_DIR, "yp_shop.db")

# One-time migration: preserve an existing local DB when switching to a new persistent path.
# It only copies when the destination database does not exist, never overwriting live data.
_legacy_db_path = os.path.join(_SCRIPT_DIR, "yp_shop.db")
if os.path.abspath(DB_PATH) != os.path.abspath(_legacy_db_path) and not os.path.exists(DB_PATH) and os.path.isfile(_legacy_db_path):
    try:
        shutil.copy2(_legacy_db_path, DB_PATH)
        print(f"[DB] Migrated existing database once: {_legacy_db_path} -> {DB_PATH}")
    except Exception as _db_migrate_error:
        print(f"[DB] WARNING: Could not migrate old database to {DB_PATH}: {_db_migrate_error}")
if _IS_RAILWAY and not os.getenv("DATA_DIR") and not os.getenv("DB_PATH"):
    print("[DB] IMPORTANT: DATA_DIR defaults to /data on Railway. Attach a Railway Volume mounted at /data or data may still disappear after redeploys.")
print(f"[DB] Database path: {DB_PATH}")
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    if "--dashboard-only" in sys.argv or "--dashboard" in sys.argv or os.getenv("DASHBOARD_ONLY", "").lower() in ("1", "true", "yes"):
        BOT_TOKEN = "9211669903:AAHSfFS7ty9DsZOCJUEDx9OF7zM3NpR_BGA"
    else:
        raise RuntimeError("BOT_TOKEN is missing. Set a NEW bot token in hosting Environment Variables; do not reuse any token previously shared in source code.")
BOT_USERNAME = ""

class AdminContainer(int):
    """
    Subclass of int that supports multiple admin IDs.
    Behaves as a valid integer ID for aiogram and database methods,
    while treating any ID in ADMIN_IDS as equal when checking equality.
    """
    def __new__(cls, primary, all_ids):
        obj = super().__new__(cls, primary)
        obj.all_ids = set(all_ids)
        return obj
    def __eq__(self, other):
        return other in self.all_ids
    def __ne__(self, other):
        return other not in self.all_ids
    def __contains__(self, item):
        return item in self.all_ids
    def __iter__(self):
        return iter(self.all_ids)

# Admin identity: keep ADMIN_ID as an int because the existing admin handlers
# compare Telegram user IDs directly against it. Optional ADMIN_IDS allows
# additional admins without breaking those legacy checks.
# Built-in owner identity: no Railway/hosting environment input is required.
ADMIN_ID = int(os.getenv("ADMIN_ID", "").strip() or "")
ADMIN_IDS = {6547154209}
for _extra_admin in os.getenv("ADMIN_IDS", "").split(","):
    _extra_admin = _extra_admin.strip()
    if _extra_admin.isdigit():
        ADMIN_IDS.add(int(8887951720))
ADMIN_CONTACT = ""

USDT_TO_INR = 90.0
VIP_DISCOUNT_PERCENTAGE = 15.0
VIP_PRICE_INR = 299.0

WELCOME_STICKER_ID = os.getenv("WELCOME_STICKER_ID", "").strip()  # Optional: set a real sticker file_id in hosting env
SPIN_DELAY_SECONDS = 2.5

# Purchase/payment click protection. These guards stop duplicate callback
# delivery from creating multiple orders or multiple fulfilments.
_purchase_locks: Dict[tuple, asyncio.Lock] = {}
_payment_verify_locks: Dict[str, asyncio.Lock] = {}
_callback_cooldowns: Dict[tuple, float] = {}
_CALLBACK_COOLDOWN_SECONDS = 3.5

def _get_purchase_lock(user_id: int, prod_id: int) -> asyncio.Lock:
    key = (int(user_id), int(prod_id))
    lock = _purchase_locks.get(key)
    if lock is None:
        lock = asyncio.Lock()
        _purchase_locks[key] = lock
    return lock

def _callback_is_on_cooldown(key: tuple, seconds: float = _CALLBACK_COOLDOWN_SECONDS) -> bool:
    now = time.monotonic()
    last = _callback_cooldowns.get(key, 0.0)
    if now - last < seconds:
        return True
    _callback_cooldowns[key] = now
    return False

FIXED_CATEGORIES = [
    "ANDROID NON ROOT PANEL",
    "ANDROID ROOT PANEL",
    "IPHONE PANEL",
    "PC PANEL"
]

def get_all_categories() -> List[str]:
    try:
        rows = db_query("SELECT name FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True)
        if rows is not None and len(rows) > 0:
            return [r[0] for r in rows if r[0]]
    except Exception as e:
        logger.error(f"Error fetching categories: {e}")
    return []

# ==============================================================================
# YOUR PREMIUM EMOJIS – all required emoji IDs
# ==============================================================================
DEFAULT_EMOJIS = {
    'product_store': '6163205892834598715',
    'profile': '6035084557378654059',
    'add_balance': '5278467510604160626',
    'history': '6160968017304888311',
    'referral': '6032609071373226027',
    'support': '6161112036148255813',
    'ludo_spin': '6147764669361692707',
    'back': '6039539366177541657',
    'upi': '5807750375033278838',
    'binance': '5843689746538173057',
    'reseller': '6120436698695338614',
    'tutorial': '5368653135101310687',
    'download': '6161336001512874965',
    'telegram': '6161096071754818473',
    'whatsapp': '6118193823823698862',
    'welcome': '5312361253610475399',
    'vip': '6086672466132865380',
    'category_android_non_root': '6161172706856282588',
    'category_android_root': '6161449831031118974',
    'category_iphone': '6161399700172840408',
    'category_pc': '5350554349074391003',
    'grid_id': '5474625972751837256',
    'name': '5215399540814781035',
    'account_level': '6129584162992034014',
    'regular_user': '5904630315946611415',
    'wallet': '6210859306602995217',
    'current_balance': '5316711376876485361',
    'global_stats': '6161437856662298090',
    'total_orders': '6160968017304888311',
    'total_spent': '5197503331215361533',
    'total_referrals': '5938196735200333756',
    'joined_grid': '5433614043006903194',
    'info_icon': '6037421444789440735',
    'check_icon': '6161241250239356403',
    'checkbox_icon': '6161437856662298090',
    'shield_icon': '6086672466132865380',
    'money_icon': '5890848474563352982',
    'redeem_icon': '5377624166436445368',
    'wallet_left': '6210859306602995217',
    'wallet_right': '5305699699204837855',
    'point_down': '6161302621027049305',
}

LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()
_LOG_FORMAT = "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
logging.basicConfig(level=getattr(logging, LOG_LEVEL, logging.INFO), format=_LOG_FORMAT, handlers=[logging.StreamHandler(sys.stdout)], force=True)
logger = logging.getLogger(__name__)
try:
    _log_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot_activity.log")
    _file_handler = logging.FileHandler(_log_file, encoding="utf-8")
    _file_handler.setFormatter(logging.Formatter(_LOG_FORMAT))
    logger.addHandler(_file_handler)
except Exception:
    logger.exception("Could not initialize file logging; stdout logging remains active")
logger.info("Logging initialized; stdout and optional bot_activity.log are enabled")

bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode="HTML"))
dp = Dispatcher()

class CallbackTraceMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        if isinstance(event, CallbackQuery):
            logger.info("CALLBACK IN: user_id=%s data=%r message_id=%s", event.from_user.id, event.data, getattr(event.message, "message_id", None))
        try:
            result = await handler(event, data)
            if isinstance(event, CallbackQuery):
                logger.info("CALLBACK OUT: user_id=%s data=%r", event.from_user.id, event.data)
            return result
        except Exception:
            logger.exception("CALLBACK FAILED: user_id=%s data=%r", getattr(getattr(event, "from_user", None), "id", None), getattr(event, "data", None))
            raise

dp.callback_query.outer_middleware(CallbackTraceMiddleware())

async def notify_admins(text: str, reply_markup=None, parse_mode: str = "HTML"):
    for aid in ADMIN_IDS:
        try:
            await bot.send_message(aid, text, reply_markup=reply_markup, parse_mode=parse_mode)
        except Exception as e:
            logger.warning(f"Could not send notification to admin {aid}: {e}")

def _extract_generated_keys(payload: Any) -> List[str]:
    """Extract only actual key strings from HK Tamim/API response shapes."""
    found: List[str] = []
    seen = set()
    key_names = {"key", "keys", "license_key", "generated_key", "license", "serial", "code", "full_value"}

    def add(value):
        if isinstance(value, str):
            value = value.strip()
            if value and value.upper() not in {"KEY_NOT_FOUND", "ERROR", "FAILED", "NONE", "NULL", "0", "FALSE"}:
                if value not in seen:
                    seen.add(value)
                    found.append(value)
        elif isinstance(value, (int, float)) and not isinstance(value, bool):
            text_value = str(value).strip()
            if text_value and text_value not in seen:
                seen.add(text_value)
                found.append(text_value)
        elif isinstance(value, list):
            for item in value:
                add(item)
        elif isinstance(value, dict):
            # Prefer a provider's explicit full_value, then key; never stringify a whole dict.
            for name in ("full_value", "key", "license_key", "generated_key", "serial", "code"):
                if name in value:
                    add(value[name])
            for name in ("keys", "licenses", "items"):
                if name in value:
                    add(value[name])

    if isinstance(payload, dict):
        # Common response shapes: {"key": "..."} or {"data": {"key": "..."}}
        for name in ("full_value", "key", "license_key", "generated_key", "serial", "code", "keys", "data", "licenses", "items"):
            if name in payload:
                add(payload[name])
    else:
        add(payload)
    return found


def fmt_curr(amount: float) -> str:
    return f"₹{amount:,.2f}"

def natural_sort_key(value: Any) -> List[Any]:
    """Sort names naturally, with numeric sequences in numeric order."""
    text = str(value or "").strip()
    return [int(part) if part.isdigit() else part.casefold()
            for part in re.split(r"(\d+)", text)]

def product_name_sort_key(value: Any) -> tuple:
    """Keep Over plans together and numeric (1 Over, 3 Over, 6 Over), rather than
    letting alphabetic Day labels appear between an Over sequence."""
    text = str(value or "").strip()
    lower = text.casefold()
    match = re.search(r"(\d+(?:\.\d+)?)\s*(over|overs|hour|hours|hr|hrs|day|days|week|weeks|month|months|year|years)\b", lower)
    if match:
        number = float(match.group(1))
        unit = match.group(2)
        if unit in ("over", "overs"):
            rank = 0
        elif unit in ("hour", "hours", "hr", "hrs"):
            rank = 1
        elif unit in ("day", "days"):
            rank = 2
        elif unit in ("week", "weeks"):
            rank = 3
        elif unit in ("month", "months"):
            rank = 4
        else:
            rank = 5
        return (0, rank, number, natural_sort_key(text))
    return (1, 99, 0, natural_sort_key(text))

def normalize_validity_group(value: Any) -> str:
    """Normalize common package durations so 1 Day/1 Days, 3 Hour/3 Hours, etc.
    appear as one admin pricing group. Unknown/custom validity strings are
    normalized conservatively and remain their own group.
    """
    raw = re.sub(r"\s+", " ", str(value or "").strip())
    if not raw:
        return "custom"
    # Match a numeric duration anywhere in the label, not only at the beginning.
    # This handles names such as "Bala Movie 1 Over" and "M1 1 Over" in one group.
    m = re.search(r"(?:^|\s)(\d+(?:\.\d+)?)\s*([A-Za-z]+)\b", raw, re.IGNORECASE)
    if m:
        number, unit = m.group(1), m.group(2).lower()
        unit_map = {
            "day":"day", "days":"day",
            "hour":"hour", "hours":"hour", "hr":"hour", "hrs":"hour",
            "week":"week", "weeks":"week",
            "month":"month", "months":"month",
            "year":"year", "years":"year",
            "over":"over", "overs":"over",
            "minute":"minute", "minutes":"minute", "min":"minute", "mins":"minute",
        }
        return f"{number} {unit_map.get(unit, unit)}"
    return raw.casefold()

def display_validity_group(key: str) -> str:
    if not key:
        return "Custom"
    if key == "custom":
        return "Custom"
    parts = key.split(" ", 1)
    if len(parts) == 2 and re.match(r"^\d", parts[0]):
        n, unit = parts
        return f"{n} {unit.title()}"
    return key.title()

def get_common_validity_groups(active_only: bool = True) -> List[Tuple[str, int]]:
    where = "WHERE is_active=1" if active_only else ""
    rows = db_query(f"SELECT validity, name FROM products {where}", fetchall=True) or []
    counts: Dict[str, int] = {}
    for row in rows:
        validity = row[0] if row else ""
        name = row[1] if len(row) > 1 else ""
        # Prefer explicit validity; if it does not contain a recognized duration,
        # fall back to the package name.
        key = normalize_validity_group(validity)
        if key == "custom" or not re.search(r"\d+(?:\.\d+)?\s*[A-Za-z]+\b", str(validity or "")):
            key = normalize_validity_group(name)
        counts[key] = counts.get(key, 0) + 1
    return sorted(counts.items(), key=lambda item: natural_sort_key(display_validity_group(item[0])))


def product_matches_validity_group(validity: Any, name: Any, target_key: str) -> bool:
    """Match a common duration using both DB validity and package name.
    This fixes older products where the duration was stored in name rather than validity.
    """
    candidates = [validity, name]
    for value in candidates:
        if normalize_validity_group(value) == target_key:
            return True
    return False

# ==============================================================================
# 2. DATABASE FUNCTIONS
# ==============================================================================
def db_query(query: str, params: tuple = (), fetchone: bool = False, fetchall: bool = False, commit: bool = True) -> Any:
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    c = conn.cursor()
    try:
        c.execute(query, params)
        if fetchone:
            res = c.fetchone()
        elif fetchall:
            res = c.fetchall()
        else:
            res = None
        if commit: conn.commit()
        return res
    except Exception as e:
        logger.error(f"DB Error: {e} | Query: {query} | Params: {params}")
        if commit: conn.rollback()
        return None
    finally:
        conn.close()

def get_setting(key: str, default: str = "") -> str:
    val = db_query("SELECT value FROM settings WHERE key=?", (key,), fetchone=True)
    return val[0] if val and val[0] else default

def set_setting(key: str, value: str) -> None:
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (key, value))

def gateway_enabled(name: str) -> bool:
    key = f"gateway_{name.lower()}_status"
    return (get_setting(key, "ON") or "ON").upper() == "ON"

def is_admin(user_id: int) -> bool:
    # ADMIN_ID is kept as an int for backwards compatibility; ADMIN_IDS is the
    # authoritative collection used by all admin checks.
    try:
        uid = int(user_id)
        dynamic = set()
        try:
            dynamic = {int(x) for x in (get_setting("dynamic_admin_ids", "") or "").split(",") if x.strip().isdigit()}
        except Exception:
            pass
        return uid in ({int(a) for a in ADMIN_IDS} | dynamic)
    except Exception:
        return False

def is_product_in_maintenance(prod_id: int) -> bool:
    try:
        row = db_query("SELECT is_maintenance FROM products WHERE id=?", (prod_id,), fetchone=True)
        return bool(row and row[0])
    except Exception:
        return False

def set_product_maintenance(prod_id: int, is_maintenance: int) -> None:
    try:
        db_query("UPDATE products SET is_maintenance=? WHERE id=?", (1 if is_maintenance else 0, prod_id))
    except Exception as e:
        logger.error(f"Failed to set product maintenance: {e}")


def log_activity(user_id: int, action: str, details: str = "") -> None:
    try:
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        db_query(
            "INSERT INTO activity_logs (user_id, action, details, timestamp) VALUES (?, ?, ?, ?)",
            (user_id, action, details, timestamp)
        )
    except Exception as e:
        logger.error(f"Failed to log activity: {e}")

def get_emoji(slot: str, default_id: str = None) -> str:
    stored = get_setting(f"emoji_{slot}", "")
    emoji_id = stored if stored and stored.isdigit() else (default_id or DEFAULT_EMOJIS.get(slot, ""))
    if emoji_id:
        return f'<tg-emoji emoji-id="{emoji_id}">✨</tg-emoji>'
    return "✨"

def get_emoji_icon(slot: str, default_id: str = None) -> str | None:
    """Return a numeric custom-emoji ID for Telegram button icon fields.

    Telegram rejects ``icon_custom_emoji_id`` when the value is sent as a
    non-numeric string.  Keep the premium emoji IDs, but convert them to an
    actual integer before aiogram serializes the button.
    """
    stored = str(get_setting(f"emoji_{slot}", "") or "").strip()
    candidate = stored if stored.isdigit() else str(default_id or DEFAULT_EMOJIS.get(slot, "") or "").strip()
    if not candidate.isdigit():
        return None
    try:
        return str(candidate)
    except (TypeError, ValueError, OverflowError):
        return None

def as_emoji_icon_id(value) -> str | None:
    """Normalize any stored custom-emoji ID to the numeric type Telegram expects."""
    if value is None:
        return None
    if isinstance(value, bool):
        return None
    try:
        text = str(value).strip()
        return text if text.isdigit() else None
    except (TypeError, ValueError, OverflowError):
        return None

# ==============================================================================
# 3. STRING RESOURCES – using placeholders for premium emojis
# ==============================================================================
UI_TEXTS = {
    "start_menu": (
        "✨ <b>WELCOME TO THE STORE</b>\n\n"
        "{product_store} Product Store : all key purchase & instantly delivery\n"
        "{profile} My Profile : check your account information\n"
        "{add_balance} Add Balance : deposit balance & secure service\n"
        "{history} All History : check all key purchase history\n"
        "{referral} Referral : invite friends & earn rewards\n"
        "{tutorial} Tutorial : view tutorial and work this bot\n"
        "{support} Support : bot problem fixed for support admin\n"
        "{ludo_spin} Ludo Spin : play game and win balance\n"
        "{download} Download Files : download latest apk for safety."
    ),
    "download_files": (
        "🗂 <b><u>DOWNLOAD PREMIUM APK & FILES 📊</u></b>\n\n"
        "🌐 All our highly secured, premium, and updated files\n"
        "are securely hosted on our private channel! ⚠️⛔️\n\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "📱 <b>WHAT YOU GET:</b> 📌\n\n"
        "✔️ Latest APK Updates 🔔\n"
        "✔️ 100% Virus Free & Secure ‼️\n"
        "✔️ All Configs & Scripts 🌸\n"
        "✔️ Complete Installation Guides 🔺\n\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "⌨️ Tap the button below to access the Download Channel! 📝"
    ),
    "lucky_dice_result": (
        "{ludo_spin} <b><u>LUCKY DICE RESULT 🔨 💯</u></b>\n\n"
        "🎲 <b>Dice Value:</b> {dice_value}\n\n"
        "💸 <b>You Won:</b> {won_amount}\n"
        "💰 <b>Total Balance:</b> {new_balance}\n\n"
        "Congratulations! Come back after 24 hours."
    ),
    "vip_menu": (
        "🌟 <b><u>VIP MEMBERSHIP CLUB</u></b> 🌟\n\n"
        "Unlock premium benefits and permanent discounts!\n\n"
        "💎 <b>VIP Benefits:</b>\n"
        "• Flat 15% off on ALL products (Stacks with Reseller!)\n"
        "• Priority Support\n"
        "• Exclusive VIP-only giveaways\n\n"
        "💳 <b>VIP Price:</b> ₹299.00 (Lifetime)\n"
        "👤 <b>Your Status:</b> {vip_status}"
    ),
    "add_balance_menu": (
        "{add_balance} <b>ADD BALANCE</b> {info_icon}\n\n"
        "{info_icon} Select your preferred payment method. {check_icon}\n\n"
        "┣ {upi} UPI — Fast Indian payments {checkbox_icon}\n"
        "┣ {binance} Binance — Crypto payments {checkbox_icon}\n\n"
        "{shield_icon} Payments are verified securely. {check_icon}"
    )
}

def get_ui_text(key: str, **kwargs) -> str:
    val = db_query("SELECT value FROM settings WHERE key=?", (f"ui_{key}",), fetchone=True)
    template = val[0] if val and val[0] else UI_TEXTS.get(key, "")

    emoji_map = {
        '{product_store}': get_emoji('product_store'),
        '{profile}': get_emoji('profile'),
        '{add_balance}': get_emoji('add_balance'),
        '{history}': get_emoji('history'),
        '{referral}': get_emoji('referral'),
        '{tutorial}': get_emoji('tutorial'),
        '{support}': get_emoji('support'),
        '{ludo_spin}': get_emoji('ludo_spin'),
        '{download}': get_emoji('download'),
        '{telegram}': get_emoji('telegram'),
        '{whatsapp}': get_emoji('whatsapp'),
        '{upi}': get_emoji('upi'),
        '{binance}': get_emoji('binance'),
        '{info_icon}': get_emoji('info_icon'),
        '{check_icon}': get_emoji('check_icon'),
        '{checkbox_icon}': get_emoji('checkbox_icon'),
        '{shield_icon}': get_emoji('shield_icon'),
        '{money_icon}': get_emoji('money_icon'),
        '{redeem_icon}': get_emoji('redeem_icon'),
        '{wallet_left}': get_emoji('wallet_left'),
        '{wallet_right}': get_emoji('wallet_right'),
        '{point_down}': get_emoji('point_down'),
        '{vip}': get_emoji('vip'),
    }
    for placeholder, emoji_tag in emoji_map.items():
        template = template.replace(placeholder, emoji_tag)

    if kwargs:
        try:
            return template.format(**kwargs)
        except KeyError as e:
            logger.warning(f"Missing formatting key for template {key}: {e}")
    return template

# ==============================================================================
# 4. DATABASE INITIALISATION & MIGRATION
# ==============================================================================
def init_db() -> None:
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    c = conn.cursor()
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY, 
            phone TEXT, 
            first_name TEXT, 
            username TEXT,
            balance REAL DEFAULT 0.0, 
            account_type TEXT DEFAULT 'Regular', 
            orders_count INTEGER DEFAULT 0, 
            spent REAL DEFAULT 0.0, 
            referrals_count INTEGER DEFAULT 0, 
            referral_earned REAL DEFAULT 0.0, 
            referred_by INTEGER, 
            last_spin TEXT, 
            joined_date TEXT,
            is_reseller INTEGER DEFAULT 0,
            reseller_since TEXT,
            total_saved REAL DEFAULT 0.0,
            is_banned INTEGER DEFAULT 0,
            warnings INTEGER DEFAULT 0,
            is_vip INTEGER DEFAULT 0,
            vip_since TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS products (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            category TEXT, 
            panel_name TEXT DEFAULT '',
            name TEXT, 
            price_inr REAL, 
            reseller_price REAL DEFAULT 0.0,
            stock INTEGER, 
            apk_link TEXT, 
            validity TEXT DEFAULT 'Lifetime', 
            device_limit TEXT DEFAULT '1 Device',
            is_active INTEGER DEFAULT 1
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS product_keys (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            product_id INTEGER, 
            key_text TEXT, 
            is_used INTEGER DEFAULT 0
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            user_id INTEGER, 
            product_name TEXT, 
            price_paid REAL, 
            delivered_key TEXT, 
            purchase_date TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS ffglorypro_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            group_id TEXT NOT NULL UNIQUE,
            clan_id TEXT NOT NULL,
            region_id TEXT NOT NULL,
            region_name TEXT DEFAULT '',
            amount REAL DEFAULT 0,
            payment_method TEXT DEFAULT '',
            status TEXT DEFAULT 'running',
            created_at TEXT NOT NULL
        )
    ''')

    c.execute('''
        CREATE TABLE IF NOT EXISTS tickets (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            user_id INTEGER, 
            message TEXT, 
            status TEXT DEFAULT 'Open',
            created_at TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS settings (
            key TEXT PRIMARY KEY, 
            value TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS coupons (
            code TEXT PRIMARY KEY, 
            amount REAL, 
            uses_left INTEGER
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS redeemed (
            user_id INTEGER, 
            code TEXT
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS transactions (
            order_id TEXT PRIMARY KEY, 
            user_id INTEGER, 
            amount_inr REAL, 
            status TEXT, 
            timestamp INTEGER
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS crypto_txns (
            txid TEXT PRIMARY KEY, 
            user_id INTEGER, 
            amount_usdt REAL,
            amount_inr REAL,
            photo_id TEXT,
            status TEXT DEFAULT 'pending',
            timestamp INTEGER
        )
    ''')

    # Safe additive migration for manual Binance payment reference IDs.
    try:
        c.execute("ALTER TABLE crypto_txns ADD COLUMN user_txid TEXT DEFAULT ''")
    except Exception:
        pass

    c.execute('''
        CREATE TABLE IF NOT EXISTS heroic_orders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            slot INTEGER NOT NULL,
            product_name TEXT NOT NULL,
            price REAL NOT NULL,
            status TEXT DEFAULT 'pending',
            delivered_id TEXT DEFAULT '',
            created_at TEXT NOT NULL,
            delivered_at TEXT DEFAULT ''
        )
    ''')

    
    c.execute('''
        CREATE TABLE IF NOT EXISTS spin_rewards (
            id INTEGER PRIMARY KEY AUTOINCREMENT, 
            amount REAL
        )
    ''')
    
    c.execute('''
        CREATE TABLE IF NOT EXISTS activity_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            action TEXT,
            details TEXT,
            timestamp TEXT
        )
    ''')

    c.execute('''
        CREATE TABLE IF NOT EXISTS categories (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT UNIQUE NOT NULL,
            emoji_id TEXT DEFAULT '',
            sort_order INTEGER DEFAULT 0
        )
    ''')

    # One demo video per panel (e.g. BALA MOD), shared by every duration/package.
    c.execute('''
        CREATE TABLE IF NOT EXISTS panel_demo_videos (
            category TEXT NOT NULL DEFAULT '',
            panel_key TEXT NOT NULL,
            display_name TEXT NOT NULL DEFAULT '',
            video_file_id TEXT NOT NULL DEFAULT '',
            updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (category, panel_key)
        )
    ''')
    c.execute("SELECT COUNT(*) FROM categories")
    if c.fetchone()[0] == 0:
        for idx, cat in enumerate(FIXED_CATEGORIES, 1):
            c.execute("INSERT OR IGNORE INTO categories (name, sort_order) VALUES (?, ?)", (cat, idx))

    # ------------------------------------------------------------------
    # SELF-HEALING SCHEMA MIGRATION
    # ------------------------------------------------------------------
    # IMPORTANT: CREATE TABLE IF NOT EXISTS does NOT add columns to an
    # existing database. Older deployments had a products table without
    # `category`, which caused: `table products has no column named category`.
    # Always inspect PRAGMA table_info and add every column required by the
    # current bot. This makes old Railway/Render .db files forward-compatible.
    required_columns = {
        "users": {
            "is_vip": "INTEGER DEFAULT 0", "vip_since": "TEXT",
            "is_banned": "INTEGER DEFAULT 0", "warnings": "INTEGER DEFAULT 0",
        },
        "products": {
            "category": "TEXT DEFAULT ''",
            "panel_name": "TEXT DEFAULT ''",
            "name": "TEXT DEFAULT ''",
            "price_inr": "REAL DEFAULT 0",
            "reseller_price": "REAL DEFAULT 0",
            "stock": "INTEGER DEFAULT 0",
            "apk_link": "TEXT DEFAULT ''",
            "validity": "TEXT DEFAULT 'Lifetime'",
            "device_limit": "TEXT DEFAULT '1 Device'",
            "is_active": "INTEGER DEFAULT 1",
            "external_enabled": "INTEGER DEFAULT 0",
            "external_product_id": "TEXT DEFAULT ''",
            "requires_android_id": "INTEGER DEFAULT 0",
            "external_duration": "TEXT DEFAULT ''",
            "api_provider": "TEXT DEFAULT 'bunty'",
            "description": "TEXT DEFAULT ''",
            "video_file_id": "TEXT DEFAULT ''",
            "is_maintenance": "INTEGER DEFAULT 0",
            "sort_order": "INTEGER DEFAULT 0",
            "panel_sort_order": "INTEGER DEFAULT 0",
        },
        "tickets": {"created_at": "TEXT"},
        "transactions": {
            "purpose": "TEXT DEFAULT 'wallet_topup'",
            "product_id": "INTEGER",
            "quantity": "INTEGER DEFAULT 1",
            "description": "TEXT DEFAULT ''",
            "gateway": "TEXT DEFAULT 'zapupi'",
        },
    }

    for table, columns in required_columns.items():
        try:
            existing = {row[1] for row in c.execute(f"PRAGMA table_info({table})").fetchall()}
            for column, definition in columns.items():
                if column not in existing:
                    c.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")
                    logger.info("DB migration: added %s.%s", table, column)
        except sqlite3.Error as exc:
            logger.exception("DB migration failed for table %s: %s", table, exc)
            raise RuntimeError(f"Database migration failed for {table}: {exc}") from exc

    # Make payment transaction schema resilient on older deployed databases.
    c.execute("CREATE TABLE IF NOT EXISTS transactions (order_id TEXT PRIMARY KEY, user_id INTEGER, amount_inr REAL, status TEXT, timestamp INTEGER, purpose TEXT DEFAULT 'wallet_topup', product_id INTEGER, quantity INTEGER DEFAULT 1, description TEXT DEFAULT '', gateway TEXT DEFAULT 'zapupi')")
    _txn_cols = {row[1] for row in c.execute("PRAGMA table_info(transactions)").fetchall()}
    for _col, _definition in {
        "purpose": "TEXT DEFAULT 'wallet_topup'", "product_id": "INTEGER",
        "quantity": "INTEGER DEFAULT 1", "description": "TEXT DEFAULT ''", "gateway": "TEXT DEFAULT 'zapupi'",
    }.items():
        if _col not in _txn_cols:
            c.execute(f"ALTER TABLE transactions ADD COLUMN {_col} {_definition}")
            logger.info("DB migration: added transactions.%s", _col)

    # Normalize NULLs left by older databases.
    c.execute("UPDATE products SET category='' WHERE category IS NULL")
    c.execute("UPDATE products SET panel_name='' WHERE panel_name IS NULL")
    c.execute("UPDATE products SET name='' WHERE name IS NULL")
    c.execute("UPDATE products SET stock=0 WHERE stock IS NULL")
    c.execute("UPDATE products SET external_enabled=0 WHERE external_enabled IS NULL")
    c.execute("UPDATE products SET api_provider='bunty' WHERE external_enabled=1 AND LOWER(COALESCE(api_provider,'')) IN ('', 'keypanel', 'manual')")
    c.execute("UPDATE products SET external_duration=validity WHERE COALESCE(external_duration, '')='' AND validity IS NOT NULL")
    c.execute("UPDATE transactions SET quantity=1 WHERE quantity IS NULL OR quantity < 1")
    c.execute("UPDATE transactions SET purpose='wallet_topup' WHERE purpose IS NULL OR purpose=''" )
    conn.commit()

    # Backfill the API duration for existing products. The purchase code still
    # has additional fallbacks, so old databases remain compatible.
    try:
        c.execute("UPDATE products SET external_duration = validity WHERE COALESCE(external_duration, '') = ''")
    except sqlite3.OperationalError:
        pass
    
    c.execute("SELECT COUNT(*) FROM spin_rewards")
    if c.fetchone()[0] == 0:
        c.executemany("INSERT INTO spin_rewards (amount) VALUES (?)", [(0.0,), (1.0,), (2.0,), (5.0,), (10.0,)])

    default_settings = [
        ('spin_status', 'ON'),
        ('daily_spin_limit', '50.0'),
        ('daily_spin_pool', '5.0'),
        ('daily_spin_spent', '0.0'),
        ('daily_spin_spent_date', ''),
        ('reseller_system_status', 'ON'),
        ('bot_status', 'ON'),
        ('how_to_video', 'None'),
        ('all_files_link', 'None'),
        ('payment_proof_channel', ''),
        ('zapupi_api', ''),
        ('gateway_zapupi_status', 'ON'),
        ('gateway_famgateway_status', 'ON'),
        ('famgateway_api', ''),
        ('famgateway_url', 'https://famgateway.in'),
        ('binance_api', ''),
        ('binance_secret', ''),
        ('binance_address', ''),
        ('binance_qr_file_id', ''),
        ('binance_usdt_rate', '90'),
        ('vip_status', 'OFF'),
        ('reseller_setup_fee', '200.0'),
        ('reseller_min_balance', '500.0'),
        ('migration_done', '0'),
        ('support_telegram', 'https://t.me/rajuconfigyt'),
        ('admin_contact', '@HGMODMENU'),
        ('support_whatsapp', 'https://wa.me/YOUR_NUMBER'),
        ('ui_start_menu', UI_TEXTS['start_menu']),
        ('ui_download_files', UI_TEXTS['download_files']),
        ('ui_referral', 'Invite friends using your personal link and earn rewards on their successful purchases.'),
        ('ui_orders', 'Your previous orders and their current status are shown here.'),
        ('ui_how_to', '1. Add funds via Add Balance.\n2. Open Product Store.\n3. Choose a category and plan.\n4. Follow the payment instructions to receive your order.'),
        ('ui_reseller', 'Become a reseller to access wholesale pricing and manage your sales.'),
        ('ui_profile', 'View your account details, balance, and activity here.'),
        ('ui_history', 'View your past orders and purchase history here.'),
        ('ui_support', 'Need help? Contact our support team using the links below.'),
        ('ui_feedback', 'Share your feedback to help us improve the service.'),
        ('ui_lucky_dice_result', UI_TEXTS['lucky_dice_result']),
        ('ui_vip_menu', UI_TEXTS['vip_menu']),
        ('ui_add_balance_menu', UI_TEXTS['add_balance_menu']),
        ('external_api_url', 'https://adminpanels.shop/api/reseller_v1.php'),
        ('external_api_key', ''),
        ('whitex_api_url', 'https://whitexmodz.store/api/v1'),
        ('whitex_api_token', ''),
        ('panelstore_api_url', 'https://panelstore.shop/api/v1/index.php'),
        ('panelstore_api_key', ''),
        ('ffglorypro_api_key', ''),
        ('ffglorypro_master_key', ''),
        ('ffglorypro_enabled', 'OFF'),
        ('product_store_enabled', 'ON'),
        ('ffglorypro_emoji', '🏆'),
        ('ffglorypro_label', 'Guild Glory'),
        ('ffglorypro_notice', 'Check the selected region and clan ID carefully before confirming.'),
        ('ff_like_regions_json', '[{"code":"IND","name":"India","emoji":"🇮🇳"},{"code":"BD","name":"Bangladesh","emoji":"🇧🇩"},{"code":"NP","name":"Nepal","emoji":"🇳🇵"},{"code":"LK","name":"Sri Lanka","emoji":"🇱🇰"}]'),
        ('ffglorypro_regions_json', '[{"id":"me","name":"Middle East","emoji":"🌍","price":0,"enabled":true},{"id":"bd","name":"Bangladesh","emoji":"🇧🇩","price":0,"enabled":true}]'),
        ('ffglorypro_price_india', '0'),
        ('ffglorypro_price_bangladesh', '0'),
        ('ffglorypro_price_nepal', '0'),
        ('ffglorypro_price_srilanka', '0'),
        ('external_master_key', ''),
        ('license_manager_api_url', 'https://licencedashboard.shop/api/v1/generate.php'),
        ('license_manager_api_key', ''),
        ('license_manager_health_url', ''),
        ('license_manager_balance_url', ''),
        ('license_manager_default_product_id', '62'),
        ('hk_tamim_api_url', 'https://hkmodz.shop/api/v1/generate_key.php'),
        ('hk_tamim_api_token', ''),
        ('hk_tamim_health_url', ''),
        ('hk_tamim_balance_url', ''),
        ('hk_tamim_default_variant_id', '50'),
        ('dripclient_api_url', 'https://dripclientofficial.shop/api/v1'),
        ('dripclient_api_token', ''),
        ('adminshops_api_url', 'https://adminshops.com/api/v1'),
        ('adminshops_api_token', ''),
        ('adminshops_default_product_id', '14'),
        ('payment_guru_channel_link', ''),
        ('payment_guru_channel_enabled', 'OFF'),
        ('main_channel_link', ''),
        ('main_channel_enabled', 'ON'),
        ('payment_proof_channel_enabled', 'ON'),
        ('referral_commission_percent', '15'),
        ('store_description', '🎉 Hello! Welcome to our store.\n\n🎯 Instant Delivery 24/7\n💰 Secure Payment\n🏆 Best Prices Guaranteed\n🛟 Professional Support'),
        ('ui_button_color', 'off'),
        ('demo_video_emoji', '🎬'),
        ('demo_video_color', 'green'),
        ('ui_back_cancel_color', 'red'),
        ('ui_back_cancel_emoji', '🔴'),
        ('ui_category_color', 'off'),
        ('ui_plan_color', 'off'),
        ('ui_button_size', 'small'),
        ('bunty_balance_alert_threshold', '0'),
        ('bunty_balance_last_alert', '0'),
        ('heroic_slot_1_name', 'One ID'), ('heroic_slot_1_price', '0'),
        ('heroic_slot_2_name', 'Two ID'), ('heroic_slot_2_price', '0'),
        ('heroic_slot_3_name', 'Three ID'), ('heroic_slot_3_price', '0'),
        ('heroic_slot_4_name', 'Four ID'), ('heroic_slot_4_price', '0'),
        ('heroic_slot_1_emoji', '🆔'), ('heroic_slot_2_emoji', '🆔'),
        ('heroic_slot_3_emoji', '🆔'), ('heroic_slot_4_emoji', '🆔'),
    ]
    for slot, emoji_id in DEFAULT_EMOJIS.items():
        default_settings.append((f"emoji_{slot}", emoji_id))
    
    for key, val in default_settings:
        c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)", (key, val))
    c.execute("DELETE FROM settings WHERE key IN ('panel_store_api_url','panel_store_api_key')")
    # Normalize every legacy external provider to the supported Bunty provider.
    c.execute("UPDATE products SET api_provider='bunty' WHERE external_enabled=1 AND LOWER(COALESCE(api_provider,'')) IN ('', 'keypanel', 'manual')")

    c.execute("""CREATE TABLE IF NOT EXISTS ff_products (
        id INTEGER PRIMARY KEY AUTOINCREMENT, title TEXT NOT NULL, description TEXT DEFAULT '',
        price REAL NOT NULL DEFAULT 0, active INTEGER NOT NULL DEFAULT 1, created_at TEXT,
        product_type TEXT NOT NULL DEFAULT 'manual', duration_days INTEGER DEFAULT 0, notice TEXT DEFAULT '')""")
    c.execute("""CREATE TABLE IF NOT EXISTS ff_orders (
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER NOT NULL, product_id INTEGER NOT NULL,
        product_title TEXT NOT NULL, price REAL NOT NULL, game_uid TEXT NOT NULL, game_photo_id TEXT NOT NULL,
        region TEXT NOT NULL, payment_method TEXT NOT NULL, proof_file_id TEXT DEFAULT '',
        status TEXT NOT NULL DEFAULT 'pending', created_at TEXT, updated_at TEXT,
        provider_order_id TEXT DEFAULT '', provider_status TEXT DEFAULT '', provider_response TEXT DEFAULT '')""")
    # Safe additive migrations for existing databases.
    for table, column, definition in [
        ("ff_products", "product_type", "TEXT NOT NULL DEFAULT 'manual'"),
        ("ff_products", "duration_days", "INTEGER DEFAULT 0"),
        ("ff_products", "notice", "TEXT DEFAULT ''"),
        ("ff_orders", "provider_order_id", "TEXT DEFAULT ''"),
        ("ff_orders", "provider_status", "TEXT DEFAULT ''"),
        ("ff_orders", "provider_response", "TEXT DEFAULT ''"),
    ]:
        cols = [r[1] for r in c.execute(f"PRAGMA table_info({table})").fetchall()]
        if column not in cols:
            c.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")
    c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES ('ffglory_api_token', '')")
    c.execute("UPDATE settings SET value='' WHERE key='ffglory_api_token'")
    c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES ('ff_like_label', 'FF Like')")
    c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES ('ff_like_emoji', '🔥')")
    c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES ('ff_like_enabled', 'OFF')")
    c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES ('fflike_upi_details', 'Admin se UPI details lein')")
    conn.commit()
    conn.close()

def migrate_categories() -> None:
    done = get_setting("migration_done", "0")
    
    # ALWAYS force update emojis and UI texts regardless of migration status
    logger.info("Forcing emoji and UI text updates...")
    
    # Update all emoji settings
    for slot, emoji_id in DEFAULT_EMOJIS.items():
        set_setting(f"emoji_{slot}", emoji_id)
    
    # Force update UI texts
    set_setting("ui_start_menu", UI_TEXTS['start_menu'])
    set_setting("ui_add_balance_menu", UI_TEXTS['add_balance_menu'])
    set_setting("ui_download_files", UI_TEXTS['download_files'])
    set_setting("ui_lucky_dice_result", UI_TEXTS['lucky_dice_result'])
    set_setting("ui_vip_menu", UI_TEXTS['vip_menu'])
    logger.info("UI texts and emojis updated with new placeholders and IDs.")
    
    set_setting("migration_done", "1")
    logger.info("Category migration complete.")

# ==============================================================================
# 5. MIDDLEWARES & SECURITY
# ==============================================================================
async def hacker_loading(message: Message, text: str = "Decrypting Data") -> Message:
    msg = await message.answer(f"⚡ {text}\n[□□□] 0%")
    await asyncio.sleep(0.3)
    await msg.edit_text(f"⚡ {text}\n[■□□] 33%", parse_mode='HTML')
    await asyncio.sleep(0.3)
    await msg.edit_text(f"⚡ {text}\n[■■□] 66%", parse_mode='HTML')
    await asyncio.sleep(0.3)
    await msg.edit_text(f"⚡ {text}\n[■■■] 100%", parse_mode='HTML')
    return msg

async def safe_edit_text(message, text, **kwargs):
    """Edit a Telegram message without crashing when the content is unchanged."""
    try:
        return await message.edit_text(text, **kwargs)
    except TelegramBadRequest as exc:
        err = str(exc).lower()
        if "message is not modified" in err:
            return message
        # If the old message cannot be edited (e.g. inaccessible/deleted), send a fresh one.
        if "message to edit not found" in err or "message can't be edited" in err or "message_id_invalid" in err:
            try:
                return await message.answer(text, **kwargs)
            except Exception:
                logger.exception("Could not send replacement for uneditable message")
                return None
        raise

async def _safe_callback_answer(event, text, show_alert=True):
    """Safely answer Telegram callback queries.

    Telegram can reject stale/expired callback queries with:
    "query is too old and response timeout expired or query ID is invalid".
    Such a stale query must never crash middleware or affect the bot/payment flow.
    """
    try:
        await event.answer(text, show_alert=show_alert)
    except TelegramBadRequest as exc:
        msg = str(exc).lower()
        if "query is too old" in msg or "query id is invalid" in msg or "response timeout expired" in msg:
            return False
        raise
    except Exception as exc:
        # A stale/expired callback is non-critical; do not let it break middleware.
        logger.warning("Callback answer skipped: %s", exc)
        return False
    return True

class GlobalSecurityMiddleware(BaseMiddleware):
    def __init__(self):
        super().__init__()
        self.last_action_times = {}

    async def __call__(self, handler, event, data):
        user_id = event.from_user.id
        now = time.time()
        if user_id in self.last_action_times:
            if now - self.last_action_times[user_id] < 0.3:
                return
        self.last_action_times[user_id] = now

        if not is_admin(user_id):
            user_info = db_query("SELECT is_banned FROM users WHERE user_id=?", (user_id,), fetchone=True)
            if user_info and user_info[0] == 1:
                msg = "🚫 <b>ACCESS DENIED</b>\nYou have been banned from using this bot.\nContact support if you think this is a mistake."
                if isinstance(event, Message): await event.answer(msg)
                elif isinstance(event, CallbackQuery): await _safe_callback_answer(event, msg, show_alert=True)
                return
                
            status_check = db_query("SELECT value FROM settings WHERE key='bot_status'", fetchone=True)
            status = status_check[0] if status_check else 'ON'
            if status == 'OFF':
                msg = "⚠️ <b>Store Maintenance</b>\n\nThe store is currently offline for updates. Please check back later!"
                if isinstance(event, Message): await event.answer(msg)
                elif isinstance(event, CallbackQuery): await _safe_callback_answer(event, "⚠️ Bot is currently OFF for Maintenance.", show_alert=True)
                return
                
        return await handler(event, data)

dp.message.middleware(GlobalSecurityMiddleware())
dp.callback_query.middleware(GlobalSecurityMiddleware())


# ==============================================================================
# ==============================================================================
# ADMIN-CONTROLLED INLINE BUTTON UI
# Telegram does not expose a pixel-size setting for inline buttons. The size
# control therefore changes row density: Small=2, Medium=2, Large=1 button/row.
# Colors are admin-controlled: OFF, BLUE, GREEN, RED. Premium custom emoji IDs
# are independent and are always preserved.
# ==============================================================================
UI_BUTTON_COLORS = {
    "off": None,
    "blue": "primary",
    "green": "success",
    "red": "danger",
}
UI_BUTTON_SIZES = {"small": 2, "medium": 2, "large": 1}

def get_ui_button_color():
    value = (get_setting("ui_button_color", "off") or "off").strip().lower()
    return value if value in UI_BUTTON_COLORS else "off"

def get_ui_button_size() -> str:
    value = (get_setting("ui_button_size", "small") or "small").lower()
    return value if value in UI_BUTTON_SIZES else "small"

def _is_back_cancel_button(button):
    cb = str(getattr(button, "callback_data", "") or "").lower()
    label = str(getattr(button, "text", "") or "").lower()
    return ("back" in cb or "cancel" in cb or "back" in label or "cancel" in label
            or "⬅" in label or "🔙" in label or "❌" in label)

def _apply_back_cancel_preferences(button):
    if not _is_back_cancel_button(button):
        return False
    color = (get_setting("ui_back_cancel_color", "red") or "red").strip().lower()
    if color not in UI_BUTTON_COLORS:
        color = "red"
    _apply_ui_button_style(button, color)
    raw_emoji = (get_setting("ui_back_cancel_emoji", "🔴") or "🔴").strip()
    emoji = "" if raw_emoji.lower() in ("off", "none", "disabled") else raw_emoji[:16]
    label = str(getattr(button, "text", "") or "Back")
    # Avoid repeatedly prefixing the configured emoji when keyboards are rebuilt.
    if emoji and not label.startswith(emoji):
        label = f"{emoji} {label}"
    try:
        button.text = label[:64]
    except Exception:
        pass
    return True

def _apply_ui_button_style(button, color):
    # The database stores the human-friendly color name (off/blue/green/red),
    # while Telegram Bot API expects style values primary/success/danger.
    # Keep these two namespaces separate so a value like "green" never gets
    # sent to Telegram as an invalid button style.
    style_map = {
        "blue": "primary",
        "green": "success",
        "red": "danger",
    }
    style = style_map.get(str(color).strip().lower()) if color is not None else None
    try:
        button.style = style
    except Exception:
        # Do not let a UI preference prevent a keyboard from being built.
        try:
            if style is None:
                button.style = None
        except Exception:
            pass

class _UIKeyboardRows(list):
    """List wrapper so buttons appended later also receive admin UI settings."""
    def __init__(self, rows, color, width):
        super().__init__(rows)
        self.color = color
        self.width = width
        for row in self:
            self._style_row(row)

    def _style_row(self, row):
        for button in row:
            cb = getattr(button, "callback_data", None)
            if _apply_back_cancel_preferences(button):
                continue
            override = get_setting(f"ui_color_{cb}", "") if cb else ""
            _apply_ui_button_style(button, override if override in UI_BUTTON_COLORS and override != "" else self.color)

    def append(self, row):
        row = list(row)
        self._style_row(row)
        if len(row) > self.width:
            for i in range(0, len(row), self.width):
                super().append(row[i:i+self.width])
            return
        super().append(row)

def make_inline_kb(inline_keyboard=None, **kwargs):
    """Central UI renderer used by all inline keyboards in this bot.

    _width is an internal layout override used by screens that intentionally
    need one full-width button per row (for example Product Panel selection).
    """
    rows = inline_keyboard or []
    width_override = kwargs.pop("_width", None)
    color = get_ui_button_color()
    width = int(width_override) if width_override in (1, 2, 3) else UI_BUTTON_SIZES[get_ui_button_size()]
    out = []
    for row in rows:
        row = list(row)
        if not row:
            continue
        for button in row:
            try:
                icon_id = getattr(button, "icon_custom_emoji_id", None)
                if icon_id is not None and not str(icon_id).strip().isdigit():
                    button.icon_custom_emoji_id = None
            except Exception:
                pass
            cb = getattr(button, "callback_data", None) or ""
            if _apply_back_cancel_preferences(button):
                continue
            override = get_setting(f"ui_color_{cb}", "") if cb else ""
            if override not in UI_BUTTON_COLORS or not override:
                # Separate owner-controlled styles for category and product/plan buttons.
                if cb.startswith(("category_", "shop_cat_")):
                    scoped = (get_setting("ui_category_color", "off") or "off").lower()
                    override = color if scoped == "off" or scoped not in UI_BUTTON_COLORS else scoped
                elif cb.startswith(("buy_", "buyqty_", "walletbuy_", "upibuy_", "famupibuy_")):
                    scoped = (get_setting("ui_plan_color", "off") or "off").lower()
                    override = color if scoped == "off" or scoped not in UI_BUTTON_COLORS else scoped
                else:
                    override = color
            _apply_ui_button_style(button, override)
        if len(row) <= width:
            out.append(row)
        else:
            for i in range(0, len(row), width):
                out.append(row[i:i+width])
    kb = InlineKeyboardMarkup(inline_keyboard=out, **kwargs)
    try:
        object.__setattr__(kb, "inline_keyboard", _UIKeyboardRows(out, color, width))
    except Exception:
        pass
    return kb

# ==============================================================================
# 6. FSM STATES
# ==============================================================================
class UserStates(StatesGroup):
    wait_for_ticket = State()
    wait_for_redeem = State()
    wait_for_crypto_txid = State()
    wait_for_crypto_amount = State()   # User enters USDT amount
    wait_for_crypto_ss = State()       # User sends payment screenshot
    custom_amount_input = State()
    ff_uid = State()
    ff_game_photo = State()
    ff_region = State()
    ffglorypro_clan_id = State()
    wait_for_glory_coupon_create = State()
    wait_for_glory_coupon_redeem = State()
    wait_for_glory_coupon_cancel = State()
    ff_payment = State()
    ff_upi_proof = State()

class AdminStates(StatesGroup):
    add_prod_category = State()
    add_prod_panel_name = State()
    add_prod_name = State()
    add_prod_validity = State()
    add_prod_device_limit = State()
    add_prod_price = State()
    add_prod_reseller_price = State()
    add_prod_apk = State()
    add_prod_keys = State()
    
    edit_prod_field = State()
    wait_for_new_value = State()
    wait_for_add_keys = State()
    wait_for_delete_key = State()
    
    broadcast_msg = State()
    add_coupon_code = State()
    add_coupon_amount = State()
    add_coupon_uses = State()
    
    wait_for_zapupi_api = State()
    wait_for_whitex_token = State()
    wait_for_panelstore_key = State()
    wait_for_glorypro_credentials = State()
    wait_for_glorypro_price = State()
    wait_for_glorypro_notice = State()
    wait_ff_like_success_txt = State()
    wait_for_ff_region_config = State()
    wait_for_glory_region_config = State()
    wait_for_glorypro_label = State()
    wait_for_binance_api = State()
    wait_for_binance_secret = State()
    wait_for_binance_address = State()
    wait_for_binance_qr = State()
    wait_for_binance_rate = State()
    
    ticket_reply_msg = State()
    reseller_manage_id = State()
    manage_target_user = State()
    wait_for_add_money = State()
    wait_for_minus_money = State()
    wait_for_warning = State()
    
    spin_add_reward = State()
    spin_set_limit = State()
    wait_for_howto_video = State()
    wait_for_all_files_link = State()
    wait_for_payment_proof_channel = State()
    
    edit_ui_text = State()
    edit_reseller_price = State()
    wait_for_reseller_setup_fee = State()
    wait_for_reseller_min_balance = State()
    confirm_ban = State()
    
    wait_for_support_telegram = State()
    wait_for_support_whatsapp = State()
    wait_for_category_emoji = State()
    wait_for_panel_emoji_id = State()
    wait_for_emoji_slot = State()
    wait_for_ext_url = State()
    wait_for_ext_key = State()
    wait_for_ext_master = State()
    add_prod_external = State()
    add_prod_external_product_id = State()
    add_prod_external_duration = State()
    photo_add_product = State()
    photo_add_product_confirm = State()
    photo_add_product_pid = State()
    wait_for_ui_color = State()
    wait_for_ui_size = State()
    wait_for_back_cancel_emoji = State()
    
    # Category Management States
    add_category_name = State()
    edit_category_name = State()
    edit_category_pos = State()
    edit_category_emoji = State()
    
    # Panel (Main Title) Position & Title States
    edit_panel_pos = State()
    edit_panel_title = State()
    edit_prod_pos = State()
    wait_for_duration_emoji = State()
    wait_for_search_product = State()
    quick_stock_qty = State()  # For quick stock add from main admin panel
    quick_add_product = State()
    bulk_update_link = State()
    wait_for_product_description = State()
    wait_for_product_video = State()
    wait_for_license_api_key = State()
    wait_for_license_product_id = State()
    wait_for_hk_tamim_token = State()
    wait_for_hk_tamim_variant = State()
    wait_for_license_api_url = State()
    wait_for_license_health_url = State()
    wait_for_license_balance_url = State()
    wait_for_hk_tamim_api_url = State()
    wait_for_hk_tamim_health_url = State()
    wait_for_hk_tamim_balance_url = State()
    wait_for_dripclient_token = State()
    wait_for_dripclient_url = State()
    wait_for_adminshops_url = State()
    wait_for_adminshops_token = State()
    wait_for_adminshops_product_id = State()
    wait_for_payment_guru_link = State()
    wait_for_main_channel = State()
    wait_for_dynamic_admin = State()
    wait_for_welcome_text = State()
    wait_for_referral_percent = State()
    wait_for_db_upload = State()
    add_prod_video = State()  # legacy state retained for compatibility
    wait_for_demo_video = State()
    wait_for_demo_emoji = State()
    ff_add_title = State()
    ff_add_description = State()
    ff_add_notice = State()
    ff_add_price = State()
    ff_edit_upi_details = State()
    ff_add_type = State()
    ff_set_api_token = State()
    ff_edit_label = State()

# ==============================================================================
# 7. KEYBOARDS & EMOJI RESOLVERS
# ==============================================================================
DEFAULT_DURATION_EMOJIS = {
    "1 hour": "⏱️", "2 hour": "⏱️", "3 hour": "⏱️", "4 hour": "⏱️",
    "6 hour": "⏳", "8 hour": "⏳", "12 hour": "⏳", "24 hour": "⚡",
    "1 day": "⚡", "2 day": "⚡", "3 day": "🌟", "4 day": "🌟",
    "5 day": "🌟", "7 day": "🔥", "10 day": "🔥", "14 day": "💎",
    "15 day": "💎", "20 day": "👑", "21 day": "👑", "28 day": "👑",
    "30 day": "👑", "45 day": "🏆", "60 day": "🏆", "90 day": "🏆",
}

def extract_emoji_or_id(m: Message) -> tuple:
    """Extracts (emoji_char, custom_emoji_id) from message."""
    raw_text = (m.text or "").strip()
    custom_id = ""
    emoji_char = ""
    if m.entities:
        for ent in m.entities:
            if ent.type == "custom_emoji" and ent.custom_emoji_id:
                custom_id = str(ent.custom_emoji_id)
                emoji_char = raw_text[ent.offset : ent.offset + ent.length]
                break
    if not custom_id and raw_text.isdigit():
        custom_id = raw_text
    elif not emoji_char:
        emoji_char = raw_text
    return emoji_char, custom_id

def get_duration_emoji(package_name: str) -> str:
    cleaned = str(package_name or "").strip()
    stored = get_setting(f"dur_emoji_{cleaned.lower()}", "")
    if stored:
        return stored
    lower = cleaned.lower()
    for key, emo in DEFAULT_DURATION_EMOJIS.items():
        if key in lower:
            return emo
    if "hour" in lower or "hr" in lower:
        return "⏱️"
    if "day" in lower or "d" in lower:
        return "⚡"
    if "vip" in lower or "month" in lower:
        return "👑"
    return "⚡"

def get_category_emoji(category: str) -> str | None:
    cid = get_setting(f"cat_custom_id_{category}", "")
    if cid and cid.isdigit():
        return cid
    stored = get_setting(f"cat_emoji_{category}", "")
    if stored and stored.isdigit():
        return stored
    try:
        cat_row = db_query("SELECT emoji_id FROM categories WHERE name=?", (category,), fetchone=True)
        if cat_row and cat_row[0] and str(cat_row[0]).isdigit():
            return str(cat_row[0])
    except Exception:
        pass
    slot_map = {
        "ANDROID NON ROOT PANEL": "category_android_non_root",
        "ANDROID ROOT PANEL": "category_android_root",
        "IPHONE PANEL": "category_iphone",
        "PC PANEL": "category_pc",
    }
    slot = slot_map.get(category)
    if slot:
        return get_emoji_icon(slot, DEFAULT_EMOJIS.get(slot, ""))
    return get_emoji_icon("product_store", "")

def get_category_display_icon(category: str) -> str:
    """Returns a unicode emoji or default icon for category button label."""
    stored = get_setting(f"cat_emoji_{category}", "")
    if stored and not stored.isdigit():
        return stored
    cat_upper = category.upper()
    if "NON ROOT" in cat_upper: return ""
    if "ROOT" in cat_upper: return ""
    if "IPHONE" in cat_upper or "IOS" in cat_upper: return ""
    if "PC" in cat_upper: return ""
    if "CARROM" in cat_upper: return ""
    if "BGMI" in cat_upper or "PUBG" in cat_upper: return ""
    if "GUILD" in cat_upper or "BOT" in cat_upper: return ""
    return ""

def get_panel_display_icon(panel_name: str) -> str:
    """Returns a unicode emoji for panel button label."""
    stored = get_setting(f"panel_emoji_{panel_name}", "")
    if stored and not stored.isdigit():
        return stored
    return ""

def get_panel_emoji(panel_name: str) -> str | None:
    cid = get_setting(f"panel_custom_id_{panel_name}", "")
    if cid and cid.isdigit():
        return cid
    stored = get_setting(f"panel_emoji_{panel_name}", "")
    if stored and stored.isdigit():
        return stored
    return get_emoji_icon("product_store")

def contact_kb() -> ReplyKeyboardMarkup:
    if (get_setting("share_contact_enabled", "ON") or "ON").upper() != "ON":
        return ReplyKeyboardMarkup(keyboard=[[KeyboardButton(text="⬅️ Back to Menu")]], resize_keyboard=True, one_time_keyboard=True)
    return ReplyKeyboardMarkup(keyboard=[[KeyboardButton(text="📱 Verify Contact", request_contact=True)]], resize_keyboard=True, one_time_keyboard=True)

def main_menu_kb(user_id: Optional[int] = None) -> InlineKeyboardMarkup:
    status_check = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    sys_status = status_check[0] if status_check else 'ON'
    
    is_reseller = False
    if user_id:
        user_check = db_query("SELECT is_reseller FROM users WHERE user_id=?", (user_id,), fetchone=True)
        if user_check:
            is_reseller = bool(user_check[0])

    kb = make_inline_kb(inline_keyboard=[])
    
    if (get_setting("product_store_enabled", "ON") or "ON").upper() == "ON":
        kb.inline_keyboard.append([
            InlineKeyboardButton(
                text="Shop / Store Product", callback_data="menu_shop",
                icon_custom_emoji_id=get_emoji_icon("product_store")
            )
        ])
    if (get_setting("ff_like_enabled", "OFF") or "OFF").upper() == "ON":
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{get_setting('ff_like_emoji', '🔥')} {get_setting('ff_like_label', 'FF Like')}", callback_data="ff_menu")])
    if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() == "ON":
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{get_setting('ffglorypro_emoji', '🏆')} {get_setting('ffglorypro_label', 'Guild Glory')}", callback_data="ffglorypro_menu")])
    kb.inline_keyboard.append([
        InlineKeyboardButton(
            text="My Profile", callback_data="menu_profile",
            icon_custom_emoji_id=get_emoji_icon("profile")
        ),
        InlineKeyboardButton(
            text="Add Balance", callback_data="menu_add_balance",
            icon_custom_emoji_id=get_emoji_icon("add_balance")
        )
    ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(
            text="All History", callback_data="menu_orders",
            icon_custom_emoji_id=get_emoji_icon("history")
        ),
        InlineKeyboardButton(
            text="Referral", callback_data="menu_referral",
            icon_custom_emoji_id=get_emoji_icon("referral")
        )
    ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(
            text="How To Use", callback_data="menu_how_to",
            icon_custom_emoji_id=get_emoji_icon("tutorial")
        ),
        InlineKeyboardButton(
            text="Support", callback_data="menu_support",
            icon_custom_emoji_id=get_emoji_icon("support")
        )
    ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(
            text="Ludo Spin", callback_data="menu_spin_landing",
            icon_custom_emoji_id=get_emoji_icon("ludo_spin")
        ),
        InlineKeyboardButton(
            text="Download File", callback_data="menu_all_files",
            icon_custom_emoji_id=get_emoji_icon("download")
        )
    ])
    # Keep reseller controls in the menu, but never show the VIP Club button.
    if str(sys_status).upper() == 'ON':
        kb.inline_keyboard.append([
            InlineKeyboardButton(
                text="Reseller Panel", callback_data="menu_reseller_dash",
                icon_custom_emoji_id=get_emoji_icon("reseller")
            )
        ])

    # Main Channel and Payment Proof Channel are separate, independently controlled menu links.
    channel_link = (get_setting("main_channel_link", "") or "").strip()
    main_channel_enabled = (get_setting("main_channel_enabled", "ON") or "ON").upper() == "ON"
    if main_channel_enabled and channel_link and channel_link.lower() not in ("none", "off", "disabled", "-"):
        if channel_link.startswith("@"):
            channel_link = "https://t.me/" + channel_link[1:]
        elif not channel_link.startswith(("http://", "https://")):
            channel_link = "https://t.me/" + channel_link.lstrip("@")
        kb.inline_keyboard.append([InlineKeyboardButton(text="📢 Main Channel", url=channel_link, icon_custom_emoji_id=get_emoji_icon("telegram"))])

    proof_link = (get_setting("payment_proof_channel", "") or "").strip()
    proof_enabled = (get_setting("payment_proof_channel_enabled", "ON") or "ON").upper() == "ON"
    if proof_enabled and proof_link and proof_link.lower() not in ("none", "off", "disabled", "-"):
        if proof_link.startswith("@"):
            proof_link = "https://t.me/" + proof_link[1:]
        elif not proof_link.startswith(("http://", "https://")):
            proof_link = "https://t.me/" + proof_link.lstrip("@")
        # Telegram public links only; numeric private chat IDs are not menu URLs.
        if "t.me/" in proof_link and "+" not in proof_link:
            kb.inline_keyboard.append([InlineKeyboardButton(text="🧾 Payment Proof Channel", url=proof_link, icon_custom_emoji_id=get_emoji_icon("check_icon"))])

    # Match the supplied screenshot: red full-width shop button, then green
    # and blue two-column buttons. Telegram does not expose pixel-size controls.
    if (get_setting("top_users_enabled", "ON") or "ON").upper() == "ON":
        kb.inline_keyboard.append([
            InlineKeyboardButton(text="Top Users", callback_data="menu_top_buyers",
                                 icon_custom_emoji_id=get_emoji_icon("global_stats"))
        ])
    menu_button_styles = {
        "menu_shop": "red", "menu_add_balance": "green", "menu_profile": "blue",
        "menu_how_to": "blue", "menu_spin_landing": "green", "menu_referral": "blue",
        "menu_support": "blue", "menu_all_files": "blue", "menu_feedback": "green",
        "menu_reseller_dash": "green", "menu_top_buyers": "blue",
    }
    if get_ui_button_color() != "off":
        for row in kb.inline_keyboard:
            for button in row:
                chosen = menu_button_styles.get(getattr(button, "callback_data", None))
                if getattr(button, "url", None) and "Main Channel" in (getattr(button, "text", "") or ""):
                    chosen = get_ui_button_color()
                if chosen:
                    override = get_setting(f"ui_color_{getattr(button, 'callback_data', '')}", "")
                    _apply_ui_button_style(button, override if override in UI_BUTTON_COLORS and override != "" else get_ui_button_color())
    return kb

def back_kb(callback: str = "back_main") -> InlineKeyboardMarkup:
    return make_inline_kb(inline_keyboard=[[
        InlineKeyboardButton(text="BACK", callback_data=callback, icon_custom_emoji_id=get_emoji_icon("back"))
    ]])

def admin_kb() -> InlineKeyboardMarkup:
    status = db_query("SELECT value FROM settings WHERE key='bot_status'", fetchone=True)
    status_val = status[0] if status else 'ON'
    vip_status = db_query("SELECT value FROM settings WHERE key='vip_status'", fetchone=True)
    vip_val = vip_status[0] if vip_status else 'OFF'
    
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Bot Statistics", callback_data="admin_view_stats", icon_custom_emoji_id=get_emoji_icon("global_stats")) , InlineKeyboardButton(text="User Control Panel", callback_data="admin_user_control_start", icon_custom_emoji_id=get_emoji_icon("profile")) , InlineKeyboardButton(text="Add Product", callback_data="admin_add_prod", icon_custom_emoji_id=get_emoji_icon("product_store"))],
        [InlineKeyboardButton(text="📷 Photo Add Product", callback_data="admin_photo_add_product", icon_custom_emoji_id=get_emoji_icon("product_store")) , InlineKeyboardButton(text="⚡ Quick Add", callback_data="admin_quick_add_product", icon_custom_emoji_id=get_emoji_icon("product_store")) , InlineKeyboardButton(text="Manage Products", callback_data="admin_manage_prods", icon_custom_emoji_id=get_emoji_icon("product_store"))],
        [InlineKeyboardButton(text="Add Stock", callback_data="admin_quick_stock", icon_custom_emoji_id=get_emoji_icon("add_balance")) , InlineKeyboardButton(text="Quick Add Key", callback_data="admin_quick_add_key", icon_custom_emoji_id=get_emoji_icon("add_balance")) , InlineKeyboardButton(text="Product Maintenance", callback_data="admin_prod_maint", icon_custom_emoji_id=get_emoji_icon("shield_icon"))],
        [InlineKeyboardButton(text="🎬 Manage Demo Videos", callback_data="admin_demo_videos")],
        [InlineKeyboardButton(text="Spin Settings", callback_data="admin_spin_menu", icon_custom_emoji_id=get_emoji_icon("ludo_spin")) , InlineKeyboardButton(text="Create Coupon", callback_data="admin_create_coupon", icon_custom_emoji_id=get_emoji_icon("redeem_icon")) , InlineKeyboardButton(text="Broadcast", callback_data="admin_broadcast_btn", icon_custom_emoji_id=get_emoji_icon("telegram"))],

        [InlineKeyboardButton(text="View Tickets", callback_data="admin_view_tickets", icon_custom_emoji_id=get_emoji_icon("support")) , InlineKeyboardButton(text="Tutorial Video", callback_data="admin_set_video", icon_custom_emoji_id=get_emoji_icon("tutorial")) , InlineKeyboardButton(text="All Files Link", callback_data="admin_set_all_files", icon_custom_emoji_id=get_emoji_icon("download"))],
        [InlineKeyboardButton(text="Payment Proof Channel", callback_data="admin_set_payment_proof", icon_custom_emoji_id=get_emoji_icon("check_icon")) , InlineKeyboardButton(text="Edit All Emojis", callback_data="admin_edit_emojis", icon_custom_emoji_id=get_emoji_icon("info_icon")) , InlineKeyboardButton(text="ZapUPI Setup", callback_data="admin_setup_zapupi", icon_custom_emoji_id=get_emoji_icon("upi"))],
        [InlineKeyboardButton(text="⚡ Bunty API", callback_data="admin_setup_external_api"), InlineKeyboardButton(text="🔑 License Manager", callback_data="admin_license_manager"), InlineKeyboardButton(text="🗝️ HK Tamim", callback_data="admin_hk_tamim")],
        [InlineKeyboardButton(text="💧 Drip Client", callback_data="admin_dripclient"), InlineKeyboardButton(text="🛍️ Admin Shops", callback_data="admin_adminshops"), InlineKeyboardButton(text="🛒 PanelStore", callback_data="admin_panelstore_setup")],
        [InlineKeyboardButton(text="⚪ WhiteX Mode API", callback_data="admin_setup_whitex"), InlineKeyboardButton(text="🔧 API Control / Bulk Update", callback_data="admin_api_control"), InlineKeyboardButton(text="🧪 Full API Check", callback_data="admin_full_system_check")],
        [InlineKeyboardButton(text="🎨 UI Controls", callback_data="admin_ui_controls"), InlineKeyboardButton(text="📢 Main Channel Link", callback_data="admin_set_main_channel", icon_custom_emoji_id=get_emoji_icon("telegram"))],
        [InlineKeyboardButton(text="🗄️ Database Backup / Restore", callback_data="admin_db_tools"), InlineKeyboardButton(text="🎁 Referral Commission %", callback_data="admin_referral_percent")],
        [InlineKeyboardButton(text="🔥 FF Like System", callback_data="admin_ff_menu"), InlineKeyboardButton(text="🏆 FF Glory Pro", callback_data="admin_ffglorypro_menu")],
        [InlineKeyboardButton(text=f"🛒 Product Store: {'🟢 ON' if (get_setting('product_store_enabled', 'ON') or 'ON').upper() == 'ON' else '🔴 OFF'}", callback_data="admin_toggle_product_store")],
        [InlineKeyboardButton(text="🔀 Channel ON/OFF", callback_data="admin_channel_toggles"), InlineKeyboardButton(text="🎨 Per-Button Colors", callback_data="admin_per_button_colors")],
        [InlineKeyboardButton(text="📜 View Logs", callback_data="admin_logs_view"), InlineKeyboardButton(text="🚨 Error Logs", callback_data="admin_logs_errors")],
        [InlineKeyboardButton(text="🌐 Hosting Server IP", callback_data="admin_hosting_server_ip")],
        [InlineKeyboardButton(text="🖥️ Web Admin Dashboard URL", callback_data="admin_dashboard_url")],
        [InlineKeyboardButton(text="👥 Manage Admins", callback_data="owner_manage_admins")],
        [InlineKeyboardButton(text="📝 Welcome Text", callback_data="owner_edit_welcome")],
        [InlineKeyboardButton(text="🏆 Top Users ON/OFF", callback_data="owner_toggle_top_users"), InlineKeyboardButton(text="📱 Share Contact ON/OFF", callback_data="owner_toggle_share_contact")],
        [InlineKeyboardButton(text="💜 FamGateway", callback_data="admin_setup_famgateway")],
        [InlineKeyboardButton(text="💳 Gateway Control", callback_data="admin_gateway_control", icon_custom_emoji_id=get_emoji_icon("upi")) , InlineKeyboardButton(text="💸 Bulk Price Adjust", callback_data="admin_bulk_price_menu", icon_custom_emoji_id=get_emoji_icon("money_icon")) , InlineKeyboardButton(text="🧹 Zero All User Balances", callback_data="admin_zero_all_balances", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text="🏆 Reset Top Sellers", callback_data="admin_reset_top_sellers", icon_custom_emoji_id=get_emoji_icon("global_stats")) , InlineKeyboardButton(text="Edit UI Texts", callback_data="admin_edit_ui_menu", icon_custom_emoji_id=get_emoji_icon("info_icon")) , InlineKeyboardButton(text="Edit Reseller Price", callback_data="admin_edit_reseller_price", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text="👥 Reseller Management", callback_data="admin_reseller_menu", icon_custom_emoji_id=get_emoji_icon("reseller")), InlineKeyboardButton(text="Reseller Fee", callback_data="admin_set_reseller_fee", icon_custom_emoji_id=get_emoji_icon("money_icon")), InlineKeyboardButton(text="Min Balance", callback_data="admin_set_reseller_min", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text="Manage Categories", callback_data="admin_manage_categories", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Product Titles & Positions", callback_data="admin_panel_positions_menu", icon_custom_emoji_id=get_emoji_icon("grid_id")) , InlineKeyboardButton(text="Set Support Links", callback_data="admin_set_support_links", icon_custom_emoji_id=get_emoji_icon("support")) , InlineKeyboardButton(text="Set Category Emojis", callback_data="admin_set_category_emojis", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Set Panel Emojis", callback_data="admin_set_panel_emojis", icon_custom_emoji_id=get_emoji_icon("info_icon")) , InlineKeyboardButton(text="Set Duration Emojis", callback_data="admin_set_duration_emojis", icon_custom_emoji_id=get_emoji_icon("info_icon")) , InlineKeyboardButton(
                text=f"Bot Status: {status_val} {'🟢' if status_val == 'ON' else '🔴'}",
                callback_data="admin_toggle_bot",
                icon_custom_emoji_id=get_emoji_icon("check_icon") if status_val == 'ON' else None
            )],
        [InlineKeyboardButton(
                text=f"VIP System: {vip_val} {'🟢' if vip_val == 'ON' else '🔴'}",
                callback_data="admin_toggle_vip_sys",
                icon_custom_emoji_id=get_emoji_icon("vip") if vip_val == 'ON' else None
            )],
    ])
    return kb

def admin_back_kb() -> InlineKeyboardMarkup:
    return make_inline_kb(inline_keyboard=[[
        InlineKeyboardButton(
            text="Back to Admin", callback_data="admin_panel_back",
            icon_custom_emoji_id=get_emoji_icon("back")
        )
    ]])

# ==============================================================================
# 8. NOTIFICATIONS
# ==============================================================================
async def send_advanced_notification(user_id: int, notif_type: str, amount: float, product: str = None, key: str = None, gateway: str = "ZapUPI") -> None:
    user_info = db_query("SELECT first_name, phone, username, is_reseller, is_vip FROM users WHERE user_id=?", (user_id,), fetchone=True)
    
    name = user_info[0] if user_info else "Unknown"
    phone = user_info[1] if user_info and user_info[1] else "Not Provided"
    username = f"@{user_info[2]}" if user_info and user_info[2] else "None"
    
    tags = []
    if user_info and user_info[3]: tags.append("👑 Reseller")
    if user_info and user_info[4]: tags.append("🌟 VIP")
    tag_str = " | ".join(tags) if tags else "👤 Regular"
        
    time_now = datetime.now().strftime("%d-%m-%Y %I:%M %p")
    
    if notif_type == "ORDER":
        title = "🛒 <b>NEW ORDER PROCESSED!</b> 🛒"
        details = (f"📦 <b>Product:</b> {product}\n🔑 <b>Key:</b> <code>{key}</code>\n💰 <b>Amount Paid:</b> ₹{amount:.2f}\n📅 <b>Time:</b> {time_now}")
    else:
        title = "💰 <b>NEW WALLET DEPOSIT!</b> 💰"
        details = (f"💵 <b>Amount Added:</b> ₹{amount:.2f}\n🧾 <b>Gateway:</b> {gateway}\n🆔 <b>Reference:</b> <code>{product}</code>\n📅 <b>Time:</b> {time_now}")

    msg = f"{title}\n━━━━━━━━━━━━━━━━━━\n👤 <b>Name:</b> {name}\n🆔 <b>User ID:</b> <code>{user_id}</code>\n📱 <b>Phone:</b> {phone}\n🔗 <b>Username:</b> {username}\n🏷 <b>Status:</b> {tag_str}\n━━━━━━━━━━━━━━━━━━\n{details}"
    for aid in ADMIN_IDS:
        try: 
            await bot.send_message(aid, msg, parse_mode='HTML')
        except Exception as e: 
            logger.error(f"Failed to send admin notification to {aid}: {e}")

async def send_payment_proof_channel(user_id: int, product: str, amount: float, order_id: str = "", api_response: Optional[dict] = None) -> None:
    """Post a public purchase proof without ever exposing the delivered key."""
    channel = (get_setting("payment_proof_channel", "") or "").strip()
    proof_enabled = (get_setting("payment_proof_channel_enabled", "ON") or "ON").upper() == "ON"
    if not proof_enabled or not channel or channel.lower() in ("none", "off", "disabled"):
        return

    user = db_query("SELECT first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
    # Public payment proof intentionally shows the customer's display name only.
    user_label = (user[0] if user and user[0] else "Customer").replace("<", "&lt;").replace(">", "&gt;")

    # Public proof deliberately contains no customer secret or API credential.
    verified_badge = get_emoji("check_icon")
    premium_badge = get_emoji("vip")
    text = (
        f"{premium_badge} <b>PREMIUM PAYMENT PROOF</b> {verified_badge}\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"📦 <b>Product:</b> {product}\n"
        f"💰 <b>Amount Paid:</b> {fmt_curr(amount)}\n"
        f"👤 <b>Customer:</b> {user_label}\n"
    )
    if order_id:
        text += f"🧾 <b>Order ID:</b> <code>{order_id}</code>\n"
    if api_response:
        if api_response.get("duration"):
            text += f"⏳ <b>Duration:</b> {api_response['duration']}\n"
        if api_response.get("expires_at"):
            text += f"⏰ <b>Expires:</b> {api_response['expires_at']}\n"
    text += (
        "━━━━━━━━━━━━━━━━━━\n"
        f"{verified_badge} <b>Payment Verified • Order Delivered</b> {premium_badge}\n"
        "\n"
        "🔑 <b>Key:</b> ____ <i>(Hide)</i>\n"
        "✓ <b>Bought via:-</b> @" + (BOT_USERNAME or "").lstrip("@") + "\n"
        "🛒 <b>Buy:-</b> @" + (BOT_USERNAME or "").lstrip("@")
    )

    # Public channels can be addressed as @username or https://t.me/username.
    target = channel
    if target.startswith("https://t.me/") or target.startswith("http://t.me/"):
        tail = target.rstrip("/").split("/")[-1]
        if tail and not tail.startswith("+"):
            target = "@" + tail.lstrip("@")
        else:
            logger.warning("Payment proof channel must be a public channel username, not a private invite link.")
            return
    elif target.startswith("t.me/"):
        tail = target.rstrip("/").split("/")[-1]
        if tail and not tail.startswith("+"):
            target = "@" + tail.lstrip("@")
        else:
            return
    elif not target.startswith("@"):
        target = "@" + target

    try:
        await bot.send_message(target, text, parse_mode="HTML", disable_web_page_preview=True)
    except Exception as exc:
        logger.warning("Payment proof channel post failed for %s: %s", target, exc)

def _clean_famgateway_api_key(raw: str) -> str:
    """Normalize a FamGateway API key pasted from a dashboard/message."""
    value = str(raw or "").strip().strip('"\'`')
    prefixes = ("Bearer ", "bearer ", "X-Api-Key:", "x-api-key:", "X-API-KEY:", "x-api-key=", "api_key=", "API_KEY=")
    changed = True
    while changed:
        changed = False
        for prefix in prefixes:
            if value.startswith(prefix):
                value = value[len(prefix):].strip().strip('"\'`')
                changed = True
                break
    return value


def _famgateway_api_key() -> str:
    """Read DB key first, then FAMGATEWAY_API_KEY environment variable."""
    stored = get_setting("famgateway_api", "")
    return _clean_famgateway_api_key(stored or os.getenv("FAMGATEWAY_API_KEY", ""))


def _famgateway_base_url() -> str:
    stored = get_setting("famgateway_url", "")
    return (stored or os.getenv("FAMGATEWAY_URL", "https://famgateway.in") or "https://famgateway.in").strip().rstrip("/")


def _famgateway_normalize_status(data: Any) -> str:
    if not isinstance(data, dict):
        return ""
    nested = data.get("data") if isinstance(data.get("data"), dict) else {}
    raw = data.get("status") or nested.get("status") or data.get("payment_status") or nested.get("payment_status")
    return str(raw or "").strip().lower()


def _famgateway_error_message(data: Any, http_status: int) -> str:
    if isinstance(data, dict):
        nested = data.get("data") if isinstance(data.get("data"), dict) else {}
        msg = data.get("message") or data.get("error") or nested.get("message")
        if msg:
            return str(msg)
    if http_status == 401:
        return "FamGateway rejected the API key (HTTP 401). Replace it with the active API Key from your FamGateway dashboard."
    if http_status == 403:
        return "FamGateway account/API access is suspended or forbidden (HTTP 403)."
    if http_status == 404:
        return "FamGateway endpoint or order was not found (HTTP 404)."
    if http_status == 408:
        return "FamGateway payment session has expired (HTTP 408)."
    if http_status == 429:
        return "FamGateway rate limit reached (HTTP 429). Please wait a few seconds."
    return f"FamGateway HTTP {http_status}."


async def _famgateway_request(method: str, url: str, api_key: str, *, json_payload: Optional[dict] = None, params: Optional[dict] = None, timeout: int = 20) -> Tuple[int, Any]:
    """Use documented FamGateway authentication; alternate auth is tried only after HTTP 401."""
    api_key = _clean_famgateway_api_key(api_key)
    base_headers = {"Accept": "application/json"}
    if json_payload is not None:
        base_headers["Content-Type"] = "application/json"
    attempts = [
        ("header", {**base_headers, "X-Api-Key": api_key}, dict(json_payload) if json_payload is not None else None, dict(params or {})),
        ("bearer", {**base_headers, "Authorization": f"Bearer {api_key}"}, dict(json_payload) if json_payload is not None else None, dict(params or {})),
    ]
    if json_payload is not None:
        body_with_key = dict(json_payload)
        body_with_key["api_key"] = api_key
        attempts.append(("body", base_headers.copy(), body_with_key, dict(params or {})))
    query_params = dict(params or {})
    query_params["api_key"] = api_key
    attempts.append(("query", base_headers.copy(), dict(json_payload) if json_payload is not None else None, query_params))

    async with aiohttp.ClientSession() as session:
        last_status, last_data = 0, {}
        for index, (_mode, headers, body, request_params) in enumerate(attempts):
            try:
                async with session.request(method.upper(), url, json=body if body is not None else None, params=request_params or None, headers=headers, timeout=timeout) as resp:
                    raw_text = await resp.text()
                    try:
                        data = json.loads(raw_text) if raw_text else {}
                    except Exception:
                        data = {"raw_text": raw_text[:1000]}
                    last_status, last_data = resp.status, data
                    if resp.status != 401 or index == len(attempts) - 1:
                        return resp.status, data
            except asyncio.TimeoutError:
                return 408, {"status": "error", "message": "FamGateway request timed out."}
            except aiohttp.ClientError as exc:
                return 0, {"status": "error", "message": f"FamGateway connection error: {exc}"}
            except Exception as exc:
                logger.exception("FamGateway request failed")
                return 0, {"status": "error", "message": f"FamGateway connection error: {exc}"}
        return last_status, last_data


async def famgateway_create_order(user_id: int, amount: float, description: str = "Wallet Topup") -> dict:
    api_key = _famgateway_api_key()
    base_url = _famgateway_base_url()
    if not api_key:
        return {"status": "error", "message": "FamGateway API key is not configured. Set FAMGATEWAY_API_KEY or configure it in Admin → FamGateway."}
    try:
        amount = round(float(amount), 2)
    except (TypeError, ValueError):
        return {"status": "error", "message": "Invalid payment amount."}
    if amount <= 0:
        return {"status": "error", "message": "Payment amount must be greater than zero."}
    user = db_query("SELECT first_name, phone FROM users WHERE user_id=?", (user_id,), fetchone=True)
    customer_name = (user[0] if user and user[0] else "Customer")
    customer_phone = (user[1] if user and user[1] else "")
    payload = {"amount": amount, "customer_name": str(customer_name)[:100], "customer_phone": str(customer_phone)[:20], "description": str(description or "Wallet Topup")[:120]}
    try:
        http_status, data = await _famgateway_request("POST", f"{base_url}/api/create-order", api_key, json_payload=payload, timeout=20)
        if http_status < 200 or http_status >= 300:
            return {"status": "error", "message": _famgateway_error_message(data, http_status), "http_status": http_status, "raw": data}
        if not isinstance(data, dict):
            return {"status": "error", "message": "FamGateway returned an invalid response."}
        result = data.get("data") if isinstance(data.get("data"), dict) else data
        status = _famgateway_normalize_status(data)
        if status not in {"success", "created", "pending"}:
            return {"status": "error", "message": _famgateway_error_message(data, http_status), "raw": data}
        gateway_order_id = result.get("order_id") or data.get("order_id")
        payment_url = result.get("checkout_url") or result.get("payment_url") or result.get("qr_url")
        if not gateway_order_id:
            return {"status": "error", "message": "FamGateway did not return an order_id.", "raw": data}
        if not payment_url:
            return {"status": "error", "message": "FamGateway did not return a checkout/QR URL.", "raw": data}
        return {**result, "status": "success", "order_id": str(gateway_order_id),
                "checkout_url": result.get("checkout_url") or payment_url,
                "payment_url": result.get("payment_url") or payment_url,
                "qr_url": result.get("qr_url") or "",
                "upi_intent": result.get("upi_intent") or "",
                "payable_amount": result.get("payable_amount") or result.get("amount") or amount}
    except Exception as exc:
        logger.exception("FamGateway create-order failed")
        return {"status": "error", "message": f"FamGateway connection error: {exc}"}


async def famgateway_check_order(order_id: str) -> dict:
    """Authoritative FamGateway server-side status check."""
    api_key = _famgateway_api_key()
    base_url = _famgateway_base_url()
    order_id = str(order_id or "").strip()
    if not api_key:
        return {"status": "error", "message": "FamGateway API key is not configured."}
    if not order_id:
        return {"status": "error", "message": "FamGateway order_id is missing."}
    try:
        http_status, data = await _famgateway_request("GET", f"{base_url}/api/verify-order.php", api_key, params={"order_id": order_id}, timeout=15)
        if http_status < 200 or http_status >= 300:
            return {"status": "error", "message": _famgateway_error_message(data, http_status), "http_status": http_status, "raw": data}
        if not isinstance(data, dict):
            return {"status": "error", "message": "Invalid FamGateway verification response."}
        status = _famgateway_normalize_status(data)
        nested = data.get("data") if isinstance(data.get("data"), dict) else data
        if status in {"success", "paid", "completed", "confirmed"}:
            return {"status": "success", "data": nested, "raw": data}
        if status in {"pending", "processing", "initiated", "created", "awaiting_payment"}:
            return {"status": "pending", "data": nested, "raw": data}
        if status in {"expired", "failed", "cancelled", "canceled", "error", "not_found"}:
            return {"status": "expired" if status == "expired" else "failed", "message": data.get("message", status), "raw": data}
        return {"status": "pending", "message": data.get("message", "Payment status is not confirmed yet."), "raw": data}
    except Exception as exc:
        logger.warning("FamGateway verify failed for %s: %s", order_id, exc)
        return {"status": "error", "message": str(exc)}

# ==============================================================================
# 9. PAYMENT VERIFIER
# ==============================================================================
def _claim_transaction_paid(order_id: str) -> bool:
    """Atomically claim a pending payment exactly once across the verifier and background worker."""
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    try:
        conn.execute("BEGIN IMMEDIATE")
        cur = conn.execute("UPDATE transactions SET status='paid' WHERE order_id=? AND status='pending'", (str(order_id),))
        won = cur.rowcount == 1
        conn.commit()
        return won
    except Exception:
        conn.rollback()
        logger.exception("Could not atomically claim paid transaction %s", order_id)
        return False
    finally:
        conn.close()

async def _fulfill_special_gateway_payment(user_id: int, purpose: str, description: str, amount: float, gateway_name: str) -> bool:
    """Fulfil FF Like / Glory purchases after gateway verification without adding a wallet top-up."""
    try:
        meta = json.loads(description or "{}")
        if not isinstance(meta, dict): raise ValueError("metadata is not an object")
        user_row = db_query("SELECT username, first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
        user_obj = SimpleNamespace(id=user_id, username=(user_row[0] if user_row else None), full_name=(user_row[1] if user_row else "User"))
        if purpose == "ff_like_purchase":
            required = ("ff_product_id", "ff_title", "ff_price", "ff_uid", "ff_photo", "ff_region_label")
            if any(k not in meta for k in required): raise ValueError("FF Like metadata incomplete")
            target = await bot.send_message(user_id, f"✅ {html.escape(gateway_name)} payment verified. Sending your FF Like order for admin review…", parse_mode="HTML")
            fake = SimpleNamespace(from_user=user_obj, answer=target.answer)
            await ff_create_order(fake, meta, f"{gateway_name} (paid)")
            return True
        if purpose == "ffglory_purchase":
            clan = str(meta.get("clan", "")); region_id = str(meta.get("region_id", "")); region_name = str(meta.get("region_name", region_id))
            if not clan or not region_id: raise ValueError("FF Glory metadata incomplete")
            target = await bot.send_message(user_id, "✅ UPI payment verified.\n⏳ Submitting Guild Glory order…\n⏱️ Waiting for provider response: 0s", parse_mode="HTML")
            submitted_at = datetime.now().astimezone()
            result = await _ffglorypro_submit_with_live_timer(target, region_id, clan)
            if result.get("_ambiguous") or result.get("_timeout"):
                matched = await _ffglorypro_find_recent_group(clan, region_id, submitted_at)
                if matched and matched.get("group_id"):
                    result = {"success": True, "group_id": matched.get("group_id"), "status": matched.get("status", "running"), "_reconciled": True}
            if result.get("success") is True and result.get("group_id"):
                gid = str(result.get("group_id")); status = str(result.get("status", "running"))
                _save_ffglorypro_order(user_id, gid, clan, region_id, region_name, amount, gateway_name, status)
                try: await send_payment_proof_channel(user_id, f"Guild Glory ({region_name})", amount, gid)
                except Exception: logger.exception("Guild Glory payment proof failed")
                await target.edit_text(f"🎉 <b>Guild Glory Order Submitted</b>\nOrder: <code>{html.escape(gid)}</code>\nClan ID: <code>{html.escape(clan)}</code>\nRegion: {html.escape(region_name)}\nStatus: <b>{html.escape(status)}</b>\nPaid: ₹{amount:g}", parse_mode="HTML")
                for aid in getattr(ADMIN_ID,"all_ids",{int(ADMIN_ID)}):
                    try: await bot.send_message(int(aid), f"📣 <b>Paid Guild Glory order</b>\nUser: <code>{user_id}</code>\nOrder: <code>{html.escape(gid)}</code>\nClan: <code>{html.escape(clan)}</code>\nRegion: {html.escape(region_name)}\nPaid: ₹{amount:g}", parse_mode="HTML")
                    except Exception: pass
                return True
            code = int(result.get("_http_status") or 0)
            if code in (400,402,403,404,409,422) and not result.get("_ambiguous"):
                db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (amount,user_id))
                await target.edit_text(f"⚠️ Provider rejected the paid order. ₹{amount:g} has been credited to your wallet instead.\nError: {html.escape(_glorypro_err(result))}", parse_mode="HTML")
            else:
                await target.edit_text("⏳ Payment is verified, but the provider response is unclear. Your paid amount is on hold while admin checks the provider history. Please do not submit again.", parse_mode="HTML")
                for aid in getattr(ADMIN_ID,"all_ids",{int(ADMIN_ID)}):
                    try: await bot.send_message(int(aid), f"⚠️ <b>Paid FF Glory status check required</b>\nUser: <code>{user_id}</code>\nClan: <code>{html.escape(clan)}</code>\nRegion: {html.escape(region_name)}\nAmount: ₹{amount:g}\nCheck provider history before retry/refund.", parse_mode="HTML")
                    except Exception: pass
            return True
    except Exception:
        logger.exception("Special gateway payment fulfilment failed: user=%s purpose=%s", user_id, purpose)
        try: await bot.send_message(user_id, "⚠️ Payment is verified but automatic order fulfilment failed. Contact admin with your payment order ID; do not pay again.")
        except Exception: pass
        return True
    return False

async def run_payment_verification(user_id: int, order_id: str, reply_target: Any) -> None:
    lock = _payment_verify_locks.get(str(order_id))
    if lock is None:
        lock = asyncio.Lock()
        _payment_verify_locks[str(order_id)] = lock
    if lock.locked():
        if isinstance(reply_target, CallbackQuery):
            return await reply_target.answer("⏳ This payment is already being checked. Please wait 3 seconds.", show_alert=True)
        return
    async with lock:
        return await _run_payment_verification_locked(user_id, order_id, reply_target)

async def _run_payment_verification_locked(user_id: int, order_id: str, reply_target: Any) -> None:
    txn = db_query(
        "SELECT amount_inr, status, timestamp, purpose, product_id, quantity, description, gateway "
        "FROM transactions WHERE order_id=?",
        (order_id,), fetchone=True
    )
    if not txn:
        err = "❌ Invalid or Fake Order ID detected in system!"
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(err, show_alert=True)
        else: await reply_target.answer(err)
        return
        
    txn_gateway = (txn[7] or "zapupi").strip().lower()
    expiry_seconds = 300 if txn_gateway == "famgateway" else 900
    if time.time() - txn[2] > expiry_seconds and txn[1] == 'pending':
        db_query("UPDATE transactions SET status='expired' WHERE order_id=? AND status='pending'", (order_id,))
        window_text = "5-minute" if txn_gateway == "famgateway" else "15-minute"
        err_msg = f"⏳ <b>Payment Timed Out!</b>\nThe {window_text} verification window has expired."
        if isinstance(reply_target, CallbackQuery): await reply_target.message.edit_text(err_msg, reply_markup=back_kb(), parse_mode='HTML')
        else: await reply_target.answer(err_msg, reply_markup=back_kb())
        return

    if txn[1] == 'paid':
        msg = ("✅ This payment has already been processed." if txn[3] in ("ff_like_purchase", "ffglory_purchase") else "✅ This payment has already been securely credited to your wallet.")
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(msg, show_alert=True)
        else: await reply_target.answer(msg)
        return
    elif txn[1] == 'expired':
        msg = "❌ This order has expired. Please create a new deposit request."
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(msg, show_alert=True)
        else: await reply_target.answer(msg)
        return
        
    gateway = (txn[7] or "zapupi").lower()
    if gateway == "famgateway":
        res_json = await famgateway_check_order(order_id)
        if res_json.get("status") == "success":
            if not _claim_transaction_paid(order_id):
                return
            if txn[3] in ("ff_like_purchase", "ffglory_purchase"):
                await _fulfill_special_gateway_payment(user_id, txn[3], txn[6] or "", float(txn[0] or 0), "FamGateway")
                return
            db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (txn[0], user_id))
            if txn[3] == "product_purchase" and txn[4]:
                target_message = reply_target.message if isinstance(reply_target, CallbackQuery) else reply_target
                user_row = db_query("SELECT user_id, username, first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
                proxy = _PurchaseCallProxy(SimpleNamespace(id=user_id, username=(user_row[1] if user_row else None), full_name=(user_row[2] if user_row else "User")), target_message)
                for _ in range(max(1, int(txn[5] or 1))):
                    await _process_single_buy(proxy, int(txn[4]))
            else:
                success_msg = f"🎉 <b>VERIFICATION SUCCESSFUL!</b>\n\n✅ {fmt_curr(txn[0])} has been added to your wallet securely via FamGateway."
                if isinstance(reply_target, CallbackQuery): await reply_target.message.edit_text(success_msg, reply_markup=back_kb(), parse_mode='HTML')
                else: await reply_target.answer(success_msg, reply_markup=back_kb())
                await send_advanced_notification(user_id, "DEPOSIT", txn[0], product=order_id, gateway="FamGateway")
            return
        if res_json.get("status") == "pending":
            msg = "⏳ FamGateway payment is still pending. Please wait a few seconds and try again."
        elif res_json.get("status") == "expired":
            db_query("UPDATE transactions SET status='expired' WHERE order_id=?", (order_id,))
            msg = "❌ This FamGateway payment session has expired. Please create a new payment."
        else:
            msg = f"⚠️ FamGateway error: {res_json.get('message', 'Unable to verify payment')}"
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(msg, show_alert=True)
        else: await reply_target.answer(msg)
        return

    api_key_check = db_query("SELECT value FROM settings WHERE key='zapupi_api'", fetchone=True)
    if not api_key_check:
        msg = "⚠️ Gateway API key missing. Administrator needs to configure it."
        if isinstance(reply_target, CallbackQuery): await reply_target.answer(msg, show_alert=True)
        else: await reply_target.answer(msg)
        return
        
    api_key = api_key_check[0]
    url = "https://pay.zapupi.com/api/order-status"
    payload = {"zap_key": api_key, "order_id": order_id}
    
    async with aiohttp.ClientSession() as session:
        try:
            async with session.post(url, json=payload) as resp:
                if resp.status == 200:
                    try: res_json = await resp.json(content_type=None)
                    except Exception: res_json = {}
                        
                    if res_json.get("status") == "success":
                        txn_data = res_json.get("data", {})
                        real_status = txn_data.get("status", "Pending")
                        
                        if real_status == "Success":
                            if not _claim_transaction_paid(order_id): return
                            if txn[3] in ("ff_like_purchase", "ffglory_purchase"):
                                await _fulfill_special_gateway_payment(user_id, txn[3], txn[6] or "", float(txn[0] or 0), "ZapUPI")
                                return
                            db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (txn[0], user_id))

                            if txn[3] == "product_purchase" and txn[4]:
                                target_message = reply_target.message if isinstance(reply_target, CallbackQuery) else reply_target
                                user_row = db_query("SELECT user_id, username, first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
                                proxy_user = SimpleNamespace(
                                    id=user_id,
                                    username=(user_row[1] if user_row else None),
                                    full_name=(user_row[2] if user_row else "User")
                                )
                                proxy = _PurchaseCallProxy(proxy_user, target_message)
                                for _ in range(max(1, int(txn[5] or 1))):
                                    await _process_single_buy(proxy, int(txn[4]))
                                log_activity(
                                    user_id, "DIRECT_UPI_PURCHASE_PAID",
                                    f"Amount: {txn[0]}, Product: {txn[4]}, Qty: {txn[5]}, Order: {order_id}"
                                )
                            else:
                                success_msg = f"🎉 <b>VERIFICATION SUCCESSFUL!</b>\n\n✅ {fmt_curr(txn[0])} has been added to your wallet securely."
                                if isinstance(reply_target, CallbackQuery):
                                    await reply_target.message.edit_text(success_msg, reply_markup=back_kb(), parse_mode='HTML')
                                else:
                                    await reply_target.answer(success_msg, reply_markup=back_kb())
                                await send_advanced_notification(user_id, "DEPOSIT", txn[0], product=order_id, gateway="ZapUPI")
                                log_activity(user_id, "DEPOSIT_SUCCESS", f"Amount: {txn[0]}, Gateway: ZapUPI, Order: {order_id}")

                        elif real_status == "Pending":
                            fail_msg = "⏳ Payment is still Pending at the gateway. Please wait a minute and try clicking manual verify again."
                            if isinstance(reply_target, CallbackQuery): await reply_target.answer(fail_msg, show_alert=True)
                            else: await reply_target.answer(fail_msg)
                        else:
                            fail_msg = f"❌ Payment Failed or Cancelled (Gateway Status: {real_status})."
                            if isinstance(reply_target, CallbackQuery): await reply_target.answer(fail_msg, show_alert=True)
                            else: await reply_target.answer(fail_msg)
                    else:
                        err = f"⚠️ Gateway Error: {res_json.get('message', 'Unknown Error')}"
                        if isinstance(reply_target, CallbackQuery): await reply_target.answer(err, show_alert=True)
                        else: await reply_target.answer(err)
                else:
                    err = f"⚠️ Gateway HTTP Error: {resp.status}. Gateway might be down."
                    if isinstance(reply_target, CallbackQuery): await reply_target.answer(err, show_alert=True)
                    else: await reply_target.answer(err)
        except Exception as e:
            logger.error(f"ZapUPI API Error: {str(e)}")
            err = f"⚠️ Unable to connect to Gateway API: Network Issue."
            if isinstance(reply_target, CallbackQuery): await reply_target.answer(err, show_alert=True)
            else: await reply_target.answer(err)

def ensure_transactions_schema() -> None:
    """Ensure the payment-verifier table exists even if a deployment points at a fresh DB."""
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    try:
        conn.execute("""CREATE TABLE IF NOT EXISTS transactions (
            order_id TEXT PRIMARY KEY,
            user_id INTEGER,
            amount_inr REAL,
            status TEXT,
            timestamp INTEGER,
            purpose TEXT DEFAULT 'wallet_topup',
            product_id INTEGER,
            quantity INTEGER DEFAULT 1,
            description TEXT DEFAULT '',
            gateway TEXT DEFAULT 'zapupi'
        )""")
        existing = {row[1] for row in conn.execute("PRAGMA table_info(transactions)").fetchall()}
        required = {
            'purpose': "TEXT DEFAULT 'wallet_topup'",
            'product_id': 'INTEGER',
            'quantity': 'INTEGER DEFAULT 1',
            'description': "TEXT DEFAULT ''",
            'gateway': "TEXT DEFAULT 'zapupi'",
        }
        for col, definition in required.items():
            if col not in existing:
                conn.execute(f"ALTER TABLE transactions ADD COLUMN {col} {definition}")
                logger.warning("Self-healing DB migration added transactions.%s", col)
        conn.commit()
    finally:
        conn.close()


async def auto_verify_task() -> None:
    """Background payment verifier. Never dies because of one bad transaction/API response."""
    while True:
        try:
            await asyncio.sleep(5)
            ensure_transactions_schema()
            pending_txns = db_query(
                "SELECT order_id, user_id, amount_inr, timestamp, purpose, product_id, quantity, gateway, description "
                "FROM transactions WHERE status='pending'",
                fetchall=True
            ) or []

            for txn in pending_txns:
                try:
                    order_id, user_id, amount, ts, purpose, product_id, quantity, gateway, description = txn
                    gw = (gateway or "zapupi").strip().lower()
                    expiry_seconds = 300 if gw == "famgateway" else 900
                    if time.time() - float(ts or 0) > expiry_seconds:
                        db_query("UPDATE transactions SET status='expired' WHERE order_id=? AND status='pending'", (order_id,))
                        try:
                            await bot.send_message(user_id, f"⏳ <b>Order Expired!</b>\nYour payment window for order <code>{order_id}</code> has timed out.", parse_mode='HTML')
                        except Exception:
                            pass
                        continue

                    paid = False
                    gateway_name = "ZapUPI"

                    if gw == "famgateway":
                        res_json = await famgateway_check_order(order_id)
                        paid = str(res_json.get("status", "")).lower() == "success"
                        gateway_name = "FamGateway"
                        if res_json.get("status") == "expired":
                            db_query("UPDATE transactions SET status='expired' WHERE order_id=? AND status='pending'", (order_id,))
                            continue
                        if res_json.get("status") in {"error", "failed"}:
                            logger.warning("FamGateway pending order %s: %s", order_id, res_json.get("message", "unknown"))
                            continue
                    else:
                        api_key_check = db_query("SELECT value FROM settings WHERE key='zapupi_api'", fetchone=True)
                        if not api_key_check or not api_key_check[0]:
                            continue
                        api_key = api_key_check[0]
                        try:
                            async with aiohttp.ClientSession() as session:
                                async with session.post(
                                    "https://pay.zapupi.com/api/order-status",
                                    json={"zap_key": api_key, "order_id": order_id},
                                    timeout=15
                                ) as resp:
                                    res_json = await resp.json(content_type=None)
                            if resp.status == 200 and isinstance(res_json, dict):
                                top = str(res_json.get("status", "")).strip().lower()
                                data = res_json.get("data") if isinstance(res_json.get("data"), dict) else res_json
                                real_status = str(data.get("status", "")).strip().lower()
                                paid = top in {"success", "ok", "paid"} and real_status in {"success", "paid", "completed", "complete"}
                                if real_status in {"expired", "failed", "cancelled", "canceled"}:
                                    db_query("UPDATE transactions SET status='expired' WHERE order_id=? AND status='pending'", (order_id,))
                                    continue
                            else:
                                logger.warning("ZapUPI status HTTP %s for %s", getattr(resp, "status", "?"), order_id)
                        except Exception as exc:
                            logger.warning("ZapUPI auto-verify request failed for %s: %s", order_id, exc)
                            continue

                    if not paid:
                        continue

                    # Atomic claim: only the worker that changes pending -> paid may fulfill.
                    if not _claim_transaction_paid(order_id):
                        continue

                    # FF Like / Glory gateway payments are fulfilled directly and must not become wallet top-ups.
                    if purpose in ("ff_like_purchase", "ffglory_purchase"):
                        await _fulfill_special_gateway_payment(user_id, purpose, description or "", float(amount or 0), gateway_name)
                        continue

                    # For direct product purchases, _process_single_buy charges the wallet; temporarily credit exactly once.
                    db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amount, user_id))

                    if purpose == "product_purchase" and product_id:
                        target_message = await bot.send_message(
                            user_id,
                            f"✨ <b>{gateway_name.upper()} PAYMENT VERIFIED</b>\n\n"
                            f"🛒 Completing your purchase automatically...\n"
                            f"💰 Paid: <b>{fmt_curr(amount)}</b>",
                            parse_mode='HTML'
                        )
                        user_row = db_query("SELECT username, first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
                        proxy_user = SimpleNamespace(
                            id=user_id,
                            username=(user_row[0] if user_row else None),
                            full_name=(user_row[1] if user_row else "User")
                        )
                        proxy = _PurchaseCallProxy(proxy_user, target_message)
                        for _ in range(max(1, int(quantity or 1))):
                            try:
                                await _process_single_buy(proxy, int(product_id))
                            except Exception:
                                logger.exception("Auto product fulfillment failed: order=%s product=%s", order_id, product_id)
                                break
                        log_activity(user_id, "DIRECT_PAYMENT_AUTO_VERIFIED", f"Amount: {amount}, Gateway: {gateway_name}, Product: {product_id}, Qty: {quantity}, Order: {order_id}")
                    else:
                        try:
                            await bot.send_message(
                                user_id,
                                f"✨ <b>AUTO-VERIFIED!</b>\n\n✅ Your payment was detected successfully. {fmt_curr(amount)} has been added to your balance!",
                                parse_mode='HTML'
                            )
                        except Exception:
                            pass
                        await send_advanced_notification(user_id, "DEPOSIT", amount, product=order_id, gateway=f"{gateway_name} Auto")
                        log_activity(user_id, "DEPOSIT_AUTO_SUCCESS", f"Amount: {amount}, Gateway: {gateway_name} Auto, Order: {order_id}")

                except Exception:
                    logger.exception("Auto-verifier transaction cycle failed for order=%s", txn[0] if txn else "?")
                    continue

        except asyncio.CancelledError:
            raise
        except Exception:
            logger.exception("Auto-verifier daemon recovered from an unexpected error")
            await asyncio.sleep(3)

# ==============================================================================

# ==============================================================================
@dp.callback_query(F.data == "admin_hosting_server_ip")
async def admin_hosting_server_ip(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    await call.answer("Checking hosting IP…")
    local_ip = "Unavailable"
    public_ip = "Unavailable"
    try:
        local_ip = socket.gethostbyname(socket.gethostname())
    except Exception:
        pass
    try:
        timeout = aiohttp.ClientTimeout(total=5)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get("https://api.ipify.org", allow_redirects=True) as response:
                if response.status == 200:
                    candidate = (await response.text()).strip()
                    import ipaddress
                    public_ip = str(ipaddress.ip_address(candidate))
    except Exception as exc:
        logger.warning("Could not determine public hosting IP: %s", exc)
    await call.message.answer(
        "🌐 <b>Hosting Server IP</b>\n\n"
        f"🌍 Public IP: <code>{html.escape(public_ip)}</code>\n"
        f"🖥️ Container/Local IP: <code>{html.escape(local_ip)}</code>\n\n"
        "<i>Railway/proxy hosting may show a shared or dynamic outbound IP. If public IP is unavailable, check the hosting dashboard.</i>",
        reply_markup=admin_back_kb(), parse_mode="HTML"
    )


# ADMIN DATABASE BACKUP/RESTORE + REFERRAL COMMISSION SETTINGS
# ==============================================================================
@dp.callback_query(F.data == "admin_db_tools")
async def admin_db_tools(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="⬇️ Download Database Backup", callback_data="admin_db_download")],
        [InlineKeyboardButton(text="⬆️ Upload / Restore Database", callback_data="admin_db_upload")],
        [InlineKeyboardButton(text="BACK", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))],
    ])
    await call.message.edit_text(
        "<b>Database Backup / Restore</b>\n\n"
        "Download a backup before restoring. Upload only a trusted SQLite .db file. "
        "Restore replaces the current database after validation.",
        reply_markup=kb, parse_mode="HTML"
    )
    await call.answer()

@dp.callback_query(F.data == "admin_db_download")
async def admin_db_download(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    try:
        # SQLite backup API safely captures a consistent snapshot.
        with sqlite3.connect(DB_PATH, timeout=30) as src:
            with tempfile.NamedTemporaryFile(prefix="bot_db_backup_", suffix=".db", delete=False) as tmp:
                backup_path = tmp.name
            with sqlite3.connect(backup_path) as dst:
                src.backup(dst)
        await bot.send_document(call.from_user.id, FSInputFile(backup_path, filename="bot_database_backup.db"),
                                caption="Database backup. Keep this file private.")
        os.unlink(backup_path)
        await call.answer("Backup sent in private chat.")
    except Exception as exc:
        logger.exception("Database backup failed: %s", exc)
        await call.answer("Database backup failed. Check logs.", show_alert=True)

@dp.callback_query(F.data == "admin_db_upload")
async def admin_db_upload(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    await state.set_state(AdminStates.wait_for_db_upload)
    await call.message.answer(
        "Send the trusted SQLite database file as a Telegram document (.db). "
        "The current database will be backed up first, then replaced after integrity checks.",
        reply_markup=admin_back_kb()
    )
    await call.answer()

@dp.message(AdminStates.wait_for_db_upload)
async def admin_db_upload_receive(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id):
        return
    doc = message.document
    if not doc or not (doc.file_name or "").lower().endswith((".db", ".sqlite", ".sqlite3")):
        return await message.answer("Please upload a SQLite .db, .sqlite, or .sqlite3 file.")
    if doc.file_size and doc.file_size > 50 * 1024 * 1024:
        return await message.answer("Database file is larger than 50 MB.")
    tmp_in = None
    backup_path = None
    try:
        fd, tmp_in = tempfile.mkstemp(prefix="db_restore_upload_", suffix=".db")
        os.close(fd)
        await bot.download(doc, destination=tmp_in)
        with sqlite3.connect(f"file:{tmp_in}?mode=ro", uri=True, timeout=20) as test_conn:
            result = test_conn.execute("PRAGMA integrity_check").fetchone()
            tables = {r[0] for r in test_conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
            if not result or result[0] != "ok":
                raise ValueError("SQLite integrity check failed")
            if not {"users", "settings", "products"}.issubset(tables):
                raise ValueError("Database is missing required bot tables")
        # Save current DB before replacement.
        with sqlite3.connect(DB_PATH, timeout=30) as src:
            fd, backup_path = tempfile.mkstemp(prefix="pre_restore_backup_", suffix=".db")
            os.close(fd)
            with sqlite3.connect(backup_path) as dst:
                src.backup(dst)
        shutil.copy2(tmp_in, DB_PATH)
        init_db()  # run schema migrations after restoring
        await message.answer("✅ Database restored and validated. The previous database backup was created on the server.")
        await state.clear()
    except Exception as exc:
        logger.exception("Database restore failed: %s", exc)
        await message.answer(f"❌ Database restore failed: {html.escape(str(exc))}")
    finally:
        for fp in (tmp_in,):
            if fp and os.path.exists(fp):
                try: os.unlink(fp)
                except OSError: pass

# ==============================================================================
# FF LIKE CUSTOM PRODUCTS / ORDERS
# ==============================================================================
def _load_region_settings(key: str, fallback: list) -> list:
    try:
        value = json.loads(get_setting(key, "") or "")
        return value if isinstance(value, list) else fallback
    except Exception:
        return fallback

def ff_regions_kb():
    fallback = [
        {"code":"IND","name":"India","emoji":"🇮🇳"},
        {"code":"BD","name":"Bangladesh","emoji":"🇧🇩"},
        {"code":"NP","name":"Nepal","emoji":"🇳🇵"},
        {"code":"LK","name":"Sri Lanka","emoji":"🇱🇰"},
    ]
    regions = _load_region_settings("ff_like_regions_json", fallback)
    rows = []
    for region in regions:
        if not isinstance(region, dict) or not region.get("code") or not region.get("name"):
            continue
        code = re.sub(r"[^A-Za-z0-9_-]", "", str(region["code"]))[:16]
        name = str(region["name"])[:28]
        emoji = str(region.get("emoji", "🌍"))[:16]
        if code and region.get("enabled", True):
            rows.append([InlineKeyboardButton(text=f"{emoji} {name}"[:64], callback_data=f"ff_region_{code}")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="ff_menu")])
    return make_inline_kb(inline_keyboard=rows, _width=1)

@dp.callback_query(F.data == "admin_ff_regions")
async def admin_ff_regions(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    regions = _load_region_settings("ff_like_regions_json", [])
    listing = "\n".join(f"• {r.get('emoji','🌍')} {r.get('name','?')} — <code>{html.escape(str(r.get('code','')))}</code>" for r in regions if isinstance(r, dict)) or "(none)"
    kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="➕ Add / Update Region", callback_data="admin_ff_regions_edit")], [InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ff_menu")]])
    await call.message.edit_text("🌍 <b>FF Like Regions</b>\n"+listing+"\n\nFormat: <code>ADD | IND | India | 🇮🇳</code>, <code>OFF | IND</code>, <code>ON | IND</code> or <code>REMOVE | IND</code>. Codes sent to the FF GLORY likes API must be supported by that provider.", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_ff_regions_edit")
async def admin_ff_regions_edit(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_ff_region_config)
    await call.message.answer("Send: ADD | CODE | Name | Emoji  OR  REMOVE | CODE\nExample: ADD | IND | India | 🇮🇳")
    await call.answer()

@dp.message(AdminStates.wait_for_ff_region_config)
async def admin_ff_regions_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    parts = [x.strip() for x in (message.text or "").split("|")]
    regions = _load_region_settings("ff_like_regions_json", [])
    if len(parts) == 2 and parts[0].upper() == "REMOVE":
        code = re.sub(r"[^A-Za-z0-9_-]", "", parts[1]).upper()
        regions = [r for r in regions if str(r.get("code", "")).upper() != code]
        set_setting("ff_like_regions_json", json.dumps(regions, ensure_ascii=False))
        await state.clear(); return await message.answer(f"✅ Removed FF Like region {code} (if it existed).", reply_markup=admin_kb())
    if len(parts) == 2 and parts[0].upper() in ("ON", "OFF"):
        code = re.sub(r"[^A-Za-z0-9_-]", "", parts[1]).upper()
        found = False
        for r in regions:
            if str(r.get("code", "")).upper() == code: r["enabled"] = parts[0].upper() == "ON"; found = True
        if not found: return await message.answer("Region not found. Add it first.")
        set_setting("ff_like_regions_json", json.dumps(regions, ensure_ascii=False))
        await state.clear(); return await message.answer(f"✅ FF Like region {code} set {parts[0].upper()}.", reply_markup=admin_kb())
    if len(parts) != 4 or parts[0].upper() != "ADD" or not parts[1] or not parts[2]:
        return await message.answer("Invalid format. Use ADD | CODE | Name | Emoji or REMOVE | CODE")
    code = re.sub(r"[^A-Za-z0-9_-]", "", parts[1]).upper()
    if not code or len(code) > 16 or len(parts[2]) > 28: return await message.answer("Code/name invalid or too long.")
    region = {"code":code,"name":parts[2],"emoji":parts[3] or "🌍"}
    regions = [r for r in regions if str(r.get("code", "")).upper() != code]
    regions.append(region)
    set_setting("ff_like_regions_json", json.dumps(regions, ensure_ascii=False))
    await state.clear(); await message.answer(f"✅ Saved FF Like region: {region['emoji']} {region['name']} ({code}). This option will now appear in the user region selector.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ff_menu")
async def admin_ff_menu(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    enabled=(get_setting("ff_like_enabled", "OFF") or "OFF").upper()
    pending=db_query("SELECT COUNT(*) FROM ff_orders WHERE status='pending'",fetchone=True)
    pending_count=int(pending[0] or 0) if pending else 0
    kb=make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"FF Like: {'🟢 ON' if enabled=='ON' else '🔴 OFF'}", callback_data="admin_ff_toggle")],
        [InlineKeyboardButton(text="➕ Add Package / Description / Notice", callback_data="admin_ff_add")],
        [InlineKeyboardButton(text="📦 Manage Packages", callback_data="admin_ff_products")],
        [InlineKeyboardButton(text=f"📋 Review Orders ({pending_count})", callback_data="admin_ff_orders")],
        [InlineKeyboardButton(text="✏️ Edit Menu Name/Emoji", callback_data="admin_ff_edit_label")],
        [InlineKeyboardButton(text="🌍 Manage Regions / Emojis", callback_data="admin_ff_regions")],
        [InlineKeyboardButton(text="💳 Set UPI Instructions", callback_data="admin_ff_upi")],
        [InlineKeyboardButton(text="⬅️ Back to Admin", callback_data="admin_panel_back")]])
    await call.message.edit_text(
        f"{html.escape(get_setting('ff_like_emoji', '🔥'))} <b>{html.escape(get_setting('ff_like_label', 'FF Like'))} — Manual Order System</b>\n\n"
        "No provider API is used for FF Likes. Add packages with your own title, description, price and notice. Users submit their UID, profile screenshot, region and payment; you approve or reject each order here. Rejected orders are refunded to the bot wallet (including UPI orders, where the refund is wallet credit rather than an external UPI transfer).",
        reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_ff_toggle")
async def admin_ff_toggle(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    new="OFF" if (get_setting("ff_like_enabled", "OFF") or "OFF").upper()=="ON" else "ON"
    set_setting("ff_like_enabled",new)
    await admin_ff_menu(call, None)

@dp.callback_query(F.data == "admin_ff_add")
async def admin_ff_add(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.ff_add_title)
    await call.message.answer("Send FF Like product title:")
    await call.answer()

@dp.message(AdminStates.ff_add_title)
async def admin_ff_add_title(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    title=(message.html_text or message.text or "").strip()
    if not title or len(title)>100: return await message.answer("Title must be 1–100 characters. Try again:")
    await state.update_data(ff_title=title); await state.set_state(AdminStates.ff_add_description)
    await message.answer("Send product description (or send - to skip):")

@dp.message(AdminStates.ff_add_description)
async def admin_ff_add_description(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    raw_description=(message.html_text or message.text or "").strip()
    await state.update_data(ff_description="" if raw_description=="-" else raw_description[:3000])
    await state.set_state(AdminStates.ff_add_notice); await message.answer("Send the product notice shown to users after they click this product. Telegram formatting (bold/code/spoiler) is preserved. Send - to skip:")

@dp.message(AdminStates.ff_add_notice)
async def admin_ff_add_notice(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    raw_notice=(message.html_text or message.text or "").strip()
    await state.update_data(ff_notice="" if raw_notice=="-" else raw_notice[:3000])
    await state.set_state(AdminStates.ff_add_price)
    await message.answer("Send product price in INR (example: 20):")

@dp.message(AdminStates.ff_add_price)
async def admin_ff_add_price(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    try: price=float((message.text or "").strip().replace("₹", ""))
    except ValueError: return await message.answer("Enter a valid numeric price, for example 25:")
    if price<=0 or price>1000000: return await message.answer("Price must be greater than ₹0 and not exceed ₹10,00,000.")
    data=await state.get_data()
    db_query("INSERT INTO ff_products(title,description,price,active,created_at,product_type,duration_days,notice) VALUES(?,?,?,?,?,?,?,?)",
             (data['ff_title'],data.get('ff_description',''),price,1,datetime.now().isoformat(timespec='seconds'),'manual',0,data.get('ff_notice','')))
    await state.clear()
    await message.answer(
        f"✅ <b>FF Like package added</b>\nName: {html.escape(data['ff_title'])}\nPrice: ₹{price:g}\n\nUsers will submit UID, profile screenshot, region and payment. Orders will wait for your approval.",
        parse_mode="HTML", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ff_products")
async def admin_ff_products(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    rows=db_query("SELECT id,title,price,active FROM ff_products ORDER BY id DESC",fetchall=True) or []
    kb=[]
    for pid,title,price,active in rows:
        kb.append([InlineKeyboardButton(text=f"{'🟢' if active else '🔴'} 📦 {title[:29]} ₹{price:g}",callback_data=f"admin_ff_product_{pid}")])
    kb += [[InlineKeyboardButton(text="📋 Pending Orders",callback_data="admin_ff_orders")],[InlineKeyboardButton(text="⬅️ Back",callback_data="admin_ff_menu")]]
    await call.message.edit_text("📦 <b>FF Like Products</b>\nTap a product to toggle it on/off.",reply_markup=make_inline_kb(inline_keyboard=kb,_width=1),parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data.startswith("admin_ff_product_"))
async def admin_ff_product_toggle(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    try: pid=int(call.data.rsplit("_",1)[1])
    except ValueError: return await call.answer("Invalid product")
    row=db_query("SELECT active,title FROM ff_products WHERE id=?",(pid,),fetchone=True)
    if not row: return await call.answer("Product not found",show_alert=True)
    db_query("UPDATE ff_products SET active=? WHERE id=?",(0 if row[0] else 1,pid))
    await admin_ff_products(call)

@dp.callback_query(F.data == "admin_ff_edit_label")
async def admin_ff_edit_label(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.ff_edit_label)
    await call.message.answer("Send the menu label and emoji separated by | (example: FF Likes | 🔥). Use a single short emoji and a label up to 24 characters.")
    await call.answer()

@dp.message(AdminStates.ff_edit_label)
async def admin_ff_edit_label_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    raw=(message.text or "").strip()
    if "|" not in raw: return await message.answer("Format: FF Likes | 🔥")
    label,emoji=[x.strip() for x in raw.split("|",1)]
    if not label or len(label)>24 or not emoji or len(emoji)>8: return await message.answer("Label must be 1–24 characters and emoji must be short. Try again.")
    set_setting("ff_like_label",label)
    set_setting("ff_like_emoji",emoji)
    await state.clear()
    await message.answer("✅ FF Like menu label and emoji updated.")

@dp.callback_query(F.data == "admin_ff_upi")
async def admin_ff_upi(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied",show_alert=True)
    await state.set_state(AdminStates.ff_edit_upi_details)
    await call.message.answer("Send UPI payment instructions to show users (UPI ID / QR instructions). These are text only; payment is manually reviewed by admin:")
    await call.answer()

@dp.message(AdminStates.ff_edit_upi_details)
async def admin_ff_upi_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    set_setting("fflike_upi_details",(message.text or "").strip()[:1500]); await state.clear()
    await message.answer("✅ FF Like UPI instructions saved.")

@dp.callback_query(F.data == "ff_menu")
async def ff_menu(call: CallbackQuery):
    if (get_setting("ff_like_enabled","OFF") or "OFF").upper()!="ON": return await call.answer("FF Like is currently unavailable.",show_alert=True)
    rows=db_query("SELECT id,title,description,price,product_type,duration_days FROM ff_products WHERE active=1 ORDER BY id",fetchall=True) or []
    if not rows: return await call.answer("No FF Like products available yet.",show_alert=True)
    buttons=[[InlineKeyboardButton(text=f"📦 {title[:35]} — ₹{price:g}",callback_data=f"ff_buy_{pid}")] for pid,title,desc,price,ptype,days in rows]
    buttons.append([InlineKeyboardButton(text="⬅️ Back to Menu",callback_data="back_main")])
    await call.message.edit_text(f"{html.escape(get_setting('ff_like_emoji', '🔥'))} <b>{html.escape(get_setting('ff_like_label', 'FF Like'))} Store</b>\nSelect a product:",reply_markup=make_inline_kb(inline_keyboard=buttons,_width=1),parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data.startswith("ff_buy_"))
async def ff_buy(call: CallbackQuery, state: FSMContext):
    if (get_setting("ff_like_enabled","OFF") or "OFF").upper()!="ON": return await call.answer("FF Like is currently unavailable.",show_alert=True)
    try: pid=int(call.data.rsplit("_",1)[1])
    except ValueError: return await call.answer("Invalid product")
    product=db_query("SELECT title,description,price,product_type,duration_days,notice FROM ff_products WHERE id=? AND active=1",(pid,),fetchone=True)
    if not product: return await call.answer("Product is unavailable",show_alert=True)
    await state.update_data(ff_product_id=pid,ff_title=product[0],ff_price=float(product[2]),ff_product_type=product[3],ff_duration_days=int(product[4] or 0))
    await state.set_state(UserStates.ff_uid)
    notice = str(product[5] or "")
    # Admin-authored Telegram HTML is retained so bold/code/spoiler formatting survives.
    notice_block = f"\n\n📢 <b>NOTICE</b>\n{notice}" if notice else ""
    await call.message.answer(f"<b>{html.escape(product[0])}</b>\n{product[1] or ''}{notice_block}\n\n💰 Price: <b>₹{float(product[2]):g}</b>\n\n1️⃣ Send your Free Fire game UID:",parse_mode="HTML")
    await call.answer()

@dp.message(UserStates.ff_uid)
async def ff_get_uid(message: Message,state:FSMContext):
    uid=(message.text or "").strip()
    if not re.fullmatch(r"[0-9]{5,24}",uid): return await message.answer("Please send a valid numeric game UID (5–24 digits):")
    await state.update_data(ff_uid=uid,ff_photo=""); await state.set_state(UserStates.ff_game_photo)
    await message.answer("🖼️ Now send a screenshot/photo of your Free Fire game profile. Make sure the UID is visible.")

@dp.message(UserStates.ff_game_photo)
async def ff_get_photo(message:Message,state:FSMContext):
    if not message.photo: return await message.answer("Please send the game profile as a photo (not text/file).")
    await state.update_data(ff_photo=message.photo[-1].file_id); await state.set_state(UserStates.ff_region)
    await message.answer("🌍 Select your region:",reply_markup=ff_regions_kb())

@dp.callback_query(F.data.startswith("ff_region_"))
async def ff_choose_region(call:CallbackQuery,state:FSMContext):
    await call.answer("Region selected")
    region_code=call.data[len("ff_region_"):]
    region_list=_load_region_settings("ff_like_regions_json", [])
    selected=next((r for r in region_list if str(r.get("code", "")).lower() == region_code.lower()), None)
    if not selected: return await call.answer("Region was removed or is invalid. Start again.", show_alert=True)
    region=f"{selected.get('emoji','🌍')} {selected.get('name',region_code)}"
    data=await state.get_data()
    if not data.get("ff_product_id") or not data.get("ff_uid"):
        await state.clear(); return await call.answer("Session expired. Open FF Like again.",show_alert=True)
    await state.update_data(ff_region=region_code, ff_region_label=region); await state.set_state(UserStates.ff_payment)
    kb=make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="👛 Pay from Wallet",callback_data="ff_pay_wallet")],[InlineKeyboardButton(text="📲 Pay by UPI",callback_data="ff_pay_upi")],[InlineKeyboardButton(text="Cancel",callback_data="ff_cancel")]],_width=1)
    await call.message.answer(f"🌍 Region: <b>{html.escape(region)}</b>\n🧾 Order will be reviewed by admin\nAmount: <b>₹{float(data['ff_price']):g}</b>\nChoose payment method:",reply_markup=kb,parse_mode="HTML")

async def ff_create_order(message:Message, data:dict, method:str, proof:str=""):
    now=datetime.now().isoformat(timespec="seconds")
    # Persist and obtain the exact order ID atomically, even if the user double-submits.
    conn=sqlite3.connect(DB_PATH,timeout=30.0)
    try:
        cur=conn.execute("INSERT INTO ff_orders(user_id,product_id,product_title,price,game_uid,game_photo_id,region,payment_method,proof_file_id,status,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",
                         (message.from_user.id,data['ff_product_id'],data['ff_title'],float(data['ff_price']),data['ff_uid'],data['ff_photo'],data['ff_region_label'],method,proof,"pending",now,now))
        oid=int(cur.lastrowid)
        conn.commit()
    finally:
        conn.close()
    admin_kb_rows=[[InlineKeyboardButton(text="✅ Approve / Mark Successful",callback_data=f"admin_ff_confirm_{oid}"),InlineKeyboardButton(text="❌ Reject + Refund",callback_data=f"admin_ff_reject_{oid}")]]
    admin_text=(
        f"🔥 <b>NEW FF LIKE ORDER #{oid}</b>\nUser: <code>{message.from_user.id}</code>\n"
        f"Package: {html.escape(str(data['ff_title']))}\nAmount: ₹{float(data['ff_price']):g}\n"
        f"UID: <code>{html.escape(str(data['ff_uid']))}</code>\nRegion: {html.escape(str(data['ff_region_label']))}\n"
        f"Payment: {html.escape(method)}\nStatus: <b>WAITING FOR ADMIN REVIEW</b>\n"
        "Check the profile screenshot and payment proof before approving."
    )
    for aid in getattr(ADMIN_ID,"all_ids",{int(ADMIN_ID)}):
        try:
            await bot.send_message(int(aid),admin_text,reply_markup=make_inline_kb(inline_keyboard=admin_kb_rows),parse_mode="HTML")
            if data.get('ff_photo'): await bot.send_photo(int(aid),data['ff_photo'],caption=f"🖼️ Game profile screenshot — FF order #{oid}")
            if proof: await bot.send_photo(int(aid),proof,caption=f"🧾 UPI payment proof — FF order #{oid}")
        except Exception as exc: logger.warning("FF order admin notification failed: %s",type(exc).__name__)
    await message.answer(
        f"⏳ <b>Order Submitted for Review</b>\nOrder ID: <code>#{oid}</code>\nPackage: {html.escape(str(data['ff_title']))}\n"
        f"Amount: ₹{float(data['ff_price']):g}\nPayment: {html.escape(method)}\n\n"
        "Please wait a few hours while the admin checks your UID, profile screenshot and payment. You will receive a message when the order is approved or rejected. Do not submit the same order again.",
        parse_mode="HTML")

@dp.callback_query(F.data == "ff_pay_wallet")
async def ff_pay_wallet(call:CallbackQuery,state:FSMContext):
    try:
        data=await state.get_data()
        if not data.get("ff_product_id"):
            return await call.answer("Session expired. Open FF Like again.",show_alert=True)
        try:
            price=float(data.get("ff_price", 0))
        except (TypeError, ValueError):
            logger.error("FF wallet callback has invalid price user_id=%s data_keys=%s", call.from_user.id, sorted(data.keys()))
            return await call.answer("Invalid product price. Please contact admin.",show_alert=True)
        if price <= 0:
            return await call.answer("This product price is invalid. Contact admin.",show_alert=True)
        # Atomic debit prevents double-taps and concurrent purchases spending the same balance.
        conn=sqlite3.connect(DB_PATH, timeout=30.0)
        try:
            conn.execute("BEGIN IMMEDIATE")
            row=conn.execute("SELECT balance FROM users WHERE user_id=?",(call.from_user.id,)).fetchone()
            if not row:
                conn.rollback()
                return await call.answer("User account not found. Send /start first.",show_alert=True)
            if float(row[0] or 0) < price:
                conn.rollback()
                return await call.answer("Insufficient wallet balance. Choose UPI or add balance.",show_alert=True)
            cur=conn.execute("UPDATE users SET balance=balance-? WHERE user_id=? AND balance>=?",(price,call.from_user.id,price))
            if cur.rowcount != 1:
                conn.rollback()
                return await call.answer("Wallet balance changed. Please try again.",show_alert=True)
            conn.commit()
        finally:
            conn.close()
        await state.clear()
        fake=SimpleNamespace(from_user=call.from_user,answer=call.message.answer)
        try:
            await ff_create_order(fake,data,"Wallet (deducted)")
        except Exception:
            # Restore wallet if local order creation itself raises before it can be recorded.
            logger.exception("FF wallet order creation failed after debit; refunding user_id=%s",call.from_user.id)
            db_query("UPDATE users SET balance=balance+? WHERE user_id=?",(price,call.from_user.id))
            await call.answer("Order creation failed locally; wallet amount was restored.",show_alert=True)
            return
        await call.answer("Wallet payment recorded")
    except Exception as exc:
        logger.exception(
            "FF_PAY_WALLET CALLBACK FAILED user_id=%s callback_data=%r message_id=%s",
            getattr(getattr(call, "from_user", None), "id", None),
            getattr(call, "data", None),
            getattr(getattr(call, "message", None), "message_id", None),
        )
        try:
            await call.answer(
                "Wallet order hit an internal error. Check order history before retrying; contact admin if balance changed.",
                show_alert=True
            )
        except Exception:
            logger.debug("Could not answer failed FF wallet callback: %s", exc)

@dp.callback_query(F.data == "ff_pay_upi")
async def ff_pay_upi(call:CallbackQuery,state:FSMContext):
    data=await state.get_data()
    if not data.get("ff_product_id"): return await call.answer("Session expired",show_alert=True)
    rows=[]
    if gateway_enabled("zapupi") and (db_query("SELECT value FROM settings WHERE key='zapupi_api'",fetchone=True) or ("",))[0]:
        rows.append([InlineKeyboardButton(text="⚡ Pay with ZapUPI",callback_data="ff_pay_zapupi")])
    if gateway_enabled("famgateway") and _famgateway_api_key():
        rows.append([InlineKeyboardButton(text="💜 Pay with FamGateway",callback_data="ff_pay_famgateway")])
    if not rows:
        return await call.answer("No UPI gateway is configured/enabled. Ask admin to configure ZapUPI or FamGateway.",show_alert=True)
    rows.append([InlineKeyboardButton(text="⬅️ Back",callback_data="ff_cancel")])
    await call.message.answer(f"📲 <b>Choose UPI Gateway</b>\nAmount: <b>₹{float(data['ff_price']):g}</b>\nPayment will be verified by gateway; no separate/manual QR is used.",reply_markup=make_inline_kb(inline_keyboard=rows),parse_mode="HTML")
    await call.answer()

async def _fflike_gateway_checkout(call: CallbackQuery, state: FSMContext, gateway: str):
    data=await state.get_data()
    required=("ff_product_id","ff_title","ff_price","ff_uid","ff_photo","ff_region_label")
    if any(k not in data for k in required): return await call.answer("Session expired. Start FF Like again.",show_alert=True)
    meta={k:data.get(k) for k in required}
    desc=json.dumps(meta,ensure_ascii=False,separators=(",",":"))
    amount=float(data["ff_price"])
    await call.answer()
    try:
        await call.message.answer(f"⏳ Creating {gateway.upper()} payment for FF Like — ₹{amount:g}…")
        if gateway == "famgateway":
            await create_famgateway_payment(call.from_user.id,amount,call.message,purpose="ff_like_purchase",description=desc)
        else:
            await generate_zapupi_order(call.from_user.id,amount,call.message,purpose="ff_like_purchase",description=desc)
    except Exception:
        logger.exception("FF Like gateway checkout failed")
        await call.message.answer("❌ Could not create UPI payment. Please try again later.")

@dp.callback_query(F.data == "ff_pay_zapupi")
async def ff_pay_zapupi(call:CallbackQuery,state:FSMContext):
    await _fflike_gateway_checkout(call,state,"zapupi")

@dp.callback_query(F.data == "ff_pay_famgateway")
async def ff_pay_famgateway(call:CallbackQuery,state:FSMContext):
    await _fflike_gateway_checkout(call,state,"famgateway")

@dp.message(UserStates.ff_upi_proof)
async def ff_upi_proof(message:Message,state:FSMContext):
    if not message.photo: return await message.answer("Send the UPI payment screenshot as a photo.")
    data=await state.get_data(); proof=message.photo[-1].file_id
    await state.clear(); await ff_create_order(message,data,"UPI (manual verification)",proof)

@dp.callback_query(F.data == "ff_cancel")
async def ff_cancel(call:CallbackQuery,state:FSMContext):
    await state.clear(); await call.answer("Cancelled")
    try: await call.message.edit_text("FF Like order cancelled.")
    except Exception: pass

@dp.callback_query(F.data.startswith("admin_ff_confirm_"))
async def admin_ff_confirm(call:CallbackQuery, state:FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied",show_alert=True)
    try: oid=int(call.data.rsplit("_",1)[1])
    except ValueError: return await call.answer("Invalid order",show_alert=True)
    row=db_query("SELECT user_id,product_title,price,status,game_uid FROM ff_orders WHERE id=?",(oid,),fetchone=True)
    if not row: return await call.answer("Order not found",show_alert=True)
    if str(row[3]).lower() != "pending": return await call.answer(f"Order is already {row[3]}; no change made.",show_alert=True)
    await state.set_state(AdminStates.wait_ff_like_success_txt)
    await state.update_data(ff_like_confirm_order_id=oid)
    await call.message.answer(
        f"Send the success TXT/message for FF Like order #{oid}. You can write the UID, likes delivered and any details.\n\n"
        f"Example:\n✅ Order Successful\nUID: {html.escape(str(row[4] or ''))}\nLikes sent: 1000\n\n"
        "Send /cancel to stop. The order will only be marked completed after you send the message.", parse_mode="HTML")
    await call.answer("Waiting for success TXT")

@dp.message(AdminStates.wait_ff_like_success_txt)
async def admin_ff_like_success_txt(message:Message, state:FSMContext):
    if not is_admin(message.from_user.id): return
    if (message.text or "").strip().lower() == "/cancel":
        await state.clear(); return await message.answer("FF Like confirmation cancelled; order remains pending.", reply_markup=admin_kb())
    data=await state.get_data(); oid=int(data.get("ff_like_confirm_order_id", 0) or 0)
    row=db_query("SELECT user_id,product_title,price,status,game_uid FROM ff_orders WHERE id=?",(oid,),fetchone=True)
    if not row or str(row[3]).lower() != "pending":
        await state.clear(); return await message.answer("Order not found or no longer pending. No status changed.", reply_markup=admin_kb())
    txt=(message.text or message.caption or "").strip()
    if not txt and message.document:
        try:
            file=await bot.get_file(message.document.file_id)
            import tempfile
            with tempfile.NamedTemporaryFile(suffix=".txt", delete=False) as tmp: tmp_path=tmp.name
            await bot.download_file(file.file_path, destination=tmp_path)
            with open(tmp_path,"r",encoding="utf-8",errors="replace") as fh: txt=fh.read().strip()
            os.unlink(tmp_path)
        except Exception: txt=""
    if not txt:
        return await message.answer("Please send the confirmation text or a .txt file. Nothing has been approved yet.")
    now=datetime.now().isoformat(timespec="seconds")
    conn=sqlite3.connect(DB_PATH,timeout=30.0)
    try:
        conn.execute("BEGIN IMMEDIATE")
        cur=conn.execute("UPDATE ff_orders SET status='completed',provider_status='admin_approved',provider_response=?,updated_at=? WHERE id=? AND status='pending'",(txt[:4000],now,oid))
        if cur.rowcount != 1:
            conn.rollback(); await state.clear(); return await message.answer("Order status changed elsewhere; no duplicate notification sent.")
        conn.commit()
    except Exception:
        conn.rollback(); raise
    finally: conn.close()
    try:
        await bot.send_message(int(row[0]), f"✅ <b>Your FF Like Order Is Successful!</b>\nOrder ID: <code>#{oid}</code>\nPackage: {html.escape(str(row[1]))}\nAmount: ₹{float(row[2]):g}\n\n<pre>{html.escape(txt[:3500])}</pre>", parse_mode="HTML")
    except Exception as exc: logger.warning("FF order success notification failed: %s",type(exc).__name__)
    await state.clear()
    await message.answer(f"Order #{oid} marked completed and TXT sent to user.", reply_markup=admin_kb())

@dp.callback_query(F.data.startswith("admin_ff_reject_"))
async def admin_ff_reject(call:CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied",show_alert=True)
    try: oid=int(call.data.rsplit("_",1)[1])
    except ValueError: return await call.answer("Invalid order",show_alert=True)
    row=db_query("SELECT user_id,product_title,price,payment_method,status FROM ff_orders WHERE id=?",(oid,),fetchone=True)
    if not row: return await call.answer("Order not found",show_alert=True)
    if str(row[4]).lower() != "pending":
        return await call.answer(f"Order is already {row[4]}; no duplicate refund was issued.",show_alert=True)
    conn=sqlite3.connect(DB_PATH,timeout=30.0)
    try:
        conn.execute("BEGIN IMMEDIATE")
        cur=conn.execute("UPDATE ff_orders SET status='rejected',provider_status='admin_rejected_refunded_to_wallet',updated_at=? WHERE id=? AND status='pending'",(datetime.now().isoformat(timespec="seconds"),oid))
        if cur.rowcount != 1:
            conn.rollback(); return await call.answer("Order status changed; no refund was issued. Refresh order status.",show_alert=True)
        # Credit the bot wallet once for every rejected paid order. For UPI payments this is a wallet credit, not an external UPI transfer.
        conn.execute("UPDATE users SET balance=COALESCE(balance,0)+? WHERE user_id=?",(float(row[2]),int(row[0])))
        conn.commit()
    except Exception:
        conn.rollback(); raise
    finally: conn.close()
    try:
        await bot.send_message(int(row[0]),
            f"❌ <b>Your FF Like Order Was Cancelled by Admin</b>\nOrder ID: <code>#{oid}</code>\nPackage: {html.escape(str(row[1]))}\n\n"
            f"💰 Refund: ₹{float(row[2]):g} has been credited to your bot wallet. You can check your wallet balance in the bot.",parse_mode="HTML")
    except Exception as exc: logger.warning("FF order refund notification failed: %s",type(exc).__name__)
    try: await call.message.edit_reply_markup(reply_markup=None)
    except Exception: pass
    await call.answer("Order rejected; refund credited to bot wallet")

@dp.callback_query(F.data == "admin_ff_orders")
async def admin_ff_orders(call:CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied",show_alert=True)
    rows=db_query("SELECT id,user_id,product_title,price,status,game_uid,region,payment_method,game_photo_id,proof_file_id FROM ff_orders WHERE status='pending' ORDER BY id DESC LIMIT 30",fetchall=True) or []
    if not rows: return await call.answer("No pending FF Like orders",show_alert=True)
    await call.answer()
    for r in rows:
        oid,user_id,title,price,status,uid,region,method,photo,proof=r
        text=(f"📋 <b>FF Likes Order #{oid}</b>\nPackage: {html.escape(str(title))}\nAmount: ₹{float(price):g}\n"
              f"User: <code>{user_id}</code>\nUID: <code>{html.escape(str(uid))}</code>\nRegion: {html.escape(str(region))}\n"
              f"Payment: {html.escape(str(method))}\nStatus: <b>{html.escape(str(status))}</b>")
        kb=make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="✅ Approve / Successful",callback_data=f"admin_ff_confirm_{oid}"),InlineKeyboardButton(text="❌ Reject + Refund",callback_data=f"admin_ff_reject_{oid}")]],_width=1)
        await call.message.answer(text,reply_markup=kb,parse_mode="HTML")
        if photo: await call.message.answer_photo(photo,caption=f"🖼️ Game profile screenshot — order #{oid}")
        if proof: await call.message.answer_photo(proof,caption=f"🧾 UPI payment proof — order #{oid}")

@dp.callback_query(F.data == "admin_referral_percent")
async def admin_referral_percent(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    current = get_setting("referral_commission_percent", "15") or "15"
    await call.message.answer(
        f"Current referral commission: <b>{html.escape(str(current))}%</b>\n"
        "Send a percentage from 0 to 100.",
        reply_markup=admin_back_kb(), parse_mode="HTML"
    )
    await state.set_state(AdminStates.wait_for_referral_percent)
    await call.answer()

@dp.message(AdminStates.wait_for_referral_percent)
async def admin_referral_percent_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id):
        return
    try:
        value = float((message.text or "").strip().replace("%", ""))
        if not 0 <= value <= 100:
            raise ValueError
    except ValueError:
        return await message.answer("Enter a valid percentage from 0 to 100, e.g. 5 or 12.5.")
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", ("referral_commission_percent", str(value)))
    await message.answer(f"✅ Referral commission updated to {value:g}%.")
    await state.clear()


# 10. ONBOARDING & START
# ==============================================================================
def bot_username_clean() -> str:
    return str(BOT_USERNAME or "").lstrip("@").strip()

def product_deep_link(prod_id: int) -> str:
    username = bot_username_clean()
    return f"https://t.me/{username}?start=product_{int(prod_id)}"

def product_share_url(prod_id: int, title: str = "") -> str:
    deep = product_deep_link(prod_id)
    share_text = f"🛒 {title}" if title else "🛒 Check this product"
    return "https://t.me/share/url?" + urllib.parse.urlencode({"url": deep, "text": share_text})

async def send_product_deep_link_menu(message: Message, prod_id: int) -> bool:
    row = db_query("""
        SELECT id, name, price_inr, stock, reseller_price, validity, device_limit,
               external_enabled, COALESCE(is_maintenance,0), category, panel_name
        FROM products WHERE id=? AND is_active=1
    """, (prod_id,), fetchone=True)
    if not row:
        await message.answer("❌ This product is no longer available.", reply_markup=main_menu_kb(message.from_user.id), parse_mode="HTML")
        return False
    user = db_query("SELECT is_reseller, is_vip FROM users WHERE user_id=?", (message.from_user.id,), fetchone=True)
    is_reseller = bool(user[0]) if user else False
    is_vip = bool(user[1]) if user else False
    _, name, price, stock, reseller_price, validity, device, external_enabled, maintenance, category, panel = row
    base = float(reseller_price or 0) if is_reseller else float(price or 0)
    display = base - (base * VIP_DISCOUNT_PERCENTAGE / 100) if is_vip else base
    if maintenance:
        status = "🟠 Under Maintenance"
    elif external_enabled:
        status = "♾️ API Available"
    elif int(stock or 0) > 0:
        status = f"✅ In Stock: {int(stock)}"
    else:
        status = "❌ Out of Stock"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"🛒 Buy {validity} — {fmt_curr(display)}", callback_data=f"buy_{prod_id}")],
        [InlineKeyboardButton(text="🏪 Open Product Store", callback_data="menu_shop")],
    ])
    await message.answer(
        f"🛍️ <b>PRODUCT</b>\n━━━━━━━━━━━━━━━━━━\n"
        f"📦 <b>{name}</b>\n"
        f"🏷️ Panel: <b>{panel or 'Main Store'}</b>\n"
        f"📁 Category: <b>{category or 'Product'}</b>\n"
        f"⏳ Validity: <b>{validity}</b>\n"
        f"📱 Device Limit: <b>{device}</b>\n"
        f"📦 Status: <b>{status}</b>\n"
        f"💰 Price: <b>{fmt_curr(display)}</b>\n\n"
        f"👇 <b>Tap Buy to open the complete purchase menu.</b>",
        reply_markup=kb, parse_mode="HTML"
    )
    return True

@dp.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext):
    await state.clear()
    if WELCOME_STICKER_ID and "..." not in WELCOME_STICKER_ID and len(WELCOME_STICKER_ID) > 20:
        try: await message.answer_sticker(WELCOME_STICKER_ID)
        except Exception: pass 
    
    args = message.text.split()
    if len(args) > 1 and args[1].startswith("v_"):
        order_id = args[1].split("v_")[1]
        msg = await message.answer("🔄 <b>Verifying your payment securely...</b>\n<i>Connecting to gateway...</i>", parse_mode='HTML')
        await run_payment_verification(message.from_user.id, order_id, msg)
        return

    # Product share/deep-link: /start product_<id> opens that exact product menu.
    if len(args) > 1 and args[1].startswith("product_"):
        try:
            shared_prod_id = int(args[1].split("product_", 1)[1])
        except (TypeError, ValueError):
            shared_prod_id = 0
        if shared_prod_id > 0:
            user_exists = db_query("SELECT user_id FROM users WHERE user_id=?", (message.from_user.id,), fetchone=True)
            if not user_exists:
                db_query("INSERT OR IGNORE INTO users (user_id, first_name, username, joined_date) VALUES (?, ?, ?, ?)",
                         (message.from_user.id, message.from_user.first_name, message.from_user.username or "", datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
            else:
                db_query("UPDATE users SET username=? WHERE user_id=?", (message.from_user.username or "", message.from_user.id))
            await send_product_deep_link_menu(message, shared_prod_id)
            return

    referred_by = None
    if len(args) > 1 and args[1].startswith("ref_"):
        try: referred_by = int(args[1].split("_")[1])
        except: pass

    user = db_query("SELECT user_id FROM users WHERE user_id=?", (message.from_user.id,), fetchone=True)
    current_username = message.from_user.username or ""

    if not user:
        db_query("INSERT OR IGNORE INTO users (user_id, first_name, username, referred_by, joined_date) VALUES (?, ?, ?, ?, ?)", 
                 (message.from_user.id, message.from_user.first_name, current_username, referred_by, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
        log_activity(message.from_user.id, "ACCOUNT_CREATED")
        if referred_by:
            db_query("UPDATE users SET referrals_count = referrals_count + 1 WHERE user_id=?", (referred_by,))
            try:
                await bot.send_message(referred_by, f"🎉 <b>Referral Success!</b>\nUser <b>{message.from_user.first_name}</b> joined using your link!", parse_mode='HTML')
            except Exception:
                pass
    else:
        db_query("UPDATE users SET username=? WHERE user_id=?", (current_username, message.from_user.id))
        log_activity(message.from_user.id, "CMD_START")

    text = get_ui_text("start_menu")
    kb = main_menu_kb(message.from_user.id)
    await message.answer(text, reply_markup=kb, parse_mode='HTML')

@dp.message(F.contact)
async def handle_contact(message: Message):
    if message.contact.user_id == message.from_user.id:
        db_query("UPDATE users SET phone=? WHERE user_id=?", (message.contact.phone_number, message.from_user.id))
        referrer = db_query("SELECT referred_by FROM users WHERE user_id=?", (message.from_user.id,), fetchone=True)
        if referrer and referrer[0]:
            db_query("UPDATE users SET referrals_count = referrals_count + 1 WHERE user_id=?", (referrer[0],))
            try: await bot.send_message(referrer[0], f"🎉 <b>Referral Success!</b>\nUser <b>{message.from_user.first_name}</b> joined using your link!", parse_mode='HTML')
            except: pass
        log_activity(message.from_user.id, "CONTACT_VERIFIED")
        await message.answer("✅ Verification successful! Welcome to the system.", reply_markup=ReplyKeyboardRemove())
        await send_main_menu(message)
    else:
        await message.answer("❌ Security Alert: Please share your OWN contact using the provided button.")

async def send_main_menu(ctx: Any):
    text = get_ui_text("start_menu")
    kb = main_menu_kb(ctx.from_user.id)
    if isinstance(ctx, Message): 
        await ctx.answer(text, reply_markup=kb, parse_mode='HTML')
    else: 
        await ctx.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "back_main")
async def back_main(call: CallbackQuery, state: FSMContext):
    await state.clear()
    log_activity(call.from_user.id, "RETURN_MAIN_MENU")
    await send_main_menu(call)

# ==============================================================================
# 11. ADD BALANCE
# ==============================================================================
@dp.callback_query(F.data == "menu_add_balance")
async def select_gateway_menu(call: CallbackQuery, state: FSMContext):
    # Cancel any in-progress deposit flow (including Binance QR screenshot/TxID states).
    await state.clear()
    log_activity(call.from_user.id, "VIEW_ADD_BALANCE")
    text = get_ui_text("add_balance_menu")
    rows = []
    if gateway_enabled("zapupi"):
        rows.append([InlineKeyboardButton(text="UPI PAY", callback_data="gateway_inr", icon_custom_emoji_id=get_emoji_icon("upi"))])
    if gateway_enabled("famgateway") and _famgateway_api_key():
        rows.append([InlineKeyboardButton(text="FAMGATEWAY", callback_data="gateway_famgateway", icon_custom_emoji_id=get_emoji_icon("money_icon"))])
    rows.append([InlineKeyboardButton(text="BINANCE PAY", callback_data="gateway_crypto", icon_custom_emoji_id=get_emoji_icon("binance"))])
    rows.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))])
    kb = make_inline_kb(inline_keyboard=rows)
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
    except Exception:
        # Binance QR is a photo message; Telegram cannot edit its text body.
        try:
            await call.message.edit_caption(caption=text, reply_markup=kb, parse_mode='HTML')
        except Exception:
            await call.message.answer(text, reply_markup=kb, parse_mode='HTML')

# ==============================================================================
# 12. UPI & CRYPTO PAYMENT FLOWS
# ==============================================================================
@dp.callback_query(F.data == "gateway_inr")
async def add_balance_inr(call: CallbackQuery):
    if not gateway_enabled("zapupi"):
        return await call.answer("⚠️ ZapUPI is currently OFF by Admin.", show_alert=True)
    text = f"💵 <b>— ZAPUPI DEPOSIT —</b> 💵\n\nSelect amount to deposit:"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="50", callback_data="pay_50", icon_custom_emoji_id=get_emoji_icon("money_icon")), 
         InlineKeyboardButton(text="100", callback_data="pay_100", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text="200", callback_data="pay_200", icon_custom_emoji_id=get_emoji_icon("money_icon")), 
         InlineKeyboardButton(text="500", callback_data="pay_500", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text="Custom Amount", callback_data="custom_deposit_keypad", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Back", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "gateway_famgateway")
async def add_balance_famgateway(call: CallbackQuery):
    if not gateway_enabled("famgateway"):
        return await call.answer("⚠️ FamGateway is currently OFF by Admin.", show_alert=True)
    if not _famgateway_api_key():
        return await call.answer("⚠️ FamGateway is not configured by admin yet.", show_alert=True)
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="₹50", callback_data="fam_pay_50"), InlineKeyboardButton(text="₹100", callback_data="fam_pay_100")],
        [InlineKeyboardButton(text="₹200", callback_data="fam_pay_200"), InlineKeyboardButton(text="₹500", callback_data="fam_pay_500")],
        [InlineKeyboardButton(text="Custom Amount", callback_data="fam_custom_deposit")],
        [InlineKeyboardButton(text="Back", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text("💜 <b>FAMGATEWAY UPI</b>\n\nSelect amount to deposit:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("fam_pay_"))
async def famgateway_fixed_payment(call: CallbackQuery):
    if _callback_is_on_cooldown((call.from_user.id, "fam_pay")):
        return await call.answer("⏳ Please wait 3 seconds before creating another payment.", show_alert=True)
    amount = float(call.data.split("_")[-1])
    await create_famgateway_payment(call.from_user.id, amount, call.message)

@dp.callback_query(F.data == "fam_custom_deposit")
async def famgateway_custom_payment(call: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.custom_amount_input)
    await state.update_data(amount_str="0", payment_gateway="famgateway")
    await show_keypad(call.message, "0")

@dp.callback_query(F.data == "custom_deposit_keypad")
async def show_custom_keypad(call: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.custom_amount_input)
    await state.update_data(amount_str="0")
    await show_keypad(call.message)

async def show_keypad(message: Message, amount_str: str = "0"):
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="      1      ", callback_data="kp_1"), InlineKeyboardButton(text="      2      ", callback_data="kp_2"), InlineKeyboardButton(text="      3      ", callback_data="kp_3")],
        [InlineKeyboardButton(text="      4      ", callback_data="kp_4"), InlineKeyboardButton(text="      5      ", callback_data="kp_5"), InlineKeyboardButton(text="      6      ", callback_data="kp_6")],
        [InlineKeyboardButton(text="      7      ", callback_data="kp_7"), InlineKeyboardButton(text="      8      ", callback_data="kp_8"), InlineKeyboardButton(text="      9      ", callback_data="kp_9")],
        [InlineKeyboardButton(text="    ⌫    ", callback_data="kp_backspace"), InlineKeyboardButton(text="      0      ", callback_data="kp_0"), InlineKeyboardButton(text="    C    ", callback_data="kp_clear")],
        [InlineKeyboardButton(text=f"✅ Confirm (₹{amount_str})", callback_data="kp_confirm", icon_custom_emoji_id=get_emoji_icon("check_icon"))],
        [InlineKeyboardButton(text="Cancel", callback_data="gateway_inr", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    text = f"💵 <b>Enter Amount (₹):</b>\n\nCurrent: ₹{amount_str}"
    await message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("kp_"), UserStates.custom_amount_input)
async def keypad_handler(call: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    amount_str = data.get("amount_str", "0")
    action = call.data.split("_")[1]
    if action == "confirm":
        if amount_str == "0":
            await call.answer("Amount cannot be zero.", show_alert=True)
            return
        try:
            amount = float(amount_str)
            if amount < 10:
                await call.answer("Minimum deposit is ₹1.", show_alert=True)
                return
            gateway = data.get("payment_gateway", "zapupi")
            await state.clear()
            await call.message.edit_text("⏳ <b>Generating Secure Link...</b>", parse_mode='HTML')
            if gateway == "famgateway":
                await create_famgateway_payment(call.from_user.id, amount, call.message)
            else:
                await generate_zapupi_order(call.from_user.id, amount, call.message)
        except ValueError:
            await call.answer("Invalid amount.", show_alert=True)
        return
    if action == "backspace":
        if len(amount_str) > 1: amount_str = amount_str[:-1]
        else: amount_str = "0"
    elif action == "clear":
        amount_str = "0"
    else:
        if amount_str == "0": amount_str = action
        else: amount_str += action
        if len(amount_str) > 6: amount_str = amount_str[:6]
    await state.update_data(amount_str=amount_str)
    await show_keypad(call.message, amount_str)
    await call.answer()

@dp.callback_query(F.data.startswith("pay_"))
async def process_zapupi_payment_callback(call: CallbackQuery):
    inr_amount = float(call.data.split("_")[1])
    await call.message.edit_text("⏳ <b>Generating Secure Link via ZapUPI...</b>", parse_mode='HTML')
    await generate_zapupi_order(call.from_user.id, inr_amount, call.message)

async def _send_payment_qr_in_bot(message_obj: Message, payment_url: str, amount: float, order_id: str, gateway_name: str) -> bool:
    """Render the provider checkout URL as a QR image inside Telegram.

    This keeps a visible external checkout button out of the chat. The QR still
    encodes the provider URL; true native UPI QR requires the provider to return
    a UPI intent/UPI QR payload and cannot be inferred from a checkout URL.
    """
    try:
        import qrcode
        from io import BytesIO
        qr = qrcode.QRCode(version=None, box_size=8, border=3)
        qr.add_data(payment_url)
        qr.make(fit=True)
        image = qr.make_image(fill_color="black", back_color="white")
        buffer = BytesIO()
        image.save(buffer, format="PNG")
        buffer.seek(0)
        await message_obj.answer_photo(
            BufferedInputFile(buffer.getvalue(), filename=f"payment_{order_id}.png"),
            caption=(f"💳 <b>{html.escape(gateway_name)} Payment QR</b>\n"
                     f"💰 Amount: <b>₹{amount:.2f}</b>\n"
                     f"🧾 Order: <code>{html.escape(order_id)}</code>\n\n"
                     "Scan the QR to continue. After paying, tap Verify Payment.\n"
                     "⏳ Payment expires in 5 minutes."),
            reply_markup=make_inline_kb(inline_keyboard=[
                [InlineKeyboardButton(text="✅ Verify Payment", callback_data=f"verify_{order_id}", icon_custom_emoji_id=get_emoji_icon("check_icon"))],
                [InlineKeyboardButton(text="❌ Cancel", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"))]
            ]),
            parse_mode="HTML"
        )
        return True
    except Exception:
        logger.exception("Could not render in-bot payment QR for order %s", order_id)
        try:
            await message_obj.answer(
                f"⚠️ <b>QR image could not be generated.</b>\nUse the secure payment link below instead.\n\n"
                f"<a href=\"{html.escape(payment_url, quote=True)}\">Open {html.escape(gateway_name)} Payment</a>\n"
                f"Order: <code>{html.escape(str(order_id))}</code>\nAmount: <b>₹{amount:.2f}</b>",
                reply_markup=make_inline_kb(inline_keyboard=[
                    [InlineKeyboardButton(text="Open Payment Link", url=payment_url)],
                    [InlineKeyboardButton(text="Verify Payment", callback_data=f"verify_{order_id}")],
                    [InlineKeyboardButton(text="Cancel", callback_data="menu_add_balance")]
                ]), parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            logger.exception("Could not send fallback payment link for order %s", order_id)
        return False

def _pending_payment_for_user(user_id: int):
    """Return one live pending payment; expire stale orders so a user cannot spam QR invoices."""
    now = int(time.time())
    rows = db_query("SELECT order_id, timestamp, gateway FROM transactions WHERE user_id=? AND status='pending' ORDER BY timestamp DESC", (user_id,), fetchall=True) or []
    for row in rows:
        order_id, created_at, gateway = row[0], int(row[1] or 0), str(row[2] or '').lower()
        ttl = 300 if gateway == 'famgateway' else 900
        if now - created_at >= ttl:
            db_query("UPDATE transactions SET status='expired' WHERE order_id=? AND status='pending'", (order_id,))
            continue
        return {"order_id": str(order_id), "gateway": gateway, "seconds_left": max(1, ttl - (now-created_at))}
    return None

async def create_famgateway_payment(user_id: int, amount: float, message_obj: Message,
                                   purpose: str = "wallet_topup", product_id: Optional[int] = None,
                                   quantity: int = 1, description: str = "") -> None:
    pending = _pending_payment_for_user(user_id)
    if pending:
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="🔎 Verify Existing Payment", callback_data=f"verify_{pending['order_id']}")],
            [InlineKeyboardButton(text="❌ Cancel Existing Payment", callback_data=f"payment_cancel_{pending['order_id']}")],
        ])
        return await message_obj.answer(f"⏳ आपके पास पहले से एक pending payment है: <code>{html.escape(pending['order_id'])}</code>\nपहले उसे Verify या Cancel करें। नया QR बनाने से spam/duplicate payment रोकने के लिए limit लगाई गई है।", reply_markup=kb, parse_mode="HTML")
    if (get_setting("gateway_famgateway_status", "ON") or "ON").upper() != "ON":
        return await message_obj.edit_text("⚠️ FamGateway payments are currently OFF. Please choose another payment method or contact admin.", reply_markup=back_kb("menu_add_balance"), parse_mode="HTML")
    if amount < 1:
        return await message_obj.edit_text("❌ Minimum deposit is ₹1.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    result = await famgateway_create_order(user_id, amount, description or "Wallet Topup")
    if result.get("status") != "success":
        return await message_obj.edit_text(f"❌ <b>FamGateway Error:</b> {html.escape(str(result.get('message','Unknown error')))}", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    order_id = str(result.get("order_id") or "")
    qr_url = str(result.get("qr_url") or "")
    payment_url = str(result.get("checkout_url") or result.get("payment_url") or "")
    upi_intent = str(result.get("upi_intent") or "")
    if not order_id or not (qr_url or payment_url):
        return await message_obj.edit_text("❌ FamGateway returned an incomplete payment response.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    current_time = int(time.time())
    db_query(
        "INSERT INTO transactions (order_id, user_id, amount_inr, status, timestamp, purpose, product_id, quantity, description, gateway) "
        "VALUES (?, ?, ?, 'pending', ?, ?, ?, ?, ?, 'famgateway')",
        (order_id, user_id, float(result.get("payable_amount") or amount), current_time, purpose, product_id, quantity, description)
    )
    invoice_label = f"🛒 <b>Direct Purchase:</b> {html.escape(description)}\n" if purpose == "product_purchase" and description else ""
    text = (f"💜 <b>FAMGATEWAY UPI PAYMENT</b>\n\n{invoice_label}"
            f"Amount: <b>₹{float(result.get('payable_amount') or amount):.2f}</b>\nOrder ID: <code>{html.escape(order_id)}</code>\n"
            "Scan the QR below. Payment will be checked automatically for up to 5 minutes.")
    # As requested, do not show an external payment-page button. Keep only
    # Verify Payment and Cancel Payment; the QR is displayed inside Telegram.
    kb_rows = [
        [InlineKeyboardButton(text="🔎 Verify Payment", callback_data=f"verify_{order_id}")],
        [InlineKeyboardButton(text="❌ Cancel Payment", callback_data=f"payment_cancel_{order_id}")],
    ]
    if not qr_url and payment_url:
        # Rare fallback if the provider does not return a QR URL: keep the
        # checkout URL copyable as plain text, without a payment-link button.
        text += f"\n\n⚠️ QR unavailable. Open this URL manually:\n<code>{html.escape(payment_url)}</code>"
    if upi_intent:
        # Telegram rejects upi:// as a button URL; show it as copyable text instead.
        text += f"\n\nUPI link (copy if needed):\n<code>{html.escape(upi_intent)}</code>"
    markup = make_inline_kb(inline_keyboard=kb_rows)
    if qr_url:
        try:
            await message_obj.delete()
        except Exception:
            pass
        try:
            await bot.send_photo(
                chat_id=user_id, photo=qr_url, caption=text,
                reply_markup=markup, parse_mode="HTML"
            )
            return
        except Exception as exc:
            logger.warning("FamGateway QR sendPhoto failed for %s: %s", order_id, exc)
    # If the image cannot be fetched by Telegram, preserve a usable in-bot message and fallback link.
    await message_obj.answer(text, reply_markup=markup, parse_mode="HTML", disable_web_page_preview=True)

@dp.callback_query(F.data.startswith("payment_cancel_"))
async def cancel_payment_order(call: CallbackQuery):
    order_id = call.data[len("payment_cancel_"):].strip()
    txn = db_query("SELECT user_id, status FROM transactions WHERE order_id=?", (order_id,), fetchone=True)
    if not txn or int(txn[0]) != int(call.from_user.id):
        return await call.answer("Order not found.", show_alert=True)
    if str(txn[1]).lower() != "pending":
        return await call.answer("This payment is already processed or expired.", show_alert=True)
    db_query("UPDATE transactions SET status='cancelled' WHERE order_id=? AND user_id=? AND status='pending'", (order_id, call.from_user.id))
    await call.answer("Payment cancelled")
    try:
        await call.message.edit_caption(caption="❌ <b>Payment cancelled.</b>", reply_markup=None, parse_mode="HTML")
    except Exception:
        try: await call.message.edit_text("❌ <b>Payment cancelled.</b>", reply_markup=back_kb("menu_add_balance"), parse_mode="HTML")
        except Exception: pass


async def generate_zapupi_order(user_id: int, inr_amount: float, message_obj: Message,
                                purpose: str = "wallet_topup", product_id: Optional[int] = None,
                                quantity: int = 1, description: str = "") -> None:
    pending = _pending_payment_for_user(user_id)
    if pending:
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="🔎 Verify Existing Payment", callback_data=f"verify_{pending['order_id']}")],
            [InlineKeyboardButton(text="❌ Cancel Existing Payment", callback_data=f"payment_cancel_{pending['order_id']}")],
        ])
        return await message_obj.answer(f"⏳ आपका एक payment पहले से pending है: <code>{html.escape(pending['order_id'])}</code>\nनया QR/payment link बनाने से पहले Verify या Cancel करें।", reply_markup=kb, parse_mode="HTML")
    api_key_check = db_query("SELECT value FROM settings WHERE key='zapupi_api'", fetchone=True)
    if not api_key_check or not api_key_check[0]:
        return await message_obj.edit_text("⚠️ ZapUPI Gateway is currently offline. Admin needs to set API Key.", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')
        
    api_key = api_key_check[0]
    current_time = int(time.time())
    order_id = f"NXT{user_id}{current_time}"
    user_phone = db_query("SELECT phone FROM users WHERE user_id=?", (user_id,), fetchone=True)
    mobile = user_phone[0] if user_phone and user_phone[0] else "9999999999"
    bot_deep_link = f"https://t.me/{bot_username_clean()}?start=v_{order_id}"
    
    db_query(
        "INSERT INTO transactions (order_id, user_id, amount_inr, status, timestamp, purpose, product_id, quantity, description, gateway) "
        "VALUES (?, ?, ?, 'pending', ?, ?, ?, ?, ?, 'zapupi')",
        (order_id, user_id, inr_amount, current_time, purpose, product_id, quantity, description)
    )
    payment_url = ""
    
    async with aiohttp.ClientSession() as session:
        try:
            url = "https://pay.zapupi.com/api/create-order"
            payload = {"zap_key": api_key, "order_id": order_id, "amount": str(inr_amount), "customer_mobile": mobile, "remark": "Wallet Topup", "success_url": bot_deep_link, "failed_url": f"https://t.me/{bot_username_clean()}", "timeout_url": f"https://t.me/{bot_username_clean()}", "webhook_url": f"https://t.me/{bot_username_clean()}"}
            async with session.post(url, json=payload) as resp:
                if resp.status == 200:
                    try: res_data = await resp.json(content_type=None)
                    except: res_data = {}
                    if res_data.get("status") == "success": payment_url = res_data.get("payment_url")
                    else: return await message_obj.edit_text(f"❌ <b>Gateway Data Error:</b> {res_data.get('message', 'Unknown structure.')}", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')
                else: return await message_obj.edit_text(f"❌ <b>Gateway Server Error:</b> HTTP {resp.status}", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')
        except Exception as e:
            return await message_obj.edit_text(f"❌ <b>API Connection Error:</b> {str(e)}", reply_markup=back_kb("gateway_inr"), parse_mode='HTML')

    invoice_label = f"🛒 <b>Direct Purchase:</b> {html.escape(description)}\n" if purpose == "product_purchase" and description else ""
    text = (f"🧾 <b>SECURE UPI INVOICE</b>\n\n{invoice_label}"
            f"Amount: <b>₹{inr_amount:.2f}</b>\nOrder ID: <code>{html.escape(order_id)}</code>\n"
            "Tap <b>Open Payment Page</b> to pay on the provider's website. After payment, use Verify Payment if the wallet has not updated yet.")
    log_activity(user_id, "GENERATE_INVOICE", f"Amount: {inr_amount}, Order ID: {order_id}")
    await message_obj.edit_text(
        text,
        reply_markup=make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="Open Payment Page", url=payment_url)],
            [InlineKeyboardButton(text="Verify Payment", callback_data=f"verify_{order_id}")],
            [InlineKeyboardButton(text="Back", callback_data="gateway_inr")]
        ]),
        parse_mode="HTML", disable_web_page_preview=True
    )

@dp.callback_query(F.data.startswith("verify_"))
async def manual_verify_callback(call: CallbackQuery):
    order_id = call.data.split("_", 1)[1]
    await run_payment_verification(call.from_user.id, order_id, call)

@dp.callback_query(F.data == "gateway_crypto")
async def add_balance_crypto(call: CallbackQuery, state: FSMContext):
    rate = float(get_setting("binance_usdt_rate", "90") or 90)
    address = (get_setting("binance_address", "") or "").strip()
    if not address:
        return await call.message.edit_text("⚠️ Binance Pay ID is not configured yet. Please contact the admin.", reply_markup=back_kb("menu_add_balance"), parse_mode='HTML')
    kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="📋 Show / Copy Binance ID", callback_data="crypto_show_id")], [InlineKeyboardButton(text="❌ Cancel", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"))]])
    await call.message.edit_text(
        f"🪙 <b>BINANCE MANUAL PAYMENT</b>\n\n💵 <b>Rate:</b> 1 USDT = ₹{rate:g}\n"
        "Enter the USDT amount you are going to pay (e.g. 5 or 10.5).\n\n"
        "Use <b>Show / Copy Binance ID</b> to view the admin's payment ID. After paying, submit your screenshot and Binance transaction/order ID.\n\n"
        "⚠️ Wallet balance is credited only after admin approval.\n\n"
        "ℹ️ A normal Binance Pay ID does not expose an official transaction-status API to this bot; auto-verification is not available through Pay ID alone.",
        reply_markup=kb, parse_mode='HTML')
    await state.set_state(UserStates.wait_for_crypto_amount)

@dp.callback_query(F.data == "crypto_show_id")
async def crypto_show_binance_id(call: CallbackQuery):
    address = (get_setting("binance_address", "") or "").strip()
    if not address:
        return await call.answer("Binance ID is not configured.", show_alert=True)
    await call.message.answer(f"🪙 <b>Admin Binance Pay ID</b>\n\n<code>{html.escape(address)}</code>\n\nTap the ID to copy it.", parse_mode="HTML")
    await call.answer("Binance ID shown")

@dp.message(UserStates.wait_for_crypto_amount)
async def process_crypto_amount(m: Message, state: FSMContext):
    try:
        usdt = float((m.text or '').strip())
        if usdt <= 0 or usdt > 1000000: raise ValueError
    except ValueError:
        return await m.answer("❌ Invalid amount. Enter a number like <code>5</code> or <code>10.5</code>.", parse_mode='HTML')
    rate = float(get_setting("binance_usdt_rate", "90") or 90)
    inr = round(usdt * rate, 2)
    address = (get_setting("binance_address", "") or "").strip()
    if not address:
        return await m.answer("⚠️ Admin Binance Pay ID is not configured. Contact support.")
    await state.update_data(crypto_usdt=usdt, crypto_inr=inr, crypto_rate=rate)
    caption = (f"🪙 <b>BINANCE MANUAL PAYMENT</b>\n\n💵 Pay: <b>{usdt:g} USDT</b>\n"
               f"💱 Rate: <b>1 USDT = ₹{rate:g}</b>\n💰 Wallet credit after approval: <b>{fmt_curr(inr)}</b>\n\n"
               f"🆔 Admin Binance Pay ID:\n<code>{html.escape(address)}</code>\n\n"
               "1. Copy the Binance Pay ID and complete payment in Binance.\n"
               "2. Send the payment screenshot in this chat.\n"
               "3. Send your Binance transaction ID / order ID.\n\n"
               "⏳ Admin will verify manually before adding balance.\n\n"
               "ℹ️ A normal Binance Pay ID does not provide this bot with an official transaction-status API, so automatic verification cannot be guaranteed without a supported merchant/payment API.")
    kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="📋 Show / Copy Binance ID", callback_data="crypto_show_id")], [InlineKeyboardButton(text="❌ Cancel", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("back"))]])
    await m.answer(caption, reply_markup=kb, parse_mode='HTML')
    await state.set_state(UserStates.wait_for_crypto_ss)

@dp.message(UserStates.wait_for_crypto_ss)
async def process_crypto_ss(m: Message, state: FSMContext):
    if not m.photo:
        return await m.answer("❌ Please send the Binance payment screenshot as a photo.", parse_mode='HTML')
    await state.update_data(crypto_photo_id=m.photo[-1].file_id)
    await m.answer("✅ Screenshot received. Now send the Binance transaction ID / order ID (TxID). Do not send your password or OTP.")
    await state.set_state(UserStates.wait_for_crypto_txid)

@dp.message(UserStates.wait_for_crypto_txid)
async def process_crypto_txid(m: Message, state: FSMContext):
    user_txid = (m.text or '').strip()
    if len(user_txid) < 5 or len(user_txid) > 180:
        return await m.answer("❌ Please send a valid transaction/order ID (5–180 characters).")
    data = await state.get_data()
    usdt = float(data.get("crypto_usdt", 0) or 0)
    inr = float(data.get("crypto_inr", 0) or 0)
    rate = float(data.get("crypto_rate", get_setting("binance_usdt_rate", "90") or 90))
    photo_id = data.get("crypto_photo_id")
    user_id = m.from_user.id
    if not usdt or not photo_id:
        await state.clear()
        return await m.answer("⚠️ Payment request session expired. Please start Add Balance again.")
    duplicate = db_query("SELECT txid FROM crypto_txns WHERE user_txid=? AND status IN ('pending','approved') LIMIT 1", (user_txid,), fetchone=True)
    if duplicate:
        return await m.answer("❌ This transaction/order ID has already been submitted. Please check the ID or contact admin.")
    import time as _time
    internal_id = f"BN_{user_id}_{int(_time.time())}"
    db_query("INSERT INTO crypto_txns (txid, user_id, amount_usdt, amount_inr, photo_id, status, timestamp, user_txid) VALUES (?,?,?,?,?,'pending',?,?)",
             (internal_id, user_id, usdt, inr, photo_id, int(_time.time()), user_txid))
    uname = f"@{m.from_user.username}" if m.from_user.username else "No username"
    admin_text = (f"🪙 <b>BINANCE MANUAL DEPOSIT REQUEST</b>\n━━━━━━━━━━━━━━\n"
                  f"👤 User: <b>{html.escape(m.from_user.full_name)}</b>\n🆔 ID: <code>{user_id}</code> | {uname}\n"
                  f"💵 Amount: <b>{usdt:g} USDT ≈ {fmt_curr(inr)}</b>\n💱 Rate: <b>₹{rate:g}/USDT</b>\n"
                  f"🔖 User TxID / Order ID: <code>{html.escape(user_txid)}</code>\n🧾 Internal Ref: <code>{internal_id}</code>\n"
                  "━━━━━━━━━━━━━━\nCheck the screenshot and transaction in Binance before approving.")
    admin_kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Approve & Credit", callback_data=f"crypto_approve_{internal_id}")],
        [InlineKeyboardButton(text="❌ Reject", callback_data=f"crypto_reject_{internal_id}")]])
    await notify_admins(admin_text, reply_markup=admin_kb, parse_mode='HTML')
    for aid in ADMIN_IDS:
        try: await bot.send_photo(aid, photo=photo_id, caption=f"📸 Binance proof | Ref: {internal_id} | User TxID: {user_txid}")
        except Exception: pass
    await m.answer(f"⏳ <b>Payment request submitted!</b>\n\n💵 {usdt:g} USDT ≈ {fmt_curr(inr)}\n🔖 TxID: <code>{html.escape(user_txid)}</code>\n\nAdmin will verify the screenshot and TxID manually. Your wallet will be credited only after approval.", reply_markup=back_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("crypto_approve_"))
async def crypto_approve(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    txid = call.data.split("crypto_approve_", 1)[1]
    row = db_query("SELECT user_id, amount_usdt, amount_inr, status FROM crypto_txns WHERE txid=?", (txid,), fetchone=True)
    if not row: return await call.answer("❌ Request not found!", show_alert=True)
    if row[3] == 'approved': return await call.answer("⚠️ Already approved!", show_alert=True)
    user_id, usdt, inr = row[0], row[1], row[2]
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    try:
        conn.execute("BEGIN IMMEDIATE")
        cur = conn.execute("UPDATE crypto_txns SET status='approved' WHERE txid=? AND status='pending'", (txid,))
        if cur.rowcount != 1:
            conn.rollback()
            return await call.answer("⚠️ This request was already processed.", show_alert=True)
        conn.execute("UPDATE users SET balance=balance+? WHERE user_id=?", (inr, user_id))
        conn.commit()
    finally:
        conn.close()
    log_activity(user_id, "CRYPTO_DEPOSIT", f"SS Approved: {txid}, USDT:{usdt}, INR:{inr}")
    try:
        await bot.send_message(user_id,
            f"🎉 <b>BINANCE PAYMENT APPROVED!</b>\n\n"
            f"✅ {usdt} USDT = <b>{fmt_curr(inr)}</b> added to your wallet!\n"
            f"💰 Check your balance in My Profile.",
            parse_mode='HTML'
        )
    except: pass
    await call.message.edit_text(f"✅ APPROVED — {usdt} USDT → {fmt_curr(inr)} credited to user {user_id}")
    await call.answer(f"✅ Approved! {fmt_curr(inr)} credited.", show_alert=True)

@dp.callback_query(F.data.startswith("crypto_reject_"))
async def crypto_reject(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    txid = call.data.split("crypto_reject_", 1)[1]
    row = db_query("SELECT user_id, amount_usdt, status FROM crypto_txns WHERE txid=?", (txid,), fetchone=True)
    if not row: return await call.answer("❌ Request not found!", show_alert=True)
    if row[2] == 'approved': return await call.answer("⚠️ Already approved, can't reject!", show_alert=True)
    db_query("UPDATE crypto_txns SET status='rejected' WHERE txid=?", (txid,))
    try:
        await bot.send_message(row[0],
            "❌ <b>BINANCE PAYMENT REJECTED</b>\n\n"
            "Your screenshot was rejected by admin.\n"
            "Contact support if you think this is a mistake.",
            parse_mode='HTML'
        )
    except: pass
    await call.message.edit_text(f"❌ REJECTED — {txid}")
    await call.answer("❌ Rejected.", show_alert=True)



# ==============================================================================
# 13. SHOP – with uppercase categories and new point_down emoji
# ==============================================================================
@dp.callback_query(F.data == "menu_shop")
async def view_shop_panels(call: CallbackQuery):
    if (get_setting("product_store_enabled", "ON") or "ON").upper() != "ON":
        return await call.answer("Product Store is currently disabled by admin.", show_alert=True)
    log_activity(call.from_user.id, "VIEW_SHOP")
    kb = make_inline_kb(inline_keyboard=[], _width=1)
    text = f"{get_emoji('product_store')} <b><u>SELECT PRODUCT PANEL</u></b>\n━━━━━━━━━━━━━━━━━━\n\n{get_emoji('point_down')} <b>Choose a panel to view its packages:</b>"
    for cat in get_all_categories():
        count = db_query("SELECT COUNT(*) FROM products WHERE category LIKE ? AND is_active=1", (cat + '%',), fetchone=True)[0]
        custom_id = get_setting(f"cat_custom_id_{cat}", "").strip()
        stored_emoji = get_setting(f"cat_emoji_{cat}", "").strip()
        
        if custom_id and custom_id.isdigit():
            btn_text = cat
            btn_icon = custom_id
        elif stored_emoji and stored_emoji.isdigit():
            btn_text = cat
            btn_icon = stored_emoji
        elif stored_emoji:
            btn_text = f"{stored_emoji} {cat}"
            btn_icon = None
        else:
            default_icon_id = get_category_emoji(cat)
            if default_icon_id and str(default_icon_id).isdigit():
                btn_text = cat
                btn_icon = default_icon_id
            else:
                cat_icon = get_category_display_icon(cat)
                btn_text = f"{cat_icon} {cat}"
                btn_icon = None
        kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"shop_cat_{cat}", icon_custom_emoji_id=as_emoji_icon_id(btn_icon))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("shop_cat_"))
async def view_panel_names(call: CallbackQuery):
    category = call.data.split("shop_cat_", 1)[1]
    panel_rows = db_query("""
        SELECT MIN(id) AS sample_id, panel_name, COALESCE(MIN(panel_sort_order), 0) AS p_order
        FROM products 
        WHERE category LIKE ? AND is_active=1 AND panel_name != ''
        GROUP BY panel_name
        ORDER BY p_order ASC, panel_name ASC
    """, (category + '%',), fetchall=True)
    if not panel_rows:
        prods = db_query("""
            SELECT id, name, price_inr, stock, reseller_price, validity, device_limit, external_enabled, COALESCE(is_maintenance, 0), COALESCE(sort_order, 0), COALESCE(description, ''), COALESCE(video_file_id, '')
            FROM products WHERE category LIKE ? AND is_active=1
            ORDER BY COALESCE(sort_order, 0) ASC, id ASC
        """, (category + '%',), fetchall=True)
        if not prods: return await call.answer("❌ No products available in this category yet.", show_alert=True)
        await show_products_for_panel(call, prods, category, category)
        return
    kb = make_inline_kb(inline_keyboard=[], _width=1)
    text = f"{get_emoji('product_store')} <b><u>{category.upper()} PANELS</u></b>\n━━━━━━━━━━━━━━━━━━\n\n{get_emoji('point_down')} <b>Choose a panel name:</b>"
    for pn in panel_rows:
        sample_id, panel, p_order = pn[0], pn[1], pn[2]
        custom_id = get_setting(f"panel_custom_id_{panel}", "").strip()
        stored_emoji = get_setting(f"panel_emoji_{panel}", "").strip()
        
        if custom_id and custom_id.isdigit():
            btn_text = panel
            btn_icon = custom_id
        elif stored_emoji and stored_emoji.isdigit():
            btn_text = panel
            btn_icon = stored_emoji
        elif stored_emoji:
            btn_text = f"{stored_emoji} {panel}"
            btn_icon = None
        else:
            btn_text = panel
            btn_icon = get_emoji_icon("product_store")
            
        kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"shop_pnl_{sample_id}", icon_custom_emoji_id=as_emoji_icon_id(btn_icon))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK TO PANELS", callback_data="menu_shop", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("shop_pnl_"))
async def view_products_for_panel(call: CallbackQuery):
    sample_id = int(call.data.split("shop_pnl_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("No products found for this panel.", show_alert=True)
    category, panel_name = prod
    prods = db_query("""
        SELECT id, name, price_inr, stock, reseller_price, validity, device_limit, external_enabled, COALESCE(is_maintenance, 0), COALESCE(sort_order, 0), COALESCE(description, ''), COALESCE(video_file_id, '')
        FROM products 
        WHERE category=? AND panel_name=? AND is_active=1
        ORDER BY COALESCE(sort_order, 0) ASC, id ASC
    """, (category, panel_name), fetchall=True)
    if not prods: return await call.answer("No products found for this panel.", show_alert=True)
    await show_products_for_panel(call, prods, f"{category} - {panel_name}", category)

async def show_products_for_panel(call: CallbackQuery, prods: List[Tuple], header: str, category: str = ""):
    user = db_query("SELECT is_reseller, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    is_reseller = bool(user[0]) if user else False
    is_vip = bool(user[1]) if user else False
    kb = make_inline_kb(inline_keyboard=[])
    text = f"{get_emoji('product_store')} <b><u>{header.upper()} PACKAGES</u></b>\n━━━━━━━━━━━━━━━━━━\n\n"
    has_custom_sort = any(len(p) > 9 and p[9] != 0 for p in prods)
    if has_custom_sort:
        prods = sorted(prods or [], key=lambda row: (row[9] if len(row) > 9 else 0, product_name_sort_key(row[1])))
    else:
        prods = sorted(prods or [], key=lambda row: product_name_sort_key(row[1]))
    for p in prods:
        prod_id, package_name, normal_price, stock, reseller_price, validity, device, external_enabled = p[:8]
        is_maint = bool(p[8]) if len(p) > 8 else is_product_in_maintenance(prod_id)
        normal_price = float(normal_price) if normal_price is not None else 0.0
        reseller_price = float(reseller_price) if reseller_price is not None else 0.0
        base_price = reseller_price if is_reseller else normal_price
        if is_vip: display_price = base_price - (base_price * (VIP_DISCOUNT_PERCENTAGE / 100))
        else: display_price = base_price
        if is_maint:
            stock_status = "🟠 Under Maintenance"
        else:
            stock_status = "♾️ API Available" if external_enabled else ("✅ In Stock" if stock > 0 else "❌ Out of Stock")

        dur_custom_id = get_setting(f"dur_custom_id_{package_name.lower().strip()}", "").strip()
        dur_stored = get_setting(f"dur_emoji_{package_name.lower().strip()}", "").strip()
        if not dur_custom_id and not dur_stored:
            lower = package_name.lower().strip()
            for k in DEFAULT_DURATION_EMOJIS:
                if k in lower:
                    dur_custom_id = get_setting(f"dur_custom_id_{k}", "").strip()
                    dur_stored = get_setting(f"dur_emoji_{k}", "").strip()
                    break

        if dur_custom_id and dur_custom_id.isdigit():
            btn_icon_id = dur_custom_id
            btn_text = f"Buy {package_name} - {fmt_curr(display_price)}"
            dur_disp = f'<tg-emoji emoji-id="{dur_custom_id}">⚡</tg-emoji>'
        elif dur_stored and dur_stored.isdigit():
            btn_icon_id = dur_stored
            btn_text = f"Buy {package_name} - {fmt_curr(display_price)}"
            dur_disp = f'<tg-emoji emoji-id="{dur_stored}">⚡</tg-emoji>'
        elif dur_stored:
            btn_icon_id = None
            btn_text = f"{dur_stored} Buy {package_name} - {fmt_curr(display_price)}"
            dur_disp = dur_stored
        else:
            fallback = get_duration_emoji(package_name)
            btn_icon_id = None
            btn_text = f"{fallback} Buy {package_name} - {fmt_curr(display_price)}"
            dur_disp = fallback

        text += f"{dur_disp} <b>Validity: {package_name}</b>\n"
        product_desc = str(p[10] or "").strip() if len(p) > 10 else ""
        if product_desc:
            text += f"{html.escape(product_desc)}\n"
        if is_maint:
            text += "⚠️ <b>Status: Under Maintenance / यह प्रोडक्ट मेंटेनेंस में है</b>\n"
        # Show only the final applicable price; never reveal reseller price separately.
        price_label = "🌟 Your VIP Price" if is_vip and not is_reseller else ("💰 Your Price" if is_reseller else "💰 Price")
        text += f"{price_label}: <b>{fmt_curr(display_price)}</b>\n"
        text += f"📱 Limit: {device} | 📦 {stock_status}\n\n"
        if is_maint:
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"🟠 {package_name} (Under Maintenance)", callback_data=f"buy_{prod_id}", icon_custom_emoji_id=get_emoji_icon("shield_icon"))])
        elif external_enabled or stock > 0:
            kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"buy_{prod_id}", icon_custom_emoji_id=as_emoji_icon_id(btn_icon_id))])
        else:
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"❌ {package_name} (Out of Stock)", callback_data="ignore_stock_click")])

    text += f"{get_emoji('point_down')} <b>Select package below to instantly purchase:</b>"
    # One panel-level Demo Video button: place it AFTER every duration/package
    # button and immediately BEFORE Back to Panels. All durations share one video.
    first_product_id = int(prods[0][0]) if prods else 0
    panel_info = db_query(
        "SELECT COALESCE(category,''), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name) FROM products WHERE id=?",
        (first_product_id,), fetchone=True
    ) if first_product_id else None
    if panel_info:
        panel_category, panel_key = str(panel_info[0] or ""), str(panel_info[1] or "")
        demo = db_query("SELECT video_file_id FROM panel_demo_videos WHERE category=? AND panel_key=?", (panel_category, panel_key), fetchone=True)
        if demo and str(demo[0] or '').strip():
            emoji_setting = (get_setting('demo_video_emoji', '🎬') or '🎬').strip()
            custom_emoji_id = ''
            emoji_prefix = emoji_setting or '🎬'
            if emoji_setting.startswith('id:') and emoji_setting[3:].isdigit():
                custom_emoji_id = emoji_setting[3:]
                emoji_prefix = ''
            elif emoji_setting.isdigit():
                custom_emoji_id = emoji_setting
                emoji_prefix = ''
            demo_button = InlineKeyboardButton(
                text=f"{emoji_prefix} Demo Video",
                callback_data=f"product_demo_{first_product_id}",
                icon_custom_emoji_id=custom_emoji_id or None,
            )
            kb.inline_keyboard.append([demo_button])
            demo_color = (get_setting('demo_video_color', 'green') or 'green').strip().lower()
            if demo_color not in UI_BUTTON_COLORS:
                demo_color = 'green'
            # This callback-specific setting lets the existing UI renderer style
            # this button independently from all other buttons.
            set_setting('ui_color_product_demo', demo_color)
            _apply_ui_button_style(demo_button, demo_color)
    back_cb = f"shop_cat_{category}" if category else "menu_shop"
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK TO PANELS", callback_data=back_cb, icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_demo_videos")
async def admin_demo_videos_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    rows = db_query("SELECT DISTINCT COALESCE(category,'') FROM products ORDER BY COALESCE(category,'') COLLATE NOCASE", fetchall=True) or []
    kb = make_inline_kb(inline_keyboard=[])
    for (category,) in rows:
        label = str(category or "Uncategorized")
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"📂 {label}", callback_data="demo_cat_" + label)])
    kb.inline_keyboard.append([InlineKeyboardButton(text="✏️ Change Demo Emoji", callback_data="demo_emoji_change")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="🎨 Change Demo Button Color", callback_data="demo_color_menu")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="⬅️ Back to Admin", callback_data="admin_panel_back")])
    current_emoji = get_setting('demo_video_emoji', '🎬') or '🎬'
    current_color = get_setting('demo_video_color', 'green') or 'green'
    await call.message.edit_text("🎬 <b>PANEL DEMO VIDEO MANAGER</b>\n\nChoose a category, then choose the panel name (not individual duration plans). Each panel has ONE demo video shared by all its plans.\n\nCurrent button: <b>" + html.escape(current_emoji) + " Demo Video</b>\nColor: <b>" + html.escape(current_color.upper()) + "</b>", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "demo_emoji_change")
async def demo_emoji_change_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_demo_emoji)
    await call.message.answer("Send the emoji you want before Demo Video. You can send a Telegram Premium custom emoji or a numeric custom-emoji ID. Send /cancel to keep the current setting.")
    await call.answer()

@dp.message(AdminStates.wait_for_demo_emoji)
async def demo_emoji_change_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id):
        return
    value = (message.text or '').strip()
    if value.lower() == '/cancel':
        await state.clear()
        return await message.answer("Demo emoji unchanged.", reply_markup=admin_kb())
    emoji_char, custom_id = extract_emoji_or_id(message)
    if custom_id:
        set_setting('demo_video_emoji', 'id:' + custom_id)
    elif emoji_char and len(emoji_char) <= 32:
        set_setting('demo_video_emoji', emoji_char)
    else:
        return await message.answer("Send one emoji or a valid custom-emoji ID, or /cancel.")
    await state.clear()
    await message.answer("✅ Demo Video emoji saved. It will appear on the panel package list.", reply_markup=admin_kb())

@dp.callback_query(F.data == "demo_color_menu")
async def demo_color_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    current = (get_setting('demo_video_color', 'green') or 'green').upper()
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🟢 Green", callback_data="demo_color_green")],
        [InlineKeyboardButton(text="🔵 Blue", callback_data="demo_color_blue")],
        [InlineKeyboardButton(text="🔴 Red", callback_data="demo_color_red")],
        [InlineKeyboardButton(text="⚪ Default / Off", callback_data="demo_color_off")],
        [InlineKeyboardButton(text="⬅️ Back", callback_data="admin_demo_videos")],
    ])
    await call.message.edit_text(f"🎨 <b>Demo Video Button Color</b>\nCurrent: <b>{current}</b>\nChoose a Telegram button style:", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data.startswith("demo_color_"))
async def demo_color_save(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    color = call.data.rsplit('_', 1)[1].lower()
    if color not in UI_BUTTON_COLORS:
        return await call.answer("Invalid color", show_alert=True)
    set_setting('demo_video_color', color)
    set_setting('ui_color_product_demo', color)
    await call.answer(f"Demo Video color set to {color.upper()}", show_alert=True)
    await admin_demo_videos_menu(call)

@dp.callback_query(F.data.startswith("demo_cat_"))
async def admin_demo_video_category(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    category_label = call.data[len("demo_cat_"):]
    category = "" if category_label == "Uncategorized" else category_label
    rows = db_query("""
        SELECT MIN(id), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name) AS panel_key, COUNT(*)
        FROM products
        WHERE COALESCE(category,'')=?
        GROUP BY COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name)
        ORDER BY panel_key COLLATE NOCASE
    """, (category,), fetchall=True) or []
    kb = make_inline_kb(inline_keyboard=[])
    for sample_id, panel_key, count in rows:
        demo = db_query("SELECT video_file_id FROM panel_demo_videos WHERE category=? AND panel_key=?", (category, str(panel_key or "")), fetchone=True)
        status = "🎬" if demo and str(demo[0] or "").strip() else "➕"
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{status} {panel_key} · {count} plan(s)", callback_data=f"demo_panel_{sample_id}")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="⬅️ Categories", callback_data="admin_demo_videos")])
    await call.message.edit_text(f"📂 <b>{html.escape(category_label)}</b> — choose a panel (not a duration):", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data.startswith("demo_panel_"))
async def admin_demo_video_panel(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    try:
        sample_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid panel", show_alert=True)
    row = db_query("SELECT COALESCE(category,''), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name), COALESCE(name,'') FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not row:
        return await call.answer("Panel not found", show_alert=True)
    category, panel_key, display_name = row
    demo = db_query("SELECT video_file_id FROM panel_demo_videos WHERE category=? AND panel_key=?", (category, panel_key), fetchone=True)
    video_id = str(demo[0] or "").strip() if demo else ""
    count = db_query("SELECT COUNT(*) FROM products WHERE COALESCE(category,'')=? AND COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name)=?", (category, panel_key), fetchone=True)
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Add / Replace Panel Video", callback_data=f"demo_set_{sample_id}")],
        [InlineKeyboardButton(text="🗑 Remove Panel Video", callback_data=f"demo_remove_{sample_id}")],
        [InlineKeyboardButton(text="⬅️ Back to Panels", callback_data="demo_cat_" + (category or "Uncategorized"))],
    ])
    status = "✅ One video attached to all plans" if video_id else "❌ No demo video attached"
    await call.message.edit_text(f"🎬 <b>{html.escape(str(panel_key))}</b>\n📂 Category: {html.escape(str(category or 'Uncategorized'))}\n📦 Plans in this panel: <b>{int(count[0] or 0) if count else 0}</b>\nStatus: {status}\n\nUpload ONE video here. Every duration under this panel will use the same demo.", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data.startswith("demo_set_"))
async def admin_demo_video_set_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    try:
        sample_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid panel", show_alert=True)
    row = db_query("SELECT COALESCE(category,''), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name) FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not row:
        return await call.answer("Panel not found", show_alert=True)
    await state.update_data(demo_video_sample_id=sample_id, demo_video_category=row[0], demo_video_panel_key=row[1])
    await state.set_state(AdminStates.wait_for_demo_video)
    await call.message.answer(f"🎬 Send the ONE demo video for panel <b>{html.escape(str(row[1]))}</b>. It will apply to every duration/package under this panel. Send /cancel to abort.", parse_mode="HTML")
    await call.answer()

@dp.message(AdminStates.wait_for_demo_video)
async def admin_demo_video_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    if (m.text or "").strip().lower() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb())
    if m.video:
        file_id = m.video.file_id
    elif m.document and (m.document.mime_type or "").startswith("video/"):
        file_id = m.document.file_id
    else:
        return await m.answer("❌ Send a video or video file, or /cancel.")
    data = await state.get_data()
    category = str(data.get("demo_video_category", ""))
    panel_key = str(data.get("demo_video_panel_key", ""))
    if not panel_key:
        await state.clear()
        return await m.answer("❌ Panel session expired. Open Demo Video Manager again.", reply_markup=admin_kb())
    db_query("INSERT INTO panel_demo_videos (category,panel_key,display_name,video_file_id,updated_at) VALUES (?,?,?,?,CURRENT_TIMESTAMP) ON CONFLICT(category,panel_key) DO UPDATE SET display_name=excluded.display_name, video_file_id=excluded.video_file_id, updated_at=CURRENT_TIMESTAMP", (category, panel_key, panel_key, file_id))
    await state.clear()
    await m.answer(f"✅ One demo video saved for <b>{html.escape(panel_key)}</b>. It is shared by all plans in this panel.", reply_markup=admin_kb(), parse_mode="HTML")

@dp.callback_query(F.data.startswith("demo_remove_"))
async def admin_demo_video_remove(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    try:
        sample_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid panel", show_alert=True)
    row = db_query("SELECT COALESCE(category,''), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name) FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not row:
        return await call.answer("Panel not found", show_alert=True)
    category, panel_key = row
    db_query("DELETE FROM panel_demo_videos WHERE category=? AND panel_key=?", (category, panel_key))
    await call.answer("Panel demo video removed", show_alert=True)
    await call.message.edit_text(f"🗑 Demo video removed for panel <b>{html.escape(str(panel_key))}</b>.", reply_markup=make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="🎬 Demo Video Manager", callback_data="admin_demo_videos")], [InlineKeyboardButton(text="⬅️ Admin Panel", callback_data="admin_panel_back")]]), parse_mode="HTML")

@dp.callback_query(F.data.startswith("product_demo_"))
async def send_product_demo_video(call: CallbackQuery):
    try:
        product_id = int(call.data.split("product_demo_", 1)[1])
    except (TypeError, ValueError):
        return await call.answer("Invalid demo video request.", show_alert=True)
    row = db_query("SELECT COALESCE(name,''), COALESCE(category,''), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name) FROM products WHERE id=? AND is_active=1", (product_id,), fetchone=True)
    if not row:
        return await call.answer("Product is not available.", show_alert=True)
    product_name, category, panel_key = row
    demo = db_query("SELECT video_file_id FROM panel_demo_videos WHERE category=? AND panel_key=?", (category, panel_key), fetchone=True)
    video_id = str(demo[0] or "").strip() if demo else ""
    if not video_id:
        return await call.answer("Demo video is not available for this panel yet.", show_alert=True)
    await call.answer()
    try:
        await call.message.answer_video(video_id, caption=f"🎬 {html.escape(str(panel_key or product_name or 'Product demo'))} — Demo Video", parse_mode="HTML")
    except Exception as exc:
        logger.exception("Could not send panel demo video for product_id=%s", product_id)
        await call.message.answer(f"Could not send demo video: {html.escape(str(exc)[:300])}")

@dp.callback_query(F.data.startswith("reseller_price_one_"))
async def show_one_reseller_price(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("This option is unavailable.", show_alert=True)
    try:
        prod_id = int(call.data.split("reseller_price_one_", 1)[1])
    except Exception:
        return await call.answer("Invalid reseller price request.", show_alert=True)
    row = db_query("SELECT name, price_inr, reseller_price, validity, panel_name FROM products WHERE id=? AND is_active=1", (prod_id,), fetchone=True)
    if not row:
        return await call.answer("Product not found.", show_alert=True)
    name, regular, reseller, validity, panel = row
    await call.message.edit_text(
        f"👑 <b>RESELLER PRICE</b>\n\n📦 <b>{html.escape(str(name or validity or 'Package'))}</b>\n🏷 Panel: <b>{html.escape(str(panel or '-'))}</b>\n💰 Regular: <s>{fmt_curr(float(regular or 0))}</s>\n👑 <b>Reseller: {fmt_curr(float(reseller or 0))}</b>\n\nℹ️ This price is for accounts with Reseller status. Your account status does not change by viewing this price.",
        reply_markup=back_kb(f"shop_pnl_{prod_id}"), parse_mode="HTML")

@dp.callback_query(F.data.startswith("reseller_prices_"))
async def show_reseller_prices(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("This option is unavailable.", show_alert=True)
    try:
        sample_id = int(call.data.split("_", 2)[2])
    except Exception:
        return await call.answer("Invalid reseller price request.", show_alert=True)
    row = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not row:
        return await call.answer("Product panel not found.", show_alert=True)
    category, panel_name = row
    prods = db_query("SELECT name, price_inr, reseller_price, validity FROM products WHERE category=? AND panel_name=? AND is_active=1 ORDER BY id ASC", (category, panel_name), fetchall=True) or []
    lines = [f"👑 <b>RESELLER PRICE LIST</b>\n<b>{html.escape(panel_name or category or 'Panel')}</b>", "━━━━━━━━━━━━━━━━━━"]
    for name, regular, rprice, validity in prods:
        lines.append(f"📦 <b>{html.escape(str(name or validity or 'Package'))}</b>\n💰 Regular: {fmt_curr(float(regular or 0))}\n👑 Reseller: <b>{fmt_curr(float(rprice or 0))}</b>")
    lines.append("━━━━━━━━━━━━━━━━━━\nℹ️ Reseller prices apply at checkout only to users whose account is marked as Reseller.")
    await call.message.edit_text("\n".join(lines), reply_markup=back_kb("shop_pnl_" + str(sample_id)), parse_mode='HTML')

@dp.callback_query(F.data == "ignore_stock_click")
async def ignore_stock_click(call: CallbackQuery):
    await call.answer("⚠️ This duration is completely Out of Stock! Admins have been notified to refill.", show_alert=True)

@dp.callback_query(F.data.startswith("buy_"))
async def process_buy(call: CallbackQuery):
    if _callback_is_on_cooldown((call.from_user.id, "buy_menu")):
        return await call.answer("⏳ Please wait 3 seconds before opening purchase again.", show_alert=True)
    try:
        prod_id = int(call.data.split("_")[1])
    except (ValueError, IndexError):
        return await call.answer("Invalid product.", show_alert=True)
    prod = db_query("SELECT name, price_inr, reseller_price, stock, is_active, is_maintenance, external_enabled, COALESCE(video_file_id,''), COALESCE(category,''), COALESCE(NULLIF(panel_name,''), NULLIF(category,''), name) FROM products WHERE id=?", (prod_id,), fetchone=True)
    user = db_query("SELECT balance, is_reseller, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not prod or not user:
        return await call.answer("❌ Product or account not found.", show_alert=True)
    if prod[5]:
        return await call.answer("⚠️ This product is under maintenance.", show_alert=True)
    base = float(prod[2] or 0) if user[1] else float(prod[1] or 0)
    if user[2]:
        base -= base * VIP_DISCOUNT_PERCENTAGE / 100
    max_qty = 10 if prod[6] else min(10, int(prod[3] or 0))
    if max_qty < 1:
        return await call.answer("❌ This product is out of stock.", show_alert=True)
    kb = make_inline_kb(inline_keyboard=[])
    # This bot sells one key per checkout; keep the quantity option fixed at 1.
    kb.inline_keyboard.append([InlineKeyboardButton(text=f"1 Key × {fmt_curr(base)}", callback_data=f"buyqty_{prod_id}_1")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="menu_shop", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(
        f"🛒 <b>{prod[0]}</b>\n\n💰 <b>Unit Price:</b> {fmt_curr(base)}\n"
        f"📦 Select quantity (1–{max_qty})\n💳 Wallet or direct UPI payment is available.",
        reply_markup=kb, parse_mode="HTML"
    )

@dp.callback_query(F.data.startswith("buyqty_"))
async def choose_purchase_payment(call: CallbackQuery):
    try:
        _, prod_id_s, qty_s = call.data.split("_")
        prod_id, qty = int(prod_id_s), int(qty_s)
        if qty != 1:
            return await call.answer("Only one key can be purchased per order.", show_alert=True)
    except (ValueError, IndexError):
        return await call.answer("Invalid purchase request.", show_alert=True)
    prod = db_query("SELECT name, price_inr, reseller_price, stock, is_maintenance, external_enabled FROM products WHERE id=?", (prod_id,), fetchone=True)
    user = db_query("SELECT balance, is_reseller, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not prod or not user or prod[4]:
        return await call.answer("Product is unavailable.", show_alert=True)
    base = float(prod[2] or 0) if user[1] else float(prod[1] or 0)
    if user[2]:
        base -= base * VIP_DISCOUNT_PERCENTAGE / 100
    total = base * qty
    if not prod[5] and int(prod[3] or 0) < qty:
        return await call.answer(f"Only {prod[3] or 0} key(s) available.", show_alert=True)
    rows = []
    if float(user[0] or 0) >= total:
        rows.append([InlineKeyboardButton(text=f"💰 Pay Wallet {fmt_curr(total)}", callback_data=f"walletbuy_{prod_id}_{qty}")])
    else:
        rows.append([InlineKeyboardButton(text=f"👛 Wallet {fmt_curr(float(user[0] or 0))}", callback_data="ignore_stock_click")])
    if gateway_enabled("zapupi"):
        rows.append([InlineKeyboardButton(text=f"📲 Pay via ZapUPI {fmt_curr(total)}", callback_data=f"upibuy_{prod_id}_{qty}", icon_custom_emoji_id=get_emoji_icon("upi"))])
    if gateway_enabled("famgateway") and _famgateway_api_key():
        rows.append([InlineKeyboardButton(text=f"💜 Pay via FamGateway {fmt_curr(total)}", callback_data=f"famupibuy_{prod_id}_{qty}", icon_custom_emoji_id=get_emoji_icon("money_icon"))])
    rows.append([InlineKeyboardButton(text="⬅️ Back to Product", callback_data=f"buy_{prod_id}", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(
        f"🧾 <b>ORDER SUMMARY</b>\n\n📦 {prod[0]}\n🔢 Quantity: <b>{qty}</b>\n"
        f"💵 Unit: <b>{fmt_curr(base)}</b>\n💰 Total: <b>{fmt_curr(total)}</b>\n"
        f"👛 Wallet: <b>{fmt_curr(float(user[0] or 0))}</b>\n\nSelect payment method:",
        reply_markup=make_inline_kb(inline_keyboard=rows), parse_mode="HTML"
    )

@dp.callback_query(F.data.startswith("walletbuy_"))
async def wallet_purchase_quantity(call: CallbackQuery):
    if _callback_is_on_cooldown((call.from_user.id, "walletbuy")):
        return await call.answer("⏳ Purchase already started. Please wait 3 seconds.", show_alert=True)
    try:
        _, prod_id_s, qty_s = call.data.split("_")
        prod_id, qty = int(prod_id_s), int(qty_s)
    except (ValueError, IndexError):
        return await call.answer("Invalid purchase request.", show_alert=True)
    for _ in range(qty):
        await _process_single_buy(call, prod_id)

@dp.callback_query(F.data.startswith("famupibuy_"))
async def famgateway_direct_purchase(call: CallbackQuery):
    if not gateway_enabled("famgateway"):
        return await call.answer("⚠️ FamGateway is currently OFF by Admin.", show_alert=True)
    if _callback_is_on_cooldown((call.from_user.id, "famupibuy")):
        return await call.answer("⏳ Please wait 3 seconds before creating another payment.", show_alert=True)
    try:
        _, prod_id_s, qty_s = call.data.split("_")
        prod_id, qty = int(prod_id_s), int(qty_s)
    except (ValueError, IndexError):
        return await call.answer("Invalid purchase request.", show_alert=True)
    prod = db_query("SELECT name, price_inr, reseller_price, is_maintenance FROM products WHERE id=?", (prod_id,), fetchone=True)
    user = db_query("SELECT balance, is_reseller, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not prod or not user or prod[3]:
        return await call.answer("Product is unavailable.", show_alert=True)
    unit = float(prod[2] or 0) if user[1] else float(prod[1] or 0)
    if user[2]: unit -= unit * VIP_DISCOUNT_PERCENTAGE / 100
    total = unit * qty
    await call.message.edit_text("⏳ <b>Generating FamGateway payment...</b>", parse_mode="HTML")
    await create_famgateway_payment(call.from_user.id, total, call.message, purpose="product_purchase", product_id=prod_id, quantity=qty, description=f"{prod[0]} × {qty}")

@dp.callback_query(F.data.startswith("upibuy_"))
async def direct_upi_purchase(call: CallbackQuery):
    if not gateway_enabled("zapupi"):
        return await call.answer("⚠️ ZapUPI is currently OFF by Admin.", show_alert=True)
    if _callback_is_on_cooldown((call.from_user.id, "upibuy")):
        return await call.answer("⏳ Please wait 3 seconds before creating another payment.", show_alert=True)
    try:
        _, prod_id_s, qty_s = call.data.split("_")
        prod_id, qty = int(prod_id_s), int(qty_s)
    except (ValueError, IndexError):
        return await call.answer("Invalid purchase request.", show_alert=True)
    prod = db_query("SELECT name, price_inr, reseller_price, is_maintenance FROM products WHERE id=?", (prod_id,), fetchone=True)
    user = db_query("SELECT balance, is_reseller, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not prod or not user or prod[3]:
        return await call.answer("Product is unavailable.", show_alert=True)
    unit = float(prod[2] or 0) if user[1] else float(prod[1] or 0)
    if user[2]:
        unit -= unit * VIP_DISCOUNT_PERCENTAGE / 100
    total = unit * qty
    await call.message.edit_text("⏳ <b>Generating direct UPI payment...</b>", parse_mode="HTML")
    await generate_zapupi_order(
        call.from_user.id, total, call.message,
        purpose="product_purchase", product_id=prod_id, quantity=qty,
        description=f"{prod[0]} × {qty}"
    )

class _PurchaseCallProxy:
    def __init__(self, user, message):
        self.from_user = user
        self.message = message
    async def answer(self, *args, **kwargs):
        return None

async def _show_purchase_timer(call: CallbackQuery, seconds: int = 3):
    """Show a visible 3-second delivery countdown in the same chat message."""
    for remaining in range(seconds, 0, -1):
        try:
            await call.message.edit_text(
                f"⏳ <b>KEY GENERATION IN PROGRESS</b>\n\n"
                f"🔐 Your key is being fetched securely...\n"
                f"⏱ <b>{remaining} seconds</b> remaining\n\n"
                "⚠️ Please do not press the purchase button again.",
                parse_mode="HTML"
            )
        except Exception:
            pass
        await asyncio.sleep(1)


async def _process_single_buy(call: CallbackQuery, prod_id: int):
    user_id = int(call.from_user.id)
    lock = _get_purchase_lock(user_id, prod_id)
    if lock.locked():
        return await call.answer("⏳ This purchase is already being processed. Please wait.", show_alert=True)
    async with lock:
        return await _process_single_buy_locked(call, prod_id)

async def _process_single_buy_locked(call, prod_id: int):
    if is_product_in_maintenance(prod_id):
        return await call.answer("⚠️ Yeh product abhi maintenance me hai!\nThis product is currently under maintenance. Please check back later!", show_alert=True)
    prod = db_query("""
        SELECT name, price_inr, stock, apk_link, validity, device_limit,
               category, reseller_price, panel_name, external_enabled,
               external_product_id, requires_android_id, external_duration, api_provider
        FROM products WHERE id=?
    """, (prod_id,), fetchone=True)
    user = db_query("SELECT balance, referred_by, is_reseller, total_saved, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not prod:
        return await call.answer("❌ Critical Error: Item not found in DB!", show_alert=True)
    if not user:
        return await call.answer("❌ User account not found!", show_alert=True)

    normal_price = float(prod[1] or 0.0)
    reseller_price = float(prod[7] or 0.0)
    is_reseller = bool(user[2]); is_vip = bool(user[4])
    base_price = reseller_price if is_reseller else normal_price
    final_price = base_price - (base_price * (VIP_DISCOUNT_PERCENTAGE / 100)) if is_vip else base_price
    savings = normal_price - final_price

    # External/API products use the remote API as the real inventory source.
    # Their local stock number is only a display buffer and must not block API purchases.
    external_enabled = bool(prod[9])
    external_product_id = (prod[10] or "").strip()
    api_provider = (prod[13] if len(prod) > 13 and prod[13] else 'bunty').lower()
    if not external_enabled and (prod[2] is None or prod[2] <= 0):
        return await call.answer("❌ This product is out of stock!", show_alert=True)
    if user[0] < final_price:
        needed = final_price - user[0]
        low_bal_kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(
                text="Add Balance Now",
                callback_data="menu_add_balance",
                icon_custom_emoji_id=get_emoji_icon("add_balance")
            )],
            [InlineKeyboardButton(
                text="Back",
                callback_data=f"buy_{prod_id}",
                icon_custom_emoji_id=get_emoji_icon("back")
            )]
        ])
        return await call.message.edit_text(
            f"❌ <b>Insufficient Balance!</b>\n\n"
            f"💰 Your Balance: <b>{fmt_curr(user[0])}</b>\n"
            f"🛒 Required: <b>{fmt_curr(final_price)}</b>\n"
            f"➕ You need: <b>{fmt_curr(needed)} more</b>\n\n"
            "👇 Add balance to continue your purchase:",
            reply_markup=low_bal_kb,
            parse_mode='HTML'
        )

    # Prevent double-click purchases while processing the external API.
    await call.answer("⏳ Processing your purchase...", show_alert=False)
    delivered_key = None
    api_response = None

    # Charge first; external API failures are refunded immediately.
    db_query("UPDATE users SET balance=?, spent=spent+?, orders_count=orders_count+1, total_saved=total_saved+? WHERE user_id=?",
             (user[0] - final_price, final_price, savings, call.from_user.id))

    # Give the user a visible 3-second secure-delivery window before the key is shown.
    # The per-user/product asyncio lock plus wallet cooldown blocks duplicate taps.
    await _show_purchase_timer(call, 3)

    # Check if a manual key is already loaded in the vault first
    key_data = db_query("SELECT id, key_text FROM product_keys WHERE product_id=? AND is_used=0 LIMIT 1", (prod_id,), fetchone=True)
    if key_data:
        delivered_key = str(key_data[1])
        db_query("UPDATE product_keys SET is_used=1 WHERE id=?", (key_data[0],))
        db_query("UPDATE products SET stock=CASE WHEN stock>0 THEN stock-1 ELSE 0 END WHERE id=?", (prod_id,))
    elif external_enabled:
        if not external_product_id:
            db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
            return await call.message.edit_text("❌ API product ID is not configured for this product.", reply_markup=back_kb("menu_shop"), parse_mode='HTML')

        # HK Tamim API: POST variant_id/quantity using X-API-Token.
        if api_provider == "hk_tamim":
            hk_url = get_setting("hk_tamim_api_url", "https://hkmodz.shop/api/v1/generate_key.php").strip()
            hk_token = get_setting("hk_tamim_api_token", "").strip()
            try:
                if not hk_token:
                    api_response = {"status": "error", "msg": "HK Tamim API token is not configured by admin."}
                else:
                    if not str(external_product_id).isdigit():
                        raise ValueError("HK Tamim variant_id must be numeric; edit this product and set a numeric variant ID.")
                    timeout = aiohttp.ClientTimeout(total=25)
                    async with aiohttp.ClientSession(timeout=timeout) as session:
                        async with session.post(
                            hk_url,
                            headers={"X-API-Token": hk_token, "Accept": "application/json"},
                            data={"variant_id": int(external_product_id), "quantity": 1},
                        ) as resp:
                            raw_body = await resp.text()
                            logger.info("HK Tamim generate response: HTTP %s content_type=%r body=%s",
                                        resp.status, resp.headers.get("Content-Type", ""), raw_body[:1200])
                            if not raw_body.strip():
                                payload = {"success": False, "error": "EMPTY_REPLY",
                                           "message": f"HK Tamim returned an empty response (HTTP {resp.status}). Check server IP allowlist and API endpoint."}
                            else:
                                try:
                                    payload = json.loads(raw_body)
                                except json.JSONDecodeError:
                                    preview = raw_body.lstrip()[:120]
                                    if preview.startswith("<") or "Just a moment" in raw_body:
                                        payload = {"success": False, "error": "CLOUDFLARE_CHALLENGE",
                                                   "message": f"HK Tamim returned a Cloudflare/browser challenge (HTTP {resp.status}); ask shop admin to allowlist this hosting server IP."}
                                    else:
                                        payload = {"success": False, "error": "BAD_REPLY",
                                                   "message": f"HK Tamim returned non-JSON (HTTP {resp.status}): {raw_body[:240]}"}
                    keys_found = _extract_generated_keys(payload)
                    declared_ok = True
                    if isinstance(payload, dict):
                        if payload.get("ok") is False or payload.get("success") is False or str(payload.get("status", "")).lower() in {"error", "failed", "failure"}:
                            declared_ok = False
                    if resp.status < 400 and declared_ok and keys_found:
                        delivered_key = "\n".join(keys_found)
                        api_response = {"status": "success", "msg": "HK Tamim key generated", "key": delivered_key, "raw": payload}
                    else:
                        detail = (payload.get("message") or payload.get("msg") or payload.get("error") or payload.get("detail")) if isinstance(payload, dict) else str(payload)
                        api_response = {"status": "error", "msg": str(detail or f"HK Tamim API returned HTTP {resp.status}")}
            except Exception as api_exc:
                logger.exception("HK Tamim API purchase failed")
                api_response = {"status": "error", "msg": f"HK Tamim API request failed: {api_exc}"}
            if api_response.get("status") != "success":
                db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
                return await call.message.edit_text(f"❌ <b>HK Tamim API Error:</b> {html.escape(str(api_response.get('msg', 'Unknown error')))}\n\n💰 Your balance has been refunded.", reply_markup=back_kb("menu_shop"), parse_mode="HTML")
        # License Manager API: POST {product_id, quantity, idempotency_key} with Bearer auth.
        elif api_provider == "license_manager":
            lm_url = get_setting("license_manager_api_url", "https://licencedashboard.shop/api/v1/generate.php").strip()
            lm_key = get_setting("license_manager_api_key", "").strip()
            try:
                if not lm_key:
                    api_response = {"status": "error", "msg": "License Manager Bearer token is not configured by admin."}
                else:
                    if not str(external_product_id).isdigit():
                        raise ValueError("License Manager product_id must be numeric; edit this product and set a numeric product ID.")
                    idem = f"tg-{call.from_user.id}-{prod_id}-{int(time.time())}"
                    timeout = aiohttp.ClientTimeout(total=25)
                    async with aiohttp.ClientSession(timeout=timeout) as session:
                        async with session.post(lm_url,
                            headers={"Authorization": f"Bearer {lm_key}"},
                            json={"product_id": int(external_product_id), "quantity": 1, "idempotency_key": idem}) as resp:
                            payload = await resp.json(content_type=None)
                    keys_found = _extract_generated_keys(payload)
                    declared_ok = isinstance(payload, dict) and (payload.get("ok") is True or payload.get("success") is True or str(payload.get("status", "")).lower() in {"success", "ok", "completed"})
                    # Some deployments return a key field without an explicit ok/success flag.
                    if isinstance(payload, dict) and keys_found and not any(k in payload for k in ("ok", "success", "status")):
                        declared_ok = True
                    if resp.status < 400 and declared_ok and keys_found:
                        delivered_key = "\n".join(keys_found)
                        api_response = {"status": "success", "msg": "License generated", "key": delivered_key, "raw": payload}
                    else:
                        err = payload.get("error") if isinstance(payload, dict) else None
                        if isinstance(err, dict): err = err.get("message") or err.get("detail")
                        detail = (err or payload.get("message") or payload.get("msg")) if isinstance(payload, dict) else str(payload)
                        api_response = {"status": "error", "msg": str(detail or f"License Manager API returned HTTP {resp.status}")}
            except Exception as api_exc:
                logger.exception("License Manager API purchase failed")
                api_response = {"status": "error", "msg": f"License Manager API request failed: {api_exc}"}
            if api_response.get("status") != "success":
                db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
                return await call.message.edit_text(
                    f"❌ <b>License Manager API Error:</b> {html.escape(str(api_response.get('msg', 'Unknown error')))}\n\n💰 Your balance has been refunded.",
                    reply_markup=back_kb("menu_shop"), parse_mode="HTML")
        elif api_provider == "dripclient":
            base = (get_setting("dripclient_api_url", "https://dripclientofficial.shop/api/v1") or "").strip().rstrip("/")
            token = (get_setting("dripclient_api_token", "") or "").strip()
            try:
                if not token:
                    api_response = {"status": "error", "msg": "Drip Client API token is not configured by admin."}
                else:
                    if not str(external_product_id).isdigit():
                        raise ValueError("Drip Client variant_id must be numeric.")
                    timeout = aiohttp.ClientTimeout(total=30)
                    async with aiohttp.ClientSession(timeout=timeout) as session:
                        async with session.post(base + "/generate_key.php",
                            headers={"X-API-Token": token, "Accept": "application/json"},
                            data={"variant_id": int(external_product_id), "quantity": 1}) as resp:
                            raw = await resp.text()
                            try:
                                payload = json.loads(raw)
                            except Exception:
                                payload = {"success": False, "error": "BAD_REPLY",
                                           "message": f"Drip Client returned non-JSON HTTP {resp.status}: {raw[:180]}"}
                    keys_found = _extract_generated_keys(payload)
                    ok_flag = isinstance(payload, dict) and payload.get("success") is not False and payload.get("ok") is not False
                    if resp.status < 400 and ok_flag and keys_found:
                        delivered_key = "\n".join(keys_found)
                        api_response = {"status": "success", "msg": "Drip Client key generated", "key": delivered_key, "raw": payload}
                    else:
                        detail = (payload.get("message") or payload.get("msg") or payload.get("error")) if isinstance(payload, dict) else str(payload)
                        api_response = {"status": "error", "msg": str(detail or f"Drip Client API returned HTTP {resp.status}")}
            except Exception as api_exc:
                logger.exception("Drip Client API purchase failed")
                api_response = {"status": "error", "msg": f"Drip Client API request failed: {api_exc}"}
            if api_response.get("status") != "success":
                db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
                return await call.message.edit_text(f"❌ <b>Drip Client API Error:</b> {html.escape(str(api_response.get('msg', 'Unknown error')))}\n\n💰 Your balance has been refunded.", reply_markup=back_kb("menu_shop"), parse_mode="HTML")
        elif api_provider == "adminshops":
            base = (get_setting("adminshops_api_url", "https://adminshops.com/api/v1") or "").strip().rstrip("/")
            token = (get_setting("adminshops_api_token", "") or "").strip()
            try:
                if not token:
                    api_response = {"status": "error", "msg": "Admin Shops Bearer token is not configured by admin."}
                elif not str(external_product_id).isdigit():
                    raise ValueError("Admin Shops product_id must be numeric.")
                else:
                    idem = f"tg-{call.from_user.id}-{prod_id}-{int(time.time())}"
                    timeout = aiohttp.ClientTimeout(total=30)
                    async with aiohttp.ClientSession(timeout=timeout) as session:
                        async with session.post(base + "/generate",
                            headers={"Authorization": f"Bearer {token}", "Accept": "application/json"},
                            json={"product_id": int(external_product_id), "quantity": 1, "idempotency_key": idem}) as resp:
                            raw = await resp.text()
                            try: payload = json.loads(raw)
                            except Exception: payload = {"ok": False, "error": {"message": f"Admin Shops returned non-JSON HTTP {resp.status}: {raw[:180]}"}}
                    keys_found = _extract_generated_keys(payload)
                    ok_flag = isinstance(payload, dict) and payload.get("ok") is True
                    if resp.status < 400 and ok_flag and keys_found:
                        delivered_key = "\n".join(keys_found)
                        api_response = {"status": "success", "msg": "Admin Shops key generated", "key": delivered_key, "raw": payload}
                    else:
                        err = payload.get("error") if isinstance(payload, dict) else None
                        if isinstance(err, dict): err = err.get("message") or err.get("detail")
                        detail = err or (payload.get("message") or payload.get("msg")) if isinstance(payload, dict) else str(payload)
                        api_response = {"status": "error", "msg": str(detail or f"Admin Shops API returned HTTP {resp.status}")}
            except Exception as api_exc:
                logger.exception("Admin Shops API purchase failed")
                api_response = {"status": "error", "msg": f"Admin Shops API request failed: {api_exc}"}
            if api_response.get("status") != "success":
                db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
                return await call.message.edit_text(f"❌ <b>Admin Shops API Error:</b> {html.escape(str(api_response.get('msg', 'Unknown error')))}\n\n💰 Your balance has been refunded.", reply_markup=back_kb("menu_shop"), parse_mode="HTML")
        elif api_provider == "panelstore":
            # PanelStore API: POST JSON with key/action/pid/quantity/custom_notes.
            try:
                ps_url = (get_setting("panelstore_api_url", "https://panelstore.shop/api/v1/index.php") or "").strip()
                ps_key = (get_setting("panelstore_api_key", "") or "").strip()
                if not ps_key:
                    api_response = {"status": "error", "msg": "PanelStore API key is not configured by admin."}
                elif not str(external_product_id).strip():
                    api_response = {"status": "error", "msg": "PanelStore PID is missing. Edit this product and set its API product ID."}
                else:
                    timeout = aiohttp.ClientTimeout(total=20)
                    async with aiohttp.ClientSession(timeout=timeout) as session:
                        async with session.post(ps_url, json={"key": ps_key, "action": "order", "pid": str(external_product_id), "quantity": 1, "custom_notes": f"Telegram user {call.from_user.id}"}, timeout=timeout) as resp:
                            raw = await resp.text()
                            try: payload = json.loads(raw)
                            except Exception: payload = {"status": "error", "message": f"PanelStore returned non-JSON HTTP {resp.status}: {raw[:200]}"}
                    if resp.status < 400 and isinstance(payload, dict) and str(payload.get("status", "")).lower() == "success" and payload.get("license_key"):
                        delivered_key = str(payload.get("license_key"))
                        api_response = {"status": "success", "msg": "PanelStore key generated", "key": delivered_key, "order_code": payload.get("order_code", ""), "remaining_balance": payload.get("remaining_balance", ""), "raw": payload}
                    else:
                        api_response = {"status": "error", "msg": str(payload.get("message") or payload.get("msg") or f"PanelStore API returned HTTP {resp.status}") if isinstance(payload, dict) else "Invalid PanelStore response"}
            except asyncio.TimeoutError:
                api_response = {"status": "error", "_ambiguous": True, "msg": "PanelStore timed out. Provider may have accepted the order; admin must check provider order history before retrying."}
            except Exception as api_exc:
                logger.exception("PanelStore API purchase failed")
                api_response = {"status": "error", "_ambiguous": True, "msg": f"PanelStore connection result is uncertain: {api_exc}. Check provider order history before retrying."}
        elif api_provider == "whitex":
            # WhiteX Mode API uses variant_id + quantity and X-API-Token authentication.
            try:
                if not _whitex_token():
                    api_response = {"status": "error", "msg": "WhiteX Mode API token is not configured by admin."}
                elif not str(external_product_id).isdigit():
                    api_response = {"status": "error", "msg": "WhiteX variant_id must be numeric."}
                else:
                    payload = await whitex_api_call("generate_key.php", "POST", {"variant_id": int(external_product_id), "quantity": 1})
                    keys_found = _extract_generated_keys(payload)
                    declared_ok = isinstance(payload, dict) and (payload.get("success") is True or payload.get("ok") is True or str(payload.get("status", "")).lower() in {"success", "ok", "completed"})
                    if declared_ok and keys_found:
                        delivered_key = "\n".join(keys_found)
                        api_response = {"status": "success", "msg": "WhiteX key generated", "key": delivered_key, "raw": payload}
                    else:
                        detail = payload.get("message") or payload.get("msg") or payload.get("error") or payload.get("help") or "WhiteX did not return a generated key."
                        api_response = {"status": "error", "msg": str(detail)}
            except Exception as api_exc:
                logger.exception("WhiteX API purchase failed")
                api_response = {"status": "error", "msg": f"WhiteX API request failed: {api_exc}"}
        else:
            # Bunty (AdminPanels) API flow
            api_duration_saved = (prod[12] or "").strip()
            validity_saved = (prod[4] or "").strip()
            name_saved = (prod[0] or "").strip()

            raw_candidates = [c for c in (api_duration_saved, validity_saved, name_saved) if c]
            duration_candidates = []

            def add_candidate(val):
                val = str(val or "").strip()
                if val and val not in duration_candidates:
                    duration_candidates.append(val)

            for c in raw_candidates:
                add_candidate(c)
                add_candidate(normalize_api_duration(c))
                c_days = re.sub(r'\b(day|days)\b', 'DaYs', c, flags=re.IGNORECASE)
                add_candidate(c_days)
                c_upper = c.upper()
                add_candidate(c_upper)

            api_response = {"status": "error", "msg": "No API duration configured"}
            api_duration_used = ""
            for api_duration in duration_candidates:
                try:
                    logger.info("Trying Bunty API duration=%r for product_id=%r", api_duration, external_product_id)
                    api_response = await fetch_external_key(external_product_id, api_duration, "")
                except Exception as api_exc:
                    logger.exception("Bunty API purchase call crashed")
                    api_response = {"status": "error", "msg": f"API call failed: {api_exc}"}

                if api_response.get("status") == "success":
                    api_duration_used = api_duration
                    break

                error_blob = json.dumps(api_response, ensure_ascii=False).lower()
                retry_keywords = ["out of stock", "price not found", "price_not_found", "duration", "not found", "invalid"]
                if not any(k in error_blob for k in retry_keywords):
                    break

        if api_response.get("status") != "success":
            ambiguous = bool(api_response.get("_ambiguous"))
            if not ambiguous:
                db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
            error_msg = api_response.get("msg", "Unknown API error")
            error_label = "PanelStore" if api_provider == "panelstore" else ("WhiteX Mode" if api_provider == "whitex" else ("HK Tamim" if api_provider == "hk_tamim" else ("License Manager" if api_provider == "license_manager" else "Bunty")))
            refund_text = "⚠️ Provider result is uncertain; balance was held while admin checks order history. Do not retry yet." if ambiguous else "💰 Your balance has been refunded."
            error_text = f"❌ <b>{error_label} API Error:</b> {html.escape(str(error_msg))}\n\n{refund_text}"
            try:
                await call.message.edit_text(
                    error_text,
                    reply_markup=back_kb("menu_shop"),
                    parse_mode='HTML'
                )
            except Exception as tg_error:
                logger.exception("Could not edit purchase message after API failure: %s", tg_error)
                try:
                    await bot.send_message(
                        call.from_user.id,
                        error_text,
                        reply_markup=back_kb("menu_shop"),
                        parse_mode='HTML'
                    )
                except Exception:
                    pass
            return

        delivered_key = api_response.get("key")
        if isinstance(delivered_key, list):
            delivered_key = "\n".join(str(x) for x in delivered_key)
        if delivered_key is None or str(delivered_key).strip() in ("", "KEY_NOT_FOUND"):
            db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
            return await call.message.edit_text("❌ Bunty API returned no key.\n\n💰 Your balance has been refunded.", reply_markup=back_kb("menu_shop"), parse_mode='HTML')
        delivered_key = str(delivered_key)        # External API products are not limited by local key-vault stock.
        # Keep the admin-entered display stock unchanged so the product never
        # becomes "Out of Stock" after a successful API purchase.
    else:
        db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (final_price, call.from_user.id))
        return await call.message.edit_text("❌ No manual key is available.\n\n💰 Your balance has been refunded.", reply_markup=back_kb("menu_shop"), parse_mode='HTML')

    if user[1]:
        try:
            referral_percent = float(get_setting("referral_commission_percent", "15") or 15)
        except (TypeError, ValueError):
            referral_percent = 15.0
        referral_percent = max(0.0, min(100.0, referral_percent))
        commission = final_price * referral_percent / 100.0
        db_query("UPDATE users SET balance=balance+?, referral_earned=referral_earned+? WHERE user_id=?", (commission, commission, user[1]))
        try:
            await bot.send_message(user[1], f"🎁 <b>Referral Bonus Added!</b>\nYou earned {fmt_curr(commission)} from a successful purchase.", parse_mode='HTML')
        except Exception:
            pass

    product_full_name = f"{prod[6]} - {prod[8]} ({prod[0]})"
    db_query("INSERT INTO orders (user_id, product_name, price_paid, delivered_key, purchase_date) VALUES (?, ?, ?, ?, ?)",
             (call.from_user.id, product_full_name, final_price, delivered_key, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    log_activity(call.from_user.id, "PURCHASE_SUCCESS", f"Product: {product_full_name}, Paid: {final_price}, External API: {external_enabled}")
    await send_advanced_notification(call.from_user.id, "ORDER", final_price, product=product_full_name, key=delivered_key)
    try:
        await send_payment_proof_channel(
            call.from_user.id, product_full_name, final_price,
            order_id=str(db_query("SELECT id FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 1", (call.from_user.id,), fetchone=True)[0])
                if db_query("SELECT id FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 1", (call.from_user.id,), fetchone=True) else "",
            api_response=api_response if external_enabled else None
        )
    except Exception:
        logger.exception("Payment proof channel notification failed")

    msg = (f"✅ <b>PURCHASE SUCCESSFUL!</b>\n━━━━━━━━━━━━━━━━━━\n"
           f"📦 <b>Panel:</b> {prod[6]}\n📁 <b>Panel Name:</b> {prod[8]}\n"
           f"⏱ <b>Package:</b> {prod[0]}\n💰 <b>Amount Deducted:</b> {fmt_curr(final_price)}\n"
           f"📱 <b>Device Limit:</b> {prod[5]}\n━━━━━━━━━━━━━━━━━━\n")
    if prod[3] and prod[3].startswith("http"):
        msg += f"📥 <b>APK Link:</b> <a href='{prod[3]}'>Click Here to Download</a>\n\n"
    msg += f"🔑 <b>Your Exclusive Key:</b>\n<code>{delivered_key}</code>\n\n"
    if external_enabled and api_response:
        if api_response.get("product"):
            msg += f"📌 <b>Product:</b> {api_response['product']}\n"
        if api_response.get("duration"):
            msg += f"⏳ <b>Duration:</b> {api_response['duration']}\n"
        if api_response.get("order_id"):
            msg += f"🧾 <b>Order ID:</b> <code>{api_response['order_id']}</code>\n"
        if api_response.get("expires_at"):
            msg += f"⏰ <b>Expires:</b> <code>{api_response['expires_at']}</code>\n"
    msg += f"\n<i>For any issues, tap Support or contact: {ADMIN_CONTACT}</i>"
    await call.message.edit_text(msg, reply_markup=back_kb("menu_shop"), disable_web_page_preview=True, parse_mode='HTML')

# ==============================================================================
# 14. USER DASHBOARD, FILES, VIP, RESELLER, ORDERS, PROFILE, REFERRAL
# ==============================================================================
@dp.callback_query(F.data == "menu_top_buyers")
async def top_buyers_leaderboard(call: CallbackQuery):
    """Show the five users with the highest value of successfully completed purchases."""
    reset_at = get_setting("top_sellers_reset_at", "1970-01-01 00:00:00") or "1970-01-01 00:00:00"
    rows = db_query(
        """
        SELECT u.user_id, u.first_name, u.username,
               COUNT(o.id) AS buy_count,
               COALESCE(SUM(o.price_paid), 0) AS total_bought
        FROM orders o
        JOIN users u ON u.user_id = o.user_id
        WHERE COALESCE(o.purchase_date, '') > ?
        GROUP BY u.user_id, u.first_name, u.username
        ORDER BY total_bought DESC, buy_count DESC, u.user_id ASC
        LIMIT 5
        """,
        (reset_at,),
        fetchall=True
    ) or []

    medals = ["🥇", "🥈", "🥉", "🏅", "🎖️"]
    lines = [
        "🏆 <b><u>TOP 5 BUYERS LEADERBOARD</u></b> 🏆",
        "━━━━━━━━━━━━━━━━━━",
        "<i>Ranked by total successful purchase value.</i>",
        ""
    ]

    if not rows:
        lines.append("📭 <b>No completed purchases yet.</b>")
    else:
        for idx, row in enumerate(rows, 1):
            user_id, first_name, username, buy_count, total_bought = row
            safe_name = html.escape(str(first_name or "User"))
            lines.extend([
                f"{medals[idx - 1]} <b>TOP {idx}</b> — {safe_name}",
                f"👤 <b>Name:</b> {safe_name}",
                f"🛒 <b>Total Bought:</b> {int(buy_count)} order(s)",
                f"💰 <b>Total Invested:</b> {fmt_curr(float(total_bought or 0))}",
                "━━━━━━━━━━━━━━━━━━"
            ])

    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(
            text="🔄 Refresh Leaderboard", callback_data="menu_top_buyers",
            icon_custom_emoji_id=get_emoji_icon("global_stats")
        )],
        [InlineKeyboardButton(
            text="BACK", callback_data="back_main",
            icon_custom_emoji_id=get_emoji_icon("back")
        )]
    ])
    await call.message.edit_text("\n".join(lines), reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_reset_top_sellers")
async def admin_reset_top_sellers(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return
    reset_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    set_setting("top_sellers_reset_at", reset_at)
    log_activity(call.from_user.id, "ADMIN_RESET_TOP_SELLERS", f"Reset leaderboard at {reset_at}")
    await call.answer("🏆 Top Sellers reset. New purchases will start a fresh leaderboard.", show_alert=True)
    await call.message.edit_text(
        f"🏆 <b>TOP SELLERS RESET</b>\n\n"
        f"Leaderboard reset time: <code>{reset_at}</code>\n"
        "Previous purchase history is preserved; only the leaderboard window was reset.",
        reply_markup=admin_kb(), parse_mode="HTML"
    )

@dp.callback_query(F.data == "menu_payment_proof")
async def payment_proof_menu(call: CallbackQuery):
    channel = (get_setting("payment_proof_channel", "") or "").strip()
    if not channel or channel.lower() in ("none", "off", "disabled"):
        return await call.answer("⚠️ Payment Proof channel is not configured yet.", show_alert=True)
    link = channel
    if link.startswith("@"):
        link = "https://t.me/" + link[1:]
    elif not link.startswith(("http://", "https://")):
        link = "https://t.me/" + link.lstrip("@")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🧾 Open Payment Proof Channel ↗️", url=link)]
    ])
    await call.message.edit_text(
        "🧾 <b>PAYMENT PROOF</b>\n\n"
        "Here you can view successful purchase proofs.\n"
        "🔐 Delivered keys are never posted in the public channel.",
        reply_markup=kb, parse_mode="HTML"
    )

@dp.callback_query(F.data == "menu_all_files")
async def all_files_handler(call: CallbackQuery):
    link_q = db_query("SELECT value FROM settings WHERE key='all_files_link'", fetchone=True)
    link = link_q[0] if link_q and link_q[0] != 'None' else None
    if link:
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="Access Download Channel ↗️", url=link, icon_custom_emoji_id=get_emoji_icon("download"))],
            [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]
        ])
        text = get_ui_text("download_files")
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
    else:
        await call.answer("⚠️ Admin has not configured the private download channel link yet.", show_alert=True)

@dp.callback_query(F.data == "menu_vip_dash")
async def vip_dashboard(call: CallbackQuery):
    u = db_query("SELECT balance, is_vip, vip_since FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    is_vip = bool(u[1])
    status_str = "🟢 Active (Lifetime)" if is_vip else "🔴 Not Subscribed"
    text = get_ui_text("vip_menu", vip_status=status_str)
    kb = make_inline_kb(inline_keyboard=[])
    if is_vip:
        text += f"\n📅 <b>Member Since:</b> {u[2]}\n\nEnjoy your permanent 15% discount!"
    else:
        text += f"\n\n💳 <b>Your Current Balance:</b> {fmt_curr(u[0])}\n"
        if u[0] >= VIP_PRICE_INR: 
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"✅ Purchase VIP for {fmt_curr(VIP_PRICE_INR)}", callback_data="execute_vip_upgrade", icon_custom_emoji_id=get_emoji_icon("vip"))])
        else:
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"❌ Need {fmt_curr(VIP_PRICE_INR)} to Upgrade", callback_data="ignore_stock_click")])
            kb.inline_keyboard.append([InlineKeyboardButton(text="Add Balance Now", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("add_balance"))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "execute_vip_upgrade")
async def execute_vip_upgrade(call: CallbackQuery):
    u = db_query("SELECT balance, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if u[1]: return await call.answer("⚠️ You are already a VIP Member!", show_alert=True)
    if u[0] < VIP_PRICE_INR: return await call.answer(f"❌ Your balance dropped below {VIP_PRICE_INR}.", show_alert=True)
    new_balance = u[0] - VIP_PRICE_INR
    now_date = datetime.now().strftime("%Y-%m-%d")
    db_query("UPDATE users SET balance=?, is_vip=1, vip_since=? WHERE user_id=?", (new_balance, now_date, call.from_user.id))
    log_activity(call.from_user.id, "UPGRADED_VIP")
    await notify_admins(f"🌟 <b>NEW VIP UPGRADE</b>\n👤 User ID: <code>{call.from_user.id}</code>")
    await call.answer("🎉 Upgrade Successful! You are now a VIP Member.", show_alert=True)
    await vip_dashboard(call)

@dp.callback_query(F.data == "menu_reseller_dash")
async def reseller_dashboard(call: CallbackQuery):
    u = db_query("SELECT balance, is_reseller, reseller_since, total_saved FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    status_check = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    system_status = status_check[0] if status_check else "ON"
    if str(system_status).upper() != "ON":
        return await call.answer("⚠️ Reseller system is OFF by admin.", show_alert=True)
    setup_fee = float(get_setting("reseller_setup_fee", "200.0"))
    min_balance = float(get_setting("reseller_min_balance", "500.0"))
    if u[1]: 
        reseller_description = get_ui_text("reseller") or "You are enjoying exclusive wholesale prices on all products."
        text = (f"{get_emoji('shield_icon')} <b><u>— RESELLER DASHBOARD —</u></b> {get_emoji('shield_icon')}\n\n🟢 <b>Status:</b> Active\n📅 <b>Since:</b> {u[2]}\n{get_emoji('money_icon')} <b>Total Saved:</b> {fmt_curr(u[3])}\n\n{reseller_description}")
        kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]])
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
        return
    if system_status == "OFF": return await call.answer("⚠️ Wholesale / Reseller registrations are currently closed by Admin.", show_alert=True)
    text = (f"⚡ <b><u>— BECOME A RESELLER —</u></b> ⚡\n\nUpgrade your account to access wholesale <b>Reseller Prices</b>!\n\n📋 <b>Requirements to Upgrade:</b>\n1️⃣ Must have a minimum balance of <b>{fmt_curr(min_balance)}</b>.\n2️⃣ A one-time setup fee of <b>{fmt_curr(setup_fee)}</b> will be deducted.\n\n💳 <b>Your Current Balance:</b> {fmt_curr(u[0])}\n")
    kb = make_inline_kb(inline_keyboard=[])
    if u[0] >= min_balance: 
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"✅ Pay {fmt_curr(setup_fee)} & Become Reseller", callback_data="execute_reseller_upgrade", icon_custom_emoji_id=get_emoji_icon("reseller"))])
    else:
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"❌ Insufficient Balance (Need {fmt_curr(min_balance)})", callback_data="ignore_stock_click")])
        kb.inline_keyboard.append([InlineKeyboardButton(text="Add Balance", callback_data="menu_add_balance", icon_custom_emoji_id=get_emoji_icon("add_balance"))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "execute_reseller_upgrade")
async def execute_reseller_upgrade(call: CallbackQuery):
    setup_fee = float(get_setting("reseller_setup_fee", "200.0"))
    min_balance = float(get_setting("reseller_min_balance", "500.0"))
    u = db_query("SELECT balance, is_reseller FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if u[1]: return await call.answer("⚠️ You are already a Reseller!", show_alert=True)
    if u[0] < min_balance: return await call.answer(f"❌ Your balance dropped below {fmt_curr(min_balance)}. Please top up.", show_alert=True)
    new_balance = u[0] - setup_fee
    db_query("UPDATE users SET balance=?, is_reseller=1, reseller_since=?, account_type='Reseller' WHERE user_id=?", (new_balance, datetime.now().strftime("%Y-%m-%d"), call.from_user.id))
    log_activity(call.from_user.id, "UPGRADED_RESELLER")
    await notify_admins(f"👑 <b>NEW RESELLER UPGRADE</b>\n👤 User ID: <code>{call.from_user.id}</code>")
    await call.answer("🎉 Upgrade Successful! Welcome to the Reseller tier.", show_alert=True)
    await reseller_dashboard(call)

@dp.callback_query(F.data == "menu_orders")
async def my_orders(call: CallbackQuery):
    orders = db_query("SELECT product_name, delivered_key, purchase_date, price_paid FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 10", (call.from_user.id,), fetchall=True)
    description = get_ui_text("orders") or "Your previous orders and their current status are shown here."
    guild_orders = db_query("SELECT group_id, clan_id, region_name, amount, status, created_at FROM ffglorypro_orders WHERE user_id=? ORDER BY id DESC LIMIT 10", (call.from_user.id,), fetchall=True) or []
    if not orders and not guild_orders:
        text = f"🧾 <b><u>— YOUR ORDER HISTORY —</u></b> 🧾\n\n{description}\n\nYou haven't made any purchases yet."
        return await call.message.edit_text(text, reply_markup=back_kb(), parse_mode='HTML')
    text = f"🧾 <b><u>— YOUR RECENT ORDERS —</u></b> 🧾\n\n{description}\n\n"
    for o in orders:
        text += f"📦 <b>{html.escape(str(o[0] or 'Product'))}</b> ({fmt_curr(o[3])})\n🔑 <code>{html.escape(str(o[1] or ''))}</code>\n📅 <i>{html.escape(str(o[2] or ''))}</i>\n━━━━━━━━━━━━━━━━\n"
    for g in guild_orders:
        text += f"🏆 <b>Guild Glory</b> — ₹{float(g[3] or 0):g}\nClan: <code>{html.escape(str(g[1]))}</code> | Region: {html.escape(str(g[2]))}\nGroup: <code>{html.escape(str(g[0]))}</code> | Status: <b>{html.escape(str(g[4]))}</b>\n📅 {html.escape(str(g[5]))}\n━━━━━━━━━━━━━━━━\n"
    await call.message.edit_text(text[:3900], reply_markup=back_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "menu_profile")
async def show_profile(call: CallbackQuery):
    u = db_query("SELECT user_id, first_name, account_type, balance, orders_count, spent, referrals_count, joined_date, is_reseller, reseller_since, total_saved, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    acc_type_display = []
    if u[8]: acc_type_display.append(f"{get_emoji('reseller')} Reseller")
    if u[11]: acc_type_display.append(f"{get_emoji('vip')} VIP")
    type_str = " | ".join(acc_type_display) if acc_type_display else f"{get_emoji('regular_user')} Regular User"
    text = (
        f"{get_emoji('grid_id')} <b><u>— YOUR SECURE PROFILE —</u></b> {get_emoji('grid_id')}\n\n"
        f"{get_emoji('grid_id')} <b>Grid ID:</b> <code>{u[0]}</code>\n"
        f"{get_emoji('name')} <b>Name:</b> {u[1]}\n"
        f"{get_emoji('account_level')} <b>Account Level:</b> {type_str}\n\n"
        f"{get_emoji('wallet_left')} <b>— Wallet —</b> {get_emoji('wallet_right')}\n"
        f"{get_emoji('wallet_left')} <b>Current Balance:</b> {fmt_curr(u[3])} {get_emoji('wallet_right')}\n\n"
        f"{get_emoji('global_stats')} <b>— Global Statistics —</b>\n"
        f"{get_emoji('total_orders')} <b>Total Orders:</b> {u[4]}\n"
        f"{get_emoji('total_spent')} <b>Total Spent:</b> {fmt_curr(u[5])}\n"
        f"{get_emoji('total_referrals')} <b>Total Referrals:</b> {u[6]}\n\n"
    )
    if u[8]:
        text += f"{get_emoji('shield_icon')} <b>— RESELLER METRICS —</b> {get_emoji('shield_icon')}\n{get_emoji('money_icon')} <b>Total Saved via Reseller:</b> {fmt_curr(u[10])}\n\n"
    text += f"{get_emoji('joined_grid')} <b>Joined Grid:</b> {u[7]}"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(
            text="Redeem Promo Code",
            callback_data="redeem_coupon",
            icon_custom_emoji_id=get_emoji_icon('redeem_icon')
        )],
        [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "redeem_coupon")
async def redeem_coupon_start(call: CallbackQuery, state: FSMContext):
    await call.message.edit_text("🎟 <b>Please enter your VIP / Promo redeem code below:</b>", reply_markup=back_kb("menu_profile"), parse_mode='HTML')
    await state.set_state(UserStates.wait_for_redeem)

@dp.message(UserStates.wait_for_redeem)
async def process_redeem(m: Message, state: FSMContext):
    code = m.text.strip().upper()
    user_id = m.from_user.id
    if db_query("SELECT * FROM redeemed WHERE user_id=? AND code=?", (user_id, code), fetchone=True):
        await m.answer("❌ Anti-Fraud Alert: You already redeemed this unique code!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
        await state.clear()
        return
    coupon = db_query("SELECT amount, uses_left FROM coupons WHERE code=?", (code,), fetchone=True)
    if not coupon: await m.answer("❌ Invalid or Expired Code!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    elif coupon[1] <= 0: await m.answer("❌ This code's usage limit has been fully claimed by other users.", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    else:
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (coupon[0], user_id))
        db_query("UPDATE coupons SET uses_left = uses_left - 1 WHERE code=?", (code,))
        db_query("INSERT INTO redeemed (user_id, code) VALUES (?, ?)", (user_id, code))
        log_activity(user_id, "PROMO_REDEEMED", f"Code: {code}, Amount: {coupon[0]}")
        await m.answer(f"🎉 <b>Success!</b>\nSafely added {fmt_curr(coupon[0])} to your balance!", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
        user_info = db_query("SELECT first_name FROM users WHERE user_id=?", (user_id,), fetchone=True)
        uname = user_info[0] if user_info else "Unknown User"
        await notify_admins(f"🎟 <b>PROMO CODE REDEEMED!</b>\n👤 User: {uname} (<code>{user_id}</code>)\n🔖 Code: <b>{code}</b>\n💵 Amount: {fmt_curr(coupon[0])}")
    await state.clear()

@dp.callback_query(F.data == "menu_referral")
async def show_referral(call: CallbackQuery):
    try:
        live_bot = await bot.get_me()
        live_username = (live_bot.username or bot_username_clean()).lstrip("@")
    except Exception:
        live_username = bot_username_clean()
    ref_link = f"https://t.me/{live_username}?start=ref_{call.from_user.id}"
    description = get_ui_text("referral") or "✨ Invite friends and earn commission on their successful purchases!"
    commission = get_setting("referral_commission_percent", "15") or "15"
    text = (
        f"{get_emoji('referral')} <b><u>REFERRAL PROGRAM</u></b> {get_emoji('referral')}\n\n"
        f"{description}\n\n"
        f"💎 <b>YOUR COMMISSION: {html.escape(str(commission))}%</b> 💰\n"
        f"<i>Earn commission when your invited users make eligible purchases.</i>\n\n"
        f"🔗 <b>YOUR REFERRAL LINK</b>\n<code>{html.escape(ref_link)}</code>"
    )
    kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

# ==============================================================================
# 15. LUDO / DICE SPIN
# ==============================================================================
@dp.callback_query(F.data == "menu_spin_landing")
async def lucky_spin_landing(call: CallbackQuery):
    status_check = db_query("SELECT value FROM settings WHERE key='spin_status'", fetchone=True)
    spin_status = status_check[0] if status_check else "ON"
    if spin_status == "OFF": return await call.answer("⚠️ Lucky Ludo Spin is currently disabled by Admin.", show_alert=True)
    await call.message.edit_text(f"{get_emoji('ludo_spin')} <b><u>— LUDO SPIN —</u></b> {get_emoji('ludo_spin')}\n\nTest your luck! You can spin once every 24 hours.", reply_markup=make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Spin Dice Now!", callback_data="execute_spin", icon_custom_emoji_id=get_emoji_icon("ludo_spin"))], 
        [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]
    ]), parse_mode='HTML')

@dp.callback_query(F.data == "execute_spin")
async def execute_spin(call: CallbackQuery):
    status_check = db_query("SELECT value FROM settings WHERE key='spin_status'", fetchone=True)
    if status_check and status_check[0] == "OFF": return await call.answer("⚠️ Lucky Spin is disabled.", show_alert=True)
    u = db_query("SELECT last_spin, balance, is_vip FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not u:
        return await call.answer("❌ Account not found. Please use /start first.", show_alert=True)
    now = datetime.now()
    last_spin = u[0]
    balance = float(u[1]) if u[1] is not None else 0.0
    is_vip = bool(u[2])
    if last_spin:
        try:
            last_spin_dt = datetime.strptime(last_spin, "%Y-%m-%d %H:%M:%S")
            if now < last_spin_dt + timedelta(hours=24):
                remaining = last_spin_dt + timedelta(hours=24) - now
                hrs = int(remaining.total_seconds() // 3600)
                mins = int((remaining.total_seconds() % 3600) // 60)
                return await call.message.edit_text(
                    f"❌ <b>Cooldown Active!</b>\nYou already played today.\n\n"
                    f"⏳ Come back in <b>{hrs}h {mins}m</b>!",
                    reply_markup=back_kb(), parse_mode='HTML'
                )
        except Exception:
            pass
    await call.message.delete()
    dice_msg = await bot.send_dice(chat_id=call.message.chat.id, emoji="🎲")
    await asyncio.sleep(SPIN_DELAY_SECONDS)
    dice_val = dice_msg.dice.value
    today = now.strftime("%Y-%m-%d")
    pool_row = db_query("SELECT value FROM settings WHERE key='daily_spin_pool'", fetchone=True)
    spent_row = db_query("SELECT value FROM settings WHERE key='daily_spin_spent'", fetchone=True)
    spent_date_row = db_query("SELECT value FROM settings WHERE key='daily_spin_spent_date'", fetchone=True)
    daily_pool = max(0.0, float(pool_row[0]) if pool_row and pool_row[0] is not None else 5.0)
    spent_today = float(spent_row[0]) if spent_row and spent_row[0] is not None else 0.0
    saved_date = spent_date_row[0] if spent_date_row else ""
    if saved_date != today:
        spent_today = 0.0
        set_setting("daily_spin_spent", "0.0")
        set_setting("daily_spin_spent_date", today)
    remaining_pool = max(0.0, round(daily_pool - spent_today, 2))

    # Pick only rewards that can actually fit inside the remaining global pool.
    # VIP 2x is also capped by the same pool, so total payouts can never exceed it.
    max_base_reward = remaining_pool / 2.0 if is_vip else remaining_pool
    rewards_db = db_query("SELECT amount FROM spin_rewards WHERE amount >= 0 AND amount <= ?", (max_base_reward,), fetchall=True)
    rewards_list = [float(r[0]) for r in rewards_db] if rewards_db else [0.0]
    reward = float(random.choice(rewards_list))
    if is_vip and reward > 0:
        reward *= 2.0
    reward = min(round(reward, 2), remaining_pool)
    spent_today = round(spent_today + reward, 2)
    set_setting("daily_spin_spent", f"{spent_today:.2f}")
    set_setting("daily_spin_spent_date", today)
    new_bal = balance + reward
    db_query("UPDATE users SET balance=?, last_spin=? WHERE user_id=?", (new_bal, now.strftime("%Y-%m-%d %H:%M:%S"), call.from_user.id))
    log_activity(call.from_user.id, "PLAYED_SPIN", f"Reward: {reward}, Dice: {dice_val}")
    msg = get_ui_text("lucky_dice_result", dice_value=dice_val, won_amount=fmt_curr(reward), new_balance=fmt_curr(new_bal))
    if is_vip and reward > 0: msg += "\n\n<i>🌟 VIP Bonus: 2x Multiplier Applied!</i>"
    await dice_msg.reply(msg, reply_markup=make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="BACK TO MENU", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]]), parse_mode='HTML')

# ==============================================================================
# 16. TUTORIALS & SUPPORT
# ==============================================================================
@dp.callback_query(F.data == "menu_how_to")
async def tutorial_system(call: CallbackQuery):
    video_link_query = db_query("SELECT value FROM settings WHERE key='how_to_video'", fetchone=True)
    video_link = video_link_query[0] if video_link_query and video_link_query[0] != 'None' else None
    description = get_ui_text("how_to") or "1. Add funds via Add Balance.\n2. Open Product Store.\n3. Choose a category and plan.\n4. Follow the payment instructions to receive your order."
    text = f"{get_emoji('tutorial')} <b><u>— HOW TO USE —</u></b> {get_emoji('tutorial')}\n\n{description}"
    kb = make_inline_kb(inline_keyboard=[])
    if video_link: kb.inline_keyboard.append([InlineKeyboardButton(text="Watch Full Video Tutorial", url=video_link, icon_custom_emoji_id=get_emoji_icon("tutorial"))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "menu_support")
async def support_center(call: CallbackQuery):
    telegram_link = get_setting("support_telegram", "https://t.me/rajuconfigyt")
    whatsapp_link = get_setting("support_whatsapp", "https://wa.me/YOUR_NUMBER")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Contact on Telegram", url=telegram_link, icon_custom_emoji_id=get_emoji_icon("telegram"))],
        [InlineKeyboardButton(text="Contact on WhatsApp", url=whatsapp_link, icon_custom_emoji_id=get_emoji_icon("whatsapp"))],
        [InlineKeyboardButton(text="Open New Ticket", callback_data="open_ticket", icon_custom_emoji_id=get_emoji_icon("support")), 
         InlineKeyboardButton(text="My Open Tickets", callback_data="my_tickets", icon_custom_emoji_id=get_emoji_icon("history"))], 
        [InlineKeyboardButton(text="BACK", callback_data="back_main", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text(f"{get_emoji('telegram')}{get_emoji('whatsapp')} <b><u>— PREMIUM SUPPORT CENTER —</u></b>\n\nContact us via Telegram or WhatsApp for instant help, or open a support ticket for admin assistance.", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "my_tickets")
async def view_my_tickets(call: CallbackQuery):
    tickets = db_query("SELECT id, message, status, created_at FROM tickets WHERE user_id=? ORDER BY id DESC LIMIT 5", (call.from_user.id,), fetchall=True)
    if not tickets: return await call.message.edit_text("📋 You do not have any active or previous support tickets.", reply_markup=back_kb("menu_support"), parse_mode='HTML')
    text = "📋 <b><u>— Your Recent Tickets —</u></b> 📋\n\n"
    for t in tickets:
        status_icon = "🟢" if t[2] == 'Open' else "🔴"
        text += f"🎫 <b>Ticket #{t[0]}</b> | Status: {status_icon} <b>{t[2]}</b>\n📅 <i>{t[3]}</i>\n📝 <i>{t[1][:80]}...</i>\n\n"
    await call.message.edit_text(text, reply_markup=back_kb("menu_support"), parse_mode='HTML')

@dp.callback_query(F.data == "open_ticket")
async def open_ticket_start(call: CallbackQuery, state: FSMContext):
    await call.message.edit_text("📝 <b>Please type your issue/message below in detail:</b>", reply_markup=back_kb("menu_support"), parse_mode='HTML')
    await state.set_state(UserStates.wait_for_ticket)

@dp.message(UserStates.wait_for_ticket)
async def process_ticket(m: Message, state: FSMContext):
    db_query("INSERT INTO tickets (user_id, message, created_at) VALUES (?, ?, ?)", (m.from_user.id, m.text, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
    await m.answer("✅ <b>Ticket Submitted Successfully!</b> Admins will reply soon.", reply_markup=main_menu_kb(m.from_user.id), parse_mode='HTML')
    await notify_admins(f"🚨 <b>NEW SUPPORT TICKET</b>\nFrom: <code>{m.from_user.id}</code>\nMsg: {m.text}")
    log_activity(m.from_user.id, "OPENED_TICKET")
    await state.clear()

# ==============================================================================
# 17. ADMIN PANEL
# ==============================================================================
def _read_recent_log_lines(errors_only: bool = False, limit: int = 80) -> str:
    """Read recent local bot logs for admins, with basic secret redaction."""
    log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot_activity.log")
    try:
        with open(log_path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()[-1200:]
    except FileNotFoundError:
        return "No log file yet. Start the bot and try again."
    except Exception as exc:
        logger.exception("Could not read log file for admin viewer")
        return f"Log read failed: {type(exc).__name__}: {exc}"
    if errors_only:
        needles = (" ERROR ", " CRITICAL ", " EXCEPTION ", "Traceback", "FAILED", "failed", "Error:", "error:")
        lines = [line for line in lines if any(n in line for n in needles)]
    if not lines:
        return "No matching errors found in the recent log window." if errors_only else "The log file is currently empty."
    text = "".join(lines[-limit:])
    # Avoid exposing API credentials accidentally written by provider exceptions.
    import re as _re
    text = _re.sub(r"(?i)(authorization\s*[:=]\s*bearer\s+)[^\s,;]+", r"\1[REDACTED]", text)
    text = _re.sub(r"(?i)(api[_-]?key\s*[=:]\s*)[^\s,;&]+", r"\1[REDACTED]", text)
    text = _re.sub(r"(?i)(x-api-key\s*[:=]\s*)[^\s,;]+", r"\1[REDACTED]", text)
    text = _re.sub(r"(?i)(token\s*[=:]\s*)[^\s,;]+", r"\1[REDACTED]", text)
    # Telegram messages have a hard 4096-character limit; leave room for wrapper.
    return text[-3000:]

async def _send_admin_logs(call: CallbackQuery, errors_only: bool = False):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    await call.answer("Loading logs…")
    content = _read_recent_log_lines(errors_only=errors_only)
    title = "🚨 <b>RECENT ERROR LOGS</b>" if errors_only else "📜 <b>RECENT BOT LOGS</b>"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="📜 All Logs", callback_data="admin_logs_view"), InlineKeyboardButton(text="🚨 Errors Only", callback_data="admin_logs_errors")],
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_logs_errors" if errors_only else "admin_logs_view")],
        [InlineKeyboardButton(text="⬅️ Back to Admin", callback_data="admin_panel_back")]
    ], _width=2)
    body = title + "\n<pre>" + html.escape(content) + "</pre>"
    try:
        await call.message.edit_text(body, reply_markup=kb, parse_mode="HTML")
    except TelegramBadRequest as exc:
        if "message is not modified" in str(exc).lower():
            return
        # New message fallback for inaccessible or uneditable old messages.
        await call.message.answer(body, reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_logs_view")
async def admin_logs_view(call: CallbackQuery):
    await _send_admin_logs(call, errors_only=False)

@dp.callback_query(F.data == "admin_logs_errors")
async def admin_logs_errors(call: CallbackQuery):
    await _send_admin_logs(call, errors_only=True)

def _get_dashboard_public_url() -> str:
    """Resolve the externally reachable dashboard URL from hosting configuration."""
    candidates = [
        (get_setting("dashboard_public_url", "") or "").strip(),
        os.getenv("DASHBOARD_PUBLIC_URL", "").strip(),
        os.getenv("RENDER_EXTERNAL_URL", "").strip(),
        os.getenv("RAILWAY_STATIC_URL", "").strip(),
    ]
    railway_domain = os.getenv("RAILWAY_PUBLIC_DOMAIN", "").strip()
    if railway_domain:
        candidates.append(railway_domain if railway_domain.startswith(("http://", "https://")) else "https://" + railway_domain)
    for value in candidates:
        if value:
            if not value.startswith(("http://", "https://")):
                value = "https://" + value
            # The web dashboard is served at the root path.
            return value.rstrip("/")
    return ""

async def _send_dashboard_url(message: Message, requester_id: Optional[int] = None):
    if not is_admin(requester_id if requester_id is not None else message.from_user.id):
        return
    public_url = _get_dashboard_public_url()
    password_ready = bool((get_setting("dashboard_password", "") or os.getenv("DASHBOARD_PASSWORD", "")).strip())
    if not password_ready:
        text = (
            "🖥️ <b>Web Admin Dashboard</b>\n\n"
            "Status: 🔴 Password missing — admin chat में <code>/setdashboardpassword YourStrongPassword</code> भेजें.\n"
            "Public URL के लिए hosting का असली HTTPS domain जरूरी है; port अकेले public URL नहीं होता. "
            "Railway/Render कुछ मामलों में domain environment variable से URL खुद पहचान सकता है.\n\n"
            "⚠️ सिर्फ port number public URL नहीं होता; hosting पर public domain/HTTPS और port routing भी enabled होना चाहिए."
        )
        return await message.answer(text, parse_mode="HTML")
    if not public_url:
        text = (
            "🖥️ <b>Web Admin Dashboard</b>\n\n"
            "Password: ✅ configured\nPublic URL: ⚠️ अभी hosting से detect नहीं हुआ.\n\n"
            "Hosting Environment Variables में <code>DASHBOARD_PUBLIC_URL=https://your-real-host-domain</code> सेट करो. "
            "यहाँ <code>your-real-host-domain</code> को अपने hosting dashboard से मिले असली domain से बदलना है. फिर bot restart करके <code>/dashboard</code> भेजो."
        )
        return await message.answer(text, parse_mode="HTML")
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🌐 Open Web Dashboard", url=public_url)]])
    text = (
        "🖥️ <b>Web Admin Dashboard</b>\n\n"
        f"Status: {'🟢 Password configured' if password_ready else '🔴 Password missing'}\n"
        f"Public URL: <code>{html.escape(public_url)}</code>\n\n"
        "Login username: <code>admin</code>\nPassword: admin द्वारा <code>/setdashboardpassword</code> से set किया गया password (या legacy DASHBOARD_PASSWORD).\n"
        "Bot के /admin panel से भी products, stock और FF API settings manage कर सकते हो."
    )
    await message.answer(text, reply_markup=kb, parse_mode="HTML", disable_web_page_preview=True)

@dp.message(Command("setdashboardpassword"))
async def set_dashboard_password_command(message: Message):
    if not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) != 2 or len(parts[1].strip()) < 10:
        return await message.answer("Use: <code>/setdashboardpassword YourStrongPassword</code>\nPassword कम से कम 10 characters का रखें. Command भेजने के बाद message delete कर दें.", parse_mode="HTML")
    password = parts[1].strip()
    set_setting("dashboard_password", "sha256$" + hashlib.sha256(password.encode("utf-8")).hexdigest())
    await message.answer("✅ Dashboard password database में save हो गया. अब /dashboard खोलकर username <code>admin</code> और नया password इस्तेमाल करें. Hosting restart की जरूरत नहीं.", parse_mode="HTML")

@dp.message(Command("dashboardport"))
async def dashboard_port_command(message: Message):
    if not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) == 1:
        configured = get_setting("dashboard_port", "8080") or "8080"
        runtime = os.getenv("PORT", "")
        note = f"\nHosting PORT currently overrides this setting: <code>{html.escape(runtime)}</code>." if runtime else "\nNo hosting PORT variable detected; this is the fallback port and a restart is required after changing it."
        return await message.answer(f"Current fallback dashboard port: <code>{html.escape(str(configured))}</code>{note}", parse_mode="HTML")
    try:
        port = int(parts[1].strip())
        if not 1024 <= port <= 65535: raise ValueError
    except ValueError:
        return await message.answer("Port 1024–65535 में दें. Example: <code>/dashboardport 8080</code>", parse_mode="HTML")
    set_setting("dashboard_port", str(port))
    runtime = os.getenv("PORT", "")
    if runtime:
        await message.answer(f"✅ Fallback port {port} save हुआ. लेकिन hosting का PORT={html.escape(runtime)} अभी active रहेगा; Railway पर port hosting assign करती है. बाहरी port बदलने के लिए hosting/domain settings चाहिए.", parse_mode="HTML")
    else:
        await message.answer(f"✅ Fallback port {port} save हुआ. इसे लागू करने के लिए bot restart करें.", parse_mode="HTML")

@dp.message(Command("dashboard", "dashboardurl", "adminurl"))
async def dashboard_url_command(message: Message):
    if not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) == 2:
        url = parts[1].strip().rstrip("/")
        if not re.fullmatch(r"https://[^\s<>]+", url, flags=re.IGNORECASE):
            return await message.answer("HTTPS public URL भेजें. Example: <code>/dashboardurl https://your-domain.up.railway.app</code>", parse_mode="HTML")
        set_setting("dashboard_public_url", url)
        return await message.answer("✅ Dashboard public URL saved. अब /dashboard भेजकर link देखें. Domain hosting में पहले से enabled होना चाहिए.", parse_mode="HTML")
    await _send_dashboard_url(message)

@dp.callback_query(F.data == "admin_dashboard_url")
async def admin_dashboard_url_callback(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    await call.answer()
    await _send_dashboard_url(call.message, call.from_user.id)

@dp.message(Command("admin"))
async def admin_panel(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    await state.clear()
    await message.answer("⚙️ <b>Advanced Admin Terminal</b>\n<i>Authorized Access Granted. Use the buttons below.</i>", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_panel_back")
async def back_to_admin(call: CallbackQuery, state: FSMContext):
    await state.clear()
    await call.message.edit_text("⚙️ <b>Advanced Admin Terminal</b>\n<i>Authorized Access Granted. Use the buttons below.</i>", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_toggle_vip_sys")
async def toggle_vip_sys(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    res = db_query("SELECT value FROM settings WHERE key='vip_status'", fetchone=True)
    current = res[0] if res else 'OFF'
    new_status = 'ON' if current == 'OFF' else 'OFF'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('vip_status', ?)", (new_status,))
    await call.message.edit_reply_markup(reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_user_control_start")
async def admin_user_control_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Download Full User List", callback_data="admin_download_userlist", icon_custom_emoji_id=get_emoji_icon("download"))],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text("💻 <b>User Control Terminal</b>\n\n✏️ Enter the <b>User ID</b> or <b>@Username</b> you want to investigate or manage:\n\n👇 <b>OR</b> download the full user CSV format list:", reply_markup=kb, parse_mode='HTML')
    await state.set_state(AdminStates.manage_target_user)

@dp.callback_query(F.data == "admin_download_database_zip")
async def admin_download_database_zip(call: CallbackQuery):
    """Legacy callback now sends a plain SQLite .db file, not a ZIP."""
    if not is_admin(call.from_user.id):
        return await call.answer("Not authorized", show_alert=True)
    if not os.path.exists(DB_PATH):
        return await call.message.answer("❌ Database file was not found on this server.")
    try:
        with tempfile.NamedTemporaryFile(prefix="shop_database_", suffix=".db", delete=False) as tmp:
            backup_path = tmp.name
        try:
            with sqlite3.connect(DB_PATH, timeout=30) as src, sqlite3.connect(backup_path) as dst:
                src.backup(dst)
            await call.message.answer_document(FSInputFile(backup_path, filename="yp_shop_database.db"),
                caption="🗄️ SQLite database backup (.db). Keep it private; it contains user/order data.")
        finally:
            if os.path.exists(backup_path): os.unlink(backup_path)
        await call.answer("Database .db sent")
    except Exception as exc:
        logger.exception("Database backup failed")
        await call.answer("Database backup failed; check logs.", show_alert=True)


@dp.callback_query(F.data == "admin_download_userlist")
async def admin_download_userlist(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    users = db_query("SELECT username, user_id, phone, balance, orders_count, is_vip, is_reseller FROM users", fetchall=True)
    if not users: return await call.answer("❌ No users found in the database.", show_alert=True)
    file_content = "FULL DATABASE DUMP\n" + "="*100 + "\n"
    for u in users:
        uname = u[0] if u[0] else "No_Username"
        uid = u[1]
        phone = u[2] if u[2] else "No_Phone"
        bal = u[3]
        orders = u[4]
        vip_status = "YES" if u[5] else "NO"
        res_status = "YES" if u[6] else "NO"
        file_content += f"UID: {uid} | UNAME: {uname} | PHONE: {phone} | BAL: ₹{bal:.2f} | BUY: {orders} | VIP: {vip_status} | RES: {res_status}\n"
    doc = BufferedInputFile(file_content.encode('utf-8'), filename=f"DB_{datetime.now().strftime('%Y%m%d')}.txt")
    await call.message.answer_document(document=doc, caption="📋 <b>Database export complete.</b>", parse_mode='HTML')
    await call.answer()

@dp.message(AdminStates.manage_target_user)
async def process_user_lookup(m: Message, state: FSMContext):
    target = m.text.strip()
    if target.startswith('@'): target = target[1:]
    loader_msg = await hacker_loading(m, "Querying User Database")
    user_q = db_query("SELECT user_id, first_name, username, balance, is_reseller, orders_count, spent, joined_date, is_banned, warnings, is_vip FROM users WHERE user_id=? OR username=? COLLATE NOCASE", (target, target), fetchone=True)
    if not user_q: return await loader_msg.edit_text("❌ Target not found in the grid. Check ID/Username syntax.", reply_markup=admin_back_kb(), parse_mode='HTML')
    u_id, u_name, u_user, bal, is_res, orders, spent, joined, is_banned, warnings, is_vip = user_q
    await state.update_data(target_u_id=u_id)
    status_emoji = "🔴 BANNED" if is_banned else "🟢 ACTIVE"
    tags = []
    if is_res: tags.append("👑 Reseller")
    if is_vip: tags.append("🌟 VIP")
    type_str = " | ".join(tags) if tags else "👤 Regular"
    text = (f"🛡 <b><u>USER CONTROL TERMINAL</u></b> 🛡\n━━━━━━━━━━━━━━━━━━\n📛 <b>Name:</b> {u_name} (@{u_user})\n🆔 <b>ID:</b> <code>{u_id}</code>\n📊 <b>Status:</b> {status_emoji}\n🔰 <b>Type:</b> {type_str}\n⚠️ <b>Warnings Issued:</b> {warnings}\n━━━━━━━━━━━━━━━━━━\n💰 <b>Wallet Balance:</b> {fmt_curr(bal)}\n📦 <b>Orders:</b> {orders} | 💸 <b>Total Spent:</b> {fmt_curr(spent)}\n📅 <b>Joined:</b> {joined}")
    ban_btn_text = "Unban ✅" if is_banned else "Ban 🚫"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Add Funds ➕", callback_data=f"usrctrl_add_{u_id}", icon_custom_emoji_id=get_emoji_icon("add_balance")), 
         InlineKeyboardButton(text="Minus Funds ➖", callback_data=f"usrctrl_min_{u_id}", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text=ban_btn_text, callback_data=f"usrctrl_ban_{u_id}", icon_custom_emoji_id=get_emoji_icon("shield_icon")), 
         InlineKeyboardButton(text="Warn User ⚠️", callback_data=f"usrctrl_warn_{u_id}", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Give VIP 🌟" if not is_vip else "Remove VIP 🚫", callback_data=f"usrctrl_vip_{u_id}", icon_custom_emoji_id=get_emoji_icon("vip"))],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await loader_msg.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("usrctrl_"))
async def handle_user_actions(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    action = call.data.split("_")[1]
    u_id = int(call.data.split("_")[2])
    await state.update_data(target_u_id=u_id)
    if action == "ban":
        current_status = db_query("SELECT is_banned FROM users WHERE user_id=?", (u_id,), fetchone=True)[0]
        if current_status == 0:
            kb = make_inline_kb(inline_keyboard=[
                [InlineKeyboardButton(text="Yes, Ban", callback_data=f"confirm_ban_{u_id}", icon_custom_emoji_id=get_emoji_icon("check_icon")), 
                 InlineKeyboardButton(text="Cancel", callback_data="admin_user_control_start", icon_custom_emoji_id=get_emoji_icon("back"))]
            ])
            await call.message.edit_text(f"⚠️ Are you sure you want to <b>BAN</b> user <code>{u_id}</code>?", reply_markup=kb, parse_mode='HTML')
            await state.set_state(AdminStates.confirm_ban)
        else:
            db_query("UPDATE users SET is_banned=0 WHERE user_id=?", (u_id,))
            await call.answer("✅ User unbanned successfully!", show_alert=True)
            m = call.message; m.text = str(u_id); await process_user_lookup(m, state)
    elif action == "vip":
        current_status = db_query("SELECT is_vip FROM users WHERE user_id=?", (u_id,), fetchone=True)[0]
        if current_status == 1:
            db_query("UPDATE users SET is_vip=0 WHERE user_id=?", (u_id,))
            await call.answer("✅ VIP Removed!", show_alert=True)
        else:
            db_query("UPDATE users SET is_vip=1, vip_since=? WHERE user_id=?", (datetime.now().strftime("%Y-%m-%d"), u_id))
            await call.answer("✅ VIP Granted!", show_alert=True)
        m = call.message; m.text = str(u_id); await process_user_lookup(m, state)
    elif action == "add":
        await call.message.edit_text("💰 Enter the amount to <b>ADD</b> to this user's wallet:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_add_money)
    elif action == "min":
        await call.message.edit_text("💸 Enter the amount to <b>DEDUCT</b> from this user's wallet:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_minus_money)
    elif action == "warn":
        await call.message.edit_text("⚠️ Type the strict warning message you want to send directly to this user:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_warning)

@dp.callback_query(F.data.startswith("confirm_ban_"))
async def confirm_ban(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    u_id = int(call.data.split("_")[2])
    db_query("UPDATE users SET is_banned=1 WHERE user_id=?", (u_id,))
    await call.answer("🔴 User has been banned!", show_alert=True)
    await state.clear()
    m = call.message; m.text = str(u_id); await process_user_lookup(m, state)

@dp.message(AdminStates.wait_for_add_money)
async def exec_add_money(m: Message, state: FSMContext):
    try:
        amt = float(m.text)
        data = await state.get_data()
        u_id = data['target_u_id']
        db_query("UPDATE users SET balance = balance + ? WHERE user_id=?", (amt, u_id))
        await m.answer(f"✅ Successfully added {fmt_curr(amt)} to target <code>{u_id}</code>.", reply_markup=admin_kb(), parse_mode='HTML')
        try: await bot.send_message(u_id, f"💰 <b>Wallet Top-up!</b>\nAdmin has manually added {fmt_curr(amt)} to your wallet.", parse_mode='HTML')
        except: pass
        await state.clear()
    except ValueError: await m.answer("❌ Critical Error: Input must be a valid number.")

@dp.message(AdminStates.wait_for_minus_money)
async def exec_minus_money(m: Message, state: FSMContext):
    try:
        amt = float(m.text)
        data = await state.get_data()
        u_id = data['target_u_id']
        db_query("UPDATE users SET balance = balance - ? WHERE user_id=?", (amt, u_id))
        await m.answer(f"✅ Successfully deducted {fmt_curr(amt)} from target <code>{u_id}</code>.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Critical Error: Input must be a valid number.")

@dp.message(AdminStates.wait_for_warning)
async def exec_warn_user(m: Message, state: FSMContext):
    data = await state.get_data()
    u_id = data['target_u_id']
    warn_text = m.text
    db_query("UPDATE users SET warnings = warnings + 1 WHERE user_id=?", (u_id,))
    await m.answer(f"✅ Official warning dispatched to <code>{u_id}</code>.", reply_markup=admin_kb(), parse_mode='HTML')
    try: await bot.send_message(u_id, f"⚠️ <b>OFFICIAL WARNING FROM SYSTEM ADMIN:</b>\n\n{warn_text}\n\n<i>Subsequent infractions may lead to an automated grid ban.</i>", parse_mode='HTML')
    except: pass
    await state.clear()

# ==============================================================================
# 18. ADMIN STATISTICS
# ==============================================================================
@dp.callback_query(F.data == "admin_view_stats")
async def admin_dashboard_stats(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    t_users = db_query("SELECT COUNT(*) FROM users", fetchone=True)[0]
    t_resellers = db_query("SELECT COUNT(*) FROM users WHERE is_reseller=1", fetchone=True)[0]
    t_vip = db_query("SELECT COUNT(*) FROM users WHERE is_vip=1", fetchone=True)[0]
    t_prods = db_query("SELECT COUNT(*) FROM products", fetchone=True)[0]
    t_keys = db_query("SELECT COUNT(*) FROM product_keys WHERE is_used=0", fetchone=True)[0]
    t_rev = db_query("SELECT SUM(spent) FROM users", fetchone=True)[0] or 0.0
    today_str = datetime.now().strftime("%Y-%m-%d")
    t_spins = db_query("SELECT COUNT(*) FROM users WHERE last_spin LIKE ?", (f"{today_str}%",), fetchone=True)[0]
    msg = (f"📊 <b><u>GRID INTELLIGENCE DASHBOARD</u></b> 📊\n━━━━━━━━━━━━━━━━━━\n👥 <b>Total Grid Users:</b> {t_users}\n👑 <b>Wholesale Resellers:</b> {t_resellers}\n🌟 <b>Elite VIP Members:</b> {t_vip}\n━━━━━━━━━━━━━━━━━━\n📦 <b>Active Products:</b> {t_prods}\n🔑 <b>Unused Keys in Vault:</b> {t_keys}\n💰 <b>Total Gross Revenue:</b> {fmt_curr(t_rev)}\n🎰 <b>Ludo Spins Today:</b> {t_spins}\n━━━━━━━━━━━━━━━━━━")
    await call.message.edit_text(msg, reply_markup=admin_back_kb(), parse_mode='HTML')


# ==============================================================================
# ADMIN CHANNEL TOGGLES + PER-BUTTON COLOR OVERRIDES
@dp.callback_query(F.data == "admin_channel_toggles")
async def admin_channel_toggles(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    main = (get_setting("main_channel_enabled", "ON") or "ON").upper()
    proof = (get_setting("payment_proof_channel_enabled", "ON") or "ON").upper()
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"Main Channel: {main} {'🟢' if main == 'ON' else '🔴'}", callback_data="admin_toggle_main_channel")],
        [InlineKeyboardButton(text=f"Payment Proof: {proof} {'🟢' if proof == 'ON' else '🔴'}", callback_data="admin_toggle_proof_channel")],
        [InlineKeyboardButton(text="⬅️ Back", callback_data="admin_panel_back")]], _width=1)
    await call.message.edit_text("🔀 <b>CHANNEL ON/OFF</b>\nMain Channel hides/shows its menu button. Payment Proof ON posts successful payment proofs to the configured channel; OFF stops new proof posts.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_toggle_main_channel")
async def admin_toggle_main_channel(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    val = "OFF" if (get_setting("main_channel_enabled", "ON") or "ON").upper() == "ON" else "ON"
    set_setting("main_channel_enabled", val); await admin_channel_toggles(call)

@dp.callback_query(F.data == "admin_toggle_proof_channel")
async def admin_toggle_proof_channel(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    val = "OFF" if (get_setting("payment_proof_channel_enabled", "ON") or "ON").upper() == "ON" else "ON"
    set_setting("payment_proof_channel_enabled", val); await admin_channel_toggles(call)

_PER_BUTTONS = [("Protect Store", "menu_shop"), ("Add Balance", "menu_add_balance"), ("Profile", "menu_profile"), ("How To", "menu_how_to"), ("Spin", "menu_spin_landing"), ("Referral", "menu_referral"), ("Support", "menu_support"), ("Download Files", "menu_all_files"), ("Feedback", "menu_feedback"), ("Reseller Panel", "menu_reseller_dash"), ("Top Users", "menu_top_buyers"), ("Android Non-Root", "category_android_non_root"), ("Android Root", "category_android_root"), ("FF Like", "ff_menu"), ("Guild Glory", "ffglorypro_menu"), ("Product Store", "menu_shop")]
@dp.callback_query(F.data == "admin_per_button_colors")
async def admin_per_button_colors(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    rows = [[InlineKeyboardButton(text=f"{label}: {(get_setting('ui_color_'+cb, 'global') or 'global').upper()}", callback_data=f"admin_pick_btncolor_{cb}")] for label, cb in _PER_BUTTONS]
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ui_controls")])
    await call.message.edit_text("🎨 <b>PER-BUTTON COLOR</b>\nChoose a menu button, then select its color. GLOBAL uses the general UI color setting.", reply_markup=make_inline_kb(inline_keyboard=rows, _width=1), parse_mode="HTML")

@dp.callback_query(F.data.startswith("admin_pick_btncolor_"))
async def admin_pick_button_color(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cb = call.data[len("admin_pick_btncolor_"):]
    if cb not in {x[1] for x in _PER_BUTTONS}: return await call.answer("Unknown button", show_alert=True)
    rows = [[InlineKeyboardButton(text=name, callback_data=f"admin_set_btncolor_{cb}_{val}")] for name, val in [("🔵 Blue", "blue"), ("🟢 Green", "green"), ("🔴 Red", "red"), ("⚪ Global", "global")]]
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="admin_per_button_colors")])
    await call.message.edit_text(f"Set color for <b>{dict((value, label) for label, value in _PER_BUTTONS)[cb]}</b>", reply_markup=make_inline_kb(inline_keyboard=rows, _width=1), parse_mode="HTML")

@dp.callback_query(F.data.regexp(r"^admin_set_btncolor_((?:menu|category)_[a-z0-9_]+|ff_menu|ffglorypro_menu)_(blue|green|red|global)$"))
async def admin_set_button_color(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    match = re.fullmatch(r"admin_set_btncolor_((?:menu|category)_[a-z0-9_]+|ff_menu|ffglorypro_menu)_(blue|green|red|global)", call.data)
    if not match: return
    cb, value = match.groups()
    if cb not in {x[1] for x in _PER_BUTTONS}: return await call.answer("Unknown button", show_alert=True)
    set_setting(f"ui_color_{cb}", "" if value == "global" else value)
    await call.answer("Button color saved")
    # Return to the list so the saved value is visible.
    await admin_per_button_colors(call)

# ADMIN UI CONTROLS
# ==============================================================================
@dp.callback_query(F.data == "admin_ui_controls")
async def admin_ui_controls(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    size = get_ui_button_size()
    color = get_ui_button_color()
    color_label = {"off":"OFF", "blue":"BLUE", "green":"GREEN", "red":"RED"}.get(color, "OFF")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"🎨 Main Menu Color: {color_label}", callback_data="admin_ui_color_menu")],
        [InlineKeyboardButton(text=f"🗂️ Category Color: {(get_setting('ui_category_color', 'off') or 'off').upper()}", callback_data="admin_ui_category_color_menu")],
        [InlineKeyboardButton(text=f"📦 Plan/Product Color: {(get_setting('ui_plan_color', 'off') or 'off').upper()}", callback_data="admin_ui_plan_color_menu")],
        [InlineKeyboardButton(text=f"📐 Button Size: {size.title()}", callback_data="admin_ui_size_menu")],
        [InlineKeyboardButton(text=f"🔴 Back/Cancel Style: {(get_setting('ui_back_cancel_color', 'red') or 'red').upper()}", callback_data="admin_back_cancel_style")],
        [InlineKeyboardButton(text=f"😀 Back/Cancel Emoji: {(get_setting('ui_back_cancel_emoji', '🔴') or '🔴')}", callback_data="admin_back_cancel_emoji")],
        [InlineKeyboardButton(text="⬅️ Back to Admin", callback_data="admin_panel_back")]
    ], _width=1)
    await call.message.edit_text(
        "🎨 <b>UI CONTROLS</b>\n\n"
        f"Color: <b>{color_label}</b>\n"
        f"Size: <b>{size.title()}</b>\n\n"
        "🟢 Green / 🔵 Blue / 🔴 Red = colored buttons\n"
        "⚪ OFF = no button color/style; premium custom emojis stay visible.\n\n"
        "Small/Medium = 2 buttons per row. Large = 1 button per row.",
        reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_back_cancel_style")
async def admin_back_cancel_style(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    current = (get_setting("ui_back_cancel_color", "red") or "red").lower()
    rows = []
    for label, value in [("🔴 Red", "red"), ("🔵 Blue", "blue"), ("🟢 Green", "green"), ("⚪ No Color", "off")]:
        rows.append([InlineKeyboardButton(text=label + (" ✅" if current == value else ""), callback_data=f"admin_back_cancel_color_{value}")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ui_controls")])
    await call.message.edit_text("🔴 <b>BACK / CANCEL BUTTON COLOR</b>\nThis applies across the bot, including the Binance QR screen. Choose a default color.", reply_markup=make_inline_kb(inline_keyboard=rows, _width=1), parse_mode="HTML")

@dp.callback_query(F.data.regexp(r"^admin_back_cancel_color_(off|blue|green|red)$"))
async def admin_back_cancel_color_set(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    value = call.data.rsplit("_", 1)[1]
    set_setting("ui_back_cancel_color", value)
    await call.answer(f"Back/Cancel color: {value.upper()}")
    await admin_ui_controls(call)

@dp.callback_query(F.data == "admin_back_cancel_emoji")
async def admin_back_cancel_emoji_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("😀 <b>Back / Cancel Emoji</b>\nSend one emoji to prefix all Back/Cancel buttons (example: 🔴, ❌, ↩️, 🛑). Send <code>off</code> to remove the prefix.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.wait_for_back_cancel_emoji)

@dp.message(AdminStates.wait_for_back_cancel_emoji)
async def admin_back_cancel_emoji_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    value = (message.text or "").strip()
    if value.lower() == "off": value = "off"
    if value.lower() != "off" and (len(value) > 16 or len(value) > 4):
        return await message.answer("Send one emoji only, such as 🔴 or ❌, or send off.")
    set_setting("ui_back_cancel_emoji", value)
    await state.clear()
    await message.answer(f"✅ Back/Cancel emoji saved: {value or '(off)'}", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ui_color_menu")
async def admin_ui_color_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    current = get_ui_button_color()
    labels = [("🟢 Green", "green"), ("🔵 Blue", "blue"), ("🔴 Red", "red"), ("⚪ OFF", "off")]
    rows = []
    for label, value in labels:
        mark = " ✅" if current == value else ""
        rows.append([InlineKeyboardButton(text=label + mark, callback_data=f"admin_ui_color_{value}")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ui_controls")])
    await call.message.edit_text("🎨 <b>SELECT BUTTON COLOR</b>\n\nChoose a color or turn colors OFF.", reply_markup=make_inline_kb(inline_keyboard=rows, _width=1), parse_mode="HTML")

@dp.callback_query(F.data.regexp(r"^admin_ui_color_(off|blue|green|red)$"))
async def admin_ui_color_set(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    value = call.data.rsplit("_", 1)[1]
    set_setting("ui_button_color", value)
    label = {"off":"OFF", "blue":"BLUE", "green":"GREEN", "red":"RED"}[value]
    await call.answer(f"✅ UI color set to {label}")
    await admin_ui_controls(call)

@dp.callback_query(F.data.in_(["admin_ui_category_color_menu", "admin_ui_plan_color_menu"]))
async def admin_ui_scoped_color_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    scope = "category" if call.data == "admin_ui_category_color_menu" else "plan"
    setting = f"ui_{scope}_color"
    current = (get_setting(setting, "off") or "off").lower()
    rows = []
    for label, value in [("🟢 Green", "green"), ("🔵 Blue", "blue"), ("🔴 Red", "red"), ("⚪ OFF / Use Main", "off")]:
        mark = " ✅" if current == value else ""
        rows.append([InlineKeyboardButton(text=label + mark, callback_data=f"admin_ui_{scope}_color_{value}")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ui_controls")])
    await call.message.edit_text(f"🎨 <b>{scope.title()} Button Color</b>\nChoose the Telegram button style.", reply_markup=make_inline_kb(inline_keyboard=rows), parse_mode="HTML")

@dp.callback_query(F.data.regexp(r"^admin_ui_(category|plan)_color_(off|blue|green|red)$"))
async def admin_ui_scoped_color_set(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    parts = call.data.split("_")
    scope, value = parts[2], parts[4]
    set_setting(f"ui_{scope}_color", value)
    await call.answer(f"{scope.title()} color set to {value.upper()}")
    await admin_ui_controls(call)

@dp.callback_query(F.data == "admin_ui_size_menu")
async def admin_ui_size_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🔹 Small — 2/row", callback_data="admin_ui_size_small")],
        [InlineKeyboardButton(text="🔸 Medium — 2/row", callback_data="admin_ui_size_medium")],
        [InlineKeyboardButton(text="🔶 Large — 1/row", callback_data="admin_ui_size_large")],
        [InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ui_controls")]
    ], _width=1)
    await call.message.edit_text("📐 <b>SELECT BUTTON SIZE</b>\n\nSmall/Medium = compact 2-column layout.\nLarge = one button per row.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data.regexp(r"^admin_ui_size_(small|medium|large)$"))
async def admin_ui_size_set(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    value = call.data.rsplit("_", 1)[1]
    set_setting("ui_button_size", value)
    await call.answer(f"✅ UI size set to {value.title()}")
    await admin_ui_controls(call)


# PHOTO-BASED PRODUCT ADD
# ==============================================================================
def _ocr_photo_fields(image_bytes: bytes) -> Dict[str, str]:
    result = {"text": "", "panel": "", "duration": "", "price": "", "pid": ""}
    try:
        from io import BytesIO
        text = ""
        if Image is not None and pytesseract is not None:
            image = Image.open(BytesIO(image_bytes)).convert("RGB")
            text = pytesseract.image_to_string(image) or ""
        else:
            # Fallback to the system tesseract binary when Python OCR packages
            # are unavailable. Failure is non-fatal and the admin can enter data manually.
            with tempfile.NamedTemporaryFile(suffix=".png", delete=True) as tmp:
                tmp.write(image_bytes); tmp.flush()
                proc = subprocess.run(["tesseract", tmp.name, "stdout", "--psm", "6"], capture_output=True, text=True, timeout=20)
                text = proc.stdout or ""
        result["text"] = text
        lines = [re.sub(r"\s+", " ", x).strip() for x in text.splitlines() if x.strip()]
        joined = " ".join(lines)
        # Price: ₹/Rs/INR followed by a number, or a standalone currency-like number.
        m = re.search(r"(?:₹|Rs\.?|INR)\s*([0-9]+(?:\\.[0-9]+)?)", joined, re.I)
        if m: result["price"] = m.group(1)
        # Duration: common day/hour/month formats.
        m = re.search(r"\b([0-9]+\s*(?:day|days|d|hour|hours|hr|hrs|month|months|week|weeks|year|years))\b", joined, re.I)
        if m: result["duration"] = m.group(1)
        # PID / product ID.
        m = re.search(r"(?:PID|P\.?ID|Product\s*ID|ID)\s*[:#-]?\s*([A-Za-z0-9_-]{2,})", joined, re.I)
        if m: result["pid"] = m.group(1)
        # Panel name from labelled text first.
        for line in lines:
            mm = re.search(r"(?:panel|panel name|name)\s*[:=-]\s*(.+)$", line, re.I)
            if mm:
                candidate = mm.group(1).strip()
                if len(candidate) >= 2:
                    result["panel"] = candidate[:100]
                    break
        if not result["panel"] and lines:
            # Conservative fallback: first non-price/non-duration line.
            for line in lines[:8]:
                if not re.search(r"(?:₹|Rs\.?|INR|day|days|hour|hours|month|months|week|weeks|pid|product\s*id)", line, re.I):
                    if 2 <= len(line) <= 100:
                        result["panel"] = line
                        break
    except Exception:
        logger.exception("Photo OCR failed")
    return result

async def _download_photo_bytes(message: Message) -> bytes:
    from io import BytesIO
    photo = message.photo[-1]
    buf = BytesIO()
    await bot.download(photo, destination=buf)
    return buf.getvalue()

@dp.callback_query(F.data == "admin_photo_add_product")
async def admin_photo_add_product_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Cancel", callback_data="admin_panel_back")]
    ])
    cats = []
    for cat in get_all_categories():
        cats.append([InlineKeyboardButton(text=cat, callback_data=f"photoadd_cat_{cat}", icon_custom_emoji_id=get_category_emoji(cat))])
    cats.extend(kb.inline_keyboard)
    await call.message.edit_text(
        "📷 <b>PHOTO ADD PRODUCT</b>\n\n"
        "First choose the product category, then send the product screenshot.\n"
        "The bot will try to read <b>Panel Name + Duration/Days + Price</b> automatically.",
        reply_markup=make_inline_kb(inline_keyboard=cats), parse_mode="HTML")

@dp.callback_query(F.data.startswith("photoadd_cat_"))
async def photo_add_category(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    category = call.data.split("photoadd_cat_", 1)[1]
    await state.update_data(cat=category)
    await state.set_state(AdminStates.photo_add_product)
    await call.message.edit_text(
        "📷 <b>Send Product Photo</b>\n\n"
        "Send a clear screenshot containing the panel name, duration/days and price.\n"
        "If OCR cannot read a field, the bot will ask you to enter it manually.",
        reply_markup=admin_back_kb(), parse_mode="HTML")

@dp.message(AdminStates.photo_add_product, F.photo)
async def photo_add_product_photo(m: Message, state: FSMContext):
    data = await state.get_data()
    try:
        raw = await _download_photo_bytes(m)
        fields = _ocr_photo_fields(raw)
    except Exception as exc:
        logger.exception("Photo product download/OCR failed")
        fields = {"text":"", "panel":"", "duration":"", "price":"", "pid":""}
    panel = fields.get("panel", "") or ""
    duration = fields.get("duration", "") or ""
    price = fields.get("price", "") or ""
    await state.update_data(photo_text=fields.get("text", ""), photo_mode=1, panel_name=panel, name=duration or "Package", validity=duration, price=price)
    summary = (
        "📷 <b>PHOTO READ RESULT</b>\n\n"
        f"🏷 Panel: <code>{html.escape(panel or 'Not detected')}</code>\n"
        f"⏱ Duration: <code>{html.escape(duration or 'Not detected')}</code>\n"
        f"💰 Price: <code>₹{html.escape(price or 'Not detected')}</code>\n\n"
        "If these values are correct, send the <b>Reseller Price</b>. If any value is missing/wrong, you can still continue and enter it manually."
    )
    await m.answer(summary, reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.photo_add_product_confirm)

@dp.message(AdminStates.photo_add_product, F.text)
async def photo_add_product_no_photo(m: Message, state: FSMContext):
    await m.answer("📷 Please send the product as a photo/screenshot. Send /cancel or use Back to stop.")

@dp.message(AdminStates.photo_add_product_confirm)
async def photo_add_product_confirm(m: Message, state: FSMContext):
    text=(m.text or "").strip()
    data=await state.get_data()
    # Allow admin to correct OCR with: panel | duration | price
    if text.count("|") >= 2:
        parts=[x.strip() for x in text.split("|")]
        try:
            price=float(parts[2])
            if price < 0: raise ValueError
        except ValueError:
            return await m.answer("❌ Price must be a number. Format: <code>Panel | 7 Days | 99</code>", parse_mode="HTML")
        await state.update_data(panel_name=parts[0], name=parts[1], validity=parts[1], price=price)
        data=await state.get_data()
    else:
        try:
            rp=float(text)
            if rp < 0: raise ValueError
        except ValueError:
            return await m.answer("Send Reseller Price (number), or correct OCR as <code>Panel | 7 Days | 99</code>.", parse_mode="HTML")
        if not data.get("price"):
            return await m.answer("❌ OCR did not detect User Price. Send <code>Panel | 7 Days | UserPrice</code> first.", parse_mode="HTML")
        if not data.get("panel_name") or not data.get("validity"):
            return await m.answer("❌ Panel name or duration was not detected. Send correction as <code>Panel | 7 Days | UserPrice</code>.", parse_mode="HTML")
        await state.update_data(reseller_price=rp)
        await m.answer("🔗 Send APK/Update link, or type <code>none</code>.", reply_markup=admin_back_kb(), parse_mode="HTML")
        await state.set_state(AdminStates.add_prod_apk)
        return
    await m.answer("👑 Now send Reseller Price (number).", parse_mode="HTML")

@dp.message(AdminStates.photo_add_product_pid, F.photo)
async def photo_add_product_pid_photo(m: Message, state: FSMContext):
    data=await state.get_data()
    try:
        fields=_ocr_photo_fields(await _download_photo_bytes(m))
    except Exception:
        fields={"pid":"", "duration":"", "panel":"", "price":"", "text":""}
    pid=(fields.get("pid") or "").strip()
    duration=(fields.get("duration") or "").strip()
    if pid:
        await state.update_data(external_product_id=pid)
    if duration:
        await state.update_data(external_duration=normalize_api_duration(duration), validity=duration, name=duration)
    data=await state.get_data()
    if not pid:
        await m.answer("⚠️ PID could not be read from the photo. Send the Bunty PID manually.", reply_markup=admin_back_kb())
        return await state.set_state(AdminStates.add_prod_external_product_id)
    await _save_photo_bunty_product(m, state)

@dp.message(AdminStates.photo_add_product_pid, F.text)
async def photo_add_product_pid_text(m: Message, state: FSMContext):
    pid=(m.text or "").strip()
    if not pid:
        return await m.answer("❌ PID cannot be empty. Send PID or the API screenshot.")
    await state.update_data(external_product_id=pid)
    await _save_photo_bunty_product(m, state)

async def _save_photo_bunty_product(m: Message, state: FSMContext):
    data=await state.get_data()
    api_duration=normalize_api_duration(data.get("external_duration") or data.get("validity") or data.get("name") or "")
    try:
        price=float(data.get("price"))
        reseller=float(data.get("reseller_price"))
    except (TypeError, ValueError):
        return await m.answer("❌ Invalid detected price. Restart Photo Add Product and correct the values.")
    conn=sqlite3.connect(DB_PATH, timeout=30.0)
    c=conn.cursor()
    try:
        c.execute("""INSERT INTO products
            (category,panel_name,name,price_inr,reseller_price,stock,apk_link,validity,device_limit,
             external_enabled,external_product_id,requires_android_id,external_duration,api_provider)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (data.get("cat",""),data.get("panel_name",""),data.get("name") or data.get("validity") or "Package",
             price,reseller,1,data.get("apk","") or "",data.get("validity") or data.get("name") or "Lifetime",
             data.get("device_limit","1 Device"),1,str(data.get("external_product_id","")),0,api_duration,"bunty"))
        prod_id=c.lastrowid
        conn.commit()
    except sqlite3.Error as exc:
        conn.rollback(); logger.exception("Photo Bunty product creation failed")
        return await m.answer(f"❌ Product save failed: <code>{html.escape(str(exc))}</code>", parse_mode="HTML")
    finally:
        conn.close()
    await state.clear()
    await m.answer(
        "✅ <b>PHOTO PRODUCT CREATED</b>\n\n"
        f"📦 Product ID: <code>{prod_id}</code>\n"
        f"🏷 Panel: <b>{html.escape(str(data.get('panel_name') or '-'))}</b>\n"
        f"⏱ Duration: <code>{html.escape(str(data.get('validity') or api_duration or '-'))}</code>\n"
        f"💰 User Price: <b>₹{price:g}</b>\n"
        f"👑 Reseller Price: <b>₹{reseller:g}</b>\n"
        f"🆔 Bunty PID: <code>{html.escape(str(data.get('external_product_id') or '-'))}</code>",
        reply_markup=admin_kb(), parse_mode="HTML")

# ==============================================================================
# 19. ADMIN PRODUCT MANAGEMENT
# ==============================================================================
@dp.callback_query(F.data == "admin_quick_add_product")
async def admin_quick_add_product_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.answer()
    await call.message.edit_text(
        "⚡ <b>QUICK ADD PRODUCT — ALL API PROVIDERS</b>\n\n"
        "बस एक लाइन भेजें; अलग-अलग 1 Hour / 3 Hour के लिए बार-बार मेन्यू खोलने की जरूरत नहीं।\n"
        "<code>Category | Panel | Package | Validity | Device | UserPrice | ResellerPrice | Provider | PID</code>\n\n"
        "Provider: <code>bunty</code>, <code>license_manager</code>, <code>hk_tamim</code>, <code>dripclient</code>, <code>adminshops</code>, <code>whitex</code>, <code>panelstore</code>, या <code>manual</code>.\n\n"
        "उदाहरण WhiteX: <code>ROOT | WHITEX | 1 Hour | 1 Hour | 1 Device | 49 | 35 | whitex | 50</code>\n"
        "उदाहरण License: <code>ROOT | LM | 1 Hour | 1 Hour | 1 Device | 49 | 35 | license_manager | 62</code>\n"
        "Manual stock के लिए PID <code>-</code> रखें। API provider चुनने पर PID/variant ID जरूरी है।",
        reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.quick_add_product)

@dp.message(AdminStates.quick_add_product)
async def admin_quick_add_product_save(m: Message, state: FSMContext):
    parts = [x.strip() for x in (m.text or "").split("|")]
    if len(parts) != 9:
        return await m.answer("❌ कुल 9 fields चाहिए, | से अलग करें। उदाहरण: <code>ROOT | WHITEX | 1 Hour | 1 Hour | 1 Device | 49 | 35 | whitex | 50</code>", parse_mode="HTML")
    cat, panel, name, validity, device, price_s, rprice_s, provider, pid = parts
    provider = provider.strip().lower().replace(" ", "_").replace("-", "_")
    aliases = {"adminpanels":"bunty", "bunti":"bunty", "buntybhaiya":"bunty", "lm":"license_manager", "license":"license_manager", "tamim":"hk_tamim", "hk":"hk_tamim", "whitex_mode":"whitex", "white_x":"whitex", "stock":"manual", "drip":"dripclient", "drip_client":"dripclient", "admin_shops":"adminshops", "admin-shop":"adminshops"}
    provider = aliases.get(provider, provider)
    supported = {"bunty", "license_manager", "hk_tamim", "dripclient", "adminshops", "whitex", "panelstore", "manual"}
    if provider not in supported:
        return await m.answer("❌ Provider गलत है। इनमें से चुनें: <code>bunty / license_manager / hk_tamim / dripclient / adminshops / whitex / panelstore / manual</code>", parse_mode="HTML")
    try:
        price, rprice = float(price_s), float(rprice_s)
        if price < 0 or rprice < 0 or price > 1000000 or rprice > 1000000: raise ValueError
    except ValueError:
        return await m.answer("❌ User Price और Reseller Price 0 से 1000000 के बीच number होने चाहिए।")
    ext_pid = "" if pid.lower() in ("-", "none", "") else pid
    external = 0 if provider == "manual" else 1
    if external and not ext_pid:
        if provider == "license_manager": ext_pid = get_setting("license_manager_default_product_id", "62").strip()
        elif provider == "hk_tamim": ext_pid = get_setting("hk_tamim_default_variant_id", "50").strip()
        elif provider == "adminshops": ext_pid = get_setting("adminshops_default_product_id", "14").strip()
    if external and not ext_pid:
        return await m.answer("❌ इस API के लिए Product ID/Variant ID जरूरी है।")
    if provider in {"license_manager", "hk_tamim", "whitex", "adminshops", "dripclient"} and not str(ext_pid).isdigit():
        return await m.answer("❌ License Manager / HK Tamim / WhiteX की Product ID या variant_id numeric होनी चाहिए।")
    if provider == "panelstore" and not get_setting("panelstore_api_key", "").strip():
        return await m.answer("⚠️ पहले Admin → PanelStore API में API key सेट करें।")
    if provider == "whitex" and not _whitex_token():
        return await m.answer("⚠️ पहले Admin → WhiteX Mode API में API token सेट करें।")
    if provider == "license_manager" and not get_setting("license_manager_api_key", "").strip():
        return await m.answer("⚠️ पहले License Manager API में token सेट करें।")
    if provider == "hk_tamim" and not get_setting("hk_tamim_api_token", "").strip():
        return await m.answer("⚠️ पहले HK Tamim API में token सेट करें।")
    if provider == "dripclient" and not get_setting("dripclient_api_token", "").strip():
        return await m.answer("⚠️ पहले Drip Client API token सेट करें।")
    if provider == "adminshops" and not get_setting("adminshops_api_token", "").strip():
        return await m.answer("⚠️ पहले Admin Shops Bearer token सेट करें।")
    if provider == "bunty" and not get_setting("external_api_key", "").strip():
        return await m.answer("⚠️ पहले Bunty API key सेट करें।")
    api_duration = normalize_api_duration(validity) if external and provider == "bunty" else (validity if external else "")
    try:
        db_query("""INSERT INTO products (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit, external_enabled, external_product_id, requires_android_id, external_duration, api_provider) VALUES (?, ?, ?, ?, ?, ?, '', ?, ?, ?, ?, 0, ?, ?)""",
                 (cat, panel, name, price, rprice, 1 if external else 0, validity, device, external, ext_pid, api_duration, provider))
    except Exception as exc:
        logger.exception("Quick add product failed")
        return await m.answer(f"❌ Product save failed: <code>{html.escape(str(exc)[:500])}</code>", parse_mode="HTML")
    await state.clear()
    await m.answer(f"✅ <b>Quick Product Added</b>\n\n📦 {html.escape(name)}\n🌐 Provider: <b>{html.escape(provider)}</b>\n🆔 PID/Variant: <code>{html.escape(ext_pid or '-')}</code>\n⏱ Duration: <code>{html.escape(api_duration or '-')}</code>", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_add_prod")
async def add_prod_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[])
    for cat in get_all_categories():
        emoji_id = get_category_emoji(cat)
        kb.inline_keyboard.append([InlineKeyboardButton(text=cat, callback_data=f"addprod_cat_{cat}", icon_custom_emoji_id=as_emoji_icon_id(emoji_id))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Cancel", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text("<b>Step 1:</b> Choose the <b>Category</b> for this product:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("addprod_cat_"))
async def add_prod_category_selected(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    category = call.data.split("addprod_cat_", 1)[1]
    await state.update_data(cat=category)
    await call.message.edit_text(f"<b>Step 2:</b> Enter <b>PANEL NAME</b>\n(e.g., 'MST PANEL', 'DRIP PANEL'):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_panel_name)

@dp.message(AdminStates.add_prod_panel_name)
async def add_prod_panel_name(m: Message, state: FSMContext):
    await state.update_data(panel_name=(m.text or '').strip())
    await m.answer("<b>Step 3:</b> Enter <b>PACKAGE DURATION/DATE NAME</b>\n(e.g., '7 Days', '1 Month'):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_name)

@dp.message(AdminStates.add_prod_name)
async def add_prod_name(m: Message, state: FSMContext):
    await state.update_data(name=(m.text or '').strip())
    await m.answer("⏳ Enter Time Validity String (e.g., '24 Hours'):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_validity)

@dp.message(AdminStates.add_prod_validity)
async def add_prod_validity(m: Message, state: FSMContext):
    await state.update_data(validity=(m.text or '').strip())
    await m.answer("📱 Enter strict Device Enforcement Limit (e.g., '1 Device HWID'):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_device_limit)

@dp.message(AdminStates.add_prod_device_limit)
async def add_prod_device_limit(m: Message, state: FSMContext):
    await state.update_data(device_limit=(m.text or '').strip())
    await m.answer("💰 Enter standard **User Price** in Rupees (₹) (e.g., 500):", parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_price)

@dp.message(AdminStates.add_prod_price)
async def add_prod_price(m: Message, state: FSMContext):
    try:
        await state.update_data(price=float(m.text))
        await m.answer("👑 Enter wholesale **Reseller Price** in Rupees (₹) (e.g., 300):", parse_mode='HTML')
        await state.set_state(AdminStates.add_prod_reseller_price)
    except ValueError: await m.answer("❌ Invalid input datatype! Must be numerical.")

@dp.message(AdminStates.add_prod_reseller_price)
async def add_prod_reseller_price(m: Message, state: FSMContext):
    try:
        await state.update_data(reseller_price=float(m.text))
        await m.answer("🔗 Enter direct APK/Payload Download Link (or type 'none' to omit):", parse_mode='HTML')
        await state.set_state(AdminStates.add_prod_apk)
    except ValueError: await m.answer("❌ Invalid input datatype! Must be numerical.")

@dp.message(AdminStates.add_prod_apk)
async def add_prod_apk(m: Message, state: FSMContext):
    await state.update_data(apk="" if (m.text or "").strip().lower() == 'none' else (m.text or "").strip(), video_file_id="")
    await _show_add_product_provider_menu(m, state)

async def _show_add_product_provider_menu(message: Message, state: FSMContext):
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Bunty API (AdminPanels)", callback_data="addprod_api_bunty", icon_custom_emoji_id=get_emoji_icon("check_icon"))],
        [InlineKeyboardButton(text="🔑 License Manager API", callback_data="addprod_api_license", icon_custom_emoji_id=get_emoji_icon("shield_icon"))],
        [InlineKeyboardButton(text="🗝️ HK Tamim API", callback_data="addprod_api_hktamim")],
        [InlineKeyboardButton(text="💧 Drip Client API", callback_data="addprod_api_dripclient")],
        [InlineKeyboardButton(text="🛍️ Admin Shops API", callback_data="addprod_api_adminshops")],
        [InlineKeyboardButton(text="⚪ WhiteX Mode API", callback_data="addprod_api_whitex")],
        [InlineKeyboardButton(text="Manual Stock (Keys)", callback_data="addprod_ext_no", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await message.answer("🔗 <b>Choose Key Source / API Provider:</b>\n\n⚡ Bunty · 🔑 License Manager · 🗝️ HK Tamim\n💧 Drip Client · 🛍️ Admin Shops · ⚪ WhiteX\n📦 Manual Stock", reply_markup=kb, parse_mode="HTML")
    await state.set_state(AdminStates.add_prod_external)

@dp.message(AdminStates.add_prod_video)
async def add_prod_video_capture(m: Message, state: FSMContext):
    value = (m.text or "").strip()
    if value == "-":
        await state.update_data(video_file_id="")
    elif m.video:
        await state.update_data(video_file_id=m.video.file_id)
    elif m.document and (m.document.mime_type or "").startswith("video/"):
        await state.update_data(video_file_id=m.document.file_id)
    else:
        return await m.answer("❌ Send a video/video file, or send '-' to skip.")
    await _show_add_product_provider_menu(m, state)

@dp.callback_query(F.data.in_(["addprod_api_bunty", "addprod_ext_yes"]), AdminStates.add_prod_external)
async def add_prod_api_bunty(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    data = await state.get_data()
    await state.update_data(external_enabled=1, api_provider="bunty")
    if data.get("photo_mode"):
        await call.message.edit_text("⚡ <b>Bunty API Selected</b>\n\n📷 Now send the <b>API product screenshot</b>. I will read PID and Duration automatically.", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.photo_add_product_pid)
    else:
        await call.message.edit_text("⚡ <b>Bunty API Selected (AdminPanels)</b>\n\nEnter the <b>Bunty Product ID (PID)</b>:", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.add_prod_external_product_id)


@dp.callback_query(F.data == "addprod_api_license", AdminStates.add_prod_external)
async def add_prod_api_license(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return
    await state.update_data(external_enabled=1, api_provider="license_manager")
    default_pid = get_setting("license_manager_default_product_id", "62")
    await call.message.edit_text(
        "🔑 <b>License Manager API selected</b>\n\nSend the License Manager product_id for this product.\n"
        f"Default configured product ID: <code>{html.escape(default_pid)}</code>",
        reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.add_prod_external_product_id)

@dp.callback_query(F.data == "addprod_api_hktamim", AdminStates.add_prod_external)
async def add_prod_api_hktamim(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.update_data(external_enabled=1, api_provider="hk_tamim")
    default_pid = get_setting("hk_tamim_default_variant_id", "50")
    await call.message.edit_text(
        "🗝️ <b>HK Tamim API selected</b>\n\nSend the <b>variant_id</b> for this product.\n"
        f"Default variant ID: <code>{html.escape(default_pid)}</code>",
        reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.add_prod_external_product_id)

@dp.callback_query(F.data == "addprod_api_dripclient", AdminStates.add_prod_external)
async def add_prod_api_dripclient(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.update_data(external_enabled=1, api_provider="dripclient")
    await call.message.edit_text("💧 <b>Drip Client API selected</b>\n\nSend the numeric <b>variant_id</b> for this product. Configure the X-API-Token under Admin → Drip Client.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.add_prod_external_product_id)

@dp.callback_query(F.data == "addprod_api_adminshops", AdminStates.add_prod_external)
async def add_prod_api_adminshops(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.update_data(external_enabled=1, api_provider="adminshops")
    default_pid = get_setting("adminshops_default_product_id", "14")
    await call.message.edit_text(f"🛍️ <b>Admin Shops API selected</b>\n\nSend numeric <b>product_id</b> from /catalog.\nDefault product ID: <code>{html.escape(default_pid)}</code>\nConfigure the Bearer token under Admin → Admin Shops.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.add_prod_external_product_id)

@dp.callback_query(F.data == "addprod_api_whitex", AdminStates.add_prod_external)
async def add_prod_api_whitex(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.update_data(external_enabled=1, api_provider="whitex")
    await call.message.edit_text(
        "⚪ <b>WhiteX Mode API selected</b>\n\nSend the numeric <b>variant_id</b> from WhiteX products list.\n"
        "WhiteX token must first be configured in Admin → WhiteX Mode API.",
        reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.add_prod_external_product_id)

@dp.message(AdminStates.add_prod_external_product_id)
async def add_prod_external_pid(m: Message, state: FSMContext):
    pid = (m.text or "").strip()
    data = await state.get_data()
    provider = data.get("api_provider", "bunty")
    if pid in {"", "-", "default", "DEFAULT"}:
        if provider == "license_manager":
            pid = get_setting("license_manager_default_product_id", "62").strip()
        elif provider == "hk_tamim":
            pid = get_setting("hk_tamim_default_variant_id", "50").strip()
        elif provider == "adminshops":
            pid = get_setting("adminshops_default_product_id", "14").strip()
    if not pid:
        return await m.answer("❌ Product PID / Variant ID cannot be empty. Set the provider's default ID or send an ID.")
    if provider in {"license_manager", "hk_tamim", "adminshops", "dripclient"} and not pid.isdigit():
        return await m.answer("❌ This provider requires a numeric product/variant ID.")
    provider_name = {"license_manager":"License Manager","hk_tamim":"HK Tamim","dripclient":"Drip Client","adminshops":"Admin Shops"}.get(provider, "Bunty/AdminPanels")
    await state.update_data(external_product_id=pid, requires_android_id=0)

    await m.answer(
        f"⏱ <b>Enter the {provider_name} API duration/tier.</b>\n\n"
        "Examples: <code>1 Day</code>, <code>7 Days</code>, <code>30 Days</code>\n"
        f"Your shop validity is: <code>{data.get('validity', '')}</code>\n\n"
        "If the API uses the same duration, send the same value.",
        reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_external_duration)

@dp.message(AdminStates.add_prod_external_duration)
async def add_prod_external_duration(m: Message, state: FSMContext):
    data = await state.get_data()
    raw_duration = (m.text or "").strip()
    api_duration = normalize_api_duration(raw_duration or data.get("validity", ""))
    if not api_duration:
        return await m.answer("❌ API duration cannot be empty.")
    data = await state.get_data()
    provider = data.get("api_provider", "bunty")
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    c = conn.cursor()
    try:
        c.execute("""INSERT INTO products
            (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit,
             external_enabled, external_product_id, requires_android_id, external_duration, api_provider, video_file_id)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (data['cat'], data['panel_name'], data['name'], data['price'], data['reseller_price'], 1,
             data['apk'], data['validity'], data['device_limit'], 1, data['external_product_id'], 0, api_duration, provider, data.get('video_file_id', '')))
        prod_id = c.lastrowid
        conn.commit()
    except sqlite3.Error as exc:
        conn.rollback()
        logger.exception("API product creation failed: %s", exc)
        return await m.answer(f"❌ <b>Product save failed</b>\n<code>{type(exc).__name__}: {exc}</code>\n\nPlease restart the bot once so database migration can run, then try again.", parse_mode='HTML')
    finally:
        conn.close()
    p_label = {"license_manager":"🔑 License Manager API","hk_tamim":"🗝️ HK Tamim API","dripclient":"💧 Drip Client API","adminshops":"🛍️ Admin Shops API"}.get(provider, "⚡ Bunty API")
    await m.answer(
        f"✅ <b>API Product Created!</b>\n\n"
        f"📦 Product ID: <code>{prod_id}</code>\n"
        f"🌐 Provider: <b>{p_label}</b>\n"
        f"🆔 API Product ID: <code>{data['external_product_id']}</code>\n"
        f"⏱ API Duration: <code>{api_duration}</code>\n\n"
        f"The {p_label} will auto-generate and deliver keys when purchased.",
        reply_markup=admin_kb(), parse_mode='HTML'
    )
    await state.clear()

@dp.callback_query(F.data == "addprod_ext_no", AdminStates.add_prod_external)
async def add_prod_external_no(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.update_data(external_enabled=0, external_product_id="", requires_android_id=0, api_provider="manual")
    await call.message.edit_text("📥 <b>Manual Key Product</b>\n\nNow send the keys, one key per line:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.add_prod_keys)

@dp.message(AdminStates.add_prod_keys)
async def add_prod_keys(m: Message, state: FSMContext):
    keys = [k.strip() for k in m.text.strip().split('\n') if k.strip()]
    if not keys:
        return await m.answer("❌ No valid keys found. Send at least one key.")
    data = await state.get_data()
    stock = len(keys)
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    c = conn.cursor()
    try:
        c.execute("""INSERT INTO products
            (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit,
             external_enabled, external_product_id, requires_android_id, api_provider, video_file_id)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (data['cat'], data['panel_name'], data['name'], data['price'], data['reseller_price'], stock,
             data['apk'], data['validity'], data['device_limit'], 0, '', 0, 'manual', data.get('video_file_id', '')))
        prod_id = c.lastrowid
        for k in keys:
            c.execute("INSERT INTO product_keys (product_id, key_text) VALUES (?, ?)", (prod_id, k))
        conn.commit()
    except sqlite3.Error as exc:
        conn.rollback()
        logger.exception("Manual product creation failed: %s", exc)
        return await m.answer(f"❌ <b>Product save failed</b>\n<code>{type(exc).__name__}: {exc}</code>\n\nPlease restart the bot once so database migration can run, then try again.", parse_mode='HTML')
    finally:
        conn.close()
    await m.answer(f"✅ <b>Manual Product Created!</b>\n\n📦 Product ID: <code>{prod_id}</code>\n🔒 Stock: {stock} keys", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

PAGE_SIZE = 10

@dp.callback_query(F.data.startswith("admin_quick_add_key"))
async def admin_quick_add_key(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    data = call.data
    page = 1
    if data.startswith("admin_quick_add_key_p_"):
        try:
            page = max(1, int(data.rsplit("_", 1)[1]))
        except ValueError:
            page = 1
    products = db_query(
        "SELECT id, category, panel_name, name, validity, stock FROM products WHERE is_active=1",
        fetchall=True
    ) or []
    products = sorted(
        products,
        key=lambda r: (natural_sort_key(r[1]), natural_sort_key(r[2]), natural_sort_key(r[3]), natural_sort_key(r[4]))
    )
    if not products:
        return await call.message.edit_text("📦 No active products found.", reply_markup=admin_back_kb(), parse_mode="HTML")
    page_size = 10
    total_pages = max(1, math.ceil(len(products) / page_size))
    page = min(page, total_pages)
    chunk = products[(page-1)*page_size:page*page_size]
    kb = make_inline_kb(inline_keyboard=[])
    for pid, cat, panel, name, validity, stock in chunk:
        label = f"➕ {panel or cat} • {name} • {validity} | Stock {stock or 0}"
        kb.inline_keyboard.append([
            InlineKeyboardButton(text=label[:60], callback_data=f"quick_add_key_{pid}")
        ])
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"admin_quick_add_key_p_{page-1}"))
    nav.append(InlineKeyboardButton(text=f"📄 {page}/{total_pages}", callback_data="ignore_stock_click"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"admin_quick_add_key_p_{page+1}"))
    kb.inline_keyboard.append(nav)
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))
    ])
    await call.message.edit_text(
        "🔑 <b>QUICK ADD KEY</b>\n\nSelect product/package directly.\n"
        "No need to open Manage Products.",
        reply_markup=kb, parse_mode="HTML"
    )

@dp.callback_query(F.data.startswith("quick_add_key_"))
async def quick_add_key_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    try:
        p_id = int(call.data.rsplit("_", 1)[1])
    except ValueError:
        return await call.answer("Invalid product.", show_alert=True)
    prod = db_query("SELECT panel_name, name, validity, stock FROM products WHERE id=?", (p_id,), fetchone=True)
    if not prod:
        return await call.answer("Product not found.", show_alert=True)
    await state.update_data(edit_p_id=p_id)
    await call.message.edit_text(
        f"🔑 <b>ADD KEY</b>\n\n📦 {prod[0] or 'Panel'}\n"
        f"🕒 {prod[1]} • {prod[2]}\n📦 Current Stock: {prod[3] or 0}\n\n"
        "Send one or multiple keys, <b>one key per line</b>:",
        reply_markup=admin_back_kb(), parse_mode="HTML"
    )
    await state.set_state(AdminStates.wait_for_add_keys)

@dp.callback_query(F.data.startswith("admin_manage_prods"))
async def admin_manage_prods(call: CallbackQuery, state: FSMContext = None):
    if not is_admin(call.from_user.id): return
    data = call.data
    page = 1
    cat_filter = None
    
    if data == "admin_manage_prods":
        page = 1
    elif data.startswith("admin_manage_prods_p_"):
        parts = data.split("_p_")[1].split("_c_")
        page = int(parts[0]) if parts[0].isdigit() else 1
        if len(parts) > 1 and parts[1]:
            cat_filter = parts[1]
    elif data.startswith("admin_manage_prods_cat_"):
        cat_filter = data.split("admin_manage_prods_cat_")[1]
        page = 1
    elif data == "admin_manage_prods_filter_menu":
        cats = get_all_categories()
        kb = make_inline_kb(inline_keyboard=[])
        for c in cats:
            count_row = db_query("SELECT COUNT(*) FROM products WHERE category LIKE ?", (c + '%',), fetchone=True)
            count = int(count_row[0]) if count_row else 0
            cat_ico = get_category_display_icon(c)
            kb.inline_keyboard.append([InlineKeyboardButton(text=f"{cat_ico} {c} ({count} items)", callback_data=f"admin_manage_prods_cat_{c}")])
        kb.inline_keyboard.append([InlineKeyboardButton(text="🌐 Show All Products", callback_data="admin_manage_prods_p_1")])
        kb.inline_keyboard.append([InlineKeyboardButton(text="🔙 Back to Products", callback_data="admin_manage_prods_p_1")])
        return await call.message.edit_text("📂 <b>Filter Products by Category:</b>\nSelect a category below to view only its products:", reply_markup=kb, parse_mode='HTML')
    elif data == "admin_manage_prods_search":
        if state:
            await state.set_state(AdminStates.wait_for_search_product)
        return await call.message.edit_text("🔍 <b>Search Products</b>\n\nSend Product ID, Panel Name, or Package Name to search:", reply_markup=admin_back_kb(), parse_mode='HTML')

    if cat_filter:
        prods = db_query("SELECT id, name, category, panel_name, stock, is_active FROM products WHERE category LIKE ?", (cat_filter + '%',), fetchall=True)
    else:
        prods = db_query("SELECT id, name, category, panel_name, stock, is_active FROM products", fetchall=True)
    if prods is None:
        logger.error("Manage Products failed: products query returned None")
        return await call.answer("Database error loading products. Check bot_activity.log.", show_alert=True)
    prods = sorted(prods, key=lambda row: (natural_sort_key(row[2]), natural_sort_key(row[3]), product_name_sort_key(row[1])))
    if not prods:
        kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="🔙 Back", callback_data="admin_manage_prods_p_1")]])
        return await call.message.edit_text("📦 Store Database is empty or no products match filter.", reply_markup=kb, parse_mode='HTML')
        
    total_items = len(prods)
    total_pages = max(1, math.ceil(total_items / PAGE_SIZE))
    page = max(1, min(page, total_pages))
    
    start_idx = (page - 1) * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    page_prods = prods[start_idx:end_idx]
    
    kb = make_inline_kb(inline_keyboard=[])
    for p in page_prods:
        status_dot = "🟢" if p[5] else "🔴"
        p_panel = p[3] if p[3] is not None else ""
        btn_text = f"{status_dot} [{p[0]}] {p_panel} - {p[1]} (Stock: {p[4]})"
        kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"admin_view_p_{p[0]}")])
        
    # Navigation row
    nav_row = []
    cat_suffix = f"_c_{cat_filter}" if cat_filter else ""
    if page > 1:
        nav_row.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"admin_manage_prods_p_{page - 1}{cat_suffix}"))
    nav_row.append(InlineKeyboardButton(text=f"📄 {page}/{total_pages} ({total_items})", callback_data="ignore_stock_click"))
    if page < total_pages:
        nav_row.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"admin_manage_prods_p_{page + 1}{cat_suffix}"))
    kb.inline_keyboard.append(nav_row)
    
    # Filter & Search row
    filter_btn_text = f"📂 Category: {cat_filter[:12]}..." if cat_filter else "📂 Filter by Category"
    kb.inline_keyboard.append([
        InlineKeyboardButton(text=filter_btn_text, callback_data="admin_manage_prods_filter_menu"),
        InlineKeyboardButton(text="🔍 Search Product", callback_data="admin_manage_prods_search")
    ])
    if cat_filter:
        kb.inline_keyboard.append([InlineKeyboardButton(text="🌐 Clear Filter (Show All)", callback_data="admin_manage_prods_p_1")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))])
    
    filter_msg = f" (Category: <b>{cat_filter}</b>)" if cat_filter else ""
    await call.message.edit_text(f"📦 <b>Database Editor: Select Node to modify</b>{filter_msg}\nShowing {len(page_prods)} of {total_items} products:", reply_markup=kb, parse_mode='HTML')

@dp.message(AdminStates.wait_for_search_product)
async def process_product_search(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    query = m.text.strip()
    if not query:
        return await m.answer("❌ Search query cannot be empty.", reply_markup=admin_kb())
        
    if query.isdigit():
        prods = db_query("SELECT id, name, category, panel_name, stock, is_active FROM products WHERE id=? OR panel_name LIKE ? OR name LIKE ?", (int(query), f"%{query}%", f"%{query}%"), fetchall=True)
    else:
        prods = db_query("SELECT id, name, category, panel_name, stock, is_active FROM products WHERE panel_name LIKE ? OR name LIKE ? OR category LIKE ?", (f"%{query}%", f"%{query}%", f"%{query}%"), fetchall=True)
        
    if not prods:
        kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="🔙 Back to Products", callback_data="admin_manage_prods_p_1")]])
        await m.answer(f"❌ No products matched '<code>{query}</code>'.", reply_markup=kb, parse_mode='HTML')
        return await state.clear()
        
    kb = make_inline_kb(inline_keyboard=[])
    for p in prods[:15]:
        status_dot = "🟢" if p[5] else "🔴"
        p_name = p[3] if p[3] is not None else ""
        btn_text = f"{status_dot} [{p[0]}] {p_name} - {p[1]} (Stock: {p[4]})"
        kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"admin_view_p_{p[0]}")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="📦 Back to Product Manager", callback_data="admin_manage_prods_p_1")])
    await m.answer(f"🔍 <b>Found {len(prods)} products for '<code>{query}</code>':</b>\nSelect product to modify stock, keys, API duration:", reply_markup=kb, parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("admin_view_p_"))
async def admin_view_product(call: CallbackQuery, p_id: Optional[int] = None):
    if not is_admin(call.from_user.id): return
    try:
        if p_id is None:
            p_id = int(call.data.split("_")[3])
        prod = db_query("SELECT * FROM products WHERE id=?", (p_id,), fetchone=True)
        if not prod: return await call.answer("❌ Architecture fault: Node lost!", show_alert=True)
        panel_name = prod[2] if prod[2] is not None else ""
        price_inr = float(prod[4]) if prod[4] is not None and prod[4] != "" else 0.0
        reseller_price = float(prod[5]) if prod[5] is not None and prod[5] != "" else 0.0
        provider_val = str(prod[15] if len(prod) > 15 and prod[15] else 'bunty').lower()
        provider_labels = {"bunty": "⚡ Bunty API", "license_manager": "🔑 License Manager API", "hk_tamim": "🗝️ HK Tamim API", "dripclient": "💧 Drip Client API", "adminshops": "🛍️ Admin Shops API", "manual": "📦 Manual Stock"}
        if prod[11]:
            api_stock_mode = f"{provider_labels.get(provider_val, provider_val)} (API ID: {html.escape(str(prod[12] or 'Not set'))})"
        else:
            api_stock_mode = "📦 Manual Stock (Vault)"
        payload_link = prod[7] if prod[7] else "None"
        visibility = "Active" if prod[10] else "Hidden"
        is_maint = is_product_in_maintenance(p_id)
        maint_mode = '🟠 In Maintenance (Blocked)' if is_maint else '🟢 Normal (Purchasable)'
        text = (
            f"📦 <b><u>NODE DEEP DIVE DETAILS</u></b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"<b>ID:</b> <code>{prod[0]}</code>\n"
            f"<b>Panel Group:</b> {prod[1]}\n"
            f"<b>Panel Name:</b> {panel_name}\n"
            f"<b>Package Date/Time:</b> {prod[3]}\n"
            f"<b>Standard Price:</b> ₹{price_inr:.2f}\n"
            f"👑 <b>Wholesale Price:</b> ₹{reseller_price:.2f}\n"
            f"<b>Vault Stock:</b> {prod[6]}\n"
            f"<b>API Mode:</b> {api_stock_mode}\n"
            f"<b>Payload Link:</b> {payload_link}\n"
            f"<b>Time Config:</b> {prod[8]}\n"
            f"<b>HWID Limit:</b> {prod[9]}\n"
            f"<b>Visibility:</b> {visibility}\n"
            f"<b>Maintenance:</b> {maint_mode}\n"
            f"━━━━━━━━━━━━━━━━━━"
        )
        toggle_btn_text = "Hide Product 👁‍🗨" if prod[10] else "Unhide Product 👁"
        toggle_maint_btn_text = "Maint OFF 🟢" if is_maint else "Maint ON 🟠"
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="Switch API Provider 🔄", callback_data=f"switch_provider_{p_id}", icon_custom_emoji_id=get_emoji_icon("info_icon")),
             InlineKeyboardButton(text="Edit API PID 🆔", callback_data=f"edit_p_{p_id}_pid", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
            [InlineKeyboardButton(text="Edit Panel Group 🏷️", callback_data=f"edit_p_{p_id}_cat", icon_custom_emoji_id=get_emoji_icon("info_icon")), 
             InlineKeyboardButton(text="Edit Panel Name 🏷️", callback_data=f"edit_p_{p_id}_panel_name", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
            [InlineKeyboardButton(text="Edit Package Name ✏️", callback_data=f"edit_p_{p_id}_name", icon_custom_emoji_id=get_emoji_icon("info_icon")),
             InlineKeyboardButton(text="Set Position", callback_data=f"pkg_pos_{p_id}", icon_custom_emoji_id=get_emoji_icon("grid_id"))],
            [InlineKeyboardButton(text="Edit Price 💰", callback_data=f"edit_p_{p_id}_price", icon_custom_emoji_id=get_emoji_icon("money_icon")), 
             InlineKeyboardButton(text="Edit R-Price 👑", callback_data=f"edit_p_{p_id}_rprice", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
            [InlineKeyboardButton(text="Edit Validity ⏳", callback_data=f"edit_p_{p_id}_validity", icon_custom_emoji_id=get_emoji_icon("info_icon")), 
             InlineKeyboardButton(text="Edit Device 📱", callback_data=f"edit_p_{p_id}_device", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
            [InlineKeyboardButton(text="Edit API Duration ⏱️", callback_data=f"edit_p_{p_id}_api_duration", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
            [InlineKeyboardButton(text="📝 Edit Product Description", callback_data=f"edit_p_{p_id}_description", icon_custom_emoji_id=get_emoji_icon("info_icon")), InlineKeyboardButton(text="🎬 Set/Change Product Video", callback_data=f"edit_p_{p_id}_video", icon_custom_emoji_id=get_emoji_icon("tutorial"))],
            [InlineKeyboardButton(text="Edit APK Link 🔗", callback_data=f"edit_p_{p_id}_apk", icon_custom_emoji_id=get_emoji_icon("info_icon")), 
             InlineKeyboardButton(text="Add Keys ➕", callback_data=f"edit_p_{p_id}_keys", icon_custom_emoji_id=get_emoji_icon("add_balance"))],
            [InlineKeyboardButton(text="Add to Stock 📦➕", callback_data=f"edit_p_{p_id}_stock_add", icon_custom_emoji_id=get_emoji_icon("add_balance"))],
            [InlineKeyboardButton(text="Delete Key 🗑", callback_data=f"delkey_p_{p_id}", icon_custom_emoji_id=get_emoji_icon("back")), 
             InlineKeyboardButton(text=toggle_btn_text, callback_data=f"toggle_p_{p_id}", icon_custom_emoji_id=get_emoji_icon("check_icon"))],
            [InlineKeyboardButton(text=f"🛠️ {toggle_maint_btn_text}", callback_data=f"adm_pmaint_single_{p_id}", icon_custom_emoji_id=get_emoji_icon("shield_icon")),
             InlineKeyboardButton(text="Nuke Full Node 🗑", callback_data=f"delete_p_{p_id}", icon_custom_emoji_id=get_emoji_icon("back"))],
            [InlineKeyboardButton(text="BACK", callback_data="admin_manage_prods", icon_custom_emoji_id=get_emoji_icon("back"))]
        ])
        await call.message.edit_text(text, reply_markup=kb, disable_web_page_preview=True, parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error in admin_view_product: {e}")
        await call.message.edit_text(f"❌ Error loading product: {str(e)}", reply_markup=admin_back_kb(), parse_mode='HTML')

@dp.callback_query(F.data.startswith("switch_provider_"))
async def switch_product_provider_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="⚡ Switch to Bunty API (AdminPanels)", callback_data=f"setapi_bunty_{p_id}")],
        [InlineKeyboardButton(text="🔑 Switch to License Manager", callback_data=f"setapi_lm_{p_id}")],
        [InlineKeyboardButton(text="🗝️ Switch to HK Tamim", callback_data=f"setapi_hktamim_{p_id}")],
        [InlineKeyboardButton(text="💧 Switch to Drip Client", callback_data=f"setapi_dripclient_{p_id}")],
        [InlineKeyboardButton(text="🛍️ Switch to Admin Shops", callback_data=f"setapi_adminshops_{p_id}")],
        [InlineKeyboardButton(text="📦 Switch to Manual Keys", callback_data=f"setapi_manual_{p_id}")],
        [InlineKeyboardButton(text="🔙 Back", callback_data=f"admin_view_p_{p_id}")]
    ], _width=1)
    await call.message.edit_text(
        f"🔄 <b>Select Key Source for Product ID #{p_id}:</b>\n\n"
        "⚡ <b>Bunty API</b> · AdminPanels Reseller API\n"
        "🔑 <b>License Manager</b> · Bearer token API\n"
        "🗝️ <b>HK Tamim</b> · X-API-Token API\n"
        "💧 <b>Drip Client</b> · X-API-Token API\n"
        "🛍️ <b>Admin Shops</b> · Bearer token API\n"
        "📦 <b>Manual Stock</b> · Pre-loaded keys from vault",
        reply_markup=kb, parse_mode='HTML'
    )

@dp.callback_query(F.data.startswith("setapi_"))
async def set_product_api_choice(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try:
        parts = call.data.split("_")
        choice = parts[1]
        p_id = int(parts[-1])
    except (ValueError, IndexError):
        return await call.answer("Invalid provider selection. Reopen Manage Products.", show_alert=True)
    provider_map = {"bunty": "bunty", "lm": "license_manager", "hktamim": "hk_tamim", "dripclient": "dripclient", "adminshops": "adminshops"}
    if choice == "manual":
        db_query("UPDATE products SET external_enabled=0, api_provider='manual' WHERE id=?", (p_id,))
        msg = "Switched to Manual Keys!"
    elif choice in provider_map:
        provider = provider_map[choice]
        # Re-enable external fulfilment and retain existing API PID; prompt admin to edit PID if needed.
        db_query("UPDATE products SET external_enabled=1, api_provider=? WHERE id=?", (provider, p_id))
        msg = f"Switched to { {'bunty':'Bunty','license_manager':'License Manager','hk_tamim':'HK Tamim','dripclient':'Drip Client','adminshops':'Admin Shops'}[provider] } API. Check this product's API PID before selling."
    else:
        return await call.answer("Unknown API provider.", show_alert=True)
    await call.answer(msg, show_alert=True)
    await admin_view_product(call, p_id=p_id)

@dp.callback_query(F.data.startswith("toggle_p_"))
async def admin_toggle_product(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    current = db_query("SELECT is_active FROM products WHERE id=?", (p_id,), fetchone=True)[0]
    new_val = 0 if current == 1 else 1
    db_query("UPDATE products SET is_active=? WHERE id=?", (new_val, p_id))
    await call.answer("Visibility updated successfully!", show_alert=True)
    await admin_view_product(call, p_id=p_id)

@dp.callback_query(F.data.startswith("adm_pmaint_single_"))
async def admin_toggle_single_product_maint(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try:
        p_id = int(call.data.split("_")[3])
    except Exception:
        return await call.answer("Invalid product ID", show_alert=True)
    cur = is_product_in_maintenance(p_id)
    new_val = 0 if cur else 1
    db_query("UPDATE products SET is_maintenance=? WHERE id=?", (new_val, p_id))
    status_msg = "🟠 Maintenance ON (Users blocked)" if new_val else "🟢 Maintenance OFF (Active)"
    await call.answer(f"Status: {status_msg}", show_alert=True)
    await admin_view_product(call, p_id=p_id)

# ==============================================================================
# PRODUCT MAINTENANCE SYSTEM (ADMIN CONTROL PANEL - MERGED BY PRODUCT)
# ==============================================================================
async def _render_admin_product_maintenance(call: CallbackQuery, page: int = 0):
    """Render Product Maintenance control panel grouped by product name (merged durations)."""
    if not is_admin(call.from_user.id):
        return
    try:
        # Group packages by product (panel_name if set, otherwise name)
        rows = db_query("""
            SELECT 
                CASE 
                    WHEN panel_name IS NOT NULL AND TRIM(panel_name) != '' THEN TRIM(panel_name) 
                    ELSE TRIM(name) 
                END AS prod_name,
                MIN(category) AS category,
                MIN(id) AS sample_id,
                COUNT(*) AS total_pkgs,
                SUM(CASE WHEN COALESCE(is_maintenance, 0) = 1 THEN 1 ELSE 0 END) AS maint_pkgs
            FROM products
            GROUP BY CASE 
                WHEN panel_name IS NOT NULL AND TRIM(panel_name) != '' THEN TRIM(panel_name) 
                ELSE TRIM(name) 
            END
            ORDER BY prod_name ASC
        """, fetchall=True) or []

        prods = []
        for row in rows:
            if not row or len(row) < 5:
                continue
            prod_name = row[0] or "Unknown"
            category = row[1] or ""
            sample_id = int(row[2])
            total_pkgs = int(row[3] or 0)
            maint_pkgs = int(row[4] or 0)
            is_maint = (maint_pkgs > 0)
            prods.append((prod_name, category, sample_id, total_pkgs, is_maint, maint_pkgs))

        if not prods:
            text = "🛠️ <b>Product Maintenance Panel</b>\n\nNo products found in the store database."
            kb = make_inline_kb(inline_keyboard=[
                [InlineKeyboardButton(text="🔙 Back to Admin", callback_data="admin_panel_back")]
            ])
            if call.message:
                try: await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
                except Exception: await call.message.answer(text, reply_markup=kb, parse_mode='HTML')
            return

        per_page = 10
        total_pages = max(1, (len(prods) + per_page - 1) // per_page)
        page = max(0, min(int(page), total_pages - 1))
        start = page * per_page
        current = prods[start:start + per_page]

        maint_count = sum(1 for p in prods if p[4])
        active_count = len(prods) - maint_count

        keyboard = []
        for prod_name, category, sample_id, total_pkgs, is_maint, maint_pkgs in current:
            status_icon = "🟠 [MAINT]" if is_maint else "🟢 [ACTIVE]"
            label = f"{status_icon} {prod_name}"
            label = label[:60]
            keyboard.append([
                InlineKeyboardButton(
                    text=label,
                    callback_data=f"adm_pmaint_t_{sample_id}_{page}"
                )
            ])

        # Batch actions: All ON / All OFF
        keyboard.append([
            InlineKeyboardButton(text="🟠 All Maint ON", callback_data=f"adm_pmaint_all_on_{page}"),
            InlineKeyboardButton(text="🟢 All Maint OFF", callback_data=f"adm_pmaint_all_off_{page}"),
        ])

        # Pagination
        if total_pages > 1:
            nav = []
            if page > 0:
                nav.append(InlineKeyboardButton(text="⬅️ Previous", callback_data=f"adm_pmaint_p_{page-1}"))
            nav.append(InlineKeyboardButton(text=f"📄 {page+1}/{total_pages}", callback_data="adm_pmaint_noop"))
            if page < total_pages - 1:
                nav.append(InlineKeyboardButton(text="Next ➡️", callback_data=f"adm_pmaint_p_{page+1}"))
            keyboard.append(nav)

        keyboard.append([InlineKeyboardButton(text="🔙 Back to Admin", callback_data="admin_panel_back")])

        text = (
            "🛠️ <b><u>PRODUCT MAINTENANCE CONTROL PANEL</u></b>\n"
            "━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
            "Click on any product below to toggle maintenance for <b>all its packages/durations</b> ON or OFF.\n\n"
            "• 🟠 <b>MAINT</b>: Users attempting to buy any duration will see an instant maintenance alert and order will be blocked.\n"
            "• 🟢 <b>ACTIVE</b>: Normal purchase flow is open for all durations.\n\n"
            f"📊 <b>Total Products:</b> {len(prods)}\n"
            f"🟠 <b>Under Maintenance:</b> {maint_count}\n"
            f"🟢 <b>Normal / Purchasable:</b> {active_count}\n"
            f"📄 <b>Page:</b> {page+1}/{total_pages}\n"
            "━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
            "<i>Click any product button below to instantly flip its state:</i>"
        )
        if call.message:
            await call.message.edit_text(text, reply_markup=make_inline_kb(inline_keyboard=keyboard), parse_mode='HTML')
    except Exception as e:
        logger.exception("Product Maintenance UI error")
        if call.message:
            try:
                await call.message.edit_text(
                    f"❌ <b>Maintenance UI error:</b> {e}",
                    reply_markup=make_inline_kb(inline_keyboard=[
                        [InlineKeyboardButton(text="🔄 Retry", callback_data="admin_prod_maint")],
                        [InlineKeyboardButton(text="🔙 Back to Admin", callback_data="admin_panel_back")]
                    ]),
                    parse_mode='HTML'
                )
            except Exception:
                pass

@dp.callback_query(F.data == "admin_prod_maint")
async def admin_prod_maint_entry(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try: await call.answer()
    except Exception: pass
    await _render_admin_product_maintenance(call, 0)

@dp.callback_query(F.data.regexp(r"^adm_pmaint_p_\d+$"))
async def admin_prod_maint_page(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try: page = int(call.data.rsplit("_", 1)[1])
    except Exception: return await call.answer("Invalid page", show_alert=True)
    try: await call.answer()
    except Exception: pass
    await _render_admin_product_maintenance(call, page)

@dp.callback_query(F.data == "adm_pmaint_noop")
async def admin_prod_maint_noop(call: CallbackQuery):
    if is_admin(call.from_user.id):
        await call.answer("Current page", show_alert=False)

@dp.callback_query(F.data.regexp(r"^adm_pmaint_t_\d+_\d+$"))
async def admin_prod_maint_toggle(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try:
        parts = call.data.split("_")
        pid = int(parts[3])
        page = int(parts[4])
    except Exception:
        return await call.answer("Invalid product/page", show_alert=True)
    
    row = db_query("SELECT name, panel_name FROM products WHERE id=?", (pid,), fetchone=True)
    if not row:
        return await call.answer("❌ Product not found", show_alert=True)
    
    panel_val = (row[1] or "").strip()
    name_val = (row[0] or "").strip()
    prod_name = panel_val if panel_val else name_val

    # Check current maintenance count for all packages of this product
    # Resolve the exact product group from the selected sample row.  Older code
    # matched only panel_name globally, so identical panel names in different
    # categories could toggle the wrong rows.  We now scope the toggle to the
    # selected category + panel (or category + package name fallback).
    exact = db_query("SELECT category, panel_name, name FROM products WHERE id=?", (pid,), fetchone=True)
    if not exact:
        return await call.answer("❌ Product group not found", show_alert=True)
    category_val = (exact[0] or '').strip()
    panel_exact = (exact[1] or '').strip()
    name_exact = (exact[2] or '').strip()
    if panel_exact:
        group_where = "category=? AND TRIM(panel_name)=?"
        group_params = (category_val, panel_exact)
        prod_name = panel_exact
    else:
        group_where = "category=? AND (panel_name IS NULL OR TRIM(panel_name)='') AND TRIM(name)=?"
        group_params = (category_val, name_exact)
        prod_name = name_exact

    stats = db_query(
        f"SELECT COUNT(*), SUM(CASE WHEN COALESCE(is_maintenance,0)=1 THEN 1 ELSE 0 END) "
        f"FROM products WHERE {group_where}",
        group_params, fetchone=True
    )
    total_pkgs = int(stats[0] or 0) if stats else 0
    maint_pkgs = int(stats[1] or 0) if stats and stats[1] is not None else 0
    new_val = 0 if maint_pkgs > 0 else 1
    db_query(f"UPDATE products SET is_maintenance=? WHERE {group_where}", (new_val, *group_params))

    status_msg = "🟠 MAINTENANCE (Users Blocked)" if new_val else "🟢 ACTIVE (Purchasable)"
    await call.answer(f"✅ {prod_name}\n({total_pkgs} durations updated)\nStatus: {status_msg}", show_alert=True)
    await _render_admin_product_maintenance(call, page)

@dp.callback_query(F.data.regexp(r"^adm_pmaint_all_(on|off)_\d+$"))
async def admin_prod_maint_toggle_all(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try:
        parts = call.data.split("_")
        mode = parts[3]
        page = int(parts[4])
    except Exception:
        return await call.answer("Invalid parameters", show_alert=True)
    val = 1 if mode == "on" else 0
    db_query("UPDATE products SET is_maintenance=?", (val,))
    msg = "🟠 All products put into Maintenance Mode!" if val else "🟢 All products restored to Active Mode!"
    await call.answer(msg, show_alert=True)
    await _render_admin_product_maintenance(call, page)


# ==============================================================================
# QUICK STOCK ADD — Admin Main Panel shortcut
# ==============================================================================
QUICK_STOCK_PAGE_SIZE = 10

@dp.callback_query(F.data == "admin_quick_stock")
async def admin_quick_stock_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await _show_quick_stock_list(call, page=1)

@dp.callback_query(F.data.startswith("qs_page_"))
async def admin_quick_stock_page(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    page = int(call.data.split("_")[2])
    await _show_quick_stock_list(call, page=page)

async def _show_quick_stock_list(call: CallbackQuery, page: int = 1):
    """Show paginated list of all active products for quick stock add."""
    products = db_query(
        "SELECT id, category, panel_name, name, stock, external_enabled FROM products WHERE is_active=1 ORDER BY category, panel_name, name",
        fetchall=True
    )
    if not products:
        return await call.message.edit_text(
            "❌ <b>No active products found.</b>\n\nAdd products first via 'Add Product'.",
            reply_markup=make_inline_kb(inline_keyboard=[[
                InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))
            ]]),
            parse_mode='HTML'
        )

    total = len(products)
    total_pages = max(1, (total + QUICK_STOCK_PAGE_SIZE - 1) // QUICK_STOCK_PAGE_SIZE)
    page = max(1, min(page, total_pages))
    start = (page - 1) * QUICK_STOCK_PAGE_SIZE
    page_items = products[start:start + QUICK_STOCK_PAGE_SIZE]

    kb = make_inline_kb(inline_keyboard=[])
    for prod in page_items:
        p_id, category, panel_name, pkg_name, stock, ext_enabled = prod
        stock_val = stock or 0
        stock_lbl = "♾️ API" if ext_enabled else f"📦 {stock_val}"
        btn_label = f"{panel_name} › {pkg_name}  [{stock_lbl}]"
        kb.inline_keyboard.append([
            InlineKeyboardButton(
                text=btn_label,
                callback_data=f"qs_select_{p_id}",
                icon_custom_emoji_id=get_emoji_icon("add_balance")
            )
        ])

    # Pagination row
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"qs_page_{page-1}"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"qs_page_{page+1}"))
    if nav:
        kb.inline_keyboard.append(nav)

    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))
    ])

    await call.message.edit_text(
        f"📦 <b>Quick Add Stock</b>\n"
        f"<i>Page {page}/{total_pages} — {total} products</i>\n\n"
        "👇 Select the product to add stock:\n"
        "<i>(Format: Panel › Package  [Current Stock])</i>",
        reply_markup=kb,
        parse_mode='HTML'
    )

@dp.callback_query(F.data.startswith("qs_select_"))
async def admin_quick_stock_select(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    prod = db_query(
        "SELECT id, panel_name, name, stock, external_enabled FROM products WHERE id=?",
        (p_id,), fetchone=True
    )
    if not prod:
        return await call.answer("❌ Product not found!", show_alert=True)
    _, panel_name, pkg_name, current_stock, ext_enabled = prod
    stock_val = current_stock or 0

    await state.update_data(qs_prod_id=p_id, qs_prod_name=f"{panel_name} › {pkg_name}")
    await state.set_state(AdminStates.quick_stock_qty)

    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="10", callback_data="qs_qty_10"),
         InlineKeyboardButton(text="25", callback_data="qs_qty_25"),
         InlineKeyboardButton(text="50", callback_data="qs_qty_50")],
        [InlineKeyboardButton(text="100", callback_data="qs_qty_100"),
         InlineKeyboardButton(text="200", callback_data="qs_qty_200"),
         InlineKeyboardButton(text="500", callback_data="qs_qty_500")],
        [InlineKeyboardButton(text="Cancel", callback_data="admin_quick_stock", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text(
        f"📦 <b>Add Stock</b>\n\n"
        f"Product: <b>{panel_name} › {pkg_name}</b>\n"
        f"Current Stock: <code>{stock_val}</code>\n\n"
        "👇 Tap a quick amount or type a custom number:",
        reply_markup=kb,
        parse_mode='HTML'
    )

@dp.callback_query(F.data.startswith("qs_qty_"))
async def admin_quick_stock_qty_btn(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    qty = int(call.data.split("_")[2])
    data = await state.get_data()
    p_id = data.get("qs_prod_id")
    prod_name = data.get("qs_prod_name", "Unknown")
    if not p_id:
        return await call.answer("❌ Session expired. Please try again.", show_alert=True)
    await _do_quick_stock_add(call.message, state, p_id, prod_name, qty)

@dp.message(AdminStates.quick_stock_qty)
async def admin_quick_stock_qty_msg(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    data = await state.get_data()
    p_id = data.get("qs_prod_id")
    prod_name = data.get("qs_prod_name", "Unknown")
    if not p_id:
        return await m.answer("❌ Session expired. Please go back and try again.")
    try:
        qty = int(m.text.strip())
        if qty <= 0 or qty > 100000:
            raise ValueError
    except ValueError:
        return await m.answer("❌ Enter a valid whole number between 1 and 100000.\nExample: <code>50</code>", parse_mode='HTML')
    await _do_quick_stock_add(m, state, p_id, prod_name, qty)

async def _do_quick_stock_add(msg_or_call, state: FSMContext, p_id: int, prod_name: str, qty: int):
    """Actually add stock to the product and show result."""
    db_query("UPDATE products SET stock=COALESCE(stock,0)+? WHERE id=?", (qty, p_id))
    new_stock = db_query("SELECT stock FROM products WHERE id=?", (p_id,), fetchone=True)
    new_stock_val = new_stock[0] if new_stock else qty
    await state.clear()
    result_text = (
        f"✅ <b>Stock Added Successfully!</b>\n\n"
        f"📦 Product: <b>{prod_name}</b>\n"
        f"➕ Added: <code>{qty}</code> units\n"
        f"📊 New Total Stock: <code>{new_stock_val}</code>"
    )
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Add More Stock", callback_data="admin_quick_stock", icon_custom_emoji_id=get_emoji_icon("add_balance"))],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    if hasattr(msg_or_call, 'edit_text'):
        await msg_or_call.edit_text(result_text, reply_markup=kb, parse_mode='HTML')
    else:
        await msg_or_call.answer(result_text, reply_markup=kb, parse_mode='HTML')

# ==============================================================================
# FIX: Edit product field – correctly handle different data types
# ==============================================================================
@dp.callback_query(F.data.startswith("edit_p_"))
async def start_edit_product(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    parts = call.data.split("_")
    p_id = int(parts[2]); field = "_".join(parts[3:])
    await state.update_data(edit_p_id=p_id, edit_field=field)
    if field == 'keys':
        await call.message.edit_text("📥 <b>Vault Injection</b>\nPaste the <b>NEW KEYS</b> to append to the stock (1 key per line):", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_add_keys)
    elif field == 'stock_add':
        await call.message.edit_text(
            "📦 <b>Add to Stock</b>\n\nEnter how many stock units to add.\nExample: <code>100</code> or <code>200</code>",
            reply_markup=admin_back_kb(), parse_mode='HTML'
        )
        await state.set_state(AdminStates.wait_for_new_value)
    else:
        field_name_map = {'cat': 'New Panel Group/Category Name', 'panel_name': 'New Panel Name', 'name': 'New Package/Date Name', 'price': 'New Standard Price in ₹', 'rprice': 'New Reseller Price in ₹', 'validity': 'New Time Validity String', 'device': 'New HWID Limit String', 'apk': 'New Payload Link (or type "none")', 'api_duration': 'Exact XYZ API Duration (e.g. 1 Day)', 'pid': 'New API Product ID (PID)', 'stock_add': 'Stock units to add'}
        await call.message.edit_text(f"✏️ Input the required data for: <b>{field_name_map.get(field, field)}</b>", reply_markup=admin_back_kb(), parse_mode='HTML')
        await state.set_state(AdminStates.wait_for_new_value)

@dp.message(AdminStates.wait_for_new_value)
async def process_edit_value(m: Message, state: FSMContext):
    data = await state.get_data()
    p_id = data['edit_p_id']; field = data['edit_field']; new_val = m.text.strip()
    
    # If field is price or reseller price, convert to float
    if field in ['price', 'rprice']:
        try:
            new_val = float(new_val)
        except ValueError:
            return await m.answer("❌ Invalid number format. Please enter a valid price (e.g., 500).")
    # If field is apk, store as string (don't convert to float!)
    elif field == 'apk':
        new_val = "" if new_val.lower() == 'none' else new_val
    elif field == 'stock_add':
        try:
            add_qty = int(new_val)
            if add_qty <= 0 or add_qty > 100000:
                raise ValueError
        except ValueError:
            return await m.answer("❌ Enter a positive whole number up to 100000, e.g. 100 or 200.")
        db_query("UPDATE products SET stock=COALESCE(stock,0)+? WHERE id=?", (add_qty, p_id))
        new_stock = db_query("SELECT stock FROM products WHERE id=?", (p_id,), fetchone=True)[0]
        await m.answer(f"✅ <b>Stock Added!</b>\n\n➕ Added: <code>{add_qty}</code>\n📦 New Stock: <code>{new_stock}</code>", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
        return
    elif field == 'cat':
        new_val = new_val.upper()
        existing_cat = db_query("SELECT id FROM categories WHERE UPPER(name)=?", (new_val,), fetchone=True)
        if not existing_cat:
            max_order = db_query("SELECT COALESCE(MAX(sort_order), 0) FROM categories", fetchone=True)[0]
            db_query("INSERT INTO categories (name, sort_order) VALUES (?, ?)", (new_val, max_order + 1))
    # For all other fields (panel_name, name, validity, device), keep as string
    
    db_col_map = {'cat': 'category', 'panel_name': 'panel_name', 'name': 'name', 'price': 'price_inr', 'rprice': 'reseller_price', 'validity': 'validity', 'device': 'device_limit', 'apk': 'apk_link', 'api_duration': 'external_duration', 'pid': 'external_product_id'}
    db_query(f"UPDATE products SET {db_col_map.get(field, field)}=? WHERE id=?", (new_val, p_id))
    await m.answer("✅ <b>Node updated gracefully!</b>", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.message(AdminStates.wait_for_add_keys)
async def process_add_keys(m: Message, state: FSMContext):
    data = await state.get_data()
    p_id = data['edit_p_id']
    keys = [k.strip() for k in m.text.strip().split('\n') if k.strip()]
    if len(keys) == 0: return await m.answer("❌ Protocol breach: Zero valid keys found.", reply_markup=admin_kb(), parse_mode='HTML')
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    c = conn.cursor()
    for k in keys: c.execute("INSERT INTO product_keys (product_id, key_text) VALUES (?, ?)", (p_id, k))
    c.execute("UPDATE products SET stock = stock + ? WHERE id=?", (len(keys), p_id))
    conn.commit(); conn.close()
    await m.answer(f"✅ <b>Vault Secure!</b> {len(keys)} new keys appended and encrypted.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("delete_p_"))
async def admin_delete_product(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    prod = db_query("SELECT panel_name, name, category FROM products WHERE id=?", (p_id,), fetchone=True)
    if not prod:
        return await call.answer("❌ Product not found.", show_alert=True)
    panel_name, package_name, category = prod
    package_count = db_query(
        "SELECT COUNT(*) FROM products WHERE category=? AND panel_name=?",
        (category, panel_name), fetchone=True
    )
    count = int(package_count[0] or 0) if package_count else 1
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"☢️ YES — DELETE ALL {count} PACKAGES", callback_data=f"confirm_delete_product_{p_id}")],
        [InlineKeyboardButton(text="🔙 Cancel", callback_data=f"admin_view_p_{p_id}")]
    ])
    await call.message.edit_text(
        "⚠️ <b>DELETE PRODUCT — FINAL CONFIRMATION</b>\n\n"
        f"📂 Category: <b>{html.escape(str(category or '-'))}</b>\n"
        f"📦 Product/Panel: <b>{html.escape(str(panel_name or package_name or '-'))}</b>\n"
        f"🧩 Packages found: <b>{count}</b>\n\n"
        "This will permanently remove the complete product group and its unused vault keys.\n"
        "Purchase/order history will remain intact.",
        reply_markup=kb, parse_mode="HTML"
    )

@dp.callback_query(F.data.startswith("confirm_delete_product_"))
async def confirm_delete_product(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[-1])
    prod = db_query("SELECT panel_name, name, category FROM products WHERE id=?", (p_id,), fetchone=True)
    if not prod:
        return await call.answer("❌ Product already deleted.", show_alert=True)
    panel_name, package_name, category = prod
    rows = db_query("SELECT id FROM products WHERE category=? AND panel_name=?", (category, panel_name), fetchall=True) or []
    ids = [int(r[0]) for r in rows]
    for pid in ids:
        db_query("DELETE FROM product_keys WHERE product_id=?", (pid,))
        db_query("DELETE FROM products WHERE id=?", (pid,))
    log_activity(call.from_user.id, "ADMIN_DELETE_PRODUCT_GROUP", f"Category={category}, Panel={panel_name}, Packages={len(ids)}")
    await call.answer(f"☢️ Deleted complete product group ({len(ids)} packages).", show_alert=True)
    await admin_manage_prods(call)

@dp.callback_query(F.data.startswith("delkey_p_"))
async def admin_delete_key_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    p_id = int(call.data.split("_")[2])
    await state.update_data(del_p_id=p_id)
    await call.message.edit_text("🗑 Send the <b>exact string match</b> of the key you wish to purge from the vault:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_delete_key)

@dp.message(AdminStates.wait_for_delete_key)
async def process_delete_key(m: Message, state: FSMContext):
    data = await state.get_data()
    p_id = data['del_p_id']
    key_to_delete = m.text.strip()
    key_data = db_query("SELECT id, is_used FROM product_keys WHERE product_id=? AND key_text=?", (p_id, key_to_delete), fetchone=True)
    if not key_data: return await m.answer("❌ Key not found. Check logs and try again.", reply_markup=admin_back_kb(), parse_mode='HTML')
    if key_data[1] == 1: return await m.answer("⚠️ Action Blocked: This key has already been dispatched to a user.", reply_markup=admin_back_kb(), parse_mode='HTML')
    db_query("DELETE FROM product_keys WHERE id=?", (key_data[0],))
    db_query("UPDATE products SET stock = stock - 1 WHERE id=?", (p_id,))
    await m.answer(f"✅ Key <code>{key_to_delete}</code> securely purged from vault.\n📦 Database indices updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# 20. ADMIN TICKETS, BROADCAST, COUPONS
# ==============================================================================
@dp.callback_query(F.data == "admin_view_tickets")
async def admin_view_tickets(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    tickets = db_query("SELECT id, user_id, message, created_at FROM tickets WHERE status='Open' LIMIT 1", fetchall=True)
    if not tickets: return await call.answer("✅ Zero pending issues. Grid is clean!", show_alert=True)
    t = tickets[0]
    text = (f"🎫 <b><u>ACTIVE TICKET #{t[0]}</u></b>\n👤 <b>Origin UID:</b> <code>{t[1]}</code>\n📅 <b>Timestamp:</b> {t[3]}\n\n📝 <b>Payload:</b>\n{t[2]}")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Formulate Reply", callback_data=f"reply_ticket_{t[0]}_{t[1]}", icon_custom_emoji_id=get_emoji_icon("telegram"))],
        [InlineKeyboardButton(text="Force Close Ticket", callback_data=f"close_ticket_{t[0]}", icon_custom_emoji_id=get_emoji_icon("back"))],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("close_ticket_"))
async def close_ticket(call: CallbackQuery):
    ticket_id = call.data.split("_")[2]
    db_query("UPDATE tickets SET status='Closed' WHERE id=?", (ticket_id,))
    await call.answer("✅ Status set to Closed.", show_alert=True)
    await admin_view_tickets(call) 

@dp.callback_query(F.data.startswith("reply_ticket_"))
async def reply_ticket_start(call: CallbackQuery, state: FSMContext):
    data = call.data.split("_")
    ticket_id, user_id = data[2], data[3]
    await state.update_data(ticket_id=ticket_id, user_id=user_id)
    await call.message.edit_text(f"💬 Formulating reply for node <code>{user_id}</code>.\n\nType your message payload:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.ticket_reply_msg)

@dp.message(AdminStates.ticket_reply_msg)
async def send_ticket_reply(m: Message, state: FSMContext):
    data = await state.get_data()
    try:
        await bot.send_message(data['user_id'], f"📞 <b>Admin Reply (Ref #{data['ticket_id']}):</b>\n\n{m.text}", parse_mode='HTML')
        db_query("UPDATE tickets SET status='Closed' WHERE id=?", (data['ticket_id'],))
        await m.answer("✅ Payload delivered and connection closed successfully.", reply_markup=admin_kb(), parse_mode='HTML')
    except Exception as e: await m.answer(f"❌ Transmission Error: {e}", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_broadcast_btn")
async def admin_broadcast_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("📢 <b>Mass Broadcast Protocol</b>\n\nSend the rich message payload you wish to transmit globally across the grid:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.broadcast_msg)

@dp.message(AdminStates.broadcast_msg)
async def admin_broadcast_send(message: Message, state: FSMContext):
    users = db_query("SELECT user_id FROM users", fetchall=True)
    sent, failed = 0, 0
    m = await message.answer("⏳ Broadcast protocol initiated... Do not interrupt.", parse_mode='HTML')
    from aiogram.exceptions import TelegramRetryAfter, TelegramForbiddenError
    for index, u in enumerate(users, 1):
        try:
            await message.send_copy(chat_id=u[0])
            sent += 1
        except TelegramRetryAfter as exc:
            await asyncio.sleep(float(exc.retry_after) + 0.2)
            try:
                await message.send_copy(chat_id=u[0]); sent += 1
            except Exception:
                failed += 1
        except TelegramForbiddenError:
            failed += 1
        except Exception:
            failed += 1
        if index % 25 == 0:
            try: await m.edit_text(f"📢 Broadcast running…\nSent: {sent} | Failed: {failed} | Total: {len(users)}")
            except Exception: pass
        await asyncio.sleep(0.035)
    await m.edit_text(f"✅ <b>Global Broadcast Complete!</b>\n\n🟢 Nodes reached: {sent}\n🔴 Nodes failed/blocked: {failed}", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_create_coupon")
async def admin_create_coupon_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("🎟 Enter a highly secure alphanumeric sequence for the Promo Code:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.add_coupon_code)

@dp.message(AdminStates.add_coupon_code)
async def admin_coupon_code(m: Message, state: FSMContext):
    await state.update_data(code=m.text.strip().upper())
    await m.answer("💰 Enter the monetary reward payload in <b>RUPEES (₹)</b>:", parse_mode='HTML')
    await state.set_state(AdminStates.add_coupon_amount)

@dp.message(AdminStates.add_coupon_amount)
async def admin_coupon_amount(m: Message, state: FSMContext):
    try:
        await state.update_data(amount=float(m.text)) 
        await m.answer("👥 Enter the exact maximum threshold uses for this code:", parse_mode='HTML')
        await state.set_state(AdminStates.add_coupon_uses)
    except ValueError: await m.answer("❌ Non-numerical data detected. Aborting.")

@dp.message(AdminStates.add_coupon_uses)
async def admin_coupon_uses(m: Message, state: FSMContext):
    try:
        uses = int(m.text)
        data = await state.get_data()
        db_query("INSERT OR REPLACE INTO coupons (code, amount, uses_left) VALUES (?, ?, ?)", (data['code'], data['amount'], uses))
        await m.answer(f"✅ Protocol <b>{data['code']}</b> encoded!\nReward Vector: {fmt_curr(data['amount'])}\nThreshold Limit: {uses} executions.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Non-numerical data detected. Aborting.")

# ==============================================================================
# 21A. ADMIN BULK MONEY / PRICE / GATEWAY / COLOR CONTROLS
# ==============================================================================
@dp.callback_query(F.data == "admin_zero_all_balances")
async def admin_zero_all_balances(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    total = db_query("SELECT COUNT(*) FROM users WHERE COALESCE(balance,0) != 0", fetchone=True)
    affected = int(total[0] or 0) if total else 0
    db_query("UPDATE users SET balance=0")
    log_activity(call.from_user.id, "ADMIN_ZERO_ALL_BALANCES", f"Affected users: {affected}")
    await call.answer(f"✅ {affected} user balances reset to ₹0.", show_alert=True)
    await call.message.edit_text("🧹 <b>ALL USER BALANCES RESET</b>\n\nAffected users: <b>%d</b>\nCurrent balance for every user: <b>₹0</b>" % affected, reply_markup=admin_kb(), parse_mode="HTML")

@dp.callback_query(F.data == "admin_bulk_price_menu")
async def admin_bulk_price_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    count = db_query("SELECT COUNT(*) FROM products WHERE is_active=1", fetchone=True)
    n = int(count[0] or 0) if count else 0
    groups = get_common_validity_groups(active_only=True)
    kb = make_inline_kb(inline_keyboard=[])
    for idx, (key, group_count) in enumerate(groups[:30]):
        label = display_validity_group(key)
        kb.inline_keyboard.append([InlineKeyboardButton(
            text=f"⏱ {label}  •  {group_count} Products",
            callback_data=f"bulk_validity_group_{idx}"
        )])
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="🌐 ALL ACTIVE PRODUCTS", callback_data="bulk_validity_group_all")
    ])
    kb.inline_keyboard.append([InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel_back")])
    await call.message.edit_text(
        "💸 <b>PREMIUM PRICE CONTROL</b>\n\n"
        f"Active packages: <b>{n}</b>\n\n"
        "Select a <b>common validity</b> to change all matching products together.\n"
        "Example: <b>1 Over</b> will update every product whose validity is 1 Over, regardless of panel name.\n\n"
        "You can also choose ALL for a global price adjustment.",
        reply_markup=kb, parse_mode="HTML"
    )

@dp.callback_query(F.data.startswith("bulk_validity_group_"))
async def admin_bulk_validity_group(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    token = call.data.split("bulk_validity_group_", 1)[1]
    if token == "all":
        title = "ALL ACTIVE PRODUCTS"
        callback_prefix = "bulk_validity_apply_all"
        count = db_query("SELECT COUNT(*) FROM products WHERE is_active=1", fetchone=True)
    else:
        try:
            idx = int(token)
            groups = get_common_validity_groups(active_only=True)
            key, _ = groups[idx]
        except (ValueError, IndexError):
            return await call.answer("❌ Validity group expired. Open the menu again.", show_alert=True)
        title = display_validity_group(key)
        callback_prefix = f"bulk_validity_apply_{idx}"
        rows = db_query("SELECT validity, name FROM products WHERE is_active=1", fetchall=True) or []
        count = sum(1 for r in rows if product_matches_validity_group(r[0] if r else "", r[1] if len(r) > 1 else "", key))
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🔻 -5%", callback_data=f"{callback_prefix}_dec_5"), InlineKeyboardButton(text="🔺 +5%", callback_data=f"{callback_prefix}_inc_5")],
        [InlineKeyboardButton(text="🔻 -10%", callback_data=f"{callback_prefix}_dec_10"), InlineKeyboardButton(text="🔺 +10%", callback_data=f"{callback_prefix}_inc_10")],
        [InlineKeyboardButton(text="🔻 -20%", callback_data=f"{callback_prefix}_dec_20"), InlineKeyboardButton(text="🔺 +20%", callback_data=f"{callback_prefix}_inc_20")],
        [InlineKeyboardButton(text="🔻 -50%", callback_data=f"{callback_prefix}_dec_50"), InlineKeyboardButton(text="🔺 +50%", callback_data=f"{callback_prefix}_inc_50")],
        [InlineKeyboardButton(text="🔙 Back to Validity Groups", callback_data="admin_bulk_price_menu")]
    ])
    await call.message.edit_text(
        f"💰 <b>{html.escape(title)} PRICE CONTROL</b>\n\n"
        f"Matching active packages: <b>{int(count[0] or 0) if not isinstance(count, int) else count}</b>\n\n"
        "This change updates <b>Regular + Reseller</b> prices together.\n"
        "Choose the percentage below.",
        reply_markup=kb, parse_mode="HTML"
    )

@dp.callback_query(F.data.regexp(r"^bulk_validity_apply_(?:all|\d+)_(inc|dec)_(5|10|20|50)$"))
async def admin_bulk_validity_apply(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    parts = call.data.split("_")
    # all => [bulk, validity, apply, all, dec, 5]; indexed => [bulk, validity, apply, 3, dec, 5]
    target = parts[3]
    direction = parts[4]
    pct = float(parts[5])
    factor = 1 + (pct / 100 if direction == "inc" else -pct / 100)
    if target == "all":
        rows = db_query("SELECT id FROM products WHERE is_active=1", fetchall=True) or []
        ids = [int(r[0]) for r in rows]
        label = "ALL ACTIVE PRODUCTS"
    else:
        try:
            idx = int(target)
            groups = get_common_validity_groups(active_only=True)
            key, _ = groups[idx]
        except (ValueError, IndexError):
            return await call.answer("❌ Validity group expired. Open the menu again.", show_alert=True)
        rows = db_query("SELECT id, validity, name FROM products WHERE is_active=1", fetchall=True) or []
        ids = [int(r[0]) for r in rows if product_matches_validity_group(r[1] if len(r) > 1 else "", r[2] if len(r) > 2 else "", key)]
        label = display_validity_group(key)
    for pid in ids:
        db_query(
            "UPDATE products SET price_inr=ROUND(MAX(0, COALESCE(price_inr,0)*?),2), reseller_price=ROUND(MAX(0, COALESCE(reseller_price,0)*?),2) WHERE id=?",
            (factor, factor, pid)
        )
    sign = "+" if direction == "inc" else "-"
    log_activity(call.from_user.id, "ADMIN_VALIDITY_PRICE_ADJUST", f"{label}: {sign}{pct:g}% on {len(ids)} products")
    await call.answer(f"✅ {label}: {sign}{pct:g}% applied to {len(ids)} products.", show_alert=True)
    await admin_bulk_price_menu(call)

@dp.callback_query(F.data == "admin_binance_manual_setup")
async def admin_binance_manual_setup(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await call.answer()
    rate = get_setting("binance_usdt_rate", "90") or "90"
    pay_id = (get_setting("binance_address", "") or "").strip()
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🆔 Set / Change Binance Pay ID", callback_data="admin_binance_set_id")],
        [InlineKeyboardButton(text="💱 Set USDT → INR Rate", callback_data="admin_binance_set_rate")],
        [InlineKeyboardButton(text="⬅️ Back to Gateway Control", callback_data="admin_gateway_control")]])
    await safe_edit_text(call.message, f"🪙 <b>Binance Manual Payment</b>\nCurrent rate: <b>1 USDT = ₹{html.escape(str(rate))}</b>\nBinance Pay ID: <code>{html.escape(pay_id) if pay_id else 'Not configured'}</code>\n\nUsers see the admin Pay ID, submit payment screenshot + Binance TxID/order ID, and wait for manual approval/rejection. No QR is shown.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_binance_set_id")
async def admin_binance_set_id(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    await call.answer()
    await call.message.edit_text("🆔 Send the Binance Pay ID / payment identifier users should pay. Send /cancel to abort.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_binance_address)

@dp.callback_query(F.data == "admin_binance_upload_qr")
async def admin_binance_upload_qr(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await call.answer()
    await safe_edit_text(call.message, "📷 Send the Binance payment QR as a photo in this admin chat. The photo will be used by users during manual payment. Send /cancel to abort.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_binance_qr)

@dp.message(AdminStates.wait_for_binance_qr)
async def admin_binance_upload_qr_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    if (m.text or '').strip().lower() == '/cancel':
        await state.clear(); return await m.answer("Cancelled.", reply_markup=admin_kb())
    if not m.photo:
        return await m.answer("❌ Please upload the Binance QR as a photo, or send /cancel.")
    set_setting("binance_qr_file_id", m.photo[-1].file_id)
    await state.clear()
    await m.answer("✅ Binance QR saved. Users will see this QR when they choose Binance Pay.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_binance_set_rate")
async def admin_binance_set_rate(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await call.answer()
    await safe_edit_text(call.message, "Send the INR rate for 1 USDT (example: 90). This only calculates the requested wallet credit; admin must still verify the payment manually.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_binance_rate)

@dp.message(AdminStates.wait_for_binance_rate)
async def admin_binance_set_rate_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    try:
        rate = float((m.text or '').strip())
        if rate <= 0 or rate > 100000: raise ValueError
    except ValueError:
        return await m.answer("❌ Enter a valid positive rate, e.g. 90.")
    set_setting("binance_usdt_rate", str(rate))
    await state.clear()
    await m.answer(f"✅ Binance rate saved: 1 USDT = ₹{rate:g}.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_gateway_control")
async def admin_gateway_control(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    z = "ON" if gateway_enabled("zapupi") else "OFF"
    f = "ON" if gateway_enabled("famgateway") else "OFF"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"ZapUPI: {'🟢' if z=='ON' else '🔴'} {z}", callback_data="admin_toggle_gateway_zapupi")],
        [InlineKeyboardButton(text=f"FamGateway: {'🟢' if f=='ON' else '🔴'} {f}", callback_data="admin_toggle_gateway_famgateway")],
        [InlineKeyboardButton(text="🪙 Binance Pay ID / Rate", callback_data="admin_binance_manual_setup")],
        [InlineKeyboardButton(text="🔙 Back to Admin", callback_data="admin_panel_back")]
    ])
    await call.message.edit_text("💳 <b>PAYMENT GATEWAY CONTROL</b>\n\nON gateway buttons are shown to users and are available for wallet top-up + direct product payment.\nOFF gateways are hidden/blocked everywhere.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data.in_(["admin_toggle_gateway_zapupi", "admin_toggle_gateway_famgateway"]))
async def admin_toggle_gateway(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    name = "zapupi" if call.data.endswith("zapupi") else "famgateway"
    key = f"gateway_{name}_status"
    new = "OFF" if gateway_enabled(name) else "ON"
    set_setting(key, new)
    log_activity(call.from_user.id, "ADMIN_GATEWAY_TOGGLE", f"{name}={new}")
    await admin_gateway_control(call)

# ==============================================================================
# 21. ADMIN RESELLER & SPIN SETTINGS
# ==============================================================================
@dp.callback_query(F.data == "admin_reseller_menu")
async def admin_reseller_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    status_check = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    sys_status = status_check[0] if status_check else "ON"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🟢 Turn Reseller ON / Grant", callback_data="reseller_make", icon_custom_emoji_id=get_emoji_icon("reseller")),
         InlineKeyboardButton(text="🔴 Turn Reseller OFF / Remove", callback_data="reseller_remove", icon_custom_emoji_id=get_emoji_icon("reseller"))],
        [InlineKeyboardButton(text="🔄 Toggle One Reseller ON/OFF", callback_data="reseller_toggle", icon_custom_emoji_id=get_emoji_icon("reseller"))],
        [InlineKeyboardButton(text="Audit Active Resellers", callback_data="reseller_view", icon_custom_emoji_id=get_emoji_icon("history"))],
        [InlineKeyboardButton(text=f"{'🟢' if sys_status == 'ON' else '🔴'} Auto-Upgrade System: {sys_status}", callback_data="admin_toggle_reseller_sys", icon_custom_emoji_id=get_emoji_icon("check_icon") if sys_status == 'ON' else None)], 
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text("👑 <b>Wholesale Reseller Protocols</b>\nSelect administrative action:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_toggle_reseller_sys")
async def toggle_reseller_sys(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    res = db_query("SELECT value FROM settings WHERE key='reseller_system_status'", fetchone=True)
    current = res[0] if res else 'ON'
    new_status = 'OFF' if current == 'ON' else 'ON'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('reseller_system_status', ?)", (new_status,))
    await admin_reseller_menu(call)

@dp.callback_query(F.data.in_(["reseller_make", "reseller_remove", "reseller_toggle"]))
async def reseller_prompt_id(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    action = call.data
    await state.update_data(reseller_action=action)
    await call.message.edit_text("👤 Identify target node. Input <b>User ID</b> or <b>@username</b>:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.reseller_manage_id)

@dp.message(AdminStates.reseller_manage_id)
async def process_reseller_manage(m: Message, state: FSMContext):
    data = await state.get_data()
    target = m.text.strip()
    if target.startswith('@'): target = target[1:]
    user_q = db_query("SELECT user_id, first_name FROM users WHERE user_id=? OR username=? COLLATE NOCASE", (target, target), fetchone=True)
    if not user_q: return await m.answer("❌ Target completely ghosted. Not in database.", reply_markup=admin_back_kb(), parse_mode='HTML')
    u_id, u_name = user_q[0], user_q[1]
    action = data.get('reseller_action', 'reseller_make')
    if action == "reseller_make":
        db_query("UPDATE users SET is_reseller=1, reseller_since=?, account_type='Reseller' WHERE user_id=?", (datetime.now().strftime("%Y-%m-%d"), u_id))
        status_text = "ON — reseller access granted"
    elif action == "reseller_remove":
        db_query("UPDATE users SET is_reseller=0, account_type='Regular' WHERE user_id=?", (u_id,))
        status_text = "OFF — reseller access removed"
    else:
        current = db_query("SELECT is_reseller FROM users WHERE user_id=?", (u_id,), fetchone=True)
        turn_on = not bool(current[0] if current else 0)
        if turn_on:
            db_query("UPDATE users SET is_reseller=1, reseller_since=?, account_type='Reseller' WHERE user_id=?", (datetime.now().strftime("%Y-%m-%d"), u_id))
            status_text = "ON — reseller access granted"
        else:
            db_query("UPDATE users SET is_reseller=0, account_type='Regular' WHERE user_id=?", (u_id,))
            status_text = "OFF — reseller access removed"
    await m.answer(f"✅ <b>{html.escape(str(u_name or 'User'))}</b> (<code>{u_id}</code>)\nReseller status: <b>{status_text}</b>.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "reseller_view")
async def reseller_view(call: CallbackQuery):
    resellers = db_query("SELECT user_id, first_name, username FROM users WHERE is_reseller=1", fetchall=True)
    if not resellers: return await call.message.edit_text("📋 Zero active resellers found.", reply_markup=admin_back_kb(), parse_mode='HTML')
    text = "👑 <b><u>ACTIVE RESELLER AUDIT LOG</u></b> 👑\n━━━━━━━━━━━━━━━━━━\n"
    for r in resellers:
        uname = f"(@{r[2]})" if r[2] else ""
        text += f"👤 {r[1]} {uname}\n🆔 <code>{r[0]}</code>\n\n"
    await call.message.edit_text(text, reply_markup=admin_back_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_spin_menu")
async def admin_spin_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    status = db_query("SELECT value FROM settings WHERE key='spin_status'", fetchone=True)
    pool = db_query("SELECT value FROM settings WHERE key='daily_spin_pool'", fetchone=True)
    spent = db_query("SELECT value FROM settings WHERE key='daily_spin_spent'", fetchone=True)
    spent_date = db_query("SELECT value FROM settings WHERE key='daily_spin_spent_date'", fetchone=True)
    status_val = status[0] if status else 'ON'
    pool_val = float(pool[0]) if pool else 5.0
    spent_val = float(spent[0]) if spent else 0.0
    if (spent_date[0] if spent_date else '') != datetime.now().strftime('%Y-%m-%d'):
        spent_val = 0.0
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Append Reward Logic", callback_data="spin_add", icon_custom_emoji_id=get_emoji_icon("add_balance")), 
         InlineKeyboardButton(text="Drop Reward Logic", callback_data="spin_del", icon_custom_emoji_id=get_emoji_icon("back"))],
        [InlineKeyboardButton(text="Audit Configs", callback_data="spin_view", icon_custom_emoji_id=get_emoji_icon("history")), 
         InlineKeyboardButton(text="Set Daily ₹5 Pool", callback_data="spin_limit", icon_custom_emoji_id=get_emoji_icon("money_icon"))],
        [InlineKeyboardButton(text=f"{'🟢' if status_val == 'ON' else '🔴'} Master Toggle: {status_val}", callback_data="spin_toggle", icon_custom_emoji_id=get_emoji_icon("check_icon") if status_val == 'ON' else None)],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    rewards_count = db_query("SELECT COUNT(*) FROM spin_rewards", fetchone=True)[0] or 0
    await call.message.edit_text(
        f"🎰 <b>Advanced Ludo / Spin Control</b>\n\n"
        f"🟢 Status: <b>{status_val}</b>\n"
        f"🎁 Reward Rules: <b>{rewards_count}</b> configured\n"
        f"💰 <b>Daily Global Pool:</b> ₹{pool_val:.2f}\n"
        f"📊 <b>Used Today:</b> ₹{spent_val:.2f} / ₹{pool_val:.2f}\n"
        f"⏱ User cooldown: <b>24 hours</b>\n"
        f"🌟 VIP multiplier is capped by the same global pool.\n\n"
        "All users combined can receive at most the configured daily pool. Default is <b>₹5/day total</b>.",
        reply_markup=kb, parse_mode='HTML'
    )

@dp.callback_query(F.data == "spin_toggle")
async def spin_toggle(call: CallbackQuery):
    res = db_query("SELECT value FROM settings WHERE key='spin_status'", fetchone=True)
    current = res[0] if res else 'ON'
    new_status = 'OFF' if current == 'ON' else 'ON'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('spin_status', ?)", (new_status,))
    await admin_spin_menu(call)

@dp.callback_query(F.data == "admin_toggle_bot")
async def toggle_bot(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    res = db_query("SELECT value FROM settings WHERE key='bot_status'", fetchone=True)
    current = res[0] if res else 'ON'
    new_status = 'OFF' if current == 'ON' else 'ON'
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('bot_status', ?)", (new_status,))
    await call.message.edit_reply_markup(reply_markup=admin_kb())

@dp.callback_query(F.data == "spin_add")
async def spin_add_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.update_data(spin_action="add")
    await call.message.edit_text(
        "🎰 <b>Inject New Reward Logic</b>\n\nEnter reward amount (e.g. <code>15.50</code> or <code>0</code> for zero reward):",
        reply_markup=admin_back_kb(), parse_mode='HTML'
    )
    await state.set_state(AdminStates.spin_add_reward)

@dp.message(AdminStates.spin_add_reward)
async def spin_add_exec(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    data = await state.get_data()
    spin_action = data.get("spin_action", "add")
    raw = m.text.strip()
    if spin_action == "delete":
        try:
            rid = int(raw)
            row = db_query("SELECT id, amount FROM spin_rewards WHERE id=?", (rid,), fetchone=True)
            if not row:
                return await m.answer(f"❌ No reward found with ID {rid}. Please check the list and try again.")
            db_query("DELETE FROM spin_rewards WHERE id=?", (rid,))
            await m.answer(f"✅ Reward [ID: {rid}] → {fmt_curr(row[1])} has been removed from the prize pool.", reply_markup=admin_kb(), parse_mode='HTML')
            await state.clear()
        except ValueError:
            await m.answer("❌ Please send a valid reward <b>ID number</b> (e.g. <code>2</code>).", parse_mode='HTML')
    else:
        try:
            amt = float(raw)
            db_query("INSERT INTO spin_rewards (amount) VALUES (?)", (amt,))
            await m.answer(f"✅ New reward {fmt_curr(amt)} added to the prize pool!", reply_markup=admin_kb(), parse_mode='HTML')
            await state.clear()
        except ValueError:
            await m.answer("❌ Invalid amount. Please send a number (e.g. <code>15.50</code>).", parse_mode='HTML')

@dp.callback_query(F.data == "spin_view")
async def spin_view(call: CallbackQuery):
    rewards = db_query("SELECT id, amount FROM spin_rewards ORDER BY amount ASC", fetchall=True)
    text = "🎰 <b>Live Ludo Reward Constants</b>\n\n"
    for r in rewards:
        text += f"🎁 [ID: {r[0]}] → {fmt_curr(r[1])}\n"
    text += "\n<i>Use '❌ Drop Reward Logic' to delete a reward by ID.</i>"
    await call.message.edit_text(text, reply_markup=admin_back_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "spin_del")
async def spin_del_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    rewards = db_query("SELECT id, amount FROM spin_rewards ORDER BY amount ASC", fetchall=True)
    if not rewards:
        return await call.answer("⚠️ No rewards configured yet.", show_alert=True)
    text = "🗑 <b>Drop Reward Logic</b>\n\n"
    for r in rewards:
        text += f"🎁 [ID: {r[0]}] → {fmt_curr(r[1])}\n"
    text += "\n👉 Reply with the <b>ID number</b> of the reward to delete (e.g. <code>2</code>):"
    await call.message.edit_text(text, reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.update_data(spin_action="delete")
    await state.set_state(AdminStates.spin_add_reward)

@dp.callback_query(F.data == "spin_limit")
async def spin_limit_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    pool_check = db_query("SELECT value FROM settings WHERE key='daily_spin_pool'", fetchone=True)
    current_pool = pool_check[0] if pool_check else "5.0"
    await call.message.edit_text(
        f"⚙️ <b>Set Daily Global Spin Pool</b>\n\n"
        f"Current Pool: <b>₹{current_pool}</b>\n\n"
        "This is the maximum combined payout for ALL users in one calendar day.\n"
        "Default is ₹5 total/day.\n\n"
        "👉 Send new daily pool amount (e.g. <code>5</code> or <code>10</code>):",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.spin_set_limit)

@dp.message(AdminStates.spin_set_limit)
async def spin_limit_exec(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    try:
        val = float(m.text.strip())
        if val < 0:
            return await m.answer("❌ Limit must be a positive number.")
        db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('daily_spin_pool', ?)", (str(val),))
        await m.answer(f"✅ Global daily spin pool updated to <b>{fmt_curr(val)}</b>", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError:
        await m.answer("❌ Invalid number. Please send e.g. <code>25.0</code> or <code>50</code>.")

@dp.callback_query(F.data == "admin_set_video")
async def admin_set_video_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("📹 Input direct streaming / YouTube Link for Tutorial system:\n<i>(Or type 'None' to clear registry):</i>", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_howto_video)

@dp.message(AdminStates.wait_for_howto_video)
async def exec_set_video(m: Message, state: FSMContext):
    link = m.text.strip()
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('how_to_video', ?)", (link,))
    await m.answer("✅ Routing complete. Video linked.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_payment_proof")
async def admin_set_payment_proof_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    current = get_setting("payment_proof_channel", "")
    await call.message.edit_text(
        "🧾 <b>Payment Proof Channel</b>\n\n"
        f"Current: <code>{current or 'Not configured'}</code>\n\n"
        "Send the <b>public channel username</b> (example: <code>@yourchannel</code>) "
        "or its public <code>https://t.me/yourchannel</code> link.\n\n"
        "⚠️ Add this bot as an admin in that channel with permission to post messages.\n"
        "🔐 Purchase keys will NEVER be posted there.",
        reply_markup=admin_back_kb(), parse_mode="HTML"
    )
    await state.set_state(AdminStates.wait_for_payment_proof_channel)

@dp.message(AdminStates.wait_for_payment_proof_channel)
async def save_payment_proof_channel(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value = (m.text or "").strip()
    if value.lower() in ("none", "off", "disable", "disabled"):
        set_setting("payment_proof_channel", "")
        await state.clear()
        return await m.answer("✅ Payment Proof channel disabled.", reply_markup=admin_kb(), parse_mode="HTML")

    if value.startswith(("https://t.me/+", "http://t.me/+", "t.me/+")):
        return await m.answer("❌ Private invite link नहीं चलेगा. Public channel username जैसे <code>@yourchannel</code> भेजें.", parse_mode="HTML")
    if not (value.startswith("@") or "t.me/" in value):
        return await m.answer("❌ Public channel username भेजें, जैसे <code>@yourchannel</code>.", parse_mode="HTML")

    set_setting("payment_proof_channel", value)
    await state.clear()
    await m.answer(
        "✅ <b>Payment Proof Channel saved.</b>\n\n"
        "Successful purchases will now be posted there automatically.\n"
        "🔐 Customer keys will remain hidden.",
        reply_markup=admin_kb(), parse_mode="HTML"
    )

@dp.callback_query(F.data == "admin_set_all_files")
async def admin_set_all_files_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("🔗 Input the direct Channel / Cloud URL for 'Download Files' button:\n<i>(Or type 'None' to format data):</i>", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_all_files_link)

@dp.message(AdminStates.wait_for_all_files_link)
async def exec_set_all_files(m: Message, state: FSMContext):
    link = m.text.strip()
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('all_files_link', ?)", (link,))
    await m.answer("✅ Global resource variable updated.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_edit_emojis")
async def admin_edit_emojis(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    rows = db_query("SELECT key, value FROM settings WHERE key LIKE 'emoji_%' ORDER BY key", fetchall=True)
    kb = make_inline_kb(inline_keyboard=[])
    for row in rows:
        key = row[0]
        slot = key.replace("emoji_", "")
        current_id = row[1] if row[1] else "Not set"
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{slot} (ID: {current_id})", callback_data=f"edit_emoji_{slot}")])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text("🎨 <b>Edit All Emojis</b>\nChoose an emoji slot to change its ID:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("edit_emoji_"))
async def admin_edit_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    slot = call.data.split("edit_emoji_", 1)[1]
    await state.update_data(emoji_slot=slot)
    current = get_setting(f"emoji_{slot}", "Not set")
    await call.message.edit_text(f"✏️ Enter new emoji ID for <b>{slot}</b>:\nCurrent: {current}\n(Leave empty to reset to default)", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_emoji_slot)

@dp.message(AdminStates.wait_for_emoji_slot)
async def save_emoji_slot(m: Message, state: FSMContext):
    data = await state.get_data()
    slot = data['emoji_slot']
    new_id = m.text.strip()
    if new_id == "":
        db_query("DELETE FROM settings WHERE key=?", (f"emoji_{slot}",))
        await m.answer(f"✅ Reset emoji for '{slot}' to default.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        if not new_id.isdigit():
            await m.answer("❌ Invalid ID! Must be numeric.", reply_markup=admin_kb(), parse_mode='HTML')
            return
        set_setting(f"emoji_{slot}", new_id)
        await m.answer(f"✅ Emoji for '{slot}' updated to ID {new_id}.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_edit_ui_menu")
async def admin_edit_ui_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Edit Start Menu Text", callback_data="edit_ui_start", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Edit Download Files Text", callback_data="edit_ui_download", icon_custom_emoji_id=get_emoji_icon("download"))],
        [InlineKeyboardButton(text="Edit VIP Menu Text", callback_data="edit_ui_vip", icon_custom_emoji_id=get_emoji_icon("vip"))],
        [InlineKeyboardButton(text="Edit Lucky Dice Text", callback_data="edit_ui_dice", icon_custom_emoji_id=get_emoji_icon("ludo_spin"))],
        [InlineKeyboardButton(text="Edit Add Balance Text", callback_data="edit_ui_add_balance", icon_custom_emoji_id=get_emoji_icon("add_balance"))],
        [InlineKeyboardButton(text="Edit Referral Description", callback_data="edit_ui_referral", icon_custom_emoji_id=get_emoji_icon("referral"))],
        [InlineKeyboardButton(text="Edit How To Use Description", callback_data="edit_ui_how_to", icon_custom_emoji_id=get_emoji_icon("tutorial"))],
        [InlineKeyboardButton(text="Edit Reseller Description", callback_data="edit_ui_reseller", icon_custom_emoji_id=get_emoji_icon("reseller"))],
        [InlineKeyboardButton(text="Edit Profile Description", callback_data="edit_ui_profile", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Edit All History Description", callback_data="edit_ui_history", icon_custom_emoji_id=get_emoji_icon("history"))],
        [InlineKeyboardButton(text="Edit Old Orders History", callback_data="edit_ui_orders", icon_custom_emoji_id=get_emoji_icon("history"))],
        [InlineKeyboardButton(text="Edit Support Description", callback_data="edit_ui_support", icon_custom_emoji_id=get_emoji_icon("support"))],
        [InlineKeyboardButton(text="Edit Feedback Description", callback_data="edit_ui_feedback", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text("✏️ <b>Edit User Interface Texts</b>\nSelect which text you want to modify:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("edit_ui_"))
async def admin_edit_ui_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    ui_key = call.data.split("_")[2]
    await state.update_data(ui_key=ui_key)
    current_text = get_ui_text(ui_key)
    await call.message.edit_text(f"📝 Send the new text for <b>{ui_key.upper()}</b> menu.\n\nCurrent text:\n{current_text}", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.edit_ui_text)

@dp.message(AdminStates.edit_ui_text)
async def admin_save_ui_text(m: Message, state: FSMContext):
    data = await state.get_data()
    ui_key = data['ui_key']
    new_text = m.text
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (f"ui_{ui_key}", new_text))
    await m.answer(f"✅ UI text <b>{ui_key}</b> updated successfully!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_edit_reseller_price")
async def admin_edit_reseller_price_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    prods = db_query("SELECT id, name, category, panel_name, reseller_price FROM products", fetchall=True)
    prods = sorted(prods or [], key=lambda row: (natural_sort_key(row[2]), natural_sort_key(row[3]), product_name_sort_key(row[1])))
    if not prods: return await call.message.edit_text("No products to edit.", reply_markup=admin_back_kb(), parse_mode='HTML')
    kb = make_inline_kb(inline_keyboard=[])
    for p in prods:
        panel_name = p[3] if p[3] is not None else ""
        r_price = float(p[4]) if p[4] is not None else 0.0
        kb.inline_keyboard.append([InlineKeyboardButton(text=f"{p[2]} - {panel_name} - {p[1]} (₹{r_price:.2f})", callback_data=f"edit_reseller_{p[0]}", icon_custom_emoji_id=get_emoji_icon("money_icon"))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text("👑 <b>Edit Reseller Price per Product</b>\nSelect a product to change its wholesale price:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("edit_reseller_"))
async def admin_edit_reseller_price_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    prod_id = int(call.data.split("_")[2])
    await state.update_data(edit_reseller_prod_id=prod_id)
    await call.message.edit_text("💰 Enter the new <b>Reseller Price</b> in Rupees (₹) for this product:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.edit_reseller_price)

@dp.message(AdminStates.edit_reseller_price)
async def admin_save_reseller_price(m: Message, state: FSMContext):
    try:
        new_price = float(m.text)
        data = await state.get_data()
        prod_id = data['edit_reseller_prod_id']
        db_query("UPDATE products SET reseller_price=? WHERE id=?", (new_price, prod_id))
        await m.answer(f"✅ Reseller price updated to {fmt_curr(new_price)} for product ID {prod_id}.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Invalid number. Please enter a valid price.")

@dp.callback_query(F.data == "admin_set_reseller_fee")
async def admin_set_reseller_fee(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("💰 Enter the new <b>Reseller Setup Fee</b> in Rupees (₹):\nCurrent: " + get_setting("reseller_setup_fee", "200.0"), reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_setup_fee)

@dp.message(AdminStates.wait_for_reseller_setup_fee)
async def admin_save_reseller_fee(m: Message, state: FSMContext):
    try:
        fee = float(m.text)
        set_setting("reseller_setup_fee", str(fee))
        await m.answer(f"✅ Reseller setup fee updated to {fmt_curr(fee)}.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Invalid number. Please enter a valid amount.")

@dp.callback_query(F.data == "admin_set_reseller_min")
async def admin_set_reseller_min(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("💳 Enter the new <b>Minimum Balance</b> required to become reseller (₹):\nCurrent: " + get_setting("reseller_min_balance", "500.0"), reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_reseller_min_balance)

@dp.message(AdminStates.wait_for_reseller_min_balance)
async def admin_save_reseller_min(m: Message, state: FSMContext):
    try:
        min_bal = float(m.text)
        set_setting("reseller_min_balance", str(min_bal))
        await m.answer(f"✅ Minimum reseller balance updated to {fmt_curr(min_bal)}.", reply_markup=admin_kb(), parse_mode='HTML')
        await state.clear()
    except ValueError: await m.answer("❌ Invalid number. Please enter a valid amount.")

@dp.callback_query(F.data == "admin_set_support_links")
async def admin_set_support_links(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Set Telegram Link", callback_data="admin_set_telegram", icon_custom_emoji_id=get_emoji_icon("telegram"))],
        [InlineKeyboardButton(text="Set WhatsApp Link", callback_data="admin_set_whatsapp", icon_custom_emoji_id=get_emoji_icon("whatsapp"))],
        [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text("📌 <b>Support Contact Links</b>\nSet the URLs for Telegram and WhatsApp support:", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_set_telegram")
async def admin_set_telegram(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("✈️ Enter the Telegram contact URL (e.g., https://t.me/YOUR_SUPPORT):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_support_telegram)

@dp.message(AdminStates.wait_for_support_telegram)
async def save_telegram_link(m: Message, state: FSMContext):
    link = m.text.strip()
    set_setting("support_telegram", link)
    await m.answer("✅ Telegram support link updated!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_whatsapp")
async def admin_set_whatsapp(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("📱 Enter the WhatsApp contact URL (e.g., https://wa.me/1234567890):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_support_whatsapp)

@dp.message(AdminStates.wait_for_support_whatsapp)
async def save_whatsapp_link(m: Message, state: FSMContext):
    link = m.text.strip()
    set_setting("support_whatsapp", link)
    await m.answer("✅ WhatsApp support link updated!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_category_emojis")
async def admin_set_category_emojis(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[])
    for cat in get_all_categories():
        custom_id = get_setting(f"cat_custom_id_{cat}", "").strip()
        stored = get_setting(f"cat_emoji_{cat}", "").strip()
        if custom_id and custom_id.isdigit():
            btn_text = f"{cat} (Custom Emoji)"
            btn_icon = custom_id
        elif stored and stored.isdigit():
            btn_text = f"{cat} (Custom Emoji)"
            btn_icon = stored
        elif stored:
            btn_text = f"{stored} {cat}"
            btn_icon = None
        else:
            ico = get_category_display_icon(cat)
            btn_text = f"{ico} {cat} (Default)"
            btn_icon = None
        kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"set_cat_emoji_{cat}", icon_custom_emoji_id=as_emoji_icon_id(btn_icon))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text("🎨 <b>Set Category Emojis</b>\n\nChoose a category to set its emoji (send any emoji like 🔥, ⚡, 🍎, 💻 or custom emoji):", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("set_cat_emoji_"))
async def admin_set_category_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    category = call.data.split("set_cat_emoji_", 1)[1]
    await state.update_data(cat_emoji_category=category)
    current = get_setting(f"cat_emoji_{category}", "Default")
    await call.message.edit_text(
        f"🎨 <b>Set Emoji for Category:</b> <code>{category}</code>\n"
        f"<b>Current:</b> {current}\n\n"
        "👉 Send an emoji (e.g. ⚡, 🛡️, 🍎, 💻, 🎯, 🔥) or Telegram custom emoji.\n"
        "<i>(Send 'reset' or leave empty to restore default)</i>",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.wait_for_category_emoji)

@dp.message(AdminStates.wait_for_category_emoji)
async def save_category_emoji(m: Message, state: FSMContext):
    data = await state.get_data()
    category = data['cat_emoji_category']
    raw = (m.text or "").strip()
    if raw.lower() in ("", "reset", "default"):
        db_query("DELETE FROM settings WHERE key=?", (f"cat_emoji_{category}",))
        db_query("DELETE FROM settings WHERE key=?", (f"cat_custom_id_{category}",))
        await m.answer(f"✅ Reset emoji for {category} to default.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        emoji_char, custom_id = extract_emoji_or_id(m)
        if custom_id:
            set_setting(f"cat_custom_id_{category}", custom_id)
            set_setting(f"cat_emoji_{category}", custom_id)
            disp = f'<tg-emoji emoji-id="{custom_id}">⭐</tg-emoji>'
            await m.answer(f"✅ Premium Custom Emoji set for <b>{category}</b>: {disp}", reply_markup=admin_kb(), parse_mode='HTML')
        else:
            to_store = emoji_char or raw
            db_query("DELETE FROM settings WHERE key=?", (f"cat_custom_id_{category}",))
            set_setting(f"cat_emoji_{category}", to_store)
            await m.answer(f"✅ Emoji set for <b>{category}</b>: {to_store}", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_panel_emojis")
async def admin_set_panel_emojis(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    panels = db_query("SELECT DISTINCT panel_name FROM products WHERE panel_name != '' ORDER BY panel_name", fetchall=True)
    if not panels:
        await call.message.edit_text("No panel names found in products.", reply_markup=admin_back_kb(), parse_mode='HTML')
        return
    kb = make_inline_kb(inline_keyboard=[])
    for p in panels:
        panel = p[0]
        custom_id = get_setting(f"panel_custom_id_{panel}", "").strip()
        stored = get_setting(f"panel_emoji_{panel}", "").strip()
        if custom_id and custom_id.isdigit():
            btn_text = f"{panel} (Custom Emoji)"
            btn_icon = custom_id
        elif stored and stored.isdigit():
            btn_text = f"{panel} (Custom Emoji)"
            btn_icon = stored
        elif stored:
            btn_text = f"{stored} {panel}"
            btn_icon = None
        else:
            pnl_ico = get_panel_display_icon(panel)
            btn_text = f"{pnl_ico} {panel} (Default)"
            btn_icon = None
        kb.inline_keyboard.append([InlineKeyboardButton(text=btn_text, callback_data=f"set_panel_emoji_{panel}", icon_custom_emoji_id=as_emoji_icon_id(btn_icon))])
    kb.inline_keyboard.append([InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))])
    await call.message.edit_text("🖼 <b>Set Panel Emojis</b>\n\nChoose a panel name to set its emoji (send any emoji like 🔥, ⚡, 🛡️, 💎, 👑 or custom emoji):", reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("set_panel_emoji_"))
async def admin_set_panel_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    panel_name = call.data.split("set_panel_emoji_", 1)[1]
    await state.update_data(panel_emoji_name=panel_name)
    current = get_setting(f"panel_emoji_{panel_name}", "Default")
    await call.message.edit_text(
        f"🎨 <b>Set Emoji for Panel:</b> <code>{panel_name}</code>\n"
        f"<b>Current:</b> {current}\n\n"
        "👉 Send an emoji (e.g. 🔥, ⚡, 👑, 🛡️, 💎) or Telegram custom emoji.\n"
        "<i>(Send 'reset' or leave empty to reset to default)</i>",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.wait_for_panel_emoji_id)

@dp.message(AdminStates.wait_for_panel_emoji_id)
async def save_panel_emoji(m: Message, state: FSMContext):
    data = await state.get_data()
    panel_name = data['panel_emoji_name']
    raw = (m.text or "").strip()
    if raw.lower() in ("", "reset", "default"):
        db_query("DELETE FROM settings WHERE key=?", (f"panel_emoji_{panel_name}",))
        db_query("DELETE FROM settings WHERE key=?", (f"panel_custom_id_{panel_name}",))
        await m.answer(f"✅ Reset emoji for panel '{panel_name}'.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        emoji_char, custom_id = extract_emoji_or_id(m)
        if custom_id:
            set_setting(f"panel_custom_id_{panel_name}", custom_id)
            set_setting(f"panel_emoji_{panel_name}", custom_id)
            disp = f'<tg-emoji emoji-id="{custom_id}">⭐</tg-emoji>'
            await m.answer(f"✅ Premium Custom Emoji set for panel '<b>{panel_name}</b>': {disp}", reply_markup=admin_kb(), parse_mode='HTML')
        else:
            to_store = emoji_char or raw
            db_query("DELETE FROM settings WHERE key=?", (f"panel_custom_id_{panel_name}",))
            set_setting(f"panel_emoji_{panel_name}", to_store)
            await m.answer(f"✅ Emoji for panel '<b>{panel_name}</b>' set to: {to_store}", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# DURATION EMOJI MANAGEMENT (ADMIN)
# ==============================================================================
DURATION_PRESETS = [
    ("1 Hour", "1 hour"), ("2 Hours", "2 hour"), ("3 Hours", "3 hour"),
    ("4 Hours", "4 hour"), ("6 Hours", "6 hour"), ("8 Hours", "8 hour"),
    ("12 Hours", "12 hour"), ("24 Hours", "24 hour"),
    ("1 Day", "1 day"), ("2 Days", "2 day"), ("3 Days", "3 day"),
    ("4 Days", "4 day"), ("5 Days", "5 day"), ("7 Days", "7 day"),
    ("10 Days", "10 day"), ("14 Days", "14 day"), ("15 Days", "15 day"),
    ("20 Days", "20 day"), ("21 Days", "21 day"), ("28 Days", "28 day"),
    ("30 Days", "30 day"), ("45 Days", "45 day"), ("60 Days", "60 day"),
    ("90 Days", "90 day"),
]

@dp.callback_query(F.data == "admin_set_duration_emojis")
async def admin_set_duration_emojis_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    kb = make_inline_kb(inline_keyboard=[])
    for label, key in DURATION_PRESETS:
        dur_custom_id = get_setting(f"dur_custom_id_{key}", "").strip()
        dur_stored = get_setting(f"dur_emoji_{key}", "").strip()
        if dur_custom_id and dur_custom_id.isdigit():
            btn_text = f"{label} (Custom Emoji)"
            btn_icon = dur_custom_id
        elif dur_stored and dur_stored.isdigit():
            btn_text = f"{label} (Custom Emoji)"
            btn_icon = dur_stored
        elif dur_stored:
            btn_text = f"{dur_stored} {label}"
            btn_icon = None
        else:
            cur_emoji = get_duration_emoji(key)
            if cur_emoji and cur_emoji.isdigit():
                btn_text = f"{label} (Custom Emoji)"
                btn_icon = cur_emoji
            else:
                btn_text = f"{cur_emoji} {label}"
                btn_icon = None
        kb.inline_keyboard.append([
            InlineKeyboardButton(text=btn_text, callback_data=f"set_dur_emoji_{key}", icon_custom_emoji_id=as_emoji_icon_id(btn_icon))
        ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))
    ])
    await call.message.edit_text(
        "⏱ <b>Set Duration Emojis</b>\n\n"
        "Choose a package/duration below to customize the emoji that appears on buttons and product descriptions in your shop:",
        reply_markup=kb,
        parse_mode='HTML'
    )

@dp.callback_query(F.data.startswith("set_dur_emoji_"))
async def admin_set_dur_emoji_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    dur_key = call.data.split("set_dur_emoji_", 1)[1]
    await state.update_data(dur_key=dur_key)
    cur = get_duration_emoji(dur_key)
    await call.message.edit_text(
        f"🎨 <b>Set Emoji for Duration:</b> <code>{dur_key.title()}</code>\n"
        f"<b>Current Emoji:</b> {cur}\n\n"
        "👉 Send an emoji (e.g. ⚡, 🔥, 💎, 👑, ⏱️, 🚀) or Telegram custom emoji.\n"
        "<i>(Send 'reset' or leave empty to restore default)</i>",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.wait_for_duration_emoji)

@dp.message(AdminStates.wait_for_duration_emoji)
async def save_duration_emoji(m: Message, state: FSMContext):
    data = await state.get_data()
    dur_key = data['dur_key'].lower().strip()
    raw = (m.text or "").strip()
    if raw.lower() in ("", "reset", "default"):
        db_query("DELETE FROM settings WHERE key=?", (f"dur_emoji_{dur_key}",))
        db_query("DELETE FROM settings WHERE key=?", (f"dur_custom_id_{dur_key}",))
        await m.answer(f"✅ Reset emoji for {dur_key.title()} to default.", reply_markup=admin_kb(), parse_mode='HTML')
    else:
        emoji_char, custom_id = extract_emoji_or_id(m)
        if custom_id:
            set_setting(f"dur_custom_id_{dur_key}", custom_id)
            set_setting(f"dur_emoji_{dur_key}", custom_id)
            disp = f'<tg-emoji emoji-id="{custom_id}">⚡</tg-emoji>'
            await m.answer(f"✅ Premium Custom Emoji for duration '<b>{dur_key.title()}</b>' set to: {disp}", reply_markup=admin_kb(), parse_mode='HTML')
        else:
            to_store = emoji_char or raw
            db_query("DELETE FROM settings WHERE key=?", (f"dur_custom_id_{dur_key}",))
            set_setting(f"dur_emoji_{dur_key}", to_store)
            await m.answer(f"✅ Duration emoji for <b>{dur_key.title()}</b> set to: {to_store}", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()


# ==============================================================================
# CATEGORY MANAGEMENT (ADMIN)
# ==============================================================================
@dp.callback_query(F.data == "admin_manage_categories")
async def admin_manage_categories(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cats = db_query("SELECT id, name, emoji_id, sort_order FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True)
    kb = make_inline_kb(inline_keyboard=[])
    text = (
        "🗂 <b><u>CATEGORY MANAGEMENT</u></b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "Click any category to <b>Rename</b>, <b>Change Position</b>, <b>Set Emoji</b>, or <b>Delete</b>.\n\n"
    )
    if not cats:
        text += "<i>No categories found. Click 'Add Category' below.</i>"
    else:
        for c in cats:
            cid, cname, cemj, corder = c
            prod_cnt = db_query("SELECT COUNT(*) FROM products WHERE category LIKE ?", (cname + '%',), fetchone=True)[0]
            emj_icon = get_category_emoji(cname)
            kb.inline_keyboard.append([
                InlineKeyboardButton(
                    text=f"[#{corder}] {cname} ({prod_cnt} prods)", 
                    callback_data=f"adm_cat_v_{cid}", 
                    icon_custom_emoji_id=as_emoji_icon_id(emj_icon) or get_emoji_icon("info_icon")
                )
            ])
    
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Add New Category", callback_data="admin_add_cat_start", icon_custom_emoji_id=get_emoji_icon("product_store"))
    ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_add_cat_start")
async def admin_add_cat_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text(
        "➕ <b>Add New Category</b>\n\nEnter the name for the new category (e.g. <code>EMULATOR PANEL</code> or <code>BGMI PANEL</code>):",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.add_category_name)

@dp.message(AdminStates.add_category_name)
async def admin_save_new_cat(m: Message, state: FSMContext):
    new_name = m.text.strip().upper()
    if not new_name:
        return await m.answer("❌ Category name cannot be empty.", reply_markup=admin_kb())
    existing = db_query("SELECT id FROM categories WHERE UPPER(name)=?", (new_name,), fetchone=True)
    if existing:
        return await m.answer(f"❌ Category <b>{new_name}</b> already exists!", reply_markup=admin_kb(), parse_mode='HTML')
    max_order = db_query("SELECT COALESCE(MAX(sort_order), 0) FROM categories", fetchone=True)[0]
    db_query("INSERT INTO categories (name, sort_order) VALUES (?, ?)", (new_name, max_order + 1))
    await m.answer(f"✅ <b>Category Added!</b>\n\nCategory <b>{new_name}</b> is now active at position #{max_order + 1}.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("adm_cat_v_"))
async def admin_view_cat(call: CallbackQuery, cid: Optional[int] = None):
    if not is_admin(call.from_user.id): return
    if cid is None:
        cid = int(call.data.split("adm_cat_v_")[1])
    cat = db_query("SELECT id, name, emoji_id, sort_order FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat: return await call.answer("Category not found.", show_alert=True)
    cid, cname, cemj, corder = cat
    prod_cnt = db_query("SELECT COUNT(*) FROM products WHERE category LIKE ?", (cname + '%',), fetchone=True)[0]
    
    text = (
        f"🏷️ <b><u>CATEGORY DETAILS</u></b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<b>Name:</b> <code>{cname}</code>\n"
        f"<b>Position / Sort Order:</b> #{corder}\n"
        f"<b>Emoji ID:</b> <code>{cemj or 'Default'}</code>\n"
        f"<b>Associated Products:</b> {prod_cnt} items\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<i>Select an action below to modify this category:</i>"
    )
    kb = make_inline_kb(inline_keyboard=[
        [
            InlineKeyboardButton(text="Rename Category", callback_data=f"adm_cat_ren_{cid}", icon_custom_emoji_id=get_emoji_icon("info_icon")),
            InlineKeyboardButton(text="Set Position #", callback_data=f"adm_cat_pos_{cid}", icon_custom_emoji_id=get_emoji_icon("grid_id"))
        ],
        [
            InlineKeyboardButton(text="⬆️ Move Up", callback_data=f"adm_cat_up_{cid}"),
            InlineKeyboardButton(text="⬇️ Move Down", callback_data=f"adm_cat_dn_{cid}")
        ],
        [
            InlineKeyboardButton(text="Set Emoji ID", callback_data=f"adm_cat_emj_{cid}", icon_custom_emoji_id=get_emoji_icon("info_icon")),
            InlineKeyboardButton(text="Delete Category", callback_data=f"adm_cat_del_{cid}", icon_custom_emoji_id=get_emoji_icon("back"))
        ],
        [
            InlineKeyboardButton(text="Back to Categories", callback_data="admin_manage_categories", icon_custom_emoji_id=get_emoji_icon("back"))
        ]
    ])
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
    except Exception:
        pass

@dp.callback_query(F.data.startswith("adm_cat_ren_"))
async def admin_rename_cat_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_ren_")[1])
    cat = db_query("SELECT name FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat: return await call.answer("Category not found.", show_alert=True)
    await state.update_data(rename_cat_id=cid, old_cat_name=cat[0])
    await call.message.edit_text(
        f"✏️ <b>Rename Category</b>\n\nCurrent Name: <b>{cat[0]}</b>\n\nEnter the new name for this category:\n<i>(All products under this category will automatically update!)</i>",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.edit_category_name)

@dp.message(AdminStates.edit_category_name)
async def admin_save_rename_cat(m: Message, state: FSMContext):
    data = await state.get_data()
    cid = data['rename_cat_id']
    old_name = data['old_cat_name']
    new_name = m.text.strip().upper()
    if not new_name:
        return await m.answer("❌ Name cannot be empty.", reply_markup=admin_kb())
    
    db_query("UPDATE categories SET name=? WHERE id=?", (new_name, cid))
    db_query("UPDATE products SET category=? WHERE category=?", (new_name, old_name))
    await m.answer(
        f"✅ <b>Category Renamed!</b>\n\nOld Name: <b>{old_name}</b>\nNew Name: <b>{new_name}</b>\nAll associated products have been updated.",
        reply_markup=admin_kb(),
        parse_mode='HTML'
    )
    await state.clear()

@dp.callback_query(F.data.startswith("adm_cat_pos_"))
async def admin_cat_pos_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_pos_")[1])
    cat = db_query("SELECT name, sort_order FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat: return await call.answer("Category not found.", show_alert=True)
    await state.update_data(pos_cat_id=cid)
    await call.message.edit_text(
        f"🔢 <b>Set Position for {cat[0]}</b>\n\nCurrent Position: #{cat[1]}\n\nEnter new position number (e.g. <code>1</code> for top, <code>2</code>, <code>3</code>...):",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.edit_category_pos)

@dp.message(AdminStates.edit_category_pos)
async def admin_save_cat_pos(m: Message, state: FSMContext):
    data = await state.get_data()
    cid = data['pos_cat_id']
    try:
        new_pos = int(m.text.strip())
    except ValueError:
        return await m.answer("❌ Please enter a valid number (e.g. 1, 2, 3).")
    cats = db_query("SELECT id FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True)
    cat_ids = [c[0] for c in cats if c[0] != cid]
    target_pos = max(1, min(new_pos, len(cat_ids) + 1))
    cat_ids.insert(target_pos - 1, cid)
    for pos, c_id in enumerate(cat_ids, start=1):
        db_query("UPDATE categories SET sort_order=? WHERE id=?", (pos, c_id))
    cat = db_query("SELECT name FROM categories WHERE id=?", (cid,), fetchone=True)
    cname = cat[0] if cat else "Category"
    await m.answer(f"✅ Position for <b>{cname}</b> set to #{target_pos} successfully!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("adm_cat_up_"))
async def admin_cat_up(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_up_")[1])
    cats = db_query("SELECT id FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True)
    cat_ids = [c[0] for c in cats]
    if cid not in cat_ids:
        return await call.answer("Category not found", show_alert=True)
    idx = cat_ids.index(cid)
    if idx == 0:
        await call.answer("Already at top!", show_alert=False)
        return await admin_view_cat(call, cid=cid)
    cat_ids[idx], cat_ids[idx - 1] = cat_ids[idx - 1], cat_ids[idx]
    for pos, c_id in enumerate(cat_ids, start=1):
        db_query("UPDATE categories SET sort_order=? WHERE id=?", (pos, c_id))
    await call.answer("⬆️ Moved Up!")
    await admin_view_cat(call, cid=cid)

@dp.callback_query(F.data.startswith("adm_cat_dn_"))
async def admin_cat_dn(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_dn_")[1])
    cats = db_query("SELECT id FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True)
    cat_ids = [c[0] for c in cats]
    if cid not in cat_ids:
        return await call.answer("Category not found", show_alert=True)
    idx = cat_ids.index(cid)
    if idx >= len(cat_ids) - 1:
        await call.answer("Already at bottom!", show_alert=False)
        return await admin_view_cat(call, cid=cid)
    cat_ids[idx], cat_ids[idx + 1] = cat_ids[idx + 1], cat_ids[idx]
    for pos, c_id in enumerate(cat_ids, start=1):
        db_query("UPDATE categories SET sort_order=? WHERE id=?", (pos, c_id))
    await call.answer("⬇️ Moved Down!")
    await admin_view_cat(call, cid=cid)

@dp.callback_query(F.data.startswith("adm_cat_emj_"))
async def admin_cat_emoji_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_emj_")[1])
    cat = db_query("SELECT name, emoji_id FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat: return await call.answer("Category not found.", show_alert=True)
    await state.update_data(emj_cat_id=cid, cat_name=cat[0])
    await call.message.edit_text(
        f"🎨 <b>Set Emoji for {cat[0]}</b>\nCurrent Emoji ID: <code>{cat[1] or 'None'}</code>\n\nEnter numeric Telegram custom emoji ID (or send <code>none</code> to reset):",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.edit_category_emoji)

@dp.message(AdminStates.edit_category_emoji)
async def admin_save_cat_emoji(m: Message, state: FSMContext):
    data = await state.get_data()
    cid = data['emj_cat_id']
    emoji_char, custom_id = extract_emoji_or_id(m)
    val = (m.text or "").strip()
    if val.lower() in ('none', 'default', '', 'reset'):
        val = ""
    elif custom_id:
        val = custom_id
    elif not val.isdigit():
        return await m.answer("❌ Please send a valid Telegram custom emoji or numeric ID (e.g. <code>6161172706856282588</code>).")
    db_query("UPDATE categories SET emoji_id=? WHERE id=?", (val, cid))
    await m.answer("✅ Category emoji updated successfully!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("adm_cat_del_"))
async def admin_cat_delete(call: CallbackQuery):
    """Immediately delete a category and everything belonging to it.

    Admin explicitly requested a one-click destructive category delete with no
    confirmation prompt. Purchase/transaction history is intentionally kept.
    """
    if not is_admin(call.from_user.id):
        return
    cid = int(call.data.split("adm_cat_del_", 1)[1])
    cat = db_query("SELECT name FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat:
        return await call.answer("Category not found.", show_alert=True)
    cname = cat[0]

    # Match the category logic used throughout the shop (supports legacy
    # category labels with a suffix). Remove keys first to avoid FK issues.
    prods = db_query("SELECT id FROM products WHERE category LIKE ?", (cname + '%',), fetchall=True) or []
    product_ids = [int(row[0]) for row in prods]
    for pid in product_ids:
        db_query("DELETE FROM product_keys WHERE product_id=?", (pid,))
    db_query("DELETE FROM products WHERE category LIKE ?", (cname + '%',))
    db_query("DELETE FROM categories WHERE id=?", (cid,))

    # Clean category-specific UI settings; this does not touch transaction history.
    try:
        db_query("DELETE FROM settings WHERE key LIKE ?", (f"cat_emoji_{cname}%",))
        db_query("DELETE FROM settings WHERE key LIKE ?", (f"cat_custom_id_{cname}%",))
    except Exception:
        pass

    await call.message.edit_text(
        f"☢️ <b>Category Deleted</b>\n\n"
        f"🏷 <b>{html.escape(str(cname))}</b>\n"
        f"📦 Products removed: <b>{len(product_ids)}</b>\n"
        f"🔑 Product keys removed with them.\n\n"
        f"🧾 Purchase/transaction history was kept safely.",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )


@dp.callback_query(F.data.startswith("adm_cat_delcf_keep_"))
async def admin_cat_delete_confirm_keep(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_delcf_keep_")[1])
    cat = db_query("SELECT name FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat: return await call.answer("Category not found.", show_alert=True)
    cname = cat[0]
    prod_cnt = db_query("SELECT COUNT(*) FROM products WHERE category LIKE ?", (cname + '%',), fetchone=True)[0]
    db_query("DELETE FROM categories WHERE id=?", (cid,))
    msg = f"✅ Category <b>{cname}</b> deleted."
    if prod_cnt > 0:
        msg += f"\n<i>Note: {prod_cnt} existing products still keep their category label unless re-assigned.</i>"
    await call.message.edit_text(msg, reply_markup=admin_back_kb(), parse_mode='HTML')

@dp.callback_query(F.data.startswith("adm_cat_delcf_all_"))
async def admin_cat_delete_confirm_all(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("adm_cat_delcf_all_")[1])
    cat = db_query("SELECT name FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat: return await call.answer("Category not found.", show_alert=True)
    cname = cat[0]
    prods = db_query("SELECT id FROM products WHERE category LIKE ?", (cname + '%',), fetchall=True)
    for p in (prods or []):
        db_query("DELETE FROM product_keys WHERE product_id=?", (p[0],))
    db_query("DELETE FROM products WHERE category LIKE ?", (cname + '%',))
    db_query("DELETE FROM categories WHERE id=?", (cid,))
    msg = f"☢️ Category <b>{cname}</b> and all its associated products/keys were permanently deleted."
    await call.message.edit_text(msg, reply_markup=admin_back_kb(), parse_mode='HTML')


# ==============================================================================
# PRODUCT MAIN TITLES & POSITIONS (ADMIN)
# ==============================================================================
@dp.callback_query(F.data == "admin_panel_positions_menu")
async def admin_panel_positions_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cats = db_query("SELECT id, name, emoji_id, sort_order FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True)
    kb = make_inline_kb(inline_keyboard=[])
    text = (
        "🎯 <b><u>PRODUCT MAIN TITLES & POSITIONS</u></b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "Select a Category to view its Main Titles (Panels) and customize their display order / position:\n"
    )
    for cid, cat, emj, corder in cats:
        emj_icon = get_category_emoji(cat)
        panel_count = db_query("SELECT COUNT(DISTINCT panel_name) FROM products WHERE category=? AND panel_name != ''", (cat,), fetchone=True)[0]
        kb.inline_keyboard.append([
            InlineKeyboardButton(
                text=f"{cat} ({panel_count} Main Titles)", 
                callback_data=f"pnlpos_c_{cid}", 
                icon_custom_emoji_id=as_emoji_icon_id(emj_icon) or get_emoji_icon("info_icon")
            )
        ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("pnlpos_c_"))
async def admin_pnlpos_list_panels(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    cid = int(call.data.split("pnlpos_c_")[1])
    cat_row = db_query("SELECT id, name FROM categories WHERE id=?", (cid,), fetchone=True)
    if not cat_row: return await call.answer("Category not found", show_alert=True)
    cat = cat_row[1]
    
    rows = db_query("""
        SELECT MIN(id) AS sample_id, panel_name, COALESCE(MIN(panel_sort_order), 0) AS p_order, COUNT(*) AS pkg_count
        FROM products
        WHERE category=? AND panel_name != ''
        GROUP BY panel_name
        ORDER BY p_order ASC, panel_name ASC
    """, (cat,), fetchall=True)
    
    kb = make_inline_kb(inline_keyboard=[])
    text = (
        f"🎯 <b><u>MAIN TITLES: {cat.upper()}</u></b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"Click any title below to <b>Change its Position (Display Order)</b> or <b>Rename the Title</b>:\n\n"
    )
    if not rows:
        text += "<i>No products / panels found in this category yet.</i>"
    else:
        for r in rows:
            sample_id, pname, porder, pkg_count = r
            emj = get_panel_emoji(pname)
            kb.inline_keyboard.append([
                InlineKeyboardButton(
                    text=f"[#{porder}] {pname} ({pkg_count} pkgs)", 
                    callback_data=f"adm_pnl_v_{sample_id}",
                    icon_custom_emoji_id=as_emoji_icon_id(emj) or get_emoji_icon("product_store")
                )
            ])
    
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Categories", callback_data="admin_panel_positions_menu", icon_custom_emoji_id=get_emoji_icon("back"))
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("adm_pnl_v_"))
async def admin_pnlpos_view_panel(call: CallbackQuery, sample_id: Optional[int] = None):
    if not is_admin(call.from_user.id): return
    if sample_id is None:
        sample_id = int(call.data.split("adm_pnl_v_")[1])
    prod = db_query("SELECT category, panel_name, COALESCE(panel_sort_order, 0) FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Panel not found.", show_alert=True)
    cat, pname, porder = prod
    pkg_count = db_query("SELECT COUNT(*) FROM products WHERE category=? AND panel_name=?", (cat, pname), fetchone=True)[0]
    cat_row = db_query("SELECT id FROM categories WHERE name=?", (cat,), fetchone=True)
    back_cb = f"pnlpos_c_{cat_row[0]}" if cat_row else "admin_panel_positions_menu"
    
    text = (
        f"📦 <b><u>MAIN TITLE DETAILS</u></b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<b>Main Title:</b> <b>{pname}</b>\n"
        f"<b>Category:</b> {cat}\n"
        f"<b>Current Position (Sort Order):</b> #{porder}\n"
        f"<b>Packages under this Title:</b> {pkg_count}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<i>Choose an action to reorganize this product title:</i>"
    )
    kb = make_inline_kb(inline_keyboard=[
        [
            InlineKeyboardButton(text="Set Position #", callback_data=f"adm_pnl_pos_{sample_id}", icon_custom_emoji_id=get_emoji_icon("grid_id")),
            InlineKeyboardButton(text="Rename Main Title", callback_data=f"adm_pnl_ren_{sample_id}", icon_custom_emoji_id=get_emoji_icon("info_icon"))
        ],
        [
            InlineKeyboardButton(text="⬆️ Move Up", callback_data=f"adm_pnl_up_{sample_id}"),
            InlineKeyboardButton(text="⬇️ Move Down", callback_data=f"adm_pnl_dn_{sample_id}")
        ],
        [
            InlineKeyboardButton(text="Organize Packages", callback_data=f"adm_pnl_pkgs_{sample_id}", icon_custom_emoji_id=get_emoji_icon("product_store")),
            InlineKeyboardButton(text="Delete Main Title", callback_data=f"adm_pnl_del_{sample_id}", icon_custom_emoji_id=get_emoji_icon("back"))
        ],
        [
            InlineKeyboardButton(text="Back", callback_data=back_cb, icon_custom_emoji_id=get_emoji_icon("back"))
        ]
    ])
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
    except Exception:
        pass

@dp.callback_query(F.data.startswith("adm_pnl_pos_"))
async def admin_pnlpos_set_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_pos_")[1])
    prod = db_query("SELECT category, panel_name, COALESCE(panel_sort_order, 0) FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Panel not found.", show_alert=True)
    cat, pname, porder = prod
    await state.update_data(pnl_sample_id=sample_id, pnl_cat=cat, pnl_name=pname)
    await call.message.edit_text(
        f"🔢 <b>Set Position for: {pname}</b>\n\n"
        f"Current Position: #{porder}\n\n"
        f"Enter the desired position number (e.g. <code>1</code> for 1st place, <code>2</code> for 2nd, etc.):",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.edit_panel_pos)

@dp.message(AdminStates.edit_panel_pos)
async def admin_pnlpos_save_pos(m: Message, state: FSMContext):
    data = await state.get_data()
    cat = data['pnl_cat']
    pname = data['pnl_name']
    try:
        new_pos = int(m.text.strip())
    except ValueError:
        return await m.answer("❌ Please enter a valid number (e.g. 1, 2, 3).")
    
    rows = db_query("""
        SELECT panel_name
        FROM products
        WHERE category=? AND panel_name != ''
        GROUP BY panel_name
        ORDER BY COALESCE(MIN(panel_sort_order), 0) ASC, panel_name ASC
    """, (cat,), fetchall=True)
    panel_list = [r[0] for r in rows if r[0] != pname]
    target_pos = max(1, min(new_pos, len(panel_list) + 1))
    panel_list.insert(target_pos - 1, pname)
    for pos, name in enumerate(panel_list, start=1):
        db_query("UPDATE products SET panel_sort_order=? WHERE category=? AND panel_name=?", (pos, cat, name))
    
    await m.answer(f"✅ <b>Position Updated!</b>\n\nMain Title <b>{pname}</b> is now set to position <b>#{target_pos}</b> in <b>{cat}</b>.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("adm_pnl_up_"))
async def admin_pnlpos_move_up(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_up_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Not found", show_alert=True)
    cat, pname = prod
    
    rows = db_query("""
        SELECT panel_name
        FROM products
        WHERE category=? AND panel_name != ''
        GROUP BY panel_name
        ORDER BY COALESCE(MIN(panel_sort_order), 0) ASC, panel_name ASC
    """, (cat,), fetchall=True)
    panel_list = [r[0] for r in rows]
    if pname not in panel_list:
        return await call.answer("Title not found", show_alert=True)
    
    idx = panel_list.index(pname)
    if idx == 0:
        await call.answer("Already at top!", show_alert=False)
        return await admin_pnlpos_view_panel(call, sample_id=sample_id)
    
    panel_list[idx], panel_list[idx - 1] = panel_list[idx - 1], panel_list[idx]
    for pos, name in enumerate(panel_list, start=1):
        db_query("UPDATE products SET panel_sort_order=? WHERE category=? AND panel_name=?", (pos, cat, name))
    
    await call.answer("⬆️ Moved Up!")
    await admin_pnlpos_view_panel(call, sample_id=sample_id)

@dp.callback_query(F.data.startswith("adm_pnl_dn_"))
async def admin_pnlpos_move_dn(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_dn_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Not found", show_alert=True)
    cat, pname = prod
    
    rows = db_query("""
        SELECT panel_name
        FROM products
        WHERE category=? AND panel_name != ''
        GROUP BY panel_name
        ORDER BY COALESCE(MIN(panel_sort_order), 0) ASC, panel_name ASC
    """, (cat,), fetchall=True)
    panel_list = [r[0] for r in rows]
    if pname not in panel_list:
        return await call.answer("Title not found", show_alert=True)
    
    idx = panel_list.index(pname)
    if idx >= len(panel_list) - 1:
        await call.answer("Already at bottom!", show_alert=False)
        return await admin_pnlpos_view_panel(call, sample_id=sample_id)
    
    panel_list[idx], panel_list[idx + 1] = panel_list[idx + 1], panel_list[idx]
    for pos, name in enumerate(panel_list, start=1):
        db_query("UPDATE products SET panel_sort_order=? WHERE category=? AND panel_name=?", (pos, cat, name))
    
    await call.answer("⬇️ Moved Down!")
    await admin_pnlpos_view_panel(call, sample_id=sample_id)

@dp.callback_query(F.data.startswith("adm_pnl_ren_"))
async def admin_pnlpos_rename_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_ren_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Not found", show_alert=True)
    cat, pname = prod
    await state.update_data(pnl_sample_id=sample_id, pnl_cat=cat, pnl_old_name=pname)
    await call.message.edit_text(
        f"✏️ <b>Rename Main Title</b>\n\n"
        f"Current Title: <b>{pname}</b>\n\n"
        f"Enter the new Main Title / Panel Name:\n<i>(This will update all duration packages under this title!)</i>",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.edit_panel_title)

@dp.message(AdminStates.edit_panel_title)
async def admin_pnlpos_save_rename(m: Message, state: FSMContext):
    data = await state.get_data()
    cat = data['pnl_cat']
    old_name = data['pnl_old_name']
    new_name = m.text.strip()
    if not new_name:
        return await m.answer("❌ Title cannot be empty.", reply_markup=admin_kb())
    
    db_query("UPDATE products SET panel_name=? WHERE category=? AND panel_name=?", (new_name, cat, old_name))
    await m.answer(
        f"✅ <b>Main Title Renamed!</b>\n\nOld: <b>{old_name}</b>\nNew: <b>{new_name}</b>\nAll packages have been updated.",
        reply_markup=admin_kb(),
        parse_mode='HTML'
    )
    await state.clear()

@dp.callback_query(F.data.startswith("adm_pnl_pkgs_"))
async def admin_pnlpos_packages(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_pkgs_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Not found", show_alert=True)
    cat, pname = prod
    
    pkgs = db_query("""
        SELECT id, name, price_inr, COALESCE(sort_order, 0) 
        FROM products 
        WHERE category=? AND panel_name=?
        ORDER BY COALESCE(sort_order, 0) ASC, id ASC
    """, (cat, pname), fetchall=True)
    
    kb = make_inline_kb(inline_keyboard=[])
    text = (
        f"📦 <b><u>PACKAGES: {pname}</u></b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"Click any package below to set its position/order within this panel:\n\n"
    )
    for p in pkgs:
        pid, pname_pkg, price, sorder = p
        kb.inline_keyboard.append([
            InlineKeyboardButton(text=f"[#{sorder}] {pname_pkg} - ₹{price:.0f}", callback_data=f"adm_pkg_pos_{pid}")
        ])
    kb.inline_keyboard.append([
        InlineKeyboardButton(text="Back to Title", callback_data=f"adm_pnl_v_{sample_id}", icon_custom_emoji_id=get_emoji_icon("back"))
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("adm_pkg_pos_"))
async def admin_pkg_pos_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    pid = int(call.data.split("pkg_pos_")[1])
    prod = db_query("SELECT name, panel_name, COALESCE(sort_order, 0) FROM products WHERE id=?", (pid,), fetchone=True)
    if not prod: return await call.answer("Product not found", show_alert=True)
    name, panel_name, sorder = prod
    await state.update_data(pkg_pid=pid)
    await call.message.edit_text(
        f"🔢 <b>Set Position for: {panel_name} - {name}</b>\n\nCurrent Position: #{sorder}\n\nEnter new position number (e.g. 1 for first package, 2 for second, etc.):",
        reply_markup=admin_back_kb(),
        parse_mode='HTML'
    )
    await state.set_state(AdminStates.edit_prod_pos)

@dp.message(AdminStates.edit_prod_pos)
async def admin_pkg_pos_save(m: Message, state: FSMContext):
    data = await state.get_data()
    pid = data['pkg_pid']
    try:
        new_pos = int(m.text.strip())
    except ValueError:
        return await m.answer("❌ Please enter a valid number (e.g. 1, 2, 3).")
    db_query("UPDATE products SET sort_order=? WHERE id=?", (new_pos, pid))
    await m.answer(f"✅ Package position updated to #{new_pos} successfully!", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data.startswith("adm_pnl_del_"))
async def admin_pnlpos_delete_prompt(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_del_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Title not found.", show_alert=True)
    cat, pname = prod
    pkg_count = db_query("SELECT COUNT(*) FROM products WHERE category=? AND panel_name=?", (cat, pname), fetchone=True)[0]
    text = (
        f"⚠️ <b><u>DELETE MAIN TITLE: {pname}</u></b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"📁 <b>Category:</b> {cat}\n"
        f"📦 <b>Packages under this title:</b> {pkg_count}\n\n"
        f"Are you sure you want to permanently delete this Main Title and all its {pkg_count} packages and vault keys?"
    )
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="☢️ Yes, Delete Title & Packages", callback_data=f"adm_pnl_delcf_{sample_id}")],
        [InlineKeyboardButton(text="❌ Cancel", callback_data=f"adm_pnl_v_{sample_id}")]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data.startswith("adm_pnl_delcf_"))
async def admin_pnlpos_delete_confirm(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    sample_id = int(call.data.split("adm_pnl_delcf_")[1])
    prod = db_query("SELECT category, panel_name FROM products WHERE id=?", (sample_id,), fetchone=True)
    if not prod: return await call.answer("Title not found or already deleted.", show_alert=True)
    cat, pname = prod
    p_ids = db_query("SELECT id FROM products WHERE category=? AND panel_name=?", (cat, pname), fetchall=True)
    for p in (p_ids or []):
        db_query("DELETE FROM product_keys WHERE product_id=?", (p[0],))
    db_query("DELETE FROM products WHERE category=? AND panel_name=?", (cat, pname))
    cat_row = db_query("SELECT id FROM categories WHERE name=?", (cat,), fetchone=True)
    back_cb = f"pnlpos_c_{cat_row[0]}" if cat_row else "admin_panel_positions_menu"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Back to Titles", callback_data=back_cb, icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text(
        f"✅ <b>Main Title Deleted!</b>\n\nTitle <b>{pname}</b> and all associated packages have been permanently wiped from the database.",
        reply_markup=kb,
        parse_mode='HTML'
    )


# Legacy Heroic ID purchase/config handlers removed: this option was retired.

@dp.callback_query(F.data == "admin_full_system_check")
async def admin_full_system_check(call: CallbackQuery):
    """Safe diagnostics: checks DB/schema and API configuration without creating purchases."""
    if not is_admin(call.from_user.id):
        return
    await call.answer("🧪 Running safe system checks...", show_alert=False)
    checks = []
    try:
        required = {
            "products": ["id","category","panel_name","name","price_inr","reseller_price","stock","is_active","external_enabled","external_product_id","external_duration","api_provider","is_maintenance"],
            "transactions": ["order_id","user_id","amount_inr","status","purpose","product_id","quantity","gateway"],
            "users": ["user_id","balance","is_reseller","is_vip"],
        }
        conn = sqlite3.connect(DB_PATH, timeout=10)
        cur = conn.cursor()
        for table, cols in required.items():
            existing = {r[1] for r in cur.execute(f"PRAGMA table_info({table})").fetchall()}
            missing = [c for c in cols if c not in existing]
            checks.append(("🟢" if not missing else "🔴", f"DB {table}: OK" if not missing else f"DB {table}: missing {', '.join(missing)}"))
        conn.close()
    except Exception as exc:
        checks.append(("🔴", f"DB check failed: {exc}"))

    bunty_url = get_setting("external_api_url", "").strip()
    bunty_key = get_setting("external_api_key", "").strip()
    checks.append(("🟢" if bunty_url and bunty_key else "🟠", "Bunty config: configured" if bunty_url and bunty_key else "Bunty config: URL/API key incomplete"))

    zap = get_setting("zapupi_api", "").strip()
    checks.append(("🟢" if zap else "🟠", "ZapUPI: API key configured" if zap else "ZapUPI: API key not configured"))

    fam = _famgateway_api_key()
    fam_url = get_setting("famgateway_url", "https://famgateway.in").strip()
    checks.append(("🟢" if fam and fam_url else "🟠", "FamGateway: configured" if fam and fam_url else "FamGateway: API key/URL incomplete"))
    checks.append(("🟢" if _whitex_token() else "🟠", "WhiteX Mode: token configured" if _whitex_token() else "WhiteX Mode: token not configured"))
    lm_key = get_setting("license_manager_api_key", "").strip()
    checks.append(("🟢" if lm_key else "🟠", "License Manager: token configured" if lm_key else "License Manager: token not configured"))
    hk_key = get_setting("hk_tamim_api_token", "").strip()
    checks.append(("🟢" if hk_key else "🟠", "HK Tamim: token configured" if hk_key else "HK Tamim: token not configured"))
    drip_key = get_setting("dripclient_api_token", "").strip()
    checks.append(("🟢" if drip_key else "🟠", "Drip Client: token configured" if drip_key else "Drip Client: token not configured"))
    shops_key = get_setting("adminshops_api_token", "").strip()
    checks.append(("🟢" if shops_key else "🟠", "Admin Shops: token configured" if shops_key else "Admin Shops: token not configured"))

    maint_total = db_query("SELECT COUNT(*) FROM products WHERE COALESCE(is_maintenance,0)=1", fetchone=True)
    checks.append(("🟢", f"Maintenance DB: {int(maint_total[0] or 0) if maint_total else 0} package(s) currently blocked"))

    text = "🧪 <b>FULL SYSTEM / API CHECK</b>\n━━━━━━━━━━━━━━━━━━\n" + "\n".join(f"{icon} {html.escape(msg)}" for icon, msg in checks)
    text += "\n━━━━━━━━━━━━━━━━━━\nℹ️ No purchase/order was created by this check.\nℹ️ Live gateway APIs that require a real order are not called here."
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="💰 Bunty Live Balance", callback_data="admin_check_bunty_balance"), InlineKeyboardButton(text="🩺 Bunty Health", callback_data="admin_bunty_health")],
        [InlineKeyboardButton(text="🔄 Re-run Check", callback_data="admin_full_system_check")],
        [InlineKeyboardButton(text="🔙 Back to Admin", callback_data="admin_panel_back")]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_api_control")
async def admin_api_control(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    rows = db_query("SELECT api_provider, COUNT(*) FROM products WHERE external_enabled=1 GROUP BY api_provider", fetchall=True) or []
    counts = {str(r[0] or 'manual').lower(): int(r[1]) for r in rows}
    bunty_key = get_setting("external_api_key", "")
    bunty_master = get_setting("external_master_key", "")
    mask = lambda x: (x[:4] + "••••" + x[-4:]) if len(x) > 8 else ("Configured" if x else "Not set")
    products = db_query("SELECT name, external_product_id, api_provider FROM products WHERE external_enabled=1 ORDER BY api_provider, name", fetchall=True) or []
    lines = ["🔧 <b>API CONTROL / BULK UPDATE</b>", "━━━━━━━━━━━━━━━━━━",
             f"⚡ <b>Bunty/AdminPanels:</b> {counts.get('bunty',0)} products",
             f"⚡ Bunty API Key: <code>{mask(bunty_key)}</code>",
             f"⚡ Bunty Master: <code>{mask(bunty_master)}</code>",
             "", "<b>Products using API:</b>"]
    for name, pid, provider in products[:30]:
        lines.append(f"• {html.escape(str(name or 'Unnamed'))} — <b>{str(provider).upper()}</b> — PID <code>{html.escape(str(pid or '-'))}</code>")
    if len(products) > 30: lines.append(f"… and {len(products)-30} more")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="💰 ⚡ Check Bunty Balance", callback_data="admin_check_bunty_balance")],
        [InlineKeyboardButton(text="🩺 ⚡ Bunty API Health Check", callback_data="admin_bunty_health")],
        [InlineKeyboardButton(text="📋 All API Products / PIDs", callback_data="admin_api_products_1")],
        [InlineKeyboardButton(text="⚡ Set Bunty API Key (ALL Bunty Products)", callback_data="admin_bulk_bunty_key")],
        [InlineKeyboardButton(text="⚡ Set Bunty Master (ALL Bunty Products)", callback_data="admin_bulk_bunty_master")],
        [InlineKeyboardButton(text="🌐 Set Update/APK Link for ALL Products", callback_data="admin_bulk_update_link")],
        [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    await call.message.edit_text("\n".join(lines), reply_markup=kb, parse_mode='HTML')

async def _bunty_balance_request() -> dict:
    """Read Bunty/AdminPanels wallet balance without placing an order."""
    url = get_setting("external_api_url", "https://adminpanels.shop/api/reseller_v1.php").strip()
    api_key = get_setting("external_api_key", "").strip()
    master_key = get_setting("external_master_key", "").strip()
    if not url:
        return {"status": "error", "message": "Bunty API URL is not configured."}
    if not api_key:
        return {"status": "error", "message": "Bunty API Key is not configured."}

    payload = {"api_key": api_key, "action": "balance"}
    headers = {"Content-Type": "application/x-www-form-urlencoded", "Accept": "application/json, text/plain, */*"}
    if master_key:
        headers["x-master-key"] = master_key
    timeout = aiohttp.ClientTimeout(total=15, connect=5, sock_connect=5, sock_read=10)
    started = time.perf_counter()
    try:
        connector = aiohttp.TCPConnector(family=socket.AF_INET, force_close=True, ssl=True)
        try:
            async with aiohttp.ClientSession(timeout=timeout, connector=connector) as session:
                async with session.post(url, data=payload, headers=headers, allow_redirects=True) as resp:
                    raw = await resp.text()
                    elapsed_ms = round((time.perf_counter() - started) * 1000)
                    result = None
                    try:
                        result = json.loads(raw) if raw.strip() else None
                    except json.JSONDecodeError:
                        result = None

                    if resp.status < 200 or resp.status >= 300:
                        return {"status":"error", "http":resp.status, "latency":elapsed_ms, "raw":raw[:1200], "message":f"Bunty HTTP {resp.status}"}
                    if result is None:
                        return {"status":"error", "http":resp.status, "latency":elapsed_ms, "raw":raw[:1200], "message":"Bunty returned non-JSON response."}

                    data = result.get("data") if isinstance(result, dict) else None
                    if not isinstance(data, dict):
                        data = result if isinstance(result, dict) else {}
                    balance = data.get("balance", result.get("balance") if isinstance(result, dict) else None)
                    currency = data.get("currency", result.get("currency", "INR") if isinstance(result, dict) else "INR")
                    ok = balance is not None and not (isinstance(result, dict) and result.get("error"))
                    if isinstance(result, dict) and str(result.get("status", "")).lower() in ("error", "failed", "failure"):
                        ok = False
                    msg = result.get("message") or result.get("msg") or result.get("error") if isinstance(result, dict) else ""
                    return {
                        "status":"success" if ok else "error",
                        "http":resp.status, "latency":elapsed_ms,
                        "balance":balance, "currency":currency,
                        "message":str(msg or ("Balance received" if ok else "Bunty did not return a balance field.")),
                        "json":result, "raw":raw[:1200]
                    }
        finally:
            if not connector.closed:
                await connector.close()
    except (aiohttp.ClientError, asyncio.TimeoutError, OSError) as exc:
        elapsed_ms = round((time.perf_counter() - started) * 1000)
        logger.warning("Bunty balance check failed: %s", exc)
        return {"status":"error", "latency":elapsed_ms, "message":f"Connection failed: {type(exc).__name__}: {exc}"}
    except Exception as exc:
        logger.exception("Unexpected Bunty balance check error")
        return {"status":"error", "message":f"Unexpected error: {exc}"}


@dp.callback_query(F.data == "admin_check_bunty_balance")
async def admin_check_bunty_balance(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await call.answer("⏳ Checking Bunty balance...", show_alert=False)
    result = await _bunty_balance_request()
    if result.get("status") == "success":
        balance = result.get("balance")
        currency = html.escape(str(result.get("currency") or "INR"))
        threshold = get_setting("bunty_balance_alert_threshold", "0")
        try:
            low = float(threshold or 0) > 0 and float(balance) <= float(threshold)
        except (TypeError, ValueError):
            low = False
        low_line = "\n⚠️ <b>LOW BALANCE ALERT:</b> threshold reached." if low else ""
        text = (f"💰 <b>BUNTY / ADMINPANELS BALANCE</b>\n\n"
                f"💵 <b>Balance:</b> <code>{html.escape(str(balance))}</code> {currency}\n"
                f"📡 <b>HTTP:</b> {result.get('http','-')}\n"
                f"⚡ <b>Response:</b> {result.get('latency','-')} ms\n"
                f"🎯 <b>Action:</b> balance\n"
                f"🔐 <b>Key:</b> configured\n"
                f"{low_line}")
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="🔄 Check Again", callback_data="admin_check_bunty_balance")],
            [InlineKeyboardButton(text="🩺 Full Health Check", callback_data="admin_bunty_health")],
            [InlineKeyboardButton(text="🔙 API Control", callback_data="admin_api_control")]
        ])
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
    else:
        preview = html.escape(str(result.get("raw") or result.get("message") or "Unknown error"))[:1800]
        text = (f"❌ <b>BUNTY BALANCE CHECK FAILED</b>\n\n"
                f"📡 HTTP: <code>{result.get('http','-')}</code>\n"
                f"⚡ Response: <code>{result.get('latency','-')} ms</code>\n"
                f"💬 {html.escape(str(result.get('message','Unknown error')))}\n\n"
                f"<b>Response Preview:</b>\n<code>{preview}</code>")
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="🔄 Retry", callback_data="admin_check_bunty_balance")],
            [InlineKeyboardButton(text="⚙️ Bunty API Setup", callback_data="admin_setup_external_api")],
            [InlineKeyboardButton(text="🔙 API Control", callback_data="admin_api_control")]
        ])
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")


@dp.callback_query(F.data == "admin_bunty_health")
async def admin_bunty_health(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await call.answer("🩺 Running Bunty API health check...", show_alert=False)
    result = await _bunty_balance_request()
    if result.get("status") == "success":
        text = ("🩺 <b>BUNTY API HEALTH</b>\n━━━━━━━━━━━━━━━━━━\n"
                f"🟢 <b>Connection:</b> OK\n"
                f"🟢 <b>HTTP:</b> {result.get('http','-')}\n"
                f"⚡ <b>Latency:</b> {result.get('latency','-')} ms\n"
                f"💰 <b>Balance:</b> <code>{html.escape(str(result.get('balance')))}</code> {html.escape(str(result.get('currency') or 'INR'))}\n"
                "🧪 <b>Test:</b> balance action only (NO purchase made)\n━━━━━━━━━━━━━━━━━━")
    else:
        text = ("🩺 <b>BUNTY API HEALTH</b>\n━━━━━━━━━━━━━━━━━━\n"
                "🔴 <b>Status:</b> FAILED\n"
                f"📡 <b>HTTP:</b> {result.get('http','-')}\n"
                f"⚡ <b>Latency:</b> {result.get('latency','-')} ms\n"
                f"💬 <b>Error:</b> {html.escape(str(result.get('message','Unknown error')))}\n━━━━━━━━━━━━━━━━━━")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="💰 Check Balance", callback_data="admin_check_bunty_balance")],
        [InlineKeyboardButton(text="⚙️ Bunty API Setup", callback_data="admin_setup_external_api")],
        [InlineKeyboardButton(text="🔙 API Control", callback_data="admin_api_control")]
    ])
    await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")


def _api_products_keyboard(page: int, total: int):
    per_page = 10
    pages = max(1, (total + per_page - 1) // per_page)
    row = []
    if page > 1:
        row.append(InlineKeyboardButton(text="◀️ Prev", callback_data=f"admin_api_products_{page-1}"))
    if page < pages:
        row.append(InlineKeyboardButton(text="Next ▶️", callback_data=f"admin_api_products_{page+1}"))
    rows = [row] if row else []
    rows.append([InlineKeyboardButton(text="🔙 API Control", callback_data="admin_api_control")])
    return rows


@dp.callback_query(F.data.regexp(r"^admin_api_products_\d+$"))
async def admin_api_products(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    page = max(1, int(call.data.rsplit("_",1)[1]))
    per_page = 10
    total_row = db_query("SELECT COUNT(*) FROM products WHERE external_enabled=1", fetchone=True)
    total = int(total_row[0] or 0) if total_row else 0
    offset = (page - 1) * per_page
    rows = db_query("SELECT name, panel_name, external_product_id, api_provider, external_duration, is_active FROM products WHERE external_enabled=1 ORDER BY api_provider, panel_name, name LIMIT ? OFFSET ?", (per_page, offset), fetchall=True) or []
    pages = max(1, (total + per_page - 1) // per_page)
    lines = [f"📋 <b>API PRODUCT MAP</b> — Page {page}/{pages}", "━━━━━━━━━━━━━━━━━━"]
    if not rows:
        lines.append("No API products found.")
    for idx, (name, panel, pid, provider, duration, active) in enumerate(rows, offset+1):
        status = "🟢" if int(active or 0) else "🔴"
        lines.append(f"{idx}. {status} <b>{html.escape(str(name or 'Unnamed'))}</b>\n   🏷 Panel: {html.escape(str(panel or '-'))}\n   🌐 API: <b>{html.escape(str(provider or 'bunty').upper())}</b> | PID: <code>{html.escape(str(pid or '-'))}</code>\n   ⏱ Duration: <code>{html.escape(str(duration or '-'))}</code>")
    kb = make_inline_kb(inline_keyboard=_api_products_keyboard(page, total))
    await call.message.edit_text("\n".join(lines), reply_markup=kb, parse_mode="HTML")


@dp.callback_query(F.data == "admin_bulk_update_link")
async def admin_bulk_update_link(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text(
        "🌐 <b>BULK UPDATE/APK LINK</b>\n\nEnter the new update/download channel or APK link.\nThis will replace the <code>apk_link</code> for <b>ALL active products</b> at once.",
        reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.bulk_update_link)

@dp.message(AdminStates.bulk_update_link)
async def save_bulk_update_link(m: Message, state: FSMContext):
    value=(m.text or '').strip()
    if value.lower() in ('none','off','-'):
        value=''
    elif value and not value.startswith(('http://','https://','tg://')):
        return await m.answer("❌ Send a valid http(s):// or tg:// link, or type <code>none</code> to clear it.", parse_mode='HTML')
    db_query("UPDATE products SET apk_link=? WHERE is_active=1", (value,))
    count = db_query("SELECT COUNT(*) FROM products WHERE is_active=1", fetchone=True)
    await state.clear()
    await m.answer(f"✅ Update/APK link synchronized across <b>{int(count[0]) if count else 0}</b> active products.", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data.in_(["admin_bulk_bunty_key", "admin_bulk_bunty_master"]))
async def admin_bulk_api_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    action = call.data.replace("admin_bulk_", "")
    await state.update_data(bulk_api_action=action)
    labels = {
        "bunty_key": "Bunty/AdminPanels API Key",
        "bunty_master": "Bunty/AdminPanels Master Key",
    }
    await call.message.edit_text(f"🔐 Enter new <b>{labels[action]}</b>.\n\nThis is a global credential: every product assigned to that provider will use the new value automatically.", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ext_key)

@dp.message(AdminStates.wait_for_ext_key)
async def save_ext_key_or_bulk(m: Message, state: FSMContext):
    data = await state.get_data()
    action = data.get("bulk_api_action")
    value = (m.text or "").strip()
    if not value:
        return await m.answer("❌ Credential cannot be empty.")
    if action == "bunty_key":
        set_setting("external_api_key", value)
        msg = "⚡ Bunty API Key updated globally. All Bunty products now use the new key."
    elif action == "bunty_master":
        set_setting("external_master_key", value)
        msg = "⚡ Bunty Master Key updated globally. All Bunty products now use the new master."
    else:
        # Existing normal External API setup flow.
        set_setting("external_api_key", value)
        msg = "✅ External API Key saved."
    await state.clear()
    await m.answer("✅ <b>" + html.escape(msg) + "</b>", reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_setup_famgateway")
async def admin_setup_famgateway(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    key = _famgateway_api_key()
    url = _famgateway_base_url()
    mask = (key[:4] + "••••" + key[-4:]) if len(key) > 8 else ("Configured" if key else "Not set")
    gateway_status = (get_setting("gateway_famgateway_status", "ON") or "ON").upper()
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"Gateway Status: {gateway_status} — Tap to Toggle", callback_data="admin_toggle_famgateway")],
        [InlineKeyboardButton(text="Set FamGateway API Key", callback_data="admin_set_famgateway_key")],
        [InlineKeyboardButton(text="Set Gateway URL", callback_data="admin_set_famgateway_url")],
        [InlineKeyboardButton(text="Back", callback_data="admin_panel_back")]
    ], _width=1)
    await call.message.edit_text(f"<b>FAMGATEWAY SETTINGS</b>\n\nStatus: <b>{gateway_status}</b>\nURL: <code>{html.escape(url)}</code>\nAPI Key: <code>{mask}</code>\n\nWhen OFF, users cannot start new FamGateway payments. Existing pending orders can still be verified.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_toggle_famgateway")
async def admin_toggle_famgateway(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    current = (get_setting("gateway_famgateway_status", "ON") or "ON").upper()
    new_value = "OFF" if current == "ON" else "ON"
    set_setting("gateway_famgateway_status", new_value)
    await call.answer(f"FamGateway {new_value}")
    key = _famgateway_api_key(); url = _famgateway_base_url()
    mask = (key[:4] + "••••" + key[-4:]) if len(key) > 8 else ("Configured" if key else "Not set")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"Gateway Status: {new_value} — Tap to Toggle", callback_data="admin_toggle_famgateway")],
        [InlineKeyboardButton(text="Set FamGateway API Key", callback_data="admin_set_famgateway_key")],
        [InlineKeyboardButton(text="Set Gateway URL", callback_data="admin_set_famgateway_url")],
        [InlineKeyboardButton(text="Back", callback_data="admin_panel_back")]
    ], _width=1)
    await call.message.edit_text(f"<b>FAMGATEWAY SETTINGS</b>\n\nStatus: <b>{new_value}</b>\nURL: <code>{html.escape(url)}</code>\nAPI Key: <code>{mask}</code>\n\nWhen OFF, users cannot start new FamGateway payments. Existing pending orders can still be verified.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "admin_set_famgateway_key")
async def admin_set_famgateway_key(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("Enter FamGateway API Key:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ext_master)
    await state.update_data(famgateway_field="key")

@dp.callback_query(F.data == "admin_set_famgateway_url")
async def admin_set_famgateway_url(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("Enter FamGateway base URL (default https://famgateway.in):", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ext_master)
    await state.update_data(famgateway_field="url")

@dp.message(AdminStates.wait_for_ext_master)
async def save_ext_master_or_famgateway(m: Message, state: FSMContext):
    data = await state.get_data()
    value = (m.text or "").strip()
    if not value:
        return await m.answer("❌ Value cannot be empty.")
    if data.get("famgateway_field") == "key":
        set_setting("famgateway_api", value)
        msg = "FamGateway API Key saved."
    elif data.get("famgateway_field") == "url":
        if not value.startswith(("http://", "https://")):
            return await m.answer("❌ URL must start with http:// or https://")
        set_setting("famgateway_url", value.rstrip("/"))
        msg = "FamGateway URL saved."
    else:
        set_setting("external_master_key", value)
        msg = "External API Master Key saved."
    await state.clear()
    await m.answer("✅ " + msg, reply_markup=admin_kb(), parse_mode='HTML')

@dp.callback_query(F.data == "admin_setup_zapupi")
async def setup_zapupi_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("⚙️ <b>ZAPUPI SECURITY DEPLOYMENT</b>\nInput master <b>API Key (zap_key)</b>:\n<i>(Type /cancel to abort sequence)</i>", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_zapupi_api)

@dp.message(AdminStates.wait_for_zapupi_api)
async def zapupi_api(m: Message, state: FSMContext):
    if m.text == '/cancel':
        await state.clear()
        return await m.answer("Sequence killed.", reply_markup=admin_kb(), parse_mode='HTML')
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('zapupi_api', ?)", (m.text.strip(),))
    await m.answer("✅ <b>Keys synchronized with ZapUPI backbone.</b>", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_setup_binance")
async def setup_binance_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("🪙 <b>CRYPTO NODE INIT: Step 1/3</b>\nInput Master <b>Binance API Key</b>:\n<i>(Type /cancel to halt protocol)</i>", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_binance_api)

@dp.message(AdminStates.wait_for_binance_api)
async def setup_binance_api(m: Message, state: FSMContext):
    if m.text == '/cancel':
        await state.clear()
        return await m.answer("Sequence aborted.", reply_markup=admin_kb(), parse_mode='HTML')
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('binance_api', ?)", (m.text.strip(),))
    await m.answer("🪙 <b>CRYPTO NODE INIT: Step 2/3</b>\nNow inject the highly secure <b>Binance Secret Key</b>:", parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_binance_secret)

@dp.message(AdminStates.wait_for_binance_secret)
async def setup_binance_secret(m: Message, state: FSMContext):
    db_query("INSERT OR REPLACE INTO settings (key, value) VALUES ('binance_secret', ?)", (m.text.strip(),))
    await m.answer("🪙 <b>CRYPTO NODE INIT: Step 3/3</b>\nFinal variable: Set the public <b>USDT Deposit Address (TRC20/BEP20)</b>\nUsers will broadcast to this ledger:", parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_binance_address)

@dp.message(AdminStates.wait_for_binance_address)
async def setup_binance_address(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    value = (m.text or "").strip()
    if value.lower() == "/cancel":
        await state.clear()
        return await m.answer("Cancelled.", reply_markup=admin_kb())
    if len(value) < 3 or len(value) > 180:
        return await m.answer("❌ Send a valid Binance Pay ID (3–180 characters).")
    set_setting("binance_address", value)
    set_setting("binance_qr_file_id", "")
    await state.clear()
    await m.answer("✅ <b>Binance Pay ID saved.</b> Users will see the ID instead of a QR.", reply_markup=admin_kb(), parse_mode='HTML')

# ==============================================================================
# 22. BOOTSTRAPPING & MAIN
# ==============================================================================
async def main() -> None:
    acquire_single_instance_lock()
    init_db()
    logger.info("Initializing DB structure...")
    migrate_categories()
    asyncio.create_task(auto_verify_task(), name="payment-auto-verifier")
    dashboard_runner = await start_web_dashboard()
    logger.info("Payment Auto-Verifier Daemon Running in Background (ZapUPI + FamGateway).")
    logger.info("🚀 CORE SYSTEM IS FULLY OPERATIONAL...")
    # Diagnostic only: Railway outbound IP may change and may not be static.
    try:
        async with aiohttp.ClientSession() as ip_session:
            async with ip_session.get("https://api.ipify.org", timeout=aiohttp.ClientTimeout(total=8)) as ip_response:
                if ip_response.status == 200:
                    logger.info("OUTGOING_PUBLIC_IPV4_DIAGNOSTIC=%s", (await ip_response.text()).strip())
                else:
                    logger.warning("Outgoing IP check returned HTTP %s", ip_response.status)
    except Exception as ip_error:
        logger.warning("Outgoing IP diagnostic failed: %s", ip_error)
    try:
        logger.info("Starting Telegram polling; configured ADMIN_IDS=%s", sorted(ADMIN_IDS))
        # Verify the token and connectivity early so a bad token/network issue is visible in logs.
        me = await bot.get_me()
        logger.info("Telegram connected successfully as @%s (id=%s)", me.username, me.id)
        await dp.start_polling(bot, close_bot_session=False, allowed_updates=["message", "callback_query"])
    except Exception:
        logger.exception("Critical System Failure in polling/startup")
        raise
    finally:
        if dashboard_runner is not None:
            await dashboard_runner.cleanup()
        await bot.session.close()

# ==============================================================================

# ==============================================================================
# ==============================================================================
# WEB ADMIN DASHBOARD & API BACKEND
# Serves dashboard.html and connects to yp_shop.db
# ==============================================================================
def _dashboard_enabled() -> bool:
    return True

def _dashboard_auth(request: web.Request) -> bool:
    # DB password can be changed by an authorized Telegram admin without redeploying.
    expected = (get_setting("dashboard_password", "") or os.getenv("DASHBOARD_PASSWORD", "")).strip()
    if not expected:
        return False
    auth = request.headers.get("Authorization", "")
    if not auth.startswith("Basic "):
        return False
    try:
        import base64
        decoded = base64.b64decode(auth.split(" ", 1)[1]).decode("utf-8")
        _username, password = decoded.split(":", 1)
        if expected.startswith("sha256$"):
            candidate = "sha256$" + hashlib.sha256(password.encode("utf-8")).hexdigest()
            return hmac.compare_digest(candidate, expected)
        return hmac.compare_digest(password, expected)
    except Exception:
        return False

@web.middleware
async def dashboard_auth_middleware(request: web.Request, handler):
    if not _dashboard_auth(request):
        return web.Response(status=401, headers={"WWW-Authenticate": 'Basic realm="Bot Admin Dashboard"'}, text="Admin login required. Set the dashboard password using the Telegram admin command.")
    return await handler(request)

async def dashboard_page(request: web.Request):
    candidate_paths = [
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "dashboard.html"),
        os.path.join(DATA_DIR, "dashboard.html"),
        "/home/monuhortanti71/uploads/dashboard.html",
    ]
    html_file = next((p for p in candidate_paths if os.path.exists(p)), None)
    if not html_file:
        raise web.HTTPNotFound(text="dashboard.html not found! Please place dashboard.html in the same directory.")
    return web.FileResponse(html_file, headers={"Content-Type": "text/html; charset=utf-8"})

async def api_stats(request: web.Request):
    total_users = (db_query("SELECT COUNT(*) FROM users", fetchone=True) or (0,))[0]
    total_orders = (db_query("SELECT COUNT(*) FROM orders", fetchone=True) or (0,))[0]
    total_rev = (db_query("SELECT SUM(price_paid) FROM orders", fetchone=True) or (0.0,))[0] or 0.0
    total_products = (db_query("SELECT COUNT(*) FROM products", fetchone=True) or (0,))[0]
    total_stock = (db_query("SELECT COUNT(*) FROM product_keys WHERE is_used=0", fetchone=True) or (0,))[0]
    total_balance = (db_query("SELECT SUM(balance) FROM users", fetchone=True) or (0.0,))[0] or 0.0
    return web.json_response({
        "total_users": total_users,
        "total_orders": total_orders,
        "total_revenue": round(float(total_rev), 2),
        "total_products": total_products,
        "total_stock": total_stock,
        "total_balance": round(float(total_balance), 2),
        "bot_status": get_setting("bot_status", "ON"),
        "vip_status": get_setting("vip_status", "OFF"),
        "reseller_system_status": get_setting("reseller_system_status", "ON"),
        "ff_like_enabled": get_setting("ff_like_enabled", "OFF"),
    })

async def api_users(request: web.Request):
    rows = db_query("SELECT user_id, phone, first_name, username, balance, account_type, orders_count, spent, is_reseller, is_vip, is_banned, warnings, joined_date FROM users ORDER BY user_id DESC LIMIT 1000", fetchall=True) or []
    users = []
    for r in rows:
        users.append({
            "user_id": r[0],
            "phone": r[1] or "",
            "first_name": r[2] or "",
            "username": r[3] or "",
            "balance": float(r[4] or 0.0),
            "account_type": r[5] or "Regular",
            "orders_count": r[6] or 0,
            "spent": float(r[7] or 0.0),
            "is_reseller": r[8] or 0,
            "is_vip": r[9] or 0,
            "is_banned": r[10] or 0,
            "warnings": r[11] or 0,
            "joined_date": r[12] or ""
        })
    return web.json_response(users)

async def api_users_update(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    uid = int(data.get("user_id"))
    balance = float(data.get("balance", 0.0))
    role = str(data.get("account_type", "Regular"))
    is_banned = 1 if str(data.get("is_banned", "0")) in ("1", "true") else 0
    warnings = int(data.get("warnings", 0))
    is_reseller = 1 if role == "Reseller" else 0
    is_vip = 1 if role == "VIP" else 0
    db_query("UPDATE users SET balance=?, account_type=?, is_reseller=?, is_vip=?, is_banned=?, warnings=? WHERE user_id=?", (balance, role, is_reseller, is_vip, is_banned, warnings, uid))
    return web.json_response({"status": "success"})

async def api_users_zero_all(request: web.Request):
    db_query("UPDATE users SET balance=0.0")
    return web.json_response({"status": "success"})

async def api_products(request: web.Request):
    rows = db_query("SELECT id, category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit, is_active, external_enabled, external_product_id, external_duration, api_provider FROM products ORDER BY id DESC", fetchall=True) or []
    res = []
    for r in rows:
        keys_count = (db_query("SELECT COUNT(*) FROM product_keys WHERE product_id=? AND is_used=0", (r[0],), fetchone=True) or (0,))[0]
        res.append({
            "id": r[0], "category": r[1] or "", "panel_name": r[2] or "", "name": r[3] or "",
            "price_inr": float(r[4] or 0.0), "reseller_price": float(r[5] or 0.0), "stock": r[6] or 0,
            "apk_link": r[7] or "", "validity": r[8] or "Lifetime", "device_limit": r[9] or "1 Device",
            "is_active": r[10] or 0, "available_keys": keys_count,
            "external_enabled": r[11] or 0, "external_product_id": r[12] or "",
            "external_duration": r[13] or "", "api_provider": r[14] or "manual"
        })
    return web.json_response(res)

async def api_products_save(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    pid = data.get("id")
    category = str(data.get("category", "")).strip()[:100]
    panel_name = str(data.get("panel_name", "")).strip()[:120]
    name = str(data.get("name", "")).strip()[:180]
    price_inr = max(0.0, float(data.get("price_inr", 0.0) or 0.0))
    reseller_price = max(0.0, float(data.get("reseller_price", 0.0) or 0.0))
    stock = max(0, int(data.get("stock", 0) or 0))
    apk_link = str(data.get("apk_link", "")).strip()[:1000]
    validity = str(data.get("validity", "Lifetime")).strip()[:80]
    device_limit = str(data.get("device_limit", "1 Device")).strip()[:80]
    is_active = 1 if str(data.get("is_active", "1")).lower() in ("1", "true", "on") else 0
    external_enabled = 1 if str(data.get("external_enabled", "0")).lower() in ("1", "true", "on") else 0
    external_product_id = str(data.get("external_product_id", "")).strip()[:160]
    external_duration = str(data.get("external_duration", validity)).strip()[:80]
    api_provider = str(data.get("api_provider", "manual")).strip().lower()[:40]
    allowed_providers = {"manual", "bunty", "license_manager", "hk_tamim", "dripclient", "adminshops", "whitex", "panelstore"}
    if api_provider not in allowed_providers:
        return web.json_response({"status": "error", "message": "Unsupported API provider"}, status=400)
    if external_enabled and (api_provider == "manual" or not external_product_id):
        return web.json_response({"status": "error", "message": "Choose an API provider and enter the provider Product ID"}, status=400)
    if not name:
        return web.json_response({"status": "error", "message": "Product name is required"}, status=400)
    if pid and str(pid).strip() and str(pid).isdigit():
        db_query("UPDATE products SET category=?, panel_name=?, name=?, price_inr=?, reseller_price=?, stock=?, apk_link=?, validity=?, device_limit=?, is_active=?, external_enabled=?, external_product_id=?, external_duration=?, api_provider=? WHERE id=?", (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit, is_active, external_enabled, external_product_id, external_duration, api_provider, int(pid)))
    else:
        db_query("INSERT INTO products (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit, is_active, external_enabled, external_product_id, external_duration, api_provider) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)", (category, panel_name, name, price_inr, reseller_price, stock, apk_link, validity, device_limit, is_active, external_enabled, external_product_id, external_duration, api_provider))
    return web.json_response({"status": "success"})

async def api_products_delete(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    pid = int(data.get("id"))
    db_query("DELETE FROM products WHERE id=?", (pid,))
    db_query("DELETE FROM product_keys WHERE product_id=?", (pid,))
    return web.json_response({"status": "success"})

async def api_keys(request: web.Request):
    pid = request.query.get("product_id")
    if not pid:
        return web.json_response([])
    rows = db_query("SELECT id, key_text, is_used FROM product_keys WHERE product_id=? ORDER BY id DESC LIMIT 500", (int(pid),), fetchall=True) or []
    return web.json_response([{"id": r[0], "key_text": r[1], "is_used": r[2]} for r in rows])

async def api_keys_bulk_add(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    pid = int(data.get("product_id"))
    raw_keys = str(data.get("keys", ""))
    lines = [line.strip() for line in raw_keys.splitlines() if line.strip()]
    for k in lines:
        db_query("INSERT INTO product_keys (product_id, key_text, is_used) VALUES (?, ?, 0)", (pid, k))
    avail = (db_query("SELECT COUNT(*) FROM product_keys WHERE product_id=? AND is_used=0", (pid,), fetchone=True) or (0,))[0]
    db_query("UPDATE products SET stock=? WHERE id=?", (avail, pid))
    return web.json_response({"status": "success", "added_count": len(lines)})

async def api_keys_delete(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    kid = int(data.get("id"))
    key_info = db_query("SELECT product_id FROM product_keys WHERE id=?", (kid,), fetchone=True)
    db_query("DELETE FROM product_keys WHERE id=?", (kid,))
    if key_info:
        avail = (db_query("SELECT COUNT(*) FROM product_keys WHERE product_id=? AND is_used=0", (key_info[0],), fetchone=True) or (0,))[0]
        db_query("UPDATE products SET stock=? WHERE id=?", (avail, key_info[0]))
    return web.json_response({"status": "success"})

async def api_categories(request: web.Request):
    rows = db_query("SELECT id, name, emoji_id, sort_order FROM categories ORDER BY sort_order ASC, id ASC", fetchall=True) or []
    return web.json_response([{"id": r[0], "name": r[1], "emoji_id": r[2] or "", "sort_order": r[3] or 0} for r in rows])

async def api_categories_save(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    name = str(data.get("name", "")).strip()[:100]
    emoji_id = str(data.get("emoji_id", "")).strip()[:50]
    sort_order = int(data.get("sort_order", 0) or 0)
    if not name:
        return web.json_response({"status": "error", "message": "Category name required"}, status=400)
    db_query("INSERT OR REPLACE INTO categories (name, emoji_id, sort_order) VALUES (?, ?, ?)", (name, emoji_id, sort_order))
    return web.json_response({"status": "success"})

async def api_categories_delete(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    cid = int(data.get("id"))
    db_query("DELETE FROM categories WHERE id=?", (cid,))
    return web.json_response({"status": "success"})

async def api_orders(request: web.Request):
    limit = int(request.query.get("limit", 200))
    rows = db_query("SELECT id, user_id, product_name, price_paid, delivered_key, purchase_date FROM orders ORDER BY id DESC LIMIT ?", (limit,), fetchall=True) or []
    return web.json_response([{"id": r[0], "user_id": r[1], "product_name": r[2], "price_paid": r[3], "delivered_key": r[4], "purchase_date": r[5]} for r in rows])

async def api_ff_system(request: web.Request):
    prods = db_query("SELECT id, title, description, price, active, created_at, product_type, duration_days, notice FROM ff_products ORDER BY id DESC", fetchall=True) or []
    orders = db_query("SELECT id, user_id, product_id, product_title, price, game_uid, game_photo_id, region, payment_method, proof_file_id, status, created_at FROM ff_orders ORDER BY id DESC LIMIT 200", fetchall=True) or []
    return web.json_response({
        "products": [{"id": r[0], "title": r[1], "description": r[2] or "", "price": r[3], "active": r[4], "created_at": r[5], "product_type": r[6], "duration_days": r[7], "notice": r[8]} for r in prods],
        "orders": [{"id": r[0], "user_id": r[1], "product_id": r[2], "product_title": r[3], "price": r[4], "game_uid": r[5], "region": r[7], "status": r[10], "created_at": r[11]} for r in orders]
    })

async def api_ff_orders_status(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    oid = int(data.get("id"))
    st = str(data.get("status", "approved")).strip()
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    db_query("UPDATE ff_orders SET status=?, updated_at=? WHERE id=?", (st, now_str, oid))
    return web.json_response({"status": "success"})

async def api_ff_products_save(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    title = str(data.get("title", "")).strip()[:100]
    price = max(0.0, float(data.get("price", 0.0) or 0.0))
    days = int(data.get("duration_days", 0) or 0)
    notice = str(data.get("notice", "")).strip()[:500]
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    db_query("INSERT INTO ff_products (title, description, price, active, created_at, product_type, duration_days, notice) VALUES (?, '', ?, 1, ?, 'manual', ?, ?)", (title, price, now_str, days, notice))
    return web.json_response({"status": "success"})

async def api_ff_products_toggle(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    pid = int(data.get("id"))
    active = 1 if int(data.get("active", 1)) else 0
    db_query("UPDATE ff_products SET active=? WHERE id=?", (active, pid))
    return web.json_response({"status": "success"})

async def api_coupons(request: web.Request):
    coupons = db_query("SELECT code, amount, uses_left FROM coupons ORDER BY code ASC", fetchall=True) or []
    rewards = db_query("SELECT id, amount FROM spin_rewards ORDER BY amount ASC", fetchall=True) or []
    return web.json_response({
        "coupons": [{"code": r[0], "amount": r[1], "uses_left": r[2]} for r in coupons],
        "spin_rewards": [{"id": r[0], "amount": r[1]} for r in rewards]
    })

async def api_coupons_save(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    code = str(data.get("code", "")).strip().upper()[:50]
    amount = max(0.0, float(data.get("amount", 0.0) or 0.0))
    uses = max(1, int(data.get("uses_left", 1) or 1))
    if not code:
        return web.json_response({"status": "error", "message": "Code required"}, status=400)
    db_query("INSERT OR REPLACE INTO coupons (code, amount, uses_left) VALUES (?, ?, ?)", (code, amount, uses))
    return web.json_response({"status": "success"})

async def api_coupons_delete(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    code = str(data.get("code", "")).strip().upper()
    db_query("DELETE FROM coupons WHERE code=?", (code,))
    return web.json_response({"status": "success"})

async def api_spin_rewards_save(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    raw = str(data.get("rewards", ""))
    amounts = [float(x.strip()) for x in raw.split(",") if x.strip()]
    db_query("DELETE FROM spin_rewards")
    for a in amounts:
        db_query("INSERT INTO spin_rewards (amount) VALUES (?)", (a,))
    return web.json_response({"status": "success"})

async def api_tickets(request: web.Request):
    rows = db_query("SELECT id, user_id, message, status, created_at FROM tickets ORDER BY id DESC LIMIT 200", fetchall=True) or []
    return web.json_response([{"id": r[0], "user_id": r[1], "message": r[2], "status": r[3], "created_at": r[4]} for r in rows])

async def api_tickets_status(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    tid = int(data.get("id"))
    st = str(data.get("status", "Closed"))
    db_query("UPDATE tickets SET status=? WHERE id=?", (st, tid))
    return web.json_response({"status": "success"})

async def api_transactions(request: web.Request):
    rows = db_query("SELECT order_id, user_id, amount_inr, status, timestamp, gateway FROM transactions ORDER BY timestamp DESC LIMIT 200", fetchall=True) or []
    return web.json_response([{"order_id": r[0], "user_id": r[1], "amount_inr": r[2], "status": r[3], "timestamp": r[4], "gateway": r[5]} for r in rows])

async def api_settings(request: web.Request):
    rows = db_query("SELECT key, value FROM settings ORDER BY key ASC", fetchall=True) or []
    return web.json_response({r[0]: r[1] or "" for r in rows})

async def api_settings_save(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    for k, v in data.items():
        if re.fullmatch(r"[a-zA-Z0-9_.-]{1,100}", k):
            set_setting(k, str(v)[:2000])
    return web.json_response({"status": "success"})

async def api_settings_toggle(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    k = str(data.get("key", "")).strip()
    curr = get_setting(k, "OFF")
    nxt = "OFF" if curr == "ON" else "ON"
    set_setting(k, nxt)
    return web.json_response({"status": "success", "key": k, "value": nxt})

async def api_db_download(request: web.Request):
    if not os.path.exists(DB_PATH):
        raise web.HTTPNotFound(text="Database file not found")
    return web.FileResponse(DB_PATH, headers={"Content-Disposition": f'attachment; filename="{os.path.basename(DB_PATH)}"'})

async def api_db_query(request: web.Request):
    data = await request.json() if request.can_read_body else await request.post()
    q = str(data.get("query", "")).strip()
    if not q:
        return web.json_response({"error": "Empty query"}, status=400)
    conn = sqlite3.connect(DB_PATH, timeout=30.0)
    c = conn.cursor()
    try:
        c.execute(q)
        if q.strip().upper().startswith("SELECT") or q.strip().upper().startswith("PRAGMA"):
            cols = [d[0] for d in c.description] if c.description else []
            rows = c.fetchall()
            res = [dict(zip(cols, r)) for r in rows]
            return web.json_response({"columns": cols, "rows": res, "count": len(res)})
        else:
            conn.commit()
            return web.json_response({"rows_affected": c.rowcount, "status": "success"})
    except Exception as e:
        return web.json_response({"error": str(e)}, status=400)
    finally:
        conn.close()

async def start_web_dashboard():
    app = web.Application(middlewares=[dashboard_auth_middleware], client_max_size=100 * 1024 * 1024)
    app.router.add_get("/", dashboard_page)
    app.router.add_get("/dashboard", dashboard_page)
    app.router.add_get("/dashboard.html", dashboard_page)
    app.router.add_get("/api/stats", api_stats)
    app.router.add_get("/api/users", api_users)
    app.router.add_post("/api/users/update", api_users_update)
    app.router.add_post("/api/users/zero_all", api_users_zero_all)
    app.router.add_get("/api/products", api_products)
    app.router.add_post("/api/products/save", api_products_save)
    app.router.add_post("/api/products/delete", api_products_delete)
    app.router.add_get("/api/keys", api_keys)
    app.router.add_post("/api/keys/add", api_keys_bulk_add)
    app.router.add_post("/api/keys/bulk_add", api_keys_bulk_add)
    app.router.add_post("/api/keys/delete", api_keys_delete)
    app.router.add_get("/api/categories", api_categories)
    app.router.add_post("/api/categories/save", api_categories_save)
    app.router.add_post("/api/categories/delete", api_categories_delete)
    app.router.add_get("/api/orders", api_orders)
    app.router.add_get("/api/ff_system", api_ff_system)
    app.router.add_post("/api/ff_products/save", api_ff_products_save)
    app.router.add_post("/api/ff_products/toggle", api_ff_products_toggle)
    app.router.add_post("/api/ff_orders/status", api_ff_orders_status)
    app.router.add_get("/api/coupons", api_coupons)
    app.router.add_post("/api/coupons/save", api_coupons_save)
    app.router.add_post("/api/coupons/delete", api_coupons_delete)
    app.router.add_post("/api/spin_rewards/save", api_spin_rewards_save)
    app.router.add_get("/api/tickets", api_tickets)
    app.router.add_post("/api/tickets/status", api_tickets_status)
    app.router.add_get("/api/transactions", api_transactions)
    app.router.add_get("/api/settings", api_settings)
    app.router.add_post("/api/settings/save", api_settings_save)
    app.router.add_post("/api/settings/toggle", api_settings_toggle)
    app.router.add_get("/api/db/download", api_db_download)
    app.router.add_post("/api/db/query", api_db_query)

    runner = web.AppRunner(app, access_log=logger)
    await runner.setup()
    host = os.getenv("DASHBOARD_HOST", "0.0.0.0")
    try:
        port = int(os.getenv("PORT", os.getenv("DASHBOARD_PORT", get_setting("dashboard_port", "8080") or "8080")))
    except ValueError:
        port = 8080
    site = web.TCPSite(runner, host, port)
    await site.start()
    logger.info("⚡ Web Admin Dashboard running on http://%s:%s", host, port)
    return runner


# EXTERNAL KEY GENERATION API
# ==============================================================================
def normalize_api_duration(duration: str) -> str:
    """Normalize the package name into the duration format expected by the API."""
    value = str(duration or "").strip()
    if not value:
        return value

    # Normalize whitespace
    value = re.sub(r"\s+", " ", value)
    
    # Define exact mapping for your API format
    # API expects: "X Hours" or "X DaYs" (with capital D and Y)
    duration_map = {
        # Hours - API expects "X Hours"
        "1 hour": "1 Hours",
        "1 hours": "1 Hours",
        "1hr": "1 Hours",
        "1h": "1 Hours",
        "2 hour": "2 Hours",
        "2 hours": "2 Hours",
        "2hr": "2 Hours",
        "3 hour": "3 Hours",
        "3 hours": "3 Hours",
        "3hr": "3 Hours",
        "6 hour": "6 Hours",
        "6 hours": "6 Hours",
        "6hr": "6 Hours",
        "12 hour": "12 Hours",
        "12 hours": "12 Hours",
        "12hr": "12 Hours",
        
        "24 hour": "24 Hours",
        "24 hours": "24 Hours",
        "24hr": "24 Hours",
        
        # Days - API expects "X DaYs" (capital D and Y)
        "1 day": "1 DaYs",
        "1 days": "1 DaYs",
        "1d": "1 DaYs",
        "2 day": "2 DaYs",
        "2 days": "2 DaYs",
        "2d": "2 DaYs",
        "3 day": "3 DaYs",
        "3 days": "3 DaYs",
        "3d": "3 DaYs",
        "5 day": "5 DaYs",
        "5 days": "5 DaYs",
        "5d": "5 DaYs",
        "7 day": "7 DaYs",
        "7 days": "7 DaYs",
        "7d": "7 DaYs",
        "10 day": "10 DaYs",
        "10 days": "10 DaYs",
        "10d": "10 DaYs",
        "14 day": "14 DaYs",
        "14 days": "14 DaYs",
        "14d": "14 DaYs",
        "15 day": "15 DaYs",
        "15 days": "15 DaYs",
        "15d": "15 DaYs",
        "20 day": "20 DaYs",
        "20 days": "20 DaYs",
        "20d": "20 DaYs",
        "28 day": "28 DaYs",
        "28 days": "28 DaYs",
        "28d": "28 DaYs",
        "30 day": "30 DaYs",
        "30 days": "30 DaYs",
        "30d": "30 DaYs",
        "60 day": "60 DaYs",
        "60 days": "60 DaYs",
        "60d": "60 DaYs",
    }
    
    # Check exact matches first (case insensitive)
    lower_val = value.lower()
    for pattern, result in duration_map.items():
        if lower_val == pattern.lower():
            return result
    
    # Check if it's already in correct format
    if value in ["1 Hours", "2 Hours", "3 Hours", "6 Hours", "12 Hours", "24 Hours",
                 "1 DaYs", "2 DaYs", "3 DaYs", "5 DaYs", "7 DaYs", "10 DaYs",
                 "14 DaYs", "15 DaYs", "20 DaYs", "28 DaYs", "30 DaYs", "60 DaYs"]:
        return value
    
    # Try to extract number and determine unit ONLY IF string is purely duration
    match = re.match(r"^(\d+)\s*(hour|hours|hr|hrs|h|day|days|d)$", value, re.IGNORECASE)
    if match:
        number = match.group(1)
        unit = match.group(2).lower()
        if unit in ["hour", "hours", "hr", "hrs", "h"]:
            return f"{number} Hours"
        if unit in ["day", "days", "d"]:
            return f"{number} DaYs"
    
    # If it's just a number, treat as hours
    if value.isdigit():
        return f"{value} Hours"
    
    # Return as-is if compound string (e.g. "1 DaYS NONROOT", "1 Days Nonroot")
    return value

async def fetch_external_key(product_id: str, duration: str, android_id: str = "") -> dict:
    """Buy a key using a fresh aiohttp session for every API attempt."""
    url = get_setting("external_api_url", "https://adminpanels.shop/api/reseller_v1.php").strip()
    api_key = get_setting("external_api_key", "").strip()
    master_key = get_setting("external_master_key", "").strip()

    if not url:
        return {"status": "error", "msg": "External API URL is not configured"}
    if not api_key:
        return {"status": "error", "msg": "External API key is not configured"}

    product_id = str(product_id or "").strip()
    duration = str(duration or "").strip()
    if not product_id:
        return {"status": "error", "msg": "External API Product ID is empty"}
    if not duration:
        return {"status": "error", "msg": "Product duration is empty"}

    data = {"api_key": api_key, "action": "buy", "product_id": product_id, "duration": duration}
    if android_id:
        data["android_id"] = str(android_id).strip()

    headers = {
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept": "application/json, text/plain, */*",
    }
    if master_key:
        headers["x-master-key"] = master_key

    timeout = aiohttp.ClientTimeout(total=15, connect=5, sock_connect=5, sock_read=10)

    for attempt in range(1, 3):
        try:
            logger.info("External API BUY attempt=%s product_id=%r duration=%r", attempt, product_id, duration)

            # Never reuse a ClientSession/connector from a previous attempt.
            connector = aiohttp.TCPConnector(family=socket.AF_INET, force_close=True, ssl=True)
            try:
                async with aiohttp.ClientSession(timeout=timeout, connector=connector) as session:
                    async with session.post(url, data=data, headers=headers, allow_redirects=True) as resp:
                        raw = await resp.text()
                        logger.info("External API BUY response: HTTP %s body=%s", resp.status, raw[:1000])

                        if resp.status != 200:
                            return {"status": "error", "msg": f"HTTP {resp.status}: {raw[:500]}"}
                        if not raw.strip():
                            return {"status": "error", "msg": "API returned an empty response"}
                        try:
                            result = json.loads(raw)
                        except json.JSONDecodeError:
                            return {"status": "error", "msg": f"API returned invalid JSON: {raw[:300]}"}
                        if not isinstance(result, dict):
                            return {"status": "error", "msg": "API returned an invalid response object"}
                        return result
            finally:
                if not connector.closed:
                    await connector.close()

        except (aiohttp.ClientConnectorError, aiohttp.ClientConnectionError, aiohttp.ServerTimeoutError, asyncio.TimeoutError) as exc:
            logger.warning("External API connection attempt %s failed: %s", attempt, exc)
            if attempt == 1:
                await asyncio.sleep(1)
                continue
            return {"status": "error", "msg": f"API connection failed: {type(exc).__name__}: {exc}"}
        except aiohttp.ClientError as exc:
            logger.exception("External API client error")
            return {"status": "error", "msg": f"API client error: {exc}"}
        except Exception as exc:
            logger.exception("API unexpected error")
            return {"status": "error", "msg": f"API unexpected error: {exc}"}

    return {"status": "error", "msg": "API request failed after retries"}


# ==============================================================================
# WhiteX Mode reseller API (kept alongside Bunty; admin must configure its own token)
# ==============================================================================
def _whitex_base_url() -> str:
    return (get_setting("whitex_api_url", "https://whitexmodz.store/api/v1") or "https://whitexmodz.store/api/v1").strip().rstrip("/")

def _whitex_token() -> str:
    return (get_setting("whitex_api_token", "") or "").strip()

async def whitex_api_call(path: str, method: str = "GET", data: Optional[dict] = None) -> dict:
    token = _whitex_token()
    if not token:
        return {"success": False, "error": "WhiteX Mode API token is not configured. Set it in Admin → WhiteX Mode API."}
    url = _whitex_base_url() + "/" + path.lstrip("/")
    headers = {"X-API-Token": token, "Accept": "application/json"}
    try:
        async with aiohttp.ClientSession() as session:
            if method.upper() == "POST":
                async with session.post(url, headers=headers, data=data or {}, timeout=30) as resp:
                    raw = await resp.text()
                    try: payload = json.loads(raw) if raw else {}
                    except Exception: payload = {"success": False, "error": "Non-JSON reply", "http": resp.status, "preview": raw[:200]}
            else:
                async with session.get(url, headers=headers, params=data or {}, timeout=30) as resp:
                    raw = await resp.text()
                    try: payload = json.loads(raw) if raw else {}
                    except Exception: payload = {"success": False, "error": "Non-JSON reply", "http": resp.status, "preview": raw[:200]}
            if not isinstance(payload, dict): payload = {"success": False, "error": "Invalid JSON object", "http": resp.status}
            payload.setdefault("http", resp.status)
            if resp.status >= 400: payload.setdefault("success", False)
            return payload
    except Exception as exc:
        logger.warning("WhiteX API request failed for %s: %s", path, exc)
        return {"success": False, "error": str(exc)}

@dp.callback_query(F.data == "admin_setup_whitex")
async def admin_setup_whitex(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    token = _whitex_token(); mask = (token[:4] + "••••" + token[-4:]) if len(token) > 8 else ("Configured" if token else "Not set")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Set WhiteX API Token", callback_data="admin_whitex_token")],
        [InlineKeyboardButton(text="Check Balance", callback_data="admin_whitex_balance")],
        [InlineKeyboardButton(text="List Products", callback_data="admin_whitex_products")],
        [InlineKeyboardButton(text="List Reset APIs", callback_data="admin_whitex_resets")],
        [InlineKeyboardButton(text="Back", callback_data="admin_panel_back")]
    ], _width=1)
    await call.message.edit_text(f"<b>WhiteX Mode API</b>\nBase URL: <code>{html.escape(_whitex_base_url())}</code>\nToken: <code>{html.escape(mask)}</code>\n\nUses X-API-Token header. Configure your own active token; never paste it into public chat.", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_whitex_token")
async def admin_whitex_token(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_whitex_token)
    await call.message.edit_text("Send WhiteX Mode API token privately. Send /cancel to stop.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await call.answer()

@dp.message(AdminStates.wait_for_whitex_token)
async def save_whitex_token(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    if (message.text or "").strip() == "/cancel":
        await state.clear(); return await message.answer("Cancelled.", reply_markup=admin_kb())
    token = (message.text or "").strip()
    if len(token) < 8: return await message.answer("Token looks too short. Try again or send /cancel.")
    set_setting("whitex_api_token", token)
    await state.clear()
    await message.answer("✅ WhiteX Mode token saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_whitex_balance")
async def admin_whitex_balance(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    data = await whitex_api_call("balance.php")
    await call.message.answer("<b>WhiteX Balance response</b>\n<pre>" + html.escape(json.dumps(data, ensure_ascii=False)[:3500]) + "</pre>", parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_whitex_products")
async def admin_whitex_products(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    data = await whitex_api_call("products.php")
    await call.message.answer("<b>WhiteX Products response</b>\n<pre>" + html.escape(json.dumps(data, ensure_ascii=False)[:3500]) + "</pre>", parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_whitex_resets")
async def admin_whitex_resets(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    data = await whitex_api_call("reset_apis.php")
    await call.message.answer("<b>WhiteX Reset APIs response</b>\n<pre>" + html.escape(json.dumps(data, ensure_ascii=False)[:3500]) + "</pre>", parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_setup_external_api")
async def admin_setup_external_api(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id):
        return
    url = get_setting("external_api_url", "")
    key = get_setting("external_api_key", "")
    master = get_setting("external_master_key", "")
    mask = lambda x: (x[:4] + "••••" + x[-4:]) if len(x) > 8 else ("Configured" if x else "Not set")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Set API URL", callback_data="admin_set_ext_url", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Set API Key", callback_data="admin_set_ext_key", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="Set Master Key", callback_data="admin_set_ext_master", icon_custom_emoji_id=get_emoji_icon("info_icon"))],
        [InlineKeyboardButton(text="💰 Check Bunty Balance", callback_data="admin_check_bunty_balance")],
        [InlineKeyboardButton(text="🩺 API Health Check", callback_data="admin_bunty_health")],
        [InlineKeyboardButton(text="Back", callback_data="admin_panel_back", icon_custom_emoji_id=get_emoji_icon("back"))]
    ])
    text = ("🔗 <b>External Key API Configuration</b>\n\n"
            f"URL: <code>{url or 'Not set'}</code>\n"
            f"API Key: <code>{mask(key)}</code>\n"
            f"Master Key: <code>{mask(master)}</code>\n\n"
            "Products can be switched to API generation from the Add Product flow.")
    await call.message.edit_text(text, reply_markup=kb, parse_mode='HTML')

@dp.callback_query(F.data == "admin_set_ext_url")
async def set_ext_url(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("Enter External API URL:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ext_url)

@dp.message(AdminStates.wait_for_ext_url)
async def save_ext_url(m: Message, state: FSMContext):
    value = m.text.strip()
    if not value.startswith(("http://", "https://")):
        return await m.answer("❌ URL must start with http:// or https://")
    set_setting("external_api_url", value)
    await m.answer("✅ External API URL saved.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_ext_key")
async def set_ext_key(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("Enter External API Key:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ext_key)

@dp.message(AdminStates.wait_for_ext_key)
async def save_ext_key(m: Message, state: FSMContext):
    set_setting("external_api_key", m.text.strip())
    await m.answer("✅ External API Key saved.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

@dp.callback_query(F.data == "admin_set_ext_master")
async def set_ext_master(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("Enter External API Master Key:", reply_markup=admin_back_kb(), parse_mode='HTML')
    await state.set_state(AdminStates.wait_for_ext_master)

@dp.message(AdminStates.wait_for_ext_master)
async def save_ext_master(m: Message, state: FSMContext):
    set_setting("external_master_key", m.text.strip())
    await m.answer("✅ External API Master Key saved.", reply_markup=admin_kb(), parse_mode='HTML')
    await state.clear()

# ==============================================================================
# OWNER CONTROLS: dynamic admins, welcome text, Top Users, share-contact button
# ==============================================================================
OWNER_ID = 8620035649

@dp.callback_query(F.data == "owner_manage_admins")
async def owner_manage_admins(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != OWNER_ID:
        return await call.answer("Only the bot owner can manage admins.", show_alert=True)
    ids = get_setting("dynamic_admin_ids", "")
    await call.message.edit_text("👥 <b>Manage Admins</b>\nCurrent extra admin IDs: <code>" + html.escape(ids or "None") + "</code>\n\nSend a Telegram numeric user ID to add it as admin, or send <code>-ID</code> to remove it.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.wait_for_dynamic_admin)

@dp.message(AdminStates.wait_for_dynamic_admin)
async def owner_manage_admins_save(m: Message, state: FSMContext):
    if m.from_user.id != OWNER_ID: return
    raw=(m.text or "").strip()
    try: target=int(raw.lstrip("-"))
    except ValueError: return await m.answer("❌ Send a numeric Telegram user ID, or -ID to remove.")
    if target == OWNER_ID: return await m.answer("Owner ID cannot be removed from owner access.")
    ids={int(x) for x in (get_setting("dynamic_admin_ids", "") or "").split(",") if x.strip().isdigit()}
    if raw.startswith("-"): ids.discard(target); action="removed"
    else: ids.add(target); action="added"
    set_setting("dynamic_admin_ids", ",".join(map(str, sorted(ids))))
    await state.clear(); await m.answer(f"✅ Admin {target} {action}.", reply_markup=admin_kb())

@dp.callback_query(F.data == "owner_toggle_top_users")
async def owner_toggle_top_users(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    value="OFF" if get_setting("top_users_enabled", "ON").upper()=="ON" else "ON"
    set_setting("top_users_enabled", value)
    await call.answer(f"Top Users: {value}", show_alert=True)
    try: await call.message.edit_reply_markup(reply_markup=admin_kb())
    except Exception: pass

@dp.callback_query(F.data == "owner_toggle_share_contact")
async def owner_toggle_share_contact(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    value="OFF" if get_setting("share_contact_enabled", "ON").upper()=="ON" else "ON"
    set_setting("share_contact_enabled", value)
    await call.answer(f"Share Contact: {value}", show_alert=True)

@dp.callback_query(F.data == "owner_edit_welcome")
async def owner_edit_welcome(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("📝 <b>WELCOME TXT EDITOR</b>\nSend the full welcome message. Use Telegram HTML tags: <code>&lt;b&gt;</code>, <code>&lt;i&gt;</code>, <code>&lt;u&gt;</code>, <code>&lt;code&gt;</code>, <code>&lt;pre&gt;</code>, <code>&lt;s&gt;</code>, <code>&lt;tg-spoiler&gt;</code>, <code>&lt;blockquote&gt;</code>, and <code>&lt;a href=\"https://t.me/...\"&gt;</code>. Emojis/custom emoji are supported.\n\nExample: <code>🔥 &lt;b&gt;WELCOME&lt;/b&gt;\n&lt;tg-spoiler&gt;Secret offer&lt;/tg-spoiler&gt;</code>\nSend <code>-</code> to restore the default. Keep tags balanced; Telegram rejects malformed HTML.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.wait_for_welcome_text)

@dp.message(AdminStates.wait_for_welcome_text)
async def owner_edit_welcome_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    # Preserve Premium Telegram custom emoji pasted into the welcome text.
    # Telegram entity offsets are UTF-16 code units, so map them safely to Python indexes.
    if m.entities and value != "-":
        def _utf16_index_to_py(s: str, offset: int) -> int:
            units = 0
            for idx, ch in enumerate(s):
                if units >= offset:
                    return idx
                units += len(ch.encode("utf-16-le")) // 2
            return len(s)
        premium_entities = [
            ent for ent in m.entities
            if getattr(ent, "type", None) == "custom_emoji" and getattr(ent, "custom_emoji_id", None)
        ]
        for ent in sorted(premium_entities, key=lambda e: e.offset, reverse=True):
            start = _utf16_index_to_py(value, ent.offset)
            end = _utf16_index_to_py(value, ent.offset + ent.length)
            original = value[start:end]
            value = value[:start] + f'<tg-emoji emoji-id="{ent.custom_emoji_id}">{html.escape(original)}</tg-emoji>' + value[end:]
    if value == "-": value = UI_TEXTS["start_menu"]
    # Validate HTML before saving to prevent malformed welcome messages breaking /start.
    try:
        from html.parser import HTMLParser
        class _CheckHTML(HTMLParser):
            ALLOWED = {"b", "strong", "i", "em", "u", "ins", "s", "strike", "del", "code", "pre", "a", "tg-spoiler", "blockquote", "tg-emoji"}
            def __init__(self):
                super().__init__(convert_charrefs=True)
                self.stack = []
            def handle_starttag(self, tag, attrs):
                if tag not in self.ALLOWED:
                    raise ValueError(f"Unsupported Telegram HTML tag: {tag}")
                if tag == "a" and not any(k == "href" and v for k, v in attrs):
                    raise ValueError("Links need an href attribute")
                if tag == "tg-emoji" and not any(k == "emoji-id" and v for k, v in attrs):
                    raise ValueError("Custom emoji needs emoji-id")
                self.stack.append(tag)
            def handle_endtag(self, tag):
                if not self.stack or self.stack[-1] != tag:
                    raise ValueError(f"Mismatched closing tag: {tag}")
                self.stack.pop()
        _parser = _CheckHTML()
        _parser.feed(value)
        _parser.close()
        if _parser.stack:
            raise ValueError("Some HTML tags were not closed")
    except Exception as exc:
        return await m.answer(f"❌ Invalid Telegram HTML: {html.escape(str(exc))}. Please send the message again.")
    set_setting("ui_start_menu", value)
    await state.clear(); await m.answer("✅ Welcome message saved.", reply_markup=admin_kb())


# ==============================================================================
# V31: Product description/video editing and License Manager API configuration
# ==============================================================================
@dp.callback_query(F.data.startswith("edit_p_") & F.data.endswith("_description"))
async def edit_product_description_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    try: pid = int(call.data[len("edit_p_"):-len("_description")])
    except ValueError: return await call.answer("Invalid product ID", show_alert=True)
    row = db_query("SELECT description FROM products WHERE id=?", (pid,), fetchone=True)
    if not row: return await call.answer("Product not found", show_alert=True)
    await state.update_data(edit_product_id=pid)
    await call.message.edit_text("📝 Send the new product description. HTML formatting and emojis are supported. Send '-' to clear it.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.wait_for_product_description)

@dp.message(AdminStates.wait_for_product_description)
async def edit_product_description_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    data = await state.get_data(); pid = int(data.get("edit_product_id", 0))
    value = "" if (m.text or "").strip() == "-" else (m.text or m.caption or "")
    db_query("UPDATE products SET description=? WHERE id=?", (value, pid))
    await state.clear()
    await m.answer("✅ Product description saved.", reply_markup=admin_kb())

@dp.callback_query(F.data.startswith("edit_p_") & F.data.endswith("_video"))
async def edit_product_video_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    try: pid = int(call.data[len("edit_p_"):-len("_video")])
    except ValueError: return await call.answer("Invalid product ID", show_alert=True)
    await state.update_data(edit_product_id=pid)
    await call.message.edit_text("🎬 Send the product video (video/file) to attach or replace it. Send '-' to remove the video.", reply_markup=admin_back_kb(), parse_mode="HTML")
    await state.set_state(AdminStates.wait_for_product_video)

@dp.message(AdminStates.wait_for_product_video)
async def edit_product_video_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    data = await state.get_data(); pid = int(data.get("edit_product_id", 0))
    if (m.text or "").strip() == "-":
        file_id = ""
    elif m.video:
        file_id = m.video.file_id
    elif m.document and (m.document.mime_type or "").startswith("video/"):
        file_id = m.document.file_id
    else:
        return await m.answer("❌ Please send a video or video file, or '-' to remove it.")
    db_query("UPDATE products SET video_file_id=? WHERE id=?", (file_id, pid))
    await state.clear()
    await m.answer("✅ Product video updated.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_license_manager")
async def admin_license_manager_menu(call: CallbackQuery):
    logger.info("License Manager menu callback received: user_id=%s data=%s", call.from_user.id, call.data)
    # Always acknowledge the callback so Telegram does not leave the button spinning.
    try:
        if not is_admin(call.from_user.id):
            await call.answer("Admin access denied. Check ADMIN_ID / ADMIN_IDS on hosting.", show_alert=True)
            return
        await call.answer()
        url = get_setting("license_manager_api_url", "https://licencedashboard.shop/api/v1/generate.php")
        key = get_setting("license_manager_api_key", "")
        pid = get_setting("license_manager_default_product_id", "62")
        health_url = get_setting("license_manager_health_url", "")
        balance_url = get_setting("license_manager_balance_url", "")
        masked = (key[:3] + "••••" + key[-3:]) if len(key) > 8 else ("Configured" if key else "Not set")
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="Set Generate API URL", callback_data="license_set_url")],
            [InlineKeyboardButton(text="Set Bearer API Key", callback_data="license_set_key")],
            [InlineKeyboardButton(text="Set Default Product ID", callback_data="license_set_pid")],
            [InlineKeyboardButton(text="Set Health URL", callback_data="license_set_health_url")],
            [InlineKeyboardButton(text="Set Balance URL", callback_data="license_set_balance_url")],
            [InlineKeyboardButton(text="🩺 Test Health / Connection", callback_data="license_test_health")],
            [InlineKeyboardButton(text="💰 Check API Balance", callback_data="license_test_balance")],
            [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back")]])
        body = (f"🔑 <b>License Manager API</b>\nGenerate URL: <code>{html.escape(url)}</code>"
                f"\nHealth URL: <code>{html.escape(health_url or 'Not set')}</code>"
                f"\nBalance URL: <code>{html.escape(balance_url or 'Not set')}</code>"
                f"\nBearer key: <code>{html.escape(masked)}</code>"
                f"\nDefault product_id: <code>{html.escape(pid)}</code>"
                "\n\nSet the provider endpoints and credential below. Health/Balance must use provider-documented endpoints.")
        try:
            await safe_edit_text(call.message, body, reply_markup=kb, parse_mode="HTML")
        except Exception as edit_exc:
            logger.exception("Could not edit License Manager settings message")
            await call.message.answer(body, reply_markup=kb, parse_mode="HTML")
    except Exception as exc:
        logger.exception("License Manager admin menu callback failed")
        # The callback may already have been acknowledged; keep the failure in logs.
        try:
            await safe_edit_text(call.message, f"❌ License Manager menu error: {html.escape(type(exc).__name__ + ': ' + str(exc)[:180])}", reply_markup=admin_back_kb(), parse_mode="HTML")
        except Exception:
            pass

@dp.callback_query(F.data == "license_set_url")
async def license_set_url_start(call: CallbackQuery, state: FSMContext):
    logger.info("License Manager configuration action requested: %s user_id=%s", call.data, call.from_user.id)
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the full License Manager GENERATE API URL (https://...).", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_license_api_url)

@dp.message(AdminStates.wait_for_license_api_url)
async def license_set_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if not value.startswith(("https://", "http://")): return await m.answer("❌ URL must start with https:// or http://")
    set_setting("license_manager_api_url", value)
    await state.clear(); await m.answer("✅ License Manager generate URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "license_set_health_url")
async def license_set_health_url_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the provider's HEALTH/STATUS endpoint URL. Send '-' to clear it.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_license_health_url)

@dp.message(AdminStates.wait_for_license_health_url)
async def license_set_health_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if value != "-" and not value.startswith(("https://", "http://")): return await m.answer("❌ URL must start with https:// or http://, or send '-'.")
    set_setting("license_manager_health_url", "" if value == "-" else value)
    await state.clear(); await m.answer("✅ License Manager health URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "license_set_balance_url")
async def license_set_balance_url_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the provider's BALANCE endpoint URL. Send '-' to clear it.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_license_balance_url)

@dp.message(AdminStates.wait_for_license_balance_url)
async def license_set_balance_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if value != "-" and not value.startswith(("https://", "http://")): return await m.answer("❌ URL must start with https:// or http://, or send '-'.")
    set_setting("license_manager_balance_url", "" if value == "-" else value)
    await state.clear(); await m.answer("✅ License Manager balance URL saved.", reply_markup=admin_kb())

async def _safe_api_probe(call: CallbackQuery, provider: str, kind: str):
    logger.info("API probe requested: provider=%s kind=%s user_id=%s", provider, kind, call.from_user.id)
    if not is_admin(call.from_user.id):
        logger.warning("API probe denied: provider=%s user_id=%s configured_admin_ids=%s", provider, call.from_user.id, sorted(ADMIN_IDS))
        return await call.answer("Admin access denied. Check ADMIN_ID on hosting.", show_alert=True)
    prefix = "license_manager" if provider == "license_manager" else "hk_tamim"
    label = "License Manager" if provider == "license_manager" else "HK Tamim"
    endpoint = get_setting(f"{prefix}_{kind}_url", "").strip()
    token = get_setting(f"{prefix}_api_key" if provider == "license_manager" else f"{prefix}_api_token", "").strip()
    if not endpoint:
        return await call.answer(f"Set the {kind.upper()} endpoint URL first.", show_alert=True)
    if not token:
        return await call.answer(f"{label} API credential is not configured.", show_alert=True)
    await call.answer(f"Checking {label} {kind} endpoint…")
    headers = {"Accept": "application/json", "Authorization": f"Bearer {token}"} if provider == "license_manager" else {"Accept": "application/json", "X-API-Token": token}
    started = time.perf_counter()
    try:
        timeout = aiohttp.ClientTimeout(total=15, connect=5)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get(endpoint, headers=headers, allow_redirects=True) as resp:
                raw = await resp.text()
                elapsed = round((time.perf_counter() - started) * 1000)
                try: payload = json.loads(raw) if raw.strip() else None
                except json.JSONDecodeError: payload = None
                good = 200 <= resp.status < 300
                if isinstance(payload, dict):
                    if payload.get("ok") is False or payload.get("success") is False or str(payload.get("status", "")).lower() in {"error", "failed", "failure"}: good = False
                details = payload if payload is not None else raw
                preview = html.escape(json.dumps(details, ensure_ascii=False)[:1400] if isinstance(details, (dict, list)) else str(details)[:1400])
                result_title = "SUCCESS" if good else "FAILED"
                message = f"{'✅' if good else '❌'} <b>{html.escape(label)} {kind.upper()} {result_title}</b>\n\nHTTP: <code>{resp.status}</code>\nLatency: <code>{elapsed} ms</code>\nEndpoint: <code>{html.escape(endpoint)}</code>\nResponse:\n<code>{preview or '(empty response)'}</code>\n\nNote: HTTP reachability is not proof that key-generation purchases work."
    except Exception as exc:
        message = f"❌ <b>{html.escape(label)} {kind.upper()} FAILED</b>\n\nEndpoint: <code>{html.escape(endpoint)}</code>\nError: <code>{html.escape(type(exc).__name__ + ': ' + str(exc))[:1000]}</code>"
    kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="Back to API Settings", callback_data="admin_license_manager" if provider == "license_manager" else "admin_hk_tamim")]])
    await safe_edit_text(call.message, message, reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "license_test_health")
async def license_test_health(call: CallbackQuery):
    await _safe_api_probe(call, "license_manager", "health")

@dp.callback_query(F.data == "license_test_balance")
async def license_test_balance(call: CallbackQuery):
    await _safe_api_probe(call, "license_manager", "balance")

@dp.callback_query(F.data == "license_set_key")
async def license_set_key_start(call: CallbackQuery, state: FSMContext):
    logger.info("License Manager configuration action requested: %s user_id=%s", call.data, call.from_user.id)
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send License Manager Bearer token (kept private in settings):", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_license_api_key)

@dp.message(AdminStates.wait_for_license_api_key)
async def license_set_key_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    set_setting("license_manager_api_key", (m.text or "").strip())
    await state.clear(); await m.answer("✅ License Manager API key saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "license_set_pid")
async def license_set_pid_start(call: CallbackQuery, state: FSMContext):
    logger.info("License Manager configuration action requested: %s user_id=%s", call.data, call.from_user.id)
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the default License Manager product_id (example: 62):", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_license_product_id)

@dp.message(AdminStates.wait_for_license_product_id)
async def license_set_pid_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value = (m.text or "").strip()
    if not value.isdigit(): return await m.answer("❌ Product ID must be numeric.")
    set_setting("license_manager_default_product_id", value)
    await state.clear(); await m.answer("✅ Default License Manager product ID saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_dripclient")
async def admin_dripclient_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    await call.answer()
    token = (get_setting("dripclient_api_token", "") or "").strip()
    masked = (token[:3] + "••••" + token[-3:]) if len(token) > 8 else ("Configured" if token else "Not set")
    base = get_setting("dripclient_api_url", "https://dripclientofficial.shop/api/v1")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Set API Base URL", callback_data="dripclient_set_url")],
        [InlineKeyboardButton(text="Set X-API-Token", callback_data="dripclient_set_token")],
        [InlineKeyboardButton(text="⬅️ Back to Admin", callback_data="admin_panel_back")]])
    await safe_edit_text(call.message,
        f"💧 <b>Drip Client API</b>\nBase URL: <code>{html.escape(base)}</code>\nToken: <code>{html.escape(masked)}</code>\n\nUses X-API-Token and POST /generate_key.php. Set token here; do not paste it into public chats.",
        reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "dripclient_set_url")
async def dripclient_set_url_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.answer()
    await safe_edit_text(call.message, "Send Drip Client API base URL (e.g. https://dripclientofficial.shop/api/v1).", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_dripclient_url)

@dp.callback_query(F.data == "dripclient_set_token")
async def dripclient_set_token_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.answer()
    await safe_edit_text(call.message, "Send the Drip Client X-API-Token privately in this admin chat.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_dripclient_token)

@dp.message(AdminStates.wait_for_dripclient_token)
async def dripclient_set_token_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value = (m.text or "").strip()
    if len(value) < 16: return await m.answer("❌ Token looks too short; please check it.")
    set_setting("dripclient_api_token", value)
    await state.clear()
    await m.answer("✅ Drip Client token saved. For safety, delete the token message from this chat if possible.", reply_markup=admin_kb())

@dp.message(AdminStates.wait_for_dripclient_url)
async def dripclient_set_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if not value.startswith("https://"): return await m.answer("❌ Please send an https:// URL.")
    set_setting("dripclient_api_url", value.rstrip("/"))
    await state.clear()
    await m.answer("✅ Drip Client base URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_adminshops")
async def admin_adminshops_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied.", show_alert=True)
    await call.answer()
    token = (get_setting("adminshops_api_token", "") or "").strip()
    masked = (token[:3] + "••••" + token[-3:]) if len(token) > 8 else ("Configured" if token else "Not set")
    base = get_setting("adminshops_api_url", "https://adminshops.com/api/v1")
    pid = get_setting("adminshops_default_product_id", "14")
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="Set Bearer Token", callback_data="adminshops_set_token")],
        [InlineKeyboardButton(text="Set Base URL", callback_data="adminshops_set_url")],
        [InlineKeyboardButton(text="Set Default Product ID", callback_data="adminshops_set_pid")],
        [InlineKeyboardButton(text="⬅️ Back to Admin", callback_data="admin_panel_back")]])
    await safe_edit_text(call.message,
        f"🛍️ <b>Admin Shops API</b>\nBase URL: <code>{html.escape(base)}</code>\nToken: <code>{html.escape(masked)}</code>\nDefault product_id: <code>{html.escape(pid)}</code>\n\nUses Authorization: Bearer TOKEN and POST /generate. Catalog IDs come from /catalog.",
        reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "adminshops_set_token")
async def adminshops_set_token_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.answer()
    await safe_edit_text(call.message, "Send the Admin Shops Bearer token privately in this admin chat.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_adminshops_token)

@dp.message(AdminStates.wait_for_adminshops_token)
async def adminshops_set_token_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if len(value) < 16: return await m.answer("❌ Token looks too short; please check it.")
    set_setting("adminshops_api_token", value)
    await state.clear()
    await m.answer("✅ Admin Shops token saved. For safety, delete the token message from this chat if possible.", reply_markup=admin_kb())

@dp.callback_query(F.data == "adminshops_set_url")
async def adminshops_set_url_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.answer()
    await safe_edit_text(call.message, "Send Admin Shops base URL (default https://adminshops.com/api/v1).", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_adminshops_url)

@dp.message(AdminStates.wait_for_adminshops_url)
async def adminshops_set_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if not value.startswith("https://"): return await m.answer("❌ Please send an https:// URL.")
    set_setting("adminshops_api_url", value.rstrip("/"))
    await state.clear()
    await m.answer("✅ Admin Shops base URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "adminshops_set_pid")
async def adminshops_set_pid_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.answer()
    await safe_edit_text(call.message, "Send the default numeric Admin Shops product_id.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_adminshops_product_id)

@dp.message(AdminStates.wait_for_adminshops_product_id)
async def adminshops_set_pid_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if not value.isdigit(): return await m.answer("❌ product_id must be numeric.")
    set_setting("adminshops_default_product_id", value)
    await state.clear()
    await m.answer("✅ Admin Shops default product_id saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_hk_tamim")
async def admin_hk_tamim_menu(call: CallbackQuery):
    logger.info("HK Tamim menu callback received: user_id=%s data=%s", call.from_user.id, call.data)
    try:
        if not is_admin(call.from_user.id):
            await call.answer("Admin access denied. Check ADMIN_ID / ADMIN_IDS on hosting.", show_alert=True)
            return
        await call.answer()
        token = get_setting("hk_tamim_api_token", "")
        masked = (token[:3] + "••••" + token[-3:]) if len(token) > 8 else ("Configured" if token else "Not set")
        url = get_setting("hk_tamim_api_url", "https://hkmodz.shop/api/v1/generate_key.php")
        variant = get_setting("hk_tamim_default_variant_id", "50")
        health_url = get_setting("hk_tamim_health_url", "")
        balance_url = get_setting("hk_tamim_balance_url", "")
        kb = make_inline_kb(inline_keyboard=[
            [InlineKeyboardButton(text="Set Generate API URL", callback_data="hk_tamim_set_url")],
            [InlineKeyboardButton(text="Set X-API-Token", callback_data="hk_tamim_set_token")],
            [InlineKeyboardButton(text="Set Default Variant ID", callback_data="hk_tamim_set_variant")],
            [InlineKeyboardButton(text="Set Health URL", callback_data="hk_tamim_set_health_url")],
            [InlineKeyboardButton(text="Set Balance URL", callback_data="hk_tamim_set_balance_url")],
            [InlineKeyboardButton(text="🩺 Test Health / Connection", callback_data="hk_tamim_test_health")],
            [InlineKeyboardButton(text="💰 Check API Balance", callback_data="hk_tamim_test_balance")],
            [InlineKeyboardButton(text="Back to Admin", callback_data="admin_panel_back")]])
        body = (f"🗝️ <b>HK Tamim API</b>\nGenerate URL: <code>{html.escape(url)}</code>"
                f"\nHealth URL: <code>{html.escape(health_url or 'Not set')}</code>"
                f"\nBalance URL: <code>{html.escape(balance_url or 'Not set')}</code>"
                f"\nToken: <code>{html.escape(masked)}</code>"
                f"\nDefault variant_id: <code>{html.escape(variant)}</code>"
                "\n\nSet the provider endpoints and credential below. Health/Balance must use provider-documented endpoints.")
        try:
            await safe_edit_text(call.message, body, reply_markup=kb, parse_mode="HTML")
        except Exception:
            logger.exception("Could not edit HK Tamim settings message")
            await call.message.answer(body, reply_markup=kb, parse_mode="HTML")
    except Exception as exc:
        logger.exception("HK Tamim admin menu callback failed")
        # The callback may already have been acknowledged; keep the failure in logs.
        try:
            await safe_edit_text(call.message, f"❌ HK Tamim menu error: {html.escape(type(exc).__name__ + ': ' + str(exc)[:180])}", reply_markup=admin_back_kb(), parse_mode="HTML")
        except Exception:
            pass

@dp.callback_query(F.data == "hk_tamim_set_url")
async def hk_tamim_set_url_start(call: CallbackQuery, state: FSMContext):
    logger.info("HK Tamim configuration action requested: %s user_id=%s", call.data, call.from_user.id)
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the full HK Tamim GENERATE API URL (https://...).", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_hk_tamim_api_url)

@dp.message(AdminStates.wait_for_hk_tamim_api_url)
async def hk_tamim_set_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if not value.startswith(("https://", "http://")): return await m.answer("❌ URL must start with https:// or http://")
    set_setting("hk_tamim_api_url", value)
    await state.clear(); await m.answer("✅ HK Tamim generate URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "hk_tamim_set_health_url")
async def hk_tamim_set_health_url_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the provider's HEALTH/STATUS endpoint URL. Send '-' to clear it.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_hk_tamim_health_url)

@dp.message(AdminStates.wait_for_hk_tamim_health_url)
async def hk_tamim_set_health_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if value != "-" and not value.startswith(("https://", "http://")): return await m.answer("❌ URL must start with https:// or http://, or send '-'.")
    set_setting("hk_tamim_health_url", "" if value == "-" else value)
    await state.clear(); await m.answer("✅ HK Tamim health URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "hk_tamim_set_balance_url")
async def hk_tamim_set_balance_url_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the provider's BALANCE endpoint URL. Send '-' to clear it.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_hk_tamim_balance_url)

@dp.message(AdminStates.wait_for_hk_tamim_balance_url)
async def hk_tamim_set_balance_url_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if value != "-" and not value.startswith(("https://", "http://")): return await m.answer("❌ URL must start with https:// or http://, or send '-'.")
    set_setting("hk_tamim_balance_url", "" if value == "-" else value)
    await state.clear(); await m.answer("✅ HK Tamim balance URL saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "hk_tamim_test_health")
async def hk_tamim_test_health(call: CallbackQuery):
    await _safe_api_probe(call, "hk_tamim", "health")

@dp.callback_query(F.data == "hk_tamim_test_balance")
async def hk_tamim_test_balance(call: CallbackQuery):
    await _safe_api_probe(call, "hk_tamim", "balance")

@dp.callback_query(F.data == "hk_tamim_set_token")
async def hk_tamim_set_token_start(call: CallbackQuery, state: FSMContext):
    logger.info("HK Tamim configuration action requested: %s user_id=%s", call.data, call.from_user.id)
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send HK Tamim X-API-Token. It will be stored in bot settings.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_hk_tamim_token)

@dp.message(AdminStates.wait_for_hk_tamim_token)
async def hk_tamim_set_token_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    set_setting("hk_tamim_api_token", (m.text or "").strip())
    await state.clear(); await m.answer("✅ HK Tamim token saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "hk_tamim_set_variant")
async def hk_tamim_set_variant_start(call: CallbackQuery, state: FSMContext):
    logger.info("HK Tamim configuration action requested: %s user_id=%s", call.data, call.from_user.id)
    if not is_admin(call.from_user.id): return
    await safe_edit_text(call.message, "Send the default HK Tamim variant_id (numeric).", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_hk_tamim_variant)

@dp.message(AdminStates.wait_for_hk_tamim_variant)
async def hk_tamim_set_variant_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value=(m.text or "").strip()
    if not value.isdigit(): return await m.answer("❌ variant_id must be numeric.")
    set_setting("hk_tamim_default_variant_id", value)
    await state.clear(); await m.answer("✅ HK Tamim default variant ID saved.", reply_markup=admin_kb())

# Payment Guru controls removed from the admin UI in V41.

@dp.callback_query(F.data == "admin_set_main_channel")
async def admin_set_main_channel_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("📢 Send the Main Channel link (https://t.me/yourchannel or @channel). Send '-' to hide the button.", reply_markup=admin_back_kb())
    await state.set_state(AdminStates.wait_for_main_channel)

@dp.message(AdminStates.wait_for_main_channel)
async def admin_set_main_channel_save(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    value = (m.text or "").strip()
    if value == "-": value = ""
    if value and not value.startswith(("@", "https://t.me/", "http://", "https://")):
        return await m.answer("❌ Send @channel or a valid URL.")
    set_setting("main_channel_link", value)
    await state.clear(); await m.answer("✅ Main Channel link saved.", reply_markup=admin_kb())


# ==============================================================================
# FF GLORY PRO (ffglory.pro) - separate Guild Glory service
# ==============================================================================
async def ffglorypro_api(method: str, path: str, payload: Optional[dict] = None, public: bool = False) -> dict:
    base = "https://ffglory.pro"
    api_key = (get_setting("ffglorypro_api_key", "") or "").strip()
    master = (get_setting("ffglorypro_master_key", "") or "").strip()
    headers = {"Accept": "application/json"}
    params = {}
    if not public:
        if not api_key or not master:
            return {"success": False, "error": "FF Glory Pro API key/master key are not configured by admin."}
        headers["x-api-key"] = master
        params["api_key"] = api_key
    # Guild creation waits for the provider's real response. Do not impose an
    # application-level read/total timeout on this POST; the live Telegram timer
    # below keeps the user informed while the request is pending.
    is_guild_launch = method.upper() == "POST" and path == "/api/client/auto-clan-group"
    if is_guild_launch:
        # FFGlory can take 90-120s to start a group; allow 210s overall and
        # 180s without a response body before reconciliation starts.
        timeout = aiohttp.ClientTimeout(total=210, connect=25, sock_connect=25, sock_read=180)
    else:
        timeout = aiohttp.ClientTimeout(total=90, connect=15, sock_connect=15, sock_read=60)
    try:
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.request(method.upper(), base + path, headers=headers, params=params,
                                       json=payload if method.upper() != "GET" else None) as resp:
                raw = await resp.text()
                try: data = json.loads(raw)
                except Exception: data = {"success": False, "error": f"Non-JSON response (HTTP {resp.status}): {raw[:250]}"}
                # The provider returns JSON arrays for list endpoints such as /my-groups.
                # Normalize these into a dict instead of misreporting them as API errors.
                if isinstance(data, list):
                    key = "groups" if path == "/api/client/my-groups" else "data"
                    return {"success": resp.status < 400, key: data, "_http_status": resp.status}
                if isinstance(data, dict):
                    data.setdefault("_http_status", resp.status)
                    if resp.status >= 400:
                        data.setdefault("success", False)
                    # A server-side error may happen after the provider created the group.
                    if method.upper() == "POST" and path == "/api/client/auto-clan-group" and resp.status >= 500:
                        data["_ambiguous"] = True
                    return data
                return {"success": False, "error": "Unexpected API response", "_http_status": resp.status}
    except asyncio.TimeoutError:
        return {"success": False, "_ambiguous": True, "_timeout": True, "error": "Provider response timed out after submission; order status must be verified in provider history."}
    except Exception as exc:
        logger.warning("FF Glory Pro API request failed (%s %s): %s", method.upper(), path, exc)
        # A dropped connection during launch does not prove the provider rejected it.
        ambiguous = method.upper() == "POST" and path == "/api/client/auto-clan-group"
        return {"success": False, "_ambiguous": ambiguous, "error": "Provider connection ended before a confirmed response." if ambiguous else "Could not connect to FF Glory Pro API."}

async def _ffglorypro_submit_with_live_timer(message: Message, region_id: str, clan_id: str) -> dict:
    """Submit once and update the existing Telegram message with elapsed seconds
    until the provider returns a real HTTP/API response or the connection errors.
    """
    started = time.monotonic()
    stop = asyncio.Event()

    async def ticker():
        last_displayed = -1
        while not stop.is_set():
            elapsed = int(time.monotonic() - started)
            if elapsed != last_displayed:
                try:
                    await message.edit_text(
                        "⏳ Submitting Guild Glory order…\n"
                        f"⏱️ Waiting for provider response: {elapsed}s\n"
                        "Please keep this message open and do not submit again."
                    )
                except Exception:
                    # Telegram may occasionally reject a rapid edit; keep waiting
                    # for the provider rather than aborting the order request.
                    pass
                last_displayed = elapsed
            try:
                await asyncio.wait_for(stop.wait(), timeout=1.0)
            except asyncio.TimeoutError:
                pass

    timer_task = asyncio.create_task(ticker())
    try:
        return await ffglorypro_api(
            "POST", "/api/client/auto-clan-group",
            {"region": region_id, "clan_id": clan_id}
        )
    finally:
        stop.set()
        timer_task.cancel()
        await asyncio.gather(timer_task, return_exceptions=True)


async def _ffglorypro_find_recent_group(clan_id: str, region_id: str, submitted_at: datetime) -> Optional[dict]:
    """Reconcile a delayed launch by polling provider-owned groups for up to ~60s.

    Never retries the launch POST: it may already have consumed provider credits.
    A recent timestamp is required to avoid mistaking an older group for this order.
    """
    for attempt in range(9):
        result = await ffglorypro_api("GET", "/api/client/my-groups")
        groups = result.get("groups", []) if isinstance(result, dict) else []
        if isinstance(groups, dict):
            groups = groups.get("groups", [])
        if isinstance(groups, list):
            candidates = []
            for group in groups:
                if not isinstance(group, dict):
                    continue
                if str(group.get("clan_id", "")).strip() != str(clan_id).strip():
                    continue
                if str(group.get("region", "")).strip().lower() != str(region_id).strip().lower():
                    continue
                raw_created = str(group.get("created_at") or group.get("launched_at") or "").strip()
                if not raw_created:
                    continue
                try:
                    created = datetime.fromisoformat(raw_created.replace("Z", "+00:00"))
                    submitted = submitted_at
                    if created.tzinfo is None:
                        created = created.replace(tzinfo=__import__("datetime").timezone.utc)
                    if submitted.tzinfo is None:
                        submitted = submitted.replace(tzinfo=__import__("datetime").timezone.utc)
                    age = (created - submitted).total_seconds()
                    if -120 <= age <= 900:
                        candidates.append((abs(age), group))
                except (ValueError, TypeError):
                    continue
            if candidates:
                candidates.sort(key=lambda item: item[0])
                return candidates[0][1]
        if attempt < 8:
            await asyncio.sleep(7)
    return None


def _save_ffglorypro_order(user_id: int, group_id: str, clan_id: str, region_id: str,
                           region_name: str, amount: float, payment_method: str, status: str) -> None:
    """Persist ownership so users can only inspect/manage their own groups."""
    try:
        db_query("""INSERT INTO ffglorypro_orders
            (user_id, group_id, clan_id, region_id, region_name, amount, payment_method, status, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(group_id) DO UPDATE SET status=excluded.status""",
            (int(user_id), str(group_id), str(clan_id), str(region_id), str(region_name),
             float(amount or 0), str(payment_method or ""), str(status or "unknown"),
             datetime.now().astimezone().isoformat()))
    except Exception:
        logger.exception("Could not persist Guild Glory order ownership for group %s", group_id)



def _glorypro_err(data: dict) -> str:
    err = data.get("error", "Unknown API error")
    if isinstance(err, dict): return str(err.get("message") or err.get("code") or "Unknown API error")
    return str(err)

@dp.callback_query(F.data == "admin_toggle_product_store")
async def admin_toggle_product_store(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    current = (get_setting("product_store_enabled", "ON") or "ON").upper()
    new_value = "OFF" if current == "ON" else "ON"
    set_setting("product_store_enabled", new_value)
    await call.answer(f"Product Store {new_value}")
    await call.message.edit_reply_markup(reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ffglorypro_menu")
async def admin_ffglorypro_menu(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    on = (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() == "ON"
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text=f"Guild Glory: {'🟢 ON' if on else '🔴 OFF'}", callback_data="admin_ffglorypro_toggle")],
        [InlineKeyboardButton(text="🔐 Set API + Master Key", callback_data="admin_ffglorypro_credentials")],
        [InlineKeyboardButton(text="💰 Set Sale Price by Region", callback_data="admin_ffglorypro_price")],
        [InlineKeyboardButton(text="🌍 Manage Regions / Emojis / Prices", callback_data="admin_ffglorypro_regions")],
        [InlineKeyboardButton(text="📝 Set User Notice", callback_data="admin_ffglorypro_notice")],
        [InlineKeyboardButton(text="✏️ Edit Menu Name / Emoji", callback_data="admin_ffglorypro_label")],
        [InlineKeyboardButton(text="📊 Check Account / Pricing", callback_data="admin_ffglorypro_check")],
        [InlineKeyboardButton(text="💳 Provider Credits", callback_data="ffglorypro_balance")],
        [InlineKeyboardButton(text="🎟 Manage Provider Coupons", callback_data="ffglorypro_coupons")],
        [InlineKeyboardButton(text="💸 Provider Transactions", callback_data="ffglorypro_transactions")],
        [InlineKeyboardButton(text="🧾 Activity / Notifications", callback_data="admin_ffglorypro_activity_menu")],
        [InlineKeyboardButton(text="❓ Setup Guide / Troubleshooting", callback_data="admin_ffglorypro_help")],
        [InlineKeyboardButton(text="⬅️ Admin Panel", callback_data="admin_panel_back")]])
    await call.message.edit_text("🏆 <b>FF Glory Pro (ffglory.pro)</b>\n\n<b>Quick setup:</b> 1) Set both credentials 2) Check Account/Pricing 3) Configure only provider-supported region IDs 4) Set sale price 5) Turn ON.\nSeparate from FF Like. Uses the documented x-api-key master header and account api_key query parameter.\nAPI credentials: " + ("configured" if get_setting("ffglorypro_api_key", "") and get_setting("ffglorypro_master_key", "") else "not configured"), reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_ffglorypro_activity_menu")
async def admin_ffglorypro_activity_menu(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🧾 Activity Log", callback_data="ffglorypro_activity")],
        [InlineKeyboardButton(text="🔔 Notifications (read once)", callback_data="ffglorypro_notifications")],
        [InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ffglorypro_menu")]])
    await call.message.edit_text("Provider account activity and notifications (admin only):", reply_markup=kb)
    await call.answer()

@dp.callback_query(F.data == "admin_ffglorypro_help")
async def admin_ffglorypro_help(call: CallbackQuery):
    if not is_admin(call.from_user.id):
        return await call.answer("Admin access denied", show_alert=True)
    text = (
        "❓ <b>FF Glory Pro Setup Guide</b>\n\n"
        "<b>1.</b> Set Account API Key and Master Key in this menu.\n"
        "<b>2.</b> Press Check Account / Pricing. If this fails, copy the HTTP/API error and verify credentials in the provider dashboard.\n"
        "<b>3.</b> Manage Regions and use the exact region IDs supplied by the provider; the display name is not necessarily the ID.\n"
        "<b>4.</b> Set your sale price, verify the user notice, then enable the menu.\n\n"
        "If provider returns API_ERROR or a timeout, don't repeat a paid order until the provider's order history confirms whether it was created. Never paste keys into public chat."
    )
    await call.message.edit_text(text, reply_markup=back_kb("admin_ffglorypro_menu"), parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_ffglorypro_toggle")
async def admin_ffglorypro_toggle(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    set_setting("ffglorypro_enabled", "OFF" if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() == "ON" else "ON")
    await admin_ffglorypro_menu(call, None)

@dp.callback_query(F.data == "admin_ffglorypro_credentials")
async def admin_ffglorypro_credentials(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_glorypro_credentials)
    await call.message.answer("Send the two rotated credentials in one message as: <code>ACCOUNT_API_KEY | MASTER_KEY</code>. They are saved privately in bot settings; do not send them in a public group.", parse_mode="HTML")
    await call.answer()

@dp.message(AdminStates.wait_for_glorypro_credentials)
async def admin_ffglorypro_credentials_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    parts = [x.strip() for x in (message.text or "").split("|", 1)]
    if len(parts) != 2 or len(parts[0]) < 20 or len(parts[1]) < 12:
        return await message.answer("Invalid format. Send: ACCOUNT_API_KEY | MASTER_KEY")
    set_setting("ffglorypro_api_key", parts[0]); set_setting("ffglorypro_master_key", parts[1])
    await state.clear(); await message.answer("✅ FF Glory Pro credentials saved. For security, rotate the credentials pasted into the chat/docs and only use the new values here.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ffglorypro_regions")
async def admin_ffglorypro_regions(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    regions = _load_region_settings("ffglorypro_regions_json", [])
    listing = "\n".join(f"• {'🟢' if r.get('enabled', True) else '🔴'} {r.get('emoji','🌍')} {r.get('name','?')} — id=<code>{html.escape(str(r.get('id','')))}</code> — ₹{float(r.get('price',0) or 0):g}" for r in regions if isinstance(r, dict)) or "(none)"
    kb = make_inline_kb(inline_keyboard=[[InlineKeyboardButton(text="➕ Add / Update Region", callback_data="admin_ffglorypro_regions_edit")], [InlineKeyboardButton(text="⬅️ Back", callback_data="admin_ffglorypro_menu")]])
    await call.message.edit_text("🌍 <b>FF Glory Pro Regions</b>\n"+listing+"\n\nFormat: <code>ADD | provider_id | Name | Emoji | sale_price</code>\nExample: <code>ADD | me | Middle East | 🌍 | 99</code>\nAlso use <code>OFF | provider_id</code> or <code>ON | provider_id</code>. Remove: <code>REMOVE | provider_id</code>. Provider ID must match an enabled ID from /api/pricing.", reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "admin_ffglorypro_regions_edit")
async def admin_ffglorypro_regions_edit(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_glory_region_config)
    await call.message.answer("Send ADD | provider_id | Name | Emoji | sale_price, or REMOVE | provider_id. Example: ADD | me | Middle East | 🌍 | 99")
    await call.answer()

@dp.message(AdminStates.wait_for_glory_region_config)
async def admin_ffglorypro_regions_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    parts = [x.strip() for x in (message.text or "").split("|")]
    regions = _load_region_settings("ffglorypro_regions_json", [])
    if len(parts) == 2 and parts[0].upper() == "REMOVE":
        rid = parts[1].lower()
        regions = [r for r in regions if str(r.get("id", "")).lower() != rid]
        set_setting("ffglorypro_regions_json", json.dumps(regions, ensure_ascii=False))
        await state.clear(); return await message.answer(f"✅ Removed Glory region {rid} (if it existed).", reply_markup=admin_kb())
    if len(parts) == 2 and parts[0].upper() in ("ON", "OFF"):
        rid = parts[1].lower(); found = False
        for r in regions:
            if str(r.get("id", "")).lower() == rid: r["enabled"] = parts[0].upper() == "ON"; found = True
        if not found: return await message.answer("Region not found. Add it first.")
        set_setting("ffglorypro_regions_json", json.dumps(regions, ensure_ascii=False))
        await state.clear(); return await message.answer(f"✅ Glory region {rid} set {parts[0].upper()}.", reply_markup=admin_kb())
    if len(parts) != 5 or parts[0].upper() != "ADD" or not parts[1] or not parts[2]:
        return await message.answer("Invalid format. Use ADD | provider_id | Name | Emoji | sale_price or REMOVE | provider_id")
    rid, name, emoji = parts[1], parts[2][:40], parts[3] or "🌍"
    try: price = float(parts[4])
    except ValueError: return await message.answer("Sale price must be numeric.")
    if price < 0 or price > 1000000: return await message.answer("Sale price must be between 0 and 1000000.")
    regions = [r for r in regions if str(r.get("id", "")).lower() != rid.lower()]
    regions.append({"id":rid,"name":name,"emoji":emoji,"price":price,"enabled":True})
    set_setting("ffglorypro_regions_json", json.dumps(regions, ensure_ascii=False))
    await state.clear(); await message.answer(f"✅ Saved Glory region {emoji} {name} ({rid}) at ₹{price:g}. Provider must return this enabled region from /api/pricing.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ffglorypro_price")
async def admin_ffglorypro_price(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_glorypro_price)
    await call.message.answer("Send region and your customer sale price: <code>India | 99</code> or <code>Bangladesh | 150</code>. Supported labels: India, Bangladesh, Nepal, Sri Lanka.", parse_mode="HTML")
    await call.answer()

@dp.message(AdminStates.wait_for_glorypro_price)
async def admin_ffglorypro_price_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    parts = [x.strip() for x in (message.text or "").split("|", 1)]
    names = {"india":"india", "ind":"india", "bangladesh":"bangladesh", "bd":"bangladesh", "nepal":"nepal", "np":"nepal", "sri lanka":"srilanka", "srilanka":"srilanka", "lk":"srilanka"}
    if len(parts) != 2 or names.get(parts[0].lower()) is None:
        return await message.answer("Format invalid. Example: India | 99")
    try: price = float(parts[1])
    except ValueError: return await message.answer("Price must be a number.")
    if price < 0 or price > 1000000: return await message.answer("Price must be between 0 and 1000000.")
    set_setting("ffglorypro_price_" + names[parts[0].lower()], str(price))
    await state.clear(); await message.answer(f"✅ {parts[0]} sale price saved: ₹{price:g}", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ffglorypro_label")
async def admin_ffglorypro_label(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_glorypro_label)
    await call.message.answer("Send menu label and emoji separated by |. Example: Guild Glory | 🏆")
    await call.answer()

@dp.message(AdminStates.wait_for_glorypro_label)
async def admin_ffglorypro_label_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    parts = [x.strip() for x in (message.text or "").split("|", 1)]
    if len(parts) != 2 or not parts[0] or len(parts[0]) > 40 or not parts[1] or len(parts[1]) > 16:
        return await message.answer("Invalid format. Use Label | Emoji (max 40 label characters).")
    set_setting("ffglorypro_label", parts[0]); set_setting("ffglorypro_emoji", parts[1])
    await state.clear(); await message.answer("✅ FF Glory menu label and emoji saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ffglorypro_notice")
async def admin_ffglorypro_notice(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(AdminStates.wait_for_glorypro_notice)
    await call.message.answer("Send the notice shown to users before they launch a Guild Glory order. Telegram formatting such as bold/code/spoiler can be preserved when sent as a Telegram message. Send - to clear.")
    await call.answer()

@dp.message(AdminStates.wait_for_glorypro_notice)
async def admin_ffglorypro_notice_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    val = (message.html_text or message.text or "").strip()
    set_setting("ffglorypro_notice", "" if val == "-" else val[:3500])
    await state.clear(); await message.answer("✅ Guild Glory notice saved.", reply_markup=admin_kb())

@dp.callback_query(F.data == "admin_ffglorypro_check")
async def admin_ffglorypro_check(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await call.answer("Checking account, credits and regions…")
    me = await ffglorypro_api("GET", "/api/auth/me")
    pricing = await ffglorypro_api("GET", "/api/pricing", public=True)
    text = "🏆 <b>FF Glory Pro API Check</b>\n"
    if me.get("_http_status") == 200 and not me.get("error"):
        text += f"Account: <code>{html.escape(str(me.get('username','-')))}</code>\nBasic credits: <b>{html.escape(str(me.get('basic_credits','-')))}</b>\nPremium credits: <b>{html.escape(str(me.get('premium_credits','-')))}</b>\nMax groups: {html.escape(str(me.get('max_groups','-')))}\n"
    else: text += "Account: ❌ " + html.escape(_glorypro_err(me)) + "\n"
    regions = pricing.get("regions", []) if isinstance(pricing.get("regions"), list) else []
    text += "\nAvailable provider regions:\n" + ("\n".join(f"• {html.escape(str(r.get('region_name',r.get('id','?'))))} — {html.escape(str(r.get('id','?')))} ({html.escape(str(r.get('tier','?')))}; {'enabled' if r.get('enabled') else 'disabled'})" for r in regions[:20]) if regions else html.escape(_glorypro_err(pricing)))
    await call.message.edit_text(text, reply_markup=back_kb("admin_ffglorypro_menu"), parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_menu")
async def ffglorypro_menu(call: CallbackQuery):
    if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() != "ON": return await call.answer("Guild Glory is currently unavailable.", show_alert=True)
    notice = get_setting("ffglorypro_notice", "") or ""
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="🚀 Launch Guild Glory", callback_data="ffglorypro_launch")],
        [InlineKeyboardButton(text="📋 My Groups / Status", callback_data="ffglorypro_groups")],
        [InlineKeyboardButton(text="🗂 My Group History", callback_data="ffglorypro_history")],
        [InlineKeyboardButton(text="📈 My Glory Progression", callback_data="ffglorypro_progress_prompt")],
        [InlineKeyboardButton(text="⬅️ Back", callback_data="back_main")]])
    txt = f"{html.escape(get_setting('ffglorypro_emoji','🏆'))} <b>{html.escape(get_setting('ffglorypro_label','Guild Glory'))}</b>\n\n{notice}"
    await call.message.edit_text(txt, reply_markup=kb, parse_mode="HTML")
    await call.answer()

@dp.callback_query(F.data == "ffglorypro_launch")
async def ffglorypro_launch_start(call: CallbackQuery, state: FSMContext):
    if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() != "ON": return await call.answer("Service is OFF", show_alert=True)
    await state.set_state(UserStates.ffglorypro_clan_id)
    await call.message.answer("Send your numeric Free Fire Guild/Clan ID (digits only).")
    await call.answer()

@dp.message(UserStates.ffglorypro_clan_id)
async def ffglorypro_clan_received(message: Message, state: FSMContext):
    clan = (message.text or "").strip()
    if not clan.isdigit() or not (5 <= len(clan) <= 24): return await message.answer("❌ Clan ID must contain 5–24 digits. Send it again.")
    pricing = await ffglorypro_api("GET", "/api/pricing", public=True)
    regions = pricing.get("regions", []) if isinstance(pricing.get("regions"), list) else []
    configured = _load_region_settings("ffglorypro_regions_json", [])
    provider_by_id = {str(r.get("id", "")).lower(): r for r in regions if isinstance(r, dict) and r.get("enabled", True)}
    buttons=[]
    for idx, cfg in enumerate(configured):
        if not isinstance(cfg, dict) or not cfg.get("enabled", True): continue
        rid = str(cfg.get("id", "")).strip()
        if rid.lower() not in provider_by_id: continue
        price=float(cfg.get("price", 0) or 0)
        if price <= 0: continue
        label=f"{cfg.get('emoji','🌍')} {cfg.get('name', provider_by_id[rid.lower()].get('region_name',rid))}"
        buttons.append([InlineKeyboardButton(text=f"{label} — ₹{price:g}"[:64], callback_data=f"ffglorypro_regioncfg_{idx}")])
    if not buttons:
        await state.clear()
        return await message.answer("⚠️ Provider pricing currently does not return any enabled configured region among India, Bangladesh, Nepal or Sri Lanka, or admin sale prices are not set. Ask admin to check API pricing and set sale prices.")
    await state.update_data(glorypro_clan_id=clan)
    buttons.append([InlineKeyboardButton(text="❌ Cancel", callback_data="ffglorypro_cancel")])
    await message.answer("Select the region. Only enabled regions returned by the provider are shown:", reply_markup=make_inline_kb(inline_keyboard=buttons, _width=1))

@dp.callback_query(F.data.startswith("ffglorypro_regioncfg_"))
async def ffglorypro_region_select_configured(call: CallbackQuery, state: FSMContext):
    if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() != "ON": return await call.answer("Service is OFF", show_alert=True)
    try: idx = int(call.data.rsplit("_", 1)[1])
    except ValueError: return await call.answer("Invalid region", show_alert=True)
    configured = _load_region_settings("ffglorypro_regions_json", [])
    if idx < 0 or idx >= len(configured): return await call.answer("Region config changed; start again.", show_alert=True)
    cfg = configured[idx]
    if not isinstance(cfg, dict) or not cfg.get("enabled", True): return await call.answer("Region unavailable", show_alert=True)
    rid = str(cfg.get("id", "")).strip(); price = float(cfg.get("price", 0) or 0)
    data = await state.get_data(); clan = str(data.get("glorypro_clan_id", ""))
    if not clan: return await call.answer("Session expired. Start again.", show_alert=True)
    if not rid or price <= 0: return await call.answer("Region ID or sale price is invalid", show_alert=True)
    provider_pricing = await ffglorypro_api("GET", "/api/pricing", public=True)
    provider_regions = provider_pricing.get("regions", []) if isinstance(provider_pricing.get("regions"), list) else []
    valid = any(isinstance(r, dict) and str(r.get("id", "")).lower() == rid.lower() and r.get("enabled", True) for r in provider_regions)
    if not valid: return await call.answer("Provider does not list this region as enabled.", show_alert=True)
    await state.update_data(glorypro_region_id=rid, glorypro_region_name=str(cfg.get("name",rid)), glorypro_price=price)
    rows = [[InlineKeyboardButton(text=f"👛 Pay from Wallet — ₹{price:g}", callback_data="ffglorypro_pay_wallet")]]
    if gateway_enabled("zapupi") and (db_query("SELECT value FROM settings WHERE key='zapupi_api'",fetchone=True) or ("",))[0]:
        rows.append([InlineKeyboardButton(text="⚡ Pay with ZapUPI",callback_data="ffglorypro_pay_zapupi")])
    if gateway_enabled("famgateway") and _famgateway_api_key():
        rows.append([InlineKeyboardButton(text="💜 Pay with FamGateway",callback_data="ffglorypro_pay_famgateway")])
    rows.append([InlineKeyboardButton(text="❌ Cancel",callback_data="ffglorypro_cancel")])
    await call.message.answer(f"🏆 <b>Guild Glory Checkout</b>\nClan ID: <code>{html.escape(clan)}</code>\nRegion: {html.escape(str(cfg.get('name',rid)))}\nAmount: <b>₹{price:g}</b>\n\nChoose wallet or UPI gateway. Gateway checkout uses the provider's payment page; no separate QR is generated by this bot.",reply_markup=make_inline_kb(inline_keyboard=rows),parse_mode="HTML")
    await call.answer("Choose payment method")
    return
    user = db_query("SELECT balance FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not user: return await call.answer("Send /start first", show_alert=True)
    if float(user[0] or 0) < price: return await call.answer("Insufficient wallet balance. Add balance first.", show_alert=True)
    old_balance = float(user[0] or 0)
    db_query("UPDATE users SET balance=balance-? WHERE user_id=? AND balance>=?", (price, call.from_user.id, price))
    check = db_query("SELECT balance FROM users WHERE user_id=?", (call.from_user.id,), fetchone=True)
    if not check or abs(float(check[0] or 0) - (old_balance-price)) > 0.02:
        return await call.answer("Wallet debit could not be confirmed; no order sent.", show_alert=True)
    await call.answer("Submitting order…")
    await call.message.edit_text("⏳ Submitting Guild Glory order…\n⏱️ Waiting for provider response: 0s")
    submitted_at = datetime.now().astimezone()
    result = await _ffglorypro_submit_with_live_timer(call.message, rid, clan)
    if result.get("_ambiguous") or result.get("_timeout"):
        matched = await _ffglorypro_find_recent_group(clan, rid, submitted_at)
        if matched and matched.get("group_id"):
            result = {"success": True, "group_id": matched.get("group_id"), "status": matched.get("status", "running"), "_reconciled": True}
    if result.get("success") is True and result.get("group_id"):
        gid = str(result.get("group_id")); status = str(result.get("status", "running"))
        note = f"{html.escape(str(cfg.get('emoji','🌍')))} <b>Guild Glory Order Submitted</b>\nOrder: <code>{html.escape(gid)}</code>\nClan ID: <code>{html.escape(clan)}</code>\nRegion: {html.escape(str(cfg.get('name',rid)))} (<code>{html.escape(rid)}</code>)\nStatus: <b>{html.escape(status)}</b>\nCharged: ₹{price:g}"
        await call.message.edit_text(note, parse_mode="HTML")
        for aid in getattr(ADMIN_ID, "all_ids", {int(ADMIN_ID)}):
            try: await bot.send_message(int(aid), "📣 <b>Guild Glory order</b>\nUser: <code>"+str(call.from_user.id)+"</code>\n"+note, parse_mode="HTML")
            except Exception: logger.exception("FF Glory Pro admin notification failed")
        await state.clear()
    else:
        code = int(result.get("_http_status") or 0)
        # Only refund when the provider has clearly rejected the request. A timeout or
        # connection drop can happen after the provider has already created the group.
        definite_rejection = code in (400, 402, 403, 404, 409, 422) and not result.get("_ambiguous")
        if definite_rejection:
            db_query("UPDATE users SET balance=balance+? WHERE user_id=?", (price, call.from_user.id))
            note = f"❌ <b>Guild Glory order rejected</b>\n{html.escape(_glorypro_err(result))}\n💰 Wallet refunded because provider rejected the request."
        else:
            note = ("⏳ <b>Guild Glory order is being checked</b>\n"
                    "Provider response was delayed, so the order may already have been submitted. "
                    "Your balance is on hold while the owner checks provider history. <b>Please do not submit again.</b>")
        await call.message.edit_text(note, parse_mode="HTML")
        for aid in getattr(ADMIN_ID, "all_ids", {int(ADMIN_ID)}):
            try:
                admin_note = ("📣 <b>Guild Glory needs status check</b>\nUser: <code>" + str(call.from_user.id) + "</code>\n"
                              + html.escape(_glorypro_err(result)) + "\nCheck provider order history before retrying or refunding.")
                await bot.send_message(int(aid), admin_note, parse_mode="HTML")
            except Exception: pass

async def _ffglorypro_gateway_checkout(call: CallbackQuery, state: FSMContext, gateway: str):
    data = await state.get_data()
    clan = str(data.get("glorypro_clan_id", "")); rid = str(data.get("glorypro_region_id", ""))
    name = str(data.get("glorypro_region_name", rid)); price = float(data.get("glorypro_price", 0) or 0)
    if not clan or not rid or price <= 0: return await call.answer("Session expired. Start Guild Glory again.", show_alert=True)
    desc = json.dumps({"clan":clan,"region_id":rid,"region_name":name},ensure_ascii=False,separators=(",",":"))
    await call.answer()
    try:
        await call.message.answer(f"⏳ Creating {gateway.upper()} payment for Guild Glory — ₹{price:g}…")
        if gateway == "famgateway": await create_famgateway_payment(call.from_user.id,price,call.message,purpose="ffglory_purchase",description=desc)
        else: await generate_zapupi_order(call.from_user.id,price,call.message,purpose="ffglory_purchase",description=desc)
    except Exception:
        logger.exception("FF Glory gateway checkout failed")
        await call.message.answer("❌ Could not create UPI payment. Please try again later.")

@dp.callback_query(F.data == "ffglorypro_pay_zapupi")
async def ffglorypro_pay_zapupi(call: CallbackQuery, state: FSMContext):
    await _ffglorypro_gateway_checkout(call,state,"zapupi")

@dp.callback_query(F.data == "ffglorypro_pay_famgateway")
async def ffglorypro_pay_famgateway(call: CallbackQuery, state: FSMContext):
    await _ffglorypro_gateway_checkout(call,state,"famgateway")

@dp.callback_query(F.data == "ffglorypro_pay_wallet")
async def ffglorypro_pay_wallet(call: CallbackQuery, state: FSMContext):
    if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() != "ON": return await call.answer("Service is OFF",show_alert=True)
    data=await state.get_data(); clan=str(data.get("glorypro_clan_id", "")); rid=str(data.get("glorypro_region_id", "")); name=str(data.get("glorypro_region_name",rid)); price=float(data.get("glorypro_price",0) or 0)
    if not clan or not rid or price<=0: return await call.answer("Session expired. Start again.",show_alert=True)
    conn=sqlite3.connect(DB_PATH,timeout=30.0)
    try:
        conn.execute("BEGIN IMMEDIATE")
        row=conn.execute("SELECT balance FROM users WHERE user_id=?",(call.from_user.id,)).fetchone()
        if not row or float(row[0] or 0)<price:
            conn.rollback(); return await call.answer("Insufficient wallet balance. Choose UPI or add balance.",show_alert=True)
        cur=conn.execute("UPDATE users SET balance=balance-? WHERE user_id=? AND balance>=?",(price,call.from_user.id,price))
        if cur.rowcount != 1: conn.rollback(); return await call.answer("Wallet balance changed. Try again.",show_alert=True)
        conn.commit()
    finally: conn.close()
    await call.answer("Submitting order…")
    await call.message.edit_text("⏳ Submitting Guild Glory order…\n⏱️ Waiting for provider response: 0s")
    submitted_at=datetime.now().astimezone()
    result=await _ffglorypro_submit_with_live_timer(call.message,rid,clan)
    if result.get("_ambiguous") or result.get("_timeout"):
        matched=await _ffglorypro_find_recent_group(clan,rid,submitted_at)
        if matched and matched.get("group_id"): result={"success":True,"group_id":matched.get("group_id"),"status":matched.get("status","running"),"_reconciled":True}
    if result.get("success") is True and result.get("group_id"):
        gid=str(result.get("group_id")); status=str(result.get("status","running"))
        _save_ffglorypro_order(call.from_user.id, gid, clan, rid, name, price, "wallet", status)
        try: await send_payment_proof_channel(call.from_user.id, f"Guild Glory ({name})", price, gid)
        except Exception: logger.exception("Guild Glory payment proof failed")
        await call.message.edit_text(f"🎉 <b>Guild Glory Order Submitted</b>\nOrder: <code>{html.escape(gid)}</code>\nClan ID: <code>{html.escape(clan)}</code>\nRegion: {html.escape(name)}\nStatus: <b>{html.escape(status)}</b>\nCharged: ₹{price:g}",parse_mode="HTML")
        await state.clear(); return
    code=int(result.get("_http_status") or 0)
    if code in (400,402,403,404,409,422) and not result.get("_ambiguous"):
        db_query("UPDATE users SET balance=balance+? WHERE user_id=?",(price,call.from_user.id))
        await call.message.edit_text(f"❌ Provider rejected order. ₹{price:g} refunded to wallet.\n{html.escape(_glorypro_err(result))}",parse_mode="HTML")
    else:
        await call.message.edit_text("⏳ Provider response unclear. Wallet amount is on hold while admin checks order history. Do not retry yet.",parse_mode="HTML")
        await notify_admins(f"⚠️ FF Glory wallet order needs status check. User: {call.from_user.id}; clan: {clan}; region: {rid}; amount: ₹{price:g}. Check provider history before refund/retry.")

@dp.callback_query(F.data.startswith("ffglorypro_region_"))
async def ffglorypro_region_select(call: CallbackQuery, state: FSMContext):
    if (get_setting("ffglorypro_enabled", "OFF") or "OFF").upper() != "ON": return await call.answer("Service is OFF", show_alert=True)
    try:
        raw = call.data[len("ffglorypro_region_"):]
        price_key, region_id = raw.split("_", 1)
    except Exception: return await call.answer("Invalid region selection", show_alert=True)
    data = await state.get_data(); clan=str(data.get("glorypro_clan_id", ""))
    if not clan: return await call.answer("Session expired. Start again.", show_alert=True)
    # Region IDs are provider IDs (e.g. me/bd), not country names or FF Like region codes.
    price=float(get_setting("ffglorypro_price_"+price_key,"0") or 0)
    if price <= 0: return await call.answer("Admin sale price is not configured", show_alert=True)
    user=db_query("SELECT balance FROM users WHERE user_id=?",(call.from_user.id,),fetchone=True)
    if not user: return await call.answer("Send /start first",show_alert=True)
    if float(user[0] or 0) < price: return await call.answer("Insufficient wallet balance. Add balance first.",show_alert=True)
    # Atomic wallet debit; only submit once after a successful guarded debit.
    old_balance = float(user[0] or 0)
    db_query("UPDATE users SET balance=balance-? WHERE user_id=? AND balance>=?",(price,call.from_user.id,price))
    check=db_query("SELECT balance FROM users WHERE user_id=?",(call.from_user.id,),fetchone=True)
    if not check or abs(float(check[0] or 0) - (old_balance - price)) > 0.02:
        return await call.answer("Wallet debit could not be confirmed. No order was sent; please check balance and try once.",show_alert=True)
    region_id = region_id.strip()
    await call.answer("Submitting order…")
    await call.message.edit_text("⏳ Submitting Guild Glory order…\n⏱️ Waiting for provider response: 0s")
    submitted_at = datetime.now().astimezone()
    result = await _ffglorypro_submit_with_live_timer(call.message, region_id, clan)
    if result.get("_ambiguous") or result.get("_timeout"):
        matched = await _ffglorypro_find_recent_group(clan, region_id, submitted_at)
        if matched and matched.get("group_id"):
            result = {"success": True, "group_id": matched.get("group_id"), "status": matched.get("status", "running"), "_reconciled": True}
    if result.get("success") is True and result.get("group_id"):
        gid=str(result.get("group_id")); status=str(result.get("status","running")); credits=result.get("credits_remaining", "provider response")
        _save_ffglorypro_order(call.from_user.id, gid, clan, region_id, str(cfg.get('name', region_id)), price, "wallet", status)
        try: await send_payment_proof_channel(call.from_user.id, f"Guild Glory ({cfg.get('name', region_id)})", price, gid)
        except Exception: logger.exception("Guild Glory payment proof failed")
        msg=f"🏆 <b>Guild Glory Order Submitted</b>\nOrder: <code>{html.escape(gid)}</code>\nClan ID: <code>{html.escape(clan)}</code>\nRegion: <code>{html.escape(region_id)}</code>\nStatus: <b>{html.escape(status)}</b>\nProvider: {html.escape(str(credits))}\nCharged: ₹{price:g}"
        await call.message.edit_text(msg,parse_mode="HTML")
        for aid in getattr(ADMIN_ID,"all_ids",{int(ADMIN_ID)}):
            try: await bot.send_message(int(aid),"📣 <b>NEW GUILD GLORY ORDER</b>\nUser: <code>"+str(call.from_user.id)+"</code>\n"+msg,parse_mode="HTML")
            except Exception: logger.exception("FF Glory Pro admin notification failed")
        await state.clear()
    else:
        # Never refund on timeout/connection errors: the provider may have accepted the order.
        status_code=int(result.get("_http_status") or 0)
        definite_rejection = status_code in (400, 402, 403, 404, 409, 422) and not result.get("_ambiguous")
        if definite_rejection:
            db_query("UPDATE users SET balance=balance+? WHERE user_id=?",(price,call.from_user.id))
            msg=f"❌ <b>Guild Glory order rejected</b>\n{html.escape(_glorypro_err(result))}\n💰 Wallet refunded because provider rejected the request."
        else:
            msg=("⏳ <b>Guild Glory order is being checked</b>\n"
                 "Provider response was delayed, so the order may already have been submitted. "
                 "Your balance is on hold while the owner checks provider history. <b>Please do not submit again.</b>")
        await call.message.edit_text(msg,parse_mode="HTML")
        for aid in getattr(ADMIN_ID,"all_ids",{int(ADMIN_ID)}):
            try:
                admin_msg=("📣 <b>Guild Glory needs status check</b>\nUser: <code>"+str(call.from_user.id)+"</code>\n"
                           +html.escape(_glorypro_err(result))+"\nCheck provider order history before retrying or refunding.")
                await bot.send_message(int(aid),admin_msg,parse_mode="HTML")
            except Exception: pass

@dp.callback_query(F.data == "ffglorypro_groups")
async def ffglorypro_groups(call: CallbackQuery):
    await call.answer("Loading groups…")
    result=await ffglorypro_api("GET","/api/client/my-groups")
    if result.get("_http_status",200)>=400 or result.get("error"):
        return await call.message.edit_text("❌ Could not load groups: "+html.escape(_glorypro_err(result)),reply_markup=back_kb("ffglorypro_menu"),parse_mode="HTML")
    groups=result if isinstance(result,list) else result.get("groups", result.get("data",[]))
    if isinstance(groups,dict): groups=groups.get("groups",[])
    if not isinstance(groups,list): groups=[]
    owned_rows = db_query("SELECT group_id FROM ffglorypro_orders WHERE user_id=?", (call.from_user.id,), fetchall=True) or []
    owned_ids = {str(row[0]) for row in owned_rows}
    groups = [g for g in groups if isinstance(g, dict) and str(g.get("group_id", "")) in owned_ids]
    lines=["📋 <b>Your Guild Glory Groups</b>", "<i>यहाँ सिर्फ़ आपके अकाउंट से लिंक किए गए ऑर्डर दिखते हैं।</i>"]
    buttons=[]
    for g in groups[:20]:
        gid=str(g.get('group_id',''))
        status=str(g.get('status','unknown')).strip().lower()
        status_icon = "🟢" if status in {"running", "active", "started"} else ("🔴" if status in {"stopped", "failed", "deleted"} else "🟡")
        lines.append(f"\n🏷️ <b>Group</b> <code>{html.escape(gid or '-')}</code>\n🏰 <b>Clan ID:</b> <code>{html.escape(str(g.get('clan_id','-')))}</code>\n🌍 <b>Region:</b> {html.escape(str(g.get('region','-')))}\n{status_icon} <b>Status:</b> {html.escape(str(g.get('status','unknown')))}   ⏱️ <b>Uptime:</b> {html.escape(str(g.get('uptime','-')))}")
        if gid:
            buttons.append([InlineKeyboardButton(text=f"ℹ️ {gid[:12]} — Glory", callback_data=f"ffglorypro_action_get-glory_{gid}"), InlineKeyboardButton(text="🔎 Clan Info", callback_data=f"ffglorypro_action_get-clan-info_{gid}")])
            buttons.append([InlineKeyboardButton(text="🔄 Restart", callback_data=f"ffglorypro_action_restart_{gid}"), InlineKeyboardButton(text="⏸ Stop", callback_data=f"ffglorypro_action_stop_{gid}")])
    if len(groups) == 0: lines.append("\n📭 <b>अभी कोई लिंक किया हुआ ग्रुप नहीं मिला।</b>\nनया ऑर्डर करने के बाद ग्रुप यहाँ दिखाई देगा।")
    buttons.append([InlineKeyboardButton(text="⬅️ Back", callback_data="ffglorypro_menu")])
    await call.message.edit_text("\n".join(lines),reply_markup=make_inline_kb(inline_keyboard=buttons,_width=2),parse_mode="HTML")

@dp.callback_query(F.data.startswith("ffglorypro_action_"))
async def ffglorypro_group_action(call: CallbackQuery):
    raw=call.data[len("ffglorypro_action_"):]
    try: action, gid = raw.split("_", 1)
    except ValueError: return await call.answer("Invalid group action", show_alert=True)
    # callback actions contain hyphens and IDs may contain underscores
    if action not in {"restart", "stop", "delete", "get-glory", "get-clan-info"}:
        return await call.answer("Unsupported action", show_alert=True)
    owned = db_query("SELECT 1 FROM ffglorypro_orders WHERE user_id=? AND group_id=?", (call.from_user.id, gid), fetchone=True)
    if not owned and not is_admin(call.from_user.id):
        return await call.answer("This group is not linked to your account.", show_alert=True)
    if action == "delete":
        return await call.answer("Delete is permanent; use provider dashboard for this action.", show_alert=True)
    await call.answer("Sending action…")
    result=await ffglorypro_api("POST","/api/client/group-action",{"action":action,"group_id":gid})
    if result.get("error") or result.get("success") is False or result.get("_http_status",200)>=400:
        return await call.message.answer("❌ Guild action failed: " + html.escape(_glorypro_err(result)[:500]))
    # Present provider details as a short, readable card rather than a long raw JSON dump.
    def _safe_text(value, limit=180):
        if value is None or value == "":
            return "—"
        if isinstance(value, bool):
            value = "Yes" if value else "No"
        elif isinstance(value, (dict, list)):
            value = json.dumps(value, ensure_ascii=False, separators=(", ", ": "))
        return html.escape(str(value)[:limit])

    def _flatten_provider_payload(payload):
        """Flatten common nested provider response shapes without exposing metadata."""
        if not isinstance(payload, dict):
            return {}
        flat = dict(payload)
        for container_key in ("clan", "clan_info", "data", "result", "info", "details", "glory"):
            nested = flat.get(container_key)
            if isinstance(nested, dict):
                flat = {**nested, **{k: v for k, v in flat.items() if k != container_key}}
        return flat

    try:
        payload = _flatten_provider_payload(result)
        is_clan = action == "get-clan-info"
        if is_clan:
            title = "🏰 <b>Clan Information</b>"
            field_specs = [
                (("clan_name", "name", "guild_name", "title"), "🏷️", "Clan Name"),
                (("clan_id", "guild_id", "id"), "🆔", "Clan ID"),
                (("level", "clan_level", "guild_level"), "⭐", "Level"),
                (("members", "member_count", "members_count", "total_members"), "👥", "Members"),
                (("leader", "leader_name", "owner", "captain"), "👑", "Leader"),
                (("region", "region_name", "server"), "🌍", "Region"),
                (("rank", "clan_rank", "guild_rank"), "🏆", "Rank"),
                (("status", "state"), "📶", "Status"),
            ]
            footer = "💡 <i>यह जानकारी प्रोवाइडर के उपलब्ध डेटा पर निर्भर है। कोई फ़ील्ड न मिले तो वह नहीं दिखेगी।</i>"
        elif action == "get-glory":
            title = "🏆 <b>Guild Glory Status</b>"
            field_specs = [
                (("total_glory", "glory", "glory_points", "current_glory", "points", "glory_farmed"), "✨", "Total Glory"),
                (("clan_name", "name", "guild_name"), "🏷️", "Clan Name"),
                (("clan_id", "guild_id"), "🆔", "Clan ID"),
                (("status", "state"), "📶", "Group Status"),
                (("uptime", "uptime_hours"), "⏱️", "Uptime"),
                (("bot_count", "container_count", "running_count"), "🤖", "Bots"),
            ]
            footer = "💡 <i>Glory के आँकड़े प्रोवाइडर की आख़िरी अपडेट के अनुसार हो सकते हैं।</i>"
        else:
            title = "⚙️ <b>Guild Group Action</b>"
            field_specs = [
                (("success", "status"), "✅", "Result"),
                (("message", "detail", "description"), "📝", "Message"),
                (("group_id",), "🆔", "Group ID"),
                (("clan_id",), "🏰", "Clan ID"),
            ]
            footer = ""

        lines = [title, "", f"🧩 <b>Action:</b> {_safe_text(action.replace('-', ' ').title(), 80)}", f"🆔 <b>Group ID:</b> <code>{_safe_text(gid, 100)}</code>"]
        used = set()
        for keys, emoji, label in field_specs:
            found = next((key for key in keys if key in payload and payload.get(key) not in (None, "")), None)
            if found is None:
                continue
            value = payload[found]
            if isinstance(value, (dict, list)):
                # Avoid dumping large arrays/objects into a single hard-to-read paragraph.
                if isinstance(value, list):
                    value = f"{len(value)} item(s)"
                else:
                    value = ", ".join(f"{str(k).replace('_', ' ').title()}: {str(v)[:60]}" for k, v in list(value.items())[:4])
            lines.append(f"{emoji} <b>{html.escape(label)}:</b> {_safe_text(value, 220)}")
            used.add(found)

        # Keep a small number of additional useful scalar fields if the provider uses a different schema.
        extras = []
        skip = {"success", "error", "message", "detail", "description", "data", "result", "info", "details", "clan", "clan_info", "glory", "snapshots", "history", "accounts", "bots", "containers"}
        for key, value in payload.items():
            if key in used or key in skip or str(key).startswith("_") or isinstance(value, (dict, list)) or value in (None, ""):
                continue
            label = str(key).replace("_", " ").strip().title()
            extras.append(f"• <b>{html.escape(label)}:</b> {_safe_text(value, 100)}")
            if len(extras) >= 4:
                break
        if extras:
            lines.extend(["", "📌 <b>More details</b>", *extras])
        if footer:
            lines.extend(["", footer])
        text_out = "\n".join(lines)
        if len(text_out) > 3700:
            text_out = text_out[:3600] + "\n\n<i>अतिरिक्त विवरण संदेश की सीमा के कारण छाँट दिया गया है।</i>"
        await call.message.answer(text_out, parse_mode="HTML", reply_markup=back_kb("ffglorypro_groups"))
    except Exception:
        logger.exception("Could not render readable Guild Glory provider response")
        await call.message.answer("⚠️ <b>Provider response received</b>\nइस बार जानकारी को कार्ड में दिखाया नहीं जा सका। कृपया थोड़ी देर बाद फिर कोशिश करें।", parse_mode="HTML", reply_markup=back_kb("ffglorypro_groups"))

@dp.callback_query(F.data == "ffglorypro_history")
async def ffglorypro_history(call: CallbackQuery):
    rows = db_query("SELECT group_id, clan_id, region_name, amount, status, created_at FROM ffglorypro_orders WHERE user_id=? ORDER BY id DESC LIMIT 20", (call.from_user.id,), fetchall=True) or []
    if not rows:
        return await call.message.edit_text("🗂 <b>Your Guild Glory History</b>\n\n📭 अभी आपके अकाउंट से लिंक किया गया कोई ऑर्डर नहीं है।\n\n🔐 यह हिस्ट्री सिर्फ़ आपके अपने ऑर्डर दिखाती है।", parse_mode="HTML", reply_markup=back_kb("ffglorypro_menu"))
    lines = ["🗂 <b>Your Guild Glory History</b>", "🔐 <i>यह सूची सिर्फ़ आपके Telegram अकाउंट के ऑर्डर दिखाती है।</i>"]
    for gid, clan, region, amount, status, created in rows:
        st = str(status or "unknown").lower()
        icon = "🟢" if st in {"running", "active", "success", "approved"} else ("🔴" if st in {"failed", "rejected", "deleted"} else "🟡")
        lines.append(f"\n━━━━━━━━━━━━━━\n🆔 <b>Order:</b> <code>{html.escape(str(gid))}</code>\n🏰 <b>Clan ID:</b> <code>{html.escape(str(clan))}</code>\n🌍 <b>Region:</b> {html.escape(str(region))}\n{icon} <b>Status:</b> {html.escape(str(status or 'unknown'))}\n💳 <b>Paid:</b> ₹{float(amount or 0):g}\n🕒 <b>Time:</b> {html.escape(str(created))}")
    await call.message.edit_text("\n".join(lines)[:3900], parse_mode="HTML", reply_markup=back_kb("ffglorypro_menu"))

@dp.callback_query(F.data == "ffglorypro_progress_prompt")
async def ffglorypro_progress_prompt(call: CallbackQuery):
    rows = db_query("SELECT group_id, clan_id FROM ffglorypro_orders WHERE user_id=? ORDER BY id DESC LIMIT 20", (call.from_user.id,), fetchall=True) or []
    if not rows:
        return await call.answer("No Guild Glory orders linked to your account yet.", show_alert=True)
    buttons = [[InlineKeyboardButton(text=f"📈 {str(gid)[:14]} · Clan {str(clan)[:12]}", callback_data=f"ffglorypro_progress_{gid}")] for gid, clan in rows]
    buttons.append([InlineKeyboardButton(text="⬅️ Back", callback_data="ffglorypro_menu")])
    await call.message.edit_text("📈 <b>Your Glory Progression</b>\n\nनीचे सिर्फ़ आपके अपने ग्रुप हैं। किसी ग्रुप को चुनकर Glory का रिकॉर्ड देखें।", parse_mode="HTML", reply_markup=make_inline_kb(inline_keyboard=buttons))

@dp.callback_query(F.data.startswith("ffglorypro_progress_"))
async def ffglorypro_progress(call: CallbackQuery):
    gid = call.data[len("ffglorypro_progress_"):]
    owned = db_query("SELECT 1 FROM ffglorypro_orders WHERE user_id=? AND group_id=?", (call.from_user.id, gid), fetchone=True)
    if not owned and not is_admin(call.from_user.id):
        return await call.answer("This group is not linked to your account.", show_alert=True)
    result = await ffglorypro_api("GET", "/api/client/glory-progression?group_id=" + __import__("urllib.parse").parse.quote(gid, safe=""))
    if result.get("error") or result.get("_http_status", 200) >= 400:
        return await call.message.edit_text("❌ Could not load progression: " + html.escape(_glorypro_err(result)), reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")
    lines = ["📈 <b>Guild Glory Progression</b>", "", f"🆔 <b>Group:</b> <code>{html.escape(gid)}</code>", f"🏰 <b>Clan ID:</b> <code>{html.escape(str(result.get('clan_id','-')))}</code>", f"✨ <b>Total Glory:</b> <b>{html.escape(str(result.get('glory_farmed','-')))}</b>", "", "🕒 <b>Recent snapshots</b>"]
    for snap in (result.get("snapshots", []) or [])[-10:]:
        if isinstance(snap, dict): lines.append(f"• {html.escape(str(snap.get('captured_at','-')))}  →  ✨ {html.escape(str(snap.get('total_glory','-')))}")
    if len(lines) == 7: lines.append("No snapshots have been returned yet.")
    await call.message.edit_text("\n".join(lines)[:3900], parse_mode="HTML", reply_markup=back_kb("ffglorypro_menu"))

@dp.callback_query(F.data == "ffglorypro_activity")
async def ffglorypro_activity(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    result = await ffglorypro_api("GET", "/api/client/activity-log")
    if result.get("error") or result.get("_http_status", 200) >= 400:
        return await call.message.edit_text("❌ " + html.escape(_glorypro_err(result)), reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")
    logs = result if isinstance(result, list) else result.get("logs", result.get("data", []))
    text = "🧾 <b>Provider Activity Log</b>\n" + "\n".join("• " + html.escape(str(x.get("timestamp", ""))) + " — " + html.escape(str(x.get("action", "event"))) + " — " + html.escape(str(x.get("details", ""))) for x in (logs or [])[:25] if isinstance(x, dict))
    await call.message.edit_text(text[:3900], reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_notifications")
async def ffglorypro_notifications(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    result = await ffglorypro_api("GET", "/api/client/notifications")
    if result.get("error") or result.get("_http_status", 200) >= 400:
        return await call.message.edit_text("❌ " + html.escape(_glorypro_err(result)), reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")
    items = result if isinstance(result, list) else result.get("notifications", result.get("data", []))
    text = "🔔 <b>Provider Notifications</b>\n" + "\n".join("• <b>" + html.escape(str(x.get("title", x.get("type", "Notice")))) + "</b>: " + html.escape(str(x.get("message", ""))) for x in (items or [])[:20] if isinstance(x, dict))
    if not items: text += "\nNo pending notifications."
    await call.message.edit_text(text[:3900], reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_coupons")
async def ffglorypro_coupons(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    kb = make_inline_kb(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Create Coupon", callback_data="ffglorypro_coupon_create")],
        [InlineKeyboardButton(text="📋 My Coupons", callback_data="ffglorypro_coupon_list")],
        [InlineKeyboardButton(text="🎁 Redeemed Coupons", callback_data="ffglorypro_coupon_redeemed")],
        [InlineKeyboardButton(text="🎟 Redeem Coupon", callback_data="ffglorypro_coupon_redeem")],
        [InlineKeyboardButton(text="❌ Cancel Active Coupon", callback_data="ffglorypro_coupon_cancel")],
        [InlineKeyboardButton(text="⬅️ Back", callback_data="ffglorypro_menu")]])
    await call.message.edit_text("🎟 <b>FFGlory Coupons</b>\nCreate, list, redeem, or cancel coupons backed by your provider credits.", reply_markup=kb, parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_coupon_create")
async def ffglorypro_coupon_create(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(UserStates.wait_for_glory_coupon_create)
    await call.message.answer("Send basic and premium credits separated by |. Example: 1 | 0 (credits are deducted immediately).")
    await call.answer()

@dp.message(UserStates.wait_for_glory_coupon_create)
async def ffglorypro_coupon_create_submit(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    try:
        parts = [int(x.strip()) for x in (message.text or "").split("|", 1)]
        if len(parts) != 2 or not (0 <= parts[0] <= 100) or not (0 <= parts[1] <= 20) or parts[0] + parts[1] < 1: raise ValueError
    except Exception:
        return await message.answer("Format: basic | premium. Basic 0–100, premium 0–20; at least 1 total.")
    result = await ffglorypro_api("POST", "/api/client/create-coupon", {"basic_credits": parts[0], "premium_credits": parts[1]})
    await state.clear()
    if result.get("error") or result.get("success") is False:
        return await message.answer("❌ Coupon failed: " + html.escape(_glorypro_err(result)))
    coupon = result.get("coupon", {})
    await message.answer("✅ Coupon created: <code>" + html.escape(str(coupon.get("code", "unknown"))) + "</code>\nBasic: " + str(parts[0]) + " | Premium: " + str(parts[1]), parse_mode="HTML", reply_markup=back_kb("ffglorypro_coupons"))

@dp.callback_query(F.data.in_({"ffglorypro_coupon_list", "ffglorypro_coupon_redeemed"}))
async def ffglorypro_coupon_list(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    path = "/api/client/my-coupons" if call.data.endswith("list") else "/api/client/redeemed-coupons"
    result = await ffglorypro_api("GET", path)
    if result.get("error") or result.get("_http_status", 200) >= 400:
        return await call.message.edit_text("❌ " + html.escape(_glorypro_err(result)), reply_markup=back_kb("ffglorypro_coupons"), parse_mode="HTML")
    items = result if isinstance(result, list) else result.get("coupons", result.get("data", []))
    lines = ["🎟 <b>Coupons</b>"]
    for x in (items or [])[:25]:
        if isinstance(x, dict): lines.append(f"• <code>{html.escape(str(x.get('code','-')))}</code> — {html.escape(str(x.get('status','redeemed')))}; basic {html.escape(str(x.get('basic_credits','-')))}, premium {html.escape(str(x.get('premium_credits','-')))}")
    if len(lines) == 1: lines.append("No coupons found.")
    await call.message.edit_text("\n".join(lines)[:3900], reply_markup=back_kb("ffglorypro_coupons"), parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_coupon_redeem")
async def ffglorypro_coupon_redeem_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(UserStates.wait_for_glory_coupon_redeem)
    await call.message.answer("Send coupon code in XXXX-XXXX-XXXX format.")
    await call.answer()

@dp.message(UserStates.wait_for_glory_coupon_redeem)
async def ffglorypro_coupon_redeem_submit(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    code = (message.text or "").strip().upper()
    result = await ffglorypro_api("POST", "/api/client/redeem-coupon", {"code": code})
    await state.clear()
    if result.get("error") or result.get("success") is False:
        return await message.answer("❌ Redeem failed: " + html.escape(_glorypro_err(result)))
    await message.answer("✅ Coupon redeemed. Basic: " + html.escape(str(result.get("basic_credits", "-"))) + "; Premium: " + html.escape(str(result.get("premium_credits", "-"))), reply_markup=back_kb("ffglorypro_coupons"))

@dp.callback_query(F.data == "ffglorypro_transactions")
async def ffglorypro_transactions(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    result = await ffglorypro_api("GET", "/api/client/transactions")
    if result.get("error") or result.get("_http_status", 200) >= 400:
        return await call.message.edit_text("❌ " + html.escape(_glorypro_err(result)), reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")
    items = result.get("data", result.get("transactions", [])) if isinstance(result, dict) else []
    lines = ["💸 <b>Provider Transactions</b>"]
    for item in (items or [])[:30]:
        if isinstance(item, dict):
            lines.append(f"\n• <code>{html.escape(str(item.get('id','-')))}</code>\nOrder: <code>{html.escape(str(item.get('order_id','-')))}</code> | Status: <b>{html.escape(str(item.get('status','-')))}</b>\nBasic: {html.escape(str(item.get('basic_credits','-')))} | Premium: {html.escape(str(item.get('premium_credits','-')))}")
    if len(lines) == 1: lines.append("\nNo transactions returned.")
    await call.message.edit_text("\n".join(lines)[:3900], reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_coupon_cancel")
async def ffglorypro_coupon_cancel_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await state.set_state(UserStates.wait_for_glory_coupon_cancel)
    await call.message.answer("Send the code of an active coupon you created. Credits are refunded only if the provider confirms cancellation.")
    await call.answer()

@dp.message(UserStates.wait_for_glory_coupon_cancel)
async def ffglorypro_coupon_cancel_submit(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    code = (message.text or "").strip().upper()
    result = await ffglorypro_api("POST", "/api/client/cancel-coupon", {"code": code})
    await state.clear()
    if result.get("error") or result.get("success") is False:
        return await message.answer("❌ Coupon cancellation failed: " + html.escape(_glorypro_err(result)))
    await message.answer("✅ Coupon cancelled. Refunded basic: " + html.escape(str(result.get("refunded_basic", "-"))) + "; premium: " + html.escape(str(result.get("refunded_premium", "-"))), reply_markup=back_kb("ffglorypro_coupons"))

@dp.callback_query(F.data == "ffglorypro_balance")
async def ffglorypro_balance(call: CallbackQuery):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied", show_alert=True)
    await call.answer("Checking provider credits…")
    result=await ffglorypro_api("GET","/api/auth/me")
    if result.get("error") or result.get("_http_status",200)>=400:
        return await call.message.edit_text("❌ Provider credit check failed: " + html.escape(_glorypro_err(result)[:500]), reply_markup=back_kb("ffglorypro_menu"), parse_mode="HTML")
    await call.message.edit_text(f"💳 <b>FF Glory Pro Provider Credits</b>\nBasic: <b>{html.escape(str(result.get('basic_credits','-')))}</b>\nPremium: <b>{html.escape(str(result.get('premium_credits','-')))}</b>\nMax groups: {html.escape(str(result.get('max_groups','-')))}",reply_markup=back_kb("ffglorypro_menu"),parse_mode="HTML")

@dp.callback_query(F.data == "ffglorypro_cancel")
async def ffglorypro_cancel(call: CallbackQuery, state: FSMContext):
    await state.clear()
    await call.message.edit_text("Guild Glory request cancelled.",reply_markup=back_kb("back_main"))
    await call.answer()

# ==============================================================================
# PanelStore API setup
# ==============================================================================
@dp.callback_query(F.data == "admin_panelstore_setup")
async def admin_panelstore_setup(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return await call.answer("Admin access denied",show_alert=True)
    await state.set_state(AdminStates.wait_for_panelstore_key)
    await call.message.answer("Send the PanelStore API key from your provider dashboard. The API URL defaults to https://panelstore.shop/api/v1/index.php. Do not paste this key in a public group.")
    await call.answer()

@dp.message(AdminStates.wait_for_panelstore_key)
async def admin_panelstore_key_save(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    key=(message.text or "").strip()
    if len(key)<20: return await message.answer("API key looks too short. Send the key from PanelStore dashboard.")
    set_setting("panelstore_api_key",key)
    await state.clear(); await message.answer("✅ PanelStore API key saved. Add products using provider <code>panelstore</code> and its PID.",parse_mode="HTML",reply_markup=admin_kb())


if __name__ == "__main__":
    if "--dashboard-only" in sys.argv or "--dashboard" in sys.argv or os.getenv("DASHBOARD_ONLY", "").lower() in ("1", "true", "yes"):
        init_db()
        logger.info("🚀 Starting Web Admin Dashboard in Standalone Mode...")
        async def _run_standalone_dashboard():
            runner = await start_web_dashboard()
            while True:
                await asyncio.sleep(3600)
        try:
            asyncio.run(_run_standalone_dashboard())
        except (KeyboardInterrupt, SystemExit):
            logger.info("Dashboard shutdown gracefully. Goodbye.")
        sys.exit(0)

    acquire_single_instance_lock()
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("System shutting down gracefully. Goodbye.")


