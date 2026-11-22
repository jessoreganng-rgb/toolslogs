#!/usr/bin/env python3
"""
LOGSIFT Terminal v2 — Memory-Safe Local Record Manager for Termux
==================================================================
Optimized for large files (100+ MB) on mobile devices.

Key features:
  - Streaming parser (constant memory)
  - SQLite-backed storage (survives RAM pressure)
  - Chunked exports
  - URL/domain validation
  - Safe regex (no catastrophic backtracking)
  - Progress guard for memory

Requirements:
    pip install rich pyfiglet

Run:
    python logsift.py
    python logsift.py "/path/to/file.txt"
"""

import os
import sys
import re
import json
import csv
import time
import sqlite3
import hashlib
import tempfile
import shutil
from pathlib import Path
from datetime import datetime
from contextlib import contextmanager

# ---------- Dependency check ----------
try:
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich.progress import (
        Progress, SpinnerColumn, BarColumn, TextColumn,
        TimeElapsedColumn, TimeRemainingColumn
    )
    from rich.prompt import Prompt, Confirm, IntPrompt
    from rich.align import Align
    from rich.text import Text
    from rich.rule import Rule
    from rich.theme import Theme
    from rich.box import ROUNDED, SIMPLE
except ImportError:
    print("=" * 60)
    print("ERROR: 'rich' library not installed.")
    print("Install with: pip install rich pyfiglet")
    print("=" * 60)
    sys.exit(1)

try:
    import pyfiglet
    HAS_FIGLET = True
except ImportError:
    HAS_FIGLET = False


# ============================================================
# CONFIG
# ============================================================
APP_NAME = "LOGSIFT"
APP_VERSION = "2.0.0"

# Chunk sizes — keep small for mobile memory safety
READ_CHUNK_LINES = 5000
EXPORT_CHUNK = 2000
MAX_DISPLAY_ROWS = 25

# User agent (for any future HTTP use — never used for scraping)
USER_AGENT = (
    "Mozilla/5.0 (Linux; Android 13; Termux) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/120.0.0.0 Mobile Safari/537.36 LOGSIFT/2.0"
)


# ============================================================
# THEME
# ============================================================
custom_theme = Theme({
    "cyan": "#00e0d0",
    "cyan.bold": "bold #00e0d0",
    "blue": "#3b82f6",
    "purple": "#a855f7",
    "green": "#4ade80",
    "yellow": "#fbbf24",
    "red": "#f87171",
    "pink": "#ec4899",
    "orange": "#fb923c",
    "muted": "#6b7c93",
    "label": "bold #6b7c93",
    "value": "#e2e8f0",
    "url": "#00e0d0",
    "login": "#fbbf24",
    "pass": "#ec4899",
})

console = Console(theme=custom_theme, soft_wrap=False)


# ============================================================
# REGEX — bounded, no catastrophic backtracking
# ============================================================
EMAIL_RE = re.compile(r"^[A-Za-z0-9._%+-]{1,64}@[A-Za-z0-9.-]{1,200}\.[A-Za-z]{2,10}$")
# Domain must have a valid TLD, no leading/trailing dots
DOMAIN_RE = re.compile(
    r"^(?:[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?\.)+[A-Za-z]{2,10}$"
)
URL_RE = re.compile(
    r"^(?:https?://)?"
    r"(?:[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?\.)+[A-Za-z]{2,10}"
    r"(?::\d{1,5})?"
    r"(?:/[^\s]{0,500})?$"
)
IP_URL_RE = re.compile(
    r"^(?:https?://)?\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}"
    r"(?::\d{1,5})?"
    r"(?:/[^\s]{0,500})?$"
)
BOT_RE = re.compile(
    r"(?:Subscription\s*bot|t\.me/|CHANNEL|MOONULP)", re.IGNORECASE
)

# Label patterns — bounded quantifiers
URL_LABEL = re.compile(r"^\s*(?:URL|Url|url|🌐|🔗)\s*[:=\-]?\s*(.{1,1000})$")
LOGIN_LABEL = re.compile(
    r"^\s*(?:USERNAME|Username|username|LOGIN|Login|login|USER|User|user|"
    r"EMAIL|Email|email|👤)\s*[:=\-]?\s*(.{1,500})$"
)
PASS_LABEL = re.compile(
    r"^\s*(?:PASSWORD|Password|password|PASS|Pass|pass|🔑|🔒)\s*[:=\-]?\s*(.{1,500})$"
)
SKIP_LABEL = re.compile(r"^\s*(?:COMBO|Combo|combo)\s*[:=\-]?\s*(.{1,2000})$")

# Combo parsers — bounded
URL_COMBO_RE = re.compile(
    r"^(https?://[^\s:]{1,300}|[A-Za-z0-9][A-Za-z0-9.-]{0,250}\.[A-Za-z]{2,10}(?:/[^\s:]{0,300})?)"
    r"\s*:\s*(.{1,500})$"
)
EMAIL_COMBO_RE = re.compile(
    r"^([A-Za-z0-9._%+-]{1,64}@[A-Za-z0-9.-]{1,200}\.[A-Za-z]{2,10})"
    r"\s*:\s*(.{1,500})$"
)

# Safety limits
MAX_LINE_LENGTH = 10000  # skip broken/large lines


# ============================================================
# HELPERS
# ============================================================
def format_bytes(n):
    if n < 1024:
        return f"{n} B"
    for unit in ["KB", "MB", "GB", "TB"]:
        n /= 1024
        if n < 1024:
            return f"{n:.2f} {unit}"
    return f"{n:.2f} PB"


def format_number(n):
    try:
        return f"{n:,}"
    except Exception:
        return str(n)


def is_email(s):
    if not s or len(s) > 320:
        return False
    return bool(EMAIL_RE.match(s))


def is_url_like(s):
    """Accept domain, URL, or IP:port forms. Reject garbage."""
    if not s or len(s) > 1000:
        return False
    s = s.strip()
    if not s:
        return False
    # Must contain at least one dot or be IP
    if "." not in s and not IP_URL_RE.match(s):
        return False
    if IP_URL_RE.match(s):
        return True
    if URL_RE.match(s):
        return True
    return False


def is_bot_line(s):
    return bool(BOT_RE.search(s))


def clean_line(line):
    """Trim + reject oversized garbage."""
    if len(line) > MAX_LINE_LENGTH:
        return None
    return line.strip()


def get_temp_db_path():
    """Get temp path that's writable on Termux."""
    # Try Termux-specific paths first
    candidates = [
        os.environ.get("TMPDIR"),
        "/data/data/com.termux/files/usr/tmp",
        os.path.expanduser("~/.cache"),
        tempfile.gettempdir(),
    ]
    for c in candidates:
        if c and os.path.isdir(c) and os.access(c, os.W_OK):
            return os.path.join(c, f"logsift_{os.getpid()}.db")
    return None


# ============================================================
# DATABASE — SQLite backed, low memory
# ============================================================
class RecordDB:
    """SQLite-backed record storage. Survives memory pressure."""

    def __init__(self, db_path=None):
        self.db_path = db_path or get_temp_db_path()
        if not self.db_path:
            raise RuntimeError("No writable temp directory found")
        self.conn = sqlite3.connect(self.db_path, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode = MEMORY")
        self.conn.execute("PRAGMA synchronous = OFF")
        self.conn.execute("PRAGMA temp_store = MEMORY")
        self._init_schema()

    def _init_schema(self):
        self.conn.executescript("""
            CREATE TABLE IF NOT EXISTS records (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                line_no INTEGER,
                url TEXT,
                login TEXT,
                pass TEXT,
                type TEXT,
                raw TEXT,
                status TEXT,
                error_code TEXT,
                error_reason TEXT,
                dedup_key TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_status ON records(status);
            CREATE INDEX IF NOT EXISTS idx_type ON records(type);
            CREATE INDEX IF NOT EXISTS idx_dedup ON records(dedup_key);
            CREATE INDEX IF NOT EXISTS idx_url ON records(url);
        """)
        self.conn.commit()

    def insert(self, r):
        self.conn.execute(
            "INSERT INTO records (line_no, url, login, pass, type, raw, "
            "status, error_code, error_reason, dedup_key) "
            "VALUES (?,?,?,?,?,?,?,?,?,?)",
            (r["line_no"], r["url"], r["login"], r["pass"], r["type"],
             r["raw"], r["status"], r["error_code"], r["error_reason"],
             r["dedup_key"])
        )

    def commit(self):
        self.conn.commit()

    def execute(self, sql, params=()):
        return self.conn.execute(sql, params)

    def count(self, where="", params=()):
        q = "SELECT COUNT(*) FROM records"
        if where:
            q += " WHERE " + where
        cur = self.conn.execute(q, params)
        return cur.fetchone()[0]

    def close(self):
        try:
            self.conn.close()
        except Exception:
            pass
        try:
            if self.db_path and os.path.exists(self.db_path):
                os.remove(self.db_path)
        except Exception:
            pass


# ============================================================
# STREAMING PARSER — constant memory
# ============================================================
class StreamingParser:
    def __init__(self, path, exclude_bots=True):
        self.path = path
        self.exclude_bots = exclude_bots
        self.current = None
        self.line_count = 0
        self.record_buffer = []
        self.stats = {
            "empty": 0,
            "bot": 0,
            "oversize": 0,
            "labeled": 0,
            "combo": 0,
            "emailpass": 0,
            "urlpass": 0,
            "unrecognized": 0,
        }

    def _new_record(self, line_no):
        return {
            "line_no": line_no,
            "url": "",
            "login": "",
            "pass": "",
            "type": "labeled",
            "raw": "",
            "status": "pending",
            "error_code": None,
            "error_reason": None,
            "dedup_key": "",
        }

    def _flush(self):
        """Push current labeled record into buffer."""
        if self.current and (self.current["url"] or
                             self.current["login"] or
                             self.current["pass"]):
            self.current["dedup_key"] = (
                f"{self.current['url']}|{self.current['login']}|{self.current['pass']}"
            ).lower()
            self.record_buffer.append(self.current)
        self.current = None

    def _emit(self, rec):
        rec["dedup_key"] = f"{rec['url']}|{rec['login']}|{rec['pass']}".lower()
        self.record_buffer.append(rec)

    def _flush_buffer(self):
        """Return and clear the current buffer."""
        if not self.record_buffer:
            return []
        buf = self.record_buffer
        self.record_buffer = []
        return buf

    def _process_line(self, line_no, raw):
        line = raw.rstrip("\r\n")
        cleaned = clean_line(line)

        if cleaned is None:
            self.stats["oversize"] += 1
            r = self._new_record(line_no)
            r["type"] = "skipped"
            r["status"] = "skipped"
            r["error_code"] = "OVERSIZE_LINE"
            r["error_reason"] = "Line exceeds max length"
            self._emit(r)
            return

        if not cleaned:
            self.stats["empty"] += 1
            r = self._new_record(line_no)
            r["type"] = "skipped"
            r["status"] = "skipped"
            r["error_code"] = "EMPTY_LINE"
            r["error_reason"] = "Blank line"
            self._emit(r)
            return

        if self.exclude_bots and is_bot_line(cleaned):
            self.stats["bot"] += 1
            r = self._new_record(line_no)
            r["type"] = "skipped"
            r["status"] = "skipped"
            r["error_code"] = "BOT_LINE"
            r["error_reason"] = "Bot line"
            self._emit(r)
            return

        # Skip redundant Combo labels
        if SKIP_LABEL.match(cleaned):
            return

        # ---- Format A: labeled ----
        m = URL_LABEL.match(cleaned)
        if m:
            val = m.group(1).strip()
            if not val.startswith(":"):
                if self.current and self.current["url"]:
                    self._flush()
                if not self.current:
                    self.current = self._new_record(line_no)
                self.current["url"] = val
                self.current["line_no"] = line_no
                self.current["type"] = "labeled"
                self.stats["labeled"] += 1
                return

        m = LOGIN_LABEL.match(cleaned)
        if m:
            if self.current and (self.current["login"] or self.current["pass"]):
                self._flush()
            if not self.current:
                self.current = self._new_record(line_no)
            self.current["login"] = m.group(1).strip()
            self.current["line_no"] = line_no
            self.current["type"] = "labeled"
            return

        m = PASS_LABEL.match(cleaned)
        if m:
            if self.current and self.current["pass"]:
                self._flush()
            if not self.current:
                self.current = self._new_record(line_no)
            self.current["pass"] = m.group(1).strip()
            self.current["line_no"] = line_no
            self.current["type"] = "labeled"
            return

        # ---- Format B: url:login:pass ----
        m = URL_COMBO_RE.match(cleaned)
        if m:
            url_part = m.group(1).strip()
            rest = m.group(2)
            if is_url_like(url_part):
                parts = rest.split(":", 1)
                if len(parts) == 2:
                    login = parts[0].strip()
                    pw = parts[1].strip()
                    if login and pw:
                        self._flush()
                        r = self._new_record(line_no)
                        r["url"] = url_part
                        r["login"] = login
                        r["pass"] = pw
                        r["type"] = "combo"
                        r["raw"] = cleaned
                        self._emit(r)
                        self.stats["combo"] += 1
                        return
                elif len(parts) == 1 and parts[0].strip():
                    self._flush()
                    r = self._new_record(line_no)
                    r["url"] = url_part
                    r["pass"] = parts[0].strip()
                    r["type"] = "urlpass"
                    r["raw"] = cleaned
                    self._emit(r)
                    self.stats["urlpass"] += 1
                    return

        # ---- Format C: email:pass ----
        m = EMAIL_COMBO_RE.match(cleaned)
        if m:
            self._flush()
            r = self._new_record(line_no)
            r["login"] = m.group(1).strip()
            r["pass"] = m.group(2).strip()
            r["type"] = "emailpass"
            r["raw"] = cleaned
            self._emit(r)
            self.stats["emailpass"] += 1
            return

        # ---- Fallback: try to split into 2 or 3 parts ----
        if ":" in cleaned:
            parts = cleaned.split(":")
            if len(parts) >= 3:
                first = parts[0].strip()
                if is_url_like(first):
                    login = parts[1].strip()
                    pw = ":".join(parts[2:]).strip()
                    if login and pw:
                        self._flush()
                        r = self._new_record(line_no)
                        r["url"] = first
                        r["login"] = login
                        r["pass"] = pw
                        r["type"] = "combo"
                        r["raw"] = cleaned
                        self._emit(r)
                        self.stats["combo"] += 1
                        return
            if len(parts) == 2:
                left, right = parts[0].strip(), parts[1].strip()
                if left and right:
                    self._flush()
                    r = self._new_record(line_no)
                    if is_url_like(left):
                        r["url"] = left
                        r["pass"] = right
                        r["type"] = "urlpass"
                        self.stats["urlpass"] += 1
                    elif is_email(left):
                        r["login"] = left
                        r["pass"] = right
                        r["type"] = "emailpass"
                        self.stats["emailpass"] += 1
                    else:
                        r["login"] = left
                        r["pass"] = right
                        r["type"] = "emailpass"
                        self.stats["emailpass"] += 1
                    r["raw"] = cleaned
                    self._emit(r)
                    return

        # ---- Unrecognized ----
        self._flush()
        r = self._new_record(line_no)
        r["type"] = "unrecognized"
        r["raw"] = cleaned
        r["error_code"] = "UNRECOGNIZED_FORMAT"
        r["error_reason"] = "Line does not match any format"
        self._emit(r)
        self.stats["unrecognized"] += 1

    def parse(self, progress_callback=None):
        """Yield batches of records. Constant memory."""
        try:
            with open(self.path, "r", encoding="utf-8", errors="replace") as f:
                batch = []
                for line_no, line in enumerate(f, 1):
                    self.line_count = line_no
                    self._process_line(line_no, line)

                    # Every N lines, yield a batch
                    if line_no % READ_CHUNK_LINES == 0:
                        self._flush()
                        batch = self._flush_buffer()
                        if batch:
                            if progress_callback:
                                progress_callback(line_no)
                            yield batch
                        # Small sleep to let system breathe on mobile
                        time.sleep(0.001)

                # Final flush
                self._flush()
                batch = self._flush_buffer()
                if batch:
                    if progress_callback:
                        progress_callback(self.line_count)
                    yield batch
        except Exception as e:
            raise RuntimeError(f"Read error: {e}")


# ============================================================
# SESSION
# ============================================================
class Session:
    def __init__(self):
        self.reset()

    def reset(self):
        if hasattr(self, "db") and self.db:
            try:
                self.db.close()
            except Exception:
                pass
        self.file_path = None
        self.file_size = 0
        self.db = None
        self.line_count = 0
        self.valid_count = 0
        self.invalid_count = 0
        self.duplicate_count = 0
        self.skipped_count = 0
        self.unrecognized_count = 0
        self.detected_formats = {}
        self.parse_duration = 0
        self.mask_emails = True
        self.export_history = []
        self.last_filter_sql = None
        self.last_filter_params = ()

    def is_loaded(self):
        return self.db is not None and self.valid_count + self.invalid_count > 0

    def mask(self, text):
        if not text or not self.mask_emails:
            return text
        try:
            return re.sub(
                r"[A-Za-z0-9._%+-]{1,64}@[A-Za-z0-9.-]{1,200}\.[A-Za-z]{2,10}",
                "[EMAIL]", str(text)
            )
        except Exception:
            return text


# ============================================================
# VALIDATION (during import)
# ============================================================
def validate_batch(db, batch):
    """Validate + dedup a batch of records, insert into DB."""
    seen_keys = set()
    valid = 0
    invalid = 0
    dup = 0

    for r in batch:
        # Skip already-skipped
        if r["status"] == "skipped":
            db.insert(r)
            continue

        # Validate based on type
        is_valid = False
        code = None
        reason = None

        t = r["type"]
        if t == "labeled":
            if r["url"] and r["login"] and r["pass"]:
                is_valid = True
            elif r["url"] and r["login"]:
                is_valid = True
            else:
                code = "MISSING_FIELDS"
                reason = "Labeled record missing required fields"
        elif t == "combo":
            if r["url"] and r["login"] and r["pass"]:
                is_valid = True
            else:
                code = "MISSING_FIELDS"
                reason = "Combo missing fields"
        elif t == "emailpass":
            if r["login"] and r["pass"]:
                is_valid = True
            else:
                code = "MISSING_FIELDS"
                reason = "Email:Pass missing fields"
        elif t == "urlpass":
            if r["url"] and r["pass"]:
                is_valid = True
            else:
                code = "MISSING_FIELDS"
                reason = "URL:Pass missing fields"
        else:
            code = "UNRECOGNIZED_FORMAT"
            reason = "Unrecognized format"

        if not is_valid:
            r["status"] = "invalid"
            r["error_code"] = code
            r["error_reason"] = reason
            db.insert(r)
            invalid += 1
            continue

        # Dedup check — within batch + DB
        key = r["dedup_key"]
        if key in seen_keys:
            r["status"] = "duplicate"
            r["error_code"] = "DUPLICATE"
            r["error_reason"] = "Duplicate (batch)"
            db.insert(r)
            dup += 1
            continue

        existing = db.execute(
            "SELECT 1 FROM records WHERE dedup_key = ? AND status = 'valid' LIMIT 1",
            (key,)
        ).fetchone()
        if existing:
            r["status"] = "duplicate"
            r["error_code"] = "DUPLICATE"
            r["error_reason"] = "Duplicate (existing)"
            db.insert(r)
            dup += 1
            continue

        seen_keys.add(key)
        r["status"] = "valid"
        db.insert(r)
        valid += 1

    db.commit()
    return valid, invalid, dup


# ============================================================
# UI
# ============================================================
def print_banner():
    console.clear()
    if HAS_FIGLET:
        try:
            banner = pyfiglet.figlet_format(APP_NAME, font="slant")
            console.print(Align.center(Text(banner, style="cyan.bold")))
        except Exception:
            console.print(Align.center(Text(f"◈ {APP_NAME} ◈", style="cyan.bold")))
    else:
        console.print(Align.center(Text("◈  L O G S I F T  ◈", style="cyan.bold")))
    console.print(Align.center(Text(
        f"v{APP_VERSION} · Memory-Safe · 100% Local",
        style="muted"
    )))
    console.print()


def make_panel(title, content, border="cyan"):
    return Panel(content, title=f"[bold {border}]{title}[/]",
                 border_style=border, box=ROUNDED, padding=(1, 2))


def pause(msg="Press Enter to continue..."):
    console.print()
    try:
        Prompt.ask(f"[muted]{msg}[/]", default="")
    except (KeyboardInterrupt, EOFError):
        pass


def confirm(msg, default=True):
    try:
        return Confirm.ask(f"[yellow]{msg}[/]", default=default)
    except (KeyboardInterrupt, EOFError):
        return False


def ask(msg, default=""):
    try:
        return Prompt.ask(f"[label]{msg}[/]", default=default)
    except (KeyboardInterrupt, EOFError):
        return default


# ============================================================
# IMPORT
# ============================================================
def action_import(session):
    console.print(Rule("[cyan]Import TXT File[/]", style="cyan"))
    console.print()
    console.print("[muted]Tip: Wrap paths with spaces in quotes[/]")
    console.print("[muted]Example: '/storage/emulated/0/Download/file.txt'[/]")
    console.print()

    path_str = ask("Enter full path to .txt file")
    if not path_str or not path_str.strip():
        console.print("[red]✕ No path entered.[/]")
        return pause()

    # Clean path
    path_str = path_str.strip()
    if (path_str.startswith("'") and path_str.endswith("'")) or \
       (path_str.startswith('"') and path_str.endswith('"')):
        path_str = path_str[1:-1]
    path_str = re.sub(r"\s+/", "/", path_str)
    path_str = re.sub(r"/\s+", "/", path_str)
    path_str = os.path.expanduser(path_str)

    path = Path(path_str)
    if not path.exists():
        console.print(f"[red]✕ File not found:[/] [muted]{path}[/]")
        console.print()
        try:
            parent = path.parent
            if parent.exists():
                similar = [f for f in parent.iterdir()
                           if f.is_file() and f.suffix.lower() == ".txt"][:5]
                if similar:
                    console.print(f"[cyan]Found similar .txt files in {parent}:[/]")
                    for f in similar:
                        console.print(f"  [muted]•[/] {f.name}")
        except Exception:
            pass
        return pause()

    if not path.is_file():
        console.print(f"[red]✕ Not a file: {path}[/]")
        return pause()

    size = path.stat().st_size
    if size == 0:
        console.print("[yellow]⚠ File is empty.[/]")
        return pause()

    console.print()
    console.print(f"[muted]File:[/]  [cyan]{path.name}[/]")
    console.print(f"[muted]Size:[/]  [cyan]{format_bytes(size)}[/]")
    console.print()

    # Memory warning for very large
    if size > 100 * 1024 * 1024:
        console.print(f"[yellow]⚠ Very large file ({format_bytes(size)}).[/]")
        console.print("[muted]Streaming parser will keep memory usage low, "
                      "but processing takes time.[/]")
        if not confirm("Continue?", default=True):
            return

    if not confirm("Start parsing?", default=True):
        return

    # Reset session
    if session.db:
        try:
            session.db.close()
        except Exception:
            pass
    session.reset()

    try:
        session.db = RecordDB()
    except Exception as e:
        console.print(f"[red]✕ Cannot create temp DB: {e}[/]")
        return pause()

    parser = StreamingParser(path, exclude_bots=True)
    start = time.time()
    total_valid = 0
    total_invalid = 0
    total_dup = 0

    progress = Progress(
        SpinnerColumn(style="cyan"),
        TextColumn("[cyan]Parsing[/]"),
        BarColumn(bar_width=30, style="cyan", complete_style="green"),
        TextColumn("[muted]{task.completed} lines[/]"),
        TimeElapsedColumn(),
        console=console,
        transient=True,
    )

    try:
        with progress:
            task = progress.add_task("parse", total=None)

            def cb(line_no):
                progress.update(task, completed=line_no)

            for batch in parser.parse(progress_callback=cb):
                v, i, d = validate_batch(session.db, batch)
                total_valid += v
                total_invalid += i
                total_dup += d
                # Release memory
                del batch

        duration = time.time() - start

        # Final stats from DB
        session.file_path = path
        session.file_size = size
        session.line_count = parser.line_count
        session.valid_count = session.db.count("status='valid'")
        session.invalid_count = session.db.count("status='invalid'")
        session.duplicate_count = session.db.count("status='duplicate'")
        session.skipped_count = session.db.count("status='skipped'")
        session.unrecognized_count = session.db.count("type='unrecognized'")
        session.parse_duration = duration
        session.detected_formats = dict(parser.stats)

        console.print()
        console.print("[green]✓ Import complete![/]")
        console.print()

        stats = Table(show_header=False, box=SIMPLE,
                      border_style="muted", padding=(0, 2))
        stats.add_column(style="label", width=20)
        stats.add_column(style="value")

        stats.add_row("Lines Read", f"[cyan]{format_number(parser.line_count)}[/]")
        stats.add_row("Valid", f"[green]{format_number(session.valid_count)}[/]")
        stats.add_row("Invalid", f"[red]{format_number(session.invalid_count)}[/]")
        stats.add_row("Duplicates", f"[yellow]{format_number(session.duplicate_count)}[/]")
        stats.add_row("Skipped", f"[orange]{format_number(session.skipped_count)}[/]")
        stats.add_row("Duration", f"[cyan]{duration:.2f}s[/]")

        console.print(make_panel("Import Summary", stats, "green"))

    except MemoryError:
        console.print("[red]✕ Out of memory. Try a smaller file.[/]")
        if session.db:
            session.db.close()
            session.db = None
    except KeyboardInterrupt:
        console.print("\n[yellow]⚠ Interrupted.[/]")
        if session.db:
            session.db.close()
            session.db = None
    except Exception as e:
        console.print(f"[red]✕ Error: {e}[/]")
        if session.db:
            session.db.close()
            session.db = None

    pause()


# ============================================================
# VIEW
# ============================================================
def fetch_records(session, where="", params=(), limit=25, offset=0):
    q = (
        "SELECT id, line_no, url, login, pass, type, status, error_code "
        "FROM records"
    )
    if where:
        q += " WHERE " + where
    q += " LIMIT ? OFFSET ?"
    cur = session.db.execute(q, params + (limit, offset))
    return cur.fetchall()


def count_records(session, where="", params=()):
    return session.db.count(where, params)


def action_view(session):
    if not session.is_loaded():
        console.print("[yellow]No records loaded. Import a file first.[/]")
        return pause()

    console.print(Rule("[cyan]View Records[/]", style="cyan"))
    console.print()

    console.print("[label]Which records?[/]")
    console.print("  [cyan]1[/] Valid")
    console.print("  [cyan]2[/] Invalid")
    console.print("  [cyan]3[/] Duplicates")
    console.print("  [cyan]4[/] Skipped")
    console.print("  [cyan]5[/] All")
    console.print()

    choice = ask("Choice", default="1")
    filters = {
        "1": ("status='valid'", ()),
        "2": ("status='invalid'", ()),
        "3": ("status='duplicate'", ()),
        "4": ("status='skipped'", ()),
        "5": ("", ()),
    }
    where, params = filters.get(choice, ("status='valid'", ()))
    title_map = {"1": "Valid", "2": "Invalid", "3": "Duplicates",
                 "4": "Skipped", "5": "All"}
    title = title_map.get(choice, "Valid")

    total = count_records(session, where, params)
    if total == 0:
        console.print(f"[yellow]No {title.lower()} records.[/]")
        return pause()

    page_size = MAX_DISPLAY_ROWS
    total_pages = (total + page_size - 1) // page_size
    page = 1

    while True:
        console.clear()
        print_banner()
        console.print(f"[cyan.bold]{title} Records[/]  "
                      f"[muted]({format_number(total)} total · "
                      f"Page {page}/{total_pages})[/]")
        console.print()

        rows = fetch_records(session, where, params,
                            limit=page_size, offset=(page - 1) * page_size)

        t = Table(show_header=True, header_style="bold cyan",
                  border_style="cyan", box=ROUNDED, padding=(0, 1))
        t.add_column("#", style="muted", width=6, justify="right")
        t.add_column("Line", style="muted", width=8, justify="right")
        t.add_column("URL", style="url", max_width=35, overflow="ellipsis")
        t.add_column("Login", style="login", max_width=25, overflow="ellipsis")
        t.add_column("Pass", style="pass", max_width=18, overflow="ellipsis")
        t.add_column("Type", style="purple", width=11)
        t.add_column("Status", width=10)

        status_style = {"valid": "green", "invalid": "red",
                        "duplicate": "yellow", "skipped": "orange"}

        for idx, row in enumerate(rows, (page - 1) * page_size + 1):
            _id, line_no, url, login, pw, typ, status, _ec = row
            url_s = session.mask(url or "") or "[muted]—[/]"
            login_s = session.mask(login or "") or "[muted]—[/]"
            pw_s = session.mask(pw or "") or "[muted]—[/]"
            status_s = f"[{status_style.get(status, 'muted')}]{status}[/]"
            t.add_row(str(idx), str(line_no), url_s, login_s, pw_s,
                      typ or "", status_s)

        console.print(t)
        console.print()
        console.print("[muted]Navigation:[/] [cyan]n[/]=next  [cyan]p[/]=prev  "
                      "[cyan]g[/]=goto  [cyan]q[/]=quit")

        nav = ask("", default="q").lower()
        if nav == "n" and page < total_pages:
            page += 1
        elif nav == "p" and page > 1:
            page -= 1
        elif nav == "g":
            try:
                p = IntPrompt.ask(f"[label]Page (1-{total_pages})[/]")
                if 1 <= p <= total_pages:
                    page = p
            except (KeyboardInterrupt, EOFError):
                pass
        elif nav == "q":
            break


# ============================================================
# SEARCH
# ============================================================
def action_search(session):
    if not session.is_loaded():
        console.print("[yellow]No records loaded. Import a file first.[/]")
        return pause()

    console.print(Rule("[cyan]Search & Filter[/]", style="cyan"))
    console.print()

    term = ask("Search term")
    if not term or not term.strip():
        console.print("[red]✕ Empty term.[/]")
        return pause()

    console.print()
    console.print("[label]Mode:[/]")
    console.print("  [cyan]1[/] All fields")
    console.print("  [cyan]2[/] URL only")
    console.print("  [cyan]3[/] Login only")
    console.print("  [cyan]4[/] Password only")
    console.print()

    choice = ask("Choice", default="1")

    case_sensitive = confirm("Case sensitive?", default=False)
    term_clean = term.strip()
    pattern = f"%{term_clean}%"

    if choice == "2":
        where = "status='valid' AND url LIKE ?"
        params = (pattern,)
    elif choice == "3":
        where = "status='valid' AND login LIKE ?"
        params = (pattern,)
    elif choice == "4":
        where = "status='valid' AND pass LIKE ?"
        params = (pattern,)
    else:
        where = ("status='valid' AND ("
                 "url LIKE ? OR login LIKE ? OR pass LIKE ?)")
        params = (pattern, pattern, pattern)

    if case_sensitive:
        # SQLite LIKE is case-insensitive for ASCII; use GLOB for case-sensitivity
        # GLOB pattern: *term* (no % wildcards)
        gpattern = f"*{term_clean}*"
        if choice == "2":
            where = "status='valid' AND url GLOB ?"
            params = (gpattern,)
        elif choice == "3":
            where = "status='valid' AND login GLOB ?"
            params = (gpattern,)
        elif choice == "4":
            where = "status='valid' AND pass GLOB ?"
            params = (gpattern,)
        else:
            where = ("status='valid' AND ("
                     "url GLOB ? OR login GLOB ? OR pass GLOB ?)")
            params = (gpattern, gpattern, gpattern)

    start = time.time()
    total = count_records(session, where, params)
    duration = time.time() - start

    session.last_filter_sql = where
    session.last_filter_params = params

    console.print()
    if total == 0:
        console.print("[yellow]⚠ No matches.[/]")
        return pause()

    console.print(f"[green]✓ {format_number(total)} match(es) in {duration:.3f}s[/]")
    console.print()

    # Preview first page
    rows = fetch_records(session, where, params, limit=10)
    t = Table(show_header=True, header_style="bold cyan",
              border_style="green", box=SIMPLE, padding=(0, 1))
    t.add_column("#", style="muted", width=5)
    t.add_column("URL", style="url", max_width=35, overflow="ellipsis")
    t.add_column("Login", style="login", max_width=25, overflow="ellipsis")
    t.add_column("Pass", style="pass", max_width=18, overflow="ellipsis")

    for idx, row in enumerate(rows, 1):
        _id, _ln, url, login, pw, _typ, _st, _ec = row
        t.add_row(
            str(idx),
            session.mask(url or "") or "[muted]—[/]",
            session.mask(login or "") or "[muted]—[/]",
            session.mask(pw or "") or "[muted]—[/]",
        )
    console.print(t)
    if total > 10:
        console.print(f"[muted]... and {total - 10} more[/]")
    console.print()
    console.print("[cyan]Use Export to save these results.[/]")
    pause()


# ============================================================
# EXPORT
# ============================================================
def action_export(session):
    if not session.is_loaded():
        console.print("[yellow]No records loaded. Import a file first.[/]")
        return pause()

    pool_where = session.last_filter_sql or "status='valid'"
    pool_params = session.last_filter_params or ()
    total = count_records(session, pool_where, pool_params)
    if total == 0:
        console.print("[yellow]No records to export.[/]")
        return pause()

    console.print(Rule("[cyan]Export[/]", style="cyan"))
    console.print()
    console.print(f"[label]Exporting [cyan]{format_number(total)}[/] record(s)[/]")
    console.print()

    console.print("[label]Format:[/]")
    console.print("  [cyan]1[/] Labeled (URL:/Login:/Pass:)")
    console.print("  [cyan]2[/] Combo (url:login:pass)")
    console.print("  [cyan]3[/] CSV")
    console.print("  [cyan]4[/] JSON")
    console.print("  [cyan]5[/] URL:Login only")
    console.print()

    choice = ask("Choice", default="1")
    fmt_map = {"1": "labeled", "2": "combo", "3": "csv",
               "4": "json", "5": "urllogin"}
    fmt = fmt_map.get(choice, "labeled")

    ext_map = {"labeled": ".txt", "combo": ".txt", "csv": ".csv",
               "json": ".json", "urllogin": ".txt"}
    ext = ext_map[fmt]
    default_name = f"logsift_{datetime.now().strftime('%Y%m%d_%H%M%S')}{ext}"

    filename = ask("Filename", default=default_name)
    if not filename.endswith(ext):
        base = filename.rsplit(".", 1)[0] if "." in filename else filename
        filename = base + ext

    out_path = Path(filename).expanduser()
    if not out_path.is_absolute():
        out_path = Path.cwd() / out_path

    try:
        with Progress(
            SpinnerColumn(style="cyan"),
            TextColumn("[cyan]Exporting[/]"),
            BarColumn(bar_width=30, style="cyan", complete_style="green"),
            TextColumn("[muted]{task.completed}/{task.total}[/]"),
            TimeElapsedColumn(),
            console=console,
            transient=True,
        ) as progress:
            task = progress.add_task("export", total=total)

            if fmt == "csv":
                with open(out_path, "w", newline="", encoding="utf-8") as f:
                    w = csv.writer(f, quoting=csv.QUOTE_ALL)
                    w.writerow(["URL", "Login", "Password", "Type", "Status"])
                    offset = 0
                    while offset < total:
                        rows = fetch_records(session, pool_where, pool_params,
                                            limit=EXPORT_CHUNK, offset=offset)
                        for row in rows:
                            _id, _ln, url, login, pw, typ, status, _ec = row
                            w.writerow([url, login, pw, typ, status])
                        progress.update(task, advance=len(rows))
                        offset += EXPORT_CHUNK
                        del rows
            elif fmt == "json":
                with open(out_path, "w", encoding="utf-8") as f:
                    f.write("[\n")
                    offset = 0
                    first = True
                    while offset < total:
                        rows = fetch_records(session, pool_where, pool_params,
                                            limit=EXPORT_CHUNK, offset=offset)
                        for row in rows:
                            _id, ln, url, login, pw, typ, status, _ec = row
                            obj = {
                                "line_no": ln,
                                "url": url or "",
                                "login": login or "",
                                "pass": pw or "",
                                "type": typ or "",
                                "status": status or "",
                            }
                            if not first:
                                f.write(",\n")
                            f.write(json.dumps(obj, ensure_ascii=False))
                            first = False
                        progress.update(task, advance=len(rows))
                        offset += EXPORT_CHUNK
                        del rows
                    f.write("\n]\n")
            else:
                with open(out_path, "w", encoding="utf-8") as f:
                    offset = 0
                    first_record = True
                    while offset < total:
                        rows = fetch_records(session, pool_where, pool_params,
                                            limit=EXPORT_CHUNK, offset=offset)
                        for row in rows:
                            _id, _ln, url, login, pw, typ, status, _ec = row
                            if fmt == "labeled":
                                block = []
                                if url:   block.append(f"URL    : {url}")
                                if login: block.append(f"Login  : {login}")
                                if pw:    block.append(f"Pass   : {pw}")
                                if block:
                                    if not first_record:
                                        f.write("\n\n")
                                    f.write("\n".join(block))
                                    first_record = False
                            elif fmt == "combo":
                                if url and login and pw:
                                    line = f"{url}:{login}:{pw}"
                                elif login and pw:
                                    line = f"{login}:{pw}"
                                elif url and pw:
                                    line = f"{url}:{pw}"
                                else:
                                    line = ""
                                if line:
                                    f.write(line + "\n")
                            elif fmt == "urllogin":
                                if url and login:
                                    f.write(f"{url}:{login}\n")
                                elif login:
                                    f.write(f"{login}\n")
                        progress.update(task, advance=len(rows))
                        offset += EXPORT_CHUNK
                        del rows

        size = out_path.stat().st_size
        console.print()
        console.print("[green]✓ Export complete![/]")
        console.print(f"[muted]File:[/] [cyan]{out_path}[/]")
        console.print(f"[muted]Size:[/] [cyan]{format_bytes(size)}[/]")

        session.export_history.insert(0, {
            "filename": filename,
            "format": fmt,
            "count": total,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        })
        if len(session.export_history) > 10:
            session.export_history.pop()

    except MemoryError:
        console.print("[red]✕ Out of memory during export.[/]")
    except Exception as e:
        console.print(f"[red]✕ Export failed: {e}[/]")

    pause()


# ============================================================
# STATS
# ============================================================
def action_stats(session):
    if not session.is_loaded():
        console.print("[yellow]No records loaded.[/]")
        return pause()

    console.print(Rule("[cyan]Statistics[/]", style="cyan"))
    console.print()

    t = Table(show_header=False, box=ROUNDED,
              border_style="cyan", padding=(0, 2))
    t.add_column("Metric", style="label", width=22)
    t.add_column("Value", style="cyan", justify="right")

    t.add_row("File", str(session.file_path.name) if session.file_path else "—")
    t.add_row("File Size", format_bytes(session.file_size))
    t.add_row("Lines Read", format_number(session.line_count))
    t.add_row("Valid", f"[green]{format_number(session.valid_count)}[/]")
    t.add_row("Invalid", f"[red]{format_number(session.invalid_count)}[/]")
    t.add_row("Duplicates", f"[yellow]{format_number(session.duplicate_count)}[/]")
    t.add_row("Skipped", f"[orange]{format_number(session.skipped_count)}[/]")
    t.add_row("Duration", f"{session.parse_duration:.2f}s")

    console.print(make_panel("Session", t, "cyan"))
    console.print()

    if session.detected_formats:
        ft = Table(show_header=True, header_style="bold cyan",
                   border_style="muted", box=SIMPLE, padding=(0, 2))
        ft.add_column("Format", style="cyan")
        ft.add_column("Count", style="value", justify="right")
        for k, v in sorted(session.detected_formats.items(),
                          key=lambda x: -x[1]):
            ft.add_row(k, format_number(v))
        console.print(ft)
        console.print()

    if session.export_history:
        et = Table(show_header=True, header_style="bold cyan",
                   border_style="muted", box=SIMPLE, padding=(0, 1))
        et.add_column("#", style="muted", width=3)
        et.add_column("File", style="cyan")
        et.add_column("Format", style="purple", width=10)
        et.add_column("Count", style="value", justify="right", width=8)
        et.add_column("When", style="muted")
        for i, item in enumerate(session.export_history[:5], 1):
            et.add_row(str(i), item["filename"], item["format"],
                       format_number(item["count"]), item["timestamp"])
        console.print(et)

    pause()


# ============================================================
# SETTINGS
# ============================================================
def action_settings(session):
    while True:
        console.clear()
        print_banner()
        console.print(Rule("[cyan]Settings[/]", style="cyan"))
        console.print()

        mask_s = "[green]ON[/]" if session.mask_emails else "[red]OFF[/]"
        console.print(f"  [cyan]1[/] Mask emails in previews   {mask_s}")
        console.print(f"  [cyan]2[/] Clear session")
        console.print(f"  [cyan]3[/] Back")
        console.print()

        choice = ask("Choice", default="3")
        if choice == "1":
            session.mask_emails = not session.mask_emails
        elif choice == "2":
            if confirm("Clear all imported records?", default=False):
                session.reset()
                console.print("[green]✓ Session cleared.[/]")
                pause()
        elif choice == "3":
            break


# ============================================================
# MAIN MENU
# ============================================================
def main_menu(session):
    while True:
        print_banner()

        if session.is_loaded():
            info = Table(show_header=False, box=SIMPLE,
                         border_style="muted", padding=(0, 1))
            info.add_column(style="muted")
            info.add_column(style="cyan")
            info.add_row("File:", session.file_path.name if session.file_path else "—")
            info.add_row("Valid:", f"[green]{format_number(session.valid_count)}[/]")
            info.add_row("Invalid:", f"[red]{format_number(session.invalid_count)}[/]")
            info.add_row("Duplicates:", f"[yellow]{format_number(session.duplicate_count)}[/]")
            console.print(make_panel("Session", info, "cyan"))
        else:
            console.print(Panel(
                "[muted]No file loaded. Import a .txt file to start.[/]",
                border_style="muted", box=ROUNDED, padding=(0, 2)
            ))

        console.print()

        menu = Table(show_header=False, box=ROUNDED,
                     border_style="cyan", padding=(0, 3))
        menu.add_column(style="cyan.bold", width=6, justify="center")
        menu.add_column(style="value")

        menu.add_row("1", "⬆  Import TXT file")
        menu.add_row("2", "▤  View records")
        menu.add_row("3", "⌕  Search & filter")
        menu.add_row("4", "⤓  Export results")
        menu.add_row("5", "▦  Statistics")
        menu.add_row("6", "⚙  Settings")
        menu.add_row("0", "✕  Exit")

        console.print(menu)
        console.print()

        choice = ask("Select", default="0")

        if choice == "1":
            action_import(session)
        elif choice == "2":
            action_view(session)
        elif choice == "3":
            action_search(session)
        elif choice == "4":
            action_export(session)
        elif choice == "5":
            action_stats(session)
        elif choice == "6":
            action_settings(session)
        elif choice == "0":
            if confirm("Exit LOGSIFT?", default=True):
                break


# ============================================================
# ENTRY
# ============================================================
def main():
    if len(sys.argv) > 1 and sys.argv[1] in ("-h", "--help"):
        console.print("[cyan]LOGSIFT Terminal v2[/]")
        console.print()
        console.print("Usage:")
        console.print("  python logsift.py                       Launch menu")
        console.print("  python logsift.py <file.txt>            Auto-load file")
        console.print("  python logsift.py --help                Show this help")
        console.print()
        console.print("Install: pip install rich pyfiglet")
        return

    session = Session()

    # Auto-load if path provided
    if len(sys.argv) > 1:
        raw = " ".join(sys.argv[1:]).strip().strip("'\"")
        raw = re.sub(r"\s+/", "/", raw)
        raw = re.sub(r"/\s+", "/", raw)
        raw = os.path.expanduser(raw)
        path = Path(raw)
        if path.exists() and path.is_file():
            console.print(f"[cyan]Auto-loading:[/] [muted]{path}[/]")
            # Delegate to import logic
            class FakeInput:
                pass
            try:
                session.db = RecordDB()
                parser = StreamingParser(path, exclude_bots=True)
                start = time.time()
                with Progress(
                    SpinnerColumn(style="cyan"),
                    TextColumn("[cyan]Parsing[/]"),
                    BarColumn(bar_width=30, style="cyan", complete_style="green"),
                    TextColumn("[muted]{task.completed} lines[/]"),
                    TimeElapsedColumn(),
                    console=console,
                    transient=True,
                ) as progress:
                    task = progress.add_task("parse", total=None)
                    def cb(n):
                        progress.update(task, completed=n)
                    for batch in parser.parse(progress_callback=cb):
                        validate_batch(session.db, batch)
                        del batch
                session.file_path = path
                session.file_size = path.stat().st_size
                session.line_count = parser.line_count
                session.valid_count = session.db.count("status='valid'")
                session.invalid_count = session.db.count("status='invalid'")
                session.duplicate_count = session.db.count("status='duplicate'")
                session.skipped_count = session.db.count("status='skipped'")
                session.parse_duration = time.time() - start
                session.detected_formats = dict(parser.stats)
                console.print(f"[green]✓ Loaded {format_number(session.valid_count)} "
                              f"valid records in {session.parse_duration:.2f}s[/]")
                pause()
            except Exception as e:
                console.print(f"[red]✕ Error: {e}[/]")
                if session.db:
                    session.db.close()
                    session.db = None
                return
        else:
            console.print(f"[red]✕ File not found: {raw}[/]")
            return

    try:
        main_menu(session)
    except KeyboardInterrupt:
        console.print()
        console.print("[muted]Interrupted.[/]")
    except Exception as e:
        console.print()
        console.print(f"[red]✕ Fatal: {e}[/]")
    finally:
        if session.db:
            session.db.close()


if __name__ == "__main__":
    main()