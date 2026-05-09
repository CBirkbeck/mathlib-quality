#!/usr/bin/env python3
"""Live mathematical-status dashboard for /develop projects.

Reads `.mathlib-quality/plan.md`, `.mathlib-quality/tickets.md`, and the
in-progress `.lean` files to build a snapshot. Serves an HTML dashboard at
http://localhost:<port>/ with a clickable dependency tree and per-ticket /
per-step zoom. The page polls `/api/status` every 3 seconds for live updates.

Usage:
    python3 project_status_server.py            # start on first free port from 8765
    python3 project_status_server.py --port N   # specific port
    python3 project_status_server.py --stop     # kill any running instance
    python3 project_status_server.py --json     # one-shot JSON dump (for the chat agent)

The server runs in the foreground; the slash command launches it in the
background. A PID file lives at `.mathlib-quality/.status_server.pid`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import socket
import subprocess
import sys
import time
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

ROOT = Path.cwd()
MQ_DIR = ROOT / ".mathlib-quality"
PID_FILE = MQ_DIR / ".status_server.pid"
TICKETS_FILE = MQ_DIR / "tickets.md"
PLAN_FILE = MQ_DIR / "plan.md"

BLOCKER_KEYWORDS = (
    "PROOF-SKETCH FAILURE",
    "MATHLIB GAP",
    "SCOPE / DEFINITION ERROR",
    "SCOPE-DEFINITION ERROR",
    "DEPENDENCY NOT MET",
    "BLOCKED",
)

STALE_DAYS = 7


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------


def parse_plan() -> dict:
    if not PLAN_FILE.exists():
        return {"title": "Untitled project", "main_goal": ""}
    text = PLAN_FILE.read_text(encoding="utf-8")
    title_match = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    title = title_match.group(1).strip() if title_match else "Untitled project"
    paras = re.split(r"\n\s*\n", text)
    main_goal = ""
    for para in paras[1:]:
        stripped = para.strip()
        if not stripped or stripped.startswith("#"):
            continue
        main_goal = stripped
        break
    return {"title": title, "main_goal": main_goal}


_TICKET_HEADING_RE = re.compile(r"^###\s+\[([^\]]+)\]\s*(.*)$", re.MULTILINE)


def parse_tickets() -> list[dict]:
    if not TICKETS_FILE.exists():
        return []
    text = TICKETS_FILE.read_text(encoding="utf-8")
    boundaries: list[tuple[int, str, str]] = []
    for m in _TICKET_HEADING_RE.finditer(text):
        boundaries.append((m.start(), m.group(1).strip(), m.group(2).strip()))
    tickets = []
    for i, (start, tid, title) in enumerate(boundaries):
        end = boundaries[i + 1][0] if i + 1 < len(boundaries) else len(text)
        body = text[start:end]
        tickets.append(_parse_ticket_block(tid, title, body))
    return tickets


def _extract_field(body: str, name: str) -> str | None:
    m = re.search(rf"^-\s+\*\*{re.escape(name)}\*\*:\s*(.+?)$", body, re.MULTILINE)
    return m.group(1).strip() if m else None


def _extract_section(body: str, header: str) -> str:
    pattern = rf"####\s+{re.escape(header)}\s*\n(.*?)(?=\n####\s|\n###\s|\n\*\*Progress\*\*:|\Z)"
    m = re.search(pattern, body, re.DOTALL | re.IGNORECASE)
    return m.group(1).strip() if m else ""


def _extract_lean_block(section: str) -> str:
    m = re.search(r"```lean\s*\n(.*?)\n```", section, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r"```\s*\n(.*?)\n```", section, re.DOTALL)
    return m.group(1).strip() if m else ""


def _extract_sketch_steps(section: str) -> list[dict]:
    if not section:
        return []
    lines = section.splitlines()
    steps: list[dict] = []
    current: dict | None = None
    step_re = re.compile(r"^\s{0,3}(\d+)\.\s+(.*)$")
    for line in lines:
        m = step_re.match(line)
        if m:
            if current:
                steps.append(current)
            current = {"index": int(m.group(1)), "text": m.group(2).strip()}
        elif current and line.strip():
            current["text"] += " " + line.strip()
    if current:
        steps.append(current)
    return steps


def _extract_bullet_list(section: str) -> list[str]:
    items = []
    for line in section.splitlines():
        m = re.match(r"^\s*-\s+(.+)$", line)
        if m:
            items.append(m.group(1).strip())
    return items


def _extract_progress(body: str) -> list[dict]:
    m = re.search(r"\*\*Progress\*\*:\s*\n(.*?)(?=\n###\s|\Z)", body, re.DOTALL)
    if not m:
        return []
    block = m.group(1)
    entries = []
    iso_re = re.compile(
        r"^\s*-\s+(\d{4}-\d{2}-\d{2}(?:T\d{2}:\d{2}(?::\d{2})?(?:Z|[+\-]\d{2}:?\d{2})?)?)\s*[—:\-–]\s*(.*?)$"
    )
    for line in block.splitlines():
        m = iso_re.match(line)
        if m:
            entries.append({"timestamp": m.group(1), "note": m.group(2).strip()})
        elif line.strip().startswith("- "):
            entries.append({"timestamp": "", "note": line.strip()[2:]})
    return entries


def _parse_ticket_block(tid: str, title: str, body: str) -> dict:
    statement_section = _extract_section(body, "Statement")
    sketch_section = _extract_section(body, "Proof sketch") or _extract_section(body, "Proof Sketch")
    sources_section = _extract_section(body, "Sources")
    mathlib_section = (
        _extract_section(body, "Mathlib lemmas needed")
        or _extract_section(body, "Mathlib lemmas")
    )
    statement = _extract_lean_block(statement_section)
    sketch_steps = _extract_sketch_steps(sketch_section)
    progress = _extract_progress(body)
    status = _extract_field(body, "Status") or "open"
    file_field = _extract_field(body, "File") or ""
    type_field = _extract_field(body, "Type") or ""
    depends_field = _extract_field(body, "Depends on") or "none"
    depends_on = []
    if depends_field.lower() not in ("none", "—", "-", ""):
        depends_on = [d.strip() for d in re.split(r"[,;]", depends_field) if d.strip()]
    return {
        "id": tid,
        "title": title,
        "status": status,
        "type": type_field,
        "file": file_field,
        "depends_on": depends_on,
        "statement": statement,
        "sketch_steps": sketch_steps,
        "sources": _extract_bullet_list(sources_section),
        "mathlib_lemmas": _extract_bullet_list(mathlib_section),
        "progress_entries": progress,
        "raw_body": body,
    }


# ---------------------------------------------------------------------------
# Sketch-step status from progress entries
# ---------------------------------------------------------------------------


_CLOSED_STEP_RE = re.compile(r"closed step (\d+)", re.IGNORECASE)
_STEP_ATTEMPT_RE = re.compile(r"step (\d+)", re.IGNORECASE)


def annotate_steps(ticket: dict) -> dict:
    """Mark each sketch step as closed / current / open based on Progress entries."""
    steps = ticket.get("sketch_steps", [])
    if not steps:
        return ticket
    closed: set[int] = set()
    notes: dict[int, str] = {}
    last_attempted: int | None = None
    for entry in ticket.get("progress_entries", []):
        note = entry.get("note", "")
        for m in _CLOSED_STEP_RE.finditer(note):
            n = int(m.group(1))
            closed.add(n)
            notes[n] = note
        for m in _STEP_ATTEMPT_RE.finditer(note):
            last_attempted = int(m.group(1))
    if ticket["status"] == "done":
        for s in steps:
            s["step_status"] = "closed"
            s.setdefault("closing_note", notes.get(s["index"], ""))
        return ticket

    current_idx: int | None = None
    if last_attempted is not None and last_attempted not in closed:
        current_idx = last_attempted
    else:
        for s in steps:
            if s["index"] not in closed:
                current_idx = s["index"]
                break
    for s in steps:
        if s["index"] in closed:
            s["step_status"] = "closed"
            s["closing_note"] = notes.get(s["index"], "")
        elif s["index"] == current_idx:
            s["step_status"] = "current"
        else:
            s["step_status"] = "open"
    ticket["stuck_step"] = current_idx
    return ticket


# ---------------------------------------------------------------------------
# Blockers + off-track detection
# ---------------------------------------------------------------------------


def is_blocker(ticket: dict) -> bool:
    if ticket["status"] == "blocked":
        return True
    if ticket["status"] != "in_progress":
        return False
    entries = ticket.get("progress_entries", [])
    if entries:
        latest = entries[-1].get("note", "").upper()
        if any(k in latest for k in (k.upper() for k in BLOCKER_KEYWORDS)):
            return True
        ts = entries[-1].get("timestamp", "")
        try:
            t = datetime.fromisoformat(ts.replace("Z", "+00:00"))
            now = datetime.now(timezone.utc)
            if (now - t).days >= STALE_DAYS:
                return True
        except (ValueError, TypeError):
            pass
    return False


_DECL_NAME_RE = re.compile(
    r"\b(?:theorem|lemma|def|abbrev|instance|noncomputable\s+def)\s+(\w+(?:\.\w+)*)"
)


def extract_declaration_name(statement: str) -> str | None:
    m = _DECL_NAME_RE.search(statement)
    return m.group(1) if m else None


def read_lean_context(ticket: dict) -> dict:
    """For an in_progress / blocked ticket, read the .lean file and surface
    the live signature, sorry positions, and surrounding `have` statements
    as mathematical context."""
    file_field = ticket.get("file", "")
    if not file_field:
        return {}
    path = ROOT / file_field.strip()
    if not path.exists():
        return {"file_status": "missing", "file_path": str(path.relative_to(ROOT))}
    decl_name = extract_declaration_name(ticket.get("statement", ""))
    if not decl_name:
        return {"file_status": "no-decl-name"}
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    short_name = decl_name.split(".")[-1]
    decl_pattern = re.compile(
        rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance)\s+(?:\w+\.)*{re.escape(short_name)}\b"
    )
    start_line = None
    for i, line in enumerate(lines):
        if decl_pattern.match(line):
            start_line = i
            break
    if start_line is None:
        return {
            "file_status": "decl-missing",
            "file_path": str(path.relative_to(ROOT)),
            "expected_name": decl_name,
        }
    end_line = start_line
    for i in range(start_line + 1, len(lines)):
        if i > start_line and lines[i] and not lines[i].startswith((" ", "\t", "·", "|")):
            if re.match(r"^\s*$", lines[i]):
                continue
            if not re.match(r"^\s*(?:end|namespace|section|private|protected|@\[|--)", lines[i]):
                end_line = i
                break
        end_line = i
    decl_block = "\n".join(lines[start_line : end_line + 1])
    sig_match = re.search(r"^.*?(?::=|\bby\b)", decl_block, re.DOTALL)
    live_signature = sig_match.group(0).strip() if sig_match else decl_block.split("\n", 1)[0]
    sorry_positions = [
        i + 1 for i, line in enumerate(lines[start_line : end_line + 1]) if "sorry" in line
    ]
    sorry_positions = [p + start_line for p in sorry_positions]
    have_statements = []
    have_re = re.compile(r"^\s*have\s+(\w+)\s*(?::\s*(.+?))?\s*:=", re.MULTILINE)
    for m in have_re.finditer(decl_block):
        have_statements.append({"name": m.group(1), "type_hint": (m.group(2) or "").strip()})
    drift_flags = detect_drift(ticket, live_signature, decl_block)
    return {
        "file_status": "ok",
        "file_path": str(path.relative_to(ROOT)),
        "declaration_lines": [start_line + 1, end_line + 1],
        "live_signature": live_signature,
        "decl_block": decl_block,
        "sorry_lines": sorry_positions,
        "have_statements": have_statements,
        "drift_flags": drift_flags,
    }


def detect_drift(ticket: dict, live_signature: str, decl_block: str) -> list[str]:
    flags = []
    decl_name = extract_declaration_name(ticket.get("statement", ""))
    live_name = extract_declaration_name(live_signature)
    if decl_name and live_name and decl_name.split(".")[-1] != live_name.split(".")[-1]:
        flags.append(
            f"Renamed: ticket says `{decl_name}`, file has `{live_name}`"
        )
    sketch_count = len(ticket.get("sketch_steps", []))
    have_count = len(re.findall(r"^\s*have\s+\w+\s*[:=]", decl_block, re.MULTILINE))
    if sketch_count and have_count > 2 * sketch_count:
        flags.append(
            f"Possible scope creep: {have_count} `have` statements vs {sketch_count} sketch steps"
        )
    return flags


# ---------------------------------------------------------------------------
# Tree + progress assembly
# ---------------------------------------------------------------------------


def compute_progress(tickets: list[dict]) -> dict:
    total_count = len(tickets)
    done_count = sum(1 for t in tickets if t["status"] == "done")
    in_prog = sum(1 for t in tickets if t["status"] == "in_progress")
    open_n = sum(1 for t in tickets if t["status"] == "open")
    blocked = sum(1 for t in tickets if t["status"] == "blocked")
    total_weight = sum(max(len(t.get("sketch_steps", [])), 1) for t in tickets)
    done_weight = sum(
        max(len(t.get("sketch_steps", [])), 1) for t in tickets if t["status"] == "done"
    )
    percent = round(100 * done_weight / total_weight) if total_weight else 0
    off_track = sum(
        1 for t in tickets if t.get("live_context", {}).get("drift_flags")
    )
    return {
        "percent": percent,
        "done_weight": done_weight,
        "total_weight": total_weight,
        "done_count": done_count,
        "total_count": total_count,
        "in_progress": in_prog,
        "open": open_n,
        "blocked": blocked,
        "off_track_flags": off_track,
    }


def build_tree(tickets: list[dict]) -> tuple[dict, list[str]]:
    by_id = {t["id"]: t for t in tickets}
    children: dict[str, list[str]] = {tid: [] for tid in by_id}
    for t in tickets:
        for dep in t["depends_on"]:
            if dep in children:
                children[dep].append(t["id"])
    has_parent = {tid for t in tickets for tid in t["depends_on"] if tid in by_id}
    referenced_as_dep = {tid for parent_list in children.values() for tid in parent_list}
    roots = [t["id"] for t in tickets if t["id"] in referenced_as_dep and t["id"] not in has_parent]
    if not roots:
        roots = [t["id"] for t in tickets if not t["depends_on"]]
    leaves = [t["id"] for t in tickets if not children[t["id"]]]
    final_roots = leaves if not roots else roots
    return children, sorted(set(final_roots))


def derive_math_name(ticket: dict) -> str:
    """Paraphrase a structural title like 'Prove fooBar_comp' into a math name.

    Strategy: prefer the first non-step line of the proof sketch; else strip
    leading verbs from the title; else use the title verbatim."""
    title = ticket.get("title", "").strip()
    if title.lower().startswith(("prove ", "show ", "verify ", "establish ")):
        title = title.split(" ", 1)[1]
    return title


# ---------------------------------------------------------------------------
# Snapshot assembly
# ---------------------------------------------------------------------------


def build_snapshot() -> dict:
    plan = parse_plan()
    tickets = [annotate_steps(t) for t in parse_tickets()]
    for t in tickets:
        if t["status"] in ("in_progress", "blocked"):
            t["live_context"] = read_lean_context(t)
        else:
            t["live_context"] = {}
        t["math_name"] = derive_math_name(t)
        t["is_blocker"] = is_blocker(t)
    children, roots = build_tree(tickets)
    progress = compute_progress(tickets)
    oldest_in_progress = None
    oldest_ts = None
    for t in tickets:
        if t["status"] != "in_progress":
            continue
        entries = t.get("progress_entries", [])
        if not entries:
            continue
        first_ts = entries[0].get("timestamp", "")
        try:
            ts = datetime.fromisoformat(first_ts.replace("Z", "+00:00"))
        except (ValueError, TypeError):
            continue
        if oldest_ts is None or ts < oldest_ts:
            oldest_ts = ts
            oldest_in_progress = t["id"]
    return {
        "title": plan["title"],
        "main_goal": plan["main_goal"],
        "progress": progress,
        "tickets": {t["id"]: t for t in tickets},
        "children": children,
        "roots": roots,
        "oldest_in_progress": oldest_in_progress,
        "last_updated": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):  # silence default access log
        pass

    def do_GET(self):
        if self.path == "/" or self.path == "/index.html":
            self._send_html(DASHBOARD_HTML)
        elif self.path.startswith("/api/status"):
            try:
                snapshot = build_snapshot()
                self._send_json(snapshot)
            except Exception as exc:
                self._send_json({"error": str(exc)}, status=500)
        else:
            self.send_response(404)
            self.end_headers()

    def _send_html(self, body: str):
        encoded = body.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(encoded)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(encoded)

    def _send_json(self, obj: dict, status: int = 200):
        encoded = json.dumps(obj, default=str).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(encoded)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(encoded)


def find_free_port(start: int = 8765, span: int = 30) -> int:
    for offset in range(span):
        port = start + offset
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind(("127.0.0.1", port))
                return port
            except OSError:
                continue
    raise RuntimeError(f"No free port in range {start}-{start+span}")


def write_pid(port: int):
    MQ_DIR.mkdir(parents=True, exist_ok=True)
    PID_FILE.write_text(f"{os.getpid()}\n{port}\n")


def read_pid() -> tuple[int, int] | None:
    if not PID_FILE.exists():
        return None
    try:
        lines = PID_FILE.read_text().splitlines()
        return int(lines[0]), int(lines[1])
    except (ValueError, IndexError):
        return None


def is_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def stop_existing() -> bool:
    info = read_pid()
    if not info:
        return False
    pid, _port = info
    if is_alive(pid):
        try:
            os.kill(pid, 15)  # SIGTERM
            time.sleep(0.3)
            if is_alive(pid):
                os.kill(pid, 9)
        except ProcessLookupError:
            pass
    PID_FILE.unlink(missing_ok=True)
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=None)
    parser.add_argument("--stop", action="store_true")
    parser.add_argument("--status", action="store_true", help="print existing server URL if any, else nothing")
    parser.add_argument("--json", action="store_true", help="one-shot snapshot to stdout, no server")
    args = parser.parse_args()

    if args.stop:
        stopped = stop_existing()
        print("stopped" if stopped else "no server running")
        return

    if args.status:
        info = read_pid()
        if info and is_alive(info[0]):
            print(f"http://127.0.0.1:{info[1]}/")
        return

    if args.json:
        print(json.dumps(build_snapshot(), default=str, indent=2))
        return

    info = read_pid()
    if info and is_alive(info[0]):
        print(f"already running: http://127.0.0.1:{info[1]}/")
        return

    if info:
        PID_FILE.unlink(missing_ok=True)

    port = args.port or find_free_port()
    write_pid(port)
    server = HTTPServer(("127.0.0.1", port), Handler)
    print(f"serving: http://127.0.0.1:{port}/")
    sys.stdout.flush()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        PID_FILE.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Dashboard HTML (embedded)
# ---------------------------------------------------------------------------


DASHBOARD_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Project Status</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js"></script>
<script defer src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"></script>
<style>
  :root {
    --bg: #fafafa;
    --bg-panel: #ffffff;
    --border: #e2e2e2;
    --fg: #1d1d1f;
    --fg-muted: #6b6b70;
    --accent: #0066cc;
    --done: #34a853;
    --in-progress: #f59e0b;
    --open: #6b6b70;
    --blocked: #d93025;
    --hover: #f0f0f4;
    --selected: #e2eaff;
    --warn: #fff7e0;
    --warn-border: #f5d97f;
    --code-bg: #f5f5f7;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #1a1a1a; --bg-panel: #242424; --border: #353535;
      --fg: #f0f0f0; --fg-muted: #a0a0a0;
      --accent: #4e9bff; --hover: #2c2c2c; --selected: #2a3550;
      --warn: #3a2f0e; --warn-border: #6b541a; --code-bg: #1f1f1f;
    }
  }
  * { box-sizing: border-box; }
  html, body { margin: 0; height: 100%; }
  body {
    background: var(--bg); color: var(--fg);
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", system-ui, sans-serif;
    font-size: 14px; line-height: 1.5;
    display: flex; flex-direction: column; height: 100vh;
  }
  header {
    background: var(--bg-panel); border-bottom: 1px solid var(--border);
    padding: 10px 18px; display: flex; align-items: center; gap: 16px;
    flex-shrink: 0;
  }
  header h1 {
    margin: 0; font-size: 16px; font-weight: 600;
    overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
  }
  .progress-bar {
    flex-grow: 1; max-width: 400px;
    height: 8px; background: var(--border); border-radius: 4px; overflow: hidden;
  }
  .progress-fill { height: 100%; background: var(--done); transition: width 0.5s; }
  .progress-text { font-variant-numeric: tabular-nums; color: var(--fg-muted); font-size: 13px; }
  .counts { display: flex; gap: 12px; font-size: 13px; }
  .counts span { color: var(--fg-muted); }
  .counts .badge { font-weight: 600; color: var(--fg); }
  .live-indicator {
    display: flex; align-items: center; gap: 6px;
    font-size: 12px; color: var(--fg-muted);
  }
  .live-dot {
    width: 8px; height: 8px; border-radius: 50%; background: var(--done);
    animation: pulse 2s infinite;
  }
  .live-dot.stale { background: var(--blocked); animation: none; }
  @keyframes pulse {
    0%, 100% { opacity: 1; } 50% { opacity: 0.4; }
  }

  main {
    flex-grow: 1; display: flex; min-height: 0;
  }
  #tree-pane {
    width: 38%; min-width: 280px; max-width: 520px;
    border-right: 1px solid var(--border);
    background: var(--bg-panel);
    overflow-y: auto;
    padding: 10px 0;
  }
  #detail-pane {
    flex-grow: 1; overflow-y: auto; padding: 18px 26px;
  }

  .tree-node {
    padding: 4px 14px; cursor: pointer; user-select: none;
    display: flex; align-items: flex-start; gap: 6px;
    border-left: 3px solid transparent;
    font-size: 13px;
  }
  .tree-node:hover { background: var(--hover); }
  .tree-node.selected { background: var(--selected); border-left-color: var(--accent); }
  .tree-node .toggle { width: 12px; flex-shrink: 0; color: var(--fg-muted); }
  .tree-node .icon { width: 16px; flex-shrink: 0; }
  .tree-node .id-label {
    color: var(--fg-muted); font-family: ui-monospace, monospace;
    font-size: 12px; flex-shrink: 0;
  }
  .tree-node .name { flex-grow: 1; word-break: break-word; }
  .tree-node .blocker-tag {
    color: var(--blocked); font-size: 11px; font-weight: 600; flex-shrink: 0;
  }

  h2 { font-size: 18px; margin: 0 0 6px; font-weight: 600; }
  h3 { font-size: 15px; margin: 18px 0 6px; font-weight: 600; }
  h4 { font-size: 13px; margin: 14px 0 4px; font-weight: 600; color: var(--fg-muted); text-transform: uppercase; letter-spacing: 0.05em; }
  p { margin: 6px 0; }

  .meta-row {
    display: flex; gap: 16px; flex-wrap: wrap; font-size: 12px;
    color: var(--fg-muted); margin: 4px 0 14px;
  }
  .status-pill {
    display: inline-block; padding: 1px 8px; border-radius: 999px;
    font-size: 11px; font-weight: 600; text-transform: uppercase;
    letter-spacing: 0.04em;
  }
  .status-done { background: rgba(52,168,83,0.15); color: var(--done); }
  .status-in_progress { background: rgba(245,158,11,0.15); color: var(--in-progress); }
  .status-open { background: rgba(107,107,112,0.15); color: var(--open); }
  .status-blocked { background: rgba(217,48,37,0.15); color: var(--blocked); }

  pre.lean, pre.code {
    background: var(--code-bg); border: 1px solid var(--border);
    border-radius: 6px; padding: 10px 12px;
    overflow-x: auto; font-size: 12.5px; line-height: 1.45;
    font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  }

  .sketch-step {
    display: flex; gap: 8px; padding: 5px 0;
    border-bottom: 1px dashed var(--border);
  }
  .sketch-step:last-child { border-bottom: none; }
  .sketch-step .icon { flex-shrink: 0; width: 18px; }
  .sketch-step .num { flex-shrink: 0; color: var(--fg-muted); width: 18px; }
  .sketch-step.current { background: rgba(245,158,11,0.08); margin: 0 -8px; padding: 5px 8px; border-radius: 4px; }
  .sketch-step .text { flex-grow: 1; }
  .sketch-step .closing-note { color: var(--fg-muted); font-size: 12px; margin-top: 2px; }

  .blocker-callout {
    background: var(--warn); border-left: 3px solid var(--warn-border);
    padding: 8px 12px; margin: 10px 0; border-radius: 0 4px 4px 0;
  }

  .progress-entries {
    background: var(--code-bg); border-radius: 4px; padding: 8px 12px;
    font-size: 12px; font-family: ui-monospace, monospace;
    max-height: 240px; overflow-y: auto;
  }
  .progress-entries .ts { color: var(--fg-muted); }

  ul.bullets { padding-left: 20px; margin: 4px 0; }
  ul.bullets li { margin: 2px 0; }

  kbd {
    background: var(--code-bg); border: 1px solid var(--border);
    border-bottom-width: 2px; border-radius: 3px;
    padding: 1px 5px; font-family: ui-monospace, monospace;
    font-size: 11px;
  }
  .help {
    font-size: 12px; color: var(--fg-muted); padding: 6px 14px;
    border-top: 1px solid var(--border); flex-shrink: 0;
    background: var(--bg-panel);
  }
  .help kbd { margin: 0 2px; }

  #search {
    width: calc(100% - 28px); margin: 0 14px 8px; padding: 6px 8px;
    border: 1px solid var(--border); border-radius: 4px;
    background: var(--bg); color: var(--fg);
    font-size: 13px;
  }
  #search:focus { outline: none; border-color: var(--accent); }
  .tree-node.hidden { display: none; }

  .empty-state {
    color: var(--fg-muted); padding: 40px 20px; text-align: center;
    font-size: 14px;
  }
</style>
</head>
<body>
<header>
  <h1 id="project-title">Loading…</h1>
  <div class="progress-bar"><div id="progress-fill" class="progress-fill" style="width: 0%"></div></div>
  <span id="progress-text" class="progress-text">— %</span>
  <div class="counts">
    <span><span class="badge" id="count-done">·</span> done</span>
    <span><span class="badge" id="count-in_progress">·</span> wip</span>
    <span><span class="badge" id="count-open">·</span> open</span>
    <span><span class="badge" id="count-blocked">·</span> blocked</span>
  </div>
  <div class="live-indicator">
    <span id="live-dot" class="live-dot"></span>
    <span id="live-text">connecting…</span>
  </div>
</header>
<main>
  <aside id="tree-pane">
    <input id="search" type="text" placeholder="Filter (e.g. T014, holomorph)" />
    <div id="tree"></div>
  </aside>
  <section id="detail-pane">
    <div class="empty-state">Loading project…</div>
  </section>
</main>
<div class="help">
  <kbd>↑</kbd><kbd>↓</kbd> move · <kbd>←</kbd><kbd>→</kbd> collapse / drill · <kbd>Enter</kbd> focus · <kbd>Esc</kbd> overview · <kbd>/</kbd> search · <kbd>r</kbd> refresh
</div>

<script>
const POLL_MS = 3000;
const ICONS = { done: "✅", in_progress: "🚧", open: "⏳", blocked: "🚨" };

let snapshot = null;
let visible = [];           // ordered list of {id, depth, expanded}
let selectedId = null;      // current cursor
let focusedId = null;       // what the right pane shows ('overview' = the project root)
let expanded = new Set();
let lastUpdate = 0;

async function fetchSnapshot() {
  try {
    const r = await fetch("/api/status");
    if (!r.ok) throw new Error("status " + r.status);
    const data = await r.json();
    snapshot = data;
    lastUpdate = Date.now();
    setLive(true);
    renderAll();
  } catch (e) {
    setLive(false, e.message);
  }
}

function setLive(ok, msg) {
  const dot = document.getElementById("live-dot");
  const text = document.getElementById("live-text");
  if (ok) {
    dot.classList.remove("stale");
    text.textContent = "live · " + new Date().toLocaleTimeString();
  } else {
    dot.classList.add("stale");
    text.textContent = "offline" + (msg ? " · " + msg : "");
  }
}

function renderAll() {
  if (!snapshot) return;
  document.getElementById("project-title").textContent = snapshot.title;
  const p = snapshot.progress;
  document.getElementById("progress-fill").style.width = p.percent + "%";
  document.getElementById("progress-text").textContent =
    p.percent + "% · " + p.done_weight + "/" + p.total_weight + " steps";
  document.getElementById("count-done").textContent = p.done_count;
  document.getElementById("count-in_progress").textContent = p.in_progress;
  document.getElementById("count-open").textContent = p.open;
  document.getElementById("count-blocked").textContent = p.blocked;

  if (selectedId === null) {
    // Auto-select the first in_progress ticket, else the first blocker, else first root
    const tickets = Object.values(snapshot.tickets);
    const inprog = tickets.find(t => t.status === "in_progress");
    const blocker = tickets.find(t => t.is_blocker);
    selectedId = (inprog && inprog.id) || (blocker && blocker.id) || snapshot.roots[0];
    focusedId = selectedId;
    // expand path to selected
    expandPathTo(selectedId);
  }

  renderTree();
  renderDetail();
  applySearchFilter();
  if (window.renderMathInElement) {
    window.renderMathInElement(document.body, { delimiters: [
      {left: "$$", right: "$$", display: true},
      {left: "$", right: "$", display: false}
    ]});
  }
  if (window.hljs) {
    document.querySelectorAll("pre.lean").forEach(b => {
      b.removeAttribute("data-highlighted");
      window.hljs.highlightElement(b);
    });
  }
}

function expandPathTo(id) {
  const parents = new Map();
  for (const [p, kids] of Object.entries(snapshot.children || {})) {
    for (const k of kids) parents.set(k, p);
  }
  let cur = id;
  while (cur && parents.has(cur)) {
    cur = parents.get(cur);
    expanded.add(cur);
  }
}

function statusOrder(t) {
  return { blocked: 0, in_progress: 1, open: 2, done: 3 }[t.status] ?? 4;
}

function sortChildren(ids) {
  return ids.slice().sort((a, b) => {
    const ta = snapshot.tickets[a], tb = snapshot.tickets[b];
    if (!ta || !tb) return 0;
    const oa = statusOrder(ta), ob = statusOrder(tb);
    if (oa !== ob) return oa - ob;
    return a.localeCompare(b);
  });
}

function buildVisible() {
  visible = [];
  function walk(id, depth) {
    const t = snapshot.tickets[id];
    if (!t) return;
    visible.push({ id, depth });
    if (expanded.has(id)) {
      const kids = sortChildren(snapshot.children[id] || []);
      for (const k of kids) walk(k, depth + 1);
    }
  }
  for (const r of snapshot.roots) walk(r, 0);
}

function renderTree() {
  buildVisible();
  const tree = document.getElementById("tree");
  tree.innerHTML = "";
  for (const { id, depth } of visible) {
    const t = snapshot.tickets[id];
    const node = document.createElement("div");
    node.className = "tree-node" + (id === selectedId ? " selected" : "");
    node.style.paddingLeft = (14 + depth * 14) + "px";
    node.dataset.id = id;
    const hasKids = (snapshot.children[id] || []).length > 0;
    const toggle = document.createElement("span");
    toggle.className = "toggle";
    toggle.textContent = hasKids ? (expanded.has(id) ? "▼" : "▶") : " ";
    const icon = document.createElement("span");
    icon.className = "icon";
    icon.textContent = ICONS[t.status] || "·";
    const idLabel = document.createElement("span");
    idLabel.className = "id-label";
    idLabel.textContent = id;
    const name = document.createElement("span");
    name.className = "name";
    name.textContent = t.math_name || t.title;
    node.append(toggle, icon, idLabel, name);
    if (t.is_blocker) {
      const tag = document.createElement("span");
      tag.className = "blocker-tag";
      tag.textContent = "BLOCKER";
      node.append(tag);
    }
    node.addEventListener("click", (e) => {
      if (e.target === toggle && hasKids) {
        toggleExpand(id);
      } else {
        selectedId = id;
        focusedId = id;
        renderTree();
        renderDetail();
      }
    });
    tree.append(node);
  }
}

function toggleExpand(id) {
  if (expanded.has(id)) expanded.delete(id);
  else expanded.add(id);
  renderTree();
}

function renderDetail() {
  const pane = document.getElementById("detail-pane");
  if (!focusedId) {
    pane.innerHTML = renderOverview();
  } else {
    const t = snapshot.tickets[focusedId];
    if (!t) { pane.innerHTML = renderOverview(); }
    else { pane.innerHTML = renderTicket(t); }
  }
  pane.scrollTop = 0;
}

function renderOverview() {
  const goal = snapshot.main_goal || "(no main goal in plan.md)";
  const p = snapshot.progress;
  return `
    <h2>${escapeHtml(snapshot.title)}</h2>
    <p style="font-size: 15px; line-height: 1.6;">${escapeHtml(goal)}</p>
    <div class="meta-row">
      <span><strong>Last updated:</strong> ${snapshot.last_updated}</span>
      <span><strong>Tickets:</strong> ${p.total_count}</span>
      ${p.off_track_flags > 0 ? `<span style="color: var(--blocked); font-weight: 600;">⚠ ${p.off_track_flags} off-track</span>` : ""}
    </div>
    <h4>Click a ticket on the left, or use ↑/↓ and Enter</h4>
  `;
}

function renderTicket(t) {
  const p = t.progress_entries || [];
  const sketch = t.sketch_steps || [];
  const live = t.live_context || {};
  return `
    <h2>${escapeHtml(t.id)} · ${escapeHtml(t.math_name || t.title)}</h2>
    <div class="meta-row">
      <span class="status-pill status-${t.status}">${escapeHtml(t.status.replace("_", " "))}</span>
      ${t.type ? `<span><strong>Type:</strong> ${escapeHtml(t.type)}</span>` : ""}
      ${t.depends_on.length ? `<span><strong>Depends on:</strong> ${t.depends_on.map(d => `<a href="#" data-jump="${d}">${escapeHtml(d)}</a>`).join(", ")}</span>` : ""}
      ${(snapshot.children[t.id] || []).length ? `<span><strong>Used by:</strong> ${snapshot.children[t.id].map(d => `<a href="#" data-jump="${d}">${escapeHtml(d)}</a>`).join(", ")}</span>` : ""}
    </div>

    ${t.is_blocker ? `<div class="blocker-callout"><strong>Blocker.</strong> ${blockerSummary(t)}</div>` : ""}

    ${live.drift_flags && live.drift_flags.length ? `
      <h4>Off-track flags</h4>
      <ul class="bullets">${live.drift_flags.map(f => `<li>${escapeHtml(f)}</li>`).join("")}</ul>
    ` : ""}

    <h3>Lean statement</h3>
    <pre class="lean">${escapeHtml(t.statement || "(no statement on file)")}</pre>

    ${live.live_signature && live.live_signature !== t.statement ? `
      <h4>Live signature in file</h4>
      <pre class="lean">${escapeHtml(live.live_signature)}</pre>
    ` : ""}

    ${sketch.length ? `
      <h3>Proof sketch — step by step</h3>
      <div>${sketch.map(s => renderStep(s)).join("")}</div>
    ` : `<p><em>No proof sketch on file. Run /develop --continue to refresh.</em></p>`}

    ${live.have_statements && live.have_statements.length ? `
      <h4>Auxiliary results in scope</h4>
      <ul class="bullets">${live.have_statements.map(h => `
        <li><code>${escapeHtml(h.name)}</code>${h.type_hint ? ` : <code>${escapeHtml(h.type_hint)}</code>` : ""}</li>
      `).join("")}</ul>
    ` : ""}

    ${t.mathlib_lemmas && t.mathlib_lemmas.length ? `
      <h4>Mathlib lemmas needed</h4>
      <ul class="bullets">${t.mathlib_lemmas.map(l => `<li>${escapeHtml(l)}</li>`).join("")}</ul>
    ` : ""}

    ${t.sources && t.sources.length ? `
      <h4>Sources</h4>
      <ul class="bullets">${t.sources.map(s => `<li>${escapeHtml(s)}</li>`).join("")}</ul>
    ` : ""}

    ${p.length ? `
      <h4>Progress timeline (${p.length} entries)</h4>
      <div class="progress-entries">${p.map(e =>
        `<div><span class="ts">${escapeHtml(e.timestamp || "·")}</span> — ${escapeHtml(e.note)}</div>`
      ).join("")}</div>
    ` : ""}
  `;
}

function renderStep(s) {
  const icon = { closed: "✅", current: "🚧", open: "⏳" }[s.step_status] || "·";
  return `
    <div class="sketch-step ${s.step_status === "current" ? "current" : ""}">
      <span class="icon">${icon}</span>
      <span class="num">${s.index}.</span>
      <div class="text">
        ${escapeHtml(s.text)}
        ${s.closing_note ? `<div class="closing-note">closed: ${escapeHtml(s.closing_note)}</div>` : ""}
        ${s.step_status === "current" ? `<div class="closing-note" style="color: var(--in-progress);">← currently being attempted</div>` : ""}
      </div>
    </div>
  `;
}

function blockerSummary(t) {
  const entries = t.progress_entries || [];
  if (!entries.length) return "Marked blocked but no progress notes on file.";
  const last = entries[entries.length - 1];
  return `Latest worker note: ${escapeHtml(last.note)}`;
}

function escapeHtml(s) {
  if (s == null) return "";
  return String(s)
    .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;").replace(/'/g, "&#39;");
}

function applySearchFilter() {
  const q = document.getElementById("search").value.trim().toLowerCase();
  if (!q) {
    document.querySelectorAll(".tree-node").forEach(n => n.classList.remove("hidden"));
    return;
  }
  document.querySelectorAll(".tree-node").forEach(n => {
    const id = n.dataset.id;
    const t = snapshot.tickets[id];
    const hay = (id + " " + (t.math_name || "") + " " + (t.title || "")).toLowerCase();
    n.classList.toggle("hidden", !hay.includes(q));
  });
}

document.getElementById("search").addEventListener("input", applySearchFilter);

document.addEventListener("click", e => {
  const a = e.target.closest("a[data-jump]");
  if (a) {
    e.preventDefault();
    selectedId = a.dataset.jump;
    focusedId = a.dataset.jump;
    expandPathTo(focusedId);
    renderTree();
    renderDetail();
  }
});

document.addEventListener("keydown", e => {
  if (e.target.tagName === "INPUT") {
    if (e.key === "Escape") { e.target.blur(); }
    return;
  }
  if (e.key === "/") {
    e.preventDefault();
    document.getElementById("search").focus();
    return;
  }
  if (e.key === "r") { fetchSnapshot(); return; }
  if (e.key === "Escape") {
    focusedId = null;
    renderDetail();
    return;
  }
  if (!visible.length) return;
  const idx = visible.findIndex(v => v.id === selectedId);
  if (e.key === "ArrowDown") {
    e.preventDefault();
    if (idx < visible.length - 1) selectedId = visible[idx + 1].id;
  } else if (e.key === "ArrowUp") {
    e.preventDefault();
    if (idx > 0) selectedId = visible[idx - 1].id;
  } else if (e.key === "ArrowRight") {
    e.preventDefault();
    const kids = snapshot.children[selectedId] || [];
    if (kids.length && !expanded.has(selectedId)) {
      expanded.add(selectedId);
    } else if (kids.length) {
      selectedId = sortChildren(kids)[0];
    }
  } else if (e.key === "ArrowLeft") {
    e.preventDefault();
    if (expanded.has(selectedId)) {
      expanded.delete(selectedId);
    } else if (idx > 0) {
      // find parent
      const parentDepth = visible[idx].depth - 1;
      for (let i = idx - 1; i >= 0; i--) {
        if (visible[i].depth === parentDepth) {
          selectedId = visible[i].id;
          break;
        }
      }
    }
  } else if (e.key === "Enter") {
    e.preventDefault();
    focusedId = selectedId;
    renderDetail();
  } else {
    return;
  }
  renderTree();
  // ensure selected is visible
  const sel = document.querySelector(".tree-node.selected");
  if (sel) sel.scrollIntoView({ block: "nearest" });
});

fetchSnapshot();
setInterval(fetchSnapshot, POLL_MS);
</script>
</body>
</html>
"""


if __name__ == "__main__":
    main()
