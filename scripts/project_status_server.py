#!/usr/bin/env python3
"""Live mathematical-status dashboard for /develop projects.

Source of truth is the project's `.lean` code, NOT the ticket file. Every
declaration (theorem/lemma/def/abbrev/instance/structure/inductive) is
discovered, its dependencies inferred from the references in its body, and
its status (done / has-sorry) read off the source. Tickets, if present, are
matched by name and provide a status-overlay hint (open / in_progress /
blocked).

The mathematical un-formalisation (English math name, description, proof-state
narrative) is the agent's job. The agent writes its un-formalisation to
`.mathlib-quality/.status_annotations.json` on each `/project-status` run;
the server merges that sidecar into every snapshot it serves. Without
annotations the dashboard renders the raw Lean signatures as a fallback —
useful but unscalable, hence the agent's role.

The server itself is pure stdlib: no LLM calls, no mathlib search.

Usage:
    python3 project_status_server.py            # start on first free port from 8765
    python3 project_status_server.py --port N   # specific port
    python3 project_status_server.py --stop     # kill any running instance
    python3 project_status_server.py --status   # print URL if running
    python3 project_status_server.py --json     # one-shot snapshot to stdout
    python3 project_status_server.py --structure  # one-shot structural snapshot, agent-friendly

The slash command launches the server in the background and opens a browser.
A PID file lives at `.mathlib-quality/.status_server.pid`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import socket
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
ANNOTATIONS_FILE = MQ_DIR / ".status_annotations.json"

# Directories never to recurse into when scanning .lean files.
SKIP_DIRS = {".lake", ".git", "build", "node_modules", ".mathlib-quality", ".venv", "__pycache__"}

# Top-level Lean declaration kinds we surface in the dashboard.
DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "noncomputable def", "noncomputable abbrev",
    "instance", "structure", "inductive", "class", "opaque",
)


# ---------------------------------------------------------------------------
# Plan parsing
# ---------------------------------------------------------------------------


def parse_plan() -> dict:
    if not PLAN_FILE.exists():
        return {"title": ROOT.name or "Project", "main_goal": ""}
    text = PLAN_FILE.read_text(encoding="utf-8")
    title_match = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    title = title_match.group(1).strip() if title_match else (ROOT.name or "Project")
    main_goal = ""
    for para in re.split(r"\n\s*\n", text)[1:]:
        stripped = para.strip()
        if stripped and not stripped.startswith("#"):
            main_goal = stripped
            break
    return {"title": title, "main_goal": main_goal}


# ---------------------------------------------------------------------------
# Lean file discovery + parsing
# ---------------------------------------------------------------------------


def walk_lean_files() -> list[Path]:
    files = []
    for p in ROOT.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in p.parts):
            continue
        if p.name == "lakefile.lean":
            continue
        files.append(p)
    return sorted(files)


_DECL_HEAD_RE = re.compile(
    r"""^
    (?P<indent>\s*)
    (?P<attrs>(?:@\[[^\]]*\]\s*)*)
    (?P<modifiers>(?:(?:private|protected|noncomputable|partial|unsafe|abbrev)\s+)*)
    (?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)
    \b
    \s*
    (?P<name>[\w'.]+)?
    """,
    re.VERBOSE,
)

# Lighter detector — used on every line during block-extraction so we know
# when one declaration ends and the next begins. Top-level declarations live
# at column 0 (no leading whitespace).
_TOP_DECL_LINE_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\b"
)

_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$")
_NAMESPACE_CLOSE_RE = re.compile(r"^\s*end\s+([\w.]+)?\s*$")
_SECTION_OPEN_RE = re.compile(r"^\s*section\b")

_LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
# Block comments are nestable in Lean; we only strip the easy single-level case.
_BLOCK_COMMENT_RE = re.compile(r"/-(?:[^-]|-(?!/))*?-/", re.DOTALL)

_HAVE_RE = re.compile(
    r"^\s*have\s+(?P<name>\w+)\s*(?::\s*(?P<type>.+?))?\s*:=", re.MULTILINE
)
_HAVE_TACTIC_RE = re.compile(
    r"^\s*have\s+(?P<name>\w+)\s*:\s*(?P<type>.+?)\s*:=\s*by", re.MULTILINE
)


def _strip_comments(text: str) -> str:
    """Remove line comments and (single-level) block comments. Preserves
    line numbering by keeping newlines intact."""
    def repl_block(m):
        return "\n" * m.group(0).count("\n")
    text = _BLOCK_COMMENT_RE.sub(repl_block, text)
    text = _LINE_COMMENT_RE.sub("", text)
    return text


def _build_namespace_stack(lines: list[str], up_to: int) -> list[str]:
    stack: list[str] = []
    for i in range(up_to):
        line = lines[i]
        m = _NAMESPACE_OPEN_RE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = _NAMESPACE_CLOSE_RE.match(line)
        if m:
            ns = m.group(1)
            if ns and stack and stack[-1] == ns:
                stack.pop()
            elif ns:
                # close out a nested namespace by name
                if ns in stack:
                    while stack and stack[-1] != ns:
                        stack.pop()
                    if stack:
                        stack.pop()
            else:
                # bare `end` closes a section, which we don't track separately
                pass
    return stack


def _qualify(name: str, ns_stack: list[str]) -> str:
    if not ns_stack:
        return name
    return ".".join(ns_stack) + "." + name


def parse_lean_file(path: Path) -> list[dict]:
    """Return a list of declaration dicts for one .lean file."""
    try:
        raw = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    stripped = _strip_comments(raw)
    lines = stripped.splitlines()
    raw_lines = raw.splitlines()
    decl_starts: list[int] = []
    for i, line in enumerate(lines):
        if _TOP_DECL_LINE_RE.match(line):
            decl_starts.append(i)
    decls: list[dict] = []
    for i, start in enumerate(decl_starts):
        # End at the next top-level decl, or end of file
        end_excl = decl_starts[i + 1] if i + 1 < len(decl_starts) else len(lines)
        block_lines = lines[start:end_excl]
        raw_block_lines = raw_lines[start:end_excl]
        # Trim trailing blank lines from the block
        while block_lines and not block_lines[-1].strip():
            block_lines.pop()
            raw_block_lines.pop()
            end_excl -= 1
        body_text = "\n".join(block_lines)
        raw_body_text = "\n".join(raw_block_lines)
        first_line = block_lines[0]
        m = _DECL_HEAD_RE.match(first_line)
        if not m or not m.group("name"):
            continue
        local_name = m.group("name")
        kind = m.group("kind")
        modifiers = m.group("modifiers") or ""
        is_private = "private" in modifiers
        ns_stack = _build_namespace_stack(lines, start)
        full_name = _qualify(local_name, ns_stack)
        # Compute signature: from start through the first `:=` or `where` token.
        signature, body_after = _split_sig_and_body(body_text)
        sorry_lines_in_block = [
            i for i, ln in enumerate(block_lines) if re.search(r"\bsorry\b", ln)
        ]
        sorry_abs_lines = [start + offset + 1 for offset in sorry_lines_in_block]
        haves = _extract_haves(body_after)
        body_hash = hashlib.sha256(raw_body_text.encode("utf-8")).hexdigest()[:16]
        decls.append({
            "name": full_name,
            "local_name": local_name,
            "kind": kind,
            "is_private": is_private,
            "file_path": str(path.relative_to(ROOT)),
            "line_range": [start + 1, end_excl],
            "lean_signature": signature.strip(),
            "lean_body_excerpt": body_after[:1200],  # capped for transport
            "lean_body_full": raw_body_text,         # the agent reads this for un-formalisation
            "has_sorry": bool(sorry_abs_lines),
            "sorry_lines": sorry_abs_lines,
            "haves": haves,
            "body_hash": body_hash,
            "namespace": ".".join(ns_stack),
        })
    return decls


def _split_sig_and_body(text: str) -> tuple[str, str]:
    """Cut a declaration block into (signature, body). The signature is
    everything up to and including the first `:= by`, `:=`, or `where` at
    depth 0 (outside parens/brackets)."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            if text[i:i + 5] == ":= by":
                return text[: i + 5], text[i + 5 :]
            if text[i:i + 2] == ":=":
                return text[: i + 2], text[i + 2 :]
            if text[i:i + 5] == "where" and (i + 5 == n or not text[i + 5].isalnum()):
                return text[: i + 5], text[i + 5 :]
        i += 1
    return text, ""


def _extract_haves(body: str) -> list[dict]:
    seen = set()
    haves = []
    for m in _HAVE_RE.finditer(body):
        name = m.group("name")
        if name in seen:
            continue
        seen.add(name)
        haves.append({"name": name, "type_hint": (m.group("type") or "").strip()})
    return haves


# ---------------------------------------------------------------------------
# Reference extraction (dependency graph from proof bodies)
# ---------------------------------------------------------------------------


_IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b")
_LEAN_KEYWORDS = frozenset({
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive",
    "class", "opaque", "private", "protected", "noncomputable", "partial",
    "unsafe", "by", "do", "if", "then", "else", "match", "with", "fun", "let",
    "have", "show", "from", "where", "in", "of", "if", "then", "else",
    "namespace", "end", "section", "open", "import", "variable", "variables",
    "true", "false", "True", "False", "fun", "λ", "rfl", "sorry", "this",
    "intro", "intros", "exact", "apply", "refine", "rw", "rewrite", "simp",
    "ring", "linarith", "omega", "tauto", "assumption", "trivial",
    "constructor", "cases", "rcases", "obtain", "use", "exists", "forall",
    "Type", "Sort", "Prop", "Nat", "Int", "Real", "Bool", "Unit", "List",
    "Option", "Array", "String", "Char", "And", "Or", "Not", "Iff", "Eq",
})


def extract_references(body: str, decl_index: dict[str, set[str]], own_name: str) -> list[str]:
    """Return the project-internal declaration names referenced in `body`.

    `decl_index` maps each fully-qualified name to a set of suffix forms
    that, when seen as identifiers, refer to it (e.g. "MyProj.fooBar"
    matches "MyProj.fooBar", "fooBar", any namespace-qualified prefix).
    """
    if not body:
        return []
    refs: set[str] = set()
    body = _strip_comments(body)
    for m in _IDENT_RE.finditer(body):
        token = m.group(0)
        if token in _LEAN_KEYWORDS:
            continue
        # Direct full-name match
        if token in decl_index["full_names"]:
            if token != own_name:
                refs.add(token)
            continue
        # Suffix match (just the local name)
        targets = decl_index["by_suffix"].get(token)
        if targets:
            for t in targets:
                if t != own_name:
                    refs.add(t)
                    break  # ambiguous suffixes pick the first; fine for v1
    return sorted(refs)


def build_decl_index(decls: list[dict]) -> dict:
    full_names = set(d["name"] for d in decls)
    by_suffix: dict[str, list[str]] = {}
    for d in decls:
        local = d["local_name"]
        by_suffix.setdefault(local, []).append(d["name"])
        # Also index every dotted suffix (so "MyProj.A.foo" is matched by
        # "A.foo" and "foo")
        parts = d["name"].split(".")
        for i in range(1, len(parts)):
            suffix = ".".join(parts[i:])
            by_suffix.setdefault(suffix, []).append(d["name"])
    return {"full_names": full_names, "by_suffix": by_suffix}


# ---------------------------------------------------------------------------
# Tickets — minor role: status overlay only
# ---------------------------------------------------------------------------


_TICKET_HEADING_RE = re.compile(r"^###\s+\[([^\]]+)\]\s*(.*)$", re.MULTILINE)
_DECL_NAME_IN_LEAN_RE = re.compile(
    r"\b(?:theorem|lemma|def|abbrev|instance|noncomputable\s+def)\s+([\w'.]+)"
)


def parse_tickets() -> list[dict]:
    if not TICKETS_FILE.exists():
        return []
    text = TICKETS_FILE.read_text(encoding="utf-8")
    boundaries = [(m.start(), m.group(1).strip(), m.group(2).strip())
                  for m in _TICKET_HEADING_RE.finditer(text)]
    tickets = []
    for i, (start, tid, title) in enumerate(boundaries):
        end = boundaries[i + 1][0] if i + 1 < len(boundaries) else len(text)
        body = text[start:end]
        status_m = re.search(r"^-\s+\*\*Status\*\*:\s*([a-z_]+)", body, re.MULTILINE)
        statement_m = re.search(r"```lean\s*\n(.*?)\n```", body, re.DOTALL)
        names: list[str] = []
        if statement_m:
            for nm in _DECL_NAME_IN_LEAN_RE.finditer(statement_m.group(1)):
                names.append(nm.group(1))
        progress_entries = []
        prog_m = re.search(r"\*\*Progress\*\*:\s*\n(.*?)(?=\n###\s|\Z)", body, re.DOTALL)
        if prog_m:
            for line in prog_m.group(1).splitlines():
                line = line.strip()
                if line.startswith("- "):
                    progress_entries.append(line[2:])
        tickets.append({
            "id": tid,
            "title": title,
            "status": status_m.group(1) if status_m else "open",
            "decl_names": names,
            "progress_entries": progress_entries,
        })
    return tickets


# ---------------------------------------------------------------------------
# Annotations sidecar
# ---------------------------------------------------------------------------


def load_annotations() -> dict:
    if not ANNOTATIONS_FILE.exists():
        return {}
    try:
        return json.loads(ANNOTATIONS_FILE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


# ---------------------------------------------------------------------------
# Snapshot assembly
# ---------------------------------------------------------------------------


# In-memory caches keyed by file path.
_FILE_CACHE: dict[str, tuple[float, list[dict]]] = {}


def get_decls_cached(path: Path) -> list[dict]:
    try:
        mtime = path.stat().st_mtime
    except OSError:
        _FILE_CACHE.pop(str(path), None)
        return []
    cached = _FILE_CACHE.get(str(path))
    if cached and cached[0] == mtime:
        return cached[1]
    decls = parse_lean_file(path)
    _FILE_CACHE[str(path)] = (mtime, decls)
    return decls


def collect_decls() -> list[dict]:
    all_decls = []
    for path in walk_lean_files():
        all_decls.extend(get_decls_cached(path))
    return all_decls


def overlay_tickets(decls: list[dict], tickets: list[dict]) -> dict[str, dict]:
    decl_by_name = {d["name"]: d for d in decls}
    decl_by_local = {d["local_name"]: d for d in decls}
    overlay: dict[str, dict] = {}  # decl_name -> ticket_info
    for t in tickets:
        for nm in t["decl_names"]:
            target = decl_by_name.get(nm) or decl_by_local.get(nm)
            if target:
                overlay[target["name"]] = {
                    "ticket_id": t["id"],
                    "ticket_title": t["title"],
                    "ticket_status": t["status"],
                    "progress_entries": t["progress_entries"],
                }
    return overlay


def compute_status(decl: dict, ticket_info: dict) -> str:
    """Status taxonomy for the dashboard:
    - done           : no sorry in body
    - in_progress    : has sorry, ticket says in_progress, OR has any progress entries
    - blocked        : has sorry, ticket says blocked
    - open           : has sorry, ticket says open
    - has_sorry_no_ticket : has sorry, no ticket assigned (unticketed work)
    """
    if not decl["has_sorry"]:
        return "done"
    if not ticket_info:
        return "has_sorry_no_ticket"
    ts = ticket_info.get("ticket_status", "open")
    if ts == "done":
        # Ticket says done but file still has sorry — flag as off-track.
        return "blocked"
    return ts


def build_snapshot() -> dict:
    plan = parse_plan()
    decls = collect_decls()
    if not decls:
        return _empty_snapshot(plan)
    decl_index = build_decl_index(decls)
    tickets = parse_tickets()
    overlay = overlay_tickets(decls, tickets)
    annotations = load_annotations()
    annotations_decls = annotations.get("declarations", {}) if isinstance(annotations, dict) else {}

    # Build dependency edges
    children: dict[str, list[str]] = {d["name"]: [] for d in decls}
    for d in decls:
        deps = extract_references(d["lean_body_full"], decl_index, d["name"])
        d["depends_on"] = deps
        for dep in deps:
            children[dep].append(d["name"])
    for d in decls:
        d["depended_on_by"] = sorted(children[d["name"]])

    # Apply ticket overlay + computed status
    for d in decls:
        ti = overlay.get(d["name"], {})
        d["ticket_id"] = ti.get("ticket_id")
        d["ticket_title"] = ti.get("ticket_title")
        d["ticket_status"] = ti.get("ticket_status")
        d["progress_entries"] = ti.get("progress_entries", [])
        d["status"] = compute_status(d, ti)
        # Merge annotations (the agent's un-formalisation)
        ann = annotations_decls.get(d["name"]) or annotations_decls.get(d["local_name"]) or {}
        d["math_name"] = ann.get("math_name")
        d["description"] = ann.get("description")
        d["proof_state_english"] = ann.get("proof_state_english")
        d["ingredients_in_scope"] = ann.get("ingredients_in_scope")
        d["what_would_help"] = ann.get("what_would_help")
        d["annotated_at"] = ann.get("annotated_at")
        d["annotation_stale"] = bool(ann) and ann.get("body_hash") not in (d["body_hash"], None)
        d["has_annotation"] = bool(ann)
        # Drop heavy fields from per-decl payload
        d.pop("lean_body_full", None)

    # Roots = decls that nothing else uses (the user-facing theorems / outputs)
    roots = sorted([d["name"] for d in decls if not children[d["name"]]
                    and not d["name"].endswith("_aux")
                    and d["kind"] in ("theorem", "lemma")
                    and not d["is_private"]])
    if not roots:
        # Fall back to "decls with no parents AND not used elsewhere" or just everything terminal
        roots = sorted([d["name"] for d in decls if not children[d["name"]]])

    progress = compute_progress(decls)
    annotations_age = _annotations_age(annotations)
    annotations_complete = (
        bool(annotations_decls) and
        all(d.get("has_annotation") and not d.get("annotation_stale") for d in decls
            if d["status"] != "done" or d["depended_on_by"])  # everything user-facing should be annotated
    )

    return {
        "title": plan["title"],
        "main_goal_lean": plan["main_goal"],
        "main_goal_english": annotations.get("project_goal_english", ""),
        "main_decls": annotations.get("project_main_decls", []) or roots[:3],
        "progress": progress,
        "decls": {d["name"]: d for d in decls},
        "children": children,
        "roots": roots,
        "annotations_present": bool(annotations_decls),
        "annotations_complete": annotations_complete,
        "annotations_age_seconds": annotations_age,
        "annotations_generated_at": annotations.get("generated_at"),
        "last_updated": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


def _annotations_age(annotations: dict) -> int | None:
    gen = annotations.get("generated_at")
    if not gen:
        return None
    try:
        t = datetime.fromisoformat(gen.replace("Z", "+00:00"))
        return int((datetime.now(timezone.utc) - t).total_seconds())
    except (ValueError, TypeError):
        return None


def _empty_snapshot(plan: dict) -> dict:
    return {
        "title": plan["title"],
        "main_goal_lean": plan["main_goal"],
        "main_goal_english": "",
        "main_decls": [],
        "progress": {
            "total": 0, "done": 0, "in_progress": 0, "blocked": 0,
            "open": 0, "has_sorry_no_ticket": 0, "percent": 0,
        },
        "decls": {},
        "children": {},
        "roots": [],
        "annotations_present": False,
        "annotations_complete": False,
        "annotations_age_seconds": None,
        "annotations_generated_at": None,
        "last_updated": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


def compute_progress(decls: list[dict]) -> dict:
    total = len(decls)
    counts = {"done": 0, "in_progress": 0, "blocked": 0, "open": 0, "has_sorry_no_ticket": 0}
    for d in decls:
        counts[d["status"]] = counts.get(d["status"], 0) + 1
    percent = round(100 * counts["done"] / total) if total else 0
    return {
        "total": total,
        "done": counts["done"],
        "in_progress": counts["in_progress"],
        "blocked": counts["blocked"],
        "open": counts["open"],
        "has_sorry_no_ticket": counts["has_sorry_no_ticket"],
        "percent": percent,
    }


# ---------------------------------------------------------------------------
# Structural-only one-shot (for the agent to consume cheaply)
# ---------------------------------------------------------------------------


def build_structural() -> dict:
    """Slim payload for the agent's un-formalisation pass: every declaration
    with its full Lean body, sorry positions, dependencies, ticket overlay.
    No annotations merged."""
    plan = parse_plan()
    decls = collect_decls()
    if not decls:
        return {"title": plan["title"], "decls": []}
    decl_index = build_decl_index(decls)
    tickets = parse_tickets()
    overlay = overlay_tickets(decls, tickets)
    children: dict[str, list[str]] = {d["name"]: [] for d in decls}
    out_decls = []
    for d in decls:
        deps = extract_references(d["lean_body_full"], decl_index, d["name"])
        d["depends_on"] = deps
        for dep in deps:
            children[dep].append(d["name"])
    for d in decls:
        ti = overlay.get(d["name"], {})
        out = {
            "name": d["name"],
            "local_name": d["local_name"],
            "kind": d["kind"],
            "file_path": d["file_path"],
            "line_range": d["line_range"],
            "namespace": d["namespace"],
            "is_private": d["is_private"],
            "lean_signature": d["lean_signature"],
            "lean_body_full": d["lean_body_full"],
            "has_sorry": d["has_sorry"],
            "sorry_lines": d["sorry_lines"],
            "haves": d["haves"],
            "depends_on": d["depends_on"],
            "depended_on_by": sorted(children[d["name"]]),
            "body_hash": d["body_hash"],
            "ticket_id": ti.get("ticket_id"),
            "ticket_status": ti.get("ticket_status"),
            "progress_entries": ti.get("progress_entries", []),
            "status": compute_status(d, ti),
        }
        out_decls.append(out)
    return {
        "title": plan["title"],
        "main_goal_lean": plan["main_goal"],
        "decls": out_decls,
    }


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self._send_html(DASHBOARD_HTML)
        elif self.path.startswith("/api/status"):
            try:
                self._send_json(build_snapshot())
            except Exception as exc:
                self._send_json({"error": str(exc)}, status=500)
        elif self.path.startswith("/api/structure"):
            try:
                self._send_json(build_structural())
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
    raise RuntimeError(f"No free port in range {start}-{start + span}")


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
            os.kill(pid, 15)
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
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--json", action="store_true",
                        help="one-shot full snapshot to stdout, no server")
    parser.add_argument("--structure", action="store_true",
                        help="one-shot structural snapshot for the agent, no server")
    args = parser.parse_args()

    if args.stop:
        print("stopped" if stop_existing() else "no server running")
        return

    if args.status:
        info = read_pid()
        if info and is_alive(info[0]):
            print(f"http://127.0.0.1:{info[1]}/")
        return

    if args.json:
        print(json.dumps(build_snapshot(), default=str, indent=2))
        return

    if args.structure:
        print(json.dumps(build_structural(), default=str, indent=2))
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
    --bg: #fafafa; --bg-panel: #fff; --border: #e2e2e2; --fg: #1d1d1f;
    --fg-muted: #6b6b70; --accent: #0066cc;
    --done: #34a853; --in-progress: #f59e0b; --open: #6b6b70;
    --blocked: #d93025; --unticketed: #8b5cf6;
    --hover: #f0f0f4; --selected: #e2eaff;
    --warn: #fff7e0; --warn-border: #f5d97f; --code-bg: #f5f5f7;
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
    flex-shrink: 0; flex-wrap: wrap;
  }
  header h1 {
    margin: 0; font-size: 16px; font-weight: 600;
    overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
    max-width: 500px;
  }
  .progress-bar {
    flex-grow: 1; max-width: 400px;
    height: 8px; background: var(--border); border-radius: 4px; overflow: hidden;
  }
  .progress-fill { height: 100%; background: var(--done); transition: width 0.5s; }
  .progress-text { font-variant-numeric: tabular-nums; color: var(--fg-muted); font-size: 13px; }
  .counts { display: flex; gap: 12px; font-size: 13px; flex-wrap: wrap; }
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
  @keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.4; } }

  .ann-banner {
    width: 100%; padding: 6px 18px;
    background: var(--warn); border-bottom: 1px solid var(--warn-border);
    color: var(--fg); font-size: 12px;
    display: flex; align-items: center; gap: 8px; flex-shrink: 0;
  }
  .ann-banner.hidden { display: none; }
  .ann-banner code {
    background: rgba(0,0,0,0.06); padding: 1px 5px; border-radius: 3px;
    font-family: ui-monospace, monospace;
  }

  main { flex-grow: 1; display: flex; min-height: 0; }
  #tree-pane {
    width: 38%; min-width: 280px; max-width: 520px;
    border-right: 1px solid var(--border); background: var(--bg-panel);
    overflow-y: auto; padding: 10px 0;
  }
  #detail-pane { flex-grow: 1; overflow-y: auto; padding: 18px 26px; }

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
  .tree-node .name { flex-grow: 1; word-break: break-word; }
  .tree-node .lean-name {
    font-family: ui-monospace, monospace;
    font-size: 11.5px; color: var(--fg-muted); margin-left: 4px;
  }

  h2 { font-size: 18px; margin: 0 0 6px; font-weight: 600; }
  h3 { font-size: 15px; margin: 18px 0 6px; font-weight: 600; }
  h4 { font-size: 13px; margin: 14px 0 4px; font-weight: 600;
       color: var(--fg-muted); text-transform: uppercase; letter-spacing: 0.05em; }
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
  .status-has_sorry_no_ticket { background: rgba(139,92,246,0.15); color: var(--unticketed); }

  pre.lean, pre.code {
    background: var(--code-bg); border: 1px solid var(--border);
    border-radius: 6px; padding: 10px 12px;
    overflow-x: auto; font-size: 12.5px; line-height: 1.45;
    font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  }
  details > summary {
    cursor: pointer; color: var(--fg-muted); font-size: 12px;
    padding: 4px 0;
  }
  details[open] > summary { color: var(--fg); }

  .placeholder {
    color: var(--fg-muted); font-style: italic;
    background: var(--code-bg); padding: 10px 12px; border-radius: 6px;
    border-left: 3px solid var(--warn-border);
  }

  ul.bullets { padding-left: 20px; margin: 4px 0; }
  ul.bullets li { margin: 2px 0; }

  kbd {
    background: var(--code-bg); border: 1px solid var(--border);
    border-bottom-width: 2px; border-radius: 3px;
    padding: 1px 5px; font-family: ui-monospace, monospace; font-size: 11px;
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
    background: var(--bg); color: var(--fg); font-size: 13px;
  }
  #search:focus { outline: none; border-color: var(--accent); }
  .tree-node.hidden { display: none; }

  .empty-state {
    color: var(--fg-muted); padding: 40px 20px; text-align: center;
    font-size: 14px;
  }

  .have-list { font-size: 12.5px; }
  .have-list code {
    background: var(--code-bg); padding: 1px 4px; border-radius: 3px;
    font-family: ui-monospace, monospace;
  }
  .progress-entries {
    background: var(--code-bg); border-radius: 4px; padding: 8px 12px;
    font-size: 12px; font-family: ui-monospace, monospace;
    max-height: 220px; overflow-y: auto;
  }
  .ref-link {
    color: var(--accent); text-decoration: none;
    font-family: ui-monospace, monospace; font-size: 12.5px;
  }
  .ref-link:hover { text-decoration: underline; }

  .file-tag {
    font-family: ui-monospace, monospace; font-size: 11px;
    color: var(--fg-muted);
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
    <span><span class="badge" id="count-unticketed">·</span> unticketed</span>
  </div>
  <div class="live-indicator">
    <span id="live-dot" class="live-dot"></span>
    <span id="live-text">connecting…</span>
  </div>
</header>
<div id="ann-banner" class="ann-banner hidden">
  <span id="ann-banner-text"></span>
</div>
<main>
  <aside id="tree-pane">
    <input id="search" type="text" placeholder="Filter declarations…" />
    <div id="tree"></div>
  </aside>
  <section id="detail-pane">
    <div class="empty-state">Loading project…</div>
  </section>
</main>
<div class="help">
  <kbd>↑</kbd><kbd>↓</kbd> move · <kbd>←</kbd><kbd>→</kbd> collapse / drill ·
  <kbd>Enter</kbd> focus · <kbd>Esc</kbd> overview ·
  <kbd>/</kbd> search · <kbd>r</kbd> refresh
</div>

<script>
const POLL_MS = 3000;
const ICONS = {
  done: "✅", in_progress: "🚧", open: "⏳", blocked: "🚨",
  has_sorry_no_ticket: "🟣"
};

let snapshot = null;
let visible = [];
let selectedId = null;
let focusedId = null;
let expanded = new Set();

async function fetchSnapshot() {
  try {
    const r = await fetch("/api/status");
    if (!r.ok) throw new Error("status " + r.status);
    snapshot = await r.json();
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
    p.percent + "% · " + p.done + "/" + p.total + " declarations";
  document.getElementById("count-done").textContent = p.done;
  document.getElementById("count-in_progress").textContent = p.in_progress;
  document.getElementById("count-open").textContent = p.open;
  document.getElementById("count-blocked").textContent = p.blocked;
  document.getElementById("count-unticketed").textContent = p.has_sorry_no_ticket;

  renderAnnBanner();

  if (selectedId === null) {
    const decls = Object.values(snapshot.decls);
    const wip = decls.find(d => d.status === "in_progress");
    const blocker = decls.find(d => d.status === "blocked");
    selectedId = (wip && wip.name) || (blocker && blocker.name) ||
                 (snapshot.roots[0]) || (decls[0] && decls[0].name);
    focusedId = null;  // start on the project overview
    if (selectedId) expandPathTo(selectedId);
  }

  renderTree();
  renderDetail();
  applySearchFilter();
  if (window.renderMathInElement) {
    window.renderMathInElement(document.getElementById("detail-pane"), {
      delimiters: [
        {left: "$$", right: "$$", display: true},
        {left: "$", right: "$", display: false}
      ],
      throwOnError: false
    });
  }
  if (window.hljs) {
    document.querySelectorAll("pre.lean").forEach(b => {
      b.removeAttribute("data-highlighted");
      window.hljs.highlightElement(b);
    });
  }
}

function renderAnnBanner() {
  const b = document.getElementById("ann-banner");
  const txt = document.getElementById("ann-banner-text");
  if (!snapshot.annotations_present) {
    b.classList.remove("hidden");
    txt.innerHTML = '⚠ No mathematical un-formalisation on file. ' +
      'Run <code>/project-status</code> in Claude Code to populate the math view. ' +
      'The dashboard is currently showing raw Lean signatures only.';
  } else if (!snapshot.annotations_complete) {
    b.classList.remove("hidden");
    const age = formatAge(snapshot.annotations_age_seconds);
    txt.innerHTML = '⚠ Un-formalisation is partial or stale (' + age + '). ' +
      'Re-run <code>/project-status</code> to refresh.';
  } else {
    const age = formatAge(snapshot.annotations_age_seconds);
    b.classList.remove("hidden");
    b.style.background = ""; b.style.borderColor = "";
    txt.innerHTML = 'Un-formalisation last refreshed ' + age + '. ' +
      'Re-run <code>/project-status</code> to refresh.';
  }
}

function formatAge(seconds) {
  if (seconds == null) return "never";
  if (seconds < 60) return seconds + "s ago";
  if (seconds < 3600) return Math.round(seconds / 60) + "m ago";
  if (seconds < 86400) return Math.round(seconds / 3600) + "h ago";
  return Math.round(seconds / 86400) + "d ago";
}

function expandPathTo(name) {
  const parents = new Map();
  for (const [parent, kids] of Object.entries(snapshot.children || {})) {
    for (const k of kids) parents.set(k, parent);
  }
  // Reverse: walk dependencies up to a root. Roots in our model are the
  // user-facing theorems; dependencies are below. So we expand from each
  // dependency back to the root that ultimately uses it.
  // For tree display we expand "users" — i.e., what uses this decl.
  const used_by = snapshot.decls[name] && snapshot.decls[name].depended_on_by;
  if (used_by && used_by.length) {
    expanded.add(used_by[0]);
    expandPathTo(used_by[0]);
  }
}

function statusOrder(s) {
  return { blocked: 0, in_progress: 1, has_sorry_no_ticket: 2, open: 3, done: 4 }[s] ?? 5;
}

function sortChildren(names) {
  return names.slice().sort((a, b) => {
    const da = snapshot.decls[a], db = snapshot.decls[b];
    if (!da || !db) return 0;
    const oa = statusOrder(da.status), ob = statusOrder(db.status);
    if (oa !== ob) return oa - ob;
    return a.localeCompare(b);
  });
}

function buildVisible() {
  visible = [];
  const seen = new Set();
  function walk(name, depth) {
    if (seen.has(name)) return;  // simple cycle guard
    seen.add(name);
    const d = snapshot.decls[name];
    if (!d) return;
    visible.push({ name, depth });
    if (expanded.has(name)) {
      const kids = sortChildren(d.depends_on || []);
      for (const k of kids) walk(k, depth + 1);
    }
  }
  for (const r of snapshot.roots) walk(r, 0);
}

function renderTree() {
  buildVisible();
  const tree = document.getElementById("tree");
  tree.innerHTML = "";
  for (const { name, depth } of visible) {
    const d = snapshot.decls[name];
    const node = document.createElement("div");
    node.className = "tree-node" + (name === selectedId ? " selected" : "");
    node.style.paddingLeft = (14 + depth * 14) + "px";
    node.dataset.name = name;
    const hasKids = (d.depends_on || []).length > 0;
    const toggle = document.createElement("span");
    toggle.className = "toggle";
    toggle.textContent = hasKids ? (expanded.has(name) ? "▼" : "▶") : " ";
    const icon = document.createElement("span");
    icon.className = "icon";
    icon.textContent = ICONS[d.status] || "·";
    const label = document.createElement("span");
    label.className = "name";
    if (d.math_name) {
      label.textContent = d.math_name;
      const ln = document.createElement("span");
      ln.className = "lean-name";
      ln.textContent = d.local_name;
      label.append(" ", ln);
    } else {
      label.textContent = d.local_name;
      label.className += " lean-name-only";
      label.style.fontFamily = "ui-monospace, monospace";
      label.style.fontSize = "12.5px";
    }
    node.append(toggle, icon, label);
    node.addEventListener("click", (e) => {
      if (e.target === toggle && hasKids) {
        toggleExpand(name);
      } else {
        selectedId = name;
        focusedId = name;
        renderTree();
        renderDetail();
      }
    });
    tree.append(node);
  }
}

function toggleExpand(name) {
  if (expanded.has(name)) expanded.delete(name);
  else expanded.add(name);
  renderTree();
}

function renderDetail() {
  const pane = document.getElementById("detail-pane");
  if (!focusedId || !snapshot.decls[focusedId]) {
    pane.innerHTML = renderOverview();
  } else {
    pane.innerHTML = renderDecl(snapshot.decls[focusedId]);
  }
  pane.scrollTop = 0;
  pane.querySelectorAll("a[data-jump]").forEach(a => {
    a.addEventListener("click", e => {
      e.preventDefault();
      const target = a.dataset.jump;
      if (snapshot.decls[target]) {
        selectedId = target;
        focusedId = target;
        expandPathTo(target);
        renderTree();
        renderDetail();
      }
    });
  });
}

function renderOverview() {
  const p = snapshot.progress;
  const goal = snapshot.main_goal_english
    ? `<p style="font-size: 15px; line-height: 1.6;">${escapeHtml(snapshot.main_goal_english)}</p>`
    : (snapshot.main_goal_lean
        ? `<p style="font-size: 14px; color: var(--fg-muted);">${escapeHtml(snapshot.main_goal_lean)}</p>
           <p class="placeholder">No mathematical un-formalisation of the goal on file. Run <code>/project-status</code> to populate.</p>`
        : `<p class="placeholder">No project goal recorded.</p>`);
  const mainList = (snapshot.main_decls || []).map(name => {
    const d = snapshot.decls[name];
    if (!d) return "";
    return `<li>${ICONS[d.status]} <a href="#" data-jump="${escapeHtml(name)}">${escapeHtml(d.math_name || d.local_name)}</a></li>`;
  }).join("");
  return `
    <h2>${escapeHtml(snapshot.title)}</h2>
    <div class="meta-row">
      <span><strong>Last updated:</strong> ${snapshot.last_updated}</span>
      <span><strong>Declarations:</strong> ${p.total}</span>
      ${p.has_sorry_no_ticket > 0 ? `<span style="color: var(--unticketed);">${p.has_sorry_no_ticket} unticketed sorries</span>` : ""}
    </div>
    ${goal}
    ${mainList ? `<h4>Top-level results</h4><ul class="bullets">${mainList}</ul>` : ""}
    <h4>How to navigate</h4>
    <p style="color: var(--fg-muted);">Click a declaration on the left, or use ↑/↓ and Enter. Top-level results sit at the top of the tree; their dependencies expand below. Math names come from the un-formalisation; if a node shows only a Lean identifier, that declaration is awaiting un-formalisation.</p>
  `;
}

function renderDecl(d) {
  const refLink = name => {
    if (snapshot.decls[name]) {
      const target = snapshot.decls[name];
      const display = target.math_name ? `${escapeHtml(target.math_name)} <span class="lean-name">${escapeHtml(target.local_name)}</span>` : `<code>${escapeHtml(target.local_name)}</code>`;
      return `<a href="#" data-jump="${escapeHtml(name)}" class="ref-link">${display}</a>`;
    }
    return `<code>${escapeHtml(name)}</code>`;
  };
  const annStale = d.annotation_stale ?
    `<div class="placeholder" style="margin-top:8px;">⚠ The un-formalisation below was generated against an older version of this declaration. Re-run <code>/project-status</code> to refresh.</div>` : "";
  const noAnn = !d.has_annotation ?
    `<div class="placeholder" style="margin-top:8px;">No mathematical un-formalisation on file for this declaration. The Lean signature below is the only available view. Run <code>/project-status</code> to populate.</div>` : "";

  const heading = d.math_name
    ? `<h2>${escapeHtml(d.math_name)} <span class="lean-name" style="font-size:14px;">${escapeHtml(d.local_name)}</span></h2>`
    : `<h2><code>${escapeHtml(d.local_name)}</code></h2>`;

  const description = d.description
    ? `<p style="font-size:14.5px; line-height:1.6;">${escapeHtml(d.description)}</p>`
    : "";

  const proofState = d.has_sorry && d.proof_state_english
    ? `<h3>Where the proof currently sits</h3><p>${escapeHtml(d.proof_state_english)}</p>`
    : (d.has_sorry
        ? `<h3>Where the proof currently sits</h3><p class="placeholder">No un-formalisation of the proof state on file. The signature has ${d.sorry_lines.length} sorry${d.sorry_lines.length === 1 ? "" : "s"} on lines ${d.sorry_lines.join(", ")} of <code>${escapeHtml(d.file_path)}</code>.</p>`
        : "");

  const ingredients = d.ingredients_in_scope && d.ingredients_in_scope.length
    ? `<h4>Ingredients in scope</h4><ul class="bullets">${d.ingredients_in_scope.map(s => `<li>${escapeHtml(s)}</li>`).join("")}</ul>`
    : "";

  const help = d.what_would_help && d.what_would_help.length
    ? `<h4>What would help</h4><ul class="bullets">${d.what_would_help.map(s => `<li>${escapeHtml(s)}</li>`).join("")}</ul>`
    : "";

  const haves = d.haves && d.haves.length
    ? `<details><summary>Auxiliary <code>have</code> statements (${d.haves.length})</summary><ul class="have-list bullets">${d.haves.map(h => `<li><code>${escapeHtml(h.name)}</code>${h.type_hint ? ` : <code>${escapeHtml(h.type_hint)}</code>` : ""}</li>`).join("")}</ul></details>`
    : "";

  const dependsLine = d.depends_on && d.depends_on.length
    ? `<div><strong>Depends on:</strong> ${d.depends_on.map(refLink).join(", ")}</div>` : "";
  const usedByLine = d.depended_on_by && d.depended_on_by.length
    ? `<div><strong>Used by:</strong> ${d.depended_on_by.map(refLink).join(", ")}</div>` : "";

  const ticketLine = d.ticket_id
    ? `<span><strong>Ticket:</strong> ${escapeHtml(d.ticket_id)} (${escapeHtml(d.ticket_status || "?")})</span>` : "";

  const progressTimeline = d.progress_entries && d.progress_entries.length
    ? `<h4>Worker progress (from ticket)</h4><div class="progress-entries">${d.progress_entries.map(e => `<div>${escapeHtml(e)}</div>`).join("")}</div>` : "";

  return `
    ${heading}
    <div class="meta-row">
      <span class="status-pill status-${d.status}">${escapeHtml(d.status.replace(/_/g, " "))}</span>
      <span class="file-tag">${escapeHtml(d.file_path)}:${d.line_range[0]}</span>
      <span><strong>${escapeHtml(d.kind)}</strong></span>
      ${ticketLine}
    </div>
    ${noAnn}${annStale}
    ${description}
    ${proofState}
    ${ingredients}
    ${help}
    <h3>Lean signature</h3>
    <pre class="lean">${escapeHtml(d.lean_signature || "(no signature)")}</pre>
    ${haves}
    <h4>Connections</h4>
    ${dependsLine || "<div><em>No internal dependencies inferred from the body.</em></div>"}
    ${usedByLine}
    ${progressTimeline}
  `;
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
    const name = n.dataset.name;
    const d = snapshot.decls[name];
    if (!d) { n.classList.add("hidden"); return; }
    const hay = (name + " " + (d.math_name || "") + " " + (d.local_name || "")).toLowerCase();
    n.classList.toggle("hidden", !hay.includes(q));
  });
}

document.getElementById("search").addEventListener("input", applySearchFilter);

document.addEventListener("keydown", e => {
  if (e.target.tagName === "INPUT") {
    if (e.key === "Escape") e.target.blur();
    return;
  }
  if (e.key === "/") { e.preventDefault(); document.getElementById("search").focus(); return; }
  if (e.key === "r") { fetchSnapshot(); return; }
  if (e.key === "Escape") { focusedId = null; renderDetail(); return; }
  if (!visible.length) return;
  const idx = visible.findIndex(v => v.name === selectedId);
  if (e.key === "ArrowDown") {
    e.preventDefault();
    if (idx < visible.length - 1) selectedId = visible[idx + 1].name;
  } else if (e.key === "ArrowUp") {
    e.preventDefault();
    if (idx > 0) selectedId = visible[idx - 1].name;
  } else if (e.key === "ArrowRight") {
    e.preventDefault();
    const d = snapshot.decls[selectedId];
    const kids = (d && d.depends_on) || [];
    if (kids.length && !expanded.has(selectedId)) expanded.add(selectedId);
    else if (kids.length) selectedId = sortChildren(kids)[0];
  } else if (e.key === "ArrowLeft") {
    e.preventDefault();
    if (expanded.has(selectedId)) expanded.delete(selectedId);
    else if (idx > 0) {
      const parentDepth = visible[idx].depth - 1;
      for (let i = idx - 1; i >= 0; i--) {
        if (visible[i].depth === parentDepth) { selectedId = visible[i].name; break; }
      }
    }
  } else if (e.key === "Enter") {
    e.preventDefault();
    focusedId = selectedId;
    renderDetail();
  } else { return; }
  renderTree();
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
