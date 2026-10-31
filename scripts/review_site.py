#!/usr/bin/env python3
"""Reviews on the Tau Ceti review site for declarations an agent checks as part of other work:
Voyager's full-statement test, the red team's correctness audit (mathlib-quality).

  site                       the Tau Ceti commit the site shows
  check NAME...              ON-SITE or MISSING for each name (Tau Ceti's own declarations only)
  reviews NAME...            the answers each declaration has had so far, and their reasons
  standard NAME... [--json]  the standard review of each declaration, the one text the site shows for it: its
                             version and text, the AI agents that approved it and the checks they made, how many
                             approved an earlier text, the reasons of the AI yeses of the earlier form recorded
                             since, and the noes still open. --json prints {NAME: {"version": V|null, "text": T,
                             "unfolded": [{"by", "at", "text"}], "noes": [{"by", "at", "category", "text", "url"}]}},
                             and null for a name the site does not have
  hash FILE                  the version of the text in FILE: what an approval or an edit names
  guide                      what a standard review is: the section of AI-REVIEWS.md that defines it
  post ACTIONS --agent A     approvals, writes and edits of standard reviews: ACTIONS (below) as lines in comments
      --commit SHA           on the site's bulk issue, as many as hold them, each starting with the agent line and
      [--note TEXT]          TEXT (default: "Reviews of declarations checked at Tau Ceti <SHA, 12 digits>.").
      [--drafts FILE]        Checks first, and posts nothing unless every action passes. --dry-run prints the
      [--dry-run]            comments instead
  no WHYFILE --agent A       a problem, "not correctly stated", as its own issue, with the reasons
      --decl NAME            in WHYFILE; the site must be at SHA. Prints `issue <number> <url>`
      --commit SHA --category AXIS [--involvement I] [--dry-run]

An AI agent's yes is an approval of the declaration's standard review (`guide`): it approves the text the site
shows, edits it, or writes the first one, with the eight checks it made, and gives no reasons of its own. A no, a
problem, is its own issue. ACTIONS is a JSONL file, an action a line:

  {"approve": DECL, "version": V, "cells": {AXIS: "checked"|"na", ...}}
  {"write": DECL, "cells": {...}, "text": TEXT}
  {"edit": DECL, "parent": V, "cells": {...}, "note": WHAT, "dropped": [{"item": I, "why": W}], "text": TEXT}

`cells` has all eight checks of the rubric: object, convention, edge-cases, junk, vacuous, choice, generality,
naming. `version` and `parent` are 8 to 16 hex digits of the version the site shows now (`standard`), or of the text
of a draft in DRAFTS, a JSONL of actions posted just before, for a text the site does not show yet. `dropped` says
why an edit leaves out a reference, test or Check of the text it replaces. `post` refuses, with the reasons on
stderr and nothing posted: a name the site does not have; cells that are not all eight; a text without its three
parts in order, or one that the intake would read cut short; a version that is not the site's or a draft's; a
declaration written or edited twice in the file; an action longer than a comment; and a site not at SHA, so that
each review is of the version that was checked. A long batch goes in several comments, split between actions, each
of at most COMMENT_CAP characters.

A is the agent, "TOOL, MODEL[, session S]" ("Voyager, claude-fable-5-1"): the reviews show on the
site as that AI agent's, via the account `gh` is signed in as. MODEL is the model exactly as the
harness names it ("claude-opus-5-5", "GPT-6 Astra"), never its family ("Opus", "GPT-6"), which is
refused: the site shows it beside each answer, and readers weigh the answer by it. What deserves a yes or a no is
decided by the skills (skills/voyager/SKILL.md section 8, commands/redteam.md R6), never here;
this only checks, formats and posts. `no` runs evidence-store through `uvx`; I, the account's
relation to Tau Ceti (outsider, contributor, author), is read from Tau Ceti's history when not
given.

Exit codes: 0 done; 1 refused (a name, a version or a commit the site does not have, or an action not
complete, with the reasons on stderr); 2 error.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.request

SITE = os.environ.get("REVIEW_SITE", "https://cbirkbeck.github.io/tauceti-reviewed-by-test/")
REPO = os.environ.get("REVIEW_SITE_REPO", "CBirkbeck/tauceti-reviewed-by-test")
EVIDENCE_STORE = os.environ.get("REVIEW_SITE_EVIDENCE_STORE",
                                "git+https://github.com/LeanTrustBuilders/evidence-store@v0.7.2")
#: The axes a problem can name (the store's rubric, ltb-rubric/1), and `other`.
AXES = ["object", "convention", "edge-cases", "junk", "vacuous", "choice", "generality", "naming", "other"]
#: The rubric's eight checks, in the order the lines of the bulk issue list them: an approval, a write and an edit
#: carry all of them.
RUBRIC = AXES[:-1]
#: What a cell says of a check: it was made, or does not apply (`n/a` as the lines of the bulk issue also write it).
CELL_STATES = {"checked": "checked", "na": "na", "n/a": "na"}
#: The parts of a standard review's text, each heading a line of its own, in this order (the site's standard.py).
HEADINGS = ("## What it says", "## References and tests", "## Lean subtleties")
#: What an action of `post` has besides the key that names its kind and its declaration.
FIELDS = {"approve": {"version", "cells"}, "write": {"cells", "text"},
          "edit": {"parent", "cells", "note", "dropped", "text"}}
#: A version, or at least 8 of its leading hex digits.
VERSION = re.compile(r"[0-9a-f]{8,16}")
#: A line that starts a command of the bulk issue, as the intake reads one (the site's standard_intake.py): a review's
#: block, which OPEN and CLOSE fence, ends before the next.
COMMAND = re.compile(r"^\s*(Approve|Write|Edit|Restore|Reviewed-by|Test|Named|Challenge)\s*:\s*(.*?)\s*$")
OPEN, CLOSE = "~~~review", "~~~"
#: What ends a field of a line of the bulk issue: a spaced em dash, or `--`.
FIELD_SEP = re.compile(r"\s+(?:—|--)\s+")
#: The section of AI-REVIEWS.md that defines a standard review.
GUIDE_BEGIN, GUIDE_END = "<!-- standard-review:begin -->", "<!-- standard-review:end -->"
#: A GitHub comment holds 65,536 characters; a longer batch goes in several comments.
COMMENT_CAP = 60000
LIBRARY = "TauCetiProject/TauCeti"


def die(msg, code):
    print(msg, file=sys.stderr)
    sys.exit(code)


def fetch(url):
    """The text at ``url``."""
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read().decode("utf-8-sig")


def get(path):
    """The site's data, past the Pages cache: a build may be minutes old."""
    url = f"{SITE}data/{path}?t={time.time():.0f}"
    try:
        return json.loads(fetch(url))
    except Exception as e:  # noqa: BLE001 - any failure to read the site is an error, not a verdict
        die(f"error: cannot read {url}: {e}", 2)


def normalize(text):
    """The text as its version is taken: `\\r\\n` and `\\r` as `\\n`, no whitespace at the end of a line, and no newline
    before the first line or after the last. A copy of the function of the same name in the site's scripts/standard.py:
    the vector in tests/test_review_site.py pins the two equal."""
    lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    return "\n".join(line.rstrip() for line in lines).strip("\n")


def version_of(text):
    """The version a text is: the first 16 hex digits of the SHA-256 of its normalized form (the site's, as above)."""
    return hashlib.sha256(normalize(text).encode("utf-8")).hexdigest()[:16]


def fnv(name, shards):
    """The site's shard of a name: FNV-1a over UTF-16 code units (its web/data.js)."""
    h, data = 0x811C9DC5, name.encode("utf-16-le")
    for i in range(0, len(data), 2):
        h = ((h ^ (data[i] | data[i + 1] << 8)) * 0x01000193) & 0xFFFFFFFF
    return h % shards


def on_site(meta, name):
    """Whether the site has a page for ``name`` as one of Tau Ceti's own declarations."""
    ids = [r[0] for r in get(f"names/{fnv(name, meta['shards']['names'])}.json") if r[1] == name]
    if not ids:
        return False
    n = meta["shards"]["nodes"]
    return get(f"nodes/{ids[0] // n}.json")[ids[0] % n][2] & 1 == 1


def at_commit(meta, sha):
    commit = meta["library"]["commit"]
    if sha and not commit.startswith(sha):
        die(f"refused: the site shows Tau Ceti at {commit[:12]}, not {sha[:12]}. Review only the "
            "version you checked: wait for the site, or leave these reviews for a later run.", 1)
    return commit


# A model's family, not the model: "GPT-6", "Opus 5", "Claude". (scripts/redteam.py has the same.)
FAMILY = re.compile(r"^(gpt|claude|opus|sonnet|haiku|fable|gemini|codex)[-\s]?(\d+(\.\d+)?)?$", re.I)


def agent_mark(agent):
    parts = [p.strip() for p in agent.split(",") if p.strip()]
    if len(parts) < 2:
        die("error: --agent is 'TOOL, MODEL[, session S]'", 2)
    if FAMILY.match(parts[1]):
        die("error: --agent's MODEL, %r, is a family, not a model: give the model exactly as your harness "
            "names it (GPT-6 Astra, not GPT-6; claude-opus-5-5, not Opus)" % parts[1], 2)
    fields = [f"tool={parts[0]}", f"model={parts[1]}"]
    if len(parts) > 2:
        fields.append("session=" + parts[2].removeprefix("session").strip())
    return "<!-- agent: " + "; ".join(fields) + " -->"


def gh(*args, body=None):
    io = {"input": body} if body is not None else {"stdin": subprocess.DEVNULL}
    r = subprocess.run(["gh", *args], capture_output=True, text=True, **io)
    if r.returncode:
        die(f"error: gh {' '.join(args[:3])}: {r.stderr.strip()}", 2)
    return r.stdout.strip()


def cmd_site(a):
    print(get("meta.json")["library"]["commit"])


def cmd_check(a):
    meta = get("meta.json")
    print("site at", meta["library"]["commit"])
    missing = [n for n in a.names if not on_site(meta, n)]
    for n in a.names:
        print("MISSING" if n in missing else "ON-SITE", n)
    sys.exit(1 if missing else 0)


def answers_on(meta, name):
    """The record views the site shows for ``name``: a declaration of the library's from its module's file,
    any other from upstream.json. None if the site has no such declaration."""
    ids = [r[0] for r in get(f"names/{fnv(name, meta['shards']['names'])}.json") if r[1] == name]
    if not ids:
        return None
    n = meta["shards"]["nodes"]
    node = get(f"nodes/{ids[0] // n}.json")[ids[0] % n]
    if node[2] & 1 and node[3] >= 0:
        entry = next((e for e in get(f"m/{node[3]}.json")["decls"] if e["id"] == ids[0]), {})
        return entry.get("records") or []
    return (get("upstream.json").get(name) or {}).get("records") or []


def cmd_reviews(a):
    meta = get("meta.json")
    print("site at", meta["library"]["commit"])
    for name in a.names:
        views = answers_on(meta, name)
        if views is None:
            print(f"\n{name}: the site has no such declaration")
            continue
        answers = [v for v in views if v.get("kind") == "review" and v.get("inForce")
                   and v.get("verdict") in ("accept", "problem")]
        print(f"\n{name}: {len(answers)} answer{'' if len(answers) == 1 else 's'}")
        for v in answers:
            word = "yes" if v["verdict"] == "accept" else "no"
            when = "" if v.get("applies", True) else " (an earlier version)"
            state = "" if word == "yes" else f" [{v.get('state', '')}]"
            what = v.get("text") or (f"{v['std']} the standard review" if v.get("std") else "(no reasons)")
            print(f"- {word}{state}{when}, {v['by']['label']}, {v['at'][:10]}: {what}")


def label(v):
    """Who made a record view, or a standard review's entry: its reviewer's label."""
    return (v.get("by") or {}).get("label", "")


def need_standard(meta):
    """How many shards of `standard/` the site has; exit 2 for a site built before the standard review."""
    n = (meta.get("shards") or {}).get("standard")
    if not n:
        die("error: the site does not show standard reviews yet (its meta.json has no shards.standard)", 2)
    return n


def standard_of(meta, name):
    """The standard review the site shows for ``name`` (its entry in standard/<k>.json), or None while it has none."""
    return get(f"standard/{fnv(name, need_standard(meta))}.json").get(name)


def earlier_form(v):
    """Whether record view ``v`` is an AI agent's yes of the earlier form: an accept by an agent that is no record of
    the standard review (those carry `std`, and no text)."""
    return (v.get("kind") == "review" and v.get("verdict") == "accept" and (v.get("by") or {}).get("kind") == "agent"
            and not v.get("std"))


def unfolded(views, since):
    """The reasons of the AI agents' yeses of the earlier form, in force, recorded after ``since``: oldest first."""
    mine = sorted((v for v in views if earlier_form(v) and v.get("inForce", True) and v.get("at", "") > since),
                  key=lambda v: v["at"])
    return [{"by": label(v), "at": v["at"], "text": v.get("text") or ""} for v in mine]


def open_noes(views):
    """The noes still open, oldest first."""
    mine = sorted((v for v in views if v.get("kind") == "review" and v.get("verdict") == "problem"
                   and v.get("state") == "open" and v.get("inForce", True)), key=lambda v: v.get("at", ""))
    return [{"by": label(v), "at": v.get("at", ""), "category": v.get("category"), "text": v.get("text") or "",
             "url": v.get("url") or ""} for v in mine]


def cells_line(cells):
    """Cells as the lines of the bulk issue list them: a check alone when it was made, `check n/a` when it does not
    apply, in the rubric's order."""
    return ", ".join(a if cells[a] == "checked" else f"{a} n/a" if cells[a] == "na" else f"{a}={cells[a]}"
                     for a in RUBRIC if a in cells)


def indent(text):
    return "\n".join("    " + line for line in text.strip("\n").split("\n")) if text.strip() else "    (no reasons)"


def describe(name, review, found):
    """What `standard` prints of a declaration: its standard review, if it has one, and what an editor may want."""
    out = [f"== {name}"]
    if review is None:
        out.append("no standard review yet")
    else:
        now = "current" if review["current"] else "written for an earlier version of the declaration"
        approvers = review["approvers"]
        out += [f"version {review['version']} ({now})",
                f"written {review['at'][:10]} by {label(review)}"
                + (", approving it" if review["approving"] else ", which approves nothing") + f"  {review['url']}",
                f"approved by {len(approvers)} AI agent{'' if len(approvers) == 1 else 's'}, latest first:"
                if approvers else "approved by no AI agent"]
        out += [f"- {label(x)}, {x['at'][:10]}: {cells_line(x.get('checked') or {})}  {x.get('url', '')}"
                for x in approvers]
        out += [f"earlier approvals: {review['earlier']} (of other texts, or of the earlier form)",
                OPEN, review["text"].strip("\n"), CLOSE]
    since = " since this version" if review else ""
    out.append(f"yeses of the earlier form{since}, with their reasons:" if found["unfolded"]
               else f"yeses of the earlier form{since}: none")
    for u in found["unfolded"]:
        out += [f"- {u['by']}, {u['at'][:10]}", indent(u["text"])]
    out.append("noes still open:" if found["noes"] else "noes still open: none")
    for n in found["noes"]:
        out += [f"- {n['by']}, {n['at'][:10]}" + (f", {n['category']}" if n["category"] else "") + f"  {n['url']}",
                indent(n["text"])]
    return "\n".join(out)


def cmd_standard(a):
    meta = get("meta.json")
    need_standard(meta)
    shown, missing = {}, False
    for name in a.names:
        views = answers_on(meta, name)
        if views is None:
            shown[name], missing = None, True
            if not a.json:
                print(f"== {name}\nthe site has no such declaration\n")
            continue
        review = standard_of(meta, name)
        shown[name] = {"version": review["version"] if review else None, "text": review["text"] if review else "",
                       "unfolded": unfolded(views, review["at"] if review else ""), "noes": open_noes(views)}
        if not a.json:
            print(describe(name, review, shown[name]) + "\n")
    if a.json:
        print(json.dumps(shown, indent=2, ensure_ascii=False))
    sys.exit(1 if missing else 0)


def cmd_hash(a):
    try:
        with open(a.file, encoding="utf-8", newline="") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError) as e:
        die(f"error: cannot read {a.file}: {e}", 2)
    print(version_of(text))


def guide_section():
    """The section of AI-REVIEWS.md, in the site's repository, that defines a standard review."""
    url = f"https://raw.githubusercontent.com/{REPO}/main/AI-REVIEWS.md"
    try:
        text = fetch(url)
    except Exception as e:  # noqa: BLE001 - as `get`
        die(f"error: cannot read {url}: {e}", 2)
    start = text.find(GUIDE_BEGIN)
    stop = text.find(GUIDE_END, start) if start >= 0 else -1
    if stop < 0:
        die(f"error: {url} has no section between {GUIDE_BEGIN} and {GUIDE_END}", 2)
    return text[start + len(GUIDE_BEGIN):stop].strip("\n")


def cmd_guide(a):
    print(guide_section())


def one_line(text):
    return " ".join(text.split())


def cell_problems(cells):
    """Why ``cells`` is not the rubric's eight checks, each `checked` or `na`, as sentences; none when it is."""
    if not isinstance(cells, dict):
        return ["cells: give all eight checks, " + ", ".join(RUBRIC) + ", each `checked` or `na`"]
    out = [f"cells: `{a}` is not a check of the rubric, whose checks are {', '.join(RUBRIC)}"
           for a in cells if a not in RUBRIC]
    out += [f"cells: `{a}` is {cells[a]!r}, and a check is `checked` or `na`" for a in RUBRIC
            if a in cells and not (isinstance(cells[a], str) and cells[a] in CELL_STATES)]
    missing = [a for a in RUBRIC if a not in cells]
    return out + ([f"cells: every check needs a cell; missing {', '.join(missing)}"] if missing else [])


def text_problems(text):
    """Why ``text`` is not the three parts of a standard review, each under its heading, in order, and none empty, as
    sentences; none when it is (the site's `parts`, in scripts/standard.py)."""
    found, before = [], []
    for line in normalize(text).split("\n"):
        if line in HEADINGS:
            found.append((line, []))
        else:
            (found[-1][1] if found else before).append(line)
    names = [heading for heading, _ in found]
    out = [f"there is text before `{HEADINGS[0]}`: every line must be in one of the three parts"] \
        if "".join(before).strip() else []
    for heading in HEADINGS:
        if heading not in names:
            out.append(f"the part `{heading}` is missing")
        elif names.count(heading) > 1:
            out.append(f"the part `{heading}` comes {names.count(heading)} times: it must come once")
    if len(set(names)) == len(names) and names != sorted(names, key=HEADINGS.index):
        out.append("the parts are out of order: they must come as " + ", ".join(f"`{h}`" for h in HEADINGS))
    return out + [f"the part `{heading}` is empty: if there is nothing to say, say so in a line (`None.`)"
                  for heading, body in found if not "\n".join(body).strip("\n")]


def block_whole(text):
    """Whether the intake reads ``text`` back whole from its block. It closes a block at the last `~~~` line before the
    next command line, so a text with a command line after a `~~~` line of its own is cut there; and it does not close
    a block with a `~~~review` line before its first `~~~` line (`closing` in the site's scripts/standard_intake.py)."""
    lines = f"{OPEN}\n{text}\n{CLOSE}".splitlines()
    end = None
    for j in range(1, len(lines)):
        line = lines[j].rstrip()
        if line == CLOSE:
            end = j
        elif end is None and line == OPEN:
            return False
        elif end is not None and COMMAND.match(line):
            break
    return end == len(lines) - 1


def body_problems(text):
    """Why ``text``, the whole text of a write or an edit, cannot be posted as it is."""
    if not isinstance(text, str):
        return ["its text is missing: give the whole text"]
    return text_problems(text) or ([] if block_whole(normalize(text)) else [
        f"its text would be read cut short: after a `{CLOSE}` line of its own it has a line that starts like an "
        f"action (`Test:`, `Edit:`...), or it has a `{OPEN}` line before its first `{CLOSE}` line"])


def edit_problems(f):
    """Why the note of an edit, and what it says it drops, are not as they should be."""
    out = [] if isinstance(f.get("note"), str) and f["note"].strip() else ["note: say what the edit adds or changes"]
    dropped = f.get("dropped", [])
    if not isinstance(dropped, list) or not all(isinstance(d, dict) for d in dropped):
        return out + ['dropped: a list of {"item": ..., "why": ...}']
    for d in dropped:
        item, why = d.get("item"), d.get("why")
        if not isinstance(item, str) or not item.strip():
            out.append("dropped: every entry needs its item")
        elif FIELD_SEP.search(one_line(item)):
            out.append(f"dropped: the item `{item}` holds a spaced dash, which would end its field: leave the dash out")
        if not isinstance(why, str) or not why.strip():
            out.append(f"dropped: say why {item!r} is dropped, in `why`")
    return out


def version_problems(field, given, name, current, drafts):
    """Why ``given``, the `field` of an approval or an edit of ``name``, names no version: the one the site shows now
    (``current``, or None) or one that a draft has (``drafts``, their hashes)."""
    given = given.strip().lower() if isinstance(given, str) else ""
    if not VERSION.fullmatch(given):
        return [f"{field}: give the version, 8 to 16 hex digits (`standard` shows it, `hash` computes one)"]
    known = ([current] if current else []) + drafts
    if any(v.startswith(given) for v in known):
        return []
    if not known:
        return ["the site shows no standard review of it yet, and no draft is given: write the first one"]
    which = ([f"the site's current version, {current}"] if current else []) \
        + ([f"the hash of a draft ({', '.join(drafts)})"] if drafts else [])
    return [f"{field} {given} is not {' or '.join(which)}: read the text the site shows now (`standard {name}`), "
            "review it, and post again"]


def read_actions(path):
    """The actions of the JSONL file ``path``, each as its line, kind, declaration and the other fields it gives; exit 2
    for a file that is not one."""
    try:
        with open(path, encoding="utf-8-sig", newline="") as f:
            rows = f.read().split("\n")
    except (OSError, UnicodeDecodeError) as e:
        die(f"error: cannot read {path}: {e}", 2)
    out = []
    for k, line in enumerate(rows, 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except ValueError as e:
            die(f"error: {path}:{k}: not JSON: {e}", 2)
        kinds = [x for x in FIELDS if isinstance(row, dict) and x in row]
        if len(kinds) != 1:
            die(f"error: {path}:{k}: an action is a JSON object with one of the keys {', '.join(FIELDS)}", 2)
        out.append({"line": k, "kind": kinds[0], "decl": row[kinds[0]],
                    "fields": {x: v for x, v in row.items() if x != kinds[0]}})
    return out


def action_problems(act, site_has, site_version, drafted):
    """Why ``act`` cannot be posted as it is, as sentences; none when it can. ``site_has(name)`` says whether the site
    has a page for a declaration, ``site_version(name)`` gives the version of its standard review that the site shows
    (or None), and ``drafted`` has the versions of the texts in the drafts, by declaration."""
    kind, name, f = act["kind"], act["decl"], act["fields"]
    if not isinstance(name, str) or not name.strip():
        return [f"`{kind}` names a declaration: give its full name"]
    out = [f"`{x}` is not a field of {kind}, which has {', '.join(sorted(FIELDS[kind]))}"
           for x in f if x not in FIELDS[kind]]
    on = site_has(name)
    if not on:
        out.append("it is not one of Tau Ceti's declarations on the site (`check` says which are)")
    out += cell_problems(f.get("cells"))
    out += body_problems(f.get("text")) if kind != "approve" else []
    out += edit_problems(f) if kind == "edit" else []
    if on and kind != "write":
        field = "version" if kind == "approve" else "parent"
        out += version_problems(field, f.get(field), name, site_version(name), sorted(drafted.get(name, ())))
    return out


def lines_of(act):
    """The lines of the bulk issue for ``act``, which passed `action_problems`: its command line, and for a write or an
    edit the `Dropped:` lines and the block, with the text as its version is taken."""
    kind, name, f = act["kind"], act["decl"], act["fields"]
    cells = cells_line({a: CELL_STATES[s] for a, s in f["cells"].items()})
    if kind == "approve":
        lines = [f"Approve: {name} — {f['version'].strip()} — {cells}"]
    elif kind == "write":
        lines = [f"Write: {name} — {cells}"]
    else:
        lines = [f"Edit: {name} — {f['parent'].strip()} — {cells} — {one_line(f['note'])}"]
        lines += [f"Dropped: {one_line(d['item'])} — {one_line(d['why'])}" for d in f.get("dropped") or []]
    if kind != "approve":
        lines += [OPEN, normalize(f["text"]), CLOSE]
    return "\n".join(lines) + "\n"


def check_actions(actions, meta, drafted, head):
    """``actions`` checked against the site: the reasons any cannot be posted, as lines that name the action; and, if
    there are none, the declaration and the lines of each. A comment starts with ``head``."""
    pages, versions = {}, {}

    def site_has(name):
        if name not in pages:
            pages[name] = on_site(meta, name)
        return pages[name]

    def site_version(name):
        if name not in versions:
            versions[name] = (standard_of(meta, name) or {}).get("version")
        return versions[name]

    problems, chunks, changed = [], [], set()
    for act in actions:
        name = act["decl"] if isinstance(act["decl"], str) else ""
        why = action_problems(act, site_has, site_version, drafted)
        if act["kind"] != "approve" and name:
            if name in changed:
                why.append("a comment changes the review of a declaration once, and this file changes it again")
            changed.add(name)
        if not why:
            lines = lines_of(act)
            if len(head) + len(lines) > COMMENT_CAP:
                why.append(f"its lines are {len(lines):,} characters, and a comment holds {COMMENT_CAP:,} with the "
                           "agent line and the note: shorten the text")
            chunks.append((name, lines))
        problems += [f"line {act['line']}" + (f" ({name})" if name else "") + f": {w}" for w in why]
    return problems, chunks


def comments_of(head, chunks):
    """The comments that carry ``chunks`` (each a declaration and the lines of its action), in order and split between
    actions: each starts with ``head`` and holds as many as fit in COMMENT_CAP characters. A list of chunks for each."""
    out, size = [[]], len(head)
    for chunk in chunks:
        if out[-1] and size + len(chunk[1]) > COMMENT_CAP:
            out.append([])
            size = len(head)
        out[-1].append(chunk)
        size += len(chunk[1])
    return out


def cmd_post(a):
    mark, note = agent_mark(a.agent), one_line(a.note)
    if COMMAND.match(note):
        die("error: --note is a line before the actions, and must not start like one (Approve:, Write:, Edit:...)", 2)
    if not a.commit:
        die("error: --commit is the Tau Ceti commit you checked", 2)
    actions = read_actions(a.actions)
    if not actions:
        die("error: no actions in " + a.actions, 2)
    drafted = {}  # the versions of the texts in the drafts (an approval has none), by declaration
    for d in read_actions(a.drafts) if a.drafts else []:
        if isinstance(d["decl"], str) and isinstance(d["fields"].get("text"), str):
            drafted.setdefault(d["decl"], set()).add(version_of(d["fields"]["text"]))
    meta = get("meta.json")
    need_standard(meta)
    commit = at_commit(meta, a.commit)
    head = mark + "\n" + (note or f"Reviews of declarations checked at Tau Ceti {commit[:12]}.") + "\n"
    problems, chunks = check_actions(actions, meta, drafted, head)
    if problems:
        die("refused, and nothing was posted:\n" + "\n".join("- " + p for p in problems), 1)
    comments = comments_of(head, chunks)
    bulk = str((meta.get("store") or {}).get("bulk", 1))
    for k, group in enumerate(comments, 1):
        text = head + "".join(lines for _, lines in group)
        if a.dry_run:
            print(text)
            continue
        try:
            print(gh("issue", "comment", bulk, "-R", REPO, "--body-file", "-", body=text), flush=True)
        except SystemExit:
            left = [name for rest in comments[k - 1:] for name, _ in rest]
            print(f"{k - 1} of {len(comments)} comments were posted; not posted: {', '.join(left)}", file=sys.stderr)
            raise
    print(f"{len(chunks)} action{'' if len(chunks) == 1 else 's'} in {len(comments)} comment"
          f"{'' if len(comments) == 1 else 's'}{' (dry run)' if a.dry_run else ''}", file=sys.stderr)


def cmd_no(a):
    if a.category not in AXES:
        die("error: --category is one of " + ", ".join(AXES), 2)
    why = open(a.why, encoding="utf-8").read().strip()
    if not why:
        die("error: the reasons file is empty", 2)
    meta = get("meta.json")
    commit = at_commit(meta, a.commit)
    if not on_site(meta, a.decl):
        die(f"refused: the site has no page for {a.decl}", 1)
    uvx = shutil.which("uvx") or os.path.expanduser("~/.local/bin/uvx")
    cmd = [uvx, "--from", EVIDENCE_STORE, "evidence-store", "submit", "--repo", REPO, "--decl", a.decl,
           "--commit", commit, "--verdict", "problem", "--category", a.category, "--rationale", why,
           "--agent", a.agent, "--involvement", a.involvement or involvement()] + (["--dry-run"] if a.dry_run else [])
    try:
        r = subprocess.run(cmd, capture_output=True, text=True)
    except OSError as e:
        die(f"error: evidence-store needs uv ({e})", 2)
    if r.returncode:
        die("error: evidence-store submit: " + (r.stderr or r.stdout).strip(), 2)
    out = r.stdout.strip()
    m = re.search(r"/issues/(\d+)\s*$", out)
    print(f"issue {m.group(1)} {out}" if m else out)


def involvement():
    """contributor if the signed-in account has commits in Tau Ceti, else outsider. Never author: an
    agent does not review what its account wrote (the skills say so)."""
    login = gh("api", "user", "-q", ".login")
    return "contributor" if gh("api", f"repos/{LIBRARY}/commits?author={login}&per_page=1",
                               "-q", "length") not in ("", "0") else "outsider"


def main(argv):
    p = argparse.ArgumentParser(prog="review_site.py", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("site").set_defaults(fn=cmd_site)
    q = sub.add_parser("check")
    q.add_argument("names", nargs="+")
    q.set_defaults(fn=cmd_check)
    q = sub.add_parser("reviews")
    q.add_argument("names", nargs="+")
    q.set_defaults(fn=cmd_reviews)
    q = sub.add_parser("standard")
    q.add_argument("names", nargs="+")
    q.add_argument("--json", action="store_true")
    q.set_defaults(fn=cmd_standard)
    q = sub.add_parser("hash")
    q.add_argument("file")
    q.set_defaults(fn=cmd_hash)
    sub.add_parser("guide").set_defaults(fn=cmd_guide)
    q = sub.add_parser("post")
    q.add_argument("actions")
    q.add_argument("--agent", required=True)
    q.add_argument("--commit", required=True)
    q.add_argument("--note", default="")
    q.add_argument("--drafts", default="")
    q.add_argument("--dry-run", action="store_true")
    q.set_defaults(fn=cmd_post)
    q = sub.add_parser("no")
    q.add_argument("why")
    q.add_argument("--agent", required=True)
    q.add_argument("--decl", required=True)
    q.add_argument("--commit", required=True)
    q.add_argument("--category", required=True)
    q.add_argument("--involvement", choices=["outsider", "contributor", "author"])
    q.add_argument("--dry-run", action="store_true")
    q.set_defaults(fn=cmd_no)
    a = p.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main(sys.argv[1:])
