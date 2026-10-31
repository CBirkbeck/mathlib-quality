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
  astra-question NAME... --tauceti CHECKOUT --out FILE [--drafts FILE]
                             the question to put to GPT-6 Astra, in a `codex exec` call that has no file access, about
                             at most 12 of Tau Ceti's own declarations, whole in one file: the instructions (look for
                             errors in the Lean first and fill the eight cells; only then approve, edit or write the
                             standard review), the section `guide` prints, and for each declaration, numbered, its kind,
                             its Lean at the commit the site shows (`git -C CHECKOUT show COMMIT:PATH`: CHECKOUT must
                             have that commit, else exit 2), up to 12 of the statements it rests on, and the standard
                             review it has now with its version: the text of its last write or edit in DRAFTS if it has
                             one there, else the site's
  astra-answer ANSWER --question QFILE --out ACTIONS --noes NOES
                             Astra's answer to such a question, as the ACTIONS (below) that `post` takes, approvals,
                             edits and writes, and as NOES, a JSONL of {"decl", "category", "why"}, a no each, for
                             `no`. The versions are those the question showed, never the answer's. It never guesses: an
                             item it cannot read, whose cells are not all eight, that has an ERROR cell but is not a
                             NO, that is not one of the question's (by number and name), or whose lines do not fit
                             its verdict, is printed as `not filed: NAME: WHY` and left out
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
stderr and nothing posted: a declaration the site does not ask its question of (it asks it of Tau Ceti's own, and of
those outside the library in a module of Mathlib or another package it reviews); cells that are not all eight; a text
without its three parts in order, or one that the intake would read cut short; a version that is not the site's or a
draft's; a declaration written or edited twice in the file; an action longer than a comment; and a site not at SHA, so
that each review is of the version that was checked. A long batch goes in several comments, split between actions, each
of at most COMMENT_CAP characters.

Astra answers each item of a question, as the instructions in the question say, with its number and name, the eight
cells, a verdict, and the lines the verdict takes:

  ### N. NAME
  CELLS: object=checked, convention=checked, ..., choice=n/a, ..., naming=checked   (a cell may be `ERROR: WHY`)
  VERDICT: APPROVE          nothing more
  VERDICT: EDIT             NOTE: WHAT IT ADDS, any DROPPED: ITEM — WHY, and the whole new text in a block,
                            ~~~review ... ~~~
  VERDICT: WRITE            the block alone (for a declaration the question showed no standard review of)
  VERDICT: NO               CATEGORY: AXIS   WHY: THE ERROR (and an ERROR cell, which no other verdict has)

A is the agent, "TOOL, MODEL[, session S]" ("Voyager, claude-fable-5-1"): the reviews show on the
site as that AI agent's, via the account `gh` is signed in as. MODEL is the model exactly as the
harness names it ("claude-opus-5-5", "GPT-6 Astra"), never its family ("Opus", "GPT-6"), which is
refused: the site shows it beside each answer, and readers weigh the answer by it. What deserves a yes or a no is
decided by the skills (skills/voyager/SKILL.md section 8, commands/redteam.md R6), never here;
this only checks, formats and posts. `no` runs evidence-store through `uvx`; I, the account's
relation to Tau Ceti (outsider, contributor, author), is read from Tau Ceti's history when not
given.

Exit codes: 0 done; 1 refused (a name, a version or a commit the site does not have, an action not
complete, or a question of more than 12 declarations or of one that is not Tau Ceti's own, with the reasons on
stderr); 2 error (a checkout without the commit the site shows, among them).
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
#: What the site's kind codes (a node's second column, an entry's `k`) stand for (its web/data.js).
KINDS = {"t": "theorem", "d": "definition", "s": "structure", "c": "class", "n": "inductive", "i": "instance",
         "a": "axiom", "o": "opaque"}
#: A question to Astra holds at most QUESTION_MAX declarations, and shows at most RESTS_MAX statements that one rests
#: on.
QUESTION_MAX = RESTS_MAX = 12
#: Over this many bytes a question is longer than `codex exec` takes in one argument, which is how gate.sh passes it
#: (Linux limits an argument to 131,072 bytes).
QUESTION_WARN = 120_000
#: What `astra-answer` leaves of a comment for the agent line and the note `post` puts before the actions, so that it
#: files no action that `post` would refuse as longer than a comment.
ROOM = 1000
#: What a question says where a declaration has no standard review, and where the site shows no statement of one.
NO_REVIEW = "(no standard review yet: write one)"
NO_STATEMENT = "(the site shows no statement)"
#: The first line of a question, round a JSON object that names its items (their number, name and the version of the
#: review each shows): `astra-answer` takes the version of an approval or an edit from it, and never from the answer.
QUESTION_OPEN, QUESTION_CLOSE = "<!-- astra-question ", " -->"
#: What an answer to an item can be, and the lines each takes besides its cells and its verdict.
VERDICTS = {"APPROVE": set(), "EDIT": {"NOTE", "DROPPED", "BLOCK"}, "WRITE": {"BLOCK"}, "NO": {"CATEGORY", "WHY"}}
#: What each verdict needs besides its cells and its verdict.
NEEDS = {"APPROVE": set(), "EDIT": {"NOTE", "BLOCK"}, "WRITE": {"BLOCK"}, "NO": {"CATEGORY", "WHY"}}
#: What the lines of an item are called in its problems ("an APPROVE takes no NOTE", "an EDIT needs a NOTE").
PARTS = {"BLOCK": f"`{OPEN}` block of the whole text", "NOTE": "NOTE", "DROPPED": "DROPPED line",
         "CATEGORY": "CATEGORY", "WHY": "WHY"}
ARTICLE = {"APPROVE": "an APPROVE", "EDIT": "an EDIT", "WRITE": "a WRITE", "NO": "a NO"}
#: The heading of an item of an answer, `### 3. Name`, as a question numbers its items (any level of heading, and `3)`).
ITEM_HEADING = re.compile(r"^ {0,3}#{1,6}[ \t]*(\d+)[ \t]*[.)][ \t]*(.*?)[ \t]*$")
#: A rule between the items, or the fence of a code block that holds the whole answer: no line of an item.
RULE = re.compile(r"^(?:-{3,}|\*{3,}|_{3,}|`{3,}[\w+-]*)$")
#: A line of an item that starts one of its fields; the label may be in bold. A NOTE, a DROPPED line and a WHY go on
#: over the lines after them.
FIELD = re.compile(r"^(?:[-*+][ \t]+)?(?:\*\*|__)?(CELLS|VERDICT|NOTE|DROPPED|CATEGORY|WHY)(?:\*\*|__)?[ \t]*:"
                   r"(?:\*\*|__)?[ \t]*(.*?)[ \t]*$", re.I)
#: What a CATEGORY line holds: the check, and the WHY if it comes on the same line.
CATEGORY_LINE = re.compile(r"^([^\s,;]+)[,;]?\s*(?:WHY\s*:\s*(.*))?$", re.I | re.S)
#: Where a cell starts in a CELLS line: the name of a check, at the start or after a comma, and `=`.
CELL_KEY = re.compile(r"(?:^|,)[ \t]*(" + "|".join(AXES[:-1]) + r")[ \t]*=[ \t]*", re.I)


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


def reader():
    """``get`` that reads each file of the site once: a question meets the same module's file again and again."""
    seen = {}

    def read(path):
        if path not in seen:
            seen[path] = get(path)
        return seen[path]

    return read


def id_of(meta, name, read=None):
    """The site's id of the declaration ``name`` (its place in nodes/<k>.json), or None if it has no such declaration.
    ``read`` reads a file of the site (default `get`)."""
    ids = [r[0] for r in (read or get)(f"names/{fnv(name, meta['shards']['names'])}.json") if r[1] == name]
    return ids[0] if ids else None


def node_at(meta, i, read=None):
    """The site's row for the declaration with id ``i`` in nodes/<k>.json: [name, kind, flags, module index, title, two
    states, the ids of what it rests on, ...]. None if there is none."""
    n = meta["shards"]["nodes"]
    rows = (read or get)(f"nodes/{i // n}.json")
    return rows[i % n] if i % n < len(rows) else None


def node_of(meta, name, read=None):
    """The site's row for ``name`` in nodes/<k>.json: [name, kind, flags, module index, ...]. None if it has no such
    declaration."""
    i = id_of(meta, name, read)
    return None if i is None else node_at(meta, i, read)


def on_site(meta, name):
    """Whether the site has a page for ``name`` as one of Tau Ceti's own declarations."""
    node = node_of(meta, name)
    return node is not None and node[2] & 1 == 1


def why_not_asked(meta, name, modules):
    """Why the site does not ask its question of ``name``, or "" when it does. It asks it of Tau Ceti's own
    declarations, and of those outside the library in a module that is one of ``meta.review.outside`` (Mathlib) or
    under one: the site's `answerable`, in its scripts/site_data.py. ``modules()`` reads its modules.json, which names
    a declaration's module by the index its node holds (-1: none)."""
    node = node_of(meta, name)
    if node is None:
        return "the site has no page for it"
    if node[2] & 1:
        return ""
    outside = (meta.get("review") or {}).get("outside") or []
    rows = modules() if outside else []
    module = rows[node[3]][0] if 0 <= node[3] < len(rows) else ""
    if module and any(module == p or module.startswith(p + ".") for p in outside):
        return ""
    return ("the site has a page for it" + (f", in {module}," if module else ",")
            + " but asks its question only of Tau Ceti's own declarations"
            + (f" and those under {', '.join(outside)}" if outside else ""))


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


def standard_of(meta, name, read=None):
    """The standard review the site shows for ``name`` (its entry in standard/<k>.json), or None while it has none."""
    return (read or get)(f"standard/{fnv(name, need_standard(meta))}.json").get(name)


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


def action_problems(act, site_reason, site_version, drafted):
    """Why ``act`` cannot be posted as it is, as sentences; none when it can. ``site_reason(name)`` is why the site does
    not ask its question of a declaration ("" when it does), ``site_version(name)`` gives the version of its standard
    review that the site shows (or None), and ``drafted`` has the versions of the drafts' texts, by declaration."""
    kind, name, f = act["kind"], act["decl"], act["fields"]
    if not isinstance(name, str) or not name.strip():
        return [f"`{kind}` names a declaration: give its full name"]
    out = [f"`{x}` is not a field of {kind}, which has {', '.join(sorted(FIELDS[kind]))}"
           for x in f if x not in FIELDS[kind]]
    asked = site_reason(name)
    if asked:
        out.append(asked)
    out += cell_problems(f.get("cells"))
    out += body_problems(f.get("text")) if kind != "approve" else []
    out += edit_problems(f) if kind == "edit" else []
    if not asked and kind != "write":
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
    reasons, versions, modules = {}, {}, []

    def site_modules():
        if not modules:
            modules.extend(get("modules.json"))
        return modules

    def site_reason(name):
        if name not in reasons:
            reasons[name] = why_not_asked(meta, name, site_modules)
        return reasons[name]

    def site_version(name):
        if name not in versions:
            versions[name] = (standard_of(meta, name) or {}).get("version")
        return versions[name]

    problems, chunks, changed = [], [], set()
    for act in actions:
        name = act["decl"] if isinstance(act["decl"], str) else ""
        why = action_problems(act, site_reason, site_version, drafted)
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


# --- Astra's review: the question, and its answer ---------------------------------------------------------------

#: What Astra is told: it is given no file, so the question holds everything. The names in braces are filled in. The
#: four examples are each an item of an answer, which `astra-answer` reads (a test files them).
INSTRUCTIONS = """\
You are reviewing {count} declaration{s} of Tau Ceti, a Lean 4 library of mathematics, for the Tau Ceti review site. You
cannot open files or the web: everything you need is in this message.

The site asks one question of a declaration: is it correctly stated? It is when it says what it should: it is the
intended notion, or states the intended result, as its name, its docstring and the literature say. The question is not
whether its proof is right, which Lean checks.

For each declaration below, in this order:

1. Look for errors in the Lean first. Read its source and the statements it rests on, work out what it should say, and
   run the eight checks of the site's rubric against that:

   | check | it passes when |
   |---|---|
   | `object` | it is the intended notion, or states the intended result, and not a different one |
   | `convention` | it follows the source's conventions: normalisation, indexing, signs, and the instances it picks up |
   | `edge-cases` | it decides degenerate and boundary inputs as the source does |
   | `junk` | no default value outside the intended domain changes what it means |
   | `vacuous` | it is neither vacuous nor trivial |
   | `choice` | it makes no arbitrary choice where the intended object is canonical |
   | `generality` | it is as general as the source |
   | `naming` | its name and docstring do not mislead |

   Give each check a cell: `checked` (you made the check and found nothing wrong), `n/a` (the check cannot fail for this
   declaration, such as `choice` where nothing is chosen) or `ERROR: <why>` (you found an error).

2. If any cell is an ERROR, answer `VERDICT: NO`, with the line `CATEGORY: <check>   WHY: <the error>`. The category
   is the check that fails, or `other`. The people who decide whether to fix it read the WHY: at most about 120 words of
   plain sentences. First say what is wrong: which hypothesis, term or claim, what it says and what it should say. Then
   give the evidence: a case where it fails, or the source it disagrees with, and the Lean names involved. Check first
   that it is not just Lean's convention: a definition may take an odd value where the classical notion is undefined
   (`x / 0 = 0`), and is correctly stated when it agrees with the classical notion under the hypotheses the results
   built on it assume. A no approves, edits and writes nothing.

3. Otherwise read its current standard review, which the definition below describes, and check it against what you
   found: what it says against the signature, hypothesis by hypothesis; its references and tests; its Lean subtleties.
   Then answer
   - `VERDICT: APPROVE`, if it is right and complete;
   - `VERDICT: EDIT`, if something is missing, wrong or unclear: a hypothesis it skips, a subtlety it misses, a
     sentence a mathematician would misread. Not to reword it. Give a `NOTE:` that says what the edit adds or changes,
     and the whole new text. The new text keeps every reference, test and Check of the text it replaces, unless a
     `DROPPED: <item> — <why>` line says which it drops, and why (the item is how its bullet starts: a test's Lean
     name in backticks, a Check's tag, a reference's author and title);
   - `VERDICT: WRITE`, if the declaration shows "{no_review}": give the whole text.

Answer in this format, an item for each declaration, in the order given. For an approval:

```
### 1. TauCeti.Foo.bar
CELLS: {cells}
VERDICT: APPROVE
```

For an edit:

```
### 2. TauCeti.Foo.baz
CELLS: {cells}
VERDICT: EDIT
NOTE: adds the hypothesis `0 < n`, which the statement has and the text skips
DROPPED: `TauCeti.Foo.baz_one` — renamed `TauCeti.Foo.baz_uno` in Tau Ceti
~~~review
## What it says
<the whole new text, in the three parts of the definition below>

## References and tests
- <a reference, a test or a Check on each line>

## Lean subtleties
None.
~~~
```

For a declaration with no standard review yet, a write:

```
### 3. TauCeti.Foo.qux
CELLS: {cells_all}
VERDICT: WRITE
~~~review
## What it says
<the whole text, in the three parts of the definition below>

## References and tests
- <a reference, a test or a Check on each line>

## Lean subtleties
None.
~~~
```

And for an error, a no:

```
### 4. TauCeti.Foo.quux
CELLS: {cells_error}
VERDICT: NO
CATEGORY: object   WHY: {why}
```

The rules of the format:

- Each heading is the number and the name of the declaration's item below, exactly as given.
- Every item has all eight cells, as `check=cell`, in the order of the table, apart at commas. A NO has at least one
  ERROR cell, and its CATEGORY is the check of one of them, or `other`; the other verdicts have none.
- A declaration shown with a standard review is answered APPROVE, EDIT or NO; one shown with "{no_review}", WRITE or
  NO.
- An APPROVE has nothing after its VERDICT line. An EDIT has its NOTE, any DROPPED lines, and the text; a WRITE has the
  text, and nothing else. The text is in a block that starts with a `~~~review` line and ends with the last `~~~` line
  of the item, in the three parts of the definition below, none empty.
- Plain text, exactly as shown: no other lines, no bold or other markup on CELLS, VERDICT, NOTE, DROPPED, CATEGORY or
  WHY, nothing before the first item or after the last.
- If you cannot tell whether a declaration is correctly stated, leave its item out rather than guess.

The site's definition of a standard review follows, then the declarations."""


#: The reason of the no in the instructions' example (a case from AI-REVIEWS.md).
EXAMPLE_WHY = ("`TauCeti.Foo.quux` states `∑ i ∈ range n, i = n * (n + 1) / 2`, but `range n` stops at `n - 1`, so "
               "the right side should be `n * (n - 1) / 2`: at `n = 1` the sum is `0` and the right side `1`.")


def instructions(count):
    """The instructions to Astra for a question about ``count`` declarations."""
    every = ", ".join(f"{x}=checked" for x in RUBRIC)
    return INSTRUCTIONS.format(
        count=count, s="" if count == 1 else "s", no_review=NO_REVIEW, why=EXAMPLE_WHY, cells_all=every,
        cells=every.replace("choice=checked", "choice=n/a"),
        cells_error=every.replace("object=checked", "object=ERROR: the sum is over `range n`, which stops at `n - 1`")
        .replace("choice=checked", "choice=n/a"))


def git(checkout, *args):
    """``git -C CHECKOUT ARGS`` (bytes); exit 2 if git cannot run."""
    try:
        return subprocess.run(["git", "-C", checkout, *args], capture_output=True)
    except OSError as e:
        die(f"error: cannot run git ({e})", 2)


def need_commit(checkout, commit):
    """Exit 2 unless ``checkout`` is a git checkout that has ``commit``, the one the site shows Tau Ceti at."""
    if not os.path.isdir(checkout):
        die(f"error: --tauceti {checkout} is not a directory: give the git checkout of Tau Ceti", 2)
    if not re.fullmatch(r"[0-9a-f]{7,64}", commit):
        die(f"error: the commit the site shows, {commit!r}, is no git hash", 2)
    r = git(checkout, "cat-file", "-e", f"{commit}^{{commit}}")
    if r.returncode:
        die(f"error: {checkout} does not have commit {commit[:12]}, the one the site shows Tau Ceti at: fetch it "
            f"(git -C {checkout} fetch origin {commit}) and ask again. git says: "
            + r.stderr.decode("utf-8", "replace").strip(), 2)


def source_lines(checkout, commit, path, files):
    """The lines of the Lean file ``path`` as the checkout has it at ``commit`` (`git -C CHECKOUT show COMMIT:PATH`),
    without their line ends; each file is read once, into ``files``."""
    if path not in files:
        r = git(checkout, "show", f"{commit}:{path}")
        if r.returncode:
            die(f"error: cannot read {path} at {commit[:12]} in {checkout}: "
                + r.stderr.decode("utf-8", "replace").strip(), 2)
        try:
            files[path] = r.stdout.decode("utf-8").replace("\r\n", "\n").split("\n")
        except UnicodeDecodeError as e:
            die(f"error: {path} at {commit[:12]} is not UTF-8: {e}", 2)
    return files[path]


def fenced(text, info=""):
    """``text`` in a code fence long enough to hold it: longer than any run of backticks in it."""
    longest = max((len(run) for run in re.findall(r"`+", text)), default=0)
    fence = "`" * max(3, longest + 1)
    return f"{fence}{info}\n{text}\n{fence}"


def module_file(node, read):
    """The file of the site that lists the entries of the module of ``node``: m/<mi>.json for Tau Ceti's own
    declarations, u/<mi>.json for any other; None for a declaration in no module."""
    return read(f"{'m' if node[2] & 1 else 'u'}/{node[3]}.json") if node[3] >= 0 else None


def entry_in(file, i):
    """The entry of the declaration with id ``i`` in a module's file, or None."""
    return next((e for e in (file or {}).get("decls", []) if e.get("id") == i), None)


def rests_on(meta, node, read):
    """What ``node`` rests on that a question shows: the lines `name: statement` of the first RESTS_MAX of the ids the
    node lists, in its order, and how many more there are."""
    ids = node[7] if len(node) > 7 else []
    total = max(len(ids), node[9] if len(node) > 9 and isinstance(node[9], int) else 0)
    lines = []
    for i in ids[:RESTS_MAX]:
        row = node_at(meta, i, read)
        if row is not None:
            entry = entry_in(module_file(row, read), i) or {}
            lines.append(f"{row[0]}: {one_line(entry.get('sig') or entry.get('stmt') or '') or NO_STATEMENT}")
    return lines, total - min(len(ids), RESTS_MAX)


def asked_about(meta, name, read):
    """What a question needs of ``name``, one of Tau Ceti's own declarations: the site's node and entry for it and where
    its Lean is (module file, first and last line); or, as a second value, why the site cannot give them."""
    i = id_of(meta, name, read)
    node = None if i is None else node_at(meta, i, read)
    if node is None:
        return None, "the site has no page for it"
    if not node[2] & 1:
        return None, "it is not one of Tau Ceti's own declarations: a question gives the Lean of Tau Ceti's"
    file = module_file(node, read)
    entry = entry_in(file, i)
    line = (entry or {}).get("line")
    if not (entry and (file or {}).get("path") and isinstance(line, list) and len(line) == 2
            and all(isinstance(x, int) for x in line)):
        return None, "the site gives no source file and lines for it"
    return {"name": name, "node": node, "entry": entry, "path": file["path"], "start": line[0], "end": line[1]}, ""


def drafts_of(path):
    """The text of the draft of each declaration in DRAFTS (a JSONL of actions): that of its last write or edit. {} for
    no file."""
    out = {}
    for d in read_actions(path) if path else []:
        text = d["fields"].get("text")
        if d["kind"] != "approve" and isinstance(d["decl"], str) and isinstance(text, str) and text.strip():
            out[d["decl"]] = text
    return out


def item_text(n, it):
    """Item ``n`` of a question, for the declaration ``it``."""
    out = [f"### {n}. {it['name']}", f"Kind: {KINDS.get(it['node'][1], 'declaration')}",
           f"Source: {it['path']}, lines {it['start']} to {it['end']}, at Tau Ceti {it['commit'][:12]}:",
           fenced(it["source"], "lean"), ""]
    if it["rests"]:
        out += ["Rests on:", *(f"- {x}" for x in it["rests"])]
        out += [f"- (and {it['more']} more)"] if it["more"] > 0 else []
    else:
        out.append("Rests on: nothing the site lists.")
    out.append("")
    if it["version"]:
        out += ["Current standard review:", f"Version: {it['version']}", OPEN, normalize(it["text"]), CLOSE]
    else:
        out.append(f"Current standard review: {NO_REVIEW}")
    return "\n".join(out)


def question_text(items, guide):
    """The question file: the line `astra-answer` reads, the instructions, the guide's section, and the items."""
    names = [{"n": n, "name": it["name"], "version": it["version"]} for n, it in enumerate(items, 1)]
    head = QUESTION_OPEN + json.dumps({"spec": "astra-question/1", "items": names}, ensure_ascii=False) + QUESTION_CLOSE
    return "\n\n".join([head, instructions(len(items)), guide, "## The declarations",
                        *(item_text(n, it) for n, it in enumerate(items, 1))]) + "\n"


def cmd_astra_question(a):
    names = a.names
    if len(names) > QUESTION_MAX:
        die(f"refused: {len(names)} declarations for one question, and it holds at most {QUESTION_MAX}: ask about them "
            "in several questions", 1)
    twice = sorted({n for n in names if names.count(n) > 1})
    if twice:
        die("refused: " + "; ".join(f"{n} is given twice" for n in twice), 1)
    drafted = drafts_of(a.drafts)
    read = reader()
    meta = read("meta.json")
    need_standard(meta)
    commit = meta["library"]["commit"]
    items, problems = [], []
    for name in names:
        it, why = asked_about(meta, name, read)
        if it is None:
            problems.append(f"{name}: {why}")
            continue
        review = standard_of(meta, name, read)
        text = drafted.get(name)
        it.update(commit=commit, from_draft=text is not None,
                  text=text if text is not None else (review or {}).get("text", ""),
                  version=version_of(text) if text is not None else (review or {}).get("version"))
        it["rests"], it["more"] = rests_on(meta, it["node"], read)
        items.append(it)
    if problems:
        die("refused, and no question was written:\n" + "\n".join("- " + p for p in problems), 1)
    need_commit(a.tauceti, commit)
    files = {}
    for it in items:
        lines = source_lines(a.tauceti, commit, it["path"], files)
        if not 1 <= it["start"] <= it["end"] <= len(lines):
            die(f"error: the site puts {it['name']} at lines {it['start']} to {it['end']} of {it['path']}, which has "
                f"{len(lines)} at {commit[:12]}", 2)
        it["source"] = "\n".join(lines[it["start"] - 1:it["end"]])
    text = question_text(items, guide_section())
    write_file(a.out, text)
    size = len(text.encode("utf-8"))
    drafts, none = sum(it["from_draft"] for it in items), sum(not it["version"] for it in items)
    print(f"wrote {a.out}: {len(items)} declaration{'' if len(items) == 1 else 's'}, {size:,} bytes ({drafts} with a "
          f"draft's review, {len(items) - drafts - none} with the site's, {none} with none)", file=sys.stderr)
    if size > QUESTION_WARN:
        print(f"warning: the question is {size:,} bytes, and gate.sh passes it to `codex exec` as one argument, which "
              "Linux limits to 131,072 bytes: ask about fewer declarations at a time", file=sys.stderr)


def write_file(path, text):
    """``text`` as the file ``path``, UTF-8 with `\\n` line ends; exit 2 if it cannot be written."""
    try:
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
    except OSError as e:
        die(f"error: cannot write {path}: {e}", 2)


def read_question(path):
    """The items a question file asks about, {number: (name, the version of the review it showed, or None)}, from the
    first line `astra-question` wrote; exit 2 for a file it did not write."""
    try:
        with open(path, encoding="utf-8") as f:
            first = f.readline().rstrip("\n")
    except (OSError, UnicodeDecodeError) as e:
        die(f"error: cannot read {path}: {e}", 2)
    try:
        if not (first.startswith(QUESTION_OPEN) and first.endswith(QUESTION_CLOSE)):
            raise ValueError("it has no first line of its items")
        spec = json.loads(first[len(QUESTION_OPEN):-len(QUESTION_CLOSE)])
        items = {i["n"]: (i["name"], i["version"]) for i in spec["items"]}
        if spec["spec"] != "astra-question/1" or not items or len(items) != len(spec["items"]) or not all(
                isinstance(n, int) and isinstance(name, str) and (version is None or isinstance(version, str))
                for n, (name, version) in items.items()):
            raise ValueError("its items are not as `astra-question` writes them")
    except (ValueError, KeyError, TypeError) as e:
        die(f"error: {path} is not a question written by `astra-question` ({e})", 2)
    return items


def bare(name):
    """A name as a heading of an answer writes it: without the backticks or asterisks round it."""
    return name.strip().strip("*` ")


def answer_items(text, pairs):
    """The items of an answer, [(number, name, the lines after its heading)]: each starts with a heading `### 3. Name`,
    and the text before the first one is no item's. In a `~~~review` block a line like a heading is the text's, unless
    it is one the question has (``pairs``, its numbers and names). The block is told by its fences: inside it a
    `~~~lean` line opens a fence of the text's, and a `~~~` line closes the innermost, or the block itself."""
    items, current, depth = [], None, None  # depth: None outside a block, else how many fences of the text are open
    for line in text.split("\n"):
        m = ITEM_HEADING.match(line)
        if m and (depth is None or (int(m[1]), bare(m[2])) in pairs):
            current, depth = [], None
            items.append((int(m[1]), bare(m[2]), current))
            continue
        if current is None:
            continue
        current.append(line)
        s = line.strip()
        if depth is None:
            depth = 0 if s == OPEN else None
        elif s == CLOSE:
            depth = depth - 1 if depth else None
        elif s.startswith(CLOSE):
            depth += 1
    return items


def parse_cells(value):
    """The cells of a CELLS line: ({check: "checked" | "na" | "error"}, why it is not all eight checks, each with a
    cell). A cell is `checked`, `n/a` (or `na`) or `ERROR` with its reason, which may hold commas: the next cell starts
    at the next comma and check name."""
    marks = list(CELL_KEY.finditer(value))
    if not marks or marks[0].start() != 0:
        return {}, ["the CELLS line starts with the first check, and gives all eight as `check=cell`, apart at commas"]
    states, problems = {}, []
    for m, after in zip(marks, marks[1:] + [None]):
        axis, raw = m[1].lower(), value[m.end():after.start() if after else len(value)].strip()
        word = raw.strip("*`. ").lower()
        if axis in states:
            problems.append(f"cells: `{axis}` comes twice")
        elif word in CELL_STATES:
            states[axis] = CELL_STATES[word]
        elif re.match(r"error\b", word):
            states[axis] = "error"
        else:
            states[axis] = None
            problems.append(f"cells: `{axis}` is {raw!r}, and a cell is `checked`, `n/a` or `ERROR: <why>`")
    missing = [x for x in RUBRIC if x not in states]
    return states, problems + ([f"cells: every check needs a cell; missing {', '.join(missing)}"] if missing else [])


def item_fields(body):
    """What the lines of an item hold, as ({field: [its values]}, the text of its `~~~review` block or None, whether
    it has one, the problems in reading it). The block starts at the first `~~~review` line and ends at the last `~~~`
    line, as the intake reads a block, so that the text may hold fences of its own."""
    problems, text = [], None
    opens = [k for k, line in enumerate(body) if line.strip() == OPEN]
    rest = body
    if opens:
        closes = [k for k in range(opens[0] + 1, len(body)) if body[k].strip() == CLOSE]
        if closes:
            text, rest = "\n".join(body[opens[0] + 1:closes[-1]]), body[:opens[0]] + [""] + body[closes[-1] + 1:]
        else:
            rest = body[:opens[0]]
            problems.append(f"the `{OPEN}` block is not closed: it ends at the last line `{CLOSE}`")
    fields, current = {}, None
    for line in rest:
        s = line.strip()
        if not s or RULE.match(s):
            if current == "WHY":  # a reason may run over several paragraphs
                fields["WHY"][-1] += ("" if s else "\n")
            else:
                current = None
            continue
        m = FIELD.match(s)
        if m is None:
            if current:
                fields[current][-1] += ("\n" if current == "WHY" else " ") + s
            elif not any(p.startswith("cannot read") for p in problems):
                problems.append(f"cannot read the line `{s[:60]}`")
            continue
        key, value = m[1].upper(), m[2]
        if key == "CATEGORY":
            c = CATEGORY_LINE.match(value)
            if c is None:
                problems.append("cannot read the CATEGORY line: it is `CATEGORY: <check>   WHY: <the error>`")
                current = None
                continue
            fields.setdefault("CATEGORY", []).append(bare(c[1]).lower())
            if c[2] is not None:
                fields.setdefault("WHY", []).append(c[2])
            current = "WHY" if c[2] is not None else None
        else:
            fields.setdefault(key, []).append(value)
            current = key if key in ("NOTE", "DROPPED", "WHY") else None
    return fields, text, bool(opens), problems


def judge_item(name, body, version):
    """What to file for the item ``name`` of an answer, whose lines after its heading are ``body``, when the question
    showed it the review of version ``version`` (None: it showed none): ("action", the row for `post`), ("no", its row
    for the noes) or ("not filed", why). It files nothing it has to guess: the cells are all eight and none an ERROR but
    a NO's, the verdict has the lines it takes and no other, and an approval or an edit has a review to approve or
    edit."""
    fields, text, has_block, problems = item_fields(body)
    for key, values in fields.items():
        if len(values) > 1 and key != "DROPPED":
            problems.append(f"{key} comes more than once")
    states = {}
    if "CELLS" not in fields:
        problems.append("no CELLS line: give the eight checks as `check=cell`")
    else:
        states, bad = parse_cells(fields["CELLS"][0])
        problems += bad
    verdict = None
    if "VERDICT" not in fields:
        problems.append("no VERDICT line: APPROVE, EDIT, WRITE or NO")
    else:
        verdict = fields["VERDICT"][0].strip("*`_. ").upper()
        if verdict not in VERDICTS:
            problems.append(f"VERDICT is {fields['VERDICT'][0]!r}, and a verdict is APPROVE, EDIT, WRITE or NO")
            verdict = None
    note = " ".join(fields.get("NOTE", [""])[0].split())
    why = (fields.get("WHY") or [""])[0].strip()
    category = (fields.get("CATEGORY") or [""])[0]
    if verdict:
        given = {k for k in fields if k not in ("CELLS", "VERDICT")} | ({"BLOCK"} if has_block else set())
        given -= {"NOTE"} if verdict == "EDIT" and not note else set()  # an empty NOTE is none
        given -= {"WHY"} if verdict == "NO" and not why else set()
        problems += [f"{ARTICLE[verdict]} takes no {PARTS[x]}" for x in sorted(given - VERDICTS[verdict])]
        problems += [f"{ARTICLE[verdict]} needs a {PARTS[x]}" for x in sorted(NEEDS[verdict] - given)]
        if verdict in ("APPROVE", "EDIT") and version is None:
            problems.append(f"the question showed no standard review to {verdict.lower()}: it asks for a WRITE")
        if verdict == "WRITE" and version is not None:
            problems.append(f"the question showed a standard review (version {version}): approve it, edit it, or "
                            "say NO")
        errors = [x for x in RUBRIC if states.get(x) == "error"]
        if verdict == "NO":
            if not errors:
                problems.append("a NO needs an ERROR cell: the cells say there is no error")
            if category and category not in AXES:
                problems.append(f"CATEGORY {category!r} is none of the checks ({', '.join(RUBRIC)}) or `other`")
            elif category and category != "other" and errors and category not in errors:
                problems.append(f"CATEGORY {category} is not the check of an ERROR cell ({', '.join(errors)}): give "
                                "the check that failed, or `other`")
        elif errors:
            problems.append(f"{', '.join(errors)} is an ERROR, which {ARTICLE[verdict]} cannot have: an error is a NO")
    dropped = []
    for d in fields.get("DROPPED", []) if verdict == "EDIT" else []:
        parts = FIELD_SEP.split(d, maxsplit=1)
        if len(parts) == 2 and parts[0].strip() and parts[1].strip():
            dropped.append({"item": parts[0].strip(), "why": parts[1].strip()})
        else:
            problems.append(f"DROPPED needs `<item> — <why>`, and this is {d!r}")
    if problems or verdict is None:
        return "not filed", "; ".join(problems)
    if verdict == "NO":
        return "no", {"decl": name, "category": category, "why": why}
    cells = {x: states[x] for x in RUBRIC}
    body_text = normalize(text or "")
    row = {"APPROVE": {"approve": name, "version": version, "cells": cells},
           "EDIT": {"edit": name, "parent": version, "cells": cells, "note": note, "dropped": dropped,
                    "text": body_text},
           "WRITE": {"write": name, "cells": cells, "text": body_text}}[verdict]
    kind = verdict.lower()
    # What `post` would refuse of it, the version's being current aside (it refuses the whole file for one such action).
    act = {"line": 0, "kind": kind, "decl": name, "fields": {k: v for k, v in row.items() if k != kind}}
    more = action_problems(act, lambda n: "", lambda n: version, {})
    if not more and len(lines_of(act)) > COMMENT_CAP - ROOM:
        more = [f"its lines are {len(lines_of(act)):,} characters, and a comment holds {COMMENT_CAP:,}"]
    return ("not filed", "; ".join(more)) if more else ("action", row)


def cmd_astra_answer(a):
    expected = read_question(a.question)
    try:
        with open(a.answer, encoding="utf-8-sig") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError) as e:
        die(f"error: cannot read {a.answer}: {e}", 2)
    if not text.strip():
        die(f"error: {a.answer} is empty", 2)
    numbered = {name: n for n, (name, _) in expected.items()}
    got, not_filed = {}, []  # the bodies of the items that match the question's, by number; and what is left out
    for n, name, body in answer_items(text, {(n, name) for n, (name, _) in expected.items()}):
        label = name or f"item {n}"
        if n in expected and expected[n][0] == name:
            got.setdefault(n, []).append(body)
        elif n in expected:
            not_filed.append((label, f"item {n} of the question is {expected[n][0]}, not {name or 'nothing'}"))
        elif name in numbered:
            not_filed.append((label, f"the question numbers it {numbered[name]}, not {n}"))
        else:
            not_filed.append((label, "it is not in the question"))
    actions, noes = [], []
    for n in sorted(expected):
        name, version = expected[n]
        if n not in got:
            not_filed.append((name, f"the answer has no item {n} for it"))
        elif len(got[n]) > 1:
            not_filed.append((name, f"the answer has item {n} twice, and it does not guess which is meant"))
        else:
            kind, row = judge_item(name, got[n][0], version)
            if kind == "not filed":
                not_filed.append((name, row))
            else:
                (actions if kind == "action" else noes).append(row)
    for path, rows in ((a.out, actions), (a.noes, noes)):
        write_file(path, "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
    for label, why in not_filed:
        print(f"not filed: {label}: {why}")
    print(f"{len(actions)} action{'' if len(actions) == 1 else 's'} in {a.out}, "
          f"{len(noes)} no{'' if len(noes) == 1 else 'es'} in {a.noes}, {len(not_filed)} not filed", file=sys.stderr)


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
    q = sub.add_parser("astra-question")
    q.add_argument("names", nargs="+")
    q.add_argument("--tauceti", required=True)
    q.add_argument("--drafts", default="")
    q.add_argument("--out", required=True)
    q.set_defaults(fn=cmd_astra_question)
    q = sub.add_parser("astra-answer")
    q.add_argument("answer")
    q.add_argument("--question", required=True)
    q.add_argument("--out", required=True)
    q.add_argument("--noes", required=True)
    q.set_defaults(fn=cmd_astra_answer)
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
