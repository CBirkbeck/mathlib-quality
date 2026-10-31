#!/usr/bin/env python3
"""Work queue, claims and scoreboard for /redteam (mathlib-quality).

  next      rank the Tau Ceti files a hunt should take next
  claim     acquire | renew | release a claim (COORDINATION.md section 3): a file path
            claims refs/tauceti-claims/redteam/<path>; branch/<pr> claims a PR branch
  finding   record a finding, or a change to one (validated; a win needs its evidence)
  audit     record a finished file audit (validated; every declaration needs a verdict
            in every category), with its reviews for the review site: for each declaration
            whose correctness checks passed, the site's eight cells and one decision on its
            standard review (approve, write or edit)
  sync      mark findings landed or rejected once their PRs merge or close
  reviews   post this agent's reviews on the Tau Ceti review site once the site shows each
            file as it was audited; drop those whose file changed first, and name for a
            re-review those whose standard review has changed since they were decided
  yes       record a re-review: new decisions for the declarations of this agent's audit
            of a file that `reviews` names to re-review
  whoami    this agent's id: its PRs carry it, so each agent tends and counts only its own
  astra     ask gpt-6-astra through the Codex CLI, for machines without the chatgpt-math MCP
  tally     the scoreboard: wins, losses, landed fixes, coverage, recurring patterns

The ledger is a directory: $REDTEAM_LEDGER, else ~/.tauceti-redteam. Each agent appends
only to its own findings/<owner>.jsonl, audits/<owner>.jsonl and reviews/<owner>.jsonl,
so a ledger shared through git never conflicts. If the directory is a git clone with a remote, reads pull
first and writes are committed and pushed.

Exit codes: 0 done; 1 refused (claim held by another agent, or a record failed
validation, with the reason on stderr); 2 error.
"""
import argparse
import datetime
import glob
import json
import os
import re
import secrets
import socket
import subprocess
import sys
import tempfile
import time
import uuid

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import review_site  # noqa: E402  - checks an audit's yes as `review_site.py post` will, so none waits on a refusal

CATEGORIES = ["correctness", "generality", "reuse", "proof", "naming", "api", "docs", "hygiene"]
SEVERITIES = ["CRITICAL", "MAJOR", "MINOR", "NIT"]
STATUSES = ["suspected", "confirmed", "refuted", "pr-open", "landed", "superseded", "rejected",
            "needs-human"]
RUBRICS = ["correctness", "reuse", "scope", "attribution", "api-design", "generality",
           "placement", "naming", "documentation", "proof-quality", "none"]
WIN = {"CRITICAL", "MAJOR"}
LIVE = {"confirmed", "pr-open", "landed", "superseded"}   # confirmed and not since overturned
REMOTE = "https://github.com/TauCetiProject/TauCeti.git"
REPO_SLUG = "TauCetiProject/TauCeti"
CLAIM_PREFIX = "refs/tauceti-claims/redteam/"
SKEW = 60
#: Reads the standard reviews on the Tau Ceti review site, and posts the red team's (R6 step 10).
REVIEW_SITE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "review_site.py")
# A model's family, not the model: "GPT-6", "Opus 5", "Claude" (as scripts/review_site.py, which refuses them too).
FAMILY = re.compile(r"^(gpt|claude|opus|sonnet|haiku|fable|gemini|codex)[-\s]?(\d+(\.\d+)?)?$", re.I)
#: The decisions an entry of an audit's yes makes on the declaration's standard review, and the keys of an entry of
#: each: approve the text the site shows (the value is its version), write the first one (the text), or edit it (the
#: parent version, with a note, what it drops and why, and the whole new text).
ENTRY_KEYS = {"approve": {"cells", "approve"}, "write": {"cells", "write"},
              "edit": {"cells", "edit", "note", "dropped", "text"}}
#: Why `reviews` drops the yeses of an audit recorded before 0.82.0, which were reasons.
OLD_FORM = "the site takes standard-review approvals now"
#: The audit's categories whose findings one of the site's eight checks covers, and the checks: while such a finding
#: stands against a declaration that check fails, and the red team leaves no no, so the declaration gets no review.
COVERED = {"correctness": "object, convention, edge-cases, junk, vacuous and choice", "generality": "generality",
           "naming": "naming", "docs": "naming"}
#: Why `yes` takes no new decision for a declaration of the audit that is not waiting for a re-review, by its state.
NOT_WAITING = {"posted": "its review was posted already", "left out": "the site has no page for it",
               "dropped": "its review was dropped", None: "its decision waits to be posted, not for a re-review"}

MODS = r"(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
DECL = re.compile(r"^\s*" + ATTRS + MODS +
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|irreducible_def)\b(.*)$")
NAME = re.compile(r"\s*(?:\(priority\s*:=\s*[^)]*\)\s*)?([^\s:({\[⦃]+)")
# git grep takes POSIX ERE, so no \s or \b there.
ERE_DEF = (r"^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|public|noncomputable|partial|"
           r"unsafe|nonrec|scoped|local)[[:space:]]+)*(def|abbrev|structure|class|inductive|opaque|"
           r"irreducible_def)[[:space:]]")
ERE_IMPORT = r"^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?TauCeti\."


def die(msg, code=2):
    print(msg, file=sys.stderr)
    sys.exit(code)


def run(cmd, cwd=None, check=True, env=None):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env)
    if check and r.returncode != 0:
        die("command failed: %s\n%s" % (" ".join(cmd), r.stderr.strip()))
    return r


def now():
    return int(time.time())


def iso(t=None):
    return datetime.datetime.fromtimestamp(t if t is not None else now(), datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# --- ledger ---------------------------------------------------------------------------

def ledger_dir():
    d = os.path.expanduser(os.environ.get("REDTEAM_LEDGER", "~/.tauceti-redteam"))
    for sub in ("findings", "audits", "reviews"):
        os.makedirs(os.path.join(d, sub), exist_ok=True)
    return d


def is_git(d):
    return os.path.isdir(os.path.join(d, ".git")) and run(["git", "remote"], cwd=d, check=False).stdout.strip()


def pull(d):
    if is_git(d):
        run(["git", "pull", "--rebase", "-q"], cwd=d, check=False)


def push(d, msg):
    if not is_git(d):
        return
    run(["git", "add", "-A"], cwd=d)
    if run(["git", "diff", "--cached", "--quiet"], cwd=d, check=False).returncode == 0:
        return
    run(["git", "commit", "-q", "-m", msg], cwd=d)
    for attempt in range(5):
        if run(["git", "push", "-q"], cwd=d, check=False).returncode == 0:
            return
        run(["git", "pull", "--rebase", "-q"], cwd=d, check=False)
        time.sleep(2 * (attempt + 1))
    print("warning: ledger commit made but not pushed", file=sys.stderr)


def owner_id(repo):
    o = os.environ.get("REDTEAM_OWNER")
    if o:
        return o
    path = os.path.join(repo, ".mathlib-quality", "redteam-owner")
    if os.path.exists(path):
        return open(path).read().strip()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    o = "%s-%s" % (socket.gethostname().split(".")[0], uuid.uuid4())
    with open(path, "w") as f:
        f.write(o + "\n")
    return o


def read_jsonl(d, sub):
    rows = []
    for path in sorted(glob.glob(os.path.join(d, sub, "*.jsonl"))):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        rows.append(json.loads(line))
                    except ValueError:
                        print("warning: unreadable line in %s" % path, file=sys.stderr)
    return rows


def append(d, sub, owner, row):
    with open(os.path.join(d, sub, owner + ".jsonl"), "a") as f:
        f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def findings(d):
    """Fold the finding events into one record per id; a later event's fields win."""
    out = {}
    for row in sorted(read_jsonl(d, "findings"), key=lambda r: r.get("at", "")):
        out.setdefault(row["id"], {}).update(row)
    return out


def topic(f):
    """The PR a queued finding would ship in: a CRITICAL alone; nits and hygiene in the file's
    chore PR; otherwise one file and one category."""
    if f["severity"] == "CRITICAL":
        return (f["file"], "critical", f["id"])
    if f["severity"] == "NIT" or f["category"] == "hygiene":
        return (f["file"], "chore")
    return (f["file"], f["category"])


def cell_ids(v):
    """A matrix cell: "ok", "F:<id>", "F:<id>,<id>", or a list of "F:<id>" strings."""
    if v == "ok":
        return []
    items = v if isinstance(v, list) else [v]
    ids = []
    for item in items:
        if not (isinstance(item, str) and item.startswith("F:")):
            return None
        ids += [x.strip() for x in item[2:].split(",") if x.strip()]
    return ids or None


# --- validation -------------------------------------------------------------------------

def problems(f):
    p = []
    for k in ("id", "file", "decl", "category", "severity", "status", "claim", "pattern", "rubric"):
        if not f.get(k):
            p.append("missing field '%s'" % k)
    if f.get("category") not in CATEGORIES:
        p.append("category must be one of %s" % ", ".join(CATEGORIES))
    if f.get("severity") not in SEVERITIES:
        p.append("severity must be one of %s" % ", ".join(SEVERITIES))
    if f.get("status") not in STATUSES:
        p.append("status must be one of %s" % ", ".join(STATUSES))
    if f.get("rubric") not in RUBRICS:
        p.append("rubric must be one of %s" % ", ".join(RUBRICS))
    if f.get("pattern") and not re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", f["pattern"]):
        p.append("pattern must be a kebab-case slug naming the kind of error")
    if f.get("status") in LIVE and f.get("severity") in WIN:
        ev = f.get("evidence") or {}
        results = ("compiles", "fails-as-expected") + (
            () if f.get("category") in ("correctness", "reuse", "generality") else ("measured",))
        if not ev.get("lean") or ev.get("result") not in results:
            p.append("a %s %s finding counts only with evidence.lean (the probe or measurement) and "
                     "evidence.result in %s" % (f.get("severity"), f.get("category"), "|".join(results)))
        a = f.get("astra") or {}
        if a.get("verdict") not in ("agrees", "disagrees", "unsure") or not a.get("summary"):
            p.append("a %s finding needs astra.verdict (agrees|disagrees|unsure) and astra.summary"
                     % f.get("severity"))
        elif a["verdict"] != "agrees" and not f.get("resolution"):
            p.append("Astra did not agree: add 'resolution' saying why the Lean evidence stands")
    if f.get("status") in ("pr-open", "landed") and not f.get("pr"):
        p.append("status %s needs the PR number" % f.get("status"))
    if f.get("status") in ("refuted", "rejected", "superseded", "needs-human") and not f.get("resolution"):
        p.append("status %s needs 'resolution': what happened, with a link (for needs-human: what a "
                 "human must decide)" % f.get("status"))
    return p


def decls_in(text):
    """(name, line) for each declaration a line-based scan finds. Anonymous instances are
    named instance@L<line>."""
    out = []
    for i, line in enumerate(text.splitlines(), 1):
        m = DECL.match(line)
        if not m:
            continue
        kind, rest = m.group(1), m.group(2)
        n = NAME.match(rest)
        name = n.group(1) if n else ""
        if kind == "instance" and (not name or name.startswith(("(", "[", "{", "⦃", ":"))):
            name = "instance@L%d" % i
        if name:
            out.append((name, i))
    return out


# --- next -------------------------------------------------------------------------------

def git_lines(repo, args):
    return run(["git"] + args, cwd=repo).stdout.splitlines()


def cmd_next(a):
    repo, d = a.repo, ledger_dir()
    pull(d)
    files = {}
    for line in git_lines(repo, ["ls-tree", "-r", "-l", a.ref, "--", "TauCeti"]):
        meta, path = line.split("\t", 1)
        if not path.endswith(".lean") or (a.under and not path.startswith(a.under)):
            continue
        _, _, oid, size = meta.split()
        files[path] = {"blob": oid, "size": int(size), "defs": 0, "importers": 0}
    for line in run(["git", "grep", "-h", "-E", ERE_IMPORT, a.ref, "--", "TauCeti/*.lean"],
                    cwd=repo, check=False).stdout.splitlines():
        mod = re.sub(r"^.*import\s+(?:all\s+)?", "", line).split()[0]
        path = mod.replace(".", "/") + ".lean"
        if path in files:
            files[path]["importers"] += 1
    for line in run(["git", "grep", "-c", "-E", ERE_DEF, a.ref, "--", "TauCeti/*.lean"],
                    cwd=repo, check=False).stdout.splitlines():
        _, path, n = line.rsplit(":", 2) if line.count(":") >= 2 else ("", "", "0")
        if path in files:
            files[path]["defs"] = int(n)
    audited = {}
    for row in sorted(read_jsonl(d, "audits"), key=lambda r: r.get("audited_at", "")):
        audited[row["file"]] = row
    busy, claimed = set(), set()
    if not a.offline:
        r = run(["gh", "pr", "list", "--repo", REPO_SLUG, "--state", "open", "--limit", "1000",
                 "--json", "files", "--jq", ".[].files[].path"], check=False)
        if r.returncode != 0:
            die("gh pr list failed, so the open PRs' files are unknown; stop the round.\n" + r.stderr)
        busy = set(r.stdout.split())
        r = run(["git", "ls-remote", a.remote, CLAIM_PREFIX + "*"], check=False)
        if r.returncode != 0:
            die("git ls-remote failed, so claims are unknown; stop the round.\n" + r.stderr)
        claimed = {ln.split("\t", 1)[1][len(CLAIM_PREFIX):] for ln in r.stdout.splitlines() if "\t" in ln}
    suspected = {}
    for f in findings(d).values():
        if f.get("status") == "suspected":
            suspected.setdefault(f["file"], []).append(f["id"])
    cutoff = now() - a.cooloff_days * 86400
    ranked = []
    for path, f in files.items():
        if path in busy or path in claimed:
            continue
        prev = audited.get(path)
        if path in suspected:
            tier, why = 0, "suspected: " + ", ".join(suspected[path])
        elif prev is None:
            tier, why = 1, "never audited"
        else:
            t = datetime.datetime.strptime(prev["audited_at"], "%Y-%m-%dT%H:%M:%SZ").replace(
                tzinfo=datetime.timezone.utc).timestamp()
            if t > cutoff or prev.get("blob") == f["blob"]:
                continue
            tier, why = 2, "changed since its audit on %s" % prev["audited_at"][:10]
        score = 3 * f["defs"] + f["importers"] + min(f["size"] // 4000, 5)
        ranked.append((tier, -score, path, f, why))
    ranked.sort()
    if a.json:
        print(json.dumps([dict(file=p, tier=t, score=-s, why=w, **f) for t, s, p, f, w in ranked[:a.limit]], indent=1))
        return
    total = len(files)
    done = sum(1 for p in files if p in audited)
    print("%d of %d files audited; %d candidates%s" % (
        done, total, len(ranked), "" if a.offline else " (%d in open PRs, %d claimed, skipped)" % (
            len(busy & set(files)), len(claimed & set(files)))))
    for t, s, p, f, w in ranked[:a.limit]:
        print("%4d  %-3s defs %-3d importers %-3d %4d KB  %s  (%s)" % (
            -s, ("sus", "new", "re")[t], f["defs"], f["importers"], f["size"] // 1024, p, w))


# --- claim ------------------------------------------------------------------------------

def claims_git(d):
    g = os.path.join(d, "claims.git")
    if not os.path.isdir(g):
        run(["git", "init", "-q", "--bare", g])
    return g


def lease(g, key, owner, ttl, observed):
    body = {"schema": "tauceti-claim/v1", "owner": owner, "host": socket.gethostname(),
            "pid": os.getpid(), "acquired_at": now(), "expires_at": now() + ttl,
            "resource": key, "observed_branch_oid": observed}
    tree = run(["git", "hash-object", "-t", "tree", "-w", "--stdin"], cwd=g).stdout.strip()
    env = dict(os.environ, GIT_AUTHOR_NAME=owner, GIT_AUTHOR_EMAIL="redteam@invalid",
               GIT_COMMITTER_NAME=owner, GIT_COMMITTER_EMAIL="redteam@invalid")
    return run(["git", "commit-tree", tree, "-m", json.dumps(body, sort_keys=True)], cwd=g, env=env).stdout.strip()


def cmd_claim(a):
    d = ledger_dir()
    g = claims_git(d)
    owner = owner_id(a.repo)
    key = a.file if re.fullmatch(r"branch/\d+", a.file) else "redteam/" + a.file
    ref = "refs/tauceti-claims/" + key
    r = run(["git", "ls-remote", a.remote, ref], check=False)
    if r.returncode != 0:
        die("git ls-remote failed; the claim state is unknown.\n" + r.stderr)
    cur = r.stdout.split()[0] if r.stdout.strip() else ""
    held = {}
    if cur:
        if run(["git", "fetch", "-q", a.remote, ref], cwd=g, check=False).returncode != 0:
            die("could not fetch the current lease on %s" % ref)
        try:
            held = json.loads(run(["git", "log", "-1", "--format=%B", cur], cwd=g).stdout)
        except ValueError:
            held = {}
    mine = held.get("owner") == owner
    expired = held.get("expires_at", 0) + SKEW < now()
    if a.action == "release":
        if not cur:
            print("released (no claim was held)")
            return
        if not mine:
            die("not released: %s holds it" % held.get("owner"), 1)
        r = run(["git", "push", "-q", "--force-with-lease=%s:%s" % (ref, cur), a.remote, ":" + ref], cwd=g, check=False)
        if r.returncode != 0:
            die("release lost a race; the claim moved.\n" + r.stderr, 1)
        print("released %s" % key)
        return
    if cur and not mine and not expired:
        die("held by %s until %s" % (held.get("owner"), iso(held.get("expires_at", 0))), 1)
    if a.action == "renew" and not mine:
        die("cannot renew: %s" % ("the claim is gone" if not cur else "held by %s" % held.get("owner")), 1)
    observed = run(["git", "rev-parse", "origin/main"], cwd=a.repo, check=False).stdout.strip()
    new = lease(g, key, owner, a.ttl, observed)
    r = run(["git", "push", "-q", "--force-with-lease=%s:%s" % (ref, cur), a.remote, "%s:%s" % (new, ref)], cwd=g, check=False)
    if r.returncode != 0:
        die("lost the race for %s; someone else moved the claim first" % key, 1)
    print("%s %s until %s (owner %s)" % ("renewed" if mine else "acquired", key, iso(now() + a.ttl), owner))


# --- finding / audit --------------------------------------------------------------------

def load_arg_json(s):
    if s.startswith("@"):
        with open(s[1:]) as f:
            s = f.read()
    try:
        return json.loads(s)
    except ValueError as e:
        die("not JSON: %s" % e)


def cmd_finding(a):
    d = ledger_dir()
    pull(d)
    owner = owner_id(a.repo)
    row = load_arg_json(a.json)
    known = findings(d)
    if not row.get("id"):
        row["id"] = "RT-%s-%s" % (datetime.date.today().strftime("%Y%m%d"), secrets.token_hex(3))
    merged = dict(known.get(row["id"], {}))
    merged.update(row)
    bad = problems(merged)
    if bad:
        die("finding %s not recorded:\n  - %s" % (row["id"], "\n  - ".join(bad)), 1)
    row["at"] = iso()
    row["owner"] = owner
    append(d, "findings", owner, row)
    push(d, "redteam: %s %s" % (row["id"], merged["status"]))
    print(row["id"])


def cmd_audit(a):
    d = ledger_dir()
    pull(d)
    owner = owner_id(a.repo)
    row = load_arg_json(a.json)
    path, matrix = row.get("file"), row.get("matrix") or {}
    if not path or not matrix:
        die("an audit needs 'file' and a 'matrix' of declaration -> {category: verdict}", 1)
    r = run(["git", "show", "%s:%s" % (a.ref, path)], cwd=a.repo, check=False)
    if r.returncode != 0:
        die("%s is not on %s" % (path, a.ref), 1)
    blob = run(["git", "rev-parse", "%s:%s" % (a.ref, path)], cwd=a.repo).stdout.strip()
    known = findings(d)
    bad = []
    keys = set(matrix)
    if "(file)" not in keys:
        bad.append("no verdicts for (file): the row for the file itself — header, module docstring, "
                   "imports, leftovers between declarations")
    for name, line in decls_in(r.stdout):
        if name not in keys and not any(k.endswith("." + name) for k in keys):
            bad.append("no verdicts for %s (line %d)" % (name, line))
    for decl, cells in matrix.items():
        for c in CATEGORIES:
            ids = cell_ids((cells or {}).get(c))
            if ids is None:
                bad.append("%s: category '%s' needs \"ok\" or \"F:<finding id>[,<id>…]\"" % (decl, c))
            for i in ids or []:
                if i not in known:
                    bad.append("%s: %s cites %s, which is not in the ledger" % (decl, c, i))
    bad += yes_problems(row, matrix, known)
    if bad:
        die("audit of %s not recorded (%d problems):\n  - %s" % (path, len(bad), "\n  - ".join(bad[:60])), 1)
    ids = sorted({i for cells in matrix.values() for v in cells.values() for i in cell_ids(v) or []})
    row.update({"blob": blob, "main": run(["git", "rev-parse", a.ref], cwd=a.repo).stdout.strip(),
                "audited_at": iso(), "owner": owner, "decls": len(matrix) - 1, "findings": ids})
    append(d, "audits", owner, row)
    push(d, "redteam: audited %s" % path)
    print("recorded: %s, %d declarations and the file row, %d findings" % (path, len(matrix) - 1, len(ids)))


def yes_problems(row, matrix, known):
    """An audit's yeses (R6 step 8): {full name: the site's eight cells and one decision on the declaration's standard
    review}, each for a declaration of the matrix whose correctness checks passed, against which no CRITICAL finding
    stands, nor any finding one of the site's checks covers (COVERED), and each one that `review_site.py post` takes
    (`entry_problems`); and the model that audited, which names the reviewer. A finding stands unless it was refuted."""
    yes, bad = row.get("yes") or {}, []
    if not isinstance(yes, dict):
        return ["'yes' maps each full name to the site's eight cells and one decision on its standard review"]
    if yes and not row.get("model"):
        bad.append("an audit with yeses needs 'model', the model that audited: the site names the reviewer by it")
    elif yes and FAMILY.match(str(row["model"]).strip()):
        bad.append("'model' is %r, a family, not a model: give the model exactly as your harness names it "
                   "(claude-opus-5-5, not Opus; GPT-6 Astra, not GPT-6)" % row["model"])
    for name, entry in yes.items():
        keys = [k for k in matrix if k == name or name.endswith("." + k)]
        cells = (matrix[keys[0]] or {}) if keys else None
        if cells is None:
            bad.append("yes for %s, which has no row in the matrix (give its full name)" % name)
        elif cells.get("correctness") != "ok":
            bad.append("yes for %s, whose correctness cell is not ok" % name)
        elif any((known.get(i) or {}).get("severity") == "CRITICAL" and known[i].get("status") != "refuted"
                 for v in cells.values() for i in cell_ids(v) or []):
            bad.append("yes for %s, which a CRITICAL finding stands against" % name)
        else:
            covered = {}  # the findings standing against it that a check of the site covers, and that check
            for column, v in cells.items():
                for i in cell_ids(v) or []:
                    f = known.get(i) or {}
                    check = COVERED.get(f.get("category")) or COVERED.get(column)
                    if check and f.get("status") != "refuted":
                        covered[i] = check
            if covered:
                bad.append("yes for %s, against which %s stands: the site checks for that (%s), so it gets no review "
                           "until its fix lands and a later audit finds it clean"
                           % (name, ", ".join(sorted(covered)), "; ".join(sorted(set(covered.values())))))
        if " " in name.strip():
            bad.append("yes for %s: give its full name" % name)
        bad += ["yes for %s: %s" % (name, p) for p in entry_problems(name, entry)]
    return bad


def decision(entry):
    """The decision an entry of an audit's yes makes, "approve", "write" or "edit"; None unless it makes exactly one."""
    kinds = [k for k in ENTRY_KEYS if k in entry]
    return kinds[0] if len(kinds) == 1 else None


def action_of(name, entry):
    """The action of `review_site.py post` for ``entry``, the yes of ``name``, which makes one decision: {"approve": name,
    "version", "cells"}, {"write": name, "cells", "text"} or {"edit": name, "parent", "cells", "note", "dropped",
    "text"}."""
    kind = decision(entry)
    if kind == "approve":
        return {"approve": name, "version": entry["approve"], "cells": entry.get("cells")}
    if kind == "write":
        return {"write": name, "cells": entry.get("cells"), "text": entry["write"]}
    return {"edit": name, "parent": entry["edit"], "cells": entry.get("cells"), "note": entry.get("note"),
            "dropped": entry.get("dropped", []), "text": entry.get("text")}


def entry_problems(name, entry):
    """Why ``entry``, the yes of ``name``, is not one that `review_site.py post` takes, as `post` checks it: the eight
    cells, one decision with the keys it has (ENTRY_KEYS), a version of 8 to 16 hex digits, a text in the three parts,
    and an edit's note and what it drops. Whether the version is the one the site shows is for `reviews` to see when it
    posts."""
    if not isinstance(entry, dict):
        return ["reasons are the earlier form of a yes, which the site no longer takes: give the site's eight cells and "
                "one decision on its standard review (reference section 7)"]
    kind = decision(entry)
    if kind is None:
        given = [k for k in ENTRY_KEYS if k in entry]
        return ["give one decision on its standard review: approve (its version), write (the text) or edit (the "
                "parent's version, a note and the text), not %s" % (" and ".join(given) or "none")]
    bad = ["`%s` is not a key of %s, which has %s" % (k, kind, ", ".join(sorted(ENTRY_KEYS[kind])))
           for k in entry if k not in ENTRY_KEYS[kind]]
    row = action_of(name, entry)
    act = {"line": 0, "kind": kind, "decl": name, "fields": {k: v for k, v in row.items() if k != kind}}
    given = act["fields"].get("version", act["fields"].get("parent"))
    shown = given.strip().lower() if isinstance(given, str) else None  # any well-formed version passes here
    bad += review_site.action_problems(act, lambda n: "", lambda n: shown, {})
    if not bad and len(review_site.lines_of(act)) > review_site.COMMENT_CAP - review_site.ROOM:
        bad.append("its lines are %d characters, more than a comment on the site's bulk issue holds: shorten its text"
                   % len(review_site.lines_of(act)))
    return bad


# --- reviews ----------------------------------------------------------------------------

def newest_audits(d, owner):
    """This agent's newest audit of each file, by file: it stands for the file."""
    newest = {}
    for au in read_jsonl(d, "audits"):
        if au.get("owner") == owner and au.get("audited_at", "") >= newest.get(au["file"], {}).get("audited_at", ""):
            newest[au["file"]] = au
    return newest


def yes_states(au, rows):
    """The yeses of the audit ``au`` as they stand after ``rows``, its rows of the reviews ledger in the order written:
    {name: entry}, and {name: state}, where a state is None while the entry waits to be posted, else "posted",
    "re-review", "left out" or "dropped". A row of `yes` ("re-reviewed") replaces entries, which wait to be posted
    again; a row that names no declarations, as those before 0.82.0, settles them all."""
    entries = dict(au.get("yes") or {})
    states = dict.fromkeys(entries)
    for row in rows:
        if row.get("state") == "re-reviewed":
            entries.update(row.get("yes") or {})
            states.update(dict.fromkeys(row.get("yes") or {}))
        else:
            states.update(dict.fromkeys(row["decls"] if "decls" in row else list(states), row.get("state")))
    return entries, states


def standard_now(names):
    """The standard reviews the site shows for ``names``, as `review_site.py standard --json` gives them: {name: {"version":
    V or None, ...}, or None where the site has no page}; None, with why printed, when it cannot be read."""
    r = run([sys.executable, REVIEW_SITE, "standard", "--json", *names], check=False)
    try:
        shown = json.loads(r.stdout) if r.returncode in (0, 1) else None  # 1: a name the site has no page for
    except ValueError:
        shown = None
    if not isinstance(shown, dict):
        print("the site's standard reviews cannot be read; the reviews wait for a later round: %s"
              % (r.stderr.strip() or r.stdout.strip()))
        return None
    return shown


def stale(entry, version):
    """Why ``entry`` no longer fits the standard review the site shows now, of ``version`` (None: it shows none): it was
    decided against another text, or writes a first one where there is one now. "" when it fits."""
    if decision(entry) == "write":
        return "a standard review was written since, %s" % version if version else ""
    given = str(entry.get("approve") or entry.get("edit") or "").strip().lower()
    if not version:
        return "the site shows no standard review of it now"
    return "" if version.startswith(given) else "its standard review is now %s, not %s" % (version, given)


def counted(actions):
    """``actions`` counted by kind: "1 approval, 2 edits"."""
    kinds = [decision(x) for x in actions]
    word = {"approve": "approval", "write": "write", "edit": "edit"}
    return ", ".join("%d %s%s" % (kinds.count(k), word[k], "" if kinds.count(k) == 1 else "s")
                     for k in ENTRY_KEYS if k in kinds)


def cmd_reviews(a):
    """The yeses of this agent's audits go on the review site once it shows each file as it was audited: the site
    follows Tau Ceti's docgen commit, behind main, so a file added or changed since then waits. If the file changes
    again before the site reaches the audited commit, its yeses are dropped: they were about a version the site never
    shows. Each goes up as it was decided, against the standard review the site shows now: one decided against another
    text, a first text where there is one now, or one `post` would refuse, is not posted, and waits for a re-review
    (`yes`)."""
    d = ledger_dir()
    pull(d)
    owner = owner_id(a.repo)
    r = run([sys.executable, REVIEW_SITE, "site"], check=False)
    if r.returncode != 0:
        print("the review site cannot be read; the reviews wait for a later round: %s" % r.stderr.strip())
        return
    site = r.stdout.strip()
    if run(["git", "cat-file", "-e", site + "^{commit}"], cwd=a.repo, check=False).returncode != 0:
        run(["git", "fetch", "-q", "origin"], cwd=a.repo, check=False)
    rows = {}  # this agent's rows of the reviews ledger, by file and audited commit, in the order written
    for x in read_jsonl(d, "reviews"):
        if x.get("owner") == owner:
            rows.setdefault((x.get("file"), x.get("main")), []).append(x)
    def settle(au, state, names, **more):  # the state of ``names``, yeses of ``au``, in the reviews ledger
        append(d, "reviews", owner, dict(more, file=au["file"], main=au["main"], site=site, state=state,
                                         decls=sorted(names), at=iso(), owner=owner))

    posted = waiting = dropped = 0
    again = {}  # the declarations waiting for a re-review, by file
    for au in sorted(newest_audits(d, owner).values(), key=lambda x: x.get("audited_at", "")):
        entries, states = yes_states(au, rows.get((au["file"], au["main"]), []))
        again[au["file"]] = sorted(n for n, s in states.items() if s == "re-review")
        pending = {n: e for n, e in entries.items() if states[n] is None}
        old = [n for n, e in pending.items() if not isinstance(e, dict)]
        if old:
            settle(au, "dropped", old, why=OLD_FORM)
            print("%s: dropped, %s" % (au["file"], OLD_FORM))
            dropped += 1
            pending = {n: e for n, e in pending.items() if n not in old}
        if not pending:
            continue
        g = run(["git", "rev-parse", "%s:%s" % (site, au["file"])], cwd=a.repo, check=False)
        if g.returncode != 0 or g.stdout.strip() != au["blob"]:
            if run(["git", "merge-base", "--is-ancestor", au["main"], site], cwd=a.repo, check=False).returncode != 0:
                waiting += 1  # the site has not reached the audited commit yet
                continue
            why = ("the file changed on the site before these were posted" if "posted" in states.values()
                   else "the file changed after the audit, before the site showed it")
            settle(au, "dropped", pending, why=why)
            print("%s: dropped, %s" % (au["file"], why))
            dropped += 1
            continue
        shown = standard_now(sorted(pending))
        if shown is None:
            waiting += 1
            continue
        actions, redo, left = [], {}, []
        for n, e in sorted(pending.items()):
            if shown.get(n) is None:
                left.append(n)
                continue
            # `post` refuses a whole comment for one action it cannot take: one recorded under laxer checks waits too.
            why = "; ".join(entry_problems(n, e)) or stale(e, shown[n].get("version"))
            if why:
                redo[n] = why
            else:
                actions.append(action_of(n, e))
        if actions:
            fd, path = tempfile.mkstemp(prefix="redteam-reviews-", suffix=".jsonl")
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as f:
                    f.write("".join(json.dumps(x, ensure_ascii=False) + "\n" for x in actions))
                p = run([sys.executable, REVIEW_SITE, "post", path, "--commit", site,
                         "--agent", "Tau Ceti red team, %s, session %s" % (au["model"], owner),
                         "--note", "Red-team audit of %s at Tau Ceti %s." % (au["file"], au["main"][:12])],
                        check=False)
            finally:
                os.remove(path)
            if p.returncode != 0:  # the site moved, or GitHub failed: try again next round
                print("%s: not posted, tried again next round: %s" % (au["file"], p.stderr.strip()))
                waiting += 1
            else:
                settle(au, "posted", [x[decision(x)] for x in actions])
                posted += 1
                print("%s: posted %s" % (au["file"], counted(actions)))
        if redo:
            settle(au, "re-review", redo)
            again[au["file"]] += sorted(redo)
            for n, why in sorted(redo.items()):
                print("%s: %s waits for a re-review: %s" % (au["file"], n, why))
        if left:
            settle(au, "left out", left)
            print("%s: left out, the site has no page for %s" % (au["file"], ", ".join(left)))
    push(d, "redteam: reviews, %d posted" % posted)
    again = {f: sorted(ns) for f, ns in again.items() if ns}
    if again:
        print("To re-review: read each text (review_site.py standard --json NAME...), then record a decision on it "
              "(redteam.py yes @update.json):")
        for f, ns in sorted(again.items()):
            print("  %s: %s" % (f, ", ".join(ns)))
    print("review site at %s: %d files posted, %d waiting, %d dropped, %d declarations to re-review"
          % (site[:12], posted, waiting, dropped, sum(len(ns) for ns in again.values())))


def cmd_yes(a):
    """New decisions for the yes of this agent's newest audit of a file, after a re-review (R0): `reviews` posts them
    once the site shows the file as audited. Each is for a declaration `reviews` holds for a re-review, and they are
    checked as the audit's are."""
    d = ledger_dir()
    pull(d)
    owner = owner_id(a.repo)
    row = load_arg_json(a.json)
    if not isinstance(row, dict) or not row.get("file") or not row.get("yes"):
        die('an update needs "file" and "yes": {"file": "<path>", "yes": {"<full name>": {"cells": {...}, '
            '"approve" | "write" | "edit": ...}}}', 1)
    extra = sorted(set(row) - {"file", "yes"})
    if extra:
        die("an update has only \"file\" and \"yes\", not %s: the reviews go up under the audit's model"
            % ", ".join(extra), 1)
    au = newest_audits(d, owner).get(row["file"])
    if au is None:
        die("no audit of %s by this agent (%s): a re-review replaces decisions of an audit" % (row["file"], owner), 1)
    rows = [x for x in read_jsonl(d, "reviews") if x.get("owner") == owner and (x.get("file"), x.get("main")) == (
        au["file"], au["main"])]
    _, states = yes_states(au, rows)
    bad = []
    for n in row["yes"] if isinstance(row["yes"], dict) else []:
        if states.get(n) != "re-review":
            why = (NOT_WAITING.get(states[n], "its state is %s" % states[n]) if n in states
                   else "the audit of %s has no review of it" % au["file"])
            bad.append("%s: %s; `yes` takes only a declaration `reviews` names to re-review" % (n, why))
    bad += yes_problems({"yes": row["yes"], "model": au.get("model")}, au.get("matrix") or {}, findings(d))
    if bad:
        die("re-review of %s not recorded (%d problems):\n  - %s" % (row["file"], len(bad), "\n  - ".join(bad[:60])), 1)
    append(d, "reviews", owner, {"file": au["file"], "main": au["main"], "state": "re-reviewed", "yes": row["yes"],
                                 "at": iso(), "owner": owner})
    push(d, "redteam: re-reviewed %s" % au["file"])
    print("recorded: %d decision%s for %s; `reviews` posts them" % (len(row["yes"]), "" if len(row["yes"]) == 1 else "s",
                                                                    au["file"]))


# --- sync -------------------------------------------------------------------------------

def cmd_sync(a):
    d = ledger_dir()
    pull(d)
    owner = owner_id(a.repo)
    changed = 0
    for f in findings(d).values():
        if f.get("status") != "pr-open":
            continue
        r = run(["gh", "pr", "view", str(f["pr"]), "--repo", REPO_SLUG, "--json", "state,url"], check=False)
        if r.returncode != 0:
            die("gh pr view %s failed; stop the round.\n%s" % (f["pr"], r.stderr))
        pr = json.loads(r.stdout)
        if pr["state"] == "MERGED":
            row = {"id": f["id"], "status": "landed"}
        elif pr["state"] == "CLOSED":
            row = {"id": f["id"], "status": "rejected",
                   "resolution": "PR #%s closed without merging (%s); read why, and re-mark it superseded "
                                 "if another change fixed it" % (f["pr"], pr["url"])}
        else:
            continue
        row.update({"at": iso(), "owner": owner})
        append(d, "findings", owner, row)
        changed += 1
        print("%s %s (#%s)" % (f["id"], row["status"], f["pr"]))
    push(d, "redteam: sync %d" % changed)
    print("synced: %d changed" % changed)


# --- whoami / astra ----------------------------------------------------------------------

def cmd_whoami(a):
    print(owner_id(a.repo))


def cmd_astra(a):
    """The same model and effort the chatgpt-math MCP uses, through `codex exec`. The question is
    read from stdin, so its size is not limited by the command line; the answer is printed."""
    q = a.question[1:] if a.question.startswith("@") else a.question
    if not os.path.isfile(q):
        die("the question must be a file (write it to one first): %s" % q)
    # $REDTEAM_CODEX_HOMES lists Codex logins to try in order (colon-separated), so one that
    # has hit its usage limit falls through to the next; unset means the default login.
    homes = [os.path.expanduser(h) for h in os.environ.get("REDTEAM_CODEX_HOMES", "").split(":") if h] or [None]
    errors = []
    for home in homes:
        out = os.path.join(ledger_dir(), "astra-%d-%d.txt" % (os.getpid(), now()))
        env = dict(os.environ, CODEX_HOME=home) if home else None
        with open(q) as stdin:
            try:
                r = subprocess.run(["codex", "exec", "-m", a.model, "-c", 'model_reasoning_effort="%s"' % a.effort,
                                    "--ephemeral", "--skip-git-repo-check", "-s", "read-only", "-o", out, "-"],
                                   stdin=stdin, capture_output=True, text=True, timeout=2400, env=env)
            except (OSError, subprocess.TimeoutExpired) as e:
                errors.append("%s: %s" % (home or "default login", e))
                continue
        answer = open(out).read() if os.path.exists(out) else ""
        if os.path.exists(out):
            os.remove(out)
        if r.returncode == 0 and answer.strip():
            print(answer)
            return
        tail = [ln for ln in r.stderr.splitlines() if ln.startswith("ERROR")][-1:] or r.stderr.splitlines()[-1:]
        errors.append("%s: exit %d %s" % (home or "default login", r.returncode, " ".join(tail)))
    die("Astra is unavailable this round:\n  " + "\n  ".join(errors))


# --- tally ------------------------------------------------------------------------------

def cmd_tally(a):
    d = ledger_dir()
    pull(d)
    fs = list(findings(d).values())
    audits = {r["file"] for r in read_jsonl(d, "audits")}
    live = [f for f in fs if f.get("status") in LIVE]
    wins = [f for f in live if f.get("severity") in WIN]
    out = {
        "wins": len(wins),
        "critical": sum(1 for f in wins if f["severity"] == "CRITICAL"),
        "landed": sum(1 for f in fs if f.get("status") == "landed"),
        "open": sum(1 for f in fs if f.get("status") == "pr-open"),
        "queued": sorted((f for f in live if f.get("status") == "confirmed"),
                         key=lambda f: (SEVERITIES.index(f["severity"]), f.get("at", "")))[:a.limit],
        "queued_findings": sum(1 for f in live if f.get("status") == "confirmed"),
        "queued_topics": len({topic(f) for f in live if f.get("status") == "confirmed"}),
        "losses": sum(1 for f in fs if f.get("status") in ("refuted", "rejected")),
        "needs_human": sum(1 for f in fs if f.get("status") == "needs-human"),
        "suspected": sum(1 for f in fs if f.get("status") == "suspected"),
        "files_audited": len(audits),
        "patterns": {},
    }
    for f in live:
        p = out["patterns"].setdefault(f["pattern"], {"count": 0, "wins": 0, "rubric": f["rubric"], "examples": []})
        p["count"] += 1
        p["wins"] += f["severity"] in WIN
        if len(p["examples"]) < 3:
            p["examples"].append("%s %s%s" % (f["file"], f["decl"], " #%s" % f["pr"] if f.get("pr") else ""))
    if a.json:
        print(json.dumps(out, indent=1, ensure_ascii=False))
        return
    print("Wins %d (%d critical) · landed %d · PRs open %d · queued %d topics (%d findings) · suspected %d · "
          "losses %d · needs a human %d · files audited %d" % (
              out["wins"], out["critical"], out["landed"], out["open"], out["queued_topics"],
              out["queued_findings"], out["suspected"], out["losses"], out["needs_human"],
              out["files_audited"]))
    if out["queued"]:
        print("\nQueued (confirmed, no PR yet), worst first:")
        for f in out["queued"]:
            print("  %-8s %s  %s %s — %s  [topic: %s]" % (f["severity"], f["id"], f["file"], f["decl"], f["claim"],
                                                       "/".join(topic(f)[1:2])))
    if out["patterns"]:
        print("\nPatterns (confirmed and since), most frequent first:")
        for name, p in sorted(out["patterns"].items(), key=lambda kv: (-kv[1]["count"], kv[0])):
            print("  %3d  %-40s rubric: %-13s e.g. %s" % (p["count"], name, p["rubric"], "; ".join(p["examples"])))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=".", help="the TauCeti checkout (default: current directory)")
    ap.add_argument("--remote", default=REMOTE, help="where claims live (default: the TauCeti repo)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    n = sub.add_parser("next", help="rank the files to hunt next")
    n.add_argument("--ref", default="origin/main")
    n.add_argument("--under", default="", help="only files under this path prefix")
    n.add_argument("--limit", type=int, default=10)
    n.add_argument("--cooloff-days", type=int, default=30)
    n.add_argument("--offline", action="store_true", help="skip the open-PR and claim lookups")
    n.add_argument("--json", action="store_true")
    c = sub.add_parser("claim", help="acquire | renew | release a claim on a file or a PR branch")
    c.add_argument("action", choices=["acquire", "renew", "release"])
    c.add_argument("file", help="a TauCeti/ file path, or branch/<pr>")
    c.add_argument("--ttl", type=int, default=1500)
    f = sub.add_parser("finding", help="record a finding or an update to one")
    f.add_argument("json", help="the record as JSON, or @path to a JSON file")
    au = sub.add_parser("audit", help="record a finished file audit")
    au.add_argument("json", help="the audit as JSON, or @path to a JSON file")
    au.add_argument("--ref", default="origin/main")
    sub.add_parser("sync", help="mark findings landed or rejected once their PRs merge or close")
    sub.add_parser("reviews", help="post this agent's reviews on the review site where it shows the file as audited")
    y = sub.add_parser("yes", help="record a re-review: new decisions for declarations `reviews` names to re-review")
    y.add_argument("json", help='{"file": <path>, "yes": {<full name>: <decision>}} as JSON, or @path to a JSON file')
    sub.add_parser("whoami", help="print this agent's id (kept in <checkout>/.mathlib-quality/redteam-owner)")
    q = sub.add_parser("astra", help="ask gpt-6-astra through the Codex CLI; prints the answer")
    q.add_argument("question", help="a file holding the question (or @file)")
    q.add_argument("--model", default="gpt-6-astra")
    q.add_argument("--effort", default="max")
    t = sub.add_parser("tally", help="the scoreboard")
    t.add_argument("--json", action="store_true")
    t.add_argument("--limit", type=int, default=10)
    a = ap.parse_args()
    a.repo = os.path.abspath(os.path.expanduser(a.repo))
    {"next": cmd_next, "claim": cmd_claim, "finding": cmd_finding, "audit": cmd_audit, "sync": cmd_sync,
     "reviews": cmd_reviews, "yes": cmd_yes, "whoami": cmd_whoami, "astra": cmd_astra, "tally": cmd_tally}[a.cmd](a)


if __name__ == "__main__":
    main()
