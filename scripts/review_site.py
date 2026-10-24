#!/usr/bin/env python3
"""Reviews on the Tau Ceti review site for declarations an agent checks as part of other work:
Voyager's full-statement test, the red team's correctness audit (mathlib-quality).

  site                       the Tau Ceti commit the site shows
  check NAME...              ON-SITE or MISSING for each name (Tau Ceti's own declarations only)
  yes FILE --agent A         one comment on the site's bulk issue, a Reviewed-by line for each line
      [--commit SHA]         of FILE (`<name><TAB><reasons, one line>`): "correctly stated". Refuses
      [--note TEXT]          a name the site does not have (--skip-missing leaves it out instead)
      [--skip-missing]       and, with --commit, a site not at SHA, so that each review is of the
      [--dry-run]            version that was checked
  no WHYFILE --agent A       a problem, "not correctly stated", as its own issue, with the reasons
      --decl NAME            in WHYFILE; the site must be at SHA. Prints `issue <number> <url>`
      --commit SHA --category AXIS [--involvement I] [--dry-run]
  fixed ISSUE [COMMIT]       a problem's fix has landed: say so on its issue (`/fixed COMMIT`)
  withdraw ISSUE NOTE        take back a review that proved wrong (`/withdraw NOTE`)

A is the agent, "TOOL, MODEL[, session S]" ("Voyager, claude-fable-5-1"): the reviews show on the
site as that AI agent's, via the account `gh` is signed in as. What deserves a yes or a no is
decided by the skills (skills/voyager/SKILL.md section 8, commands/redteam.md R6), never here;
this only checks, formats and posts. `no` runs evidence-store through `uvx`; I, the account's
relation to Tau Ceti (outsider, contributor, author), is read from Tau Ceti's history when not
given. `fixed` and `withdraw` are accepted from the account that opened the issue.

Exit codes: 0 done; 1 refused (a name or a commit the site does not have, with the reason on
stderr); 2 error.
"""
import argparse
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
#: A GitHub comment holds 65,536 characters; a longer batch goes in several comments.
COMMENT_CAP = 60000
LIBRARY = "TauCetiProject/TauCeti"


def die(msg, code):
    print(msg, file=sys.stderr)
    sys.exit(code)


def get(path):
    """The site's data, past the Pages cache: a build may be minutes old."""
    url = f"{SITE}data/{path}?t={time.time():.0f}"
    try:
        with urllib.request.urlopen(url, timeout=60) as r:
            return json.load(r)
    except Exception as e:  # noqa: BLE001 - any failure to read the site is an error, not a verdict
        die(f"error: cannot read {url}: {e}", 2)


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


def agent_mark(agent):
    parts = [p.strip() for p in agent.split(",") if p.strip()]
    if len(parts) < 2:
        die("error: --agent is 'TOOL, MODEL[, session S]'", 2)
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


def cmd_yes(a):
    rows = []
    for k, line in enumerate(open(a.file, encoding="utf-8").read().splitlines(), 1):
        if not line.strip():
            continue
        name, _, reasons = line.partition("\t")
        name, reasons = name.strip().strip("`"), " ".join(reasons.split())
        if not name or " " in name or not reasons:
            die(f"error: {a.file}:{k}: expected '<name><TAB><reasons>'", 2)
        rows.append((name, reasons))
    if not rows:
        die("error: no reviews in " + a.file, 2)
    meta = get("meta.json")
    commit = at_commit(meta, a.commit)
    missing = [n for n, _ in rows if not on_site(meta, n)]
    if missing and not a.skip_missing:
        die("refused: the site has no page for " + ", ".join(missing) + ". Nothing was posted; "
            "leave these names out (or wait for the site) and run again.", 1)
    for n in missing:
        print("skipped, not on the site:", n, file=sys.stderr)
    rows = [r for r in rows if r[0] not in missing]
    if not rows:
        print("nothing to post", file=sys.stderr)
        return
    head = [agent_mark(a.agent)]
    head.append(a.note or f"Reviews of declarations checked at Tau Ceti {commit[:12]}.")
    comments, cur = [], list(head)
    for name, reasons in rows:
        line = f"Reviewed-by: {name} — {reasons}"
        if len("\n".join(cur + [line])) > COMMENT_CAP and len(cur) > len(head):
            comments.append(cur)
            cur = list(head)
        cur.append(line)
    comments.append(cur)
    bulk = str((meta.get("store") or {}).get("bulk", 1))
    for c in comments:
        text = "\n".join(c) + "\n"
        if a.dry_run:
            print(text)
        else:
            print(gh("issue", "comment", bulk, "-R", REPO, "--body-file", "-", body=text))
    print(f"{len(rows)} reviews{' (dry run)' if a.dry_run else ''}", file=sys.stderr)


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


def cmd_fixed(a):
    print(gh("issue", "comment", str(a.issue), "-R", REPO, "--body", f"/fixed {a.commit}".strip()))


def cmd_withdraw(a):
    print(gh("issue", "comment", str(a.issue), "-R", REPO, "--body", f"/withdraw {a.note}"))


def main(argv):
    p = argparse.ArgumentParser(prog="review_site.py", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("site").set_defaults(fn=cmd_site)
    q = sub.add_parser("check")
    q.add_argument("names", nargs="+")
    q.set_defaults(fn=cmd_check)
    q = sub.add_parser("yes")
    q.add_argument("file")
    q.add_argument("--agent", required=True)
    q.add_argument("--commit", default="")
    q.add_argument("--note", default="")
    q.add_argument("--skip-missing", action="store_true")
    q.add_argument("--dry-run", action="store_true")
    q.set_defaults(fn=cmd_yes)
    q = sub.add_parser("no")
    q.add_argument("why")
    q.add_argument("--agent", required=True)
    q.add_argument("--decl", required=True)
    q.add_argument("--commit", required=True)
    q.add_argument("--category", required=True)
    q.add_argument("--involvement", choices=["outsider", "contributor", "author"])
    q.add_argument("--dry-run", action="store_true")
    q.set_defaults(fn=cmd_no)
    q = sub.add_parser("fixed")
    q.add_argument("issue", type=int)
    q.add_argument("commit", nargs="?", default="")
    q.set_defaults(fn=cmd_fixed)
    q = sub.add_parser("withdraw")
    q.add_argument("issue", type=int)
    q.add_argument("note")
    q.set_defaults(fn=cmd_withdraw)
    a = p.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main(sys.argv[1:])
