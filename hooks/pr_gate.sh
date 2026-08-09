#!/usr/bin/env bash
# mathlib-quality :: PR gate (PreToolUse on Bash)
#
# WHAT THIS DOES
#   Blocks `gh pr create` unless the local review-rubric dry run (/pre-submit Step 8)
#   has actually been run, is GREEN, and was run against the CURRENT commit.
#
#   This exists because instruction text does not hold. Opening a PR and waiting for
#   the server reviewer is easier and feels like progress, so workers drift to it.
#   The fix is not a louder rule — it is making the shortcut the blocked path, so the
#   cheapest route to a PR runs the dry run first.
#
# HOW IT IS GATED (inert unless you opted in)
#   Activation hinges on .mathlib-quality/pr-session.json, which /pre-submit Step 0a
#   writes at the start of a PR chain. No session file -> this hook is inert and every
#   `gh pr create` proceeds normally. It never affects a repo that isn't running the
#   managed workflow.
#
# FAIL DIRECTION (deliberately asymmetric)
#   * Missing / stale / non-green receipt  -> BLOCK. That is the whole point.
#   * Infrastructure trouble (no python3, not a git repo, unreadable files, unparseable
#     payload) -> ALLOW. A broken gate must not wedge the user out of their own repo.
#
# ESCAPES (all immediate)
#   * PR_GATE_OVERRIDE=1 gh pr create ...          -> one-shot bypass
#   * touch .mathlib-quality/pr_gate_disabled      -> disable for the repo
#   * rm .mathlib-quality/pr-session.json          -> leave the managed workflow
#
# I/O CONTRACT
#   stdin : PreToolUse JSON. We read tool_input.command.
#   exit 0 : allow. exit 2 : block, with the reason on stderr (fed back to the agent).

payload="$(cat 2>/dev/null || true)"

root="${CLAUDE_PROJECT_DIR:-$PWD}"
session="$root/.mathlib-quality/pr-session.json"
receipt="$root/.mathlib-quality/review-receipt.json"

# --- escapes and inertness -------------------------------------------------------
[ -n "$PR_GATE_OVERRIDE" ] && exit 0
[ -f "$root/.mathlib-quality/pr_gate_disabled" ] && exit 0
[ -f "$session" ] || exit 0          # not a managed PR chain -> inert

command -v python3 >/dev/null 2>&1 || exit 0   # no parser -> fail open

# --- is this actually `gh pr create`? --------------------------------------------
cmd="$(printf '%s' "$payload" | python3 -c '
import json,sys
try:
    print(json.load(sys.stdin).get("tool_input",{}).get("command",""))
except Exception:
    print("")
' 2>/dev/null)"

[ -n "$cmd" ] || exit 0              # unparseable -> fail open

# Normalise whitespace so `gh   pr  create` and compound commands both match.
norm="$(printf '%s' "$cmd" | tr '\n' ' ' | tr -s ' ')"
case "$norm" in
  *"gh pr create"*) ;;
  *) exit 0 ;;                       # not a PR creation -> allow
esac

# --- receipt must exist ----------------------------------------------------------
if [ ! -f "$receipt" ]; then
  cat >&2 <<'EOF'
BLOCKED: /pre-submit Step 8 (local review-rubric dry run) has not been run.

No .mathlib-quality/review-receipt.json exists. Opening a PR and waiting for the
server reviewer is exactly the shortcut this gate prevents — the rubric runs on a
LOCAL branch, with no PR in existence, via the engine's --diff-file / --pr-desc-file
/ --no-post flags.

Do this instead:
  1. Stage: code/ (git archive of HEAD), a FRESH roadmap clone, mathlib/ (symlink to
     the pinned .lake/packages/mathlib), diff.txt (MERGE-BASE diff vs the base
     branch), pr_desc.txt.
  2. Run the INNER engine with --no-post --mode manual. On Tau Ceti that is
     runner/review.py (the layer carrying --diff-file/--pr-desc-file/--no-post),
     NOT the tauceti-review CLI, which requires an existing PR number.
  3. Fix findings, re-run, until every rubric is green.
  4. Write .mathlib-quality/review-receipt.json (schema in commands/pre-submit.md
     Step 8) recording head_sha, the invocation, exit code, and per-rubric verdicts.

Then `gh pr create` will proceed. See references/pr-workflow.md sections 4-5 and
references/tauceti.md.

If you deliberately choose the post-PR flow instead (open the PR, then review it
with `tauceti-review <PR>`), that is a legitimate choice this gate cannot verify:
re-run with PR_GATE_OVERRIDE=1. You still owe the iterate-until-green loop, and
contests go in the rubric thread they came from, never a top-level comment.
EOF
  exit 2
fi

# --- receipt must be green, and must match the current commit --------------------
verdict="$(python3 - "$receipt" "$session" <<'EOF' 2>/dev/null
import json,os,subprocess,sys,datetime
try:
    r = json.load(open(sys.argv[1]))
except Exception as e:
    print("ERR unreadable receipt: %s" % e); raise SystemExit
if not r.get("all_green") is True:
    bad = [k for k,v in (r.get("rubrics") or {}).items() if v != "green"]
    print("NOTGREEN " + (", ".join(bad) if bad else "all_green is not true"))
    raise SystemExit

# --- duplication check: did we look at the open PRs, recently, and come up clean? ---
d = r.get("duplication_check")
if not isinstance(d, dict) or d.get("overlaps") is None:
    print("NODUP"); raise SystemExit
unack = [o for o in d["overlaps"]
         if not (isinstance(o, dict) and o.get("acknowledged") is True)]
if unack:
    def lab(o):
        if isinstance(o, dict):
            return "#%s (%s)" % (o.get("pr", "?"), o.get("kind", "overlap"))
        return str(o)
    print("DUP " + "; ".join(lab(o) for o in unack)); raise SystemExit
try:
    maxage = float(os.environ.get("PR_GATE_DUP_MAX_AGE_MIN", "60"))
except Exception:
    maxage = 60.0
ts = d.get("checked_at")
if maxage > 0 and ts:
    try:
        dt = datetime.datetime.fromisoformat(str(ts).replace("Z", "+00:00"))
        now = datetime.datetime.now(dt.tzinfo) if dt.tzinfo else datetime.datetime.now()
        age = (now - dt).total_seconds() / 60.0
    except Exception:
        age = None            # unparseable timestamp -> do not block on freshness
    if age is not None and age > maxage:
        print("DUPSTALE %d %d" % (age, maxage)); raise SystemExit

# --- source sweep: was each named source actually pinned and searched? --------------
ss = r.get("source_sweep")
if ss is None:
    print("NOSWEEP"); raise SystemExit
if not isinstance(ss, list):
    print("NOSWEEP"); raise SystemExit
# An empty sweep is only honest when the chain declared no source. Cross-check the
# Step-0a intake, so "source_sweep": [] cannot be used to skip a source the user named.
if not ss:
    named = ""
    try:
        sv = json.load(open(sys.argv[2])).get("source")
        if isinstance(sv, dict):
            named = str(sv.get("repo") or "").strip()
        elif isinstance(sv, str):
            named = sv.strip()
    except Exception:
        named = ""            # unreadable session -> do not block on this
    if named and named.lower() not in ("original work", "none", "n/a", "-"):
        print("EMPTYSWEEP " + named); raise SystemExit

bad = []
for e in ss:
    if not isinstance(e, dict):
        bad.append("<malformed entry>"); continue
    name = e.get("repo") or "<unnamed repo>"
    rev = str(e.get("revision") or "").strip()
    qs = e.get("queries") or []
    if len(rev) < 7:
        bad.append("%s: no pinned revision" % name)
    elif not (isinstance(qs, list) and len([q for q in qs if str(q).strip()]) >= 1):
        bad.append("%s: no recorded queries" % name)
if bad:
    print("SWEEP " + "; ".join(bad)); raise SystemExit

try:
    head = subprocess.run(["git","rev-parse","HEAD"], capture_output=True, text=True,
                          timeout=10).stdout.strip()
except Exception:
    print("OK"); raise SystemExit          # cannot determine HEAD -> fail open
if not head:
    print("OK"); raise SystemExit
if r.get("head_sha") != head:
    print("STALE %s %s" % (r.get("head_sha","<none>")[:12], head[:12]))
    raise SystemExit
print("OK")
EOF
)"

case "$verdict" in
  OK|"") exit 0 ;;                   # green and current, or infra trouble -> allow
  ERR*)  exit 0 ;;                   # unreadable receipt -> fail open
  NODUP*)
    cat >&2 <<'EOF'
BLOCKED: no open-PR duplication check in the review receipt.

A declaration can be absent from main, absent from mathlib, and still already
written — sitting in an open PR, including one of your own earlier branches in
this chain. Running several branches in flight is what makes this collide.

  gh pr list --state open --json number,title,headRefName,files,body --limit 100

Compare against what this branch introduces — same roadmap target marker first
(two PRs claiming one target is a direct duplicate), then same declaration
names, then same files touched. Record the result in
.mathlib-quality/review-receipt.json:

  "duplication_check": {
    "checked_at": "<ISO now>", "open_prs_examined": [12, 13],
    "overlaps": []
  }

A real overlap you intend to proceed with is recorded, not deleted:
  "overlaps": [{"pr": 13, "kind": "same-files", "acknowledged": true,
                "note": "stacked on #13; rebase once it merges"}]
EOF
    exit 2 ;;
  NOSWEEP*)
    cat >&2 <<'EOF'
BLOCKED: no source_sweep in the review receipt.

Before new material is written, every source the roadmap names must be swept —
upstream research repos, sibling formalisation projects (FLT and the like) —
not just pinned Mathlib. "Checked it" is not a sweep; the six-step method is in
references/pr-workflow.md section "The source sweep":

  1. Pin and CLONE it (the recorded revision is the artifact — web-UI browsing
     leaves nothing to cite and no revision you can name afterwards)
  2. Read the index first: blueprint, dep graph, "## Main results", README
  3. Search THREE vocabularies: your name, the source's naming convention, and
     the operator/constant that cannot be renamed away (this one finds things)
  4. Read the neighbourhood, not the grep hits — results live as unnamed `have`s
     inside larger proofs, or as a more general statement
  5. If the source proves something that would NEED your result, read that proof
  6. Port and adapt; do not rederive

Record in .mathlib-quality/review-receipt.json:

  "source_sweep": [
    {"repo": "github.com/org/FLT", "revision": "<full sha>",
     "queries": ["<literal grep 1>", "..."], "verdict": "absent"}
  ]

Genuinely original work with no roadmap source: "source_sweep": []
EOF
    exit 2 ;;
  EMPTYSWEEP*)
    printf 'BLOCKED: empty source_sweep, but this chain named a source.\n\nChain source (from .mathlib-quality/pr-session.json): %s\n\n%s\n' \
      "${verdict#EMPTYSWEEP }" \
      "An empty sweep asserts there was nothing to search, which contradicts the intake you gave at Step 0a. Sweep that source (references/pr-workflow.md, 'The source sweep') and record repo + full revision + the literal queries. If the chain genuinely has no source, correct it with /pre-submit --reset-intake rather than emptying the sweep." >&2
    exit 2 ;;
  SWEEP*)
    printf 'BLOCKED: the source sweep is not citable.\n\n%s\n\n%s\n' \
      "${verdict#SWEEP }" \
      "Each swept source needs a full pinned revision AND the literal queries run. A worker who never cloned the repo cannot produce a revision — which is the point: a sweep you cannot cite did not constrain what you wrote. See references/pr-workflow.md section 'The source sweep'." >&2
    exit 2 ;;
  DUPSTALE*)
    set -- $verdict
    printf 'BLOCKED: the open-PR duplication check is stale (%s min old, max %s).\n\n%s\n' \
      "$2" "$3" \
      "A duplication check is a claim about now, and in a pipelined chain that expires fast — PRs have likely opened since, including your own. Re-run 'gh pr list --state open' and refresh duplication_check.checked_at. Tune the window with PR_GATE_DUP_MAX_AGE_MIN (0 disables it)." >&2
    exit 2 ;;
  DUP*)
    printf 'BLOCKED: this branch overlaps an open PR.\n\nOverlaps: %s\n\n%s\n' \
      "${verdict#DUP }" \
      "Resolve it before opening another PR — rebase onto that branch, narrow this PR'\''s scope, or close the older one. If the overlap is deliberate (a stacked follow-up), mark it acknowledged:true in the receipt with a note saying why, and say the same in the PR body." >&2
    exit 2 ;;
  NOTGREEN*)
    printf 'BLOCKED: the local review rubric is not green.\n\nNot green: %s\n\n%s\n' \
      "${verdict#NOTGREEN }" \
      "Iterate /pre-submit Step 8 until every rubric passes, then create the PR. A PR opened now would spend a server review round on findings you can already read locally." >&2
    exit 2 ;;
  STALE*)
    set -- $verdict
    printf 'BLOCKED: the review receipt is stale.\n\nReviewed commit: %s\nCurrent HEAD:   %s\n\n%s\n' \
      "$2" "$3" \
      "The branch has moved since the rubric last ran, so the green result no longer describes what you are about to submit. Re-run /pre-submit Step 8 against the current commit and refresh .mathlib-quality/review-receipt.json." >&2
    exit 2 ;;
  *) exit 0 ;;
esac
