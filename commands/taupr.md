---
name: taupr
description: The Tau Ceti worker loop — one unit of work per round, first that applies: rebase, fix CI, fix findings, review a stalled PR, else author a new one. Authoring checks the source material first, cleans up, and opens the PR; CI reviews it. We only self-review a PR that CI has left unreviewed for an hour.
---

# /taupr — the Tau Ceti worker loop

Modelled on the reference worker (`kim-em/TauCetiWorker`): **a round does exactly one unit
of work — the first of these that applies.**

```
R1  REBASE     one of our PRs has a genuine TauCeti/ conflict after a sibling merged
R2  FIX-CI     one of our PRs has `build` red — it cannot be reviewed until it builds
R3  FIX        one of our PRs has findings: fix the code, or contest a wrong one in-thread
R4  REVIEW     one of our PRs is green but CI has not reviewed it for ≥ 1h  →  --post
R5  AUTHOR     otherwise: open a new PR advancing a target
```

**Maintenance outranks authoring.** R1–R4 come first so PRs already in flight cannot be
starved by opening yet more of them. A round that finds work at R2 stops there.

**CI reviews our PRs; we do not race it.** Opening the PR is enough — `pr-build` runs, and
a green build triggers the review automatically. Self-reviewing costs your subscription and
your wall-clock, so R4 exists only as a *fallback* for PRs CI has left sitting.

**Merging, closing and de-duplicating are the repo's CI, not this loop.** Do not merge
green PRs, close stuck ones, or sweep duplicates from here.

> **A GitHub API failure aborts the round.** It must never read as "nothing to do" and fall
> through to R5 — a transient outage would then author duplicate PRs. No data means stop,
> not proceed.

## Usage

```
/taupr                     run ONE round and stop
/taupr --only <r>[,<r>]    restrict to given steps: rebase,fix-ci,fix,review,author
/taupr --skip <r>[,<r>]    drop steps from the cascade
/taupr status              print the board: every open PR, its build + review state, age
/taupr --review-age <dur>  R4 threshold (default 1h)
/taupr --reset-intake      re-ask the chain questions
```

**`/taupr` itself runs one round and stops.** It has no loop flag of its own — recurrence
comes from the harness (see "Running it continuously"), which is the same arrangement
`/beastmode` uses.

`/taupr --only fix,fix-ci` tends existing PRs only; `/taupr --skip author` is the same
cascade without opening anything new.

## Prerequisites

- `gh` authenticated
- `codex` logged into a ChatGPT subscription — the reviewer for R4 (see "Why codex")
- `uvx` on PATH — how `tauceti-review` is fetched
- A TauCeti checkout with pinned mathlib built, plus a TauCetiRoadmap clone

---

# The board

Every round starts by reading state. **Never infer from labels** — they lag.

```bash
gh pr list --repo TauCetiProject/TauCeti --state open \
   --json number,headRefName,headRefOid,author,title,body,updatedAt --limit 100
```

Per PR, two independent facts:

**Build** — `build` is a commit *status* on the head sha (not a check-run):

```bash
gh pr view <PR> --repo TauCetiProject/TauCeti --json statusCheckRollup \
  --jq '.statusCheckRollup[] | select(.context=="build") | {state, createdAt}'
```

**Review** — the newest scoreboard comment, parsed from its machine block:

```bash
gh api --paginate /repos/TauCetiProject/TauCeti/issues/<PR>/comments?per_page=100
```

Keep comments containing `<!--tauceti-scoreboard-->`, take the newest by `updated_at`, and
read `<!--tauceti-meta:v1 {...}-->` for `head_sha`, `overall` and per-rubric `states`.
**A review applies only to the `head_sha` it names** — if that differs from the current
head, the PR counts as unreviewed.

Rubric states: `green` · `stale` · `blocking_request` · `blocking_block` · `error` · `absent`.

---

# R1 — Rebase

One of our PRs has a genuine content conflict under `TauCeti/` after a sibling merged.
(Root `TauCeti.lean` is auto-synced on `main` and no longer collides.) Rebase, rebuild,
push with `--force-with-lease`.

# R2 — Fix CI

One of our PRs has `build` red. **This outranks R3**: a PR that does not build cannot be
reviewed, so fixing findings on it is wasted work.

Reproduce locally with `lake build`, fix, push. The repo rules are CI-enforced: no `sorry`,
no axioms beyond `propext`/`Classical.choice`/`Quot.sound` (so no `native_decide`), Mathlib's
linter set, **no `maxHeartbeats` overrides** (`/buzz` it instead).

# R3 — Fix findings

One of our PRs has an adverse rubric. Read the rubric threads, then either fix the code or
contest.

**Contesting goes in the thread the finding came from** — a reply whose `in_reply_to_id` is
that rubric's thread root:

```bash
gh api --method POST \
  "/repos/TauCetiProject/TauCeti/pulls/<PR>/comments/<ROOT_ID>/replies" \
  -f body="$(cat contest.md)"
```

Silent failures: a top-level `gh pr comment` is the *issue* endpoint and is never read as a
contest; a reply to nothing belongs to no rubric; and a body containing `tauceti-reply:` or
`tauceti-rubric:` is **dropped as machine output** — so when you quote the conflicting
thread, quote the prose and strip the markers.

Contest only a **genuine contradiction** (one finding requires X, another not-X; or a later
round reverses an earlier one). Link the conflicting thread, quote its wording with rubric
and round, and show why both cannot hold. Disagreeing with a finding you merely dislike is
not this — implement it, or show it wrong on the merits.

**A contest does not re-trigger CI** — contest re-reviews belong to the local worker, so
follow it with R4's command on that PR regardless of age.

Push fixes with `--force-with-lease` (see R5).

# R4 — Review a stalled PR

**Only when all three hold:**

1. `build` is **success** at the current head,
2. there is **no scoreboard for that head sha**, and
3. it has been **≥ 1h** since the `build` status was posted (`--review-age` to change).

The wait is the point. CI reviews automatically once the build goes green; posting sooner
just spends your subscription on work the project was about to do for free. An hour without
a scoreboard means CI is not coming.

```bash
uvx --from git+https://github.com/TauCetiProject/TauCetiReview \
    tauceti-review <PR> --reviewer codex --post
```

Posting also claims the head, so a late CI run skips (`skipping to avoid duplicate spend`),
and the scoreboard is canonical whoever posts it — `merge_from_scoreboard.py` takes the
newest by `updated_at` with *no access bar: any author*.

Drop `--post` for a private look that records nothing.

**Why codex.** Claude writes the Lean, so a Claude reviewer checks its own family's work.
And on macOS only codex gets a real clean room: its credential is a file
(`~/.codex/auth.json`) copied into a throwaway `CODEX_HOME`, whereas
`~/.claude/.credentials.json` is absent under a Keychain login, so the Claude reviewer falls
back to your real `HOME` and sees your personal config.

# R5 — Author a new PR

Only when R1–R4 found nothing.

### 5a. Intake — once per chain, not per PR

Read `.mathlib-quality/pr-session.json`; **if it exists, ask nothing**. Otherwise ask once
and write it: what the chain delivers, which roadmap area (and whether this is new
mathematics or improving existing code), and from what source. Per-PR description and
target id are derived from the diff, never asked.

The roadmap gates **new** declarations only. Refactoring, proof simplification, modest
generalisation, relocation and documentation are always in scope with no roadmap entry — do
not report "off-roadmap" as a risk on a refactor chain.

### 5b. Check the source material first

**Do not rebuild mathematics that already exists.** In priority order: the roadmap as
written, then review-quality library code, then adapting the named source.

Per source: pin and **clone** it (record `repo@sha` — a worker that never cloned cannot
produce one), read its index before grepping (blueprint, dep graph, `## Main results`),
search **three vocabularies** (your name, the source's convention, and the operator that
cannot be renamed away — that last one finds things), read the *neighbourhood* rather than
the grep hits, and check whether your result is a step inside a bigger proof.
`references/pr-workflow.md` § "The source sweep" has the full method.

Mathlib absence additionally needs an untruncated full-name grep **and** a compiled
`example` probe — typeclass-derived and auto-generated results are text nowhere.

**Duplication uses the native mechanism.** Claim `author/<focus>/<target-id>` and stop if
you lose it; check open PRs for the same `tauceti-target` marker id. Roadmap targets others
have claimed on the [intentions board](https://github.com/leanprover-community/intentions)
are likewise off-limits.

### 5c. Build, then clean up

`/develop` to plan and `/beastmode` to execute, for genuinely new material.

Then **`/cleanup` on every changed `.lean` file** — ported or new, full workflow, including
the `/simplify` and `/buzz` hand-offs — and **`/decompose-proof`** for any proof over 30
lines (50 is the hard cap).

This is the most-skipped step, because by now the code already builds so nothing complains.
It is gated: see "The pre-PR gate" below.

### 5d. PR body

```text
Roadmap: CanonicalAreaName        ← or `Roadmap: none`; canonical roadmap DIRECTORY name,
                                     never inferred from a TauCeti/ path
<!--tauceti-target:v1 {"focus":"<area>","id":"<canonical-target-id>"}-->
Provenance: <source repo> @ <revision>, <license>, <files and declarations>
```

A PR without the target marker is invisible to the duplicate sweeper. Keep the body in sync
with the code — a drifted body is itself a review finding.

### 5e. Push and create

**`--force-with-lease`, always** — other agents may be on this branch:

```bash
git push --force-with-lease=<headRefName>:<observed_oid> \
    https://github.com/<owner>/<repo> HEAD:<headRefName>
# new branch: --force-with-lease=<branch>:   (empty = create-only)
gh pr create --repo TauCetiProject/TauCeti --title "..." --body-file pr.md
```

A `! [rejected] (stale info)` means someone moved the branch — re-observe and decide afresh,
never fall back to a plain push.

**Then the round ends.** Do not review what you just opened: CI will. It becomes eligible
for R4 only if still unreviewed an hour after its build goes green.

---

## The pre-PR gate

`gh pr create` is blocked until `.mathlib-quality/review-receipt.json` records the cheap
checks that must precede a PR. Write it at the end of 5c:

```json
{
  "head_sha": "<git rev-parse HEAD>", "base_ref": "origin/main",
  "cleanup": [
    {"file": "TauCeti/Foo/Bar.lean", "status": "done",
     "phases": "P1-P7 incl 5a, 6.5 simplify, 6.6 buzz"},
    {"file": "TauCeti/Foo/Baz.lean", "status": "skipped",
     "reason": "import-line change only"}
  ],
  "duplication_check": {"checked_at": "<ISO>", "open_prs_examined": [12,13], "overlaps": []},
  "source_sweep": [{"repo": "github.com/org/FLT", "revision": "<full sha>",
                    "queries": ["<literal grep>"], "verdict": "absent"}]
}
```

**No review fields are required** — there is no pre-PR review in this design, so nothing
here waits on inference. The gate only checks work that is cheap to do and expensive to
skip:

- **`cleanup[]` must cover every changed `.lean` file.** The list is computed from
  `git diff merge-base..HEAD`, *not* read from the receipt, so under-reporting fails and
  names the files you missed. `done` needs `/cleanup`'s phase checklist; `skipped` needs a
  reason, and every skip is reported to the user.
- **`source_sweep[]`** needs a pinned revision and the literal queries per source; empty is
  honest only when the intake recorded no source.
- **`duplication_check`** needs to be fresh and free of unacknowledged overlaps.

If the gate blocks, a step did not happen. Do that step rather than reaching for
`PR_GATE_OVERRIDE=1`.

## Running it continuously

`/taupr` does one round per invocation. To keep it going, wrap it — the recurrence belongs
to the harness, not to this command:

```
/loop 10m /taupr          in-session: a round every ten minutes while the session lives
```

For an unattended schedule that survives the session ending, use the `schedule` skill to
create a cron running `/taupr` on the same cadence.

**What the interval does — and does not do.** It is the polling cadence: how often a round
runs, and therefore how quickly a red build or a fresh finding is picked up. It does **not**
move R4's one-hour threshold, which is measured from the `build` status timestamp. A
ten-minute tick means you act within ten minutes of that hour elapsing; a thirty-minute tick
means within thirty. Shorter reacts faster and costs more API calls and agent invocations;
longer is cheaper and lazier.

Ten minutes is the cadence the original working practice used, and it sits sensibly under
the one-hour review threshold.

Between rounds, report one line:

```
**Round <n>: <STEP> on #<PR>** — <what changed>. Open: <N> (<b> building, <r> awaiting review, <f> awaiting author).
```

## Report

```
## /taupr round <n>

Step:       <REBASE|FIX-CI|FIX|REVIEW|AUTHOR|IDLE>
PR:         #<N> <title>
Action:     <what was done>
Cleanup:    <file: done (phases) | SKIPPED — reason>   ← every skip listed
Board:      <N> open — <b> building, <r> awaiting review, <f> awaiting author, <g> green
Next:       <what the next round would pick up>
```

## Reference

- `references/tauceti.md` — verified mechanics: contest wire format, scoreboard block,
  target markers and claims, `--force-with-lease`, merge policy
- `references/pr-workflow.md` — the source sweep
- `references/mathlib-search.md` — proving mathlib-absence
- Upstream: `AGENTS.md`, `COORDINATION.md` (TauCeti); `REVIEWING.md` (TauCetiReview);
  `kim-em/TauCetiWorker` (the reference worker this cascade follows)
