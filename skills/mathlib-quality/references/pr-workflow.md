# PR workflow for a review-gated Lean repo

The governing rule: **never open a PR that has not already passed the review rubric
locally.** A PR should be a formality — by the time it exists, you already know it passes.

This is written for projects that gate merges behind an automated reviewer (an AI review
bot, a scope/roadmap checker, a house-rules linter). Mathlib itself has a human review
queue rather than a scriptable rubric, so steps 4–5 apply only where such an engine
exists; steps 0–3 and 6 apply everywhere.

The worked example throughout is **TauCeti**, whose reviewer lives in a separate repo
(`TauCetiReview`, `runner/review.py`) and is backed by ChatGPT models through the `codex`
CLI — the same models CI draws.

---

## 0. Intake, then sources before code

**Ask the user three things — once per chain, not once per PR.** They determine what
everything downstream is measured against:

| Question | Why it matters |
|---|---|
| **What is this chain delivering?** | The overall goal the run of PRs serves |
| **Which roadmap area / target family?** | The layer these PRs land in. "Not on the roadmap" is a valid and *important* answer — it predicts a scope finding, so it should be known now, not in round four |
| **From what source, if any?** | Upstream repo, sibling project (e.g. FLT), or paper, with revision and license. Drives the provenance block in step 5. "Original work" is valid |

Inferred candidates (branch name, changed files, the roadmap's open targets) make
reasonable *options* to offer, but the user's answer is the one that counts — a wrong
guess propagates straight into the PR body's attribution and provenance lines, where the
reviewer checks it.

**Then persist the answers and stop asking.** They go in
`.mathlib-quality/pr-session.json`; every later PR in the chain reads that file instead of
re-prompting. Per branch, the one-line description of *this* PR and its specific target
marker are **derived** from the diff plus the chain's roadmap area, and merely stated. A
long chain should cost exactly one round of questions, at the start.

Re-ask only when the chain's provenance actually changes (`--reset-intake`), not per PR.

That same file is the **sentinel arming the PR gate** in step 5 — writing it is what opts
the chain into mechanical enforcement.

Then, before writing any new Lean, check **every source the roadmap names** for the
content — upstream research repos, sibling formalisation projects (e.g. FLT) — **and
pinned Mathlib itself**.

### The source sweep

Mathlib-absence has a hard standard (§ below: untruncated grep **and** a compiled probe).
Source-repo absence needs one too, or "checked FLT ✓" becomes a box a worker ticks on the
way to writing the thing that was already there. Six steps, per source, per result:

**1. Pin it and clone it.** Record `repo@sha`. Browsing the GitHub web UI does not count:
you cannot grep it, and you cannot say afterwards which revision you looked at. **The
recorded revision is the artifact** — a worker who never cloned cannot produce one, which
is what makes this checkable rather than performative.

**2. Read the index before grepping.** Formalisation projects curate exactly the list you
need: a blueprint, a dependency graph, `## Main results` in module docstrings, the README's
status table. This is the highest-yield minute in the whole sweep and it is usually skipped.

**3. Search three vocabularies, not one.** The same result appears under:
- *your* name for it,
- the **source's** naming convention (which differs from mathlib's, and from yours),
- the **operator or constant** that must occur in any statement of it — the one piece of
  notation that cannot be renamed away.

The third is the one that finds things, because it survives every naming disagreement.

**4. Read the neighbourhood, not the hits.** Open the module where the result *would* live
and read the section. A grep returns lines; what you need is whether the fact is present in
any form. Results routinely exist as an unnamed `have` inside a larger proof, or as a
special case of something stated more generally — neither is greppable by name.

**5. The sub-lemma check.** If the source proves a theorem whose proof would *need* your
result, read that proof. Your lemma is very likely a step inside it. This is the same
discipline `/develop` Phase 1e Step 1 requires — read the source's full proof including
every sub-lemma, page by page, not headline plus summary — applied before writing rather
than during planning.

**6. Port and adapt; do not rederive.** If it is there, take it, with provenance (repo,
license, revision, declaration names). Rederiving what the roadmap points at is the most
expensive way to fail review, because the reviewer will find the source you didn't.

#### What does not count as a sweep

| Claimed check | Why it fails |
|---|---|
| "GitHub code search found nothing" | No pinned revision, indexes lag, and it silently misses what is not indexed |
| "The name isn't in the source" | Naming conventions differ between projects; step 3 exists precisely because of this |
| "I read the README / the paper's abstract" | Papers don't name their sub-steps, and READMEs describe headline results only |
| "It's not in the source's blueprint" | The blueprint indexes *stated* results, not the lemmas inside proofs — step 5 |
| A truncated grep | Same failure as the mathlib check: a `head`-ed grep that scrolls past its own hit |

**The repo's own open PRs are one of those sources.** A result can be absent from `main`,
absent from Mathlib, and still already written — sitting in an open PR, quite possibly one
of your own earlier branches in this chain. Step 6 deliberately keeps several branches in
flight, which is what turns this from a theoretical collision into a routine one.

```bash
gh pr list --state open --json number,title,headRefName,files,body --limit 100
```

Compare in descending order of sharpness: **same roadmap target marker** (two PRs claiming
one target is a direct duplicate), then same declaration names, then same files touched,
then same source section ported. An overlap is not automatically fatal — a deliberate
stacked follow-up is fine — but it is resolved *before more code is written*: rebase onto
the open branch, narrow the scope, or close the older PR. Check again at step 5, because
the list moves while you work.

**Port and adapt; do not rederive.** Rederiving something the roadmap already points at is
the most expensive way to fail review, because the reviewer will find the source you
didn't.

Mathlib absence is a claim that has to be *earned*. See
`mathlib-search.md` § "Proving absence is a compile-checked claim" for the standard: an
untruncated full-name grep **and** a compiled `example` probing the generic routes. A name
grep plus a statement grep, both clean, still missed **three duplicates in one file** —
Mathlib supplies facts generically via typeclasses and auto-generated lemmas that appear
as text nowhere.

## 1. Genuinely new code only

Once step 0 has established the content really is new:

| Stage | Command |
|---|---|
| Plan | `/develop` |
| Execute | `/beastmode` |
| Assess the headline declarations | `/mathlibable` |

`/mathlibable` on the headline declarations is what stops a project quietly accumulating
material that belonged upstream.

## 2. Cleanup is unconditional

**Ported or new, every file gets the full `/cleanup`.** Ported code is not exempt — a
faithful port of someone else's file still has to meet this project's standards.

Then check whether `/decompose-proof` is needed: **any proof over 30 lines** is a
candidate, and **50 lines is the hard cap**. (These are the same thresholds `/cleanup`
Phase 4 already applies — see `commands/cleanup.md` item 12 LENGTH.)

## 3. CI gates, locally

Run the gates CI will run, before CI runs them:

- `lake build`
- the repo's audit executables
- the repo's lint script

## 4. Local rubric dry-run — no PR yet

This is the step that makes the whole workflow work, and the one most people don't realise
is available.

**A review engine that accepts a diff on stdin does not need a PR to exist.** TauCeti's
runner takes `--diff-file`, `--pr-desc-file` and `--no-post`, so it runs against a **local
branch** with nothing on GitHub at all.

Stage a directory holding what the engine expects to read:

| Item | Contents | Note |
|---|---|---|
| `code/` | `git archive` of the branch head | not the dirty working tree |
| roadmap clone | a **fresh** clone | a stale local roadmap checkout produced a false scope `BLOCK` |
| `mathlib/` | symlink to the project's pinned `.lake/packages/mathlib` | must be the pinned revision, not a system copy |
| `diff.txt` | **merge-base** diff vs `origin/main` | not a two-dot diff |
| `pr_desc.txt` | the PR body you intend to use | the reviewer reads it, so draft it now |

Then invoke the engine with `--no-post --mode manual`. **Nothing touches GitHub.**

Two details that cost real time when got wrong:

- **Clone the roadmap fresh each run.** A stale checkout is indistinguishable, to the
  engine, from the branch being out of scope — it emits a scope `BLOCK` that has nothing
  to do with your code.
- **Merge-base, not two-dot.** A two-dot diff includes everything `main` gained since you
  branched, and the reviewer will comment on all of it.

For **API-design questions** — which shape the reviewer will prefer — ask the same model
*beforehand* via the `ask_chatgpt_math` MCP. Cheaper than discovering the preference in
round four of the rubric.

## 5. Iterate until green, then create the PR

Repeat step 4 until **every rubric is green**. Only then `gh pr create` — at that point the
PR is known to pass, because it has already passed.

**Re-check the open PRs here.** Step 0's check happened before the code was written; by now
hours have passed and, because step 6 keeps a queue moving, other PRs have opened —
including your own. This is the check that catches the race, and it is the one that keeps
a pipelined chain from submitting the same work twice.

**This is enforced mechanically, not by discipline.** On a green run, step 4 writes
`.mathlib-quality/review-receipt.json` (`head_sha`, `all_green`, per-rubric verdicts, the
literal invocation and its exit code, and a `duplication_check` recording which open PRs
were examined and what overlapped). The plugin's `PreToolUse` hook — `hooks/pr_gate.sh` —
blocks `gh pr create` unless that receipt exists, is green, carries a fresh duplication
check with no unacknowledged overlaps, and matches the current `HEAD`. A stale receipt (the
branch moved since the review) blocks too, naming both commits; so does a duplication check
older than `PR_GATE_DUP_MAX_AGE_MIN` (default 60), since a duplication check is a claim
about *now*.

An overlap you intend to proceed with is recorded rather than deleted —
`{"pr": 13, "kind": "same-files", "acknowledged": true, "note": "..."}` — and the same
reasoning goes in the PR body.

The reason for a hook rather than a firmer rule: opening a PR and waiting for the server
reviewer is *easier* and *feels like progress*, so under a long chain, attention drifts
there. Making it the blocked path means the cheapest route to a PR runs the dry run first.
The gate is armed by the step-0 session file and fails open on infrastructure trouble, so
it is inert everywhere else and cannot wedge you out of your own repo.

The PR body carries:

- the roadmap attribution line
- the exact layer / target
- **full provenance**: source repo, license, pinned revision, file and declaration names
- the project's machine-readable target marker

The marker and the code must stay **in sync**; a body that has drifted from what the branch
actually does is itself a review finding.

## 6. Never wait around

Waiting on a review is not a reason to stop working.

- A **10-minute cron** checks open PRs for reviews and movement. Read the **scoreboard
  states / `head_sha`**, never the label — labels lag and lie.
- **Between server rounds, pipeline.** Take the next candidates through steps 0–5 locally,
  so a queue of locally-green branches is always ready while the earlier ones merge.

The throughput limit should be your own step-0–5 work, never the review server.

---

## Why this shape

Every clause exists because the opposite failed:

| Clause | The failure it prevents |
|---|---|
| 0 — intake first | Guessing the roadmap target, then carrying the guess into the PR body's attribution where the reviewer checks it |
| 0 — intake persisted | Re-interrogating the user on every branch of a long chain |
| 0/5 — open PRs as a source | Writing again what is already sitting in an open PR — most often your own earlier branch in the same chain |
| 5 — receipt + hook | A worker opening the PR and waiting for the server reviewer because that felt like progress |
| 0 — sources first | Rederiving what the roadmap already names; three Mathlib duplicates in one file |
| 2 — cleanup unconditional | "It's a port, so it's fine as-is" |
| 4 — local dry-run | Burning review rounds on findings you could have read locally |
| 4 — fresh roadmap clone | A false scope `BLOCK` from a stale checkout |
| 5 — green before create | A PR whose first review is its fourth |
| 6 — cron + pipeline | Idle time that isn't the server's fault |

## Source

Contributed 2026-08-08 from TauCeti (`tauceti-pr-workflow-5c917ea4`,
`data/community_learnings/archived/20260808_tauceti.jsonl`).
