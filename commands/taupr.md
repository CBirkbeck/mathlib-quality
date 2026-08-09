---
name: taupr
description: The complete Tau Ceti PR pipeline — prepare a branch, land it, and review open PRs with tauceti-review on your own subscription. Chain-aware: asks intake once, then runs branch after branch.
---

# /taupr — the Tau Ceti PR pipeline

Everything from branch to merge on [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti),
including reviewing the PRs that get made.

**The shape of this workflow is set by one fact:** `tauceti-review` takes a **PR number** and
reads the head, diff and description from GitHub. There is no local-branch mode at the
documented layer. So the discipline here is not "never open a PR" — it is **open the PR,
then immediately review it yourself, locally, on your own subscription, and iterate to green
before spending anyone's CI budget or a human's attention.**

Mechanics this command depends on are in `references/tauceti.md`; read it before editing
this file. Getting a wire format wrong here fails *silently*.

## Usage

```
/taupr                        full pipeline for the current branch
/taupr review                 review every open PR (dry run — prints, posts nothing)
/taupr review <PR>...         review specific PRs
/taupr review <PR> --post     publish the scoreboard + per-rubric threads, as you
/taupr contest <PR> <rubric>  post a contest in that rubric's own thread
/taupr status [<PR>]          read scoreboards (tauceti-meta), no inference
/taupr watch                  set up / run the open-PR monitoring loop
/taupr --reset-intake         re-ask the chain questions
```

## Prerequisites (Phase 0 checks these)

- `gh` authenticated — reads PRs, posts as **you**
- `uvx` (or `uv`) on PATH — how the reviewer is fetched
- `claude` and/or `codex` logged into a subscription — **at least one**. With both, the
  reviewer is drawn per rubric, like CI
- A TauCeti checkout with its pinned mathlib built

---

# Full pipeline

```
P0  INTAKE          chain-scoped, asked once
P1  SOURCES         source sweep + mathlib absence + duplication (target marker + claim)
P2  BUILD           /develop → /beastmode, if writing new material
P3  CLEANUP         /cleanup every touched file; /decompose-proof where needed
P4  LOCAL GATES     lake build + audits + lint + repo rules
P5  PR BODY         Roadmap: line, target marker, provenance
P6  CREATE          --force-with-lease push, then gh pr create
P7  REVIEW          tauceti-review <PR> — iterate to green
P8  CONTEST         only genuine contradictions, in-thread
P9  MONITOR         scoreboard polling; pipeline the next branch meanwhile
P10 MERGE           auto-merge; never --admin
```

## P0 — Intake (asked once per chain)

Read `.mathlib-quality/pr-session.json`. **If it exists, ask nothing** — echo what is being
reused and continue. If absent, ask three questions once, then write it:

1. **What is this chain delivering?**
2. **Which roadmap area, and is this new mathematics or improving existing code?** The
   distinction matters: the roadmap gates **new** declarations only. Refactoring, proof
   simplification, modest generalisation, relocation and documentation are **always in
   scope with no roadmap entry**. Do not report "off-roadmap" as a risk for improvement work.
3. **From what source, if any?** — repo + revision + license, or "original work".

Per branch, this PR's one-line description and its target id are **derived** from the diff,
never asked. `--reset-intake` re-asks when the chain's provenance actually changes.

## P1 — Sources and duplication, before any new Lean

**Source sweep** (`references/pr-workflow.md` § "The source sweep"): pin and clone each
roadmap-named source, read its index before grepping, search three vocabularies, read the
neighbourhood rather than the hits, check whether your result is a step inside a bigger
proof. Port and adapt; do not rederive.

**Mathlib absence** needs the untruncated full-name grep **and** a compiled `example` probe
(`references/mathlib-search.md`). Typeclass-derived and auto-generated results are text
nowhere.

**Duplication — use the native mechanism, not a heuristic.** Before authoring a target,
take the claim and stop if you lose it:

```bash
git push --force-with-lease=refs/tauceti-claims/author/<focus>/<target-id>: \
    origin <oid>:refs/tauceti-claims/author/<focus>/<target-id>
```

Then check open PRs for the same target marker id — that, not files-touched, is what the
duplicate sweeper matches on:

```bash
gh pr list --repo TauCetiProject/TauCeti --state open --json number,title,body --limit 100
```

A PR **without** a `tauceti-target` marker is invisible to dedup, so emitting one (P5) is
part of not-duplicating.

## P2 — Build (only for genuinely new material)

`/develop` to plan, `/beastmode` to execute, `/mathlibable` on the headline declarations.
Improving existing code skips straight to P3.

## P3 — Cleanup (unconditional, ported or new)

Run `Skill(mathlib-quality:cleanup)` on **every touched file** — the full 11-phase workflow,
no phase skipping, including the Phase 6.5 `/simplify` and Phase 6.6 `/buzz` hand-offs. A
faithful port still has to meet this repo's standards.

Then `/decompose-proof` for any proof over **30 lines**; **50 is the hard cap**.

## P4 — Local gates (run what CI runs, before CI does)

```bash
lake build
```

Plus the repo's audit executables and lint script, and the standing repo rules — these are
CI-enforced and non-negotiable:

- no `sorry`
- no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (so **no `native_decide`**)
- Mathlib's linter set, including **no `maxHeartbeats` overrides** (a proof needing one is
  slow — `/buzz` it, never raise the limit)
- one topic per PR; ship a prerequisite refactor separately
- **no backwards-compatibility surface**: when declarations move, are renamed or deleted,
  update every in-repo use and remove the old names in the same PR. No aliases, wrappers,
  forwarding modules, `deprecated_module`, or duplicate theorem names

## P5 — PR body

Three things, kept **in sync with the code** — a drifted body is itself a review finding:

```text
Roadmap: CanonicalAreaName          ← or `Roadmap: none`; canonical roadmap DIRECTORY name,
                                       never inferred from a TauCeti/ path

<!--tauceti-target:v1 {"focus":"<area>","id":"<canonical-target-id>"}-->

Provenance: <source repo> @ <pinned revision>, <license>, <file and declaration names>
```

`Roadmap: none` is correct for genuinely general, cross-cutting, infrastructure or
dependency work. New mathematics must additionally cite the exact roadmap file and target.

## P6 — Push and create

**`--force-with-lease`, always** — a `[HARD]` coordination rule. Other agents may be on
this branch; a plain push can clobber them.

```bash
git push --force-with-lease=<headRefName>:<observed_oid> \
    https://github.com/<owner>/<repo> HEAD:<headRefName>
# creating a new branch: --force-with-lease=<branch>:   (empty = create-only)
```

A `! [rejected] (stale info)` is **the system working**: someone moved the branch. Re-observe
and decide afresh; never fall back to a plain push.

```bash
PR_GATE_OVERRIDE=1 gh pr create --repo TauCetiProject/TauCeti --title "..." --body-file pr.md
```

The override is correct **here and only here**: the plugin's PR gate exists to stop a PR
being opened and left to the server reviewer, and `/taupr` does the opposite — P7 runs
immediately and iterates to green. Creating a PR outside `/taupr` still goes through the gate.

## P7 — Review it yourself, now

This is the point of the command. Same engine, same rubrics, same scoreboard as CI — but
inference runs on your logged-in subscription, so there is no per-token bill.

```bash
# print the verdicts for PR #42, posting nothing:
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 42

# add --post to publish the scoreboard and per-rubric threads, as you:
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 42 --post
```

**It defaults to a dry run.** Start there — read the verdicts, fix, push, re-run. Only
`--post` when you intend to publish a review under your own GitHub identity.

Useful flags:

| Flag | Effect |
|---|---|
| `--rubrics a,b,c` | review a subset |
| `--mode manual` | force a full re-review of every rubric. Default `commit` re-runs only unresolved ones, carrying prior approvals forward as ♻️ stale until the PR is otherwise clean, then sweeping them |
| `--reviewer claude` / `codex` | pin the reviewer instead of drawing per rubric |
| `--no-mathlib` | faster, but `reuse`/`naming` lose their Mathlib grep |
| `--no-coordinate` | a private read-only pass that touches the PR **not at all** (at the cost of possible duplicate spend) |
| `--auth api` | bill `ANTHROPIC_API_KEY`/`OPENAI_API_KEY` instead of the subscription — the opposite of why you are here |
| `--keep` | keep the workspace to inspect |

**Iterate P4 → P6 → P7 until every rubric is green.** After any push the previous verdicts
are stale by construction: a review binds to the `head_sha` it names.

Two operational notes. A contributing run posts a short-lived `review in progress` marker
scoped to the head, so a fleet never pays twice for one commit — a *different model is not a
distinct unit*, only a new push is. And with both CLIs installed the reviewer is drawn
randomly per rubric, so borderline rubrics can differ between runs; that is CI's behaviour too.

## P8 — Contest, in the thread the finding came from

**Only for a genuine contradiction**: one finding requires X and another requires not-X, or
a later round reverses what an earlier round required. Do not silently satisfy one and let
the other re-fire. Disagreeing with a single finding you dislike is not this — implement it,
or show it is wrong on the merits.

Required shape: contest one thread, **link the conflicting one**, **quote its wording
(rubric and round)**, explain why both cannot hold. *Show* the contradiction.

```bash
# find the rubric thread roots
gh api --paginate --jq '.[]' \
  "/repos/TauCetiProject/TauCeti/pulls/<PR>/comments?per_page=100" \
  | python3 -c 'import json,sys,re
for l in sys.stdin:
    c=json.loads(l)
    if c.get("in_reply_to_id") is None:
        m=re.search(r"tauceti-rubric:([a-z][a-z-]*?)\s*-->", c.get("body",""))
        if m: print(m.group(1), c["id"])'

# reply IN that thread — this is the contest
gh api --method POST \
  "/repos/TauCetiProject/TauCeti/pulls/<PR>/comments/<ROOT_ID>/replies" \
  -f body="$(cat contest.md)"
```

**Silent failures to avoid:**

| Mistake | Result |
|---|---|
| `gh pr comment` | Ignored — that is the *issue* endpoint, never read for contests |
| A review comment replying to nothing | Ignored — belongs to no rubric |
| Wrong rubric's thread | Attributed to that rubric instead |
| Body containing `tauceti-reply:` / `tauceti-rubric:` | **Dropped as machine output** — when you quote the conflicting thread, quote the prose and **strip the markers** |

**A contest does not re-trigger CI.** Contest re-reviews are owned by the local worker, so
run `tauceti-review <PR>` afterwards or the contest sits unadjudicated. Say it once: a
re-run picks it up only when the comment id exceeds the watermark already adjudicated, so
re-posting the same argument does nothing.

`/review` on its **own line** (not in prose) re-triggers a full CI review, write access or better.

## P9 — Monitor, and never wait around

Read state from the **scoreboard**, never the label:

```bash
gh api --paginate /repos/TauCetiProject/TauCeti/issues/<PR>/comments?per_page=100
```

Keep comments carrying `<!--tauceti-scoreboard-->`, take the **newest by `updated_at`**, and
parse the `<!--tauceti-meta:v1 {...}-->` JSON for `head_sha` and per-rubric `states`. Never
scrape the rendered Markdown; labels lag and lie. No valid comment means unreviewed — behave
conservatively and do not merge on it.

States: `green` · `stale` (approved at an older sha) · `blocking_request` · `blocking_block`
· `error` (infrastructure, no parseable verdict — blocks merge, spawns no thread) · `absent`.

**Poll on a ~10-minute cadence** and, between rounds, take the next branch through P1–P7.
The throughput limit should be your own work, never the review server. A queue of
locally-green branches should always be ready while earlier ones merge.

For an unattended loop: `/loop 10m /taupr watch`.

## P10 — Merge

All rubrics green **on the current head** + `TauCeti/`-only + CI green → **merges
automatically**. Also-touching `lake-manifest.json` / `lean-toolchain` can auto-merge once
`bump-guard` confirms a forward-only bump. Anything touching `scripts/`, `.github/` or the
lakefile always needs a human.

- **Never `--admin`-merge an AI-authored PR.** Landing is the pipeline's job.
- **Never strip a PR's human-owned changes** to make it auto-mergeable — if a PR
  intentionally touches `scripts/`/`.github/`/lakefile, those changes *are* the deliverable
  and the gate routes it to a human on purpose. Leave such PRs alone.
- **Never merge or close without visible cause** — close only on GitHub-visible budget
  evidence (`review-budget-spent`, or stale with changes requested), never a private
  counter. `keep`/`hold`/`wip`/`human`/`do-not-close` opts a PR out entirely.

---

# `/taupr review` — reviewing open PRs

Reviewing on your subscription instead of CI's metered APIs is the main cost lever the
project has. Use it on your own PRs and on the fleet's.

```bash
gh pr list --repo TauCetiProject/TauCeti --state open --json number,title,headRefName
```

For each PR, dry run first:

```bash
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR>
```

Print a one-line scoreboard between PRs — `**K/N reviewed. G green, C changes-requested, B blocked.** Continuing.` —
and only `--post` where you actually intend to publish:

```bash
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR> --post
```

**Posting publishes under your GitHub identity, as a fresh scoreboard comment** (a local run
keeps no state shared with CI, so it will not edit the bot's comment in place). Treat
`--post` as an outward-facing action: confirm before the first one unless the user has
already said to publish.

Skip a PR when the scoreboard already shows every rubric green **at the current head**;
re-reviewing an unchanged head spends inference for nothing, and the de-contention marker
will make you skip it anyway.

Nothing stops a local reviewer from rubber-stamping — the safeguard is social. Read the
verdicts before posting them.

---

## Report

```
## /taupr — <branch or review sweep>

Intake:      <chain goal / roadmap area / source — reused or asked>
Sources:     <sweep verdicts per source>
Duplication: <claim taken; target id; open-PR marker matches>
Cleanup:     <files, /cleanup outcome, decompositions>
Gates:       lake build <PASS/FAIL> · audits <…> · lint <…>
PR:          #<N> <url>   Roadmap: <area>   target: <id>
Review:      round <k> — <rubric: state, …>   overall: <approved|changes requested|blocked>
Contests:    <rubric ← thread root id, or none>
Next:        <iterate / monitoring / merged>
```

## Reference

- `references/tauceti.md` — the verified mechanics this command depends on
- `references/pr-workflow.md` — the generic workflow and the source sweep
- `references/mathlib-search.md` — proving mathlib-absence
- `commands/fix-pr-feedback.md` — Tau Ceti mode for working through findings
- Upstream: `AGENTS.md`, `COORDINATION.md` in TauCeti; `REVIEWING.md` in TauCetiReview
