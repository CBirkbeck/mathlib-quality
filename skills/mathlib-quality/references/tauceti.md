# Tau Ceti: how review actually works

Project-specific wire formats and rules for [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti).
`pr-workflow.md` holds the generic workflow; this holds the parts that are true *here* and
would be wrong to guess. Sourced from the repo's own `AGENTS.md`, `COORDINATION.md`, and
the `TauCetiReview` engine (`runner/cli.py`, `runner/review.py`, `runner/verdict.py`).

The three repos: **TauCeti** (AI-owned code) · **TauCetiRoadmap** (human-owned roadmaps) ·
**TauCetiReview** (rubrics + engine).

---

## Contesting a review — in the thread it came from

**The single most important mechanic, and the easiest to get silently wrong.**

The engine gathers contests from `/repos/{owner}/{repo}/pulls/{pr}/comments` — the **review
comment** endpoint — and keeps only comments whose `in_reply_to_id` points at a thread root
carrying `<!--tauceti-rubric:NAME-->`. So:

> **A contest is a reply inside the rubric's own review thread. Nothing else is a contest.**

```bash
# 1. Find the rubric thread root (in_reply_to_id == null, carries the rubric marker)
gh api --paginate --jq '.[]' "/repos/TauCetiProject/TauCeti/pulls/<PR>/comments?per_page=100" \
  | python3 -c 'import json,sys,re
for l in sys.stdin:
    c=json.loads(l)
    if c.get("in_reply_to_id") is None:
        m=re.search(r"tauceti-rubric:([a-z][a-z-]*?)\s*-->", c.get("body",""))
        if m: print(m.group(1), c["id"])'

# 2. Reply IN that thread — this is the contest
gh api --method POST \
  "/repos/TauCetiProject/TauCeti/pulls/<PR>/comments/<ROOT_ID>/replies" \
  -f body="$(cat contest.md)"
```

### What is silently ignored

| What you might do | What happens |
|---|---|
| `gh pr comment` (a top-level PR comment) | **Ignored.** That is the *issue* comment endpoint; the engine never reads it for contests |
| A new review comment that isn't a reply | **Ignored** — no `in_reply_to_id`, so it belongs to no rubric |
| A reply in the wrong rubric's thread | Attributed to **that** rubric, not the one you meant |
| A body containing `tauceti-reply:` or `tauceti-rubric:` | **Dropped** — the engine reads those markers as its own comments |

That last one is a genuine trap. `AGENTS.md` tells you to *quote the conflicting thread's
wording* when you show a contradiction — and if you paste a block that still carries the
engine's HTML markers, your contest is discarded as machine output. **Quote the prose;
strip the markers.**

### A contest does not re-trigger CI

From `review.yml`: *"Author CONTESTS (a reply in a rubric thread) are no longer handled
here: the local worker owns contest re-reviews so they have a single execution owner and
one durable watermark, rather than racing a CI run."*

So posting the contest is only half of it — **someone must then run `tauceti-review <PR>`**
to adjudicate it. A contest left unadjudicated simply sits there.

`/review` as an **exact line** (not mentioned in prose) re-triggers a full CI review, and
only for users with write access or better.

### When to contest, per AGENTS.md

Contest when **two findings contradict** — one requires X and another requires not-X, or a
later round reverses a change an earlier finding required. Do *not* silently satisfy one
and let the other re-fire.

The required shape: contest one of the threads, **link the conflicting one**, **quote its
wording (rubric and round)**, and explain why both cannot hold. *Show* the contradiction;
do not merely assert it.

### How the re-run treats it

Replies fold into the rubric's case file as `author_replies`, so the re-run **audits your
contest** rather than re-judging the diff blind. A contest re-fires the rubric only when
its comment id is **strictly greater** than the watermark the rubric last adjudicated
(`last_reply_seen`) — so deleting or minimising your newest reply can never re-fire it, and
re-posting the same argument twice does nothing. Say it once, in the right thread.

---

## Reading review state — the scoreboard, never the label

The canonical reviewer posts exactly one issue comment carrying `<!--tauceti-scoreboard-->`
and a machine-readable block:

```text
<!--tauceti-meta:v1 {"head_sha":"...","overall":"approved|changes requested|blocked",
                     "clean":true,"states":{"correctness":"green",...},
                     "review_id":"...","schema_version":1}-->
```

```bash
gh api --paginate /repos/TauCetiProject/TauCeti/issues/<PR>/comments?per_page=100
```

Keep comments with the `tauceti-scoreboard` marker, take the **newest by `updated_at`**,
parse the `tauceti-meta` JSON. **Never scrape the rendered Markdown heading, and never read
the PR label** — labels lag. No valid comment means unreviewed: behave conservatively, do
not merge on it.

**A review applies only to the `head_sha` it names.** A new commit needs a fresh review —
which is exactly why the local review receipt is bound to a commit too.

Rubric states: `green` · `stale` (approved, but at an older sha) · `blocking_request` ·
`blocking_block` · `error` (infrastructure, no parseable verdict — blocks merge but spawns
no thread) · `absent` (never run).

---

## Running the review yourself

Two layers, and the difference matters.

**`tauceti-review <PR#>` — the documented CLI.** Requires an **existing PR**: it reads the
head sha, diff and description from GitHub via `gh`. It **defaults to a dry run** and posts
nothing; `--post` is the opt-in (there is no `--no-post` at this layer). Runs on your
logged-in Claude/Codex subscription instead of metered API keys — that, not PR-avoidance,
is the reason to run it locally.

```bash
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 42
tauceti-review 42 --rubrics scope,correctness --mode manual
tauceti-review 42 --post          # publish, under YOUR gh identity
```

`--mode commit` (default) re-runs only rubrics not already passing; `--mode manual` runs
all. `--no-coordinate` gives a private pass that touches the PR at all — otherwise a
contributing run posts a short-lived `review in progress` marker so a fleet never pays
twice for one commit.

**`runner/review.py` — the inner engine.** This is the layer that takes `--diff-file`,
`--pr-desc-file` and `--no-post`, against a hand-staged workspace (`--tool-cwd` with
`code/`, `roadmap/`, `mathlib/`, plus `--store`, `--rubrics-dir`). `--pr` is still a
required argument, but with the diff and description supplied from files and `--no-post`
set, it need not name a live PR — which is what makes a genuine **pre-PR** dry run
possible.

Staging notes that cost real time: clone the roadmap **fresh** (a stale checkout reads as
out-of-scope and yields a false scope `BLOCK`), symlink the **pinned**
`.lake/packages/mathlib`, and take a **merge-base** diff, not a two-dot one.

---

## Before you write: roadmap, marker, claim

**The roadmap gates new mathematics only.** A new definition, theorem, instance, notation
or file needs to advance a specific roadmap target. **Improving existing code is always in
scope and needs no roadmap entry** — refactoring, simplifying proofs, modest
generalisation, relocation, cleaner idioms, documentation. Do not treat "not on the
roadmap" as a blanket scope failure; it only bites for *new* mathematics.

If something you want to build is not on the roadmap, say so and leave it to a human.
**Never open a PR or issue in TauCetiRoadmap yourself.**

Every PR description carries one standalone attribution line — canonical roadmap
*directory* name, and **not** inferred from a `TauCeti/` path, since code organisation and
roadmap scope do not coincide:

```text
Roadmap: CanonicalAreaName
```
```text
Roadmap: none
```

`Roadmap: none` covers genuinely general, cross-cutting, infrastructure or dependency work.

**Duplication has a native mechanism here — use it over file-overlap guessing.** Before
authoring a target, claim `author/<focus>/<target-id>` (COORDINATION.md § 3) and stop if
you lose it. Put the marker in the PR body:

```text
<!--tauceti-target:v1 {"focus":"<area>","id":"<canonical-target-id>"}-->
```

The `id` is deterministic (roadmap file plus declaration or label), never a free-form slug.
The duplicate sweeper closes a newer duplicate only when **both** PRs carry the same
marker, keeping the lower number — so a missing marker means your PR is invisible to dedup.

---

## Pushing — `--force-with-lease`, always

`[HARD]` rule, COORDINATION.md § 1. **Never a plain `git push` to a PR branch.**

```bash
git push --force-with-lease=<headRefName>:<observed_oid> \
    https://github.com/<headRepositoryOwner>/<headRepository> HEAD:<headRefName>
```

`observed_oid` is the tip you based your work on. If anyone moved the branch since, the
push fails closed (`! [rejected] (stale info)`) — **that is the system working**. Re-observe
and decide afresh; never fall back to a plain push. Creating a new branch uses an empty
expected value (`--force-with-lease=<branch>:`) so you create-only.

---

## Merge, and what not to do

All rubrics green **on the current head** + only `TauCeti/` touched + CI green → **merges
automatically**. A PR also touching `lake-manifest.json` / `lean-toolchain` can auto-merge
once `bump-guard` confirms a forward-only bump. Anything touching `scripts/`, `.github/` or
the lakefile always needs a human.

Three prohibitions worth stating plainly:

- **Never `--admin`-merge an AI-authored PR.** Landing is the pipeline's job.
- **Never delete a PR's human-owned changes to get past the build gate.** If a PR
  intentionally touches `scripts/`/`.github/`/lakefile, those changes *are* the deliverable
  and the gate routes it to a human on purpose. Leave such PRs alone rather than "fixing"
  them toward auto-mergeability.
- **Never merge or close without visible cause.** Close only on GitHub-visible budget
  evidence (`review-budget-spent`, or stale with changes requested) — never a private local
  counter. A `keep`/`hold`/`wip`/`human`/`do-not-close` label opts a PR out entirely.

## Repo rules that shape the code

`main` is always green: no `sorry`, no axioms beyond `propext` / `Classical.choice` /
`Quot.sound` (so no `native_decide`), Mathlib's linter set including no `maxHeartbeats`
overrides. One topic per PR — ship a prerequisite refactor separately.

**No backwards compatibility.** When declarations move, are renamed, replaced or deleted,
update every in-repo use and remove the obsolete names in the same PR. No aliases, wrapper
declarations, forwarding import modules, `deprecated_module` shims, or duplicate theorem
names. Breaking an external user's source is not a reason to keep an obsolete surface.
