---
name: taupr
description: The complete Tau Ceti PR pipeline — review a branch against the real rubrics BEFORE any PR exists (via the inner engine, which makes no network calls), then create the PR and post the verdict immediately so CI's metered run skips. Also reviews open PRs on your own subscription. Chain-aware: asks intake once, then runs branch after branch.
---

# /taupr — the Tau Ceti PR pipeline

Everything from branch to merge on [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti),
including reviewing the PRs that get made.

**The discipline: iterate to green privately, then open the PR, then immediately record the
verdict.**

- **Before the PR** (P6), review the local branch until every rubric is green. This posts
  nothing, so the rounds it takes are nobody's business and cost the PR nothing.
- **After the PR** (P8), `--post` at once. A private run leaves *no review state on GitHub*,
  and merging requires a GitHub-visible all-green review for the current head — so the PR
  still needs reviewing, and posting is how you get that in minutes instead of waiting.
  It also claims the head, so CI's metered run skips: your subscription displaces the
  project's API bill.

The two phases use **different tools**, because `tauceti-review` takes a PR number and
reads the head, diff and description from GitHub — it has nothing to work with before the
PR exists. P6 therefore drives the inner engine (`runner/review.py`, which carries
`--diff-file` / `--no-post`); P8 uses `tauceti-review`.

Mechanics this command depends on are in `references/tauceti.md`; read it before editing
this file. Getting a wire format wrong here fails *silently*.

## Usage

```
/taupr                        full pipeline for the current branch
/taupr dryrun                 P6 alone — review the LOCAL branch, no PR, nothing posted
/taupr review [<PR>...]       review open PRs (see P8 on when to --post)
/taupr review <PR> --post     publish the scoreboard + per-rubric threads, as you
/taupr contest <PR> <rubric>  post a contest in that rubric's own thread
/taupr status [<PR>]          read scoreboards (tauceti-meta), no inference
/taupr watch                  set up / run the open-PR monitoring loop
/taupr --reset-intake         re-ask the chain questions
```

## Prerequisites (Phase 0 checks these)

- `gh` authenticated — reads PRs, posts as **you**
- `uvx` (or `uv`) on PATH — how `tauceti-review` is fetched for **P8**
- **A TauCetiReview checkout** — required for **P6**, which runs `runner/review.py` and
  reads `rubrics/` directly. `uvx` alone does not give you these
- `claude` and/or `codex` logged into a subscription — **at least one**. With both, the
  reviewer is drawn per rubric, like CI
- A TauCeti checkout with its pinned mathlib built, and a TauCetiRoadmap clone

---

# Full pipeline

```
P0  INTAKE          chain-scoped, asked once
P1  SOURCES         source sweep + mathlib absence + duplication (target marker + claim)
P2  BUILD           /develop → /beastmode, if writing new material
P3  CLEANUP         /cleanup every touched file; /decompose-proof where needed
P4  LOCAL GATES     lake build + audits + lint + repo rules
P5  PR BODY         Roadmap: line, target marker, provenance
P6  DRY RUN         review the LOCAL branch, no PR yet — iterate until green
P7  CREATE          --force-with-lease push, then gh pr create
P8  POST            tauceti-review <PR> --post, immediately — record the verdict
P9  CONTEST         only genuine contradictions, in-thread
P10 MONITOR         scoreboard polling; pipeline the next branch meanwhile
P11 MERGE           auto-merge; never --admin
```

**The two review phases are different things and both are needed.** P6 is *private*: it
posts nothing, so it costs the PR nothing and nobody sees a half-finished branch — that is
where you iterate to green. P8 is *the record*: a local dry run leaves no review state on
GitHub at all, and merging requires a GitHub-visible all-green review for the current head.
P6 makes P8 a formality that comes back green on the first try.

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

## P6 — Local dry run, before the PR exists

Iterate here until every rubric is green. Nothing touches GitHub, so a branch that needs
four rounds costs four private runs instead of four public ones.

**This phase cannot use `tauceti-review`** — that CLI takes a PR number and reads the head,
diff and description from GitHub, so it has nothing to work with before the PR exists. The
pre-PR run drives the **inner engine**, `runner/review.py`, which is the layer carrying
`--diff-file` / `--pr-desc-file` / `--no-post`:

```bash
REVIEW=<a TauCetiReview checkout>     # git clone https://github.com/TauCetiProject/TauCetiReview
WORK=<a fresh staging dir>
STORE=<a fresh empty dir>
```

`uvx` is not enough for this phase — it installs the `tauceti-review` console script, and
P6 needs the repo itself for `runner/review.py` **and** `rubrics/`.

Stage a workspace holding what the engine reads:

| Item | Contents |
|---|---|
| `code/` | `git archive` of the branch head — not the dirty working tree |
| `roadmap/` | a **fresh** clone of TauCetiRoadmap; a stale checkout reads as out-of-scope and yields a false scope `BLOCK` |
| `mathlib/` | symlink to the project's **pinned** `.lake/packages/mathlib` |
| `diff.txt` | **merge-base** diff vs `origin/main`, not a two-dot diff |
| `pr_desc.txt` | the PR body you drafted in P5 — the reviewer reads it, so it must be the real one |

```bash
python3 "$REVIEW/runner/review.py" \
    --repo TauCetiProject/TauCeti --pr 0 --mode manual --no-post \
    --rubrics-dir "$REVIEW/rubrics" --tool-cwd "$WORK" \
    --code-path code --roadmap-path roadmap --mathlib-path mathlib \
    --diff-file "$WORK/diff.txt" --pr-desc-file "$WORK/pr_desc.txt" \
    --store "$STORE" --head-sha "$(git rev-parse HEAD)" \
    --auth subscription --providers claude,codex \
    --daily-budget 1000000 \
    --scoreboard-file "$WORK/scoreboard.md" --threads-dir "$WORK/threads"
```

Then read `$WORK/scoreboard.md` and `$WORK/threads/` — that is where the verdicts land.

**Why it works with no PR:** `review.py` makes **no GitHub calls and no network calls** —
it reads the diff, description and code from the paths above. `--pr` is required by the
parser but is purely a *label*: it names record ids, a ledger key, and an output directory,
and appears in one line of prompt context. `--pr 0` is fine.

**Four flags whose defaults differ from the wrapper — omit them and this misbehaves
silently:**

| Flag | Inner-engine default | Why you must set it |
|---|---|---|
| `--auth` | **`api`** | The wrapper flips this to `subscription`. Left alone, the engine wants `ANTHROPIC_API_KEY`/`OPENAI_API_KEY` and **bills them** — the opposite of why you are running locally |
| `--daily-budget` | **`5.0`** | The wrapper passes `1000000`. Left alone, rubrics get deferred once the *notional* spend estimate passes $5 and the scoreboard reads `budget cap reached; deferred N and after` — a truncated review that looks like a finished one |
| `--scoreboard-file` / `--threads-dir` | unset | Where the output is written. Without them you have run a review you cannot read |
| `--mode` | `commit` | `manual` forces every rubric to run. `commit` carries prior approvals forward, which is meaningless on a scratch store |

`--store` is **any empty writable directory** — despite its help text saying "checkout of
the reviews branch". The ledger is created empty if `ledger.json` is absent. Use a fresh
scratch dir per branch; reusing one carries stale case files across unrelated reviews.

**Fix, re-stage, re-run — until green.** Re-stage properly each round: `code/` and
`diff.txt` are snapshots, so a fix you made after staging is not in the review you just ran.

For **API-design questions** — which shape the reviewer will prefer — ask the same model
beforehand via the `ask_chatgpt_math` MCP, rather than discovering the preference in round
four.

> This is the inner engine, not the documented command. Its flags can move without notice.
> If the invocation fails, fall back to creating the PR and iterating with
> `tauceti-review <PR>` (bare, no `--post`) — private in effect, at the cost of a visible
> half-finished PR **and of CI reviewing each intermediate head at the project's expense**
> (`pr-build` fires on every push; see P8). That cost is the reason to prefer getting this
> phase working: P6 is the only point where iteration is genuinely free.

## P7 — Push and create

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
being opened and left to the server reviewer, and `/taupr` does the opposite — P6 already reviewed it privately and P8 records that verdict
immediately and iterates to green. Creating a PR outside `/taupr` still goes through the gate.

**Go straight to P8 — do not wait for `pr-build`.** The claim is what saves the project
money, and it is contested the moment the build goes green.

## P8 — Post the review, immediately

P6 established the branch is green privately. **That leaves no review state on GitHub** —
and merging requires a GitHub-visible all-green review for the current head. This phase
puts it there.

Same engine, same rubrics, same scoreboard as CI, but inference runs on your logged-in
subscription, so there is no per-token bill.

```bash
# print the verdicts for PR #42, posting nothing:
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 42

# add --post to publish the scoreboard and per-rubric threads, as you:
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 42 --post
```

**Post immediately on creating the PR — do not dry-run again here, and do not ask.** You
already did the dry running in P6; repeating it now just delays the record and risks losing
the head claim. Two verified reasons to be prompt:

1. **It claims the head, so CI's metered run skips.** De-contention is scoped to the
   commit: first claimer wins, and *a different model is not a distinct unit*. A run that
   finds the head claimed prints `skipping to avoid duplicate spend`. Posting promptly is
   how your subscription displaces the project's API bill — which is the entire reason the
   local path exists.
2. **Your scoreboard is canonical.** `merge_from_scoreboard.py` takes the newest scoreboard
   comment by `updated_at` with **no access bar — any author**. A review posted under your
   identity drives auto-merge exactly as the bot's does.

Waiting is the expensive option. CI's `review.yml` fires the instant `pr-build` succeeds,
so hesitating here means racing CI and often losing — and then the project pays for a
review you had already done.

The one thing you give up by posting before the build finishes: the engine passes CI's
build conclusion into the prompt so the reviewer can assert the code compiles. Post early
and that is blank, and the engine injects nothing. It is best-effort context, not a gate —
P4 established locally that the thing builds.

**This should come back green on the first try.** Same engine, same rubrics, same diff as
P6. If it does not, the interesting question is *why the two runs disagree*: a stale P6
staging (you fixed something after `git archive`), a different reviewer drawn for a
borderline rubric, or a scope rubric that reads the real PR body differently from your
`pr_desc.txt`. Do not just re-run and hope — a disagreement between P6 and P8 means one of
them was measuring the wrong thing.

### On an open PR, a dry run does not save the project anything

The rule is about **whether the PR exists**, not who created it.

`pr-build` fires on `pull_request_target: [opened, synchronize, reopened]` — so **every push
to an open PR** triggers a build, and a successful build triggers `review.yml`. CI is going
to review that head whether or not you dry-ran it first.

This inverts the usual instinct:

| Situation | Bare dry run | `--post` |
|---|---|---|
| **PR does not exist yet** (P6) | Free. Nothing is watching, iterate as long as you like | n/a |
| **PR is open** | CI reviews that head anyway — the project pays, and your dry run bought nothing but information | Claims the head, CI skips, **your subscription pays instead** |

So on an open PR, posting is the *cheaper* option for the project, not the riskier one. The
expensive habit is pushing repeatedly to an open PR and dry-running each time: every one of
those heads gets a CI review you already paid for locally.

Which is the real argument for P6 — it is the only phase where iteration is genuinely free.

**Bare dry runs remain right for**: a PR you did not create and do not intend to publish a
verdict on; a rubric you are re-checking out of curiosity; checking state *without* claiming
the head; and the P6 fallback, where the inner-engine invocation failed and you are
iterating on an open PR instead. In that fallback, expect CI to review your intermediate
heads — that is the cost of the fallback, and a reason to prefer getting P6 working.

> **macOS caveat, and it applies to every review you publish from this machine.** The clean
> room — a throwaway HOME seeded with only the reviewer's own credential — is what stops
> your personal `CLAUDE.md`, skills, plugins and MCP servers from colouring a review. On
> macOS the login lives in the keychain, so it **falls back to your real HOME** and prints a
> note. `--auth api` restores the guarantee but bills tokens, defeating the point. Know
> that the reviews you post here are not clean-room reviews.

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

## P9 — Contest, in the thread the finding came from

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

## P10 — Monitor, and never wait around

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

## P11 — Merge

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

```bash
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR> --post
```

Print a one-line scoreboard between PRs:
`**K/N reviewed. G green, C changes-requested, B blocked.** Continuing.`

**Your own chain's PRs: post, no dry run, no asking** — P8's reasoning applies unchanged.

**Someone else's PR is a different act.** You are publishing a verdict under your own name
on work you did not write, and it can auto-merge on the strength of it. Confirm once at the
start of a sweep that publishing is wanted, then post for the rest without re-asking. If
publishing is not wanted, the bare command (no `--post`) reviews privately and touches
nothing.

**Skip a PR already green at its current head.** Re-reviewing an unchanged head buys
nothing; de-contention would make you skip it anyway. Read state from the scoreboard first
(P10), not from a fresh review.

Two honesty notes. Nothing stops a local reviewer from rubber-stamping — the safeguard is
social, so read the verdicts you publish rather than posting a wall you have not looked at.
And on macOS these are not clean-room reviews (see P8): your personal configuration is
visible to the reviewer, which matters more when the PR is not yours.

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
