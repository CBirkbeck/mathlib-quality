---
name: redteam
description: The Tau Ceti red team — an adversarial loop that audits the library file by file for wrong definitions, vacuous or mis-stated theorems, needless hypotheses, duplication of Mathlib or of other roadmaps, and code smells; confirms every big finding in Lean with a second opinion from gpt-6-astra; fixes what it finds in PRs and sees them through review to merge; and keeps the scoreboard and the common-errors list for improving the rubrics. One round per invocation; loop it with /loop.
---

# /redteam — the Tau Ceti red team

The red team finds what Tau Ceti's review let through, and fixes it. **It is adversarial and
exhaustive.** Every definition and statement is presumed wrong until you have tried to break
it and failed; every declaration gets a recorded verdict in every category; nothing is too
small to record.

**The red team wins every time it confirms a big problem** — a CRITICAL or MAJOR finding
whose evidence compiles — **and loses every time one of its claims is refuted.** Both go on
the scoreboard (`scripts/redteam.py tally`), so the way to win is to be right, not loud.

Everything on `main` was reviewed and approved, so every finding is also a miss by one of
TauCetiReview's rubrics. Recording which rubric missed it, and the error's pattern, is how
the hunt turns into better rubrics (`/redteam report`).

**REQUIRED:** the checklist, evidence recipes, Astra prompts and fix playbook are in
`references/tauceti-redteam.md`. Read it before your first hunt.

## The round

Modelled on `/taupr`: **a round does exactly one unit of work — the first that applies.**

```
R0  BOARD    every round, first: read our red-team PRs, sync the ledger, print the score
R1  REBASE   a red-team PR has a genuine TauCeti/ conflict
R2  FIX-CI   a red-team PR has `build` red
R3  FIX      a red-team PR has review findings: fix them, or contest in the rubric thread
R4  REVIEW   a red-team PR is green, and unreviewed ≥ 1h after its build → tauceti-review --post
R5  SHIP     fewer than --max-open (default 3) of this agent's PRs are open, and the ledger
             holds a confirmed finding with no PR: fix the worst one and open its PR
R6  HUNT     otherwise — unless --max-queue (default 10) topics of confirmed findings already
             wait for a PR — claim the next file and audit it down to the last declaration
    IDLE     none of the above
```

- **Maintenance outranks new work**, so PRs in flight get merged instead of piling up.
- **The PR cap is load-bearing.** A building PR and a green PR inside its first hour both
  look like nothing to do; uncapped, a ten-minute loop opens a PR every tick. **At the cap
  the round hunts instead of shipping**: finding problems is the red team's main job and
  needs no PR slot. Never open "just one more" because the fixes are small or the pipeline
  looks quick.
- **The queue cap** stops hunting when shipping has fallen too far behind, so the backlog of
  confirmed-but-unfixed findings stays small enough to ship before `main` moves under it. It
  counts topics — the PRs the backlog would make (`tally` prints both) — since one file's
  twenty nits are one PR, not twenty.
- **A GitHub API failure aborts the round.** No data means stop, never "nothing to do".
- **Merging, closing and de-duplicating belong to Tau Ceti's CI**, never to this loop.

## Usage

```
/redteam                      run ONE round and stop
/redteam status               the board and the scoreboard; changes nothing
/redteam report               write the common-errors report (see "Report")
/redteam --file <path>        hunt this file next (still claimed and fully audited)
/redteam --under <prefix>     hunt only files under this path, e.g. TauCeti/NumberTheory/
/redteam --only <r>[,<r>]     restrict to steps: rebase,fix-ci,fix,review,ship,hunt
/redteam --skip <r>[,<r>]     drop steps from the cascade
/redteam --max-open <n>       this agent's open PRs before SHIP stops (default 3; 0 = no cap)
/redteam --max-queue <n>      queued topics (future PRs) before HUNT stops (default 10)
/redteam --review-age <dur>   R4 threshold (default 1h)
```

## What the red team may touch

**Its outputs are PRs to `TauCetiProject/TauCeti` that change only files under `TauCeti/`,
replies on those PRs' own threads, claims under `refs/tauceti-claims/`, and the ledger.**
Nothing else. In particular, never:

- open issues anywhere, or touch TauCetiRoadmap, the intentions board, TauCetiReview,
  Mathlib, or any other project;
- change `scripts/`, `.github/`, the lakefile, `lake-manifest.json` or `lean-toolchain`;
- comment on, push to, label, close or merge any PR, including our own (closing is CI's job);
- "fix" a missed-by-review or missed-by-CI problem at its source.

What the red team cannot fix inside `TauCeti/` still counts — a pipeline gap, a rubric that
keeps missing a pattern, a roadmap-level duplication, an upstreaming candidate. Record it
as a finding, status `needs-human`, and it reaches the user through the report.

## Prerequisites

- `gh` authenticated; `uvx` on PATH; `codex` logged in (R4's reviewer).
- **Astra: gpt-6-astra at `max` effort, every call.** Through the `chatgpt-math` MCP tool
  (`/setup-chatgpt`) when this session has it; otherwise through the Codex CLI, which needs
  only a `codex` login: write the question to a file and run `python3 "$RT" astra <file>`.
  Set `REDTEAM_CODEX_HOMES` (e.g. `~/.codex:~/.codex2`) to fall through to another login
  when one hits its usage limit. If neither works, hunt anyway: the findings stay `suspected`, because a win cannot be
  recorded without Astra.
- The `lean-lsp` MCP server.
- **A TauCeti checkout of this agent's own** (rounds switch branches). Fetch both caches,
  `lake exe cache get` (Mathlib) and `bash scripts/lake-cache-get.sh .` (Tau Ceti's own
  oleans; without it `lake build` compiles the library for hours), then `lake build`.
  Several agents need several checkouts.
- The helper, resolved once per round:
  ```bash
  RT="${CLAUDE_PLUGIN_ROOT:-$(ls -d ~/.claude/plugins/cache/*/mathlib-quality/*/ 2>/dev/null | sort -V | tail -1)}/scripts/redteam.py"
  python3 "$RT" --help
  ```
  Run it from the TauCeti checkout. Its ledger is `$REDTEAM_LEDGER`, default
  `~/.tauceti-redteam`. For agents on several machines, make that directory a clone of a
  private git repository; the script then pulls before reading and pushes after writing,
  and each agent writes only its own files, so they never conflict.
- **The PR gate.** On the first round in a checkout, if `.mathlib-quality/pr-session.json`
  is missing, write it (no questions — a red team's chain is fixed):
  ```json
  {"chain_goal": "red-team fixes: findings from /redteam", "roadmap_area": "refactor of existing code (any area)",
   "source": "none", "started": "<ISO date>"}
  ```
  That arms `hooks/pr_gate.sh`, so every red-team PR must show `/cleanup` on each changed file.

---

# R0 — The board

```bash
gh pr list --repo TauCetiProject/TauCeti --state open --author @me \
   --json number,headRefName,headRefOid,title,body,updatedAt,labels --limit 100
```

**Ours** = those whose `<!--redteam:v1 {...}-->` block names this agent as `owner`
(`python3 "$RT" whoami`). Each agent tends and counts only its own PRs, so every agent has
its own `--max-open`. The id lives in the checkout (`.mathlib-quality/redteam-owner`): an
agent restarted in the same checkout picks its PRs back up. For each, read the `build` status and
the newest scoreboard exactly as `/taupr` does (`statusCheckRollup` context `build`; the
`<!--tauceti-meta:v1 {...}-->` block of the newest `<!--tauceti-scoreboard-->` comment — a
review binds only to the `head_sha` it names; never trust labels).

Then `python3 "$RT" sync` (marks findings `landed` or `rejected` as their PRs merge or
close) and `python3 "$RT" tally`.

**Parked PRs** are left alone by R1–R4 and not counted against the cap: one labelled
`review-budget-spent`, or whose findings are all `refuted` or `needs-human`. Name each in
the report so the user can close it.

**A rejected finding is a loss until shown otherwise.** For each finding `sync` marked
`rejected`, read why its PR closed. If another change fixed the problem, re-mark it
`superseded` (still a win); if review showed the claim wrong, leave it `rejected` and
record the reason.

# R1–R4 — Tend our PRs

These are `/taupr`'s steps, applied to red-team PRs. Before touching a PR's branch, claim
it: `python3 "$RT" claim acquire branch/<pr>` (exit 1 means another agent has it: move on).
Release it when done.

- **R1 REBASE** — a genuine conflict under `TauCeti/`: rebase on `origin/main`, rebuild,
  re-run the finding's evidence probe (the problem must still exist), push.
- **R2 FIX-CI** — reproduce with `lake build`, fix, push. The CI rules: no `sorry`, no
  axioms beyond `propext`/`Classical.choice`/`Quot.sound`, Mathlib's linters, no
  `maxHeartbeats`.
- **R3 FIX** — read every rubric thread and every human comment. Implement each finding,
  or contest a genuine contradiction with a reply in that rubric's thread
  (`POST /repos/TauCetiProject/TauCeti/pulls/<PR>/comments/<ROOT_ID>/replies`; strip any
  `tauceti-reply:` / `tauceti-rubric:` markers from quoted text), then run R4's command on
  it, since a contest does not re-trigger CI. A maintainer's comment outranks a rubric.
  **When review attacks the red team's premise** (the "wrong" definition is a deliberate
  convention, the "duplicate" differs), re-examine it the way you confirmed it: Lean, then
  Astra. If the premise falls, record the finding `refuted` with the reviewer's reason — a
  loss, honestly taken — and park the PR. Never quietly reshape a PR into something else.
- **R4 REVIEW** — `build` success at the head, no scoreboard for that head, and ≥ 1h since
  the `build` status:
  `uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR> --reviewer codex --post`.

Every push is `git push --force-with-lease=<branch>:<observed_oid> https://github.com/TauCetiProject/TauCeti HEAD:<branch>`.
A `[rejected] (stale info)` means someone moved it: re-observe, never plain-push.

# R5 — Ship a confirmed finding

Only when fewer than `--max-open` of this agent's PRs are open (parked ones excluded).

1. **Pick.** `python3 "$RT" tally` lists the queue worst first, each with its topic. Take
   the first, then gather the rest of its topic (below).
2. **Claim its file**: `python3 "$RT" claim acquire <file>`. Held → take the next finding.
3. **Re-check on today's `main`.** `git fetch origin`, then re-run the evidence probe. If
   the problem is gone, record the finding `superseded` (resolution: the commit that fixed
   it) and pick again — that does not end the round.
4. **Branch**: `git switch -c redteam/<finding-id, lower case> origin/main`.
5. **Fix it** by the playbook in the reference (delete and repoint, restate and re-prove,
   generalise, decompose, rename, relocate). **No backwards compatibility**: a deleted or
   renamed declaration has every use in the repository updated and leaves no alias,
   `@[deprecated]` wrapper or forwarding module behind — `api-design` rejects all of them.
6. **Repair everything downstream.** Find each use (`lean_references`, and
   `git grep -wn <name> -- TauCeti`), fix it, and build every changed module and every module
   that mentions a changed name. A downstream proof that breaks because a wrong definition
   was corrected is expected: it was leaning on the error. Repair it.
7. **Clean up**: `Skill(mathlib-quality:cleanup)` on every changed `.lean` file (the gate
   checks), and `Skill(mathlib-quality:decompose-proof)` for any proof you touched that is
   over 30 lines.
8. **PR** — shape below; write the pre-PR receipt; create the branch with
   `--force-with-lease=<branch>:` (empty expected value); `gh pr create`.
9. **Record** every finding the PR resolves — including each finding on a declaration it
   deletes, so no later round ships a fix to something already gone:
   `python3 "$RT" finding '{"id":"<id>","status":"pr-open","pr":<n>}'`. List them all in the
   body's `redteam:v1` block. Release the file claim. The round ends; CI reviews the PR.

**When the fix is beyond a PR.** If the intended statement or definition cannot be settled
from the source, the roadmap or Astra, or the repair needs a decision about another roadmap's
design, record the finding `needs-human` with a written plan and pick again.

### One topic per PR

Tau Ceti's `scope` rubric blocks a PR that is more than one topic, and one rejected half
sinks the other. So:

| Findings | PR |
|---|---|
| a CRITICAL finding | alone, with its downstream repairs |
| MAJOR or MINOR, one file, one category | together (e.g. every Mathlib duplicate in one file) |
| NIT and hygiene in one file | one `chore` PR, together with `/cleanup`'s changes to that file |
| one pattern across many files (≤ 15) | together, titled by the pattern |
| several findings one inseparable change fixes (a deletion, a replacement) | together, whatever their categories |

Never mix categories to save a review cycle; only an inseparable change joins them.

### The PR

```text
<type>(<scope>): <what the fix does>          type: fix for CRITICAL, refactor or chore otherwise

Roadmap: <canonical roadmap directory of the code, or none>
<!--redteam:v1 {"owner":"<whoami>","findings":["<id>",...],"patterns":["<slug>",...],"severity":"<worst>"}-->

## What was wrong
<per finding: the declaration, the claim, and why it matters downstream>

## Evidence
<the probe, verbatim, and what Lean said>
<Astra's verdict, one paragraph>

## The fix
<what changed; every declaration deleted or renamed, and where its uses went>

🤖 Generated with [Claude Code](https://claude.com/claude-code)
```

No `tauceti-target` marker: a red-team fix advances no roadmap target (`/taupr` 5d explains
why a fabricated one is harmful). Keep the body true to the diff after every push.

### The pre-PR receipt

`.mathlib-quality/review-receipt.json`, as `/taupr` writes it: `head_sha`, `base_ref`,
`cleanup[]` covering every changed `.lean` file with `/cleanup`'s phase checklist,
`"source_sweep": []` (the session names no source), and a fresh `duplication_check`
listing the open PRs examined — including any other open PR touching the same file, which
must be named in the body.

# R6 — Hunt a file

Only when fewer than `--max-queue` topics of confirmed findings await a PR.

1. **Pick and claim.** Audit `main`, not the branch the last round left checked out:
   `git fetch origin && git switch --detach origin/main`. `python3 "$RT" next` ranks the
   files (flagged by a pattern sweep first, then never audited, most definitions and
   importers first; files in open PRs and files other agents hold are skipped). Claim the
   first you can: `python3 "$RT" claim acquire <file>`. Renew it (`claim renew <file>`)
   every 15 minutes; the lease lasts 25. Build its module (`lake build <Module>`) so the
   language server sees it.
2. **Read it all**, then `lean_file_outline` for the declaration list. State in prose what
   the file claims to do — `/unformalise <file> --md --statement-only` helps — and set the
   module docstring, each docstring and each name beside the statement it describes.
3. **Start Astra's blind pass** (template A1) in a background `Agent`, so it works while
   you do. It sees the file and nothing of your view.
4. **Audit every declaration in every category** — `correctness`, `generality`, `reuse`,
   `proof`, `naming`, `api`, `docs`, `hygiene` — with the checklist in the reference. A cell
   is `"ok"` only when you ran that category's checks on that declaration; otherwise it
   cites a finding. For a file of more than 40 declarations, give batches of about 10 to
   subagents with the checklist, and merge their verdicts.
5. **Merge Astra's list.** Each point it raises is a suspected finding you confirm or refute
   in Lean. Astra finding something you missed is not a loss; failing to check it would be.
6. **Confirm.** Build the evidence for every finding by its recipe. For every CRITICAL and
   MAJOR, ask Astra to refute it (template A2; batch them into one call) and record its
   verdict. **Lean decides facts; Astra is a second opinion on whether the fact is the
   problem you say.** If Astra disagrees and you keep the finding, write the resolution.
7. **Sweep the pattern.** For each confirmed CRITICAL or MAJOR, grep the library for the same
   shape and record each hit as `suspected` in its own file — those files are hunted next.
8. **Record** with the script: each finding (`python3 "$RT" finding @f.json`), then the audit
   with the full matrix (`python3 "$RT" audit @audit.json`). **The script refuses a win
   without compiled evidence and an Astra verdict, and an audit with any declaration or
   category missing.** A refusal means a step was skipped: do it.
9. **Release the claim.**

## Severity, wins and losses

| Severity | What | Win |
|---|---|---|
| **CRITICAL** | The library says something it does not mean: a wrong definition; a theorem that is vacuous, tautological, unrelated to its name or docstring, or weaker than they claim; content moved into hypotheses; a placeholder; a junk value making a statement hold for the wrong reason; anything built on one of these | yes |
| **MAJOR** | An existing declaration (Mathlib, or Tau Ceti in any roadmap) directly replaces it; a second construction of an object another roadmap already has; assumptions that exclude cases the name or docstring covers, or that ≥ 3 consumers must carry needlessly; a name that overstates the statement; a compatibility shim; free data that defeats `@[ext]`; a proof over 50 lines; over 10 s to elaborate | yes |
| **MINOR** | Reprovable in a line from existing API; a redundant hypothesis or too-strong typeclass; a proof of 30–50 lines, a brittle rewrite chain, undocumented `change`/`show`, defeq abuse; a name that describes the proof, repeats its namespace or sits in the wrong namespace for dot notation; general material hidden as `private` or in the wrong file; missing characteristic API or `@[simp]`; over 1 s; a stale or missing docstring | no |
| **NIT** | Commented-out code, leftovers (`#check`, `set_option trace`), unused imports or variables, header or module-doc omissions | no |

**Wins** are confirmed CRITICAL and MAJOR findings (`confirmed`, `pr-open`, `landed`, or
`superseded`). **Losses** are findings `refuted` (Lean, Astra or review overturned them) or
`rejected` (their PR closed for being wrong). The score line shows both.

| Thought | Reality |
|---|---|
| "Both fixes are tiny; one PR saves a review cycle" | One topic per PR. `scope` blocks bundles, and one rejected half sinks the other. |
| "The pipeline is moving; one more PR is fine" | The cap is the cap. At the cap, hunt. |
| "Deprecate the old name — that's Mathlib's convention" | Tau Ceti forbids compatibility shims. Delete it and repoint every use. |
| "It's minor; not worth recording" | Everything is recorded. Nits ship in the file's `chore` PR. |
| "Astra agrees, so it's confirmed" | Lean confirms. Astra is the second opinion. |
| "Lean says so; no need to ask Astra" | A win needs both: Lean for the fact, Astra on whether the fact is the problem. |
| "Probably intended API — a specialisation" | Show a consumer (`lean_references`). No consumer, no exemption. |
| "`ok`, it looks fine" | `ok` means you ran that category's checks on that declaration. |
| "This proof is long, decompose it" | Search first. A one-line Mathlib proof replaces it; decomposing it keeps the waste. |
| "This needs an issue, a roadmap change or a rubric PR" | Out of bounds. Record it `needs-human`; the report carries it to the user. |

## Running it continuously

`/redteam` runs one round and stops. Recurrence belongs to the harness:

```
/loop 10m /redteam        a round every ten minutes while the session lives
```

For an unattended schedule, use the `schedule` skill to create a cron running `/redteam`.
Several agents can run at once — each in its own checkout, sharing the ledger; claims keep
them off each other's files, and each tends only the PRs carrying its own id, with its own
`--max-open`.

Between rounds, one line:

```
**Round <n>: <STEP> <on #PR | file>** — <what changed>. Score: <wins> wins (<c> critical), <l> landed, <x> losses. Open: <k>/<max-open>; queued <t> topics (<q> findings).
```

## Report

`/redteam report` reads the ledger (`python3 "$RT" tally --json`, plus the findings files)
and writes `$REDTEAM_LEDGER/REPORT.md`:

1. **The score** — wins, critical wins, landed, losses, files audited.
2. **Common errors** — one section per pattern, most frequent first: what the error is, how
   many times, its severities, three examples with PR links, the check that catches it, and
   **the rubric that missed it**.
3. **Rubric proposals** — per TauCetiReview rubric, the text you would add, justified by the
   patterns and counts above; and mechanical checks CI could run instead (a grep, a linter,
   a `False`-from-hypotheses probe).
4. **Checklist additions** — patterns seen three or more times that the reference's
   checklist does not name.
5. **Needs a human** — every `needs-human` finding and parked PR.

It proposes; it sends nothing. Tell the user where the report is. If the ledger is a git
clone, commit and push it.

## Reference

- `references/tauceti-redteam.md` — checklist per category, evidence recipes, Astra prompts,
  the fix playbook, the ledger's records
- `references/tauceti.md` — review mechanics, claims, `--force-with-lease`, merge policy
- `commands/taupr.md` — the worker loop R1–R4 come from
- `scripts/redteam.py` — queue, claims, ledger, score (`--help`)
- Upstream: TauCeti `AGENTS.md`, `COORDINATION.md`; TauCetiReview `rubrics/`
