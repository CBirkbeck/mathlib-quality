---
name: fix-pr-feedback
description: Fetch PR reviewer comments, implement fixes locally, gate the push behind explicit user approval, then watch CI to completion
---

# /fix-pr-feedback — Address PR Reviewer Comments

Pull every reviewer comment on a mathlib PR, implement the fixes locally, **stop and wait
for user approval before pushing**, then push and watch CI to completion.

The non-negotiable rules:
- **Never push before the user has reviewed and approved the changes.** No exceptions.
- **Every comment must be accounted for** — addressed, deferred with a reason, or marked
  unable-to-address with a reason. Silent skipping is a defect.
- **After pushing, the skill must wait for CI** — it's not done until checks finish.
- **Every commit and any PR description update follows the conventions in
  "PR description, commit messages, dependencies" below** — short, concrete,
  dependencies stated, Claude co-author footer.

## Usage

```
/fix-pr-feedback <PR_number>
/fix-pr-feedback <PR_url>
/fix-pr-feedback                  # If currently on a branch with an open PR, auto-detect
```

If only inline review comments are visible without a PR number, you can also paste them:

```
/fix-pr-feedback --comments "<pasted comments>"
```

But the workflow assumes a real PR (the CI-watching phase needs one).

---

## PR description, commit messages, dependencies

Every commit this skill creates and every PR description update it performs
follows these conventions. They apply equally to the initial fix commits in
Phase 3 and to any re-push fixes in Phase 7.

### PR description

Default behaviour: do **not** touch the PR description. The user wrote it; the
fixes are responses, not a re-statement of the PR. Update the description
only when one of the following is true:

- The fix changes the scope of the PR (new files, removed features, a
  different conclusion)
- The fix introduces or resolves a dependency on another PR
- A reviewer explicitly asked for the description to be updated
- You are creating a new follow-up PR for deferred items

When you do update it, follow these rules:

- **Short.** A one-line summary, then 1–5 bullets naming the substantive
  changes. No background paragraphs. No "this PR addresses the following
  comments" walls of text — comments are visible in the PR thread; don't
  duplicate them.
- **Concrete.** Each bullet names *what changed*, not *why* in the abstract.
  "Renames `wt_eq_zero` → `weight_eq_zero`" not "Improves naming consistency".
- **Lists dependencies.** If the PR depends on another PR being merged first
  (a mathlib bump, a sister-project PR, an upstream contribution), state
  them on a dedicated line:

  ```
  Depends on #1234 (mathlib bump to v4.30.0), #5678 (FooBar API)
  ```

  If there are no dependencies, omit the line entirely — don't write
  "Depends on: none".

- **Co-author footer.** Always include, on its own line at the bottom:

  ```
  Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
  ```

Use `gh pr edit <PR> --body "$(cat <<'EOF' … EOF)"` with a HEREDOC so the
body renders with proper line breaks.

### Commit messages

Every commit this skill creates follows the same shape:

- Subject line ≤ 72 characters, imperative mood ("address PR feedback",
  not "Addressing" or "addressed"). When fixing CI in Phase 7, name the
  fix concretely: "fix style-linter on Foo.lean" rather than "fix CI".
- Body (optional, separated from subject by a blank line): short bullets
  naming the substantive changes. Same concreteness rule as the PR
  description.
- Co-author footer on its own line at the bottom:

  ```
  Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
  ```

Use the HEREDOC pattern (per project convention) so newlines render:

```bash
git commit -m "$(cat <<'EOF'
address PR feedback

- rename wt_eq_zero → weight_eq_zero (reviewer1)
- inline single-use have h := bar in Foo.lean:60 (reviewer2)
- add docstring to weightedSum (reviewer2)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Dependencies (binding)

If the fix needs another PR merged first, surface the dependency in three
places:

1. **PR description**'s `Depends on:` line (per above) — visible to
   reviewers at a glance.
2. **Phase 5 approval report** — explicit row flagging the dependency
   to the user so they can verify the prerequisite landed before
   approving the push.
3. **Commit message body** if the dependency is what motivated a
   specific change ("rewrite uses Foo.bar from upstream PR #1234").

Do not push fixes whose dependencies are unmerged — CI will fail.

---

## Phases

```
PHASE 1  FETCH                 pull every comment + PR description
PHASE 2  TRIAGE                build numbered punch-list, classify, prioritise
PHASE 3  IMPLEMENT             fix each item, track addressed / deferred / unable
PHASE 4  COVERAGE              re-fetch comments, verify nothing slipped through
PHASE 5  STOP — USER APPROVAL  print full report, do NOT push, wait for explicit OK
PHASE 6  PUSH + WATCH CI       once approved, push; watch checks to completion
PHASE 7  CI FOLLOW-UP          if CI fails, fix → return to Phase 5
PHASE 8  REPORT + LEARNINGS    final summary, write learnings
```

---

## PHASE 1 — Fetch (Main agent)

### 1a. Resolve the PR

Determine the repo and PR number:

- If the user supplied a number with no repo, default to `leanprover-community/mathlib4`.
- If a URL: extract `<owner>/<repo>` and number.
- If neither: `gh pr view --json number,headRepository,baseRepository,url` from the current
  branch.

Print the resolved PR (number, title, URL) so the user can confirm the right one.

### 1b. Pull comments

Mathlib PRs accumulate three kinds of feedback:

| Kind | What it is | gh API |
|---|---|---|
| **Review comments** | Inline comments tied to a file + line | `gh api repos/<owner>/<repo>/pulls/<N>/comments --paginate` |
| **Issue comments** | Top-level PR comments (no line attachment) | `gh api repos/<owner>/<repo>/issues/<N>/comments --paginate` |
| **Reviews** | Approve/Request-changes summary bodies | `gh api repos/<owner>/<repo>/pulls/<N>/reviews --paginate` |

Pull all three. Store the raw JSON in scratch so you can re-fetch later for the coverage
check. Capture for each comment:

- `id` (stable identifier — used in Phase 4 to verify coverage)
- `user.login` (author)
- `body` (comment text)
- `path` + `line` + `original_line` (review comments only)
- `commit_id` (review comments only — flags if the comment is on an outdated commit)
- `in_reply_to_id` (threading)
- `created_at`

### 1c. Pull PR description and diff

```bash
gh pr view <PR> --json title,body,files,headRefName,baseRefName,commits
gh pr diff <PR>
```

The PR description sometimes contains a checklist or "things to fix" the reviewer points
back to. Read it.

### 1d. Filter

- **Bot comments**: drop comments from `github-actions[bot]`, `mathlib4-bot`, etc., unless
  the user specifies they're meaningful.
- **Resolved threads**: review comments have a `position: null` field if the thread is
  outdated/resolved on the current commit. Don't drop these silently — flag them in the
  punch-list as "thread was on outdated code; check whether the underlying issue still
  applies".
- **Threading**: when a comment has `in_reply_to_id`, group it under the parent.

---

## PHASE 2 — Triage (Main agent)

Build a single numbered punch-list. Print it before doing any edits. Format:

```
## PR Feedback Punch-List for <owner>/<repo>#<N>

Total comments fetched: 23
After dropping bots: 18
After threading (top-level comments): 14

| # | Author | Where | Severity | Category | Comment summary |
|---|--------|-------|----------|----------|-----------------|
| 1 | @reviewer1 | Foo.lean:45 | 🔴 must-fix | golf | "This can be `simpa using h`" |
| 2 | @reviewer2 | Bar.lean:78 | 🔴 must-fix | naming | "Rename `wt_eq_zero` → `weight_eq_zero`" |
| 3 | @reviewer1 | Foo.lean:120 | 🟡 should-fix | api-design | "Should this be an instance?" |
| 4 | @reviewer2 | (PR body) | 🟢 question | clarification | "Why prove this here vs in core mathlib?" |
| ... |
```

### Severity scale

| Mark | Meaning | Default action |
|---|---|---|
| 🔴 must-fix | Reviewer used "please change", "should be", "must"; or it's a correctness/CI-blocking issue | Implement |
| 🟡 should-fix | Suggestion phrased as recommendation; convention/style | Implement; document if you don't |
| 🟢 question | Reviewer asks a question rather than requesting a change | Answer in writeup; only fix if answer implies a change |
| ⚪ resolved | Thread was on outdated code or already resolved | Verify still resolved |

### Categories (pick one each)

`golf`, `style`, `naming`, `documentation`, `api-design`, `correctness`, `import`, `decomposition`, `mathlib-discovery`, `clarification`, `other`.

### Prioritisation

Order the implementation pass:
1. Correctness 🔴 (could be wrong code)
2. API/structural changes 🔴 (touch other items, do these first to avoid rework)
3. Naming 🔴 (cascades through call sites)
4. Golf / style 🔴/🟡
5. Documentation 🔴/🟡
6. Questions 🟢 (no code change, but draft an answer)

Print the prioritised order before Phase 3 starts.

#### API-extraction comments belong in bucket 2, not bucket 4

Comments of the form *"this should be an API lemma"*, *"looks like more API lemmas
for X"*, *"can you extract a lemma for the underlying object?"* — these are
**API/structural** items, not golf. Promote them to bucket 2 even if the reviewer
phrased them as "consider …" or attached them to a single one-line proof.

Two reasons:

1. **They cascade.** A new API lemma named for the underlying object (not the
   one-shot target) usually shortens 2–6 other proofs in the same file once
   extracted. Doing it after the golf pass means re-touching the same proofs twice.
2. **The reviewer is making a teaching point, not a cosmetic one.** Reviewers
   on mathlib PRs flag this pattern explicitly — the request is about the
   *shape* of the contribution, not the specific characters in the affected
   proof.

Before applying the fix, **grep all call sites of the underlying object** in the
file (and adjacent files in the same area) so the new API is named for the broader
use case, not just the one-shot context the reviewer happened to point at. See
`references/proof-patterns.md § Extract API Before Bulling Through Ugly Proofs`
for the full set of signals and a worked before/after.

---

## PHASE 3 — Implement (Main agent + workers)

For each item in the prioritised order:

### 3a. Understand exactly what's being asked

If the comment quotes code (most review comments do), make sure you're looking at the same
code in the file *now* — the line numbers in `original_line` may have drifted. Use the
quoted text + filename + nearby identifiers, not just the line number.

### 3b. Apply the fix

For golf/style/naming: small focused edits inline. For multi-line proof restructures or
proofs you're rewriting: dispatch a worker the same way `/cleanup` Phase 4 does (one
declaration at a time, full audit + golf rules from `golfing-rules.md`).

For naming changes: `Grep` for the old name across the whole repo and update **every** call
site. A reviewer-requested rename that misses a call site is a defect.

For "consider X" suggestions where you decide *not* to do it: that's allowed, but you must
write a reason in the report so the user can confirm in Phase 5.

### 3c. Verify each fix

After every edit, run `lean_diagnostic_messages` on the affected file. If the change broke
the build, fix it before moving to the next item — don't accumulate breakage.

### 3d. Record in the running log

Maintain a per-item record:

```
Item #1 (Foo.lean:45, "This can be `simpa using h`")
  Status:    ✓ addressed
  Action:    Replaced `simp [foo]; exact h` with `simpa [foo] using h`
  Verified:  lean_diagnostic_messages clean
  Diff:      L45-46

Item #2 (Bar.lean:78, "Rename wt_eq_zero → weight_eq_zero")
  Status:    ✓ addressed
  Action:    Renamed declaration; updated 7 call sites in 4 files
  Verified:  lean_diagnostic_messages clean on all 4 files; lake build [target] succeeded

Item #3 (Foo.lean:120, "Should this be an instance?")
  Status:    ⚠ unable-to-decide
  Action:    Drafted a reply asking the reviewer; no code change yet
  Reason:    Both options have trade-offs; want reviewer's preference
```

---

## PHASE 4 — Coverage Check (Main agent)

**This phase exists to catch the "I forgot one" failure.**

### 4a. Re-fetch comments

Run the same `gh api` calls as Phase 1b to get the comment list *now*. (Reviewers may have
added more between Phase 1 and now; also, this is the canonical list against which we check
coverage.)

### 4b. Cross-reference by `id`

For each comment `id` from the re-fetch, find the matching entry in your Phase-3 running
log. Build the verification table:

```
| Comment ID    | Phase-3 status      |
|---------------|---------------------|
| 12345678      | ✓ addressed         |
| 12345679      | ✓ addressed         |
| 12345680      | ⚠ unable-to-decide  |
| 12345681      | ❌ NOT IN LOG — investigate |
```

Any `❌ NOT IN LOG` entries mean Phase 3 missed the comment. Go back, address them, then
re-do Phase 4. Do not move on with unaddressed comments.

### 4c. Verify the build

```bash
lake build [target_modules]   # for the changed files
```

If the project has a `lake exe runLinter`, run it too. Resolve every error before Phase 5.

### 4d. Commit the changes locally (per conventions)

With every Phase-3 fix verified and the build clean, stage and commit the
changes locally — do NOT push yet (the push is gated by Phase 5 approval).

The commit message follows "PR description, commit messages, dependencies":
imperative subject ≤ 72 chars, optional bullet body naming the substantive
changes, Claude co-author footer on its own line.

```bash
git add <each changed file by name>
git commit -m "$(cat <<'EOF'
address PR feedback

- <bullet per substantive change, naming the file or rename or reformulation>
- <…>

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

If a reviewer asked for separate commits per concern (see the multi-commit
edge case below), repeat the above per group rather than one bundled commit.

After committing, `git status` should be clean. Phase 5 prints the commit
list as part of the approval report.

---

## PHASE 5 — STOP. Wait for user approval. (Main agent)

**Do not push. Do not run `git push`. Do not commit-and-push. Do not "while we're here".**

Print the full report (template below) and stop. Wait for the user to read it and either:

- **Approve** ("ok push", "looks good", "go ahead") → proceed to Phase 6.
- **Request changes** ("change item 3 to do X instead", "add a reply on item 4") → make the
  change, re-run Phase 4 coverage, return to this Phase 5 and wait again.
- **Cancel** ("don't push", "stop") → end here. The local commits stay; user can decide
  what to do with them.

### Phase 5 report template

```
## PR Feedback — Local Changes Ready (NOT YET PUSHED)

PR: <owner>/<repo>#<N> — <title>
Branch: <branch_name>
Base: <base_branch>

### Coverage
| Total comments | 18 |
| Addressed       | 15 |
| Deferred (with reason) | 2 |
| Unable to address (with reason) | 1 |
| Unaddressed (DEFECT — should be 0) | 0 |

### Changes summary

#### Correctness (1)
1. ✓ Bar.lean:120 — Fixed off-by-one in induction step (reviewer was right;
   the `n + 1` case used `n` instead of `n + 1` in the IH application)

#### Naming (1)
2. ✓ Renamed `wt_eq_zero` → `weight_eq_zero` (Foo.lean:78); updated 7 call sites
   in 4 files (list…)

#### Golf (8)
3. ✓ Foo.lean:45 — `simp; exact h` → `simpa using h`
4. ✓ Foo.lean:60 — Inlined single-use `have h := bar`
   ... etc

#### Style (3) ...
#### Documentation (2) ...

### Deferred (2)
- Item #3 (Foo.lean:120, "Should this be an instance?") — drafted reply asking
  for preference; no code change. Reasoning: the trade-off depends on
  downstream usage we don't have visibility into.
- Item #14 (Bar.lean:200, "Could you also handle the `Int` case?") — out of
  scope for this PR; suggested a follow-up issue.

### Unable to address (1)
- Item #18 (general comment, "The whole approach feels off") — not an
  actionable change request; need clarification before any code change.

### Drafted replies (for the user to send after pushing)
- Item #3: "Both work; the trade-off is X vs Y. Do you have a preference?"
- Item #14: "I'd like to handle that in a follow-up — opened #YYYY."
- Item #18: "Could you say more? Specifically, X feels off because Z, but
  if you mean Y, then …"

### Local git state
- New commits: 1 ("address PR feedback")
- Files changed: 6 (list…)
- Lines: +23 −41
- Commit footer: Co-Authored-By: Claude Opus 4.7 (1M context) ✓

### Dependencies (other PRs that must merge first)
<If none: omit this section. If any:>
- ⚠ Depends on <owner>/<repo>#<N> (<one-line: what it provides>). Status:
  <merged / open / draft>. **Pushing before this lands will fail CI.**
- ⚠ ...

### PR description update
<One of:>
- ✗ No update needed (scope unchanged, no new dependencies, reviewer didn't ask).
- ✓ Updated. Diff of the description: <show the before/after, or "appended Depends on line and updated bullet 2">.

### Next step
**Awaiting your approval to push.** Reply with "push", "ok", or
"approved" to proceed; or describe further changes you want first.
```

Then **stop** and wait. Do not pre-emptively push.

---

## PHASE 6 — Push + Watch CI (Main agent, only after user approval)

### 6a. Pre-push check: PR description

Before pushing, decide whether the PR description needs updating per the
rules in "PR description, commit messages, dependencies" above. The four
triggers:

- Fix changed the scope of the PR (new files, removed features, different conclusion)?
- Fix introduced or resolved a dependency on another PR?
- A reviewer explicitly asked for the description to be updated?
- You are about to push to a new follow-up PR for deferred items?

If yes, update via:

```bash
gh pr edit <PR> --body "$(cat <<'EOF'
<one-line summary>

- <bullet 1>
- <bullet 2>
- ...

Depends on #<N> (<what>), #<M> (<what>)   <only if applicable>

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

Verify with `gh pr view <PR> --json body` that the update landed.

If no update needed, leave the description alone.

### 6b. Push

```bash
git push
```

If the branch tracks a remote, this is enough. If not, the user has to set the upstream
themselves — print the suggested `git push --set-upstream …` command and stop.

Verify the push landed:
```bash
gh pr view <PR> --json headRefOid
```

The `headRefOid` should match `git rev-parse HEAD`.

### 6c. Wait for CI to start, then watch to completion

CI runs are not instant — there's usually a 10–60 second delay between push and the first
check appearing. Wait briefly, then start watching:

```bash
sleep 15
gh pr checks <PR> --watch --interval 30
```

Run this with `Bash` `run_in_background: true`. The runtime auto-notifies you when the
process exits — that's our wake-timer. Do **not** use a polling sleep loop in foreground —
that wastes context and can hit timeouts. Do **not** use `ScheduleWakeup` (that's for
`/loop` mode only).

Tell the user what's happening:

```
Pushed to origin/<branch>. Watching CI on <owner>/<repo>#<N>.
This typically takes 10–40 minutes for mathlib. I'll come back when checks finish.
```

Then continue with other work or wait. When `gh pr checks --watch` exits, you'll be
notified.

### 6d. Read the result

When the watch process completes, capture its status:

```bash
gh pr checks <PR>           # final state
gh pr view <PR> --json statusCheckRollup
```

Three outcomes:

| State | What it means | Next step |
|---|---|---|
| `SUCCESS` (all green) | CI passed | Phase 8 report |
| `FAILURE` (any check failed) | CI flagged something | Phase 7 |
| `PENDING` (still running) | The watch ended early; re-watch | Loop back to 6c |

---

## PHASE 7 — CI Follow-up (Main agent, only if CI failed)

### 7a. Diagnose

For each failed check:

```bash
gh run list --branch <branch> --limit 5
gh run view <run_id> --log-failed
```

Read the failure log. Common categories on mathlib PRs:

- **Build failure**: a file doesn't compile. The log shows the specific Lean error.
- **Style linter failure**: a `style.*` linter fired on the diff.
- **Mathlib4-style linter**: `lake exe runLinter` errors (unused, simpNF, etc.).
- **Bench / nolints / other CI scripts**: project-specific checks (e.g., `!bench`).
- **Imports** failure: `lake exe shake` flagged an unneeded or missing import.

### 7b. Fix

Apply the fix. For build failures, this often reveals that one of the Phase-3 changes
introduced a regression — the diagnostic now leads you to the exact line.

After fixing locally, run:

```bash
lake build <affected_modules>
lake exe runLinter <affected_modules>   # if the CI failure was a linter
```

### 7c. Commit the fix (per conventions)

Commit the CI fix locally before going back to Phase 5. Follow the same
commit conventions as Phase 4d: imperative subject naming the fix
concretely ("fix style-linter on Foo.lean", not "fix CI"), optional bullet
body, Claude co-author footer.

```bash
git commit -m "$(cat <<'EOF'
fix <concrete CI failure>

- <what was fixed and where>

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### 7d. Loop back to Phase 5

Print a short follow-up report ("CI failed on X; here's the fix; awaiting approval to push
again") and wait for user approval again. Do not push without approval, even if the fix
looks obvious.

---

## PHASE 8 — Final Report + Learnings (Main agent)

Once CI is green:

```
## PR Feedback Resolution — <owner>/<repo>#<N> — DONE

### Comments
- Total addressed: 15
- Deferred: 2 (with replies drafted)
- Unable: 1 (clarification needed)

### Code changes (final)
- Files changed: 6
- Lines: +23 −41
- Commits: 1 ("address PR feedback")

### CI
- Final status: ✓ SUCCESS
- Runs: 1 push + 0 fixes (or N pushes if Phase 7 fired)
- Total wait time: ~22 minutes

### Replies drafted (paste these into PR comments)
- Item #3: "..."
- Item #14: "..."
- Item #18: "..."

### Reviewer is now unblocked.
```

Then write learnings to `.mathlib-quality/learnings.jsonl` per the schema below.

---

## Edge cases

### "I want to push myself, just do the fixes"

If the user says they'll handle the push, stop after Phase 5. Don't run Phase 6 or 7. The
fixes-only mode is fine; the no-push mandate is the default.

### Multiple commits requested

If the reviewer wants distinct concerns in separate commits ("please split this PR"):
group the Phase-3 fixes by reviewer-asked grouping, then make one commit per group
in Phase 4d rather than one bundled commit. Every commit still follows the
conventions in "PR description, commit messages, dependencies" — short
imperative subject, bullet body, Claude co-author footer. Commit subjects
should reference the comment(s) addressed, e.g. `address naming feedback
(reviewer1)`.

### CI is intermittently flaky

If a check fails on something obviously unrelated (mathlib master broke, network glitch),
don't loop back to Phase 7 with a code fix. Re-trigger the run:

```bash
gh run rerun <run_id>          # rerun the specific run
# or
gh pr comment <PR> --body "/bench"   # if a project bot accepts trigger commands
```

Then watch again. Treat persistent flakes as the user's call.

### Reviewer dismissed or resolved a thread mid-flow

If between Phase 1 and Phase 4 the reviewer resolved threads, don't worry — Phase 4
re-fetches comments and the resolved-but-still-relevant ones stay in the punch-list
(`⚪ resolved`). New comments added between Phase 1 and Phase 4 also get caught by 4b.

---

## Reference

- `skills/mathlib-quality/references/pr-feedback-examples.md` — common feedback patterns
- `skills/mathlib-quality/references/golfing-rules.md` — used by Phase 3 workers when a comment requests proof golf
- `commands/cleanup.md` — Phase 4 worker prompt (used here when proofs need a deep golf pass)

---

## Final Step: Record Learnings

After completing the resolution, capture what was learned.

For each significant fix made, write a JSON entry to `.mathlib-quality/learnings.jsonl`:

```json
{
  "id": "<short unique id>",
  "timestamp": "<ISO timestamp>",
  "command": "fix-pr-feedback",
  "type": "<golf_pattern|style_correction|naming_fix|mathlib_discovery|api_change|failed_pattern>",
  "before_code": "<original code, max 500 chars>",
  "after_code": "<fixed code, max 500 chars>",
  "pattern_tags": ["<relevant pattern names>"],
  "description": "<what the reviewer asked for and how it was resolved>",
  "math_area": "<analysis|algebra|...|other>",
  "accepted": true,
  "source": "agent_suggestion",
  "context": {
    "file_path": "<relative path>",
    "theorem_name": "<if applicable>",
    "pr": "<owner>/<repo>#<N>",
    "reviewer": "<gh login>"
  }
}
```

**What to capture:**
- Each reviewer-requested change — what reviewers catch is what `/cleanup` should catch earlier.
- Patterns the skill should have flagged in `/cleanup`'s Phase 2 (style audit) or Phase 4 (per-declaration golf) but didn't.
- Novel reviewer insights not yet in the reference docs.
- Fixes the user disagreed with or modified during Phase 5 review.

**What NOT to capture:**
- Trivial formatting fixes already in the style guide.
- CI-flake reruns.

**Keep it lightweight** — only 1–5 entries per command run, prioritising novel reviewer insights.
