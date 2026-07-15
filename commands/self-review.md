---
name: self-review
description: Run N rounds of neutral, independent review-and-implement on your changes before a PR. Each round spawns a FRESH, unbiased review agent (techniques from the built-in /review and from /check-style, specialised to four Lean dimensions — definition necessity, generalisation, automation, mathlib naming/style), reports its findings to you, implements every suggestion, and reports back — then relaunches until N rounds are done. Defaults to 3 rounds. The reviewer never rubber-stamps, even on the last round.
---

# /self-review — Independent, Multi-Round Self-Review Before PR

Review your own changes the way a good external reviewer would — by **not** being the
instance that wrote them. `/self-review` spawns a **fresh, neutral review agent** each
round, reports its findings to you, implements every suggestion it makes, reports what
changed, and relaunches for the next round. It runs a **fixed number of rounds** (default
**3**) and stops there, even if the code still isn't perfect.

The whole point is *structural* objectivity. The instance that wrote a proof is the worst
judge of whether it is well-named, well-generalised, or best closed by automation — it is
anchored on the choices it already made. So the reviewer is a **separate agent, spawned
fresh every round**, with no access to the author's rationalisations and no stake in the
existing code. The driving instance (you) is the **implementer**, not the reviewer, and
implements what the independent reviewer asks.

## Non-negotiable rules

- **The reviewer is a fresh, independent agent every round.** A new `Agent` dispatch per
  round — *not* `SendMessage` continuity — so no round is anchored on the previous one and
  no reviewer has an ego stake in comments it made last time. Never let the implementer
  grade its own homework.
- **Exactly N rounds.** One round = one review + one implementation. Default N = 3. The loop
  terminates after the **Nth implementation**, even if findings remain. N is a hard cap, not
  "until perfect".
- **The round number never changes the reviewer's standard.** On the final round the
  reviewer reviews exactly as it would on the first. It does **not** declare the code done,
  soften findings, or withhold warranted feedback because the review budget is ending.
  Termination is the loop's decision, never the reviewer's.
- **Implement every suggestion.** The implementer applies *all* of the reviewer's requested
  changes. The only thing it may decline is a change it cannot make without breaking the
  build or introducing an error — and even then it must be **attempted, reverted, and
  documented** for the next round, never silently skipped. Disagreement is not grounds to
  skip: defeating the author's bias is the entire reason the reviewer is separate.
- **Report twice per round.** First report the reviewer's requested changes to the user;
  then, after implementing, report a summary of what changed. Both are mandatory, both in
  chat.
- **Feedback lands on the PR thread when there is one.** If the branch has an open PR, each
  round's findings are posted as a PR comment; otherwise they are reported in chat only.
- **No commits, no pushes.** `/self-review` edits the working tree and (optionally) comments
  on the PR. Committing and pushing stay with you, `/pre-submit`, or `/fix-pr-feedback`.

## Usage

```
/self-review                      # 3 rounds; review the changes on this branch vs its base
/self-review 5                    # 5 rounds
/self-review 5 Foo/Bar.lean       # 5 rounds, scoped to one file
/self-review Foo/Bar.lean         # 3 rounds, scoped to one file
/self-review 3 Foo/Bar.lean thm   # 3 rounds, scoped to a single declaration
/self-review --no-pr              # never post to the PR thread; report in chat only
```

**Parsing.** If the first whitespace-separated token is a positive integer, it is **N**
(the number of rounds); otherwise **N defaults to 3**. Remaining non-flag tokens are the
**scope**. With no scope, the scope is every changed `.lean` file on the current branch
relative to its base branch (PR mode).

## The round model

A "round of review" is one **review** followed by one **implementation**. `/self-review N`
runs N of them back to back:

```
round 1:   REVIEW (report)  →  IMPLEMENT (report)
round 2:   REVIEW (report)  →  IMPLEMENT (report)
   ...
round N:   REVIEW (report)  →  IMPLEMENT (report)
           └── stop here, even if the code is not perfect
```

So `/self-review` (N = 3) produces exactly six reported steps —

```
1. Review   2. Implement   3. Review   4. Implement   5. Review   6. Implement
```

— and `/self-review 5` produces ten. The **Nth review is a genuine review** whose findings
are implemented in the Nth implementation; *then* the loop ends. The reviewer is never told
"this is the last round, wrap up".

## Where the techniques come from

- **`/review`** (the built-in PR-review skill) and **`/code-review`** (the working-diff
  variant): adversarial, verify-before-you-report reviewing; findings ranked by severity;
  a steelman of the author's choice before a finding is allowed to stand.
- **`/check-style`**: absorbed into this plugin as `/cleanup`'s **Phase 2 style audit**. The
  style/naming rules live in `references/style-rules.md`, `references/naming-conventions.md`,
  and the style section of `CLAUDE.md`.
- The four Lean-specific dimensions below are what this command adds on top of those.

---

## PHASE 0 — Resolve (driving instance)

1. **Parse N and the scope** per the usage grammar above. Print them.
2. **Baseline build (doctor).** Run `lake build` on the scope's modules. If the baseline is
   already broken, **stop and report** — the reviewer can't distinguish what the changes
   introduced from what was already red, and the implementer can't verify fixes against a
   broken baseline. (Same doctor gate as `/cleanup` Phase 0.)
3. **Resolve the scope to a concrete file/decl list:**
   - No scope → the changed files on this branch:
     ```bash
     base=$(git remote show origin | sed -n 's/.*HEAD branch: //p')   # usually main/master
     git diff --name-only "$(git merge-base HEAD "origin/$base")"...HEAD -- '*.lean'
     ```
   - Explicit files/dirs → use them (expand directories to their `.lean` files).
   - `<file> <decl>` → a single declaration.
   Print the resolved list so the user can confirm the right code is under review.
4. **Detect the PR** (skip if `--no-pr`):
   ```bash
   gh pr view --json number,url,state,headRefName
   ```
   If there is an open PR for the branch, record its number — each round's findings will be
   posted there. If there is none (or `--no-pr`), the reviews are **chat-only**. Say which
   mode you are in.

Then enter the round loop for `k = 1 … N`.

---

## Per round — REVIEW (driving instance dispatches a FRESH review agent)

Dispatch **one** `Agent` (`subagent_type: general-purpose`) with the verbatim prompt below.
A fresh dispatch every round — **never** `SendMessage` an earlier reviewer. The reviewer
reads the scoped code, works the four dimensions, verifies findings where it is cheap to do
so, and returns a structured findings list. It does **not** edit code and does **not** decide
whether the process is complete.

Substitute only the bracketed fields. For round 1, omit the "Prior rounds" block.

```
You are an INDEPENDENT, NEUTRAL code reviewer for a Lean 4 / mathlib project. You did NOT
write this code and you have NO stake in it. Review it the way a respected mathlib maintainer
reviews a stranger's PR: on the merits, and on nothing else.

Working dir:  [absolute project root]
Branch:       [branch name]
Build is clean at the scope below (the orchestrator verified this just now).

Scope — review ONLY these:
  [file / decl list, one per line, with line counts]

This is REVIEW ROUND [k] of [N].

Prior rounds (ONLY if k > 1 — treat these as ANOTHER reviewer's notes: NOT authoritative,
possibly wrong; verify against the code as it is NOW, and do not blindly re-raise or blindly
avoid them):
  Round 1 requested: [one line per finding]  → outcome: [implemented | reverted because X]
  ...

## Your stance (binding)
- OBJECTIVE and UNBIASED. Judge the code, never the author or the effort behind it. Do not
  soften findings to be kind. Do not manufacture findings to look thorough.
- OPEN-MINDED and SELF-SCEPTICAL. For every candidate finding, first STEELMAN the author's
  choice: can it be justified? Report the finding only if it survives the steelman. Stay open
  to the possibility that your own comment is the thing that is wrong.
- ...but NOT paralysed. Scepticism is not inaction. If a finding survives the steelman, state
  it plainly — do not bury real issues under hedging or drop them out of excessive doubt.
- The ROUND NUMBER DOES NOT CHANGE YOUR STANDARD. This may be the final round; that is
  irrelevant to you. Do NOT declare the code "done", and do NOT withhold warranted feedback
  because the review budget is ending. Report exactly what you would report on any round.
  Deciding when to stop reviewing is NOT your job — the orchestrator counts the rounds.

## Method (techniques from /review and /check-style)
Read every scoped declaration. For each, work the four dimensions below. VERIFY before you
report wherever it is cheap — ESPECIALLY automation and generalisation claims, which you can
test directly with `lean_multi_attempt` and `lean_diagnostic_messages`, and mathlib questions,
which you can settle with `lean_loogle` / `lean_leansearch`. A finding you tested is worth ten
you merely suspect.

### Dimension 1 — Are the definitions necessary?  (`def`/`abbrev` vs `notation` vs inline)
For each definition, ask: is much lost if this were just NOTATION (or inlined)? A definition
earns its keep when it:
  - carries valuable DATA (e.g. "the type of arithmetic functions"),
  - encodes an important PROPOSITIONAL quality (e.g. "the property of being prime"), or
  - encapsulates a horrendously complicated construction whose internals proofs NEVER need to
    unfold (e.g. "the type of real numbers").
Indicative, not definitive: definitions are more often Types or Props than terms of other
types (function types aside). A `def` that merely names a term, and whose internals get
unfolded all over the proofs anyway, is a candidate for `notation` / `abbrev` / inlining —
flag it, say what it should become, and say what (if anything) is actually lost by the change.

### Dimension 2 — Can it be generalised, and how far?
For each declaration, identify generalisations and say TO WHAT EXTENT and IN WHAT WAY:
weaken a typeclass to a parent (`CommRing`→`Ring`, `Field`→`DivisionRing`,
`MetricSpace`→`PseudoMetricSpace`, …), drop an unused hypothesis, point-localise
(`Continuous`→`ContinuousAt`), strict→weak (`0 < x`→`0 ≤ x`), concrete→abstract (`ℝ`→a general
field/space). The catalogue in `references/generalisation-patterns.md` lists the mechanical
weakenings and marks each "safe" (strictly more general, original is a special case) vs
"requires-restatement". Where cheap, TEST that the weaker form still compiles (swap it in, run
the diagnostics) — do not assert a generalisation you have not at least sketched.

### Dimension 3 — Best use of automation?
Are proofs making the best use of `simp` / `grind` / `aesop` / `fun_prop` / `omega` / `ring` /
`linarith` — or of PROJECT-LOCAL tactics (e.g. a `Tendsto_cont`-style helper the project itself
defines)? Can any proof be golfed or replaced outright by an automation call?
BINDING PRINCIPLE: DETERMINISTIC automation is always better than non-deterministic. It is far
better for a goal to be closed DETERMINISTICALLY by a tactic than to be proven by a long,
ad-hoc, inefficient hand-written script (the failure mode of an LLM brute-forcing a proof). So:
  (a) flag long manual proofs that a single tactic can close — but TEST with `lean_multi_attempt`
      before you claim it, and report the tactic that actually worked;
  (b) prefer robust, reproducible forms — `simp only [explicit list]` for non-terminal steps,
      `exact?`-found terms — over brittle ones; a bare TERMINAL `simp`/`grind`/`aesop` that
      closes the goal is fine and need not be squeezed;
  (c) point at the project-local tactic when one exists and the proof re-derives it by hand.
See `references/proof-patterns.md`, `references/golfing-rules.md`, `examples/automation.md`.

### Dimension 4 — Mathlib naming & style conventions
NAMES: `def`→lowerCamelCase, `lemma`/`theorem`→snake_case, `structure`/`inductive`→UpperCamelCase;
the `C_of_A_of_B` hypothesis-ordering pattern; the symbol dictionary (`add`, `mul`, `mem`, …);
American English; `private` helpers with the `_aux` suffix; `Is`-prefix Prop-valued classes.
STYLE: `by` at the END of the preceding line; focusing dots `·`; `fun x ↦` over `λ`; `<|` over
`$`; NO comments in proofs; 1–2 line docstrings with no proof strategy; every inequality written
`≤`/`<` (never `≥`/`>`) in Lean code. See `references/style-rules.md`,
`references/naming-conventions.md`. Do NOT nitpick what mathlib's own linters catch
automatically (over-long lines, unused variables/arguments) — spend your attention on what a
HUMAN reviewer has to catch.

## Output (return EXACTLY this; you do NOT edit code)
A findings list, most-important first. For each finding:
  - id:           R[k]-[n]
  - where:        file:line   (+ declaration name)
  - dimension:    1 def-necessity | 2 generalisation | 3 automation | 4 naming/style
  - severity:     must-fix | should-fix | consider
  - finding:      what is wrong / what is better (1–2 sentences)
  - change:       concretely what to do — the new name, the weakened signature, the exact tactic
  - verified:     TESTED (what you ran + the result) | JUDGEMENT (why you are still confident)
  - steelman:     the best case for leaving it as-is, and why the finding beats it
Then a short overall note. If nothing warrants change, say so HONESTLY and list what you
checked — but never reach that verdict merely because it is a late round.
```

### After the reviewer returns

1. **Report to the user (mandatory — rule 5.i).** Print the round's findings as a punch-list:

   ```
   ## Self-review — round k/N — findings

   Scope: <files/decls>          Reviewer: fresh independent agent

   | # | Where | Dim | Sev | Finding → recommended change | Verified? |
   |---|-------|-----|-----|------------------------------|-----------|
   | R k-1 | Foo.lean:45 | 3 automation | must-fix | 12-line manual proof; `grind [Foo.bar]` closes it | TESTED ✓ |
   | R k-2 | Foo.lean:12 | 2 generalisation | should-fix | `CommRing R` → `Ring R` (mul_comm unused) | TESTED compiles ✓ |
   | R k-3 | Bar.lean:8  | 1 def-necessity | consider | `def foo := …` unfolded everywhere; make it `abbrev`/notation | JUDGEMENT |
   | R k-4 | Bar.lean:30 | 4 naming/style | must-fix | `def cauchy_pv` → `cauchyPv` (defs are lowerCamelCase) | JUDGEMENT |

   Overall: <the reviewer's overall note>
   ```

2. **Post to the PR thread** (only if an open PR exists and `--no-pr` was not passed):

   ```bash
   gh pr comment <PR> --body "$(cat <<'EOF'
   ## Self-review — round k/N (independent neutral review)

   <the same findings table + overall note>
   EOF
   )"
   ```

   This is the reviewer's feedback landing on the thread, per the round model. If there is no
   PR (or `--no-pr`), skip this silently — the chat report is the record.

---

## Per round — IMPLEMENT (driving instance)

Implement **every** finding the reviewer returned, worst-first (must-fix → should-fix →
consider). For each:

1. **Apply the change.**
   - Renames: `Grep` every call site across the repo and update all of them — a missed call
     site is a defect (same rule as `/fix-pr-feedback` Phase 3b).
   - Multi-line proof rewrites: do them the way `/cleanup` Phase 4 does — one declaration at a
     time, using the golfing rules.
   - Mechanical edits (style, `λ`→`fun`, notation, small signature weakenings): edit inline.
2. **Verify.** After each edit run `lean_diagnostic_messages` on the touched file; for renames
   and signature changes run `lake build` on the affected modules. Don't accumulate breakage —
   fix or revert before moving on.
3. **The only permitted non-implementation.** If a change breaks the build or turns out to be
   incorrect and you cannot make it work, **revert it** and record it as
   `attempted → reverted because <reason>`. This is reported to the user **and** shown to the
   next round's reviewer (who, being open-minded, may drop it or propose a corrected version).
   Reverting-because-it-doesn't-work is allowed; skipping-because-you-disagree is not.
4. **Log** each finding's status (implemented / reverted-because-X), the action taken, and the
   verification result.

Do **not** commit and do **not** push (see the non-negotiable rules).

### Report the implementation summary (mandatory — rule 5.iii)

```
## Self-review — round k/N — implemented

| # | Where | Status | Action taken | Verified |
|---|-------|--------|--------------|----------|
| R k-1 | Foo.lean:45 | ✓ implemented | manual proof → `grind [Foo.bar]` | diagnostics clean |
| R k-2 | Foo.lean:12 | ✓ implemented | `CommRing R` → `Ring R`; 0 call sites affected | lake build ✓ |
| R k-3 | Bar.lean:8  | ✓ implemented | `def foo` → `abbrev foo` | diagnostics clean |
| R k-4 | Bar.lean:30 | ↩ reverted    | rename broke 3 downstream files; see note | reverted, build ✓ |

Files changed: 2   Lines: +6 −19   Build: ✓ clean
Reverted (carried to round k+1): R k-4 — <reason>
```

### Loop

- If **k < N**: begin round **k+1**'s REVIEW with a **fresh** `Agent` (pass this round's
  findings + outcomes as the "Prior rounds" block).
- If **k = N**: go to the final report and **STOP**.

A round in which the reviewer finds nothing is fine: the implementation is a no-op (report it
as such), and the loop **still proceeds** to the next round — N is fixed and the next fresh
reviewer may catch something this one didn't (or confirm the code is clean).

---

## Final report (after round N)

```
## Self-review complete — N rounds

| Round | Findings | Implemented | Reverted |
|-------|----------|-------------|----------|
| 1 | 4 | 3 | 1 |
| 2 | 2 | 2 | 0 |
| 3 | 1 | 1 | 0 |

Net change over all rounds:  +N −M lines across K files
Final build: ✓ clean

Still open (reverted / not resolved — YOUR call, the review budget is spent):
- R1-4 (Bar.lean:30) — reviewer wanted the rename `cauchy_pv → cauchyPv`; it breaks 3
  downstream files not in scope. Decide whether to widen the rename or keep the name.

PR thread: N round comments posted to <owner>/<repo>#<N>   (or: chat-only, no PR)
```

State plainly that the **N-round budget is exhausted and the code may still have open
items** — list them. Do not imply the code is now perfect or "done"; the command guarantees
N rounds of honest review-and-implement, not a finished result.

---

## Edge cases

- **Empty scope.** If the diff against base is empty and no scope was given, say so and ask
  the user to name files/decls — don't invent work to review.
- **Build broken on entry.** Stop at Phase 0 (doctor). Report where it's broken.
- **A finding that is raised and reverted across multiple rounds.** If the same issue keeps
  being suggested and keeps failing to implement, note the loop and surface it in the final
  report as a genuine design decision for the human — don't churn on it silently.
- **Large scope.** The review agent may itself dispatch one sub-reviewer per file (as
  `/overview` does) and aggregate; keep the returned findings list unified and de-duplicated.
- **User interrupts.** The user is driving; if they stop early, honour it — leave the working
  tree as-is and give the final report for the rounds completed so far.

## Design note — why a fresh agent each round

One persistent reviewer (via `SendMessage`) would accumulate an ego stake in its earlier
comments and drift toward "I already blessed this." A **fresh** agent each round is the
gold standard for objectivity — like sending the PR to a different reviewer each time — and
it is what makes rule 6 (no rubber-stamping on the final round) actually hold: a reviewer
that has never seen this code before has no reason to wave it through. The prior rounds'
findings are still passed in as *context to hold sceptically*, so the new reviewer neither
blindly re-raises settled points nor blindly avoids them.

## References

- built-in `/review`, `/code-review` — the review methodology this command specialises
- `commands/cleanup.md` — Phase 2 (style audit ≈ `/check-style`), Phase 4 (per-declaration golf)
- `commands/generalise.md`, `references/generalisation-patterns.md` — Dimension 2
- `references/proof-patterns.md`, `references/golfing-rules.md`, `examples/automation.md`,
  `references/mathlib-quality-principles.md` — Dimension 3
- `references/style-rules.md`, `references/naming-conventions.md` — Dimension 4
- `commands/fix-pr-feedback.md` — the implement-and-verify loop and the rename-all-call-sites rule

## Final step — record learnings

After the run, write 1–5 entries to `.mathlib-quality/learnings.jsonl` per the schema in
`skills/mathlib-quality/learning/schema.md`. Prioritise **what the independent reviewer caught
that the author-instance missed** — those are exactly the checks `/cleanup` should catch
earlier. Skip trivia already in the style guide.
