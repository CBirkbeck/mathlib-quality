---
name: extended-work
description: Pick up a ticket and work it to completion. When a sub-step needs a missing lemma, a missing dependency, or a sub-result not on the board, spawn a sub-ticket following /develop's template and recurse. Only stop on genuine off-track conditions — a wrong statement, scope outside the project, depth limit, or broken baseline build.
---

# /extended-work — Single-Ticket Work Session With Sub-Ticket Spawning

Pick up one ticket and work it to completion. If you encounter a blocker that has
a clear mathematical content — a missing lemma whose statement you can articulate,
a missing dependency that needs creating, a sub-step that needs its own intermediate
result — do **not** stop. Spawn a sub-ticket following `/develop`'s template, mark the
current ticket as depending on it, and recursively work the sub-ticket. When the
sub-ticket completes, return to the parent.

This skill is the execution counterpart to `/develop`. `/develop` does the original
project plan; `/extended-work` executes it, and when execution surfaces a gap that
the plan didn't anticipate, fills the gap by adding focused tickets *in /develop's
format* and proceeding. The role separation is preserved — every new ticket follows
the planning rules in `commands/develop.md` (statement, proof sketch, mathlib lemmas,
sources, generality decision).

The only legitimate hard stops are: completion of the original ticket and all its
sub-tickets; a ticket whose statement is mathematically wrong; a blocker that's
genuinely outside the project's scope; sub-ticket recursion depth exhausted; the
baseline `lake build` already broken on entry.

## Hard rules (read these first; they are non-negotiable)

The following responses are **forbidden** and will be rejected:

- *"This is a multi-week effort"* / *"This will take a long time"* / *"This is non-trivial"*
- *"Let me come back to this"* / *"I'll skip this for now"* / *"This needs more time"*
- *"I'm not sure I can do this"* / *"This might be too complex"*
- *"Let me try a different approach"* without evidence. Pivoting away from the
  planned sketch is only allowed after proving the planned approach fails. If the
  failure is a missing piece with clear mathematical content, **spawn a sub-ticket
  for it and proceed** — that is not pivoting, that is filling in a gap.
- Asking the user mid-work *"should I continue?"* / *"do you want me to keep going?"*
  — yes, continue. Don't ask.
- Marking a ticket "done" with a `sorry` still in the file. **Never.**
- Hard-stopping on MATHLIB GAP or a missing sub-lemma when the gap is small enough
  to be a focused sub-ticket. The presumption is **spawn a sub-ticket**, not stop.
  Stops are reserved for genuinely off-track cases (criteria below).

The following are **mandatory**:

- Read the ticket fully. Read the Statement. Read the Proof Sketch. Read the cited
  Sources if you can access them. The plan is in the ticket; follow it.
- Work in a tight loop: try → diagnose → adjust → retry. Use `lean_multi_attempt` to try
  several tactics at once when stuck.
- Search mathlib whenever the plan says "use `<lemma>`" — don't assume a name; verify it.
  Use the five-method search from `references/mathlib-search.md`.
- Checkpoint progress in the ticket's `**Progress**:` field every time you make a
  meaningful step. Future sessions resume from these notes.
- Stop only on the hard stop conditions below.

## Stop conditions — two tiers

### Tier A — Spawn-and-continue (the default response to blockers)

These conditions used to be hard stops. They are now triggers to spawn a sub-ticket
via the focused-planning flow below, then continue working. The intent is that
`/extended-work` is **self-sufficient at filling in gaps within the project's scope**.

A1. **MATHLIB GAP that can be a project lemma** — a mathlib lemma the sketch
    references doesn't exist (after the five-method search), and the missing fact
    is small enough to be a focused project lemma. Spawn a sub-ticket with the
    lemma's statement and the sketch you would use to prove it. Recurse into the
    sub-ticket. When done, return to the parent step.

A2. **MISSING SUB-LEMMA** — a step of the parent's sketch needs an intermediate
    result the sketch didn't surface as its own lemma, but you can state it
    cleanly. Spawn a sub-ticket. Recurse. Return.

A3. **DEPENDENCY MISSING FROM THE BOARD** — the current ticket's `Depends on`
    names a ticket that doesn't exist yet, or a declaration the ticket assumes
    exists but doesn't. Spawn a sub-ticket for the missing dependency (or
    declarations the parent assumes), recurse, return.

A4. **PARAMETRIC SUB-STEP NEEDED** — the sketch's step is parametric in a way
    that's better discharged as its own universally-quantified lemma. Spawn a
    sub-ticket with the universal claim. Recurse. Return.

In every Tier-A case, log to the parent ticket's progress notes what was spawned
and why, then proceed.

### Tier B — Genuine hard stops (these end the session)

Stop and report **only** when one of these is true:

B1. **DONE** — The original ticket and every sub-ticket it transitively spawned
    are complete. `lean_diagnostic_messages` clean on every touched file; no
    `sorry` anywhere in the new declarations; `#print axioms` clean; `lake build`
    clean on the modules touched.

B2. **PROOF-SKETCH FUNDAMENTALLY WRONG** — the parent's sketch is not just
    missing an ingredient (Tier A); it is wrong as a proof strategy. For example,
    "induction on n" but the inductive step would need a hypothesis the
    statement doesn't grant. No reasonable sub-ticket fixes this — only a
    replan does. Your report MUST name:
    - which step is fundamentally wrong
    - why no sub-ticket of bounded scope can fix it
    - a concrete replanning suggestion (re-state with extra hypothesis, replace
      strategy with X, etc.)

B3. **SCOPE / DEFINITION ERROR** — the ticket's stated declaration is
    mathematically wrong (conclusion false as stated; hypotheses don't entail
    the conclusion). Report a counterexample or a concrete reason. User decides
    whether to fix the statement or pivot.

B4. **OFF-TRACK** — the work the worker is being asked to do isn't a
    recognisable extension of the project's plan. Specifically, one of:
    - The missing lemma is large enough to be a mathlib contribution in its
      own right, not a focused project lemma (= upstream contribution
      candidate, not a sub-ticket)
    - The sub-ticket needed would itself require sub-tickets of unbounded
      mathematical depth (= the gap is research-scale, not engineering-scale)
    - The work the worker is on contradicts a stated intent in `plan.md` or
      the parent ticket's generality decision
    - Re-planning the parent's sketch is needed before sub-tickets can be
      added meaningfully

    "Off-track" requires evidence. It is **not** "I don't like this approach".
    Your report MUST cite the specific reason from the list above.

B5. **DEPTH LIMIT** — sub-ticket recursion has reached depth 3 (configurable;
    see below). Past this, sub-ticketing is getting away from the parent's
    scope. Stop, report the spawned chain, let the user decide.

B6. **BROKEN BASELINE** — `lake build` was already broken when work started.
    The project isn't in a workable state. Hard stop on entry (Phase 2b).

What is **not** a stop condition:

- "I've been trying for a while." Keep going.
- "This is harder than I thought." Keep going.
- "I want to try a different approach." If the planned approach fails because
  of a missing ingredient with clear content, spawn a sub-ticket — that is
  filling in a gap, not pivoting.
- "The proof is long." Long is fine. Keep going.
- "I think there's a more elegant proof." Implement the planned proof. Golf
  in `/cleanup` later.
- "The mathlib lemma I expected isn't there." Spawn a sub-ticket per A1.
- "A dependency isn't on the board yet." Spawn a sub-ticket per A3.

## Usage

```
/extended-work                              # Auto-pick the next available ticket
/extended-work --ticket T042                # Specific ticket
/extended-work --resume                     # Resume an in_progress ticket
/extended-work --max-depth N                # Override sub-ticket recursion limit (default 3)
```

For new projects, run `/develop` first to create the original ticket board.
Sub-tickets are added by `/extended-work` itself during execution.

---

## Spawning sub-tickets (focused planning)

When you hit a Tier-A blocker (missing lemma, missing dependency, parametric
sub-step needed), perform a focused-planning pass following `commands/develop.md`'s
ticket template:

1. **Re-verify the gap is real.** Run the five-method mathlib search
   (`references/mathlib-search.md`). Search the project's existing declarations.
   A "missing" lemma that actually exists under a different name is not a Tier-A
   trigger — use the existing lemma and continue.

2. **State the new ticket using `/develop`'s ticket template** (read
   `commands/develop.md` for the exact field set):
   - `Status`: open
   - `Title`: a math-name description in English
   - `File`: same file as parent unless the new lemma is naturally in a
     different module
   - `Depends on`: inherit from the parent's `Depends on` (the sub-ticket
     can only use what the parent could)
   - `Parent`: the parent ticket's ID (new field — tracks the sub-ticket
     relationship; show this in reports)
   - `Type`: `lemma` / `def` / etc.
   - `Statement`: the exact Lean statement of the missing piece
   - `Proof sketch`: numbered steps. Draw from the context in which the gap
     was hit — the parent's sketch step that referenced this is the
     starting point for the new sketch
   - `Mathlib lemmas needed`: anything you've identified during the search
   - `Sources`: inherit from the parent if the source covers this; otherwise
     leave empty (the worker doesn't research literature)
   - `Generality decision`: minimal — match the use site. Don't over-generalise
     in a sub-ticket; that's `/develop`'s job, not `/extended-work`'s.

3. **Update the parent ticket:**
   - Append the new ticket ID to `Depends on`
   - Add a progress entry: `<ISO>: spawning <new-ID> for <math reason>; sub-ticket added`
   - Status stays `in_progress` — the parent is paused, not blocked

4. **Save `tickets.md`.** This is the only file you write.

5. **Recurse.** Re-enter Phase 0 with `--ticket <new-id>`. Track the recursion
   depth (default cap = 3; see Tier-B condition B5).

6. **On sub-ticket completion**, return to the parent's Phase 4 from the
   step that triggered the spawn. The parent's progress notes record where
   to resume.

### Sub-ticket recursion depth

The depth is the count of ancestors a ticket has in the sub-ticket chain. Top-level
tickets (created by `/develop`) have depth 0. A sub-ticket spawned while working
a depth-0 ticket has depth 1. And so on. Default cap is 3 — past that, the work
has clearly drifted from the original ticket's scope and the user should judge.

Track the depth in each sub-ticket's `Parent` chain. When deciding whether to
spawn, check the current ticket's depth; if it's already at `--max-depth`, do
NOT spawn — hard stop with condition B5.

### What to put in the parent's progress notes when spawning

```markdown
**Progress**:
- 2026-05-11T09:14: spawning T078 for "absolute summability of M/n^k on k ≥ 4"
  (parent step 3 needs this; mathlib has tsum_comparison but with shape mismatch).
  Sub-ticket added with parent=T042. Pausing parent at step 3.
```

When the sub-ticket completes:

```markdown
**Progress**:
- ...
- 2026-05-11T10:42: resumed from sub-ticket T078 (done). Step 3 now uses
  `absoluteSummability_inv_pow` (newly proven). Continuing at step 4.
```

---

## Phases

```
PHASE 0   PICK             auto-pick next available ticket; or honour --ticket
PHASE 1   READ             read ticket in full; understand statement, sketch, sources
PHASE 2   PRE-WORK         dependencies done? lake build clean?
                           (missing dependency → spawn sub-ticket per Tier A3)
PHASE 3   STATE            write the declaration with sorry from the ticket's stated form
PHASE 4   PROVE            iterate to completion using the proof sketch
                           (mathlib gap → spawn sub-ticket per Tier A1 / A2)
PHASE 5   VERIFY           no sorry, no axiom, lake build clean
PHASE 6   GATES            cleanup-gates on the diff
PHASE 7   MARK DONE        update ticket status; checkpoint final progress
                           (if a parent was paused for sub-tickets, return to it)
PHASE 8   REPORT
```

Sub-tickets follow the same phase loop with their own depth indicator. The
agent's stack of active tickets is tracked implicitly via each ticket's
`Parent` field; resumption after a sub-ticket completes is via the parent's
progress notes.

For cleanup tickets:

```
PHASE 0   PICK             same
PHASE 1   READ             ticket points at a file
PHASE 2   DELEGATE TO /cleanup  invoke /cleanup <file> (full 8-phase workflow)
PHASE 7   MARK DONE
PHASE 8   REPORT
```

---

## PHASE 0 — Pick the ticket

If `--ticket <id>` was passed: load that ticket. Verify status is `open` or `in_progress`
(if `--resume`).

Otherwise: scan `.mathlib-quality/tickets.md`. Find the first ticket where:
- `Status` is `open`, AND
- Every `Depends on` ticket is `done`.

Print the picked ticket's title, ID, and status. Set its status to `in_progress` with a
timestamp. Save the ticket board.

If no ticket is available: print `No open tickets with met dependencies. Either run
/develop --status to see why, or run /develop to plan more work.` and stop.

---

## PHASE 1 — Read the ticket

Read the entire ticket in `.mathlib-quality/tickets.md`. The ticket has been written by
`/develop` to be **complete and self-contained**. It contains:

- The exact Lean **statement** to prove
- A numbered **proof sketch** referencing sources
- The **mathlib lemmas** needed at each step
- The **sources** (papers, books) the sketch is drawn from
- The **generality decision** (which typeclasses, which abstraction level)
- **Progress notes** from previous `/extended-work` sessions on this ticket (if `--resume`)

If any of the above fields is missing or vague, the ticket isn't ready. Stop and report
to the user with: `Ticket TXXX is not fully specified — needs <field>. Re-run /develop
to complete the ticket plan.` Do not invent the missing pieces yourself.

If the ticket is a CLEANUP ticket (type: `cleanup`), skip to Phase 2 (delegate path).

---

## PHASE 2 — Pre-work checks

### 2a. Dependencies actually done (or spawn a sub-ticket)

For each `Depends on: TYYY`, verify `TYYY` is genuinely done — open the file, find the
declaration `TYYY` covers, confirm:
- Compiles
- No `sorry`
- Signature matches what the current ticket assumes

If any dependency fails the check:

- **If the dependency ticket exists but has `sorry`** (or hasn't been worked
  yet, status `open`): switch to working that ticket first. Save the current
  ticket's state, recurse into the dependency with `--ticket <its-id>`. When
  the dependency finishes, return to the current ticket.
- **If the dependency ticket exists but its declaration's signature differs**
  from what the current ticket assumes: this is a real planning bug — the
  parent's signature drifted. Hard stop B3 (SCOPE / DEFINITION ERROR) so the
  user can reconcile.
- **If the dependency ticket is missing entirely** (named in `Depends on`
  but no ticket in the board with that ID, or named declaration doesn't
  exist in the project): spawn a sub-ticket for it (Tier A3), recurse,
  return.

Only hard-stop here if the dependency situation is genuinely off-track
(B3 or B4).

### 2b. Baseline build

```bash
lake build [target_module_for_this_ticket]
```

Must pass. If it doesn't, the project isn't in a state to work — hard stop. Don't try to
fix project-wide breakage from inside a single ticket.

For cleanup tickets: jump straight to delegation in 2c.

### 2c. Cleanup-ticket delegation

If this ticket's type is `cleanup`:

1. Invoke `/cleanup <file>` (the file the cleanup ticket targets).
2. Wait for `/cleanup` to complete its full 8-phase workflow.
3. If `/cleanup` reports success (Phase 6 gates pass), mark this ticket `done`. Skip to
   Phase 8.
4. If `/cleanup` reports failure, this is a stop condition for the cleanup ticket — the
   underlying file has issues. Mark the cleanup ticket `blocked` and report what failed.
   Don't try to fix `/cleanup`'s output yourself.

Cleanup tickets are easy because the heavy lifting is in `/cleanup`. The remaining
phases (3–7) below are only for proof/definition tickets.

---

## PHASE 3 — State the declaration

Open the file the ticket targets. Place the declaration at the right location (per the
ticket's `File` and the natural ordering — defs before lemmas about them; lemmas in
dependency order).

Write the declaration **exactly as stated in the ticket's Statement field**. Don't
modify the signature. Don't "improve" the type. Don't add or drop hypotheses. The
planning agent decided the form; your job is to prove it as stated.

End with `:= by sorry` so the file compiles and you have a target to work against.

```bash
lean_diagnostic_messages [file]
```

Confirm the declaration parses, the `sorry` is registered as a warning, and nothing else
broke.

---

## PHASE 4 — Prove

Work the proof sketch step by step. For each step:

### 4a. Find the lemma (or spawn a sub-ticket)

The sketch names a mathlib lemma (e.g., "Apply `Finset.prod_image`"). Verify the lemma
exists with that exact name and signature:

```
lean_loogle "<expected type signature>"
# OR
lean_local_search "<lemma name>"
```

If the lemma exists with the exact name: use it.

If the lemma exists with a slightly different name: use the actual name. Update the
ticket's progress notes with the actual name found.

If the lemma doesn't exist after the **five-method search** (`mathlib-search.md`):
this is a Tier-A MATHLIB GAP. Decide whether it qualifies for A1 (focused
project lemma) or B4 (off-track, mathlib-contribution scale):

- **A1 (spawn sub-ticket and continue)** if the missing fact is:
  - Statable in one or two Lean lines
  - Provable from facts already in mathlib or already in the project
  - Naturally part of the project's mathematical area (not an isolated
    abstract algebra fact when the project is about analysis, etc.)

  Then spawn a sub-ticket per the "Spawning sub-tickets" section. Statement
  is the needed lemma's type; sketch is what you would do to prove it from
  the existing infrastructure. Recurse into the new ticket.

- **B4 (off-track, real stop)** if the missing fact is:
  - A major mathlib API gap that would need a multi-file contribution
  - A research-scale result (a published-paper theorem nobody has formalised)
  - Outside the project's stated area

  Report B4 with the concrete reason and let the user decide whether to
  ticket it upstream, redirect the parent, or pause the project.

In neither case do you invent a "substitute that looks similar" — that's how
silent inconsistency creeps in.

### 4b. Apply the step

Write the tactic call. Run `lean_diagnostic_messages` to see the new goal state. Use
`lean_goal` if you need a fine-grained read of the goal at a specific position.

If the tactic produces an unexpected goal: examine why. Often it's because a hypothesis
needs to be massaged first (`push_cast`, `simp only [foo]`, etc.). The proof sketch may
not list every micro-tactic — small bridging steps are expected. Big detours are not.

### 4c. Loop

Repeat 4a–4b until the proof closes. Use `lean_multi_attempt` aggressively when stuck on
a single goal:

```
lean_multi_attempt [
  "exact <lemma> h",
  "apply <lemma>; exact h",
  "simp [<lemma>]; exact h",
  "grind [<lemma>]"
]
```

### 4d. Checkpoint

Every time you successfully close a goal that was nontrivial (took >1 attempt or
required >1 lemma), update the ticket's progress notes:

```markdown
**Progress**:
- 2026-05-06T10:32: stated the declaration; sorry on line 47
- 2026-05-06T10:38: closed step 1 (Finset.prod_comp); 3 sub-goals remain
- 2026-05-06T10:51: closed step 2 (Finset.prod_image); refining at the n=0 base case
- ...
```

The progress notes serve two purposes: a future `/extended-work --resume` can pick up
exactly where you left off, and the user can scan the ticket board to see how things are
going without reading the full Lean files.

### 4e. Off-script tactics are fine; off-script proofs are not

Small bridging tactics that the sketch doesn't explicitly mention (`push_cast`, `simp`,
`norm_cast`, `omega`, `ring`) are fine — the sketch describes the mathematical argument,
not every Lean micro-step. Use them.

A wholesale change in approach (the sketch said "induction on n", you do "structural
induction on the term") is **not fine** without first proving the planned approach
fails. If you genuinely think there's a better proof, finish the planned one first;
golf in `/cleanup` later.

---

## PHASE 5 — Verify

```bash
lean_diagnostic_messages [file]      # must be clean
grep "sorry" [file]                  # must find none in the new declaration
```

Then check axioms:

```lean
#print axioms decl_name
```

Must show only the standard set: `propext`, `Quot.sound`, `Classical.choice`, plus any
axioms that mathlib uses (these are accepted). If a `sorryAx` appears, your declaration
isn't actually proven — the `sorry` may have been moved into a `have`. Find it. Prove it.

Then a project build:

```bash
lake build [target_module]
```

Must succeed. If it fails on a different file (your change broke something downstream),
that's a Phase-5 stop: the ticket as planned has unforeseen consequences. Hard stop,
condition 4 (SCOPE/DEFINITION ERROR).

---

## PHASE 6 — Gates

Run the cleanup-gates from `references/cleanup-gates.md` on the diff your work
produced:

| Gate                           | Expected for this ticket |
|--------------------------------|--------------------------|
| `lake_build_file`              | ✓ pass                  |
| `definition_protected`         | ✓ pass — the only def changes are the new declaration the ticket created. If the diff touches OTHER def lines, that's a defect. |
| `theorem_statement_protected`  | ✓ pass — the only theorem/lemma changes are the new declaration the ticket created. |
| `cumulative_no_unintended_breakage` | ✓ pass — call sites elsewhere still compile |

Gate failures here mean your work touched something the ticket didn't authorise. Find
out what (the gate's `Details` will name the line) and revert the unauthorised part.

---

## PHASE 7 — Mark done

Update `.mathlib-quality/tickets.md`:

```markdown
### [TXXX] <title>
- **Status**: done   (was: in_progress; finished YYYY-MM-DDTHH:MMZ)
...
```

Append a final progress note:

```markdown
**Progress**:
- ...
- 2026-05-06T11:42: DONE — `decl_name` proven, lake build clean, all gates pass
```

---

## PHASE 8 — Report

### On DONE

```
## /extended-work report — [TXXX] <title>

Status: DONE
Time on ticket: from <start ISO> to <end ISO>
Cycles: <approximate number of try-diagnose-adjust loops>

### Sub-tickets spawned during this session
- [TYYY] <math name> (depth 1) — DONE
- [TZZZ] <math name> (depth 2, spawned from TYYY) — DONE
- ...
(If none: "None.")

### Result (for the original ticket and each sub-ticket completed)
- Declaration: `<decl_name>` at <file>:<line>
- Lines: <N>
- Mathlib lemmas used: <list>
- Off-script bridging tactics needed: <list>

### Diagnostics
✓ lean_diagnostic_messages clean on all touched files
✓ No sorry in the new declarations
✓ #print axioms shows only standard set
✓ lake build clean on <modules>

### Gates
✓ definition_protected
✓ theorem_statement_protected
✓ lake_build_file
✓ cumulative_no_unintended_breakage

### Next ticket
<auto-suggest the next available ticket per dependency analysis, or "none ready">
```

### On a Tier-B hard stop

```
## /extended-work report — [TXXX] <title>

Status: BLOCKED — <one of: PROOF-SKETCH FUNDAMENTALLY WRONG (B2) /
                  SCOPE-DEFINITION ERROR (B3) / OFF-TRACK (B4) /
                  DEPTH LIMIT (B5) / BROKEN BASELINE (B6)>

### Sub-tickets spawned during this session
- [TYYY] <math name> (depth 1) — DONE / in_progress / blocked
- ...

### What stopped the work
<concrete description as required by the corresponding stop condition.
For B4 (OFF-TRACK), cite the specific bullet from the B4 definition that
applies: mathlib-contribution scale, research-scale depth, plan
contradiction, or replanning needed. "I don't like this approach" is not
a valid B4 reason.>

### What was tried
<specific tactics, mathlib searches, sub-tickets considered but not spawned
because they would also be off-track>

### Concrete suggestion
<a specific change: re-state with extra hypothesis, ticket the missing
lemma upstream to mathlib, replan the parent's sketch via /develop --continue,
etc. Not "this needs rethinking".>

### Ticket state
- Parent: status in_progress (left for the user to decide)
- Sub-tickets that completed: status done
- Sub-tickets that didn't complete: in_progress
- Progress notes updated through <ISO>
```

The original ticket stays `in_progress` so `/develop --status` (or
`/project-status`) shows it. The user decides whether to replan, escalate,
or move on.

---

## Multi-ticket / batch usage

`/extended-work` is single-ticket. To work several in sequence:

```bash
# bash loop in the user's terminal
for i in $(seq 1 10); do
  echo "iteration $i"
  # invoke /extended-work; capture exit; break if BLOCKED
done
```

Or run `/extended-work` repeatedly in Claude Code, each time letting it auto-pick the
next ticket. The pattern keeps each ticket's context isolated, which matches the
"deep focus on one ticket" principle.

For cleanup-cadence-driven sequences, this naturally executes in dependency order:
proof-tickets followed by their cleanup-tickets followed by the next proof-ticket.

---

## Why this design

`/develop` produced the original plan. The ticket has a statement, sketch, sources,
lemmas. But in practice no plan anticipates every sub-step — proofs surface ingredients
the planner didn't foresee. Past versions of this command hard-stopped on those
surprises, which felt productive (concrete report back) but in practice left workers
parked, waiting for the user to manually add a ticket and resume.

The new design is: **gaps that have clear mathematical content become sub-tickets,
and the worker keeps going**. The role separation with `/develop` is preserved —
every sub-ticket follows `/develop`'s ticket template (Statement / Proof Sketch /
Mathlib Lemmas / Sources / Generality), so a `/develop --continue` would recognise
the work. The split is no longer "develop plans, extended-work executes blindly"
but "develop plans the original, extended-work fills focused gaps and executes
both".

Hard stops are reserved for cases where sub-ticketing genuinely doesn't help:
the parent's sketch is wrong as a strategy (B2); the parent's statement is
mathematically wrong (B3); the gap is research-scale rather than engineering-scale
(B4); the sub-ticket chain has gone too deep (B5); the baseline build is broken
(B6). For each, the stop produces a concrete, evidenced report back. "It's hard"
is still not evidence.

---

## Reference

- `commands/develop.md` — the planner that produces the tickets this skill executes
- `references/cleanup-gates.md` — the gate definitions used in Phase 6
- `references/mathlib-search.md` — the five-method search used in Phase 4a
- `commands/cleanup.md` — invoked directly by Phase 2c when the ticket is a cleanup ticket
