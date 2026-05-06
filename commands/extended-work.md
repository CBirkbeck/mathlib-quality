---
name: extended-work
description: Pick up one ticket from the /develop ticket board and work it to completion or concrete approach error. Strict no-complaining, no-pivoting, no-divergence mode. Single-ticket focus, non-stop until a hard stop condition.
---

# /extended-work — Single-Ticket Work Session

Pick up one ticket and work on it. Don't stop until either the ticket is **done** or you
have a **concrete, evidenced reason** the planned approach doesn't work.

This skill is the execution counterpart to `/develop`. `/develop` plans, designs the API,
writes detailed tickets including the Lean statement and proof sketch from the user's
sources. `/extended-work` *executes* those tickets.

The split is deliberate: `/develop` does the thinking, `/extended-work` does the doing. A
worker that's been given a complete plan with the proof sketch should not need to think
about strategy — only about implementing the planned approach.

## Hard rules (read these first; they are non-negotiable)

The following responses are **forbidden** and will be rejected:

- *"This is a multi-week effort"* / *"This will take a long time"* / *"This is non-trivial"*
- *"Let me come back to this"* / *"I'll skip this for now"* / *"This needs more time"*
- *"I'm not sure I can do this"* / *"This might be too complex"*
- *"Let me try a different approach"* — **only** allowed after you have proven the
  planned approach fails, with concrete evidence (specific tactic that fails, specific
  mathlib lemma that turns out to not exist, specific hypothesis that's genuinely
  insufficient). General "I don't like this approach" is not evidence.
- Asking the user mid-work *"should I continue?"* / *"do you want me to keep going?"*
  — yes, continue. Don't ask.
- Marking a ticket "done" with a `sorry` still in the file. **Never.**

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

## Hard stop conditions

Stop the work and report **only** when one of these is true:

1. **DONE** — The ticket's declaration is stated and proven; `lean_diagnostic_messages`
   clean; no `sorry`; `#print axioms <decl>` shows only `propext`, `Quot.sound`,
   `Classical.choice` (or no axioms beyond mathlib's standard set); `lake build` clean
   on this module.
2. **PROOF-SKETCH FAILURE** — A specific step in the ticket's proof sketch cannot
   succeed, and you've exhausted the search/retry strategy. Your report MUST name:
   - which step failed (e.g., "Step 3: apply `Finset.prod_image`")
   - what you tried (specific tactics, specific mathlib searches, specific alternative
     formulations)
   - why each attempt failed (concrete error, not "didn't work")
   - a concrete replanning suggestion (e.g., "the proof sketch assumes `f` is injective,
     but the statement doesn't enforce that — needs an extra hypothesis")
3. **MATHLIB GAP** — A mathlib lemma the proof sketch references does not exist (and no
   equivalent variant does either, after the five-method search). Your report MUST name:
   - the missing lemma (the name the sketch expected)
   - the type signature that would be needed
   - what you tried as a substitute
   - whether the gap is a candidate for upstream contribution
4. **SCOPE / DEFINITION ERROR** — The ticket's stated declaration is mathematically
   wrong (the conclusion is false as stated; the hypotheses don't actually entail the
   conclusion). Your report MUST include a counterexample or a concrete reason the
   statement is wrong, not just "I think this might be wrong".
5. **DEPENDENCY NOT MET** — A ticket the current one depends on isn't actually done
   (the dependent declaration has `sorry`, doesn't compile, or has a different
   signature than the current ticket assumes). Stop and flag for the user.

What is **not** a stop condition:

- "I've been trying for a while." Keep going.
- "This is harder than I thought." Keep going.
- "I want to try a different approach." Only after exhausting the planned one.
- "The proof is long." Long is fine. Keep going.
- "I think there's a more elegant proof." Implement the planned proof. If it works,
  golf in `/cleanup` later. Don't pivot mid-implementation.

## Usage

```
/extended-work                       # Auto-pick the next available ticket
/extended-work --ticket T042         # Specific ticket
/extended-work --resume              # Resume an in_progress ticket from its progress notes
```

For new projects, run `/develop` first to create the ticket board.

---

## Phases

```
PHASE 0   PICK             auto-pick next available ticket; or honour --ticket
PHASE 1   READ             read ticket in full; understand statement, sketch, sources
PHASE 2   PRE-WORK         dependencies done? lake build clean?
PHASE 3   STATE            write the declaration with sorry from the ticket's stated form
PHASE 4   PROVE            iterate to completion using the proof sketch
PHASE 5   VERIFY           no sorry, no axiom, lake build clean
PHASE 6   GATES            cleanup-gates on the diff (definition / theorem / build)
PHASE 7   MARK DONE        update ticket status; checkpoint final progress
PHASE 8   REPORT
```

Or, for cleanup tickets:

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

### 2a. Dependencies actually done

For each `Depends on: TYYY`, verify `TYYY` is genuinely done — open the file, find the
declaration `TYYY` covers, confirm:
- Compiles
- No `sorry`
- Signature matches what the current ticket assumes

If any dependency fails the check: hard stop (DEPENDENCY NOT MET, condition 5).

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

### 4a. Find the lemma

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

If the lemma doesn't exist after the **five-method search** (`mathlib-search.md`): hard
stop, condition 3 (MATHLIB GAP). Don't invent a substitute that "looks similar".

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

Print:

```
## /extended-work report — [TXXX] <title>

Status: DONE  (or: BLOCKED-on-<concrete reason>)
Time on ticket: from <start ISO> to <end ISO>
Cycles: <approximate number of try-diagnose-adjust loops>

### Result
- Declaration: `<decl_name>` at <file>:<line>
- Lines: <N>
- Mathlib lemmas used: <list>
- Off-script bridging tactics needed: <list, e.g. push_cast at step 2>

### Diagnostics
✓ lean_diagnostic_messages clean
✓ No sorry
✓ #print axioms shows only standard set
✓ lake build clean on <module>

### Gates
✓ definition_protected
✓ theorem_statement_protected
✓ lake_build_file
✓ cumulative_no_unintended_breakage

### Next ticket
<auto-suggest the next available ticket per dependency analysis, or "none ready">
```

If the stop was a hard-stop condition 2–5 instead of DONE:

```
## /extended-work report — [TXXX] <title>

Status: BLOCKED — <one of: PROOF-SKETCH FAILURE / MATHLIB GAP / SCOPE-DEFINITION ERROR / DEPENDENCY NOT MET>

### What stopped the work
<concrete description as required by the corresponding stop condition>

### What was tried
<list of specific tactics, mathlib searches, alternative formulations attempted>

### Concrete suggestion for replanning
<not a vague "this needs rethinking"; a specific change>

### Ticket state
- Status: in_progress (left for the user to decide whether to mark blocked)
- Progress notes updated through <ISO>
```

The ticket stays `in_progress` so a `/develop --status` shows it. The user decides
whether to replan, escalate, or move on to other tickets.

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

## Why the strict no-complain mode

`/develop` produced a complete plan. The ticket has the statement, the sketch, the
sources, the lemmas. There should be nothing left to "figure out at the strategic
level." Workers that complain about difficulty have, in practice, been agents that
slipped into "let me reconsider the whole approach" mode — exactly what `/develop` was
designed to prevent.

If the plan is wrong (which can happen), the right response is hard-stop condition 2 or
3 with a concrete replanning suggestion — not "this is a multi-week effort." That's a
tractable signal back to the user. "It's hard" is not.

---

## Reference

- `commands/develop.md` — the planner that produces the tickets this skill executes
- `references/cleanup-gates.md` — the gate definitions used in Phase 6
- `references/mathlib-search.md` — the five-method search used in Phase 4a
- `commands/cleanup.md` — invoked directly by Phase 2c when the ticket is a cleanup ticket
