---
name: prove
description: Plan and prove a mathematical development with ticket-based project management
---

# /prove - Mathematical Development Engine

Plan and execute a mathematical development project. Creates a comprehensive plan,
manages work via a ticket system, dispatches focused worker agents, and builds clean
API along the way.

**This is the default skill for proving new theorems.** It handles everything from
project planning to proof execution to periodic cleanup.

## Usage

```
/prove                              # Start planning a new development
/prove --continue                   # Resume from existing tickets
/prove --status                     # Show current ticket board
```

---

## Phase 1: Project Planning (Super Agent)

The planner runs ONCE at the start to create the full development plan. This is the
most important phase — a good plan prevents wasted work.

### 1a: Gather Context

Ask the user:

```
## New Mathematical Development

1. **Goal**: What are you trying to prove? (Main theorem/result)
2. **References**: Do you have papers, textbook chapters, or mathlib docs to follow?
   (PDF paths, URLs, or descriptions)
3. **Existing code**: Any Lean files already started? (paths)
4. **Scope**: Is this a single file or multi-file development?
5. **Mathlib version**: Which toolchain/mathlib version? (check lakefile.lean)
```

### 1b: Study References

If the user provides references:
1. Read them thoroughly (use WebFetch for URLs, Read for PDFs/files)
2. Extract the proof structure: what are the key lemmas, definitions, and dependencies?
3. Identify which parts likely already exist in mathlib
4. Map out the dependency graph: what must be proved before what?

### 1c: Search Mathlib Exhaustively

Before planning ANY definition or lemma:
1. Search mathlib for the main result — it may already exist
2. Search for each key definition — use `exact?`, Loogle, grep
3. Search for each intermediate lemma
4. Document what exists, what's close, and what's genuinely new

**Rule: Never define what mathlib already has.** If mathlib has a close variant,
use it or generalize from it — don't redefine.

### 1d: Design the API

Think about this development as building a LIBRARY, not just proving one theorem.

For each new definition:
- **Is it genuinely needed?** Can we inline it or use an existing mathlib concept?
- **Is it stated in maximum generality?** (e.g., over `CommRing` not just `ℤ`)
- **What API lemmas does it need?** (`_iff_`, `_of_`, `_mono`, `_comp`, `_add`, etc.)
- **What namespace should it live in?**
- **What `@[simp]`/`@[ext]`/`@[norm_num]` tags does it need?**

**Rule: No one-off definitions without API.** Every definition must have at least
basic API lemmas (membership, composition, monotonicity as appropriate).

### 1e: Write the Plan

Create a comprehensive plan document at `.mathlib-quality/plan.md`:

```markdown
# Development Plan: [Title]

## Goal
[Main theorem statement in Lean, precisely]

## References
- [List of references with how each maps to the plan]

## Mathlib Inventory
| Concept | Mathlib Status | Our Action |
|---------|---------------|------------|
| FooBar | `Mathlib.Topology.FooBar` | USE directly |
| BazQux | Close: `Mathlib.Algebra.Baz` | GENERALIZE from existing |
| NewThing | Not in mathlib | DEFINE with full API |

## File Structure
- `MyProject/Defs.lean` — core definitions + API
- `MyProject/Basic.lean` — basic properties
- `MyProject/Main.lean` — main theorem

## Dependency Graph
```
Def A → Lemma B → Lemma C ──→ Main Theorem
                → Lemma D ──↗
Def E → Lemma F ──────────↗
```

## Generality Decisions
- [Explain key generality choices: why CommRing vs Ring, etc.]
```

### 1f: Create Tickets

Create the ticket board at `.mathlib-quality/tickets.md`:

```markdown
# Ticket Board

## Summary
- Total: N tickets
- Open: N | In Progress: 0 | Done: 0
- Parallel capacity: M workers (based on dependency analysis)

## Tickets

### [T001] Define FooBar and basic API
- **Status**: open
- **File**: MyProject/Defs.lean
- **Depends on**: none
- **Parallel**: yes (no dependencies)
- **Description**: Define `FooBar` over `CommMonoid`. Create API:
  `fooBar_zero`, `fooBar_one`, `fooBar_mul`, `fooBar_mono`.
  Tag `fooBar_zero` and `fooBar_one` with `@[simp]`.
- **Mathlib check**: Not in mathlib. Closest: `Mathlib.Algebra.Foo` (different).
- **Naming**: `FooBar` (UpperCamelCase def), `fooBar_zero` (snake_case lemma).
- **Generality**: State over `CommMonoid` not `CommRing` — multiplication is all we need.

### [T002] Prove fooBar_comp
- **Status**: open
- **File**: MyProject/Basic.lean
- **Depends on**: T001
- **Parallel**: yes (after T001, parallel with T003)
- **Description**: Prove `fooBar_comp : FooBar (f ∘ g) = FooBar f * FooBar g`.
  Reference: Theorem 3.2 in [Paper]. Proof sketch: unfold, use `Finset.prod_comp`.
- **Proof approach**: Should follow from `Finset.prod_comp` + API from T001.

### [T003] Prove fooBar_mono
- **Status**: open
- **File**: MyProject/Basic.lean
- **Depends on**: T001
- **Parallel**: yes (after T001, parallel with T002)
- **Description**: ...

### [CLEANUP-1] Run /cleanup on MyProject/Defs.lean
- **Status**: open
- **File**: MyProject/Defs.lean
- **Depends on**: T001
- **Parallel**: no (must wait for T001 to complete)
- **Type**: cleanup
- **Description**: Run /cleanup to ensure mathlib quality before building on top.

### [T004] Main theorem
- **Status**: open
- **File**: MyProject/Main.lean
- **Depends on**: T002, T003, CLEANUP-1
- **Parallel**: no (needs all prerequisites)
- **Description**: ...
```

**Ticket rules:**
- Every definition ticket includes its API lemmas
- Every 3-5 proof tickets, insert a CLEANUP ticket for the files worked on
- Mark parallel opportunities explicitly
- Include proof approach/sketch from references
- Include mathlib check result
- Include precise naming following mathlib conventions

### 1g: Get User Approval

Show the plan and ticket board to the user. Ask:
```
## Plan Review

I've created N tickets across M files.
- K definitions with API
- L lemmas/theorems
- P cleanup checkpoints
- Up to Q workers can run in parallel at peak

Does this plan look right? Should I adjust anything before starting?
```

---

## Phase 2: Execution (Worker Agents)

### 2a: Pick Up a Ticket

When starting work (or resuming with `--continue`):

1. Read `.mathlib-quality/tickets.md`
2. Find the next open ticket whose dependencies are all done
3. **Update the ticket status to `in_progress`** immediately (with timestamp)
4. Read the file context and any dependent files

### 2b: Work the Ticket

For each ticket, the worker agent follows this cycle:

```
Search → Draft → Prove → Verify → Iterate
```

#### Search (before writing ANY code)
1. **Search mathlib** for the result or close variants
   - Use `exact?`, `apply?`, Loogle, grep
   - If found: use it directly, update ticket as "resolved by mathlib"
2. **Search mathlib** for each helper lemma you plan to use
3. **Check generality**: is your statement as general as it could be?
   - Can `Ring` be weakened to `Semiring`? `Finset` to `Set`?
   - The user wants MAXIMUM generality, no shortcuts

#### Draft
1. Write the definition/lemma statement precisely
   - Follow mathlib naming: `conclusion_of_hypothesis`
   - Use the right universe levels, typeclasses, implicit vs explicit args
2. For definitions: write ALL planned API lemmas as `sorry` stubs
   - This forces you to think about the API before proving anything
3. Verify the statements compile: `lean_diagnostic_messages`

#### Prove (multi-cycle for each sorry)

For each `sorry`, run cycles until filled:

**Cycle:**
1. Read the goal state with `lean_goal`
2. Think about the mathematical content — what is this really saying?
3. Search for relevant lemmas: `lean_loogle`, `exact?`, `apply?`
4. Generate 2-3 proof candidates
5. Test with `lean_multi_attempt`
6. If none pass:
   - Try automation: `grind`, `simp`, `aesop`, `fun_prop`, `omega`
   - Try a different proof strategy
   - Try breaking into sub-goals with `have` or `suffices`
7. If stuck after 3 attempts on the same sorry:
   - Step back and reconsider the approach
   - Is the statement correct? Is it general enough?
   - Would a helper lemma make this easier?
   - If a helper lemma is needed: **go back to the ticket board and add
     new tickets** for the helper lemma and its API. Do not just prove
     it inline as a one-off `have`.

**Generality rule:** If you find yourself proving a `have` block that's
more than 5 lines, ask: should this be its own lemma? If it's reusable,
extract it as a new ticket with proper naming and API.

#### Verify
1. `lean_diagnostic_messages` — no errors
2. Check all `sorry` stubs are filled for this ticket
3. Run through the /cleanup audit mentally:
   - No `by exact` wrappers
   - No single-use `have` blocks
   - Terminal simp not squeezed
   - Proper naming

### 2c: Complete the Ticket

1. **Update the ticket status to `done`** (with timestamp)
2. If the ticket revealed additional work needed:
   - **Add new tickets** to the board with full descriptions
   - Update dependency graph
   - Note which new tickets can be parallelized
3. Commit with a clear message: `feat: [ticket ID] description`

### 2d: Cleanup Tickets

When a CLEANUP ticket comes up:
1. Run `/cleanup` on the specified file
2. This applies the full 13-item audit + golfing rules to every declaration
3. Verify compilation after cleanup
4. Mark the cleanup ticket as done

---

## Phase 3: Review & Iterate

After all tickets are done:

### 3a: Final Review

1. Run `lean_diagnostic_messages` on every file
2. Run `lake build` to verify the full project
3. Check for any remaining `sorry`
4. Review the API: is it complete? Would a mathlib reviewer accept this?

### 3b: Final Cleanup

Run `/cleanup` on every file one more time.

### 3c: Report

```markdown
## Development Complete

### Files Created
| File | Definitions | Lemmas | Lines |
|------|------------|--------|-------|
| Defs.lean | 3 | 12 | 180 |
| Basic.lean | 0 | 8 | 120 |
| Main.lean | 0 | 3 | 90 |

### Tickets
- Total: N | Done: N | Added during execution: K

### Mathlib Usage
- Definitions reused from mathlib: M
- Lemmas found in mathlib: L
- New definitions created: D (with API)

### Generality
- [Summary of generality decisions made]

### Ready for PR?
- [ ] All files compile
- [ ] No sorry remaining
- [ ] /cleanup run on all files
- [ ] Naming follows mathlib conventions
- [ ] API is complete for all new definitions
```

---

## Parallel Execution

The planner identifies which tickets can run in parallel based on dependencies.

**How to run parallel workers:**
- The main agent dispatches multiple worker agents simultaneously
- Each worker picks up ONE ticket, updates its status, and works independently
- Workers must check the ticket board before starting (another worker may have taken it)
- A Lean project typically supports 2-3 parallel workers (limited by file dependencies
  and LSP server load)

**Parallel rules:**
- Two tickets on the SAME file cannot run in parallel
- Two tickets on DIFFERENT files CAN run in parallel if no import dependency
- CLEANUP tickets must run AFTER all proof tickets for that file
- The main theorem ticket must run AFTER all dependency tickets

---

## Key Principles

### 1. Maximum Generality, Always

> "They should never try and take shortcuts just to prove things for the immediate
> goal, they should always look to prove results in as general a way as possible,
> no matter how much work this will take."

- If a lemma works for `CommRing`, don't state it for `ℤ`
- If a lemma works for `Finset`, don't state it for `List`
- If a proof uses `n : ℕ`, check if it works for `n : ℤ` or `n : α` with a typeclass
- When in doubt, always choose the more general formulation

### 2. No One-Off Definitions

Every new definition must have:
- At least 3-5 API lemmas (zero, one, composition, monotonicity, etc. as appropriate)
- Proper namespace placement
- Appropriate automation tags (`@[simp]`, `@[ext]`, `@[norm_num]`, etc.)
- A docstring

If a definition would have no API, it should be inlined in the proof instead.

### 3. Mathlib First

Before creating ANY definition or lemma:
1. Search mathlib thoroughly
2. If it exists: use it
3. If something close exists: generalize from it
4. Only create new things when genuinely necessary

### 4. Workers Escalate, Never Shortcut

When a worker discovers a ticket needs more work than expected:
1. **Do NOT take shortcuts** (e.g., adding `sorry`, using weaker hypotheses,
   specializing to a concrete type)
2. **Go back to the ticket board** and:
   - Add a full description of the extra work needed
   - Break it into new tickets
   - Mark dependencies
   - Identify what can be parallelized
3. Continue with what CAN be done, leave the rest for other workers

### 5. Periodic Cleanup

Cleanup tickets are inserted every 3-5 proof tickets. They ensure:
- Code stays at mathlib quality throughout development
- Naming issues are caught early
- Proofs are golfed before being built upon
- API gaps are identified while context is fresh

---

## Ticket Status Values

| Status | Meaning |
|--------|---------|
| `open` | Ready to be picked up |
| `blocked` | Dependencies not yet done |
| `in_progress` | A worker is actively working on this |
| `done` | Completed and verified |
| `expanded` | Was too big, broken into sub-tickets |

---

## Reference

- `skills/mathlib-quality/references/golfing-rules.md` — golfing rules applied during cleanup
- `skills/mathlib-quality/references/proof-patterns.md` — data-driven proof patterns
- `skills/mathlib-quality/references/naming-conventions.md` — mathlib naming
- `skills/mathlib-quality/references/style-rules.md` — mathlib style
- `commands/cleanup.md` — cleanup procedure run during CLEANUP tickets
