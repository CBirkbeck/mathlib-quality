---
name: develop
description: Plan a mathematical development project (planning-only). Searches mathlib, designs the API, drafts proof sketches from your sources, and writes detailed self-contained tickets. Workers run via /extended-work, not here.
---

# /develop — Mathematical Development Planner

Plan a mathematical development. Creates a comprehensive plan from your references,
designs the API for every new declaration, drafts the proof sketches step-by-step, and
writes a detailed ticket board where **every ticket contains the Lean statement and
the full proof sketch with cited sources** — detailed enough that no replanning is
needed once execution starts.

**`/develop` is planning-only.** Workers don't run here. Once the ticket board is
approved, invoke `/extended-work` to pick up the next available ticket and work it to
completion.

This split keeps strategic thinking (mathlib search, API design, proof sketching from
sources, generality decisions) in `/develop` and tactical execution (state declaration,
call planned lemmas, iterate to compilation) in `/extended-work`. It prevents the
"agent reconsiders the whole approach mid-proof" failure mode — once `/extended-work`
starts a ticket, the plan is fixed; the worker either implements it or hard-stops with
a concrete reason it can't.

## Usage

```
/develop                            # Auto-detect: new, resume, or takeover
/develop --continue                 # Audit the current ticket board against the code, propose updates
/develop --status                   # Show current ticket board
/develop --takeover                 # Force takeover mode on existing code (creates tickets to bring it to completion)
```

After any of these completes and the ticket board is approved, run `/extended-work` to
start (or resume) work.

---

## ChatGPT Second Opinion (Optional)

If the `chatgpt-math` MCP server is configured (check for `ask_chatgpt_math` tool),
`/develop` will consult ChatGPT at key moments for mathematical second opinions.
This is **not required** — the command works without it — but catches errors earlier:

- **Plan validation**: after drafting the plan, ask ChatGPT if the approach is sound
- **Source clarification**: if a referenced source is ambiguous, ask ChatGPT to fill in
  the gap (especially useful for "what's the canonical statement of theorem X")
- **Sketch sanity-check**: when drafting a proof sketch for a ticket, ask ChatGPT
  whether the sketch's argument structure is sound

(`/extended-work` may also consult ChatGPT during execution if available; that's
documented separately in `extended-work.md`.)

All ChatGPT questions must be **fully self-contained** — ChatGPT has no access to
local files. Include all definitions, theorem statements, and reference citations
inline in the question.

If `ask_chatgpt_math` is not available, skip all ChatGPT steps silently.

---

## Mode Detection

On startup, `/develop` determines the mode automatically:

1. Check for `.mathlib-quality/tickets.md` — if it exists, this is a **resume**
2. Check for `.lean` files with `sorry` — if found without tickets, this is a **takeover**
3. Otherwise, this is a **new project** — go to Phase 1

For `--continue`: skip mode detection, go straight to resume.
For `--status`: just print the ticket board and exit.

---

## Resume Mode

When tickets already exist (from a previous `/develop` session or another agent):

### R1: Deep Scan

Thoroughly assess the current state of the project:

1. **Read the plan** — `.mathlib-quality/plan.md`
2. **Read the ticket board** — `.mathlib-quality/tickets.md`
3. **Scan every `.lean` file** in the project:
   - Count remaining `sorry` declarations
   - Run `lean_diagnostic_messages` on each file — note errors and warnings
   - List every definition, lemma, and theorem with line counts
   - Check what compiles and what doesn't
4. **Cross-reference tickets with reality:**
   - Are tickets marked `done` actually done? (no `sorry`, compiles)
   - Are tickets marked `in_progress` still being worked on or abandoned?
   - Are there declarations in the code not covered by any ticket?
   - Are there tickets for declarations that no longer exist?
5. **Check mathlib** — have any of our definitions/lemmas been added to
   mathlib since the plan was made? (especially after a mathlib bump)

### R2: Status Report

Present findings to the user:

```markdown
## Project Status: [Title]

### Progress
| Status | Count |
|--------|-------|
| Done | D |
| In Progress | P |
| Open | O |
| Blocked | B |
| Stale (needs update) | S |

### Current State
- Files: N .lean files, M compiling, K with errors
- Sorries remaining: X total across Y files
- Errors: [list any compilation errors]

### Discrepancies Found
- [T005] marked done but `fooBar_comm` still has sorry on line 45
- [T008] marked in_progress but file hasn't changed since [date]
- `helper_lemma` on Defs.lean:120 exists but has no ticket
- [T012] depends on [T009] which was expanded — dependency may be stale

### Tickets Needing Update
- [T005]: should be reopened (sorry remains)
- [T008]: likely abandoned — should be reset to open
- NEW: need ticket for `helper_lemma` (uncovered declaration)
```

### R3: Cleanup-Cadence Audit

Before proposing updates to the user, audit whether the existing ticket board still
satisfies the cleanup cadence from §1f. Resumed projects routinely drift on cleanup
discipline because new tickets were added during execution without re-running the
cadence rule.

For each file in the project:

1. List all `done` and `in_progress` proof/definition tickets touching that file in
   dependency order.
2. Walk the list. After every 3rd one, there should be a cleanup ticket (open, in_progress,
   or done) before the next proof ticket. If not, the cadence is broken there — add a
   `[CLEANUP-<n>]` ticket to the proposal in R4 below.
3. After the last proof ticket on the file, there should be a final per-file cleanup ticket.
   If not, propose adding one.
4. If a milestone ticket is open and a `CLEANUP-ALL` doesn't precede it, propose adding one.
5. Verify the final `[CLEANUP-FINAL] /cleanup-all` ticket exists. If not, propose adding it.

Print the audit result before R4:

```
## Cleanup-cadence audit (R3)

| File | Proof tickets done | Cleanups present | Cleanups missing per cadence rule |
|------|--------------------|------------------|------------------------------------|
| Defs.lean | 5 | CLEANUP-1 (after T003) | none |
| Basic.lean | 4 | none | CLEANUP-X needed after T008; final cleanup missing |
| Main.lean | 1 (milestone open) | none | CLEANUP-ALL needed before milestone |

Pre-milestone /cleanup-all: missing (T010 is a milestone with no preceding CLEANUP-ALL)
Final /cleanup-all: missing
```

### R4: Update Plan with User

Discuss findings — including the cleanup-cadence audit from R3 — with the user:

```
## Proposed Updates

State:
1. Reopen [T005] — sorry still present
2. Reset [T008] to open — appears abandoned
3. Add new ticket for `helper_lemma`
4. [T012] dependency chain updated after [T009] expansion
5. Remove [T014] — `bar_mono` now exists in mathlib (added in recent bump)

Cleanup cadence (from R3 audit):
6. Add [CLEANUP-X] for Basic.lean (3 proof tickets done since last cleanup)
7. Add [CLEANUP-Y] final cleanup for Basic.lean
8. Add [CLEANUP-ALL-1] before T010 (milestone)
9. Add [CLEANUP-FINAL] as last ticket

Shall I apply these updates? Anything else to change?
```

Wait for user confirmation, then update `.mathlib-quality/tickets.md`. Items 6–9 are not
optional unless the user explicitly opts out — they're the cadence rule, not a suggestion.

### R5: Hand off to `/extended-work`

After updating the ticket board, `/develop --continue` is done. Tell the user:

```
Plan updated. Next available ticket: TXXX (<title>).
Run `/extended-work` to pick it up and work it to completion.
```

`/develop` does not execute. Workers run via `/extended-work`.

---

## Takeover Mode

When there's existing Lean code but no ticket system (e.g., taking over a project
started manually, by another agent, or from a template):

### T1: Full Project Audit

Scan everything thoroughly:

1. **Read every `.lean` file** — understand the mathematical content
   - What definitions exist? What are they doing mathematically?
   - What theorems are stated? Which are proved, which have `sorry`?
   - What's the dependency structure between files?
   - What imports from mathlib are used?
2. **Read any documentation** — `README.md`, docstrings, comments
3. **Check compilation** — `lean_diagnostic_messages` on each file, then `lake build`
4. **Assess quality:**
   - Naming conventions followed?
   - API completeness for each definition?
   - Generality level appropriate?
   - Any one-off definitions that should be inlined or given API?

### T2: Present Understanding to User

```markdown
## Project Takeover: [directory name]

### What I Found
- N .lean files with M definitions, L lemmas/theorems
- X sorry declarations remaining
- K compilation errors

### Mathematical Content
[1-2 paragraph summary of what this project is about mathematically,
based on reading the code and any documentation]

### File Structure
| File | Defs | Lemmas | Sorries | Compiles? |
|------|------|--------|---------|-----------|
| Defs.lean | 5 | 12 | 0 | ✓ |
| Basic.lean | 0 | 8 | 3 | ✗ (depends on sorry) |
| Main.lean | 0 | 2 | 5 | ✗ |

### Quality Assessment
- Naming: [mostly good / needs fixes — list]
- Generality: [appropriate / could be more general — list]
- API completeness: [good / gaps — list]
- One-off definitions: [none / list ones that need API or inlining]
- Mathlib overlap: [none found / list definitions that duplicate mathlib]

### Questions for You
1. Is my understanding of the mathematical goal correct?
2. Are there references I should follow for the remaining proofs?
3. Any specific approach you want for [specific sorry]?
4. Should I generalize [specific definition] from X to Y?
```

### T3: Create Plan and Tickets

After the user confirms understanding:

1. Create `.mathlib-quality/plan.md` capturing the project state and goals
2. Create `.mathlib-quality/tickets.md` with tickets for:
   - Each remaining `sorry` (with proof approach if discernible)
   - Each quality issue found (naming, generality, API gaps)
   - CLEANUP tickets for files with quality issues
   - Any structural work needed (file splits, import cleanup)
3. Get user approval on the ticket board

### T4: Hand off to `/extended-work`

After ticket board approval, `/develop --takeover` is done. Tell the user:

```
Takeover plan ready. N tickets created from the existing code.
Run `/extended-work` to start working through them.
```

Same separation as the new-project flow: `/develop` plans, `/extended-work` executes.

---

## Phase 1: New Project Planning (the only phase — `/develop` is planning-only)

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

### [T002] Prove fooBar_comp
- **Status**: open
- **File**: MyProject/Basic.lean
- **Depends on**: T001
- **Parallel**: yes (after T001, parallel with T003)
- **Type**: lemma

#### Statement
```lean
theorem fooBar_comp {α β γ : Type*} [CommMonoid α] [CommMonoid β] [CommMonoid γ]
    (f : α → β) (g : β → γ) (s : Finset α) :
    fooBar s (g ∘ f) = fooBar (s.image f) g := by
  sorry
```

#### Proof sketch
Following [Lang2002], Theorem 5.1 in §3.5 (statement-side); the Lean proof is
straightforward once the right `Finset` lemmas are identified.

1. **Unfold `fooBar`** to expose the `Finset.prod` form. (Tactic: `simp only [fooBar]`
   or `unfold fooBar`.)
2. **Apply `Finset.prod_comp`** to push the composition `(g ∘ f) x = g (f x)` through
   the product, turning it into a product over `s.image f`.
3. The two sides now match definitionally; close with `rfl` or `simp`.

Off-script bridging tactics that may be needed: `Function.comp_apply` rewrite if step 2
doesn't fire automatically.

#### Mathlib lemmas needed
- `Finset.prod_comp` — distributes a product over a composition `Finset s (g ∘ f) = ∏ x in s.image f, g x` (verify: `lean_loogle "Finset.prod _ (_ ∘ _)"`)
- `Function.comp_apply` — definitional unfolding (`(g ∘ f) x = g (f x)`); usually fires via `simp`

#### Sources
- [Lang2002] Serge Lang, *Algebra* (3rd ed., Springer 2002, GTM 211). Theorem 5.1, §3.5
  pp. 144–145 — the categorical statement that products commute with reindexing.

#### Generality decision
- Stated over `[CommMonoid α/β/γ]` (the weakest setting in which the result holds — the
  product needs commutativity, no inverses needed).
- Universe-polymorphic in `α β γ` — `Type*` not `Type`.
- Not requiring `[Fintype α]` because we work over a fixed `Finset s` rather than the
  universe.

### [T001] Define FooBar and basic API
- **Status**: open
- **File**: MyProject/Defs.lean
- **Depends on**: none
- **Parallel**: yes (no dependencies)
- **Type**: def + API lemmas
- **Mathlib check**: Not in mathlib. Closest: `Mathlib.Algebra.Foo` (different shape — operates on `Multiset` not `Finset`).
- **Naming**: `FooBar` (UpperCamelCase def), `fooBar_zero` (snake_case lemma).

#### Statement
```lean
def fooBar {α : Type*} [CommMonoid α] (s : Finset α) (f : α → α) : α :=
  ∏ x ∈ s, f x

@[simp]
theorem fooBar_empty {α : Type*} [CommMonoid α] (f : α → α) :
    fooBar ∅ f = 1 := by sorry

@[simp]
theorem fooBar_singleton {α : Type*} [CommMonoid α] (a : α) (f : α → α) :
    fooBar {a} f = f a := by sorry

theorem fooBar_insert {α : Type*} [CommMonoid α] [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) (f : α → α) :
    fooBar (insert a s) f = f a * fooBar s f := by sorry
```

#### Proof sketch
- `fooBar_empty`: `simp [fooBar]` — `Finset.prod_empty` fires.
- `fooBar_singleton`: `simp [fooBar]` — `Finset.prod_singleton` fires.
- `fooBar_insert`: `simp [fooBar, Finset.prod_insert ha]` — the standard insert lemma.

#### Mathlib lemmas needed
- `Finset.prod_empty`, `Finset.prod_singleton`, `Finset.prod_insert` — all standard.

#### Sources
- (None — this is the basic API. The shape follows mathlib's `Finset.prod` convention.)

#### Generality decision
- `[CommMonoid α]`: the weakest typeclass that supports `∏`.
- `f : α → α`: deliberately self-mapping (the project's downstream applications need
  this; the more general `f : α → β` form lives in `Finset.prod` already).

### [CLEANUP-1] Run /cleanup on MyProject/Defs.lean
- **Status**: open
- **File**: MyProject/Defs.lean
- **Depends on**: T001
- **Parallel**: no (must wait for T001 to complete)
- **Type**: cleanup
- **Description**: Run /cleanup on Defs.lean to ensure mathlib quality before building
  on top. This is an algorithmically-inserted cleanup ticket per the cadence rule
  below (every 3 proof/def tickets per file → cleanup ticket).

### [T004] Main theorem
- **Status**: open
- **File**: MyProject/Main.lean
- **Depends on**: T002, T003, CLEANUP-1
- **Parallel**: no (needs all prerequisites)
- **Type**: theorem
- (... full Statement, Proof sketch, Mathlib lemmas, Sources, Generality block as above ...)
```

**Ticket rules — every proof/definition ticket MUST include:**

1. **Status / File / Depends on / Parallel / Type** — the metadata header (as before).
2. **Statement** — the full Lean statement of the declaration, including the type
   signature with all hypotheses, ending in `:= by sorry`. The `/extended-work` worker
   must be able to copy this verbatim into the file. **No abbreviations, no "etc."**
3. **Proof sketch** — a numbered list of steps. Each step names the *mathematical idea*
   ("Apply Cauchy's residue theorem"), the *tactical realisation* ("Use `Complex.residue`"),
   and any *bridging tactics* that may be needed. The sketch is detailed enough that the
   `/extended-work` worker doesn't need to think strategically — only execute.
4. **Mathlib lemmas needed** — every mathlib lemma the proof sketch references, by exact
   name. The planner verifies each name exists before writing the ticket (search via
   `lean_loogle`/`lean_leansearch`/`lean_local_search`). If a lemma isn't found in
   mathlib, the sketch must either provide an alternative path or flag the gap.
5. **Sources** — every paper/book cited in the proof sketch, with full bibliographic
   info. The planner reads the source (or asks the user) and extracts the relevant
   theorem.
6. **Generality decision** — explicit choice of typeclasses + universes + bundled-vs-
   unbundled hypotheses, with one-line reason. Defaults to maximum generality per
   `references/style-rules.md` § "Maximal Generalization of Theorems".

The point of this level of detail is **no mid-work pivots**. The user explicitly asked
for tickets detailed enough to avoid replanning due to unforeseen complications. If a
ticket lacks any of fields 2–6, `/extended-work` will refuse to start and report
"Ticket TXXX is not fully specified" — that's a planning bug, not a worker bug.

**Other ticket rules:**

- Every definition ticket includes its API lemmas (`_zero`, `_one`, `_singleton`,
  `_insert`, etc., as appropriate) — all in the **Statement** field with their own
  individual proof sketches.
- Cleanup tickets are inserted **algorithmically** (see "Cleanup cadence" below) — not by feel.
- Mark parallel opportunities explicitly.
- For sources: the planner is responsible for digging through the references the user
  provided in 1a/1b. If a reference is incomplete ("Section 3 of [Author]"), ask the
  user to supply the missing precision before writing tickets that depend on it.

#### Cleanup cadence (this is the rule, not a guideline)

Cleanup tickets get skipped when the rule is "every 3–5 proof tickets, insert a cleanup".
Use the deterministic procedure below instead.

Walk the proof/definition tickets in dependency order. For each file in the project, count
proof+definition tickets touching that file as you encounter them. Insert cleanup tickets
according to:

1. **Per-file cadence.** For every file, insert `[CLEANUP-<n>] Run /cleanup on <file>`
   after every **3rd** proof/definition ticket on that file. Depends on the most recent
   proof ticket on that file, blocks all later proof tickets on that file.
2. **Final per-file cleanup.** After the last proof ticket on each file, insert one final
   `[CLEANUP-<n>] Run /cleanup on <file>` ticket. Depends on the last proof ticket for
   that file.
3. **Project-wide cleanup before milestone tickets.** Before any "main theorem" or
   "milestone" ticket (i.e., a ticket the user marked as a project goal in 1d), insert a
   `[CLEANUP-ALL-<n>] Run /cleanup-all on the project so far` ticket. Depends on every
   open proof ticket; blocks the milestone.
4. **Final pass.** As the last ticket in the dependency graph, insert a single
   `[CLEANUP-FINAL] Run /cleanup-all on the whole project` ticket. Depends on every other
   ticket. The Phase-3 final review takes over from here.

**Worked example.** Suppose Defs.lean has 5 proof tickets (T001–T005), Basic.lean has
4 (T006–T009), and Main.lean has the milestone theorem T010:

```
T001  proof on Defs.lean         (Defs count: 1)
T002  proof on Defs.lean         (Defs count: 2)
T003  proof on Defs.lean         (Defs count: 3) → INSERT CLEANUP-1 (Defs.lean) after this
CLEANUP-1  cleanup Defs.lean     (depends on T003)
T004  proof on Defs.lean         (Defs count: 4, depends on CLEANUP-1)
T005  proof on Defs.lean         (Defs count: 5)
CLEANUP-2  cleanup Defs.lean     (final per-file, depends on T005)
T006  proof on Basic.lean        (Basic count: 1)
T007  proof on Basic.lean        (Basic count: 2)
T008  proof on Basic.lean        (Basic count: 3) → INSERT CLEANUP-3 (Basic.lean)
CLEANUP-3  cleanup Basic.lean    (depends on T008)
T009  proof on Basic.lean        (Basic count: 4, depends on CLEANUP-3)
CLEANUP-4  cleanup Basic.lean    (final per-file, depends on T009)
CLEANUP-ALL-1  /cleanup-all      (before milestone; depends on CLEANUP-2, CLEANUP-4)
T010  main theorem on Main.lean  (depends on CLEANUP-ALL-1)
CLEANUP-FINAL  /cleanup-all      (depends on T010)
```

**Verify before saving the ticket board.** Count: did you insert at least
`⌈total_proof_tickets / 3⌉` cleanup tickets, plus one final per-file cleanup per file?
If not, you skipped some — re-check.

In the Phase-1g ChatGPT validation request below, include "Cleanup tickets:
N (1 per ~3 proof tickets + 1 final per file + project-wide cleanups)" in the **Planned
Approach** section so ChatGPT can flag a planner that skipped them.

### 1g: Validate Plan with ChatGPT (if available)

Before showing the plan to the user, ask ChatGPT for a sanity check. Call
`ask_chatgpt_math` with a self-contained question:

```
I am planning a Lean 4 / Mathlib formalization project. Please review my plan
for mathematical soundness.

## Goal
[Main theorem statement in natural language AND in Lean]

## References
[Explicit list: paper titles, theorem/section numbers, textbook chapters]

## Planned Approach
[Dependency graph: which definitions, which lemmas, in what order]

## Key Decisions
- [Generality choices: e.g., "Stating over CommMonoid rather than CommRing because..."]
- [Definitions we plan to create vs. what we found in Mathlib]

## Questions
1. Is the overall proof strategy sound?
2. Are we missing any key intermediate lemmas?
3. Are our generality choices appropriate?
4. Do you see any issues with the dependency ordering?
```

If ChatGPT flags issues, revise the plan before presenting to the user.
Note any ChatGPT suggestions in the plan for transparency.

### 1h: Get User Approval

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

After the user approves, **`/develop` is done.** It does not execute the plan.

---

## End of `/develop` — what happens next

`/develop` is **planning-only**. After the ticket board is approved:

- **To start working tickets**: invoke `/extended-work` (single-ticket focused work session
  that picks the next available ticket and works it to completion or concrete approach
  error). See `commands/extended-work.md`.
- **To check progress**: `/develop --status` prints the current ticket board.
- **When all tickets are done**: invoke `/pre-submit` for the final-review checklist
  (`lake build` clean, no `sorry`, no new axioms, etc.). The "Phase 3 Review & Iterate"
  step that used to live in `/develop` is now `/pre-submit`'s job.

The split is deliberate. `/develop` does the strategic thinking — searches mathlib,
designs the API, drafts the proof sketches from the user's references, makes generality
decisions. `/extended-work` does the tactical implementation — states the declaration,
calls the planned mathlib lemmas, iterates to compilation. This separation prevents the
"agent reconsiders the whole approach mid-proof" failure mode that motivated the
detailed-tickets requirement (see Phase 1f's "Ticket rules").

Tickets are written to be **complete and self-contained** so a worker doesn't need to
think strategically — only execute. If a `/extended-work` worker finds the plan is
genuinely wrong (proof-sketch failure, mathlib gap, scope/definition error per the stop
conditions in `extended-work.md`), it stops with a concrete report and the user
re-invokes `/develop` to replan.

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

### 4. No Placeholders, No New Axioms

**Never leave `sorry` as a placeholder.** Every declaration must be fully proved
before a ticket is marked done. If you can't prove something:
- Escalate by adding tickets (Principle 5)
- Mark the ticket as `blocked` with a clear reason
- Do NOT leave `sorry` in committed code

**Never introduce new axioms.** This means:
- No `axiom` declarations
- No `constant` declarations (these are axioms in disguise)
- No `Decidable.em` unless the proof genuinely requires classical logic
  and is in a file that already uses it
- No `sorry` — this is an axiom (`sorryAx`)
- No `native_decide` on propositions that aren't actually decidable

**Enforcement:** After every `lake build`, run `#print axioms mainTheorem` on
each key theorem. The only acceptable axioms are:
- `propext` (propositional extensionality)
- `Quot.sound` (quotient soundness)
- `Classical.choice` (if the proof genuinely needs classical logic)

If ANY other axiom appears (especially `sorryAx`), the ticket is NOT done.

### 5. Tickets that prove insufficient on contact with reality

If a `/extended-work` worker hits a hard-stop condition (proof-sketch failure, mathlib
gap, scope/definition error per `extended-work.md`), the worker reports the failure and
stops. The user then re-invokes `/develop --continue`, which runs the resume-mode audit
(R1–R5) — this is when the plan gets repaired:

1. **Do NOT take shortcuts** in repair (e.g., dropping a hypothesis we don't have, adding
   a `sorry`, specializing to a concrete type). The fix has to be a real plan.
2. **Update the ticket board** — modify the failed ticket, add new tickets if the work
   genuinely decomposed into more pieces than expected, mark dependencies, identify
   parallel opportunities.
3. **Re-run the cleanup-cadence check on the new tickets.** Adding N new proof tickets to
   a file may push it over the 3-ticket-since-last-cleanup threshold; if so, insert a
   cleanup ticket for that file as a dependency before any of the new tickets. Use the
   per-file cadence rule from §1f. This is the most common path by which cleanup tickets
   get skipped — new tickets get added during the resume audit without re-running the
   cadence rule.
4. Once the board is updated and re-approved, the user runs `/extended-work` again to
   continue.

### 6. Periodic Cleanup (this is the rule, see §1f for the algorithm)

Cleanup tickets are inserted **algorithmically** at planning time (§1f), re-checked at
each `/extended-work` ticket pickup, and re-checked again whenever new tickets are added
during a `/develop --continue` resume (§5 step 3 above). The cadence is:
- **Per-file**: cleanup ticket every 3 proof tickets touching that file
- **Final per-file**: one cleanup ticket after the last proof ticket on each file
- **Pre-milestone**: `/cleanup-all` ticket before any user-marked milestone theorem
- **Final**: one `[CLEANUP-FINAL] /cleanup-all` ticket as the last item in the graph

They ensure:
- Code stays at mathlib quality throughout development
- Naming issues are caught early
- Proofs are golfed before being built upon
- API gaps are identified while context is fresh

If you find yourself doing 3+ proof tickets without a cleanup, the cadence check has
been skipped. Stop and add the missing cleanup ticket before proceeding.

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
