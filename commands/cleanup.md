---
name: cleanup
description: Full file cleanup to mathlib standards (style audit + golf, methodical, no skipping)
---

# /cleanup — Style Audit + Cleanup + Golf

Run a full mathlib-quality pass on a Lean file. Absorbs what used to be `/check-style`:
the audit phase first, then methodical fixes, then per-declaration deep golf.

**This command is slow on purpose.** Workers must take as long as they need. Nothing is
skipped. Every rule is checked, every declaration is processed, every golfing technique is
tried. "I'll come back to this" is forbidden — every audit item gets a concrete action or a
documented "n/a: <reason>".

## Usage

```
/cleanup [file_path]                -- whole file (the standard mode)
/cleanup [file_path] [decl_name]    -- single declaration only
```

---

## Mode A: Single Declaration

Skip the file-wide phases. Run Phase 4 (per-declaration deep cleanup) on just `decl_name`.

1. Read the file, find the declaration.
2. Run `lean_diagnostic_messages` and capture warnings on those lines.
3. Dispatch the worker agent for that declaration (Phase 4 worker prompt below). The worker
   MUST read `golfing-rules.md` and `proof-patterns.md` in full as its first step.
4. Verify compilation.
5. Print before/after report.

---

## Mode B: Whole File (the standard mode)

Nine phases. **Do them in order. Do not skip phases.**

```
PHASE 0  DOCTOR                   pre-flight: baseline must be green
PHASE 1  PREPARE                  collect context
PHASE 2  STYLE AUDIT              full punch-list, no fixes yet
PHASE 3  FILE-LEVEL FIXES         work the file-level items from the punch-list
PHASE 4  PER-DECLARATION GOLF     one worker per declaration, full audit + full golf + diff gates
PHASE 5  REFACTORING              cross-declaration changes from worker reports
PHASE 6  FINAL VERIFICATION       file-level gates + cumulative checks
PHASE 6.5 SIMPLIFY                hand off to the built-in /simplify skill for a holistic review pass
PHASE 7  REPORT                   one consolidated report
```

---

## PHASE 0 — Doctor (pre-flight baseline)

The Doctor establishes a known-good baseline. Without it, /cleanup can't tell what
breakage it introduced versus what was already there. **If the baseline is broken, abort
unless the user explicitly says to proceed anyway.**

Reference: `skills/mathlib-quality/references/cleanup-gates.md` § "Pre-flight doctor".

### 0a. Cache + project build

```bash
lake exe cache get   # optional, ignore failure
lake build           # required to be clean
```

If `lake build` fails:
- Print the failure output.
- Print: `BASELINE BROKEN — /cleanup will not start. Fix the build first, or re-run with
  --skip-baseline-build to acknowledge the existing breakage and proceed anyway.`
- Exit Phase 0; do not continue.

### 0b. LSP responsive on the target file

```
lean_diagnostic_messages(file_path=<file>)
```

Must return without error (warnings are fine; we'll handle those in Phase 2). If LSP
times out or errors, abort: real errors during workers will be masked.

### 0c. Optional: linter on the target file

```bash
lake exe runLinter <module>   # if available in the project
```

The output is informational — feeds Phase 2 as an extra source of issues. Linter
warnings don't abort Phase 0.

### 0d. Print the baseline block (REQUIRED ARTIFACT)

```
### Baseline (Phase 0)

[1] lake exe cache get          <ran / skipped (no cache) / failed (continued)>
[2] lake build                   <pass / FAIL — aborted>
[3] LSP on <file>                <responsive / FAIL — aborted>
[4] runLinter <module>           <pass / N warnings — feeding to Phase 2 / n/a>
```

This block goes into the final report so the user knows what the baseline was.

---

## PHASE 1 — Prepare (Main agent)

### 1a. Read the file in full

`Read [file_path]` with no limit. You need to see the whole thing.

### 1b. Collect Lean diagnostics

```
lean_diagnostic_messages(file_path=[file_path])
```

Group warnings by line number and keep the full list available for later phases. These are
authoritative — they're the same warnings VS Code shows as yellow underlines.

### 1c. Read the four reference docs

You will not memorise them; you will *consult* them in Phases 2–4. Read them now so they
are in working memory:

- `skills/mathlib-quality/references/style-rules.md`
- `skills/mathlib-quality/references/naming-conventions.md`
- `skills/mathlib-quality/references/golfing-rules.md`
- `skills/mathlib-quality/references/proof-patterns.md`

If a phase below conflicts with these references, the references win.

### 1d. Build the declaration list

List every `def`/`lemma`/`theorem`/`structure`/`instance`/`abbrev` with line numbers and proof
length. You'll iterate over this list in Phase 4.

```
1. def myFoo                      lines 25–35  (10 lines)
2. lemma bar_thing                lines 40–52  (12 lines)
3. theorem main_result            lines 65–130 (65 lines)  ← long, watch for STRUCTURE
...
```

---

## PHASE 2 — Style Audit (Main agent, no fixes yet)

**Do not edit the file in this phase.** Build a complete numbered punch-list. Every item below
must be checked. Items that don't apply are explicitly recorded as "OK" or "n/a", not omitted.

The punch-list output goes into the conversation as a markdown section like:

```
## Style Audit Punch-List for [file_path]

### File-level (A.x)
A.1  COPYRIGHT — present, authors line OK
A.2  MODULE DOCSTRING — MISSING (will create in 3.2)
A.3  IMPORTS — out of order: `Mathlib.Topology.Basic` after `Mathlib.Data.Set.Basic`
A.4  SUBSECTION DIVIDERS — 3 found at L42, L91, L156 (will strip in 3.3)
A.5  FILE LENGTH — 740 lines (OK; <1000)
A.6  FILE-LEVEL SET_OPTION — `set_option maxHeartbeats 400000 in` at L33 (will remove in 3.5)
A.7  MECHANICAL — `λ` ×4 (L60, L91, L102, L201); `$` ×2 (L88, L155); `push_neg at h` ×3 (will batch in 3.6)

### Linter findings (B.x)
B.1  L45  unusedVariables — `hp0`
B.2  L78  style.longLine — 112 chars
B.3  L123 docBlame — `importantDef` lacks docstring
...

### Per-declaration scan (C.x — light scan only, deep audit in Phase 4)
C.1  `myFoo` (def, L25)
     - NAMING: OK (lowerCamelCase)
     - VISIBILITY: should this be private? not used outside this file → make private
     - DOCSTRING: present, public def → OK
     - JUNK DEF: 4 use sites, has _apply lemma → OK
C.2  `bar_thing` (lemma, L40)
     - NAMING: OK
     - DOCSTRING: missing on private/aux → OK (private has no docstring)
     - LENGTH: 12 lines → OK
C.3  `main_result` (theorem, L65)
     - NAMING: OK
     - DOCSTRING: missing — public theorem MUST have one (will add in 4)
     - LENGTH: 65 lines → STRUCTURE: decompose in 4 (or flag for /decompose-proof)
     - FORBIDDEN ABBREV in name: `wt_*` — rename to `weight_*` (refactoring item)
...

### Total items in punch-list: 23
```

### What every audit must check

#### A. File-level audit

| Tag | Check | What to record |
|---|---|---|
| **A.1 COPYRIGHT** | First few lines: `Copyright (c) YYYY Author. All rights reserved.` / `Released under Apache 2.0...` / `Authors: ...` | OK or what's wrong |
| **A.2 MODULE DOCSTRING** | `/-! # Title ... -/` *immediately* after imports? | Present, or **MISSING (will create in 3.2)** |
| **A.3 IMPORTS** | Mathlib first, alphabetical within groups, no obvious unused imports | OK or list of issues |
| **A.4 SUBSECTION DIVIDERS** | `/-! ##` or `/-! ###` *inside* the file body (below the top docstring) | List every line |
| **A.5 FILE LENGTH** | `wc -l` on the file. <1000 OK, ≥1000 flag for `/split-file` | Line count + verdict |
| **A.6 FILE-LEVEL SET_OPTION** | `set_option maxHeartbeats`, `set_option maxRecDepth`, debug `set_option trace.*`, etc. | List every line |
| **A.7 MECHANICAL** | Count of `λ` (vs `fun`), `$` (vs `<|`), `push_neg` (deprecated → `push Not`) | Counts + line numbers |

#### B. Linter findings

Take every warning from `lean_diagnostic_messages`. List each with line number and short
description. Don't filter — the linter is authoritative.

#### C. Per-declaration light scan

For each declaration in the list from 1d, do a *light* scan only (deep audit happens in
Phase 4). Record:

- **NAMING**: lemma/theorem → snake_case; def returning data → lowerCamelCase; structure/inductive → UpperCamelCase. Forbidden abbreviations: `whomog`, `mvpoly`, `wt`, `soln`, `imp`, `eqn`, `thm`. American English.
- **VISIBILITY**: only-used-in-file → should be private; helper → should be private + `_aux`.
- **DOCSTRING (presence)**: public theorem/def with no docstring → CREATE a 1-sentence one in Phase 4. Private/aux WITH a docstring → STRIP.
- **LENGTH**: >30 lines flags STRUCTURE; >50 lines flags `/decompose-proof`.
- **JUNK DEF** (for `def`s only): is this `def foo : T := value` with no `_apply`/`_def` lemmas and used outside one local proof? If no API and ≤1 use site → INLINE (refactoring item).
- **EXISTS LEMMA**: private single-use `∃`-lemma whose body is `⟨witness, rfl, ...⟩`? → INLINE (refactoring item).

This is a *scan*, not a deep audit. Phase 4 does the full per-declaration audit.

### Output of Phase 2

A single punch-list as shown above. Do not start fixing. Print the punch-list and continue
to Phase 3.

---

## PHASE 3 — File-Level Fixes (Main agent)

Work the file-level items (A.x) from the punch-list. Per-declaration items (C.x) wait for
Phase 4.

**Order matters.** Do steps in this order:

### 3.1 Copyright header

Fix only if A.1 reported issues. Don't invent author names — if the header is missing
authors, ask the user before guessing.

### 3.2 Module docstring — CREATE if missing

**This is the item that gets forgotten most.** If A.2 reported MISSING, you MUST create one
now. No excuses.

Format:

```lean
/-!
# <Title>

<1–3 sentences describing what this file contains.>

## Main definitions

* `<defName>`: <what it is>

## Main results

* `<theorem_name>`: <what it proves>

## References

* (optional, only if the file cites a paper/book)
-/
```

How to write it without guessing:
1. Read the namespace at the top of the file → that's a hint at the title.
2. List the public `def`s → those become the "Main definitions" bullets.
3. List the public theorems with `_main`/`_thm` -ish names or that other files might import → those are the "Main results" bullets.
4. The opening sentence describes the *subject*, not the proof technique.

If the file is genuinely a grab-bag with no clear theme, that's a signal for `/split-file`,
but write a docstring anyway: "This file collects miscellaneous results about X." is fine.

### 3.3 Strip subsection dividers

Every `/-! ## ... -/` and `/-! ### ... -/` *below* the top module docstring is rejected by
review. Delete them — both the comment and the leading/trailing blank line that hugged it.

Only the top-of-file `/-!` block survives.

### 3.4 Imports

Reorder: Mathlib first (alphabetical), then project imports (alphabetical), with one blank
line between groups. One import per line. Don't speculatively delete imports here — wait
for the linter to flag unused ones in Phase 6.

### 3.5 File-level `set_option`

Delete every `set_option maxHeartbeats`, `set_option maxRecDepth`, and any debug
`set_option trace.*`. After deletion, run `lean_diagnostic_messages`:

- If the file still compiles: done.
- If proofs now time out: those proofs need fixing in Phase 4 (extract helpers, golf,
  use `grind`). The `set_option` line stays deleted regardless. Flag the affected
  declarations as "needs heartbeat fix" in the per-decl punch-list.

`set_option linter.* false in` for legitimate suppressions is allowed but rare — keep only
when there's a real reason.

### 3.6 Batch mechanical replacements

**Do all in one pass with `Edit` `replace_all: true`.** The Lean LSP rebuilds between edits
and can revert pending changes if you intersperse diagnostics.

Order:
1. `λ` → `fun` (preserve trailing space)
2. `$ ` → `<| ` (be careful — `$` only in expression context; if any doc strings or string
   literals contain `$`, use a more specific pattern)
3. `push_neg at h` → `push Not at h` (and `push_neg ` standalone → `push Not `)

After all three, run `lean_diagnostic_messages` ONCE and fix any breakage from the
replacements (e.g., a `$` that was actually inside a string).

### 3.7 What is NOT a mechanical replacement

`show` vs `change` is per-occurrence in Phase 4, not here. Each `show T` in tactic mode
needs a decision:

- If subsequent tactics rewrite the goal → replace with `change T` (`linter.style.show` enforces this).
- If `show T` is redundant (goal already T, line is just an annotation) → delete the line.
- If `show T from by tac` → `show T by tac` (drop redundant `from`).
- If `show T` is in term mode → leave it.

Don't `replace_all` `show → change`; it will mis-fire.

### 3.8 Verify

Run `lean_diagnostic_messages`. The file should still compile. Phase-2 linter findings (B.x)
that turned out to be `λ` / `$` / `push_neg` are now resolved; the rest are addressed in
Phase 4 per declaration.

---

## PHASE 4 — Per-Declaration Deep Cleanup (one worker per declaration)

**One declaration per agent.** Each declaration gets its own worker via the `Agent` tool with
`subagent_type="general-purpose"`. Multiple workers can run in parallel if the declarations
don't depend on each other (read each other's helpers).

**The worker prompt below is verbatim. Copy it as-is into every `Agent` call.**
Do not abbreviate or summarise — the worker won't read external files reliably, so the rules
have to be in the prompt.

### Worker Agent Prompt

````
You are cleaning up a SINGLE Lean 4 declaration in [file_path]: `decl_name` at lines N–M.

This is your ONLY job. You may take as long as you need. The user has explicitly said
"no excuses, no skipping" — every rule below MUST be checked, every applicable golfing
technique MUST be tried.

The lint warnings for this file are:
[paste lint warnings from Phase 1b]

The Phase-2 punch-list items for this declaration are:
[paste C.x items for this decl]

## Step 1 — Read the reference docs IN FULL

Before you make any edit, read these files completely (with `Read`, no offset/limit):
1. skills/mathlib-quality/references/golfing-rules.md
2. skills/mathlib-quality/references/proof-patterns.md
3. skills/mathlib-quality/references/mathlib-search.md (five-method search + six strict rules + common-equivalents table — needed for the MATHLIB audit and the search-status block)
4. skills/mathlib-quality/references/generalisation-patterns.md (typeclass-weakening catalogue + drop-test + pointwise/strict→weak — needed for the GENERALISE audit and the generalisation-status block in Step 2.6)
5. skills/mathlib-quality/references/cleanup-gates.md (definition_protected, theorem_statement_protected, lake_build_file, etc. — needed for Step 5b worker gates)
6. skills/mathlib-quality/references/style-rules.md (sections relevant to your declaration)
7. skills/mathlib-quality/references/naming-conventions.md (if NAMING came up in C.x)

In your first response, confirm: "I have read golfing-rules.md, proof-patterns.md,
mathlib-search.md, generalisation-patterns.md, and cleanup-gates.md." If you skip this step,
the rest of the work is invalid.

## Step 2 — Print the FULL audit report

Every item below MUST have a concrete answer. No "I'll come back to this." No "looks fine."
If an item doesn't apply, write `n/a: <one-sentence reason>`. If it does, write the action.

```
### Auditing: `decl_name` (lines N–M, K lines)

 1. LINT          [warnings from diagnostics for this range, or "none"]
 2. HAVE SCAN     [list EVERY have — see procedure below]
 3. SET_OPTION    [any per-declaration `set_option`? must remove]
 4. SIMP SQUEEZE  [each simp call: bare? non-terminal? badly-formatted simp only?]
 5. NAMING        [snake_case/camelCase/UpperCamelCase as appropriate;
                   forbidden abbreviations: whomog, mvpoly, wt, soln, imp, eqn, thm]
 6. LINE PACKING  [signature breaks too early? use #check as width reference]
 7. BY PLACEMENT  [`by` at end of line, never alone]
 8. FORMAT        [2-space indent; no empty lines inside; one tactic per line;
                   merge sequential `rw [a]; rw [b]` → `rw [a, b]`]
 9. COMMENTS      [strip ALL narrative `--` inside the proof]
10. DOCSTRING     [public theorem/def → 1-sentence; private/aux → none;
                   if missing on public, CREATE one — do not skip]
11. VISIBILITY    [only-used-in-file → private; helper → private + _aux]
12. STRUCTURE     [proof length, ∧ in statement, branches >10 lines]
13. MATHLIB       [print the five-method search-status block — see Step 2.5 below]
14. JUNK DEF      [n/a unless decl is a `def`; if so, has API? used >1 place? if not → inline]
15. EXISTS LEMMA  [n/a unless private single-use ∃-lemma `:= ⟨_, rfl, …⟩` → inline]
16. SHOW vs CHANGE [each `show T` in tactic mode: → `change`, drop, or leave (term-mode)]
17. PUSH_NEG      [any remaining `push_neg`? → `push Not at h` (deprecated)]
18. GENERALISE    [required: print the generalisation-status block — see Step 2.6 below.
                   Run the mechanical-weakening pass on EVERY hypothesis. Big-change
                   candidates are flagged for Phase 5, not done here.]

Issues to fix: [numbered list — every item has a concrete action]
Refactoring needed: [cross-declaration changes; fed back to main agent for Phase 5.
                     Includes: big-change generalisation candidates flagged at item 18.]
```

### HAVE SCAN procedure

For every `have` in the proof body:

| Pattern | Has `by`? | Use count | Action |
|---|---|---|---|
| `have h := expr` | NO | 1 | INLINE — substitute expr at the use site, delete the line |
| `have h : T := expr` | NO | 1 | INLINE — same, with type ascription if needed |
| `have h := expr` | NO | 2+ | KEEP |
| `have h := by tac` | YES | any | KEEP (proof content) |
| `have h : T := by tac` | YES | any | KEEP |

Output format for the audit:
```
2. HAVE SCAN:
   - L52  `have h1 := lemma1 x`              no by, used 1× at L55         → INLINE
   - L53  `have h2 : T := foo y`             no by, used 1× at L58         → INLINE
   - L55  `have h3 := by linarith`           has by                        → KEEP
   - L60  `have h4 := baz z`                 no by, used 2× at L62, L65    → KEEP
```

### SIMP SQUEEZE procedure

For every `simp` / `simp only [...]`:

- **Bare `simp`, terminal (closes the goal):** leave as `simp`. Do not squeeze.
  Optionally try `grind` or `simp_all` if shorter.
- **Bare `simp`, non-terminal:** must squeeze.
  1. Edit: replace `simp` with `simp?`.
  2. `lean_diagnostic_messages`. Look for `Try this: simp only [...]`.
  3. Replace `simp?` with the suggestion exactly (Lean's formatting is what we want).
- **Existing `simp only [...]`, terminal:** unsqueeze to bare `simp` (mathlib convention: don't squeeze terminal simp).
- **Existing `simp only [...]`, non-terminal but badly formatted:** redo via `simp?` to get correct formatting.

### LINE PACKING procedure

Fill lines to ~100 chars. Do NOT break at 50–60 chars when there's room.

Use `#check @decl_name` to see how Lean formats the type — your declaration syntax should be
equally compact.

```lean
-- BAD (~40 chars/line)
theorem foo
    (S : Finset α)
    (hS : ∀ p ∈ S, P p) :
    Q := by

-- GOOD (~100 chars/line)
theorem foo (S : Finset α) (hS : ∀ p ∈ S, P p) :
    Q := by
```

### SET_OPTION procedure

Per-declaration `set_option maxHeartbeats X in` (or `maxRecDepth`) is unacceptable.

1. Delete the `set_option` line.
2. `lean_diagnostic_messages`. If proof still compiles: done.
3. If it now times out, in this order:
   a. Try `grind` / `grind [hints]` (use `lean_multi_attempt`).
   b. Inline single-use `have`s and apply other golfing rules — proof shrinks, heartbeats drop.
   c. Extract the largest `have ... := by ...` blocks (>8 lines) as private helpers above
      this theorem. Splitting elaboration work usually fits within default heartbeats.
   d. If STILL timing out: report `Refactoring needed: /decompose-proof on decl_name`.
      The `set_option` line stays deleted. No exceptions.

### STRUCTURE procedure (attempt fixes — never just flag)

- **Proof >30 lines after golfing**: extract the largest `have ... := by` blocks as private
  helpers with mathematically meaningful names (not `_aux1`, `_aux2`).
- **`∧` in theorem statement**: split into `foo_left` and `foo_right`, recombine.
- **Branch >10 lines** (`constructor`, `by_cases`, `rcases`): each branch becomes a private helper.

If after honest attempts the proof is still >50 lines, report `Refactoring needed:
/decompose-proof on decl_name`.

## Step 2.5 — Mathlib search-status block (REQUIRED for item 13)

Item 13 in the audit is the mathlib check. It is not a one-line answer — it is a five-method
search. Print the block below for this declaration. Skipping any method is a defect; "didn't
think it was in mathlib" is not an exemption.

The five methods, the six strict rules, and the common-equivalents lookup table all live
in `references/mathlib-search.md`, which you read in Step 1.

```
### Mathlib search-status: `decl_name`

[A] Lean-Finder       <queries tried>            <hits / no hits / n/a: reason>
[B] Loogle            <queries tried>            <hits / no hits / n/a: reason>
[C] LeanSearch        <queries tried>            <hits / no hits / n/a: reason>
[D] Grep mathlib src  <terms tried>              <hits / no hits / n/a: reason>
[E] Name pattern      <terms via lean_local_search> <hits / no hits / n/a: reason>

Auxiliary-lemma variants tried (per Rule 3): <list, e.g., `.of_subset`, `_left`, `foo_of_bar`>
Common-equivalents lookup matched: <"yes — discrete/finite bucket: …" | "no">

Concluded: <one of:>
  - "found in mathlib as <full qualified name>; ACTION: delete this declaration, update
     N call sites to use mathlib directly"
  - "found in mathlib as <name> but more general; ACTION: delete local, specialize mathlib
     where called"
  - "found a partial match (<name>); ACTION: keep local but build on mathlib via …"
  - "not in mathlib (all 5 methods exhausted, plus auxiliary-variant search); ACTION:
     keep, consider future mathlib PR"
```

If the conclusion is one of the "found" cases, the corresponding `delete / specialize /
build on mathlib` action goes in the "Refactoring needed" section of your report so the
main agent picks it up in Phase 5.

The six strict rules from `mathlib-search.md` apply to whatever action you choose:
- **No wrapper lemmas** — if you would replace a wrapper that just chains 1–3 mathlib
  calls, delete it; don't simplify it.
- **No custom predicates if a type class exists** — `[DiscreteTopology S]` over
  `(h : ∀ s ∈ S, …)`.
- **Delete, don't simplify** — when you find a match, the local declaration goes; call sites
  use mathlib directly.
- (See the reference doc for the rest.)

## Step 2.6 — Generalisation status block (REQUIRED for item 18)

This is the inline mechanical-weakening pass on the declaration's hypotheses. It runs the
same mechanical phases as the standalone `/generalise` command (its Phases 2–4) but on
just this one declaration. Skipping any hypothesis is a defect.

You read `generalisation-patterns.md` in Step 1. Use the catalogue to generate weakening
candidates for every hypothesis.

### 2.6a. Per-hypothesis status table (REQUIRED ARTIFACT)

For every parameter on the declaration (`(h : P)`, `[Foo X]`, `{x : α}`, `(x : α)`),
fill in this table:

```
### Generalisation status: `decl_name`

| # | Hypothesis           | Class       | Used as                         | Mechanical candidates tried       | Verified? | Result                              |
|---|----------------------|-------------|---------------------------------|-----------------------------------|-----------|-------------------------------------|
| 1 | [CommRing R]         | typeclass   | mul_comm at L42, ring at L48    | [Ring R]; [CommSemiring R]        | yes       | ✗ both reverted — `mul_comm` needed |
| 2 | (x : R)              | structure value | passed through                | n/a — type follows R              | n/a       | n/a                                 |
| 3 | (h : 0 < x)          | proposition | strict at L46                   | (h : 0 ≤ x)                       | yes       | ✗ reverted — strict needed          |
| 4 | (h2 : Polynomial.IsMonic p) | proposition | .leadingCoeff_eq_one at L43 | drop; (h2 : p.leadingCoeff = 1) | yes       | ✗ drop reverted; alt-form compiles → SMALL change applied |
| 5 | [DecidableEq R]      | decidability| (none found)                    | drop                              | yes       | ✓ dropped — kept                    |
| 6 | (universe `Type`)    | universe    | n/a                             | Type → Type*                      | yes       | ✓ generalised — kept                |
```

The classes follow `generalisation-patterns.md`: typeclass, proposition, structure-value,
type-variable, decidability. Each row's "Mechanical candidates tried" must list every
catalogue entry that *could* apply (drop-test, typeclass parents, point-localise variants,
strict→weak forms, universe poly). A row that says only "n/a" must include a one-sentence
reason. Hypotheses missing from the table = audit defect.

### 2.6b. Candidate verification

For each candidate that's marked "yes" in **Verified?**, the procedure was:
1. Apply the substitution.
2. Run `lean_diagnostic_messages` on the file.
3. If clean → keep (Result: ✓ ... → kept). If errors → revert (Result: ✗ reverted, with the
   line that triggered).

Multiple weakenings on the same hypothesis are tried in catalogue order: weakest first.
The result kept is the *weakest* one that compiles.

### 2.6c. Big-change candidates (flag for Phase 5)

After mechanical pass, list any big-change candidates the worker noticed but should NOT
apply inline. These get flagged in `Refactoring needed:` for Phase 5 to escalate to a
full `/generalise` invocation (which has the literature search + user approval gate).

A change is "big" — and therefore goes into the flagged list, not into the inline result —
if ANY of the following hold:

- It would change the declaration name (e.g., dropping a `_real` prefix).
- It would change argument order, or convert an explicit argument to instance / vice versa.
- It would restate the conclusion (e.g., `=` to `Iff`, single fact → conjunction).
- It would touch an existing `@[simp]` / `@[ext]` / `@[fun_prop]` / `@[grind]` normal form.
- It would require restating the lemma over a different abstract structure (`ℝ` →
  `LinearOrderedField` / `RCLike`; `ℕ`-indexed → `Fintype`-indexed).
- The decl is `public` AND the change alters its call signature in a way that would
  affect call sites in other files (typeclass-arg weakenings that compile cleanly under
  typeclass resolution don't count — instance args are filled by resolution, not callers).

Output format:

```
Big-change candidates (flag for /generalise full mode in Phase 5):
- Generalise `(x : ℝ)` → `{K : Type*} [LinearOrderedField K] (x : K)` —
  literature suggests max generality is ordered fields; 4 call sites in this project,
  all currently compile-clean under the generalised form (verified diagnostics in 2.6b).
  Why deferred: public-API restatement, user approval needed.
- Drop `IsMonic p` per [literature finding] — restates conclusion with `leadingCoeff ≠ 0`,
  may want rename to `<lemma>_of_leadingCoeff_ne_zero`. Why deferred: rename + restating.

(or "none" if none)
```

### 2.6d. Literature search (REQUIRED for public decls)

For *public* declarations, the inline mechanical pass is not enough — the user has
explicitly required a literature search (this is the same requirement as in the standalone
`/generalise` command's Phase 5). Run:

- **WebSearch** for "<theorem keywords> generalization", nLab/Stacks/Wikipedia for the
  canonical formulation. Capture top 3 hits per query.
- **mcp__chatgpt-math** if available, asking "what's the most general known statement
  of <theorem in plain math English>? My current hypotheses are <list>. Are any
  unnecessary in the literature?"

Required artifact:

```
### Literature search status: `decl_name`

[A] WebSearch                queries: <list>          findings: <summary or "none">
[B] ChatGPT (math MCP)       asked? yes / n/a: <reason>   key insight: <…>

Literature-driven big-change candidates (added to Phase-5 flag list above):
- <e.g., "drop IsMonic per [Mumford 1966, §4]">
- ...
```

For **private/aux** decls: literature search is skipped per scope rule. Record `n/a:
private decl, literature search not required`. Mechanical pass (2.6a–2.6c) still runs.

### 2.6e. Apply small-safe results

Any "✓ ... → kept" result from 2.6a is a small-safe change that has already been verified
diagnostics-clean. It stays applied; record it in your Phase 4 worker report as a
generalisation success.

### 2.6f. Why this runs inline (not deferred to /generalise)

If left to "the worker notices and flags it", the cadence skips. The user has explicitly
required: "should not rely on the agent noticing anything since they'll just skip this
otherwise." So: every Phase 4 worker runs 2.6a–2.6e on its declaration, every time. The
status table is the artifact that makes skipping detectable. Big-change candidates that
need the full `/generalise` literature-search-plus-user-approval flow are flagged for
Phase 5 — but the **mechanical pass and (for public decls) the literature search are
inline-required, not optional.**

## Step 3 — Apply EVERY golfing rule (with status reporting)

You read `golfing-rules.md` in Step 1. Now go through it section by section and report
status for EVERY rule. Use this output format:

```
### Golfing rule pass

Phase 1 (instant wins):
  [1.1]  by exact wrapper          applied at L48: `:= by exact h_step` → `:= h_step`
  [1.2]  by rfl                    n/a (no `by rfl`)
  [1.3]  rw + exact                applied at L52: `rw [h]; exact e` → `rwa [h]`
  [1.4]  simp + exact → simpa      applied at L55
  [1.5]  trailing rfl after simp   n/a
  [1.6]  constructor + exact + exact → ⟨ ⟩    applied at L60
  [1.7]  apply + exact             n/a
  [1.8]  by_contra + push_neg → by_contra!   n/a
  [1.9]  eta-reduce lambdas        applied at L61: `fun x => f x` → `f`
  [1.10] inline single-use have    applied at L65–L66 (h2)
  [1.11] apply + intro → refine + fun        n/a
  [1.12] redundant show            removed L70
  [1.13] have + .1/.2 → obtain     applied at L72–L75
  [1.14] merge consecutive rw      applied at L77 (rw [a]; rw [b] → rw [a, b])
  [1.15] unsqueeze terminal simp only        n/a (no terminal simp only)
  [1.16] squeeze nonterminal bare simp       applied at L80 (used simp?)
  [1.17] dot notation              applied at L82: `Monotone.comp hf hg` → `hf.comp hg`
  [1.18] use <| over ()            applied at L85
  [1.19] push_neg → push Not       n/a (none left after Phase 3.6)
  [1.20] inline trivial single-use ∃-lemma   n/a (this isn't an ∃-lemma)

Phase 2 (automation upgrades — try each, keep if compiles):
  [2.1]  grind on whole proof      tried via lean_multi_attempt — failed: `unsolved goal: …`
  [2.2]  delete tactics before grind         n/a (no grind in proof)
  [2.3]  simpa consolidation       applied at L88
  [2.4]  fun_prop                  n/a (no Continuous/Differentiable goal)
  [2.5]  positivity                tried at L92 — succeeded, replaced 3-line linarith block
  [2.6]  gcongr                    n/a
  [2.7]  omega / lia               applied at L100: `linarith` → `omega`
  [2.8]  aesop                     tried — failed
  [2.9]  norm_num / norm_cast      n/a
  [2.10] decide / decide +kernel   n/a
  [2.11] field_simp; ring          n/a
  [2.12] linear_combination        tried at L105 — failed
  [2.13] wlog for symmetric cases  n/a
  [2.14] collapse 2-step calc      n/a (not a calc)
  [2.15] close multiple goals with <;>       applied at L110

Phase 3 (cleanup):
  [3.1]  erw → rw                  n/a
  [3.2]  continuity/measurability → fun_prop  n/a
  [3.3]  omega → lia               applied at L100 (already in 2.7)
  [3.4]  rcases ... with rfl auto-substitutes n/a
  [3.5]  register lemmas for automation       n/a (this is a one-off proof)
  [3.6]  simp_all over simp_all only          n/a
  [3.7]  remove set_option maxHeartbeats      n/a (none here)
```

You MUST output this status block. Reviewers (and the user) check that every rule was
considered. "Skipping" any rule without an `n/a` reason is a defect.

## Step 4 — Step back and think

After mechanical rules and automation upgrades, look at the proof again:

- Could the ENTIRE proof be one tactic? (`grind`, `simp`, `aesop`, `decide`, `omega`)
- Is there a mathlib lemma that makes this trivial? Try `exact?` and `apply?`.
- Term-mode shorter than the tactic proof?
- Can `have` blocks fold into a single composed expression?
- Are there redundant steps that don't actually change the goal?
- Would a completely different proof strategy be shorter? (Sometimes the right move is to
  scrap the existing approach.)

If you find a one-tactic proof: take it. If not: keep the result of Step 3.

## Step 5 — Verify

Two layers: diagnostics first, then gates.

### Step 5a — `lean_diagnostic_messages`

Run `lean_diagnostic_messages` on the file. Fix any breakage caused by your edits before
moving to 5b. If the file doesn't compile, the gates can't run.

### Step 5b — Diff gates (REQUIRED ARTIFACT)

You read `cleanup-gates.md` in Step 1. Capture the diff your worker has produced — the
edits you made versus the file as it was when you started — and run the gates on it.

Capture the diff:

```bash
git diff --no-color -- "<file>"   # Or compare against your start-of-worker snapshot
```

Run the gates on the captured diff. Print this block (the artifact):

```
### Gate status — `decl_name` (Phase 4)

| Gate                          | Result | Details                                          |
|-------------------------------|--------|--------------------------------------------------|
| lake_build_file               | ✓ pass | `lake build <module>` exited 0 in 6s             |
| definition_protected          | ✓ pass | no `def`/`abbrev` lines in the diff              |
| theorem_statement_protected   | ✓ pass | the `theorem decl_name : ...` line is unchanged  |

Overall: pass
```

**Definition_protected** allows a fail only if your audit declared one of:
- audit item 14 (JUNK DEF: inline at use sites), OR
- audit item 18 (GENERALISE: a small typeclass change to a def signature)

**Theorem_statement_protected** allows a fail only if your audit declared one of:
- audit item 5 (NAMING: rename to <new>), OR
- audit item 12 (STRUCTURE: split conjunction / extract branch), OR
- audit item 18 GENERALISE: small-safe typeclass weakening that survives all other gates

If a gate fails *without* a corresponding audit-declared action: revert your edits
(`git checkout -- <file>` if you have git access; otherwise rewrite the affected lines
back to their pre-edit form), and retry without that change. Don't ship a worker run
that fails a gate without an explicit reason.

If `lake build <module>` is too slow to run per-worker (rare for individual modules but
possible for tightly-coupled mathlib files): record `lake_build_file: deferred to Phase
6` and run only the diff-pattern gates. The deferred build will run once at Phase 6.

## Step 6 — Report

Output:

```
### Result: `decl_name`

Before: K lines  After: K' lines  Saved: ΔK lines
Audit issues found: N    Fixed: N    Refactoring deferred: M
Rules applied: [list rule numbers from Step 3 status block]
Gates: [pass / pass with deferred lake_build_file / FAIL on <gate>]
Refactoring needed: [or "none"]
```

If `Gates: FAIL`, the main agent should treat this declaration as not-yet-cleaned and
re-dispatch with the gate failure as feedback. Don't claim the decl is done.

If `Refactoring needed` is non-empty, list each item explicitly so the main agent can
collect it for Phase 5.
````

### Dispatching workers

For each declaration in the list from 1d:

1. Decide if it can run in parallel. A declaration that uses helpers being modified by
   another worker should run *after* those helpers are done.
2. Send the worker prompt as one `Agent` call. Substitute `[file_path]`, `decl_name`, line
   range, lint warnings for the range, and the C.x punch-list items.
3. Wait for completion, capture the report.

**Do not batch multiple declarations into one worker.** That is exactly what causes the
"agent forgets" problem the user complained about.

---

## PHASE 5 — Refactoring (Main agent)

Collect every `Refactoring needed` line from the worker reports. Work them one at a time.

### Order

1. **Mathlib replacements** (delete custom defs/lemmas that mathlib provides; update call sites).
2. **Junk-def inlining** (defs flagged in C.x as junk; inline at every use site).
3. **Junk single-use ∃-lemma inlining**.
4. **Renames** (forbidden abbreviations, snake_case/camelCase fixes, `_aux` suffix). Update
   ALL usages with `Grep`. Update both the file and any other files that reference the
   renamed declaration.
5. **Big-change generalisations** flagged at item 18 by Phase-4 workers — escalate each to a
   full `/generalise <file> <decl_name>` invocation. That mode runs the full Phases 1–9
   (including the user-approval gate), so the user gets the trade-off menu. Don't try to
   apply big-change generalisations inline — they need the literature search confirmed and
   the user's call.
6. **`/decompose-proof` flags**: don't run decomposition here, but record the list in the final report.

### After each refactor

`lean_diagnostic_messages` on the file. Fix any breakage before moving to the next item.

---

## PHASE 6 — Final Verification (Main agent)

Two layers — diagnostic / textual checks first, then the gates on the cumulative diff.

### 6a. Diagnostics + housekeeping

1. `lean_diagnostic_messages` — should be diagnostic-clean. If warnings remain, address them
   (or document why a `nolint` is justified).
2. Grep for `-- FIXME` / `-- TODO` markers — they should not exist (the only acceptable
   FIXME is one tagged `[STRUCTURE]` waiting for `/decompose-proof`).
3. Grep for the file-level rules: no `set_option maxHeartbeats`, no inline `λ`, no `$`, no
   `/-! ##` dividers, no `push_neg` (only `push Not`).

### 6b. File-level gates (REQUIRED ARTIFACT — see cleanup-gates.md)

Run the gates on the cumulative file-level diff (file before /cleanup vs file now). Print
the gate-status block:

```
### Gate status — <file_path> (Phase 6 cumulative)

| Gate                                | Result | Details                                |
|-------------------------------------|--------|----------------------------------------|
| lake_build_file                     | ✓ pass | `lake build <module>` ok in 8s         |
| lake_build                          | ✓ pass | full project build clean               |
| definition_protected                | ✓ pass | (or list every accepted def-line change with the audit item that authorised it) |
| theorem_statement_protected         | ✓ pass | (or list every accepted statement change with its audit item / Phase-5 refactoring source) |
| cumulative_no_unintended_breakage   | ✓ pass | 7 call-site files re-checked; 0 broken |

Overall: pass (or FAIL — <gate>: <reason>)
```

`lake_build` (whole project) is the strongest signal. If the project is small enough that
`lake build` runs in a reasonable time, run it. For large projects, run `lake_build_file`
on this module + every call-site module instead.

`definition_protected` and `theorem_statement_protected` are at file level: every diff
hunk that adds/removes a `def`/`abbrev`/`theorem`/`lemma` line must trace back to either
a Phase-4 worker's audit-declared action OR a Phase-5 refactoring action (rename, mathlib
replacement, junk-def inline). Untraceable signature changes are gate failures.

`cumulative_no_unintended_breakage` is the most expensive gate: re-check every
file-outside-this-one that uses any declaration from this file (find with `Grep`). If any
such file's diagnostics broke: regression — investigate, fix, re-gate.

### 6c. Recovery from gate failure

A `FAIL` in 6b means /cleanup is *not* done. Three responses:

1. **Single-decl regression** — a Phase-4 worker's edits were the cause. Re-run that
   declaration's worker with the gate failure as feedback (Phase 4 retry).
2. **Phase-5 refactoring regression** — a rename or replacement missed a call site, or
   broke a downstream API. Identify and fix in Phase 5; re-run 6b.
3. **Cannot fix in-place** — the change introduces unavoidable breakage (e.g., a planned
   rename that genuinely needs deeper redesign). Stop. Report to user; revert the
   problematic change pending decision.

Do NOT proceed to Phase 6.5 (or Phase 7) with `Overall: FAIL`. The report is for
successful runs only.

---

## PHASE 6.5 — Simplify pass (hand-off to the built-in `/simplify` skill)

After Phase 6 has confirmed the file is gate-clean and project-clean, hand off to the
**built-in `/simplify` skill** for a final holistic review. `/simplify` is a
Claude-Code-provided skill (not part of mathlib-quality) whose job is: *"Review changed
code for reuse, quality, and efficiency, then fix any issues found."*

Its strengths are complementary to ours: where `/cleanup` is checklist-driven (every
golfing rule, every audit item), `/simplify` is holistic — it spots:

- Duplicated proof skeletons across the file we should have factored into a helper but
  didn't.
- Quality issues that don't match any specific rule but are visible at a glance.
- Cross-cutting efficiency / structure issues the per-declaration workers missed because
  they each saw only one declaration.

This is a second pair of eyes after the rule-driven pass. We always run it, never skip.

### 6.5a. Invoke `/simplify`

Use the `Skill` tool to invoke the built-in skill:

```
Skill(skill="simplify")
```

The skill operates on changed code by default. Let it run on the files this `/cleanup`
session modified.

### 6.5b. Required artifact: simplify-pass status block

The simplify pass produces one of three outcomes. Print the corresponding block:

```
### Simplify pass — <file_path>

Outcome: <PASS-THROUGH | ISSUES-FOUND-AND-FIXED | ISSUES-FOUND-NOT-FIXED>

Issues identified by /simplify:
- <list, or "(none)">

Fixes applied by /simplify:
- <list of changes; or "(none — pass-through)">

Files modified:
- <list>
```

### 6.5c. If `/simplify` made changes — re-run gates

If `/simplify` modified anything (`ISSUES-FOUND-AND-FIXED`), the file is in a new state
and the gates from Phase 6 may no longer hold. **Re-run Phase 6** (`6a` diagnostics +
`6b` gates) to confirm the simplify-induced changes also pass:

- `lake_build_file` — must still pass
- `definition_protected` — `/simplify`'s changes must trace to a legitimate refactoring
  action (extract-helper / DRY-fold / etc.); if it touched a `def` line for an unrelated
  reason, that's a defect — investigate
- `theorem_statement_protected` — `/simplify` shouldn't be rewriting theorem statements
  during a polish pass; statement changes here are defects unless the user explicitly
  authorised one
- `cumulative_no_unintended_breakage` — call sites still compile after `/simplify`'s
  changes

If the post-simplify gates fail: revert `/simplify`'s changes (its changes are
post-Phase-6 polish, not load-bearing — reverting is safe) and report the conflict in
Phase 7.

### 6.5d. If `/simplify` found issues but couldn't fix them — log them

If `/simplify` flagged issues that are out of its scope (e.g., it suggested a structural
refactor it didn't implement), record those in the Phase 7 report under a "Simplify
suggestions for follow-up" section. Don't try to apply them inline — that's a follow-up
task for the user.

### 6.5e. Why we always run /simplify, never skip

Adding /simplify isn't optional. It catches what the rule-driven pass missed; if it has
nothing to say, it pass-throughs in seconds. Skipping it because "the file looks clean"
is a defect. The artifact in 6.5b is what makes skipping detectable: a missing
simplify-pass status block fails the Phase-7 report's required-artifact check.

---

## PHASE 7 — Report (Main agent)

Required artifacts that must appear in the report (a missing section = the corresponding
phase wasn't completed; treat as a defect and re-run that phase):

- **Baseline (Phase 0)** — proves the doctor ran
- **Audit (Phase 2)** — proves the punch-list was built
- **Phase 3 file-level fixes** — proves file-level work happened
- **Phase 4 per-declaration results** — proves each decl had a worker
- **Phase 5 refactoring** — even "(none)" is acceptable; missing section = phase skipped
- **Verification (Phase 6)** — diagnostics-clean confirmation
- **Gates (Phase 6 cumulative)** — proves gates were run
- **Simplify pass (Phase 6.5)** — proves the simplify hand-off happened
- **Total line delta** — confirms the work made measurable changes

Single consolidated report:

```
## /cleanup report — [file_path]

### Baseline (Phase 0)
- lake build:                ✓ clean
- LSP responsive:            ✓
- Linter warnings (input):  12 (fed into Phase 2)

### Audit (Phase 2)
- File-level items:        7 (3 fixed in Phase 3, 0 deferred)
- Linter findings:        12 (all resolved)
- Per-decl items:         18 (16 fixed in Phase 4, 2 deferred to Phase 5 refactoring)

### Phase 3 file-level fixes
- Created module docstring (was missing)
- Stripped 3 subsection dividers
- Removed file-level `set_option maxHeartbeats`
- Reordered imports (4 items)
- Mechanical: λ→fun ×4, $→<| ×2, push_neg→push Not ×3

### Phase 4 per-declaration results
| Declaration         | Before | After | Δ   | Rules applied                        |
|---------------------|--------|-------|-----|--------------------------------------|
| `myFoo`             | 10     | 10    |  0  | n/a (def, no proof)                  |
| `bar_thing`         | 12     |  3    | -9  | 1.1, 1.4, 1.10, 2.1                  |
| `main_result`       | 65     | 22    | -43 | 1.4, 1.10, 1.13, 2.1, 2.5, 2.7       |
| ...                 |        |       |     |                                      |

### Phase 5 refactoring
- Renamed `wt_eq_zero` → `weight_eq_zero` (3 call sites updated)
- Inlined junk def `E₄E₆Weight` (13 use sites)
- Removed bridge lemma `splits_id_iff_*` (mathlib equivalent used instead)

### Verification (Phase 6)
✓ lean_diagnostic_messages clean
✓ No FIXMEs remaining

### Gates (Phase 6 cumulative)
| Gate                               | Result |
|------------------------------------|--------|
| lake_build_file                    | ✓ pass |
| lake_build (full project)          | ✓ pass |
| definition_protected               | ✓ pass (1 def-line change traced to Phase-5 junk-def inline of `E₄E₆Weight`) |
| theorem_statement_protected        | ✓ pass (1 statement change traced to rename `wt_eq_zero` → `weight_eq_zero`) |
| cumulative_no_unintended_breakage  | ✓ pass (7 call-site files re-checked) |

### Simplify pass (Phase 6.5)
Outcome: ISSUES-FOUND-AND-FIXED
Issues identified:
- Two near-identical `have` blocks in `lemma_a` and `lemma_b` factored into a shared helper.
- Redundant `simp only [foo, bar]` chain in three lemmas collapsed to a single `simp` call (terminal position).
Fixes applied: 2 (verified diagnostics-clean and gates-clean afterwards)

### Flagged for /decompose-proof
- `theorem_X` (now 38 lines) — STRUCTURE branch >15 after golfing

### Simplify suggestions for follow-up
- (none — all issues addressed in 6.5)

### Total: 740 → 612 lines (-128, -17%)
```

---

## What this command does NOT do

- **Decomposition of long proofs** is flagged, not done. Run `/decompose-proof` separately for those.
- **File splitting** is flagged when files >1000 lines, not done. Run `/split-file` separately.
- **Cross-file PR-feedback fixes** are out of scope. Use `/fix-pr-feedback`.
- **Big-change generalisations** (restating over different abstract structures, public-API
  renames, conclusion restatements driven by literature findings) are flagged for the user
  in Phase 5, not auto-applied. The mechanical generalisation pass and the literature
  search for public decls *do* run inline as part of Phase 4 item 18 — so soft skipping
  is detectable. Only the final approve/apply step is deferred to `/generalise <file>
  <decl_name>` so the user sees the trade-offs before committing to a big change.

---

## Reference

- `skills/mathlib-quality/references/golfing-rules.md` — full rule list (Phase 4 worker reads this)
- `skills/mathlib-quality/references/proof-patterns.md` — data-driven golf patterns (3,772 PRs)
- `skills/mathlib-quality/references/style-rules.md` — file-level + declaration style
- `skills/mathlib-quality/references/naming-conventions.md` — naming + forbidden abbreviations

## Learnings

After completing, record significant learnings to `.mathlib-quality/learnings.jsonl`. Only
non-trivial patterns (1–5 entries). See `skills/mathlib-quality/learning/schema.md`. For
mathlib API discoveries during Phase 5 refactoring, prefer `type: mathlib_discovery`. For
recurring style issues caught in Phase 2 that the user might not have known about, use
`type: style_correction`.
