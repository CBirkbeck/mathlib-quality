---
name: cleanup
description: Full file cleanup to mathlib standards
---

# /cleanup - Full File Cleanup

Combined cleanup + golfing. Worker agents audit and fix each declaration one by one.

## Usage

```
/cleanup [file_path]
```

## Architecture

Each worker agent gets a batch of 3-5 declarations. For each declaration, the worker MUST:
1. Print the structured 13-item audit report (forces checking every rule)
2. Implement all fixes
3. Verify compilation

This way the same agent that identifies issues also fixes them — nothing falls through the cracks.

---

## Step 1: Setup (Main Agent)

### 1a: Collect Lint Diagnostics

Run `lean_diagnostic_messages` on the file. Group warnings by line number and print.

### 1b: Header Cleanup

Fix file-level issues now: copyright header, import order, module docstring.

### 1c: Build Declaration List

List every declaration with line numbers and proof length:

```
1. def myFoo (lines 25-35, 10 lines)
2. lemma bar_thing (lines 40-52, 12 lines)
3. theorem main_result (lines 65-130, 65 lines)
...
```

---

## Step 2: Dispatch Worker Agents

Group declarations into batches of 3-5 by proximity. Dispatch each batch as a worker agent using the `Agent` tool with `subagent_type="general-purpose"`.

**Include the FULL worker prompt below in each agent dispatch.** Do not abbreviate or summarize — the workers need the actual rules.

### Worker Agent Prompt

```
You are cleaning up Lean 4 declarations in [file_path].

Lint diagnostics for this file:
[paste the lint warnings from Step 1a]

Your declarations (process them IN ORDER):
- `decl_1` (lines N-M)
- `decl_2` (lines P-Q)
- `decl_3` (lines R-S)

## FOR EACH DECLARATION, DO EXACTLY THIS:

### A. Print the audit report

You MUST print this report. Every item MUST have an answer.

```
### Auditing: `decl_name` (lines N-M, K lines)

1. LINT: [warnings in this range from diagnostics, or "none"]
2. HAVE SCAN: [see procedure below — list EVERY have]
3. NAMING: [OK / rename to X — reason]
4. LINE PACKING: [lines breaking too early, or "all lines ≥80 chars"]
5. BY PLACEMENT: [any `by` on own line, or "OK"]
6. FORMAT: [λ→fun, $→<|, show→change, indent, empty lines, or "OK"]
7. COMMENTS: [inline comments in proof, or "clean"]
8. DOCSTRING: [needs adding/removing/shortening, or "OK"]
9. TERM MODE: [`by exact h`, `by rfl`, eta-reducible, or "none"]
10. AUTOMATION: [blocks where grind/fun_prop/omega might work, or "none"]
11. VISIBILITY: [should be private / needs _aux, or "OK"]
12. STRUCTURE: [>30 lines / ∧ in statement / branches >10 lines, or "OK"]
13. MATHLIB: [could replace with mathlib, or "no replacement found"]

Issues to fix: [numbered list]
Refactoring needed: [cross-declaration changes, or "none"]
```

### B. Implement ALL fixes from the report

Fix every issue you listed. Then verify with lean_diagnostic_messages.

### C. Move to next declaration

---

## ITEM 2: HAVE SCAN (Do This Carefully)

For EVERY `have` in the proof, list it and classify:

```
2. HAVE SCAN:
   - L52: `have h1 := lemma1 x` — no by, used 1x at L55 → INLINE
   - L53: `have h2 : T := foo y` — no by, used 1x at L58 → INLINE
   - L55: `have h3 := by linarith` — has by → KEEP
   - L60: `have h4 := baz z` — no by, used 2x at L62,65 → KEEP
```

Rules:
| Pattern | Has by? | Uses | Action |
|---------|---------|------|--------|
| `have h := expr` | NO | 1 | INLINE — replace h with expr at use site |
| `have h : T := expr` | NO | 1 | INLINE — replace h with expr at use site |
| `have h := expr` | NO | 2+ | KEEP |
| `have h := by ...` | YES | any | KEEP |
| `have h : T := by ...` | YES | any | KEEP |

To inline: delete the have line, substitute the RHS where h was used.

## ITEM 4: LINE PACKING (Enforce This)

**Fill lines to ~100 chars. Do NOT break at 50-60 chars.**

Signatures — pack parameters:
```lean
-- BAD (4 lines at ~40 chars)
theorem foo
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
-- GOOD (2 lines at ~90 chars)
theorem foo (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
```

simp/rw lists — pack lemma names:
```lean
-- BAD (4 lines)
  simp only [ne_eq, mul_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true,
    ofReal_eq_zero, Real.pi_ne_zero,
    I_ne_zero, or_self]
-- GOOD (2 lines)
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
    Real.pi_ne_zero, I_ne_zero, or_self]
```

Expressions — keep on one line when they fit:
```lean
-- BAD (4 lines)
  rw [show -(2 * ↑Real.pi * I *
      ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) =
    2 * ↑Real.pi * I *
      (-((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))
    from by ring] at h_eq
-- GOOD (2 lines)
  rw [show -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) =
      2 * ↑Real.pi * I * (-((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) from by ring] at h_eq
```

## REMAINING ITEMS (Quick Reference)

3. NAMING: lemma/theorem→snake_case, def→lowerCamelCase, structure→UpperCamelCase.
   conclusion_of_hypothesis pattern. American English.
5. BY PLACEMENT: `by` at end of preceding line, NEVER alone on own line.
6. FORMAT: `fun` not `λ`, `<|` not `$`, `change` not `show`, 2-space indent, no empty lines in decls.
7. COMMENTS: Remove ALL inline comments from proofs. No commented-out code.
8. DOCSTRING: Public theorem/def → one sentence. Private/helper → none.
9. TERM MODE: `by exact h`→`h`, `by rfl`→`rfl`, `fun x => f x`→`f`,
   `constructor; exact a; exact b`→`⟨a, b⟩`, `intro h; exact f h`→`f`.
10. AUTOMATION: Try grind/fun_prop/omega/ring on multi-step blocks (use lean_multi_attempt).
    `rw[..]; exact h`→`rwa`. `simp; exact h`→`simpa using h`. Merge consecutive rw.
11. VISIBILITY: Only used in file → private. Helper → private + _aux.
12. STRUCTURE: >30 lines → add `-- FIXME: [STRUCTURE]` (for /decompose-proof later).
    ∧ in statement → note. Branches >10 lines → note.
13. MATHLIB: Quick search if def/lemma duplicates mathlib.

## CROSS-DECLARATION CHANGES

If a fix requires changes to OTHER declarations (rename, remove, mathlib replace),
do NOT do it inline. Instead, report it as a "Refactoring needed" item.
```

Dispatch all batches in parallel.

---

## Step 3: Refactoring (Main Agent)

After all workers complete, collect their "Refactoring needed" items.

Work through them one at a time:
1. Make the change
2. Update ALL affected call sites (use Grep)
3. Verify with `lean_diagnostic_messages`

Priority: mathlib replacements > removals > renames.

---

## Step 4: Final Verification (Main Agent)

1. Run `lean_diagnostic_messages` — should be clean
2. Check for any remaining `-- FIXME:` comments (only `[STRUCTURE]` should remain)

---

## Output Format

```
## Cleanup Report for [filename]

### Workers Dispatched: N batches, M declarations total

### Per-Declaration Results
| Declaration | Issues Found | Fixed | Skipped |
|-------------|-------------|-------|---------|
| `foo_bar` | 5 | 5 | 0 |
| `main_thm` | 3 | 2 | 1 (grind failed) |

### Refactoring Completed
- Renamed: [list]
- Removed: [list]
- Mathlib replaced: [list]

### Verification
✓ File compiles without errors
✓ No remaining FIXME comments (except STRUCTURE)

### Flagged for /decompose-proof
- `theorem_X` (line N): 45 lines
```

---

## Reference

- `skills/mathlib-quality/SKILL.md` — comprehensive style reference
- `skills/mathlib-quality/references/` — naming, style, proof patterns
- `skills/mathlib-quality/examples/` — golf examples from PR reviews

## Learnings

After completing, record significant learnings to `.mathlib-quality/learnings.jsonl`.
Only capture non-trivial patterns (1-5 entries). See `skills/mathlib-quality/learning/schema.md`.
