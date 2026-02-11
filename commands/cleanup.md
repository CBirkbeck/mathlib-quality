---
name: cleanup
description: Full file cleanup to mathlib standards
---

# /cleanup - Full File Cleanup

Clean up a Lean file to meet mathlib standards.

## Usage

```
/cleanup [file_path]
```

If no file is specified, operates on the currently open file.

## Workflow

### Step 1: Initial Analysis

Read the target file and assess:
- File length (flag if >1500 lines)
- Line lengths (flag any >100 chars)
- Import organization
- Module docstring presence

### Step 2: Header Cleanup

1. **Copyright header** - Ensure proper format:
   ```lean
   /-
   Copyright (c) YEAR [Names]. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: [Names]
   -/
   ```

2. **Imports** - Organize alphabetically, remove unused:
   ```lean
   import Mathlib.Algebra.Group.Basic
   import Mathlib.Data.Set.Basic
   ```

3. **Module docstring** - Add or improve:
   ```lean
   /-!
   # Module Title

   Brief description.

   ## Main definitions
   * `Foo`: Description

   ## Main results
   * `foo_bar`: Description
   -/
   ```

### Step 3: Naming Convention Fixes (CRITICAL)

**All declaration names MUST follow mathlib conventions.** For each declaration:

1. **Check the name** against naming rules
2. **Rename if non-conforming** - fix the name
3. **Update ALL usages** in the file

**CRITICAL: Different conventions for defs vs lemmas/theorems!**

| Declaration | Returns | Convention | Example |
|-------------|---------|------------|---------|
| `lemma`/`theorem` | `Prop` | `snake_case` | `continuous_of_bounded` |
| `def` | Data (ℂ, ℝ, Set, etc.) | `lowerCamelCase` | `cauchyPrincipalValue` |
| `structure`/`inductive` | Type | `UpperCamelCase` | `ModularForm` |
| Helper lemmas | `Prop` | `snake_case` + `_aux` | `main_theorem_aux` |

**Key rule: Look at what the declaration RETURNS:**
- Returns **Prop** (statement to prove) → `snake_case`
- Returns **data** (number, set, function) → `lowerCamelCase`
- Defines a **Type** → `UpperCamelCase`

**Examples:**
```lean
-- Lemmas/theorems (return Prop) → snake_case
theorem continuous_of_uniform : Continuous f := ...
lemma norm_le_of_mem_ball : ‖x‖ ≤ r := ...

-- Defs returning data → lowerCamelCase
def cauchyPrincipalValue (f : ℝ → ℂ) : ℂ := ...
def residueAtPole (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := ...
def fundamentalDomain : Set ℂ := ...

-- Types → UpperCamelCase
structure ModularForm where ...
```

**"Conclusion of hypotheses" pattern for lemmas:**
```lean
-- Good lemma names (snake_case, descriptive)
continuous_of_uniform      -- conclusion: continuous, hypothesis: uniform
norm_le_of_mem_ball        -- conclusion: norm ≤, hypothesis: mem ball
integrable_of_bounded      -- conclusion: integrable, hypothesis: bounded

-- Bad - rename these
myLemma                    → describe what it proves (snake_case)
Lemma1                     → use meaningful snake_case
continuous_Function        → continuous_function (consistent snake_case)
```

**Common mistake: snake_case for defs returning data:**
```lean
-- WRONG: def returning ℂ uses snake_case
def cauchy_principal_value (f : ℝ → ℂ) : ℂ := ...

-- CORRECT: def returning ℂ uses lowerCamelCase
def cauchyPrincipalValue (f : ℝ → ℂ) : ℂ := ...
```

**American English:**
- `Factorization` not `Factorisation`
- `normalize` not `normalise`
- `localization` not `localisation`

**How to rename:**
```lean
-- For lemmas: rename to snake_case
lemma fooBar : P := ...  →  lemma foo_bar : P := ...

-- For defs returning data: rename to lowerCamelCase
def foo_bar : ℂ := ...   →  def fooBar : ℂ := ...

-- Then find and replace ALL usages in the file
```

### Step 4: Formatting Fixes

For each declaration, check and fix:

1. **Indentation** - Ensure 2-space indentation in tactic blocks
2. **Line breaks** - Break lines >100 chars appropriately
3. **Whitespace** - Fix spacing around operators, colons, parentheses
4. **Syntax preferences**:
   - `fun` over `λ`
   - `<|` over `$`
   - `change` over `show` in tactic mode

### Step 5: Comment Stripping

**Remove ALL inline comments from proofs:**
```lean
-- BEFORE (bad)
theorem foo : P := by
  -- First establish the bound
  have hbound := bound_lemma hf
  -- Now apply convergence
  exact convergence_lemma hbound

-- AFTER (good)
theorem foo : P := by
  have hbound := bound_lemma hf
  exact convergence_lemma hbound
```

**Docstrings only on key public theorems** (one sentence).

### Step 6: Documentation Check

For each **key public declaration** only:
- Add ONE-SENTENCE docstring describing the result
- Do NOT add docstrings to helper/private lemmas

### Step 7: Structural Decomposition (CRITICAL)

**Apply these mandatory rules to EVERY proof:**

1. **No `∧` in theorem statements** - Split into separate lemmas, combine at end:
   ```lean
   -- BAD
   theorem main : P ∧ Q := by constructor; ...

   -- GOOD
   lemma main_left : P := by ...
   lemma main_right : Q := by ...
   theorem main : P ∧ Q := ⟨main_left, main_right⟩
   ```

2. **Split large `constructor` branches** - If either branch >10 lines, extract both:
   ```lean
   -- BAD
   theorem foo : A ∧ B := by
     constructor
     · -- 15 lines
     · -- 20 lines

   -- GOOD
   private lemma foo_fst : A := by ...  -- 15 lines
   private lemma foo_snd : B := by ...  -- 20 lines
   theorem foo : A ∧ B := ⟨foo_fst, foo_snd⟩
   ```

3. **Split large case branches** - If any branch >10 lines, extract all:
   ```lean
   -- BAD
   theorem bar : P := by
     by_cases h : cond
     · -- 20 lines
     · -- 25 lines

   -- GOOD
   private lemma bar_pos (h : cond) : P := by ...
   private lemma bar_neg (h : ¬cond) : P := by ...
   theorem bar : P := by by_cases h : cond <;> [exact bar_pos h; exact bar_neg h]
   ```

**10 lines is the threshold** - Extract ANY block exceeding 10 lines.

### Step 8: Proof Opportunities

Identify obvious golfing opportunities:
- Inline `have foo := bar` (simple invocations used once)
- Term-mode candidates (simple `by exact x` → `x`)
- Automation opportunities (`ring`, `linarith`, `omega`, `grind`)

### Step 9: Compile Verification

After all changes:
1. Save the file
2. Run `lean_diagnostic_messages` to check for errors
3. If errors introduced, revert problematic changes

## Output Format

```
## Cleanup Report for [filename]

### Summary
- Lines: X (Y lines changed)
- Declarations: N
- Names fixed: K
- Other issues fixed: M

### Naming Fixes
| Old Name | New Name | Reason |
|----------|----------|--------|
| `fooBar` | `foo_bar` | snake_case for lemmas |
| `Lemma1` | `bound_of_compact` | descriptive name |

### Other Changes Made
1. Fixed line length on lines: 45, 78, 123
2. Fixed indentation in: theorem foo, lemma bar
3. Stripped inline comments from proofs
4. Inlined 5 single-use `have` statements

### Compilation Status
✓ File compiles without errors
```

## Reference

See:
- `skills/mathlib-quality/references/naming-conventions.md` - Full naming guide
- `skills/mathlib-quality/references/style-rules.md` - Complete style rules

## Example

Before:
```lean
import Mathlib.Data.Set.Basic

-- My custom lemma for addition
theorem myAddLemma(x:Nat):x+0=x:= by
    -- This is obvious
    simp
```

After:
```lean
import Mathlib.Data.Set.Basic

/-!
# Basic theorems

Simple arithmetic lemmas.
-/

/-- Addition of zero on the right. -/
theorem add_zero_right (x : Nat) : x + 0 = x := by simp only [add_zero]
```
