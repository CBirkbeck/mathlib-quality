# PR Feedback Examples

This guide contains curated examples of common feedback patterns from mathlib PR reviews,
based on the official [PR review guide](https://leanprover-community.github.io/contribute/pr-review.html).

## Review Principles

### Core Values

**Respect and Encouragement:** Reviews must follow the Code of Conduct while being constructive.

```
-- Bad feedback
"This is useless"

-- Good feedback
"Thanks for this work, but we already have a similar lemma called X.
Please consider using that instead."
```

**Humility:** No one has a monopoly on best practices. Allow room for better approaches.

## Review Categories (Easiest to Hardest)

### 1. Style

The easiest issues to catch and fix.

#### Line Length

**Issue:** Lines exceeding 100 characters

```lean
-- Before (too long)
theorem very_long_theorem_name_that_exceeds_the_limit (h₁ : some_hypothesis) (h₂ : another_hypothesis) : conclusion := by

-- After (properly broken)
theorem very_long_theorem_name_that_exceeds_the_limit
    (h₁ : some_hypothesis) (h₂ : another_hypothesis) : conclusion := by
```

**Feedback pattern:** "Line too long, please break at 100 chars"

#### Indentation

**Issue:** Incorrect tactic block indentation

```lean
-- Before (wrong indentation)
theorem foo : P := by
    apply h  -- 4 spaces is wrong
    exact hx

-- After (correct 2-space indentation)
theorem foo : P := by
  apply h
  exact hx
```

**Feedback pattern:** "Please use 2-space indentation for tactic blocks"

#### Whitespace

**Issue:** Missing or extra whitespace

```lean
-- Before
def foo(x:α):β:= ...
f(x,y)

-- After
def foo (x : α) : β := ...
f (x, y)
```

**Feedback pattern:** "Missing space around colon" / "Space needed before parenthesis"

#### `by` Placement

**Issue:** `by` on its own line

```lean
-- Before
theorem foo : P :=
  by exact h

-- After
theorem foo : P := by
  exact h
```

**Feedback pattern:** "Place `by` at end of previous line"

### 2. Naming

#### Non-Descriptive Names

**Issue:** Theorem names that don't follow the conclusion-of-hypothesis pattern

```lean
-- Before
theorem lemma1 : a + b = b + a := ...
theorem my_theorem : P → Q → P ∧ Q := ...

-- After
theorem add_comm : a + b = b + a := ...
theorem And.intro : P → Q → P ∧ Q := ...
```

**Feedback pattern:** "Please use a descriptive name following mathlib conventions"

#### Inconsistent Naming

**Issue:** Names that don't match similar existing lemmas

```lean
-- Before (inconsistent with add_zero)
theorem zero_added : 0 + a = a := ...

-- After (matches existing convention)
theorem zero_add : 0 + a = a := ...
```

**Feedback pattern:** "This should be named X to match the existing Y"

#### Hypothesis Names

**Issue:** Non-standard hypothesis names

```lean
-- Before
theorem foo (hypothesis1 : P) (H : Q) : R := ...

-- After
theorem foo (hp : P) (hq : Q) : R := ...
```

**Feedback pattern:** "Use h-prefixed names for hypotheses"

### 3. Documentation

#### Missing Module Docstring

**Issue:** File lacks module documentation

```lean
-- Before (missing)
import Mathlib.Algebra.Group.Basic

namespace Foo

-- After
import Mathlib.Algebra.Group.Basic

/-!
# Foo structures and lemmas

This file defines `Foo` and proves basic properties.

## Main definitions
* `Foo`: A structure representing...

## Main results
* `foo_bar`: Shows that foo implies bar
-/

namespace Foo
```

**Feedback pattern:** "Please add a module docstring"

#### Missing Declaration Docstring

**Issue:** Public declaration without documentation

```lean
-- Before
def importantFunction (x : α) : β := ...

-- After
/-- Converts `x` to its corresponding `β` value.

This is useful when... -/
def importantFunction (x : α) : β := ...
```

**Feedback pattern:** "Please add a docstring for this definition"

#### History in Docstrings

**Issue:** Referencing development history

```lean
-- Before
/-- This theorem was previously an axiom, now proven. -/
theorem foo : P := ...

-- After
/-- States that P holds. -/
theorem foo : P := ...
```

**Feedback pattern:** "Document current functionality, not development history"

### 4. Location

#### Wrong File

**Issue:** Declaration in inappropriate location

```lean
-- Use #find_home to verify location
#find_home myLemma
```

**Feedback pattern:** "This lemma belongs in X.lean, not Y.lean"

#### Duplicates

**Issue:** Lemma already exists (possibly more general)

```lean
-- Use apply? or exact? to check
example : P := by apply?  -- shows if existing lemma works
```

**Feedback pattern:** "This already exists as `existing_lemma`"

#### File Size

**Issue:** File too long or loosely organized

**Feedback pattern:** "Consider splitting this file (~1500 lines) by topic"

#### Import Issues

**Issue:** Circular dependencies or import creep

```lean
-- Before (unnecessary import)
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Basic  -- not actually used

-- After
import Mathlib.Topology.Basic
```

**Feedback pattern:** "This import doesn't seem to be used"

### 5. Improvements

#### Long Proofs

**Issue:** Proof should be refactored into lemmas

```lean
-- Before (long inline proof)
theorem main_result : P := by
  -- 50 lines of tactics

-- After (with helper lemma)
private lemma helper : Q := by ...

theorem main_result : P := by
  have h := helper
  exact ...
```

**Feedback pattern:** "Consider extracting the X part into a helper lemma"

#### Better Tactics

**Issue:** Verbose tactics when better alternatives exist

```lean
-- Before
theorem foo (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d := by
  apply add_le_add
  · exact h
  · exact h'

-- After (using gcongr)
theorem foo (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d := by
  gcongr
```

**Feedback pattern:** "Try `gcongr` here instead of `add_le_add`"

#### Simpler Proof Structure

**Issue:** Not using available library lemmas

```lean
-- Before (manual induction)
theorem foo : ∀ n, P n := by
  intro n
  induction n with
  | zero => ...
  | succ n ih => ...

-- After (using existing lemma)
theorem foo : ∀ n, P n := existing_induction_lemma
```

**Feedback pattern:** "This follows from `existing_lemma`"

### 6. Library Integration

#### Missing Attributes

**Issue:** Declaration should have `@[simp]`, `@[ext]`, etc.

```lean
-- Before
theorem myFun_zero : myFun 0 = 0 := rfl

-- After
@[simp]
theorem myFun_zero : myFun 0 = 0 := rfl
```

**Feedback pattern:** "This should be a simp lemma"

#### API Design

**Issue:** Missing convenient constructors or lemmas

```lean
-- Feedback: "Please add a constructor that takes X directly"
-- Feedback: "We need the _iff version of this lemma too"
```

#### Generality

**Issue:** Lemma could be more general

```lean
-- Before (only for ℝ)
theorem foo_real : P ℝ := ...

-- After (for any field)
theorem foo [Field K] : P K := ...
```

**Feedback pattern:** "This should work for any Field, not just ℝ"

#### Instance Placement

**Issue:** Instance in wrong location

**Feedback pattern:** "Move this instance to X.lean where the type is defined"

## Proof Golf Feedback

### Unnecessary Tactics

**Issue:** Proofs longer than necessary

```lean
-- Before
theorem foo : a = a := by
  rfl

-- After
theorem foo : a = a := rfl
```

**Feedback pattern:** "This can just be `rfl`"

### Missing Automation

**Issue:** Manual proofs where automation works

```lean
-- Before
theorem foo (a b : ℤ) : a + b = b + a := by
  induction a
  · simp
  · simp [add_succ]
  · simp [neg_add]

-- After
theorem foo (a b : ℤ) : a + b = b + a := add_comm a b
-- or
theorem foo (a b : ℤ) : a + b = b + a := by ring
```

**Feedback pattern:** "This follows from add_comm" / "Try `ring` here"

### Verbose Have Blocks

**Issue:** Unnecessary intermediate steps

```lean
-- Before
theorem foo (h : P → Q) (hp : P) : Q := by
  have hq : Q := h hp
  exact hq

-- After
theorem foo (h : P → Q) (hp : P) : Q := h hp
```

**Feedback pattern:** "The `have` is unnecessary, just use `h hp` directly"

### Bare simp in Non-Terminal Position

**Issue:** Using unsqueezed `simp` before other tactics

```lean
-- Before
theorem foo : P := by
  simp  -- non-terminal
  exact h

-- After
theorem foo : P := by
  simp only [specific_lemmas]
  exact h
```

**Feedback pattern:** "Please use `simp only` with explicit lemmas here"

Note: Terminal `simp` (closing the goal) should NOT be squeezed.

## Performance Feedback

### Slow Proofs

**Issue:** Proofs that take too long to compile

```lean
-- Before (slow)
theorem foo : P := by
  simp [everything]  -- takes 30 seconds

-- After (fast)
theorem foo : P := by
  simp only [specific_lemmas]  -- takes 0.5 seconds
```

**Feedback pattern:** "This proof is slow, please optimize"

### Heartbeat Issues

**Issue:** Proof exceeds default heartbeat limit

```lean
-- Before
set_option maxHeartbeats 400000 in
theorem foo : P := by ...

-- After (optimized to not need the option)
theorem foo : P := by ...
```

**Feedback pattern:** "Please optimize the proof to not need maxHeartbeats increase"

## Common Response Patterns

When addressing feedback:

1. **Acknowledge the issue:** "Fixed the line length issue"
2. **Explain if unclear:** "Changed to X because Y"
3. **Ask if uncertain:** "Should this be X or Y?"
4. **Verify compilation:** Always ensure changes compile
5. **Address all comments:** Don't miss any feedback items
6. **Use `!bench`:** Comment on PR to get performance benchmarks

## Reviewer Experience Levels

**New reviewers** can effectively address:
- Style issues
- Documentation
- Basic location issues

**Experienced reviewers** are better equipped to evaluate:
- Library integration
- Design alignment with mathlib conventions
- Generality and API design

A history of helpful reviews is the primary criterion for advancement to reviewer or maintainer status.

## Real PR Review Examples

The following examples are extracted from actual mathlib4 PR reviews (collected from 1,500+ merged PRs).

### Proof Golf Examples

**Example 1:** Simplifying verbose tactic proofs

```lean
-- Before
@[simp]
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t length_append

-- After
  Quotient.inductionOn₂ s t fun _ _ => length_append
```

**Example 2:** Using `simp_all` instead of manual steps

```lean
-- Before
prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible...)

-- After
· simp_all
```

**Example 3:** Simplifying with `grind`

```lean
-- Before
theorem castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i ≠ 0 := by
  cases n
  · exact i.elim0
  · rw [castSucc_ne_zero_iff, Ne, Fin.ext_...]

-- After
· grind [castSucc_ne_zero_iff]
```

**Example 4:** Removing redundant have blocks

```lean
-- Before
have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

-- After
apply Continuous.tendsto (by fun_prop)
```

### Automation Tactic Examples

**Example 1:** Using `grind` for case analysis

```lean
-- Before
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  exact ⟨a, rfl⟩

-- After
grind
```

**Example 2:** Automation for measurability

```lean
-- Before
(g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } :=
  countable_meas_level_set_pos₀ g_mble.nullMeasurable

-- After
· exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
```

### Simp Cleanup Examples

**Example 1:** Avoid bare simp, use simp only

```lean
-- Before
theorem isSimplyLaced_E₈ : IsSimplyLaced E₈ :=
  fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₈] at h ⊢

-- After
rcases this with h | h <;> simp_all [G₂]
```

**Example 2:** Simp with explicit lemmas

```lean
-- Before
simp only [Function.comp_apply,]

-- After (cleaner formatting)
simp only [Function.comp_apply]
```

### Common Tactic Patterns from PR Reviews

Based on analysis of 2,481 unique suggestions:

| Change | Frequency |
|--------|-----------|
| Added `by` | 509 |
| Removed `by` (term-mode) | 331 |
| Removed `simp` | 311 |
| Removed `exact` | 311 |
| Added `simp` | 284 |
| Removed `rw` | 276 |
| Added `rw` | 171 |
| Removed `rfl` (used directly) | 169 |
| Added `have` | 168 |

### Most Common File Hotspots

Files that received the most review suggestions:

1. `GroupTheory/GroupAction/SubMulAction/Combination.lean` - 36 suggestions
2. `RepresentationTheory/Intertwining.lean` - 31 suggestions
3. `NumberTheory/ModularForms/EisensteinSeries/E2/Summable.lean` - 24 suggestions
4. `ModelTheory/Definability.lean` - 21 suggestions
5. `NumberTheory/MahlerMeasure.lean` - 20 suggestions

### The `grind` Tactic

`grind` is a powerful automation tactic that combines multiple proof strategies. It appears
frequently in PR suggestions as a replacement for verbose case analysis.

**When to use `grind`:**
```lean
-- Case analysis with Finset/card lemmas
-- Before
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
exact ⟨a, rfl⟩

-- After
grind

-- With hints for specific lemmas
grind [castSucc_ne_zero_iff]
grind [Finset.card_eq_zero, primeFactors_eq_empty]
grind [Real.dist_eq]

-- For measurability goals
exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
```

**When NOT to use `grind`:**
- When explicit lemmas make the proof clearer
- When `grind` is slow (> 1s)
- In lemmas that should be simp-normal

### `fun_prop` for Analysis Properties

`fun_prop` is the modern tactic for continuity, differentiability, and measurability.
It replaces `continuity`, `measurability`, and explicit lemma chains.

**Real examples from PRs:**
```lean
-- Proving continuity
@[to_fun (attr := fun_prop, simp)]

-- In proof context
apply Continuous.tendsto (by fun_prop)

-- With sqrt
continuousOn_sqrt := by fun_prop

-- IMPORTANT: unfold definitions first
example : Continuous F := by
  simp only [F]  -- unfold so fun_prop can see structure
  fun_prop
```

### Converting Term Mode ↔ Tactic Mode

**Prefer term mode** when the proof is a direct application:
```lean
-- Before (verbose tactic mode)
theorem foo : P := by
  exact h

-- After (clean term mode)
theorem foo : P := h

-- Before
theorem add_comm : a + b = b + a := by ring

-- After (if a direct lemma exists)
theorem add_comm : a + b = b + a := add_comm a b
```

**Prefer tactic mode** when multiple steps are needed:
```lean
-- Before (ugly nested term)
theorem foo : P := And.intro (by simp) (by ring)

-- After (cleaner tactics)
theorem foo : P := by
  constructor <;> [simp; ring]
```

### Quotient Induction Patterns

A common golf pattern for quotient types:
```lean
-- Before
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t length_append

-- After (using anonymous function)
  Quotient.inductionOn₂ s t fun _ _ => length_append
```

### Data-Driven Feedback Categories

Based on analysis of curated PR data (`data/pr_feedback/`):

| Category | File | Examples |
|----------|------|----------|
| Golf | `curated_golf.json` | 195KB of shortened proofs |
| Tactic improvement | `curated_tactic_improvement.json` | Better tactic choices |
| Simp cleanup | `curated_simp_cleanup.json` | Simp lemma fixes |
| Naming | `curated_naming.json` | Convention fixes |
| Automation | `clean_examples_by_category.json` | `grind`, `fun_prop` usage |
