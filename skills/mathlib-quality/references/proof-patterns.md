# Proof Golf Patterns

## Overview

"Golfing" proofs means making them shorter and cleaner while maintaining correctness and readability. This guide covers common patterns for optimizing Lean 4 proofs.

## Automation Tactics

### `simp` Best Practices

**In library code, always use `simp only`:**
```lean
-- Bad: bare simp (can break with mathlib updates)
theorem foo : a + 0 = a := by simp

-- Good: explicit lemmas
theorem foo : a + 0 = a := by simp only [add_zero]

-- Good: with configuration
theorem foo : ... := by simp only [add_zero, mul_one, ← sub_eq_add_neg]
```

**Use `simp?` to find lemmas:**
```lean
-- In development, use simp? to discover what simp uses
theorem foo : a + 0 = a := by simp?
-- Outputs: Try this: simp only [add_zero]
```

### `ring` / `ring_nf`
```lean
-- Solves polynomial equalities
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- ring_nf normalizes without closing
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring_nf; rfl
```

### `linarith` / `nlinarith`
```lean
-- Linear arithmetic over ordered rings
example (a b : ℝ) (h1 : a < b) (h2 : b < 2) : a < 2 := by linarith

-- Nonlinear (limited)
example (a : ℝ) (h : 0 < a) : a * a > 0 := by nlinarith [sq_nonneg a]
```

### `omega`
```lean
-- Integer/natural number arithmetic with quantifier-free formulas
example (n : ℕ) (h : n > 5) : n ≥ 6 := by omega
example (a b : ℤ) (h : a + b = 10) (h2 : a = 3) : b = 7 := by omega
```

### `decide` / `native_decide`
```lean
-- For decidable propositions
example : 2 + 2 = 4 := by decide
example : Nat.Prime 17 := by native_decide
```

### `aesop`
```lean
-- Automated proof search
example (h : P ∧ Q) : Q ∧ P := by aesop

-- With configuration
example : ... := by aesop (add norm simp [my_lemma])
```

## Common Golfing Patterns

### Eliminate Unnecessary `have` Blocks

```lean
-- Verbose
theorem foo (h : P → Q) (hp : P) : Q := by
  have hq : Q := h hp
  exact hq

-- Golfed
theorem foo (h : P → Q) (hp : P) : Q := h hp
```

### Use Term Mode for Simple Proofs

```lean
-- Verbose tactic proof
theorem and_comm : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- Golfed term proof
theorem and_comm : P ∧ Q → Q ∧ P := fun ⟨hp, hq⟩ => ⟨hq, hp⟩

-- Even shorter with And.symm
theorem and_comm : P ∧ Q → Q ∧ P := And.symm
```

### Chain Applications

```lean
-- Verbose
theorem foo : A → D := by
  intro ha
  have hb := f ha
  have hc := g hb
  exact h hc

-- Golfed
theorem foo : A → D := h ∘ g ∘ f

-- Or
theorem foo : A → D := fun ha => h (g (f ha))
```

### Use `exact?` and `apply?`

```lean
-- When stuck, use search tactics
theorem foo : P := by
  apply?  -- Suggests: exact my_lemma h₁ h₂
  -- or
  exact?  -- Searches for exact match
```

### Combine with `<;>`

```lean
-- Verbose
theorem foo : P ∧ Q ∧ R := by
  constructor
  · exact hp
  constructor
  · exact hq
  · exact hr

-- Golfed with <;>
theorem foo : P ∧ Q ∧ R := by
  refine ⟨?_, ?_, ?_⟩ <;> assumption
```

### Use `_root_` Sparingly

```lean
-- Only when necessary to disambiguate
theorem foo : _root_.id x = x := rfl
```

## Structural Patterns

### `obtain` vs `rcases` vs Pattern Matching

```lean
-- All equivalent, choose based on readability
theorem foo (h : ∃ x, P x) : Q := by
  obtain ⟨x, hx⟩ := h
  ...

theorem foo (h : ∃ x, P x) : Q := by
  rcases h with ⟨x, hx⟩
  ...

theorem foo : (∃ x, P x) → Q
  | ⟨x, hx⟩ => ...
```

### `refine` for Partial Terms

```lean
-- Fill in some parts, leave others for tactics
theorem foo : ∃ x, x > 0 ∧ x < 10 := by
  refine ⟨5, ?_, ?_⟩
  · norm_num
  · norm_num

-- Even shorter
theorem foo : ∃ x, x > 0 ∧ x < 10 := ⟨5, by norm_num, by norm_num⟩
```

### `suffices` for Backward Reasoning

```lean
-- Verbose
theorem foo (h : P → Q) : Q := by
  have hp : P := ...
  exact h hp

-- Using suffices
theorem foo (h : P → Q) : Q := by
  suffices P by exact h this
  ...
```

## Specific Domain Patterns

### Set Theory
```lean
-- Use ext for set equality
theorem foo : s ∪ t = t ∪ s := Set.union_comm s t

-- Use mem_* lemmas
theorem bar (h : x ∈ s ∪ t) : x ∈ t ∨ x ∈ s := by
  simp only [Set.mem_union] at h ⊢
  exact h.symm
```

### Algebra
```lean
-- Use ring for polynomial identities
-- Use group for group identities (when available)
-- Use field_simp for field expressions

example (a : ℚ) (ha : a ≠ 0) : a / a = 1 := by field_simp
```

### Analysis
```lean
-- Continuity/measurability tactics
example : Continuous (fun x => x^2 + 1) := by continuity
example : Measurable (fun x => x^2) := by measurability
```

## Anti-Patterns to Avoid

### Don't Over-Golf

```lean
-- Too golfed (hard to read)
theorem foo : P := by simp only [a, b, c, d, e, f] <;> (try ring) <;> linarith

-- Better: readable steps
theorem foo : P := by
  simp only [a, b, c]
  ring_nf
  linarith
```

### Don't Use `decide` for Large Computations

```lean
-- Bad: slow compilation
example : (List.range 10000).sum = 49995000 := by native_decide

-- Better: prove it mathematically
example : (List.range 10000).sum = 49995000 := by
  simp only [List.sum_range_id]
  norm_num
```

### Avoid Redundant Tactics

```lean
-- Bad: redundant rfl
theorem foo : a = a := by rfl; rfl

-- Good
theorem foo : a = a := rfl
```

## Measuring Proof Quality

Good proofs should be:
1. **Correct** - Obviously
2. **Readable** - Others can understand the approach
3. **Maintainable** - Won't break with mathlib updates
4. **Efficient** - Compiles in reasonable time

Balance brevity with clarity. A slightly longer proof that's readable is often better than a cryptic one-liner.
