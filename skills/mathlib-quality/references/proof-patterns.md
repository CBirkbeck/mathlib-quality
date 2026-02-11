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

### `grind`
```lean
-- Powerful automation combining multiple strategies
-- Great for case analysis with Finset/card lemmas
example (hs : s.card = 1) : ∃ a, s = {a} := by grind

-- With hints for specific lemmas
example : castSucc i ≠ 0 := by grind [castSucc_ne_zero_iff]

-- For distance/metric goals
example : dist a b < ε := by grind [Real.dist_eq]

-- For cardinality/emptiness
example (h : n.primeFactors = ∅) : n ≤ 1 := by
  grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

## Quick Reference: Pattern Savings

| Pattern | Savings | Risk | Priority |
|---------|---------|------|----------|
| `by rfl` → `rfl` | 1 line | Zero | ⭐⭐⭐⭐⭐ |
| `by exact h` → `h` | 1 line | Zero | ⭐⭐⭐⭐⭐ |
| Eta-reduction `fun x => f x` → `f` | Tokens | Zero | ⭐⭐⭐⭐⭐ |
| `rw; exact` → `rwa` | 50% | Zero | ⭐⭐⭐⭐⭐ |
| `rw; simp_rw` → `rw; simpa` | 1 line | Zero | ⭐⭐⭐⭐⭐ |
| `.mpr` over `rwa` for trivial | 1 line | Zero | ⭐⭐⭐⭐⭐ |
| `ext + rfl` → `rfl` | 67% | Low | ⭐⭐⭐⭐⭐ |
| intro-dsimp-exact → lambda | 75% | Low | ⭐⭐⭐⭐⭐ |
| Dot notation `.rfl`/`.symm` | Tokens | Zero | ⭐⭐⭐⭐⭐ |
| Inline `show` in `rw` | 50-70% | Zero | ⭐⭐⭐⭐⭐ |
| Transport `▸` for rewrites | 1-2 lines | Zero | ⭐⭐⭐⭐⭐ |
| let+have+exact inline | 60-80% | Medium | ⭐⭐⭐⭐⭐ |
| calc → .trans chains | 2-3 lines | Low | ⭐⭐⭐⭐ |
| Single-use `have` inline | 30-50% | Low | ⭐⭐⭐⭐ |
| Redundant `ext` before `simp` | 50% | Medium | ⭐⭐⭐⭐ |
| `congr; ext; rw` → `simp only` | 67% | Medium | ⭐⭐⭐⭐ |
| Multi-pattern match | 7 lines | Low | ⭐⭐⭐ |
| Symmetric cases with `<;>` | 11 lines | Low | ⭐⭐⭐ |

**ROI Strategy:** Do ⭐⭐⭐⭐⭐ first (instant wins), then ⭐⭐⭐⭐ (quick with testing).

## Mandatory Structural Decomposition

**These rules MUST be applied before any other golfing:**

### Rule 1: No `∧` in Theorem Statements

Split theorems with conjunctions into separate lemmas, then combine:

```lean
-- BAD
theorem main : P ∧ Q := by
  constructor
  · -- proof of P
  · -- proof of Q

-- GOOD
lemma main_left : P := by ...
lemma main_right : Q := by ...
theorem main : P ∧ Q := ⟨main_left, main_right⟩
```

### Rule 2: Extract Large `constructor` Branches (>10 lines)

```lean
-- BAD: Either branch >10 lines
theorem foo : A ∧ B := by
  constructor
  · -- 15 lines
  · -- 20 lines

-- GOOD: Extract both branches
private lemma foo_fst : A := by -- 15 lines, now independently golfable
private lemma foo_snd : B := by -- 20 lines, now independently golfable
theorem foo : A ∧ B := ⟨foo_fst, foo_snd⟩
```

### Rule 3: Extract Large Case Branches (>10 lines)

```lean
-- BAD: Any branch >10 lines
theorem bar : P := by
  by_cases h : cond
  · -- 25 lines
  · -- 30 lines

-- GOOD: Extract all branches
private lemma bar_pos (h : cond) : P := by -- 25 lines
private lemma bar_neg (h : ¬cond) : P := by -- 30 lines
theorem bar : P := by
  by_cases h : cond
  · exact bar_pos h
  · exact bar_neg h
```

**The 10-line threshold applies to:**
- `constructor` branches
- `by_cases` / `rcases` branches
- `match` arms
- `induction` cases
- Individual `have` blocks

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

### Analysis - `fun_prop`

**`fun_prop` is the modern, preferred tactic for continuity, differentiability, and measurability:**

```lean
-- Preferred: fun_prop handles most cases
example : Continuous (fun x => x^2 + 1) := by fun_prop
example : Differentiable ℝ (fun x => x^2 + 3*x) := by fun_prop
example : Measurable (fun x => x^2) := by fun_prop

-- IMPORTANT: fun_prop needs to see the function structure
-- If F is defined elsewhere, unfold it first:
def F (x : ℝ) := x^2 + 3*x

example : Continuous F := by
  simp only [F]  -- unfold so fun_prop can see structure
  fun_prop

-- For composed functions, unfold outer definitions:
example : Continuous (fun x => F (x + 1)) := by
  simp only [F]
  fun_prop
```

**When `fun_prop` fails:**
1. Check if definitions need unfolding with `simp [MyDef]`
2. Check if required instances are available
3. Fall back to explicit lemmas like `Continuous.add`, `Differentiable.mul`

**Legacy tactics (still work but prefer `fun_prop`):**
```lean
-- These are being replaced by fun_prop
example : Continuous (fun x => x^2 + 1) := by continuity
example : Measurable (fun x => x^2) := by measurability
```

## Anti-Patterns to Avoid

### Don't Add Comments to Proofs

```lean
-- Bad: ANY inline comments
theorem foo : P := by
  -- Step 1: Show A
  have hA : A := lemma_a
  -- Step 2: Use A to get B
  have hB : B := lemma_b hA
  -- Step 3: Conclude
  exact hB

-- Good: no comments, self-documenting through structure
theorem foo : P := by
  have hA : A := lemma_a
  have hB : B := lemma_b hA
  exact hB
```

### Golf Aggressively

```lean
-- Good: maximally golfed
theorem foo : P := by simp only [a, b, c, d, e, f] <;> (try ring) <;> linarith

-- Also good: single tactic if possible
theorem foo : P := by simp [a, b, c]; linarith

-- Acceptable but could be shorter
theorem foo : P := by
  simp only [a, b, c]
  ring_nf
  linarith
```

**Goal:** Reduce proof to fewest possible lines/tactics. One-liners are ideal.

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
2. **Short** - Minimize lines and tactics; one-liners are ideal
3. **Maintainable** - Won't break with mathlib updates
4. **Efficient** - Compiles in reasonable time
5. **Comment-free** - No inline comments; use docstrings for documentation

**Brevity is king.** When golfing, the ultimate goal is to reduce proof length. A cryptic one-liner is preferred over a longer, more readable proof. If a proof can be reduced to `by simp`, `by ring`, `by aesop`, or a single `exact`, do it.

## High-Impact Golf Transformations

### Term Mode Conversions

**`by exact` → term mode:**
```lean
-- Before
theorem foo : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t length_append

-- After (with eta-reduced lambda)
theorem foo : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t fun _ _ => length_append
```

**`obtain + exact` → direct:**
```lean
-- Before
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
exact ⟨a, rfl⟩

-- After
grind
```

### Powerful Automation Replacements

**Multi-step proofs → `grind`:**
```lean
-- Before
simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
  Finsupp.card_support_eq_one', pos_iff_ne_zero]

-- After
grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

**Case analysis → `grind`:**
```lean
-- Before
simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
grind

-- After (simpler setup)
intro; grind
```

**Finset/card proofs → `grind`:**
```lean
-- Before (multi-line)
have : 1 < g.support.card := by ...
obtain ⟨b, c, hb, hc, hbc⟩ := Finset.one_lt_card_iff.mp this

-- After
have : 1 < g.supportᶜ.card := by grind [Finset.card_compl, Nat.card_eq_fintype_card]
obtain ⟨b, c, hb, hc, hbc⟩ := Finset.one_lt_card_iff.mp this
```

### Simp Cleanup Patterns

**Trailing commas/noise:**
```lean
-- Before
simp only [Function.comp_apply,]

-- After
simp only [Function.comp_apply]
```

**`fin_cases` + `simp` → `simp_all`:**
```lean
-- Before
fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₈] at h ⊢

-- After
rcases this with h | h <;> simp_all [G₂]
```

### Redundant Code Removal

**Unnecessary setup:**
```lean
-- Before
have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

-- After
apply Continuous.tendsto (by fun_prop)
```

**Verbose lambda → point-free:**
```lean
-- Before
fun s t ht ↦ h_indep s fun i hi ↦ h_le i (t i) <| ht i hi

-- After (if possible)
fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)
```

## Common Reviewer Suggestions

From real mathlib PR reviews:

1. **Replace manual proofs with automation** - If `grind`, `aesop`, or `simp` can do it, use them
2. **Eliminate intermediate `have`** - Inline single-use values
3. **Use `fun_prop`** - Replace `continuity`/`measurability` with `fun_prop`
4. **Remove redundant setup** - Often continuity/tendsto proofs don't need explicit witnesses
5. **Prefer term mode** - `by exact h` should be `h`
