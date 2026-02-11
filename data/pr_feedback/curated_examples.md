# Curated PR Review Examples

These examples are extracted from actual mathlib4 PR reviews showing
before/after code changes suggested by reviewers.


## Golf

### Example 1: `by exact` to term mode

**File:** `Mathlib/Data/Multiset/AddSub.lean`

**Before:**
```lean4
@[simp]
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t length_append
```

**After:**
```lean4
@[simp]
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t fun _ _ => length_append
```

**Principle:** Eta-reduce and use lambda for cleaner term-mode proofs.

### Example 2: Replace verbose proof with `grind`

**File:** `Mathlib/GroupTheory/GroupAction/SubMulAction/Combination.lean`

**Before:**
```lean4
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
exact ⟨a, rfl⟩
```

**After:**
```lean4
grind
```

**Principle:** When dealing with Finset/card lemmas, `grind` often handles the case analysis automatically.

### Example 3: Simplify case analysis with `grind`

**File:** `Mathlib/Data/Nat/Factorization/PrimePow.lean`

**Before:**
```lean4
simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
  Finsupp.card_support_eq_one', pos_iff_ne_zero]
```

**After:**
```lean4
grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

**Principle:** `grind` with specific lemmas can replace complex simp chains.


## Tactic Improvement

### Example 1: `fun_prop` replaces explicit continuity

**File:** `Mathlib/Analysis/SpecialFunctions/MulExpNegMulSq.lean`

**Before:**
```lean4
have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))
```

**After:**
```lean4
apply Continuous.tendsto (by fun_prop)
```

**Principle:** Often the setup proving intermediate values is unnecessary - `fun_prop` handles it.

### Example 2: `grind` with distance lemmas

**File:** `Mathlib/Analysis/Convex/StdSimplex.lean`

**Before:**
```lean4
-- Multi-line proof with explicit rewrites
```

**After:**
```lean4
grind [Real.dist_eq]
```

**Principle:** For metric/distance goals, `grind` with `Real.dist_eq` is often sufficient.

### Example 3: `grind` for card inequalities

**File:** `Mathlib/GroupTheory/SpecificGroups/Alternating.lean`

**Before:**
```lean4
-- Complex proof establishing cardinality bound
```

**After:**
```lean4
have : 1 < g.supportᶜ.card := by grind [Finset.card_compl, Nat.card_eq_fintype_card]
obtain ⟨b, c, hb, hc, hbc⟩ := Finset.one_lt_card_iff.mp this
```

**Principle:** Use `grind` with cardinality lemmas for Finset bounds.


## Simp Cleanup

### Example 1: Remove trailing commas

**File:** `Mathlib/Topology/ContinuousMap/ContinuousSqrt.lean`

**Before:**
```lean4
simp only [Function.comp_apply,]
```

**After:**
```lean4
simp only [Function.comp_apply]
```

**Principle:** Remove trailing commas in simp lists.

### Example 2: Use `simp_all` for case analysis

**File:** `Mathlib/Data/Matrix/Cartan.lean`

**Before:**
```lean4
fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₈] at h ⊢
```

**After:**
```lean4
rcases this with h | h <;> simp_all [G₂]
```

**Principle:** `simp_all` can often replace repeated `simp` across cases.


## Line Break

### Example 1: Proper hypothesis alignment

**Before:**
```lean4
theorem foo (h₁ : a_very_long_hypothesis_type) (h₂ : another_very_long_hypothesis) : conclusion := by
```

**After:**
```lean4
theorem foo
    (h₁ : a_very_long_hypothesis_type)
    (h₂ : another_very_long_hypothesis) :
    conclusion := by
```


## Naming

### Example 1: Use conclusion-of-hypotheses pattern

**Before:**
```lean4
theorem helper_lemma : ...
```

**After:**
```lean4
theorem continuous_of_bounded : ...
```

**Principle:** Name lemmas by `conclusion_of_hypotheses` pattern (e.g., `continuous_of_bounded`).


## Remove Redundant

### Example 1: Remove unnecessary witness setup

**File:** `Mathlib/Analysis/SpecialFunctions/MulExpNegMulSq.lean`

**Before:**
```lean4
have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))
```

**After:**
```lean4
apply Continuous.tendsto (by fun_prop)
```

**Principle:** Don't manually prove witnesses that automation can handle.

### Example 2: Inline trivial `have` blocks

**Before:**
```lean4
have h := some_computation
exact h
```

**After:**
```lean4
exact some_computation
```

**Principle:** Single-use `have` blocks should be inlined.

### Example 3: Direct lambda instead of verbose intro

**File:** `Mathlib/Probability/Independence/Kernel/Indep.lean`

**Before:**
```lean4
Indep m₁ m₃ κ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)
```

**After:**
```lean4
fun s t ht ↦ h_indep s fun i hi ↦ h_le i (t i) <| ht i hi
```

**Principle:** Use `↦` and cleaner lambda patterns.


## General Principles from PR Reviews

1. **Automation first** - Try `grind`, `aesop`, `simp`, `ring`, `omega` before manual proofs
2. **Term mode preferred** - `by exact h` should just be `h`
3. **Inline single-use values** - Don't create `have` for something used once
4. **Use `fun_prop`** - Replaces `continuity`, `measurability`, explicit lemma chains
5. **`grind` for case analysis** - Especially with Finset/card/membership goals
6. **No comments in proofs** - Proofs should be self-documenting
7. **One-liners ideal** - Brevity trumps readability when golfing
