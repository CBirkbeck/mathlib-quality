# Proof Decomposition Examples

**Rule: No proof should exceed 50 lines. Target: main theorems <15 lines.**

Long proofs indicate the mathematical structure hasn't been properly captured. First understand
the mathematics, then extract.

## Core Principles

1. **Search mathlib FIRST** - Before creating ANY helper, check if mathlib already has it
2. **Generalize, don't specialize** - No single-use helpers; make lemmas reusable
3. **Review definitions too** - Not just proofs; definitions may duplicate mathlib
4. **Result by result** - Careful, systematic review of EVERY declaration

## Example 0: Search Mathlib First

**Before writing ANY helper, search mathlib:**

```bash
# Type pattern search
lean_loogle "IsCompact → ∃ x, ∀ y, ‖f y‖ ≤ ‖f x‖"

# Natural language search
lean_leansearch "continuous function on compact set achieves maximum"

# Result: IsCompact.exists_isMaxOn
```

Many "helpers" you think you need are already in mathlib. Common examples:
- `IsCompact.exists_bound_of_continuousOn` - bounded on compact
- `norm_sum_le` - triangle inequality for sums
- `MeasureTheory.tendsto_integral_of_dominated_convergence` - DCT
- `Differentiable.continuous` - differentiable → continuous

**If mathlib has it, USE IT. Don't create a helper.**

## Example 0.5: Generalize Before Extracting

```lean
-- BAD: Single-use helper tied to specific context
private lemma residue_theorem_aux (γ : PiecewiseC1Curve) (S0 : Finset ℂ)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    ∀ t, γ.toFun t ∉ S0 → DifferentiableAt ℂ f (γ.toFun t) := ...

-- GOOD: General lemma useful elsewhere
lemma differentiableAt_of_mem_diff_finset {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ S)) {z : ℂ}
    (hz : z ∈ U) (hz' : z ∉ S) : DifferentiableAt ℂ f z :=
  hf.differentiableAt (hU.mem_nhds hz |>.diff_finite S hz')
```

**Ask before extracting:**
- Can this be stated more generally?
- Would this be useful in other contexts?
- Are the hypotheses minimal?

## Example 1: Mathematical Analysis First

This is the key pattern. Before coding, understand what's being proved.

```lean
-- Before (85 lines - CRITICAL: must decompose aggressively)
theorem dominated_convergence_integral (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (F : ℝ → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hF_meas : Measurable F)
    (hg_int : Integrable g)
    (hbound : ∀ n x, ‖f n x‖ ≤ g x)
    (hconv : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x, f n x) atTop (𝓝 (∫ x, F x)) := by
  -- [85 lines of tactics...]

-- STEP 1: Mathematical Analysis
-- Q1: What does this prove?
--     If f_n → F pointwise and |f_n| ≤ g with g integrable, then ∫f_n → ∫F
-- Q2: Key mathematical steps?
--     1. Each f_n is integrable (dominated by g)
--     2. The limit F is integrable (also dominated by g)
--     3. Apply Lebesgue DCT
-- Q3: What independent facts?
--     - Integrability of f_n (from bound by g)
--     - Integrability of F (from pointwise limit + bound)
--     - The actual DCT application

-- STEP 2: Extract based on mathematical structure
private lemma dominated_implies_integrable (f : ℝ → ℝ) (g : ℝ → ℝ)
    (hf : Measurable f) (hg : Integrable g) (hbound : ∀ x, ‖f x‖ ≤ g x) :
    Integrable f :=
  hg.mono hf.aestronglyMeasurable (eventually_of_forall hbound)

private lemma limit_integrable_of_dominated (F : ℝ → ℝ) (g : ℝ → ℝ)
    (hF : Measurable F) (hg : Integrable g)
    (hbound : ∀ x, ‖F x‖ ≤ g x) : Integrable F :=
  dominated_implies_integrable F g hF hg hbound

-- Main theorem now assembles these (<10 lines)
theorem dominated_convergence_integral (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (F : ℝ → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hF_meas : Measurable F)
    (hg_int : Integrable g)
    (hbound : ∀ n x, ‖f n x‖ ≤ g x)
    (hconv : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x, f n x) atTop (𝓝 (∫ x, F x)) :=
  MeasureTheory.tendsto_integral_of_dominated_convergence g
    (fun n => (hf_meas n).aestronglyMeasurable)
    (fun n => eventually_of_forall (hbound n))
    hg_int
    (eventually_of_forall hconv)
```

## Example 2: Extract Estimate Lemmas

```lean
-- Before (60 lines)
theorem continuous_bounded_on_compact (f : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    ∃ M, ∀ x ∈ K, ‖f x‖ ≤ M := by
  -- [60 lines establishing bound...]

-- Mathematical Analysis:
-- This proves: continuous functions are bounded on compact sets
-- Key facts: (1) Image is compact, (2) Compact ⊆ ℝ is bounded

private lemma image_compact_of_continuousOn (f : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    IsCompact (f '' K) :=
  hK.image_of_continuousOn hf

private lemma compact_real_bounded (S : Set ℝ) (hS : IsCompact S) :
    Bornology.IsBounded S :=
  hS.isBounded

theorem continuous_bounded_on_compact (f : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    ∃ M, ∀ x ∈ K, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (image_compact_of_continuousOn f K hK hf).isBounded.subset_ball 0
  exact ⟨M, fun x hx => by simpa using hM (Set.mem_image_of_mem f hx)⟩
```

## Example 3: Extract Case Analysis by Mathematical Case

```lean
-- Before (55 lines)
theorem sign_mul (a b : ℝ) : SignType.sign (a * b) = SignType.sign a * SignType.sign b := by
  -- [55 lines of nested case analysis...]

-- Mathematical Analysis:
-- Sign of product depends on signs of factors
-- Cases: (pos,pos), (pos,neg), (pos,zero), (neg,pos), (neg,neg), (neg,zero), (zero,_)

-- Extract by mathematical meaning, not syntax
private lemma sign_mul_pos_pos (ha : 0 < a) (hb : 0 < b) :
    SignType.sign (a * b) = 1 := sign_pos (mul_pos ha hb)

private lemma sign_mul_pos_neg (ha : 0 < a) (hb : b < 0) :
    SignType.sign (a * b) = -1 := sign_neg (mul_neg_of_pos_of_neg ha hb)

private lemma sign_mul_neg_pos (ha : a < 0) (hb : 0 < b) :
    SignType.sign (a * b) = -1 := sign_neg (mul_neg_of_neg_of_pos ha hb)

private lemma sign_mul_neg_neg (ha : a < 0) (hb : b < 0) :
    SignType.sign (a * b) = 1 := sign_pos (mul_pos_of_neg_of_neg ha hb)

private lemma sign_mul_zero_left (hb : b = 0) :
    SignType.sign (a * b) = 0 := by simp [hb]

private lemma sign_mul_zero_right (ha : a = 0) :
    SignType.sign (a * b) = 0 := by simp [ha]

theorem sign_mul (a b : ℝ) : SignType.sign (a * b) = SignType.sign a * SignType.sign b := by
  rcases lt_trichotomy a 0 with ha | ha | ha <;>
  rcases lt_trichotomy b 0 with hb | hb | hb <;>
  simp [sign_mul_pos_pos, sign_mul_pos_neg, sign_mul_neg_pos, sign_mul_neg_neg,
        sign_mul_zero_left, sign_mul_zero_right, *]
```

## Example 4: Parameterize Repeated Patterns

```lean
-- Before (70 lines with 3 nearly identical bounds)
theorem triangle_ineq_three (a b c : ℝ) (ε : ℝ) (hε : 0 < ε)
    (ha : ‖a‖ < ε/3) (hb : ‖b‖ < ε/3) (hc : ‖c‖ < ε/3) :
    ‖a + b + c‖ < ε := by
  have h1 : ‖a‖ < ε/3 := by
    -- [10 lines]
  have h2 : ‖b‖ < ε/3 := by
    -- [10 lines, same structure as h1]
  have h3 : ‖c‖ < ε/3 := by
    -- [10 lines, same structure as h1]
  calc ‖a + b + c‖ ≤ ‖a‖ + ‖b + c‖ := norm_add_le a (b + c)
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_add_le b c]
    _ < ε/3 + ε/3 + ε/3 := by linarith
    _ = ε := by ring

-- After: The bounds ha, hb, hc are already given! No extraction needed.
-- The main theorem is just:
theorem triangle_ineq_three (a b c : ℝ) (ε : ℝ) (hε : 0 < ε)
    (ha : ‖a‖ < ε/3) (hb : ‖b‖ < ε/3) (hc : ‖c‖ < ε/3) :
    ‖a + b + c‖ < ε := by
  calc ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_add₃ a b c
    _ < ε := by linarith
```

But if the bounds need to be established:

```lean
-- Parameterized helper for the repeated pattern
private lemma bound_from_hypothesis (x : ℝ) (C : ℝ) (hC : 0 < C)
    (hx : SomeProperty x) : ‖f x‖ < C :=
  -- The common proof structure

theorem main : ... := by
  have ha := bound_from_hypothesis a (ε/3) (by linarith) ha_prop
  have hb := bound_from_hypothesis b (ε/3) (by linarith) hb_prop
  have hc := bound_from_hypothesis c (ε/3) (by linarith) hc_prop
  linarith [norm_add₃ a b c]
```

## Example 5: Consolidate Shared Helpers Across Theorems

```lean
-- Before: Two theorems with similar internal logic (100+ lines total)
theorem foo_theorem (f : ℝ → ℝ) (hf : Differentiable ℝ f) : ... := by
  have deriv_bound : ∀ x ∈ K, ‖deriv f x‖ ≤ C := by
    intro x hx
    -- [15 lines establishing derivative bound using mean value theorem]
  ...

theorem bar_theorem (g : ℝ → ℝ) (hg : Differentiable ℝ g) : ... := by
  have deriv_bound : ∀ x ∈ K, ‖deriv g x‖ ≤ C := by
    intro x hx
    -- [15 lines - SAME structure as foo_theorem]
  ...

-- After: Shared mathematical helper
private lemma deriv_bound_on_compact (φ : ℝ → ℝ) (K : Set ℝ) (C : ℝ)
    (hφ : Differentiable ℝ φ) (hK : IsCompact K)
    (hbound : ∀ x ∈ K, ‖φ x‖ ≤ C) :
    ∃ D, ∀ x ∈ K, ‖deriv φ x‖ ≤ D := by
  -- Single implementation of the shared logic
  exact hK.exists_bound_of_continuousOn hφ.continuous.continuousOn

theorem foo_theorem (f : ℝ → ℝ) (hf : Differentiable ℝ f) : ... := by
  obtain ⟨D, hD⟩ := deriv_bound_on_compact f K C hf hK hf_bound
  ...

theorem bar_theorem (g : ℝ → ℝ) (hg : Differentiable ℝ g) : ... := by
  obtain ⟨D, hD⟩ := deriv_bound_on_compact g K C hg hK hg_bound
  ...
```

## Example 6: Complex Analysis Decomposition

```lean
-- Before (90 lines)
theorem residue_integral (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ)
    (hf : ∀ z ∈ Metric.sphere z₀ r, DifferentiableAt ℂ f z)
    (hpole : HasSimplePoleAt f z₀) :
    (∮ z in C(z₀, r), f z) = 2 * π * I * residue f z₀ := by
  -- [90 lines...]

-- Mathematical Analysis:
-- 1. Near z₀, f(z) = c/(z-z₀) + g(z) where g is holomorphic
-- 2. Integral of g around circle = 0 (Cauchy)
-- 3. Integral of c/(z-z₀) around circle = 2πic
-- 4. Residue = c by definition

private lemma simple_pole_decomposition (f : ℂ → ℂ) (z₀ : ℂ)
    (hpole : HasSimplePoleAt f z₀) :
    ∃ c g, (∀ z ≠ z₀, f z = c / (z - z₀) + g z) ∧ AnalyticAt ℂ g z₀ :=
  hpole.exists_eq_add_analytic

private lemma holomorphic_integral_zero (g : ℂ → ℂ) (z₀ : ℂ) (r : ℝ)
    (hg : ∀ z ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ g z) :
    (∮ z in C(z₀, r), g z) = 0 :=
  circleIntegral.integral_eq_zero_of_differentiableOn hg

private lemma simple_pole_integral (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (c : ℂ) :
    (∮ z in C(z₀, r), c / (z - z₀)) = 2 * π * I * c :=
  circleIntegral.integral_sub_inv_smul z₀ r c

theorem residue_integral (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ)
    (hf : ∀ z ∈ Metric.sphere z₀ r, DifferentiableAt ℂ f z)
    (hpole : HasSimplePoleAt f z₀) :
    (∮ z in C(z₀, r), f z) = 2 * π * I * residue f z₀ := by
  obtain ⟨c, g, hdecomp, hg⟩ := simple_pole_decomposition f z₀ hpole
  calc (∮ z in C(z₀, r), f z)
    = (∮ z in C(z₀, r), c / (z - z₀) + g z) := by simp_rw [hdecomp _ (ne_of_mem_sphere ...)]
    _ = (∮ z in C(z₀, r), c / (z - z₀)) + (∮ z in C(z₀, r), g z) := circleIntegral.integral_add ...
    _ = 2 * π * I * c + 0 := by rw [simple_pole_integral, holomorphic_integral_zero]
    _ = 2 * π * I * residue f z₀ := by simp [residue_simple_pole hpole]
```

## Example 7: Review Definitions Too

**Don't just review proofs - review EVERY definition.**

```lean
-- BAD: Reinventing mathlib
def cauchySequence (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖f m - f n‖ < ε

-- GOOD: Use mathlib's CauchySeq
-- (Already exists: CauchySeq f)

-- BAD: Overly specific definition
def functionBoundedOnGamma (f : ℂ → ℂ) (γ : PiecewiseC1Curve) : Prop :=
  ∃ M, ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M

-- GOOD: General definition (or use mathlib's BoundedContinuousFunction)
def BoundedOn (f : α → β) (s : Set α) [Norm β] : Prop :=
  ∃ M, ∀ x ∈ s, ‖f x‖ ≤ M
```

**For each definition, ask:**
1. Does mathlib already have this? (`lean_loogle`, `lean_leansearch`)
2. Is it stated at the right level of generality?
3. Could it use existing mathlib structures instead?

## Aggressive Decomposition Checklist

For any proof >50 lines:

- [ ] **Searched mathlib** for existing lemmas (loogle, leansearch)
- [ ] **Wrote mathematical summary** (3-5 sentences, no code)
- [ ] **Identified 3+ independent facts** to extract
- [ ] **Checked each fact against mathlib** before creating helper
- [ ] **Generalized helpers** - no single-use lemmas
- [ ] **Named helpers mathematically** (not `_aux1`, `_aux2`)
- [ ] **Minimized hypotheses** on each helper
- [ ] **Main theorem <15 lines** after decomposition
- [ ] **Golfed all helpers**
- [ ] **Checked for consolidation** across file
- [ ] **Reviewed definitions** in the file too

## Helper Naming Guide

| Mathematical Content | Good Name |
|---------------------|-----------|
| Bound on norm | `norm_bound_of_...` |
| Integrability | `integrable_of_...` |
| Continuity | `continuous_...` |
| Convergence | `tendsto_...`, `limit_...` |
| Existence | `exists_...` |
| Case analysis | `case_pos`, `case_neg`, `case_zero` |

## When NOT to Extract

- Helper would need 5+ parameters (too coupled to context)
- Logic is inherently sequential (steps depend on each other)
- Main theorem is already <15 lines
- Extraction would lose clarity
