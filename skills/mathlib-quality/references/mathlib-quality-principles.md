# Mathlib Quality Principles

This document synthesizes the key quality principles from analyzing 4,600+ mathlib PR review comments.
Use this as your guide for understanding what mathlib quality means.

## Core Philosophy

### 1. Brevity is King
**The #1 principle from PR reviews: shorter is almost always better.**

```lean
-- Bad: 4 lines
have h1 := foo
have h2 := bar h1
have h3 := baz h2
exact h3

-- Good: 1 line
exact baz (bar foo)
```

One-liners are the gold standard. If a proof can be a single tactic or term, it should be.

### 2. Automation First
Try automation tactics before writing manual proofs. The order of preference:

1. **`grind`** - Most powerful, handles case analysis, Finset/card, membership
2. **`aesop`** - Good for search-based proofs
3. **`simp_all`** - For goals with many hypotheses to use
4. **`fun_prop`** - For continuity, differentiability, measurability
5. **`omega`** / **`ring`** / **`linarith`** - For arithmetic
6. **`decide`** - For decidable props
7. **Manual proof** - Only if automation fails

### 3. Term Mode Preferred
Tactic mode adds overhead. If the proof is simple, use term mode.

```lean
-- Bad
theorem foo : P := by exact some_term

-- Good
theorem foo : P := some_term
```

### 4. No Comments in Proofs
Proofs should be self-documenting through good naming and structure.
**Zero inline comments allowed in mathlib proofs.**

```lean
-- Bad
theorem foo : P := by
  -- First we establish the bound
  have hbound := bound_lemma hf
  -- Now apply convergence
  exact convergence_lemma hbound

-- Good (one-liner is even better)
theorem foo : P := convergence_lemma (bound_lemma hf)
```

### 5. Minimal Docstrings
Docstrings must be **1-2 consecutive lines only**. No blank lines inside docstrings.
No proof strategies, no technical notes.

```lean
-- Bad: verbose docstring with proof strategy
/-- Classical residue theorem: when γ avoids all singularities.

    This is the special case where all winding numbers are integers.

    **Note**: The hypothesis `hf_ext` ensures f is properly extended at singularities.
    While the integral only depends on f along the curve (which avoids S), the proof
    goes through the general residue theorem machinery which requires this condition.
-/
theorem classical_residue_theorem : ... := by

-- Good: one sentence
/-- Classical residue theorem when γ avoids all singularities. -/
theorem classical_residue_theorem : ... := by
```

**Forbidden in docstrings:**
- `**Proof idea**:` or `**Proof strategy**:`
- `**Note**:` or `**Technical note**:`
- Multi-paragraph explanations
- Bullet points explaining the proof
- References to other proof assistants (e.g., Isabelle, HOL)

**File structure:**
- Module docstring only at TOP of file
- NO section markers (`/-! ## ... -/`) throughout the code
- Results separated by single blank line
- Definitions should always have a one-sentence docstring

## Tactical Wisdom

### The Power of `grind`

`grind` is underutilized. It handles many patterns that look complex:

```lean
-- Pattern 1: obtain + exact
-- Before:
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
exact ⟨a, rfl⟩
-- After:
grind

-- Pattern 2: Finset/card goals
-- Before: complex card inequality proof
-- After:
grind [Finset.card_compl, Nat.card_eq_fintype_card]

-- Pattern 3: Distance/metric goals
-- Before: multi-line dist rewrites
-- After:
grind [Real.dist_eq]

-- Pattern 4: Case analysis
-- Before: simp_rw with multiple rewrites
-- After:
grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

**Rule: Try `grind` first on any complex-looking goal.**

### `fun_prop` Replaces Manual Chains

```lean
-- Bad: explicit continuity
apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

-- Good: let fun_prop figure it out
apply Continuous.tendsto (by fun_prop)

-- Even better if whole proof is continuity
theorem foo : Continuous f := by fun_prop
```

**Rule: For continuity/differentiability/measurability, always try `fun_prop` first.**

### `simpa` vs `simp`

```lean
-- Bad
simp only [foo]
exact h

-- Good
simpa only [foo] using h

-- Also bad
simp; exact h

-- Good
simpa using h
```

### `simp_all` for Case Analysis

```lean
-- Bad
fin_cases i <;> fin_cases j <;> simp [X] at h ⊢

-- Good
rcases this with h | h <;> simp_all [X]
```

## Structural Patterns

### Inline Single-Use `have`

```lean
-- Bad: have used only once
have h := some_computation
exact f h

-- Good: inline it
exact f some_computation

-- Exception: keep if used multiple times
have h := expensive_computation
exact ⟨f h, g h, h.property⟩  -- h used 3 times
```

### Eta-Reduce Functions

```lean
-- Bad
fun x => f x

-- Good
f

-- Bad
intro hp
exact f hp

-- Good
f
```

### Constructor Shortcuts

```lean
-- Bad
constructor
exact a
exact b

-- Good
exact ⟨a, b⟩
```

### Rewrite + Rfl

```lean
-- Bad
rw [h]
rfl

-- Good (if applicable)
h

-- Or
h ▸ rfl
```

## Code Structure

### Line Length: 100 Characters Max
Break at operators, align continuations:

```lean
-- Bad
theorem foo (h₁ : a_very_long_hypothesis_type) (h₂ : another_very_long_hypothesis) : conclusion := by

-- Good
theorem foo
    (h₁ : a_very_long_hypothesis_type)
    (h₂ : another_very_long_hypothesis) :
    conclusion := by
```

### Proof Length: 50 Lines Max (Target <15)

Long proofs indicate poor structure. Decompose:

| Length | Action |
|--------|--------|
| <15 lines | Ideal |
| 15-30 lines | Consider decomposition |
| 30-50 lines | Must decompose |
| >50 lines | Critical - aggressive decomposition required |

### Helper Lemmas

```lean
-- Good: private, _aux suffix, descriptive name
private lemma norm_bound_of_continuous_aux : ‖f x‖ ≤ C := by ...

-- Bad: non-descriptive
private lemma aux1 : ... := by ...
```

## Naming Conventions

### The Critical Distinction

| Declaration | Returns | Convention | Example |
|-------------|---------|------------|---------|
| `lemma`/`theorem` | `Prop` | `snake_case` | `continuous_of_bounded` |
| `def` | Data (ℂ, ℝ, Set) | `lowerCamelCase` | `cauchyPrincipalValue` |
| `structure`/`inductive` | Type | `UpperCamelCase` | `ModularForm` |

**Common mistake: using `snake_case` for defs returning data.**

```lean
-- Wrong
def cauchy_principal_value : ℂ := ...

-- Right
def cauchyPrincipalValue : ℂ := ...
```

### The "Conclusion of Hypotheses" Pattern

```lean
-- Good: describes what it proves
continuous_of_bounded     -- continuous IF bounded
norm_le_of_mem_ball       -- norm ≤ IF in ball
integrable_of_summable    -- integrable IF summable

-- Bad: non-descriptive
helper_lemma
lemma1
my_result
```

## Simp Cleanup

### No Trailing Commas
```lean
-- Bad
simp only [Function.comp_apply,]

-- Good
simp only [Function.comp_apply]
```

### Non-Terminal Simp Needs `only`
```lean
-- Bad (if not closing goal)
simp
exact h

-- Good
simp only [relevant_lemmas]
exact h
```

### Terminal Simp is OK Unsqueezed
```lean
-- Fine if it closes the goal
theorem foo : P := by simp
```

## What Reviewers Flag Most Often

From analyzing 4,600+ PR comments, these are the top issues:

1. **Verbose proofs** - Can automation handle it? (40% of feedback)
2. **Unnecessary `have` blocks** - Inline single-use (15%)
3. **`by exact` instead of term mode** (10%)
4. **Lines over 100 characters** (8%)
5. **Comments in proofs** (7%)
6. **Poor naming conventions** (6%)
7. **Not using `fun_prop`** (5%)
8. **Not using `grind`** (5%)
9. **Trailing commas in simp** (2%)
10. **Other style issues** (2%)

## Quick Reference: Pattern Replacements

| Before | After | Savings |
|--------|-------|---------|
| `by exact h` | `h` | 1 line |
| `by rfl` | `rfl` | 1 line |
| `fun x => f x` | `f` | tokens |
| `have h := x; exact h` | `exact x` | 1 line |
| `simp; exact h` | `simpa using h` | 1 line |
| `rw [h]; exact g` | `rwa [h]` | 1 line |
| `obtain ⟨a,b⟩ := h; exact ⟨a,b⟩` | `h` or `grind` | 2 lines |
| `constructor; exact a; exact b` | `⟨a, b⟩` | 2 lines |
| complex case analysis | `grind [hints]` | 60-80% |
| manual continuity | `fun_prop` | 50-90% |

## Summary

**The essence of mathlib quality:**

1. **Brevity** - Shortest proof wins
2. **Automation** - Let tactics do the work
3. **Structure** - Decompose, name well, no comments
4. **Consistency** - Follow conventions exactly

When in doubt, ask: "Can this be shorter?"
