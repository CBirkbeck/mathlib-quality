# Replace with Automation

**Pattern**: Replace multi-step manual proofs with powerful automation tactics.

**Stats**: 1144 automation_suggestion patterns in PR feedback data.

## `grind` - The Power Tactic

### Example 1: Finset/card proofs
```lean
-- Before
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
exact ⟨a, rfl⟩

-- After
grind
```

### Example 2: Cardinality bounds
```lean
-- Before
have : 1 < g.support.card := by
  rw [Finset.card_compl]
  omega

-- After
have : 1 < g.supportᶜ.card := by grind [Finset.card_compl, Nat.card_eq_fintype_card]
```

### Example 3: Distance/metric goals
```lean
-- Before
rw [Real.dist_eq]
ring_nf
linarith

-- After
grind [Real.dist_eq]
```

### Example 4: Membership proofs
```lean
-- Before
simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
cases h <;> simp_all

-- After
intro; grind
```

### Example 5: Prime factors
```lean
-- Before
simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
  Finsupp.card_support_eq_one', pos_iff_ne_zero]

-- After
grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

## `fun_prop` - Analysis Properties

### Example 1: Continuity
```lean
-- Before
have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
  simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
nth_rw 2 [this]
apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

-- After
apply Continuous.tendsto (by fun_prop)
```

### Example 2: Differentiability
```lean
-- Before
apply Differentiable.add
· exact differentiable_const _
· apply Differentiable.mul
  · exact differentiable_id
  · exact differentiable_const _

-- After
fun_prop
```

### Example 3: With definition unfolding
```lean
-- Before
def F (x : ℝ) := x^2 + 3*x
example : Continuous F := by
  apply Continuous.add
  · exact continuous_pow 2
  · exact continuous_const.mul continuous_id

-- After
example : Continuous F := by simp only [F]; fun_prop
```

## Other Automation

### `omega` for integers
```lean
-- Before
have h : n ≥ 6 := by linarith
exact Nat.lt_of_succ_le h

-- After
omega
```

### `ring` for polynomials
```lean
-- Before
rw [mul_comm, add_assoc]
ring_nf

-- After
ring
```

### `aesop` for logic
```lean
-- Before
constructor
· intro ⟨h1, h2⟩
  exact ⟨h2, h1⟩
· intro ⟨h1, h2⟩
  exact ⟨h2, h1⟩

-- After
aesop
```

## Priority Order

1. Try `grind` first (especially for Finset/card/membership)
2. Try `fun_prop` for continuity/differentiability/measurability
3. Try `omega` for ℕ/ℤ arithmetic
4. Try `ring` for polynomial identities
5. Try `aesop` for logical goals
6. Fall back to manual proof only if all fail
