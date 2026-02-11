# Simplify `simp` Usage

**Pattern**: Replace verbose simp chains with simpler alternatives.

**Stats**: 311 `simp` removals, 323 simp_usage patterns in PR feedback data.

## Examples

### Example 1: simp chain → grind
```lean
-- Before
simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
  Finsupp.card_support_eq_one', pos_iff_ne_zero]

-- After
grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

### Example 2: simp + exact → simpa
```lean
-- Before
simp only [cons_head!_tail h]
exact l.tail.mem_cons_self (a := l.head!)

-- After
simpa [cons_head!_tail h] using l.tail.mem_cons_self (a := l.head!)
```

### Example 3: Remove trailing comma
```lean
-- Before
simp only [Function.comp_apply,]

-- After
simp only [Function.comp_apply]
```

### Example 4: fin_cases + simp → simp_all
```lean
-- Before
fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₈] at h ⊢

-- After
rcases this with h | h <;> simp_all [G₂]
```

### Example 5: simp at multiple locations → simp_all
```lean
-- Before
simp only [h] at ha hb hc ⊢

-- After
simp_all only [h]
```

### Example 6: rw + simp → simp only
```lean
-- Before
rw [foo_eq]
simp only [bar_eq]

-- After
simp only [foo_eq, bar_eq]
```

### Example 7: Non-terminal simp → simp only
```lean
-- Before (non-terminal, bad)
theorem foo : P := by
  simp
  exact h

-- After (explicit lemmas)
theorem foo : P := by
  simp only [relevant_lemma]
  exact h
```

## Rules

1. **Terminal simp**: Can stay unsqueezed (more maintainable)
2. **Non-terminal simp**: MUST use `simp only [...]`
3. **simp + exact**: Usually → `simpa`
4. **Multiple simp**: Often → `simp_all` or single `simp only`
5. **Complex simp chains**: Try `grind` first
