# Convert to Term Mode

**Pattern**: Replace tactic proofs with term-mode proofs.

**Stats**: 311 `exact` removals, 331 `by` removals in PR feedback data.

## Examples

### Example 1: by exact → direct
```lean
-- Before
theorem foo : P := by exact h

-- After
theorem foo : P := h
```

### Example 2: by rfl → rfl
```lean
-- Before
theorem foo : a = a := by rfl

-- After
theorem foo : a = a := rfl
```

### Example 3: intro + exact → lambda
```lean
-- Before
theorem foo : P → Q := by
  intro hp
  exact f hp

-- After
theorem foo : P → Q := fun hp => f hp
-- Or even shorter if f has right type:
theorem foo : P → Q := f
```

### Example 4: constructor + exact → anonymous constructor
```lean
-- Before
theorem foo : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- After
theorem foo : P ∧ Q := ⟨hp, hq⟩
```

### Example 5: intro + destruct + exact → pattern lambda
```lean
-- Before
theorem and_comm : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- After
theorem and_comm : P ∧ Q → Q ∧ P := fun ⟨hp, hq⟩ => ⟨hq, hp⟩
-- Or using library:
theorem and_comm : P ∧ Q → Q ∧ P := And.symm
```

### Example 6: Quotient induction
```lean
-- Before
@[simp]
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t length_append

-- After (eta-reduce)
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t fun _ _ => length_append
```

## Priority Order

1. `by exact h` → `h` (instant win)
2. `by rfl` → `rfl` (instant win)
3. Single `intro` + `exact` → lambda
4. `constructor` + multiple `exact` → anonymous constructor
5. Complex pattern matching → keep tactic mode if clearer
