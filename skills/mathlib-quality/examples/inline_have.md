# Inline `have` Blocks

**Pattern**: Remove single-use `have` blocks by inlining the value directly.

**Stats**: 77 `have` removals in PR feedback data.

## Examples

### Example 1: Simple inline
```lean
-- Before
theorem foo : Q := by
  have h := f x
  exact g h

-- After
theorem foo : Q := g (f x)
```

### Example 2: Inline with rwa
```lean
-- Before
theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' := mem_cons_self l.head! l.tail
  rwa [cons_head!_tail h] at h'

-- After
theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  simpa [cons_head!_tail h] using l.tail.mem_cons_self (a := l.head!)
```

### Example 3: Chain of have → composition
```lean
-- Before
theorem foo : A → D := by
  intro ha
  have hb := f ha
  have hc := g hb
  exact h hc

-- After
theorem foo : A → D := h ∘ g ∘ f
```

### Example 4: have + exact → direct
```lean
-- Before
theorem foo (h : P → Q) (hp : P) : Q := by
  have hq : Q := h hp
  exact hq

-- After
theorem foo (h : P → Q) (hp : P) : Q := h hp
```

### Example 5: obtain + exact → grind
```lean
-- Before
obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
exact ⟨a, rfl⟩

-- After
grind
```

## When to Inline

- `have` used exactly once → always inline
- `have` used 2 times → inline if expression is short
- `have` used 3+ times → keep the `have`

## When NOT to Inline

- Expression is very long (>40 chars)
- Same value used multiple times
- Improves type inference to name it
