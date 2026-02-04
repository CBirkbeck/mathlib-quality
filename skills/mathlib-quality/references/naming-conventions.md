# Mathlib Naming Conventions

## General Principles

### Case Conventions
| Entity | Convention | Example |
|--------|------------|---------|
| Lemmas/theorems | `snake_case` | `add_comm`, `mul_one` |
| Types/structures | `UpperCamelCase` | `AddCommGroup`, `TopologicalSpace` |
| Namespaces | `UpperCamelCase` | `Nat`, `List`, `Set` |
| Type classes | `UpperCamelCase` | `Ring`, `Module`, `Continuous` |
| Inductive constructors | `lowerCamelCase` | `nil`, `cons`, `zero`, `succ` |

### Type Variables
Standard order for universe-polymorphic types:
```lean
-- Types: α, β, γ, δ, ε (then ι, κ, λ, μ)
-- Propositions: p, q, r, s
-- Natural numbers: m, n, k, l
-- Integers: a, b, c (also for ring elements)
-- Functions: f, g, h

variable {α β γ : Type*}
variable {m n k : ℕ}
variable {f g : α → β}
```

### Hypothesis Names
```lean
-- Generic: h, h₁, h₂, h'
-- Descriptive: hf (about f), hx (about x), hab (about a and b)
-- Membership: ha (a ∈ s), hb (b ∈ t)
-- Properties: hP (proof of P), hcont (continuity), hinj (injectivity)

example (h₁ : P) (h₂ : Q) (hf : Continuous f) (ha : a ∈ s) : R := ...
```

## Theorem Naming Pattern

### The "Conclusion of Hypotheses" Pattern
Name theorems by: `conclusion_of_hypothesis1_hypothesis2`

```lean
-- The conclusion is the main result
-- Hypotheses are conditions needed

add_comm           -- commutativity of addition
mul_one            -- multiplication by one
div_self           -- division by self

-- With hypotheses
add_pos_of_pos_of_pos     -- sum is positive if both addends are positive
mul_ne_zero_of_ne_zero    -- product nonzero if factors nonzero
continuous_of_uniform     -- continuous if uniformly continuous
```

### Structural Suffixes

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_iff` | If and only if | `mem_union_iff` |
| `_of_` | Implication (from hypothesis) | `pos_of_ne_zero` |
| `_left` / `_right` | Left/right version | `mul_comm_left` |
| `_self` | Applying to itself | `add_self`, `div_self` |
| `_zero` / `_one` | Involving 0 or 1 | `mul_zero`, `pow_one` |
| `_neg` / `_inv` | Involving negation/inverse | `add_neg_self` |
| `_injective` / `_inj` | Injectivity | `add_left_injective` |
| `_surjective` / `_surj` | Surjectivity | `Int.toNat_surjective` |
| `_bijective` / `_bij` | Bijectivity | `Equiv.bijective` |
| `_ext` | Extensionality | `funext`, `Set.ext` |
| `_def` | Definition unfolding | `Set.mem_def` |
| `_eq` | Equality version | `add_sub_cancel_eq` |
| `_ne` | Inequality version | `add_ne_zero` |

### Property Prefixes

| Prefix | Meaning | Example |
|--------|---------|---------|
| `is_` | Boolean predicate | `isUnit`, `isEmpty` |
| `mk_` | Constructor | `mk_add_comm_group` |
| `of_` | Conversion from | `ofNat`, `ofInt` |
| `to_` | Conversion to | `toNat`, `toInt` |

### Namespace Organization

```lean
-- Operations in type namespace
namespace Nat
  def add : Nat → Nat → Nat := ...
  theorem add_comm : ∀ a b, add a b = add b a := ...
end Nat

-- Lemmas about operations
namespace Nat
  -- Basic lemmas
  theorem add_zero : a + 0 = a := ...
  theorem zero_add : 0 + a = a := ...

  -- Commutativity/associativity
  theorem add_comm : a + b = b + a := ...
  theorem add_assoc : (a + b) + c = a + (b + c) := ...
end Nat
```

## Specific Naming Patterns

### Set Operations
```lean
Set.mem_union           -- a ∈ s ∪ t ↔ ...
Set.mem_inter           -- a ∈ s ∩ t ↔ ...
Set.subset_union_left   -- s ⊆ s ∪ t
Set.union_subset        -- s ∪ t ⊆ u ↔ ...
Set.empty_union         -- ∅ ∪ s = s
Set.union_empty         -- s ∪ ∅ = s
```

### Function Properties
```lean
Function.Injective.comp   -- composition preserves injectivity
Function.Surjective.comp  -- composition preserves surjectivity
Function.LeftInverse      -- g ∘ f = id
Function.RightInverse     -- f ∘ g = id
```

### Algebraic Structures
```lean
-- Zero and one
zero_add, add_zero
one_mul, mul_one
zero_mul, mul_zero

-- Inverses
add_neg_cancel, neg_add_cancel
mul_inv_cancel, inv_mul_cancel

-- Distributivity
mul_add, add_mul
left_distrib, right_distrib
```

### Order Relations
```lean
le_refl, le_trans, le_antisymm
lt_irrefl, lt_trans, lt_asymm
le_of_lt, lt_of_le_of_lt
max_le, le_max_left, le_max_right
min_le_left, min_le_right, le_min
```

## Instance Naming

### Standard Pattern: `inst` + TypeClass + Type
```lean
instance instAddCommMonoidNat : AddCommMonoid Nat := ...
instance instRingInt : Ring Int := ...
instance instTopologicalSpaceReal : TopologicalSpace Real := ...
```

### Derived Instances
```lean
-- Use descriptive names showing derivation
instance instAddCommGroupProd [AddCommGroup α] [AddCommGroup β] :
    AddCommGroup (α × β) := ...

instance instModulePoly [CommRing R] : Module R (Polynomial R) := ...
```

## Abbreviations

### Common Abbreviations
| Full | Abbreviation |
|------|--------------|
| `commutative` | `comm` |
| `associative` | `assoc` |
| `distributive` | `distrib` |
| `symmetric` | `symm` |
| `transitive` | `trans` |
| `reflexive` | `refl` |
| `injective` | `inj` |
| `surjective` | `surj` |
| `bijective` | `bij` |
| `equivalence` | `equiv` |
| `homomorphism` | `hom` |
| `isomorphism` | `iso` |
| `continuous` | `cont` |
| `differentiable` | `diff` |
| `measurable` | `meas` |

### Avoid Abbreviating
- Don't abbreviate when it hurts clarity
- New or uncommon terms should be spelled out
- When in doubt, be explicit
