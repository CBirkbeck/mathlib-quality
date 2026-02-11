# Mathlib Naming Conventions

This is the authoritative naming guide for mathlib contributions, based on the official
[leanprover-community naming guide](https://leanprover-community.github.io/contribute/naming.html).

## File Names

Files use `UpperCamelCase`. Rare exceptions exist for specifically lowercased objects (e.g., `lp.lean`).

## Capitalization Rules

**CRITICAL: The convention depends on what the declaration RETURNS:**

| Declaration | Returns | Convention | Example |
|-------------|---------|------------|---------|
| `lemma`/`theorem` | `Prop` | `snake_case` | `add_comm`, `continuous_of_bounded` |
| `def` | Data (ℂ, ℝ, Set, etc.) | `lowerCamelCase` | `cauchyPrincipalValue`, `residueAtPole` |
| `structure`/`inductive` | Type | `UpperCamelCase` | `AddCommGroup`, `ModularForm` |

**Key distinction:**
```lean
-- lemma/theorem (returns Prop) → snake_case
lemma continuous_of_bounded : Continuous f := ...
theorem norm_le_of_mem_ball : ‖x‖ ≤ r := ...

-- def returning data → lowerCamelCase
def cauchyPrincipalValue (f : ℝ → ℂ) : ℂ := ...
def fundamentalDomain : Set ℂ := ...

-- WRONG: def returning data with snake_case
def cauchy_principal_value : ℂ := ...  -- Should be cauchyPrincipalValue
```

**Additional entities:**
| Entity | Convention | Example |
|--------|------------|---------|
| Types/Props (structure/inductive) | `UpperCamelCase` | `AddCommGroup`, `TopologicalSpace` |
| Functions (non-Prop return) | `lowerCamelCase` | `toNat`, `ofInt` |
| Other terms | `lowerCamelCase` | `myValue`, `defaultConfig` |
| Structure fields | Follow rules above | `field_name` or `fieldName` |
| Inductive constructors | Follow rules above | `nil`, `cons`, `zero` |

### Special Cases

**UpperCamelCase in snake_case context:**
```lean
-- Convert to lowerCamelCase
iidProjectiveFamily  -- not IIDProjectiveFamily
topologicalSpace_induced  -- for lemma about TopologicalSpace
```

**Acronyms:** Apply casing as a group based on first character:
```lean
-- In UpperCamelCase context
HTTPServer  -- not HttpServer (all caps)
-- In lowerCamelCase context
httpServer  -- not hTTPServer (all lower for first word)
```

## Spelling

**Use American English:**
```lean
-- Good
Factorization
Localization
FiberBundle
normalize

-- Bad (British)
Factorisation
Localisation
FibreBundle
normalise
```

## Symbol Naming

### Logic Symbols

| Symbol | Name |
|--------|------|
| `∨` | `or` |
| `∧` | `and` |
| `→` | `imp` / `of` (in theorem names) |
| `↔` | `iff` |
| `¬` | `not` |
| `∃` | `exists` / `bex` (bounded) |
| `∀` | `forall` / `ball` (bounded) |

### Set Operations

| Symbol/Operation | Name |
|------------------|------|
| `∈` | `mem` |
| `∪` | `union` |
| `∩` | `inter` |
| `⋃` (indexed) | `iUnion` |
| `⋂` (indexed) | `iInter` |
| `⋃₀` (set of sets) | `sUnion` |
| `⋂₀` (set of sets) | `sInter` |
| `\` | `sdiff` |
| `ᶜ` | `compl` |
| `{x | P x}` | `setOf` |
| `{a}` | `singleton` |

### Algebra

| Symbol/Operation | Name |
|------------------|------|
| `0` | `zero` |
| `+` | `add` |
| `-` (unary) | `neg` |
| `-` (binary) | `sub` |
| `1` | `one` |
| `*` | `mul` |
| `^` | `pow` |
| `/` | `div` |
| `•` | `smul` |
| `⁻¹` | `inv` |
| `∣` | `dvd` |
| `∑` | `sum` |
| `∏` | `prod` |

### Order Relations

| Symbol | Name |
|--------|------|
| `<` | `lt` |
| `>` | `gt` |
| `≤` | `le` |
| `≥` | `ge` |
| `⊔` | `sup` |
| `⊓` | `inf` |
| `⨆` | `iSup` |
| `⨅` | `iInf` |
| `⊥` | `bot` |
| `⊤` | `top` |

## Variable Conventions

Standard order for universe-polymorphic types:

```lean
-- Universes
variable {u v w : Level}

-- Types
variable {α β γ δ ε : Type*}  -- then ι, κ for index types

-- Propositions
variable {p q r s : Prop}

-- Natural numbers
variable {m n k l : ℕ}

-- Integers
variable {a b c : ℤ}  -- also for ring elements

-- Functions
variable {f g h : α → β}

-- Hypotheses (in theorem statements)
-- h, h₁, h₂, h'  (generic)
-- hf (about f), hx (about x), hab (about a and b)
-- ha (a ∈ s), hcont (continuity), hinj (injectivity)
```

### Mathematical Type Variables

| Variable | Purpose |
|----------|---------|
| `G`, `H` | Groups |
| `R`, `S` | Rings |
| `K`, `𝕜` | Fields |
| `E`, `F` | Vector spaces / Normed spaces |
| `M`, `N` | Modules / Monoids |
| `X`, `Y` | Topological spaces |

## Theorem Naming Pattern

### The "Conclusion of Hypotheses" Pattern

Name theorems by describing what they prove, with hypotheses noted using `_of_`:

```lean
conclusion_of_hypothesis1_of_hypothesis2
```

**Examples:**
```lean
add_comm             -- commutativity of addition (the conclusion)
mul_one              -- multiplication by one equals itself
div_self             -- division by self equals one

-- With hypotheses
add_pos_of_pos_of_pos    -- sum is positive IF both addends are positive
mul_ne_zero_of_ne_zero   -- product nonzero IF factors nonzero
continuous_of_uniform    -- continuous IF uniformly continuous
```

### Abbreviations in Names

| Full | Abbreviation | Example |
|------|--------------|---------|
| positive | `pos` | `add_pos` |
| negative | `neg` | `mul_neg` |
| non-positive | `nonpos` | `nonpos_of_neg` |
| non-negative | `nonneg` | `nonneg_of_sq` |

### Structural Suffixes

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_aux` | Helper/auxiliary lemma | `foo_aux`, `bar_step_aux` |
| `_iff` | If and only if | `mem_union_iff` |
| `_of_` | Implication (hypothesis) | `pos_of_ne_zero` |
| `_left` / `_right` | Left/right version | `mul_comm_left` |
| `_self` | Applying to itself | `add_self`, `div_self` |
| `_zero` / `_one` | Involving 0 or 1 | `mul_zero`, `pow_one` |
| `_neg` / `_inv` | Involving negation/inverse | `add_neg_self` |
| `_injective` | Injectivity (unidirectional) | `add_left_injective` |
| `_inj` | Injectivity (bidirectional) | `add_left_inj` |
| `_surjective` / `_surj` | Surjectivity | `Int.toNat_surjective` |
| `_bijective` / `_bij` | Bijectivity | `Equiv.bijective` |
| `_ext` | Extensionality | `funext`, `Set.ext` |
| `_ext_iff` | Extensionality iff | `Set.ext_iff` |
| `_def` | Definition unfolding | `Set.mem_def` |
| `_eq` | Equality version | `add_sub_cancel_eq` |
| `_ne` | Inequality version | `add_ne_zero` |

### Property Prefixes

| Prefix | Meaning | Example |
|--------|---------|---------|
| `is` | Boolean predicate | `IsUnit`, `IsEmpty` |
| `mk` | Constructor | `mkAddCommGroup` |
| `of` | Conversion from | `ofNat`, `ofInt` |
| `to` | Conversion to | `toNat`, `toInt` |

### Structural Lemma Patterns

```lean
-- Injectivity
f_injective    -- f is injective (Prop)
f_inj          -- f a = f b ↔ a = b

-- Induction/recursion
T.induction_on  -- induction principle
T.recOn         -- recursion principle
T.induction     -- alternative form
T.rec           -- alternative form

-- Extensionality
T.ext           -- extensionality lemma
T.ext_iff       -- extensionality as iff
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
-- Show derivation in name
instance instAddCommGroupProd [AddCommGroup α] [AddCommGroup β] :
    AddCommGroup (α × β) := ...

instance instModulePoly [CommRing R] : Module R (Polynomial R) := ...
```

## Helper Lemma Naming

**Helper lemmas use `_aux` suffix and should be `private`:**

```lean
-- Good: main theorem is public, helpers are private with _aux
theorem main_theorem : P := main_theorem_aux₁ ▸ main_theorem_aux₂

private theorem main_theorem_aux₁ : Q := by ...
private theorem main_theorem_aux₂ : R := by ...

-- For multi-step helpers, number them
private lemma foo_aux₁ : ... := ...
private lemma foo_aux₂ : ... := ...
private lemma foo_aux₃ : ... := ...
```

**When to use `_aux`:**
- Lemmas only used to prove one main result
- Intermediate steps in a complex proof
- Technical lemmas not useful elsewhere

**When NOT to use `_aux`:**
- API lemmas intended for reuse
- Standard properties (use standard naming instead)
- Lemmas that might be useful in other files

## Namespace Organization

```lean
-- Operations in type namespace
namespace Nat
  def add : Nat → Nat → Nat := ...
  theorem add_comm : ∀ a b, add a b = add b a := ...
end Nat

-- Allows dot notation
#check Nat.add_comm
#check n.add m  -- if n : Nat
```

## Common Abbreviations

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
| `continuous` | `cont` (in names) |
| `differentiable` | `diff` (in names) |
| `measurable` | `meas` (in names) |

**When NOT to abbreviate:**
- Don't abbreviate when it hurts clarity
- New or uncommon terms should be spelled out
- When in doubt, be explicit
