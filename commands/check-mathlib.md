# /check-mathlib - Find Mathlib Equivalents

Systematically check definitions and lemmas against mathlib to avoid duplication.

## Usage

```
/check-mathlib [file_path] [--definition name] [--lemma name]
```

If no specific name given, analyzes all definitions and lemmas in the file.

## Why This Matters

**Avoiding duplication is CRITICAL for mathlib contributions.** Before creating any:
- Definition
- Lemma/Theorem
- Notation
- Instance

You MUST search mathlib extensively. Mathlib results are often:
- More general than what you need
- Under different names
- In unexpected locations
- Stated with different type classes

## Workflow

### Step 1: Inventory Declarations

For each definition/lemma in the file, extract:
1. The name
2. The type signature
3. Key type classes/structures used
4. Mathematical meaning in plain language

### Step 2: Multi-Strategy Search (EXHAUSTIVE - ALL METHODS)

**CRITICAL: Use ALL search methods before concluding something isn't in mathlib.**

For EACH declaration, run ALL of these searches:

#### A. Lean-Finder (AI-Powered Search) - USE FIRST, BEST TOOL
```
https://huggingface.co/spaces/delta-lab-ai/Lean-Finder
```
Supports BOTH type signatures AND natural language. Most powerful search tool available.

**Type signature queries:**
- `IsCompact s → DiscreteTopology s → s.Finite`
- `DiscreteTopology s → t ⊆ s → DiscreteTopology t`
- `∀ x ∈ S, ∃ ε > 0, ball x ε ∩ S = {x}`

**Natural language queries:**
- "discrete topology inherited by subset"
- "compact set with discrete topology is finite"
- "closed subset of compact is compact"
- "ball isolation characterizes discrete topology"

#### B. Type-Based Search (Loogle)
```bash
# Search by type pattern
lean_loogle "Type_Pattern"

# Examples:
lean_loogle "DiscreteTopology → Set.Finite"
lean_loogle "IsCompact → DiscreteTopology → Finite"
lean_loogle "∀ s ∈ S, ∃ ε > 0, _"
lean_loogle "Metric.ball _ _ ∩ _ = {_}"
```

#### C. Natural Language Search (LeanSearch)
```bash
# Search by mathematical concept
lean_leansearch "isolated points in metric space"
lean_leansearch "finite intersection compact discrete"
lean_leansearch "discrete topology inherited by subset"
```

#### D. Grep Mathlib Source Directly
```bash
# Search for key function names
grep -rn "DiscreteTopology.of_subset" .lake/packages/mathlib/
grep -rn "IsCompact.finite" .lake/packages/mathlib/
grep -rn "def.*yourConceptName" .lake/packages/mathlib/
```

#### C. Name Pattern Search
```bash
# Search for related names
lean_local_search "discrete"
lean_local_search "isolated"
lean_local_search "finite_of"
lean_local_search "pairwise"
```

#### D. Direct Mathlib Exploration
```bash
# Check likely mathlib locations
grep -r "pattern" ~/.elan/toolchains/*/lib/lean4/library/
# Or use the Glob/Grep tools on mathlib source
```

### Step 3: Analyze Potential Matches

For each potential mathlib match:

1. **Compare types** - Is mathlib version more general?
2. **Check hypotheses** - What assumptions does mathlib require?
3. **Verify applicability** - Can you specialize mathlib's version?
4. **Check imports** - What import is needed?

### Step 4: Replacement Decision

For each declaration, decide:

| Status | Action |
|--------|--------|
| **Exact match** | Delete local, use mathlib import |
| **More general in mathlib** | Delete local, specialize mathlib |
| **Partial match** | Keep local but build on mathlib |
| **No match** | Keep local, consider mathlib PR |

### Step 5: Refactor

When replacing with mathlib:
1. Update imports
2. Replace definition/lemma with mathlib's version
3. Update all call sites
4. Verify compilation

## Common Mathlib Equivalents

### Discrete/Isolated Points
| Custom Pattern | Mathlib Equivalent |
|----------------|-------------------|
| `∀ s ∈ S, ∃ ε > 0, ball s ε ∩ S = {s}` | `DiscreteTopology` on subtype |
| `∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ d(s,s')` | `Set.Pairwise` with distance |
| Points isolated in subspace | `discreteTopology_subtype_iff` |

### Finiteness
| Custom Pattern | Mathlib Equivalent |
|----------------|-------------------|
| Discrete ∩ Compact is finite | `IsCompact.finite` with `DiscreteTopology` |
| Finite preimage of singleton | `Set.Finite.preimage` |

### Separation
| Custom Pattern | Mathlib Equivalent |
|----------------|-------------------|
| Minimum pairwise distance | `Finset.inf'` over pairs |
| Positive separation | `Set.pairwiseDisjoint` |

## Output Format

```markdown
## Mathlib Check Report for [filename]

### Definitions Checked

#### `myDefinition`
- **Type**: `X → Y`
- **Searches performed**:
  - Loogle: `X → Y` → Found `Mathlib.X.Y.foo`
  - LeanSearch: "description" → Found `bar_baz`
- **Mathlib equivalent**: `Mathlib.X.Y.foo`
- **Generalization**: Mathlib uses `[TopologicalSpace X]` instead of `MetricSpace`
- **Action**: Replace with `import Mathlib.X.Y` and use `foo`

#### `anotherDef`
- **Searches performed**: [list]
- **Mathlib equivalent**: None found
- **Action**: Keep local, consider mathlib PR

### Lemmas Checked

#### `myLemma`
- **Statement**: `P → Q`
- **Searches performed**: [list]
- **Mathlib equivalent**: `Mathlib.A.B.pq_of_something`
- **Note**: Mathlib version requires extra hypothesis `H`
- **Action**: Add hypothesis or prove `H` as separate lemma

### Summary
- Definitions: X checked, Y have mathlib equivalents
- Lemmas: A checked, B have mathlib equivalents
- Recommended imports: [list]
```

## Example: Checking Discrete Definition

**Custom definition:**
```lean
def myDiscrete (S : Set ℂ) : Prop :=
  ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖
```

**Search 1: Loogle**
```bash
lean_loogle "∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → _ ≤ dist s' s"
```

**Search 2: LeanSearch**
```bash
lean_leansearch "discrete set metric space isolated points"
```

**Search 3: Concept search**
```bash
lean_local_search "DiscreteTopology"
lean_local_search "isolated"
```

**Finding:** Mathlib has `DiscreteTopology` which, when applied to a subtype, gives exactly this property via `discreteTopology_subtype_iff`.

**Replacement (AGGRESSIVE):**
```lean
-- BEFORE: Custom condition as explicit hypothesis
lemma foo (hS : ∀ s ∈ S, ∃ ε > 0, ball s ε ∩ S = {s}) : P := ...

-- AFTER: Mathlib type class as instance argument
lemma foo [DiscreteTopology S] : P := ...
```

**Recovering properties when needed:**
```lean
-- Get ball isolation from DiscreteTopology:
obtain ⟨ε, hε_pos, hε_ball⟩ := exists_ball_inter_eq_singleton_of_mem_discrete hs
```

## Critical Rules (STRICT)

### Rule 1: NO WRAPPER LEMMAS
If a lemma just combines 1-3 mathlib calls, **DELETE IT**. Use mathlib directly at call sites.

```lean
-- FORBIDDEN: wrapper lemma
lemma my_finite [DiscreteTopology S] (hK : IsCompact K) : (S ∩ K).Finite := ...

-- CORRECT: use mathlib directly where needed
theorem main ... := by
  haveI := DiscreteTopology.of_subset ‹_› Set.inter_subset_left
  have := hK.finite this
```

### Rule 2: EXHAUSTIVE SEARCH
Use ALL search methods before concluding something isn't in mathlib:
1. Lean-Finder (https://huggingface.co/spaces/delta-lab-ai/Lean-Finder)
2. Loogle (type patterns)
3. LeanSearch (natural language)
4. Grep mathlib source
5. Check auxiliary lemmas (`.of_subset`, `_left`, `_right`)

### Rule 3: CHECK AUXILIARY LEMMAS
Often what you need is a variant. Search for:
- `Foo.of_subset`, `Foo.inter`, `Foo.union`
- `foo_left`, `foo_right`
- `foo_of_bar` (implications)

### Rule 4: USE TYPE CLASSES
Replace custom conditions with mathlib type classes:
- `(h : ∀ x, isolated x)` → `[DiscreteTopology S]`
- `(h : bounded S)` → `[Bornology S]` or `Metric.Bounded`

### Rule 5: DELETE, DON'T SIMPLIFY
When you find a mathlib equivalent:
- **Don't** simplify your lemma to call mathlib
- **Do** delete your lemma entirely
- **Do** update call sites to use mathlib directly

### Rule 6: DOCUMENT MATHLIB USAGE
In the module docstring, document which mathlib lemmas to use:
```lean
/-!
## Mathlib Lemmas to Use Directly
* `IsCompact.finite` + `DiscreteTopology.of_subset` for finiteness
-/
```
