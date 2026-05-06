# Mathlib Search Guide

Mathlib contains over 100,000 theorems. Before proving something new, always search
for existing lemmas. This guide covers effective search strategies.

## Core Philosophy

**Always search before proving.** The likelihood of duplicating an existing lemma is high.

**Recommended workflow:**
1. Understand the mathematical requirement
2. Identify keywords and type signatures
3. Use multiple search strategies
4. Examine candidate files
5. Verify via `#check`
6. Import and use
7. Only prove independently if truly absent

## Search Strategies

### Strategy 1: Keyword-Based Search

Search using domain-specific mathematical terminology.

**Common keywords by domain:**

| Domain | Keywords |
|--------|----------|
| Analysis | `continuous`, `differentiable`, `integrable`, `limit`, `converge` |
| Topology | `compact`, `open`, `closed`, `connected`, `hausdorff` |
| Algebra | `ring`, `ideal`, `module`, `group`, `homomorphism` |
| Measure Theory | `measure`, `measurable`, `integrable`, `ae` (almost everywhere) |
| Probability | `probability`, `random`, `expectation`, `variance` |
| Order | `lattice`, `complete`, `directed`, `monotone` |

**Command-line techniques:**
```bash
# Find files containing keyword
find .lake/packages/mathlib -name "*.lean" -exec grep -l "keyword" {} \;

# Search with line numbers
grep -n "lemma.*keyword" file.lean

# Case-insensitive search
grep -in "keyword" file.lean
```

### Strategy 2: Type-Based Search

Search by the shape of the type signature.

**Examples:**
```lean
-- Looking for: α → β → α
-- Search for functions with that pattern in relevant files

-- Looking for: ∀ x : α, P x → Q x
-- Search for implications with that structure
```

### Strategy 3: Loogle (Type Signature Patterns)

[Loogle](https://loogle.lean-lang.org/) searches by type patterns, not names.

**Key syntax:**
- `?a`, `?b` for type variables
- `_` for wildcards
- Actual types for specific searches

**Examples:**
```
-- Find lemmas about List.map preserving properties
List.map ?f ?l = List.map ?g ?l

-- Find lemmas about addition commutativity
?a + ?b = ?b + ?a

-- Find coercions
(?a : ?B)

-- Find anything about Continuous and composition
Continuous (_ ∘ _)
```

**Important:** Simple name searches don't work well with Loogle. Use type patterns.

### Strategy 4: Naming Convention Search

Mathlib follows predictable naming patterns. Use these to guess lemma names.

**Patterns:**
```lean
-- Implications: conclusion_of_hypothesis
continuous_of_uniform
integrable_of_bounded

-- Equivalences: property_iff_characterization
compact_iff_finite_subcover
continuous_iff_seqContinuous

-- Properties: structure_property_property
AddGroup.neg_add_cancel
Ring.mul_comm

-- Operations: operation_property
add_comm
mul_assoc
```

### Strategy 5: File Organization Search

Mathlib is organized hierarchically. Find files by topic.

**Top-level directories:**
```
Mathlib/
├── Algebra/          -- algebraic structures
├── Analysis/         -- real/complex analysis
├── CategoryTheory/   -- category theory
├── Combinatorics/    -- combinatorics
├── Data/             -- data structures (List, Set, Finset)
├── FieldTheory/      -- field extensions
├── Geometry/         -- geometry
├── GroupTheory/      -- group theory
├── LinearAlgebra/    -- linear algebra
├── MeasureTheory/    -- measure and integration
├── NumberTheory/     -- number theory
├── Order/            -- order theory, lattices
├── Probability/      -- probability theory
├── RingTheory/       -- ring theory
├── SetTheory/        -- set theory
├── Tactic/           -- tactic extensions
└── Topology/         -- point-set topology
```

### Strategy 6: In-Editor Search

**Using `apply?` and `exact?`:**
```lean
-- Let Lean find applicable lemmas
example (h : P) : Q := by
  apply?  -- suggests lemmas that could work

example : P := by
  exact?  -- finds exact matches
```

**Using `#check`:**
```lean
-- Verify a lemma exists and see its type
#check add_comm
#check @add_comm  -- show implicit arguments
```

## Verification Methods

### Check the Type
```lean
#check lemma_name           -- basic signature
#check @lemma_name          -- with implicit arguments
#print lemma_name           -- full definition
```

### Test Compatibility
```lean
-- Create isolated test
example : my_goal := by
  exact suspected_lemma
  -- or
  apply suspected_lemma
```

### Check Imports
```lean
-- Verify the import is correct
#check SomeModule.lemma_name
```

## Import Guidelines

### Order
1. Mathlib imports first (alphabetical)
2. Project imports second (alphabetical)
3. Tactic imports last

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.ContinuousFunction.Basic

import MyProject.Definitions
import MyProject.Lemmas

import Mathlib.Tactic
```

### Common Domain Imports

**Analysis:**
```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

**Measure Theory:**
```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace
```

**Probability:**
```lean
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments
```

**Algebra:**
```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
```

**Topology:**
```lean
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.MetricSpace.Basic
```

### Common Tactic Imports
```lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
```

## When Lemmas Are Absent

If you can't find an existing lemma:

1. **Try alternative phrasings** - the lemma might exist under a different name
2. **Check for more general versions** - your specific case might be a corollary
3. **Look for building blocks** - combine existing lemmas
4. **Consult Lean Zulip** - the community can help locate obscure lemmas
5. **Mark provisional lemmas** - if you must prove it, note it may need mathlib inclusion

```lean
/-- TODO: Check if this exists in mathlib under a different name.
This lemma states... -/
theorem my_provisional_lemma : P := by
  ...
```

## Recognizing Mathlib Concepts in Disguise

Custom definitions often restate mathlib concepts. Common patterns:

### Discrete/Isolated Points

| Your Pattern | Mathlib Concept |
|--------------|-----------------|
| `∀ s ∈ S, ∃ ε > 0, ball s ε ∩ S = {s}` | `DiscreteTopology S.Elem` |
| `∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s ≠ s' → ε ≤ d(s,s')` | `Set.Pairwise S (fun x y => r ≤ dist x y)` |
| Points isolated in subspace | `discreteTopology_subtype_iff` |
| Neighborhoods intersect trivially | `𝓝[S \ {x}] x = ⊥` |

**Key files:** `Mathlib/Topology/DiscreteSubset.lean`, `Mathlib/Topology/Separation.lean`

### Finiteness of Intersections

| Your Pattern | Mathlib Concept |
|--------------|-----------------|
| Discrete ∩ Compact is finite | `IsCompact.finite` + `DiscreteTopology` |
| Closed discrete ∩ Compact | `IsClosed.isDiscrete`, `IsCompact.inter_left` |
| Finite preimage | `Set.Finite.preimage_embedding` |

**Key files:** `Mathlib/Topology/Compactness/Compact.lean`

### Separation Properties

| Your Pattern | Mathlib Concept |
|--------------|-----------------|
| Minimum pairwise distance | `Finset.inf'` on `(S ×ˢ S).filter (·.1 ≠ ·.2)` |
| Positive separation | `Set.pairwiseDisjoint` with balls |
| ε-separated set | `Metric.pairwise_dist` |

### Poles and Residues

| Your Pattern | Mathlib Concept |
|--------------|-----------------|
| Simple pole at z₀ | Check `Mathlib/Analysis/Analytic/Meromorphic.lean` |
| Residue computation | `Mathlib/Analysis/Complex/Residue.lean` |
| Laurent series | `Mathlib/Analysis/Analytic/Laurent.lean` |

### When Mathlib Uses More General Types

Mathlib often states results more generally:

```lean
-- Your version (specific):
lemma my_lemma (f : ℂ → ℂ) (hf : Continuous f) : P f

-- Mathlib version (general):
lemma mathlib_lemma {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : P f
```

**Solution:** Specialize by applying with explicit type arguments:
```lean
-- Use mathlib version for your case:
example (f : ℂ → ℂ) (hf : Continuous f) : P f := mathlib_lemma f hf
```

## Anti-Patterns

**Don't:**
- Prove basic facts without searching first
- Give up after one search strategy
- Assume a lemma doesn't exist because you can't find it quickly
- Import more than you need
- Rely on transitive imports
- Define concepts that exist under different names in mathlib

**Do:**
- Try multiple search strategies
- Ask on Zulip if unsure
- Use `apply?` and `exact?` liberally
- Keep imports minimal and explicit
- Check if your "custom" definition is a mathlib concept

## Five-Method Exhaustive Search (the rule for `/cleanup`'s MATHLIB audit)

The MATHLIB item in `/cleanup`'s per-declaration audit (Phase 4) requires this five-method
search. A worker that concludes "not in mathlib" without trying all five has skipped the
check.

| # | Method | When it shines |
|---|---|---|
| **A** | **Lean-Finder** (https://huggingface.co/spaces/delta-lab-ai/Lean-Finder) — AI-powered, type signatures + natural language | Use first. Most powerful single tool. |
| **B** | **Loogle** (`lean_loogle`) — type-pattern queries | When you know the rough shape: `IsCompact → DiscreteTopology → Finite` |
| **C** | **LeanSearch** (`lean_leansearch`) — natural language | "discrete topology inherited by subset" / "compact + discrete is finite" |
| **D** | **Grep mathlib source** (`grep -rn ... .lake/packages/mathlib/`) | When you have a guess at the name (e.g., `IsCompact.finite`) |
| **E** | **Name-pattern search** (`lean_local_search`) — partial names | `discrete`, `isolated`, `finite_of`, `_left`, `_right`, `_of_subset` variants |

If a method genuinely doesn't apply (e.g., grepping mathlib source isn't available in this
environment), record `n/a: <reason>` — not blank. The audit must be auditable.

## Six Strict Rules for Mathlib Replacement

When `/cleanup`'s Phase-4 MATHLIB check finds (or doesn't find) an equivalent, apply these
rules:

**Rule 1 — No wrapper lemmas.** If a lemma just combines 1–3 mathlib calls, **delete it**.
Use mathlib directly at every call site.

```lean
-- ❌ Wrapper lemma
lemma my_finite [DiscreteTopology S] (hK : IsCompact K) : (S ∩ K).Finite := ...

-- ✓ Use mathlib directly where needed
theorem main ... := by
  haveI := DiscreteTopology.of_subset ‹_› Set.inter_subset_left
  have := hK.finite this
```

**Rule 2 — Exhaustive search.** All five methods (A–E above) before concluding "not in
mathlib".

**Rule 3 — Check auxiliary lemmas.** Often what you need is `Foo.of_subset`,
`Foo.inter_left`, `foo_of_bar` — search variants, not just the canonical name.

**Rule 4 — Use type classes, not custom predicates.** Replace explicit hypotheses with
mathlib type-class arguments.

```lean
-- ❌ Custom predicate
lemma foo (h : ∀ x ∈ S, ∃ ε > 0, ball x ε ∩ S = {x}) : P := ...

-- ✓ Mathlib type class
lemma foo [DiscreteTopology S] : P := ...
```

**Rule 5 — Delete, don't simplify.** When you find a mathlib equivalent, delete your local
copy entirely; update call sites to use mathlib directly. Don't keep your version as a
thin wrapper around mathlib.

**Rule 6 — Document mathlib usage.** In the module docstring, note which mathlib lemmas
the file relies on, so future readers don't recreate them locally:

```lean
/-!
## Mathlib lemmas used directly
* `IsCompact.finite` + `DiscreteTopology.of_subset` for finiteness on discrete subsets.
-/
```

## Common Mathlib Equivalents (lookup table)

When `/cleanup`'s MATHLIB check finds a candidate, it usually falls into one of these
buckets. Use this table to spot the pattern.

### Discrete / isolated points

| Custom pattern | Mathlib equivalent |
|---|---|
| `∀ s ∈ S, ∃ ε > 0, ball s ε ∩ S = {s}` | `DiscreteTopology` on the subtype + `discreteTopology_subtype_iff` |
| `∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ d(s, s')` | `Set.Pairwise` with the distance |
| Points isolated in a subspace | `DiscreteTopology.of_subset` |
| Recover ball isolation from `[DiscreteTopology S]` | `exists_ball_inter_eq_singleton_of_mem_discrete` |

### Finiteness

| Custom pattern | Mathlib equivalent |
|---|---|
| Discrete ∩ Compact is finite | `IsCompact.finite` (with `DiscreteTopology` on the subtype) |
| Finite preimage of singleton | `Set.Finite.preimage` |
| Subset of finite is finite | `Set.Finite.subset` |

### Separation

| Custom pattern | Mathlib equivalent |
|---|---|
| Minimum pairwise distance | `Finset.inf'` over pairs |
| Positive separation | `Set.pairwiseDisjoint` |

### Bounded / bornology

| Custom pattern | Mathlib equivalent |
|---|---|
| `∃ M, ∀ x ∈ S, ‖x‖ ≤ M` | `Bornology.IsBounded` or `Metric.Bounded` |
| Bounded ↔ contained in a ball | `Metric.isBounded_iff_subset_closedBall` |

This table is non-exhaustive; it captures patterns that came up repeatedly in PR review.
Add to it via `/teach` when you find another recurring custom-vs-mathlib pair.
