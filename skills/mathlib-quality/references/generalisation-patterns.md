# Generalisation Patterns

Catalogue of mechanical assumption-weakenings used by `/generalise`. These are the
candidates the skill tries first, before falling back to literature search.

## How the catalogue is used

1. For each hypothesis on a declaration, look up the catalogue entry.
2. The catalogue gives one or more weaker forms.
3. `/generalise` tries each weakening (substitutes it, runs `lean_diagnostic_messages`).
4. If the weaker form compiles, it's a candidate; if it changes meaning or breaks the
   proof, drop it.

A weakening is **safe** if it produces a strictly more general statement that the original
is a special case of. The catalogue marks each entry as `safe` or `requires-restatement`.

## Type-class weakenings (algebra)

| Strong | Weaker (in dependency order) | Safe? |
|---|---|---|
| `CommRing R` | `Ring R` (drops commutativity) | safe — try if proof never uses `mul_comm` |
| `CommRing R` | `CommSemiring R` (drops subtraction) | safe — try if proof never uses subtraction or `Neg` |
| `Ring R` | `Semiring R` | safe — try if no subtraction |
| `Ring R` | `NonAssocRing R` | requires-restatement — only if associativity unused |
| `Field K` | `DivisionRing K` | safe — try if `mul_comm` unused |
| `Field K` | `CommRing K` + `[IsField K]` (predicate-class form) | requires-restatement — useful when the user wants to factor through `IsField` |
| `LinearOrderedField K` | `LinearOrderedCommRing K` | safe — try if division unused; otherwise stay |
| `LinearOrderedCommRing` | `OrderedCommRing` | safe — try if `lt`/`le` decidability unused |
| `IsDomain R` (with `Ring R`) | `NoZeroDivisors R` | safe |
| `Algebra R A` | `Module R A` (algebra map / `IsScalarTower` unused) | safe — try if neither algebra map nor multiplicativity is needed |

## Type-class weakenings (analysis)

| Strong | Weaker | Safe? |
|---|---|---|
| `NormedField K` | `NormedRing K` (or `NormedDivisionRing K`) | safe |
| `NormedSpace 𝕜 E` | `Module 𝕜 E` + `IsBoundedSMul 𝕜 E` | requires-restatement |
| `InnerProductSpace 𝕜 E` | `NormedAddCommGroup E` + `NormedSpace 𝕜 E` | safe — only if inner product unused |
| `CompleteSpace E` | (drop) | safe — try if completeness unused |
| `CompactSpace X` | `LocallyCompactSpace X` | requires-restatement — usually needs sub-statement |
| `CompactSpace X` | `IsCompact (univ : Set X)` | safe — value-level form, sometimes useful |
| `T2Space X` | `T1Space X` or `T0Space X` | safe — most uses of T2 only need uniqueness of limits |
| `MetricSpace X` | `PseudoMetricSpace X` (no separation), or `UniformSpace X` | safe / requires-restatement |
| `EMetricSpace X` | `PseudoEMetricSpace X` | safe |

## Hypothesis weakenings (point vs global)

| Global hypothesis | Pointwise weaker form | Safe? |
|---|---|---|
| `Continuous f` | `ContinuousAt f x` (when proof only uses continuity at one point) | safe |
| `ContinuousOn f s` | `ContinuousWithinAt f s x` | safe |
| `Differentiable 𝕜 f` | `DifferentiableAt 𝕜 f x` | safe |
| `DifferentiableOn` | `DifferentiableWithinAt` | safe |
| `Measurable f` | `AEMeasurable f μ` (when an `ae`-version is needed) | requires-restatement |
| `Integrable f μ` | `IntegrableOn f s μ` | safe — when integration is over `s` |
| `Monotone f` | `MonotoneOn f s` | safe |
| `Bornology.IsBounded` (whole space) | `IsBounded` of a subset | safe |

## Hypothesis weakenings (strict → weak)

| Strict | Weaker | Safe? |
|---|---|---|
| `0 < x` | `0 ≤ x` (when proof only needs non-negativity) | safe |
| `x ≠ 0` | `0 ≤ x` or `x ∈ s` (depending on need) | usually requires-restatement |
| `x = y` | `x ≤ y` and `y ≤ x` (le_antisymm form) — rarely a generalisation, more an unbundling | n/a |
| `Injective f` | `LeftInverse g f` (with explicit retract) | requires-restatement |
| `Bijective f` | `Injective f` or `Surjective f` (depending on which direction is used) | safe |
| `IsOpen s` | `s ∈ 𝓝 x` (filter-based, pointwise) | requires-restatement |

## Concrete → abstract

| Concrete | Abstract | Notes |
|---|---|---|
| `ℕ` | `WellFoundedLT α` / `LinearOrder α + …` | Useful when only induction structure is used |
| `ℤ` | `CommRing R` (or stronger as needed) | If only ring properties are used |
| `ℚ` | `Field K` (or `LinearOrderedField K`) | If only field axioms used |
| `ℝ` | `LinearOrderedField K`, `NormedField K`, `NormedLinearOrderedField K`, `RCLike K` | Pick the weakest typeclass that supports what's used |
| `ℂ` | `RCLike K` (works for both ℝ and ℂ uniformly) | Frequently the right choice |

## Universe weakening

| Specific | Generalised | Notes |
|---|---|---|
| `Type` | `Type*` | universe polymorphism — always safe to try |
| `Type u` | `Type*` | when no universe constraint is required |
| Cross-universe constraints | Use universe parameters | requires care; `lean_diagnostic_messages` will catch breakage |

## Unbundling

When a hypothesis bundles two facts (`Bijective f = Injective f ∧ Surjective f`),
inspect which half is actually used:

| Bundled hypothesis | Unbundled candidates |
|---|---|
| `Bijective f` | `Injective f` or `Surjective f` |
| `Equiv α β` | `α ≃ β` is the same; what's needed often is just `α → β` plus a one-sided inverse |
| `OrderIso α β` | `OrderEmbedding α β` + surjectivity, or just monotone bijection |
| `IsClosedEmbedding f` | `Embedding f` + `IsClosed (range f)` |

## Drop-test (the cheapest weakening)

For *every* hypothesis, try simply removing it. If `lean_diagnostic_messages` is still
clean, the hypothesis was unused — drop it permanently.

The `unusedArguments` linter catches some of these but not all (e.g., a hypothesis used
only inside a `simp` lemma that fires the same way without it).

## Big-change patterns (require user judgement)

These almost always change the public API and need explicit approval:

| Pattern | What changes |
|---|---|
| Real → general field | `(x : ℝ)` parameters become `[Field K] (x : K)` everywhere; the lemma name often changes (`real_*` → drop the prefix or generalise) |
| Concrete construction → abstract structure | A definition expressed via `ℕ`-indexed sums becomes one indexed by an arbitrary `Fintype`/`Finset` |
| Bundled → unbundled API | Splitting `Bijective` lemmas into `_injective` / `_surjective` halves |
| Add a typeclass for what was a hypothesis | `(h : ∀ x ∈ S, ∃ ε > 0, …)` → `[DiscreteTopology S]` (also lives in `mathlib-search.md`) |

## Inversion check: when the proof outruns the statement

The catalogue above operates on the *statement* — typeclass weakenings,
hypothesis drops, pointwise restatements. There is one important class of
generalisation it misses: when the statement names a concrete object but the
proof body, after the first one or two unfolding rewrites, never mentions
that object again. The real content is an abstract theorem about whichever
properties the concrete object happens to satisfy; the concrete version is
a one-line corollary.

`/generalise` Phase 5c.1 (mandatory inversion check) and `/mathlibable` Phase
4c Q8 (concrete-via-abstract) both run the same diagnostic.

### The adversarial diagnostic

1. **Grep the proof body** for every named-object identifier in the
   statement (exclude the statement line itself).
2. **Count occurrences.** If a named identifier appears in 0 or 1 lines
   after the first `rw [<unfolding lemma>]`, the proof from that point
   forward is working with abstractions only.
3. **If the diagnostic fires**: propose the abstract restatement; the
   original becomes a one-line corollary.

### Pattern

```lean
-- Original (statement-concrete, proof-abstract)
theorem foo_bar : <P concrete_witness> := by
  rw [<concrete_witness>_unfolding]
  -- ... proof here, never mentions `concrete_witness` again ...

-- Abstract restatement (the real content)
theorem foo_bar_of_abstract
    (x : <abstract type>) (h1 : <abstract hyp>) (h2 : <abstract hyp>) :
    <P x> := by
  rw [<abstract unfolding>]
  -- ... the same proof, transferred verbatim ...

-- Original as one-line corollary
theorem foo_bar : <P concrete_witness> :=
  foo_bar_of_abstract concrete_witness <evidence h1> <evidence h2>
```

### When the diagnostic does NOT fire

- The named-object identifier really does appear throughout the proof —
  the proof uses specific properties peculiar to that object.
- The "abstract" version would require hypotheses no other object actually
  satisfies — the concrete version is the abstract version (a generality
  of one).
- The statement has no concrete named object (purely typeclass-parametric
  from the start).

In any of these cases, record NOT-APPLICABLE with the reason — but record
it; the inversion check is mandatory.

### Why this is different from the typeclass-weakening table

The catalogue tables ask "can this hypothesis be weaker?" The inversion
check asks "is this theorem a corollary of a more general one whose proof
would be the same?" Theorems with no hypotheses (the catalogue cannot
weaken nothing) are exactly where the inversion check is most useful —
the right generalisation is restatement against an abstract witness, not
hypothesis weakening.

## Adding to this catalogue

When `/generalise` finds a weakening that isn't here, record it via `/teach` or a learnings
entry (`type: user_teaching`, with `pattern_tags` mentioning `generalisation`). After
review, append a row to one of the tables above so the next run picks it up
automatically.
