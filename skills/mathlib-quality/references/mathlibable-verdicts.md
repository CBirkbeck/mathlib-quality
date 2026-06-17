# `/mathlibable` Verdicts — Definitions and Worked Examples

This reference is read by `/mathlibable` Phase 7 workers. It defines the five
verdict buckets, the canonical case studies (one per bucket), and the anti-patterns
to avoid when synthesising.

The Phase 7 verdict gate checks evidence pointers; this doc gives workers the
mental model of what good evidence looks like.

---

## Mathlib is Bourbaki 2.0 — the philosophy (READ THIS FIRST)

Mathlib is not a translation of textbooks into Lean. It is a redo of mathematics
using everything we know *now* about how mathematical structures fit together —
filters where 20th-century texts used sequences, typeclass hierarchies where
they used informal "let R be a ring"-style preambles, categorical universal
properties where they constructed objects explicitly, abstract topological
groups where Bourbaki used metric spaces.

**Consequences for `/mathlibable` verdicts:**

1. **"The literature has X" is not decisive.** A modernised reformulation that
   captures the same mathematics with contemporary tools is its own
   contribution. The classical version may exist; the *mathlib-idiomatic*
   version may not.

2. **Cost is not a verdict factor.** "Spending a lot more time on a new
   version of an old definition" is not a reason to downgrade YES-add-as-is or
   YES-but-generalise-first to NO-mathlib-has-it. EXPENSIVE generalisations
   are explicitly worth doing — that is the work mathlib is here to do.

3. **The "general form" Phase 3 finds may be the wrong target.** The
   literature-standard form is one anchor; the mathlib-idiomatic form is
   another. Phase 4c (the modern-idiom check) asks the second question.
   YES-but-generalise-first naturally covers "the literature says X, but
   modern mathlib would say Y — let's do Y".

4. **"Replace classical X with categorical/typed Y" is a legitimate verdict.**
   If Phase 5 finds mathlib's existing decl uses an older formulation (point-
   set topology where filters would be cleaner; sequences where a net would
   abstract better; concrete construction where a universal property would
   characterise) and the user's contribution is the modernisation, then the
   verdict is YES-add-as-is — **even though** mathlib has *something* by that
   name.

5. **What this is NOT a license for.** Modernisation has to be a real
   improvement in *mathematical organisation* — composes with more of
   mathlib, eliminates a redundancy, enables proofs that the old form
   blocked. "It looks cooler in category theory" is not enough. The Phase 7
   rationale must point at specific downstream consequences.

**Canonical cases of modernisation that worked:**

- **Modules, not vector spaces.** The classical hierarchy starts with vector
  spaces over a field; mathlib starts with modules over a (semi)ring. Every
  vector space theorem then specialises automatically, and module theorems
  serve scalar restriction / extension cleanly. Defining vector-spaces-as-
  distinct-from-modules would have been a wrong YES; defining the module
  framework was the right one.

- **Filters, not sequences.** Convergence in topology, limits, neighbourhoods,
  cluster points: classical texts use sequences (or nets) in metric spaces;
  mathlib uses filters everywhere. Reformulating a "limit of a sequence"
  result as a "limit along a filter" result was repeatedly the right move,
  even when an old sequence-only version already existed in literature.

- **`Submodule` vs ad-hoc subset predicates.** A submodule is a
  bundled-structure type, not "a set closed under operations". The latter
  works classically; the former composes with quotients, sums, intersections,
  and lattices throughout mathlib.

- **`MeasureTheory.OuterMeasure` + Carathéodory + topological-measure
  triple.** Classical measure theory builds measures from outer measures via
  Carathéodory and stops there; mathlib's triple (OuterMeasure → Measure →
  topological-measure-compatibility) was the right modernisation even though
  the underlying mathematics is decades old.

- **Categorical limits/colimits as universal-property bundles.** Classical
  texts construct products / coproducts / equalisers explicitly per
  category; mathlib has them as universal-property classes that specialise.

When the user's declaration is *itself* a modernisation move — even if the
content is classical — Phase 4c is the right place to flag it, and Phase 7
should *not* dismiss it as "literature already has X".

---

## The five verdicts

### 1. `YES-add-as-is`

The declaration is genuinely novel for mathlib, stated at the right level of
generality, and is non-trivial (composition from existing mathlib primitives does
not give it in ≤3 calls).

**When to pick:** Phase 4 verdict was MAXIMALLY GENERAL, Phase 5 found no hit
under either the user's form or the literature-standard form, Phase 6 was
NOT-COMPOSABLE.

**Required evidence:** Phase 3 lit table with ≥3 channels (or all 4 if bounded),
Phase 4 generality analysis explicitly concluding MAXIMALLY GENERAL, Phase 5
five-method search with all five methods attempted, Phase 6 composition check
explicitly NOT-COMPOSABLE.

**Common worker mistake:** declaring YES-add-as-is when Phase 4 actually noted
weakening opportunities but the worker called them "out of scope". If Phase 4
found weakenings, the verdict is YES-but-generalise-first, not YES-add-as-is.

### 2. `YES-but-generalise-first`

The result is novel for mathlib *in some form*, but the user's form is
strictly narrower than the literature-standard one, and the generalisation is
worth doing before opening a PR.

**When to pick:** Phase 4 verdict was STRICTLY NARROWER THAN STANDARD; Phase 5
found no hit under either form (the general form is also missing).

**Required evidence:** Phase 3 must have identified the more general form
explicitly; Phase 4 must propose the restatement (new signature); Phase 5 must
have searched both forms.

**Common worker mistake:** picking this when Phase 4's weakenings are
EXPENSIVE (the proof needs new ideas to generalise). For EXPENSIVE
generalisations the user might legitimately ship the narrower form first —
that's a BORDERLINE call ("is the more general form worth the work?") and
should be surfaced as a numbered question.

### 3. `NO-mathlib-has-it`

Mathlib already has the result, in identical or strictly more general form. The
user's form follows in ≤1 line.

**When to pick:** Phase 5 conclusion is "found in mathlib as <X>" with the
follows-in-≤1-line check passing.

**Required evidence:** Phase 5 must cite the existing mathlib decl by full
qualified name. The Phase 7 verdict must include a one-line `example : <our
statement> := <mathlib_call> ...` showing the derivation. Worker mistakes here
look like "mathlib has the general form so we don't need this" without showing
the specialisation actually works — Phase 5 must verify.

### 4. `NO-composable-from-mathlib`

Mathlib doesn't have the exact form, but it has the building blocks. A 1–3 line
composition of mathlib decls gives the result. No new lemma is justified.

**When to pick:** Phase 6 verdict was COMPOSABLE with a sketch ≤3 lines.

**Required evidence:** Phase 5 must list the mathlib building blocks; Phase 6
must show the composition sketch with mathlib decls cited by qualified name; the
sketch must be a real composition (per the heuristics table in Phase 6), not a
proof in disguise.

**Common worker mistake:** picking this for a 5-line composition or one
involving `by rw [...]; ring_nf; aesop` chains. If the composition is more than
3 mathlib calls, or requires real rewriting/automation steps to glue, it's a
proof, not a composition — the lemma is justified, and the verdict is one of
the YES options.

### 5. `BORDERLINE-needs-human`

The verdict depends on a judgment call the skill can't make alone:
mathematical taste, project policy, audience-narrow result, generality vs cost
tradeoff, naming conflicts with the project, etc.

**When to pick:** Phases 3–6 all completed cleanly, but synthesising them
requires a judgment the worker can't ground in the evidence.

**Required evidence:** all phases complete; a numbered list of ≤5 concrete
questions for the user, each answerable yes/no or with a short response.

**Common worker mistake:** picking BORDERLINE because the worker is uncertain,
without spelling out the questions. The numbered questions are the artifact —
no questions means the worker hasn't done the synthesis and should re-run
Phase 7.

---

## Canonical case studies

### Case 1 — `YES-add-as-is`

**User's declaration (project Lean file):**

```lean
/-- A locally compact Hausdorff group admits a unique left-invariant Radon measure
up to positive scaling. -/
theorem Haar.exists_unique (G : Type*) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] :
    ∃ μ : Measure G, IsHaarMeasure μ ∧ ∀ ν : Measure G, IsHaarMeasure ν → ∃ c > 0, ν = c • μ := …
```

**Phase 3 finds:** Haar's theorem is canonical (Wikipedia, nLab, Folland's *Real
Analysis*, every textbook on harmonic analysis or representation theory).
Standard form: locally compact Hausdorff topological group → unique left
Haar measure up to scaling. The user's form *is* the standard form.

**Phase 4:** MAXIMALLY GENERAL (Phase 3 confirms locally-compact-Hausdorff-
topological-group is the standard hypothesis cluster).

**Phase 5:** five methods searched; mathlib has `MeasureTheory.Measure.haarMeasure`
which constructs *a* Haar measure on a locally compact Hausdorff topological group,
but **the uniqueness statement** in this combined form (existence + uniqueness +
explicit scaling description) is NOT in mathlib as a single declaration.
Building blocks exist (`MeasureTheory.Measure.IsHaarMeasure`, the construction
lemma) but the packaged statement is not.

**Phase 6:** Composition would require unfolding `IsHaarMeasure` and assembling
multiple lemmas about regular measures — more than 3 calls and involves real
reasoning. NOT-COMPOSABLE.

**Verdict:** `YES-add-as-is`. Proposed mathlib location:
`Mathlib/MeasureTheory/Group/Haar.lean`. Next action: run `/cleanup` first
(mathlib PRs go through Phase-4 + simplify), then open the PR.

### Case 2 — `YES-but-generalise-first`

**User's declaration:**

```lean
/-- The translate of a continuous real-valued function on ℝ. -/
def continuousTranslate (s : ℝ) (f : C(ℝ, ℝ)) : C(ℝ, ℝ) :=
  ⟨fun x => f (x - s), by fun_prop⟩
```

**Phase 3 finds:** "Translate of a function" / "shift operator" is standard
across analysis and representation theory. The most general standard form
takes ANY function (not just continuous), and the underlying set can be ANY
additive group (not just ℝ). The standard symbol is τ_s or T_s; the
operation is just `(τ_s f)(x) = f(x - s)`. Wikipedia, Folland §8.2, every
harmonic analysis text. The continuity is preserved automatically when f is
continuous (translation is a homeomorphism), so the wrapped form is fine —
but defining it ONLY in the continuous case is a needless restriction.

**Phase 4:** STRICTLY NARROWER. Two weakening axes:
- `ℝ` → any `[AddGroup G]` (CHEAP — definition is the same)
- `C(ℝ, ℝ)` → any function `G → α` (TRIVIAL — preserves whatever structure f
  has via composition with subtraction)

Proposed restatement:

```lean
def Function.translate {G : Type*} [Sub G] (s : G) (f : G → α) : G → α := fun x => f (x - s)
```

with continuity / measurability / differentiability lemmas as separate API
(`Continuous.translate`, `Measurable.translate`, etc.).

**Phase 5:** searched mathlib for `Function.translate`, `translate`,
`shift`, `(·) ∘ (· - s)`, etc. — nothing exists with this name and signature.
Mathlib has many specific cases (`AddCircle`, periodic functions) but no
general `Function.translate`.

**Phase 6:** Composition of `(· - s)` with `f` is itself the definition; the
question is whether a separate named definition is worth it. For the
continuous case alone, the answer is "no — just inline". For the general
case, "yes — it's a named operation in the literature, has its own API
ecosystem (continuity, measurability, integrability laws), and is referenced
across analysis".

**Verdict:** `YES-but-generalise-first`. Next action: run `/generalise
continuousTranslate` to restate as `Function.translate` over `[AddGroup G]`,
then add the continuity/measurability lemmas as separate API, then open the
mathlib PR.

### Case 3 — `NO-mathlib-has-it`

**User's declaration:**

```lean
/-- The composition of two continuous functions is continuous. -/
lemma my_continuous_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (g : Y → Z) (f : X → Y) (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) := by
  intro U hU
  exact hf (hg hU)
```

**Phase 3:** "Composition of continuous functions" — every textbook. Standard
since Hausdorff. Maximally general form: any continuous map between topological
spaces.

**Phase 4:** MAXIMALLY GENERAL (matches the standard form).

**Phase 5:** mathlib has `Continuous.comp`:

```lean
theorem Continuous.comp {f : Y → Z} {g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f ∘ g)
```

Identical statement (with argument-order convention). Located at
`Mathlib/Topology/Continuous.lean`.

**Phase 6:** N/A — Phase 5 already found the exact thing.

**Verdict:** `NO-mathlib-has-it`. Existing decl: `Continuous.comp`. Our form
follows in 0 lines (just call `Continuous.comp`). Next action: delete
`my_continuous_comp` from the project; replace every call site with
`Continuous.comp` (note the dot-notation argument order: `hg.comp hf`).

### Case 4 — `NO-composable-from-mathlib`

**User's declaration:**

```lean
/-- The sum of two continuous integrable functions is continuous and integrable. -/
lemma my_sum_cont_integrable {f g : ℝ → ℝ}
    (hf_cont : Continuous f) (hg_cont : Continuous g)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    Continuous (f + g) ∧ Integrable (f + g) := by
  refine ⟨?_, ?_⟩
  · exact hf_cont.add hg_cont
  · exact hf_int.add hg_int
```

**Phase 3:** sum of continuous functions, sum of integrable functions — both
canonical, both in mathlib.

**Phase 4:** MAXIMALLY GENERAL (the form just packages two well-known facts).

**Phase 5:** mathlib has both `Continuous.add` and `Integrable.add` — both with
identical hypotheses to our individual facts.

**Phase 6:** the composition is exactly the proof body: `⟨hf_cont.add hg_cont,
hf_int.add hg_int⟩` — 1 call per conjunct, 2 calls total, ≤3.

COMPOSABLE.

**Verdict:** `NO-composable-from-mathlib`. Building blocks: `Continuous.add`,
`Integrable.add`. Composition: `⟨hf_cont.add hg_cont, hf_int.add hg_int⟩`.

Next action: delete `my_sum_cont_integrable`; replace every call site with the
two mathlib calls directly. (The `∧` packaging is itself a small anti-pattern
per `/cleanup` audit item 12 STRUCTURE: split conjunctions don't go in mathlib
as combined statements when the components are separate mathlib facts.)

### Case 5 — `BORDERLINE-needs-human`

**User's declaration:**

```lean
/-- For each prime ideal P of K's ring of integers, the local zeta sum at P. -/
def localZetaSum_chebotarev (K : Type*) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [P.IsMaximal] (s : ℝ) (hs : 1 < s) : ℝ := …
```

**Phase 3:** zeta sums at primes are classical in analytic number theory;
shapes vary widely (Dedekind, Artin, Hecke, …). The "_chebotarev" suffix
signals this is the variant used in Chebotarev-density proofs, not a
universally-named object.

**Phase 4:** unclear — the literature has many specialised local-sum
definitions tied to specific proofs. No single "standard form" emerges from
Phase 3.

**Phase 5:** mathlib has `NumberField.zetaSum` (different — global), and
several pieces of Dedekind / Artin L-function machinery, but not this
specific combination.

**Phase 6:** the formula can almost be assembled from existing primitives
but with non-trivial reindexing — not a clean composition.

**Verdict:** `BORDERLINE-needs-human`. Numbered questions:

  1. Is `localZetaSum_chebotarev` a public-facing object you want
     downstream consumers (other mathlib developments) to use, or is it
     internal to *this* Chebotarev proof?
  2. The suffix `_chebotarev` is unusual for mathlib — would the underlying
     definition (without the `_chebotarev` suffix) be reusable for other
     analytic-number-theory work, or is it really tied to this proof?
  3. Does the literature have a name for this exact form (Dedekind partial
     sum? Local Hecke sum?), or is it a project-specific bookkeeping
     definition?
  4. If we keep it project-local (don't PR), is the long name justified?
     A shorter name + a docstring would do.

Next action: user answers; re-run `/mathlibable` to resolve. Likely outcomes
based on the answers:
  - Internal + project-specific → drop from mathlib consideration entirely;
    rename to project-local convention.
  - Reusable + has a literature name → re-run with the literature name as a
    Phase-1 input; likely flips to YES-but-generalise-first.
  - Reusable + no literature name → consider proposing a name + PR; still
    BORDERLINE on naming.

---

## Anti-patterns when synthesising

### "I searched and didn't find it" without an artifact

Phase 3 / Phase 5 MUST produce the search tables. A worker who writes
"searched: nothing found" with no rows in the table has skipped the search,
not done it.

### Picking `YES-add-as-is` because the user wrote a docstring

The user's prose / docstring isn't evidence the form is novel. Phase 3 /
Phase 5 are the evidence.

### Picking `NO-mathlib-has-it` based on Loogle returning *something*

Loogle hits include partial matches, near-misses, and statements that share
some symbols but mean something different. Phase 5 MUST check the candidate
mathlib decl by reading its actual statement — not just citing the name.

### Treating literature absence as YES

If Phase 3 returns nothing after the protocol ran in full, the verdict is
**not** "novel, therefore add". An empty Phase 3 means the concept may be
too narrow / too specialised / too project-specific. Phase 7 should consider
BORDERLINE or NO-composable in that case, not YES.

### Generalising past what the proof supports

`YES-but-generalise-first` proposes restatements grounded in Phase 3. A
worker who proposes "let's just generalise from `ℝ` to any `CommRing`"
without Phase 3 confirming that's the literature's form is making it up.
The generalisation target comes from the literature, not from typeclass
hierarchy walking alone.

### Letting the verdict drive the search

The Phase 7 worker reads Phases 3–6 *as evidence*, not *as a constraint*.
If a Phase 3 finding contradicts the worker's expected verdict, the
verdict updates — not the artifact. Cherry-picking evidence to support a
pre-committed verdict is the failure mode this skill exists to prevent.
