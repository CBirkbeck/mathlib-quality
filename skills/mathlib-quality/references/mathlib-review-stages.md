# The six stages of reviewing a mathlib PR (and of self-review)

A framework for reviewing a mathlib PR — ordered from most impactful
(most global) to least impactful (most local). Also applies to
**self-review** before opening a PR: `/cleanup` runs the local stages,
`/mathlibable` runs the global ones.

The ordering is load-bearing. Fixing a local issue (naming, formatting,
docstring wording) on a result that shouldn't be in mathlib at all is
wasted work. Answer the earlier questions first.

## Stage 1 — Do we want this mathematical result in mathlib?

- **Is this of interest to mathematicians?** Look for references in the
  published literature. A result nobody cites, publishes, or teaches is
  usually not mathlib-worthy.
- **Does this have applications outside of this PR?** A single-use
  helper that only supports the current PR probably isn't mathlib
  material. "We might not want every single OEIS sequence in mathlib."
- **Does this belong somewhere else?** The `Archive/` folder catches
  results that are proved but not part of the main library.
  `CombinatorialGames` / other satellite libraries catch domain-specific
  material. A downstream library the user maintains catches project-
  specific machinery. `NO-belongs-elsewhere` is a valid `/mathlibable`
  verdict — name the target destination.
- **Controversial: conditional results?** Results that depend on
  unproved conjectures (RH-conditional, GRH-conditional) are contested.
  Position must be stated explicitly in the rationale; not a
  self-resolving verdict.

## Stage 2 — Do we want the mathematical result in this generality?

**Mathlib generality** has two components:

1. **General enough to encompass every case mathematicians care about.**
   Convergence at a point + convergence at infinity → filters, even if
   nobody in the specific PR uses arbitrary filters. Localisation at a
   submonoid of a ring + Grothendieck-group localisation → arbitrary
   monoid actions.

2. **General enough to ease downstream development.** Ramification
   theory for non-Dedekind domains isn't a user-facing target, but
   having the general form lets us apply it without first proving the
   domain is Dedekind at each use site.

**Beware of false generalisations.** Not every widening is a
generalisation. `ModuleCat` weakened to `AddCommMonoid` is the wrong
def, not a generalisation of it. The check is: does the generalisation
preserve the intended mathematical content?

**When is sacrificing generality OK?**

- If the material is still useful after later refactoring to the
  correct generality (e.g. Hausdorff second-countable regular →
  metrisable using Urysohn is fine because it refactors cleanly once
  someone strengthens the metrisable theorem).
- If the correct generality is far away and shipping the specific case
  now unblocks important theorems (don't block quadratic reciprocity
  because it's a special case of class field theory).

## Stage 3 — Is the proof strategy optimal mathematically?

Area-specific and taste-driven, with one universal criterion:

> **We want the shortest path modulo what SHOULD be in mathlib, not
> modulo what IS currently in mathlib.**

Prefer:
- **Filters in topology** over ε-δ. `Tendsto` composition beats explicit
  neighbourhood-chasing.
- **Point-free arguments in algebra** over element-based ones. Argue
  about ideal / subring / submodule inclusions, not about elements
  satisfying predicates.
- **Universal properties** over explicit constructions. Characterise;
  don't build.

Q for the review: could this proof be shorter if mathlib had the API
it *should* have? If yes, that API gap is a separate contribution —
file it as its own PR / development ticket. Don't route around it in
the current proof.

## Stage 4 — Is the proof strategy executed correctly?

The first stage where you actually read the proof body. Per step ask:

- **Should this step be its own lemma?** If so, run Stages 1–3 on it
  recursively.
- **If too specific to be its own lemma**, is the local code missing
  automation that would make this easier?
- **Or is mathlib missing that automation?** Note it; consider filing
  a follow-up.

## Stage 5 — Are the results stated correctly in Lean?

For one mathematical result there are usually multiple syntactically-
different Lean statements. Pick the right one.

### Normal forms

**Each mathematical idea should have a unique canonical representation
in mathlib.** If a statement has n equivalent formalisms A, B, C, …, we
should not have O(n²) equivalence lemmas `A ↔ B`, `A ↔ C`, `B ↔ C`, …;
we should pick one normal form X and have O(n) lemmas `A ↔ X`, `B ↔
X`, `C ↔ X`.

Because of how `simp` works, **normal forms usually go on the RHS**.
That's why we write `X ↔ B` not `B ↔ X` when X is the normal form.

Check: does an equivalent form of your statement already exist in
mathlib? If yes, either (a) delete yours and use theirs, or (b) prove
`yours ↔ existing-normal-form` and let the existing form be canonical.

### Syntactic generality (mathematically-equivalent, easier to apply)

Sometimes a mathematically equivalent restatement is materially easier
to apply. Example: `Ideal.ResidueField.map` can be stated with the
"correct" homomorphism hypothesis (a bare `A →+*[R] B` with `hf : I =
Ideal.comap f.toRingHom J`) rather than the derived one — the correct
form composes better.

Check: is there a mathematically-equivalent restatement that would be
easier to apply at call sites? If yes, prefer it.

### Superfluous arguments and typeclasses

The linter catches most, but subtle ones survive. Example: an equiv
lemma stated with `[LocallyCompactSpace G]` when the proof never uses
local compactness — the typeclass is superfluous.

Check: does the proof essentially use each hypothesis and typeclass?
If not, drop the unused ones. This is more than the linter's
mechanical dead-argument check — it's about whether the *conclusion*
would hold without the hypothesis.

## Stage 6 — Are the results presented correctly?

Only when the PR structure is stable. Local questions:

- **Right file?** `#find_home` and `#min_imports` are the tools (watch
  for false positives). Files are cheap — the only cost of splitting
  is discoverability. Avoid `Def.lean`/`Lemmas.lean` splits inside the
  same folder.
- **New imports?** Check the GitHub Actions "Import changes for all
  files" summary. How much does downstream fan out? Is the modified
  file a leaf? Would an outside user expect this import when they
  import the file?
- **Variables organised nicely?** Implicitness of arguments, use of
  `variable` blocks, section structure.
- **Named correctly?** Follows mathlib conventions (`snake_case` for
  `Prop`, `lowerCamelCase` for data, `UpperCamelCase` for types;
  `_le_` / `_lt_` orientation; no forbidden abbreviations).
- **Documented clearly?** See "Documentation depth" below.
- **Formatting + suboptimal tactic usage:** `exact` instead of
  `refine`, `let` instead of `letI`, `cases` instead of `induction`,
  etc.

## Documentation depth (a Stage-6 sub-topic worth its own section)

**Mathlib is under-documented.** If unsure, err on the "more
documentation" side.

**Module docstrings** should include:
- Overview of what the file contains.
- Highlights of the key results.
- Overarching design decisions.
- References in the literature.

**Declaration docstrings** should include:
- Addendum to the statement (context the raw type doesn't convey).
- Tips + tricks when applying the lemma at call sites.
- Difference from similar-looking lemmas nearby.

**Reminder:** people reading the declaration docstring can also see the
statement (in files, in `docs`, in hovering tooltips). Don't just
paraphrase the statement — add value.

**Long proofs could (and arguably should) be documented** with `--`
comments explaining the strategy.

### Buzzphrases

- **Comments should explain _why_, not _what_.** The what is in the
  code.
- **Rules are meant to be breached. Breaches are meant to be
  documented.** A rule-breaking piece of code with a one-line comment
  explaining why is fine; without one, it's a bug waiting to happen.
- **The best comment is when it is unnecessary.** The code should be
  its own documentation where possible.
- **How to trick contributors into adding docstrings? Ask them good
  questions.** Reviews that ask "why?" invite docstrings.

## How this maps to our skills

| Yang stage | `/mathlibable` phase | `/cleanup` audit |
|---|---|---|
| 1. Want in mathlib? | Phases 1 + 3 (comprehend + lit search); Phase 7 verdict NO buckets can include "belongs-elsewhere" | — |
| 2. Right generality? | Phase 4 generality analysis; Phase 4c modern-idiom check; Phase 4c Q9 false-generalisation | Item 18 GENERALISE |
| 3. Proof strategy optimal? | Phase 4.6 proof-strategy-optimality | (out of scope; noted for future PR) |
| 4. Proof executed correctly? | Phase 5 mathlib composition + Phase 6 | Items 1–3 (LINT, HAVE, SET_OPTION); Item 4 SIMP squeeze |
| 5. Stated correctly? | Phase 5.5 statement-shape (normal form + syntactic generality + superfluous typeclasses) | Items 20 NORMAL-FORM + 21 SYNTACTIC-GENERALITY |
| 6. Presented correctly? | (out of scope — this is /cleanup's territory) | Items 5–10 (naming/packing/format/docstring); Item 22 IMPORT-FANOUT |

The two skills split the work: `/mathlibable` does Stages 1–5 (the
"should this exist" questions); `/cleanup` does Stages 5–6 (the
"is this stated + presented well" questions). Stage 5 is where they
overlap and reinforce.
