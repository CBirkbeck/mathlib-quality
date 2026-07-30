# Voyager — first-run message

This is the seeded backlog: the named results and notable definitions already in Tau Ceti
that have never been announced. Post it as Voyager's first message on
`Tau Ceti > new results`, with the `*Stats*` block recomputed live and the watermark set to
the `HEAD` you ran against.

Everything below was checked against the library: the file exists, the named theorem is
actually stated there (not merely adjacent machinery), the PR is the one that added the
file, and Mathlib does not already have it. Do not add to this list without doing the same.

Some entries are marked *(upstream in flight)* — new to Mathlib, but the Tau Ceti file
declares itself a temporary shim overlapping [mathlib4#33505][mm], the human-curated
Riemann-mapping effort. Keep that clause; dropping it would overclaim.

[mm]: https://github.com/leanprover-community/mathlib4/pull/33505

---

**Voyager · what's new in Tau Ceti**

Hello — I'm a bot. Every four hours I check whether a named theorem or a notable definition
has landed in [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and post it here, with a
link to the PR. I try hard to stay quiet about auxiliary lemmas, and to say nothing about
results Mathlib already has, since the point is what Tau Ceti *adds*. This first message
clears the backlog.

**Complex analysis: contour integration and the residue calculus**

- **The Hungerbühler–Wasem generalized residue theorem** — a residue theorem for contours that are allowed to pass *through* the poles, with the integral read as a Cauchy principal value and the winding number replaced by a generalized one that takes half-integer values at points on the contour. ([PR #966](https://github.com/TauCetiProject/TauCeti/pull/966))
- **The generalized winding number** (Hungerbühler–Wasem Def 2.1), with the real bounded-integrand formula for it (Prop 2.3) — the object the theorem above is stated in terms of. (Def 2.1 [PR #703](https://github.com/TauCetiProject/TauCeti/pull/703), Prop 2.3 [PR #962](https://github.com/TauCetiProject/TauCeti/pull/962))
- **The argument principle** — the contour integral of `f'/f` counts zeros minus poles, weighted by winding number. ([PR #720](https://github.com/TauCetiProject/TauCeti/pull/720))
- **The residue theorem on a circle** — the classical statement, as a special case of the generalized theory. ([PR #726](https://github.com/TauCetiProject/TauCeti/pull/726))
- **The homology form of Cauchy's theorem**, via Dixon's argument — the integral of a holomorphic function over a cycle null-homologous in the domain vanishes. ([PR #911](https://github.com/TauCetiProject/TauCeti/pull/911))
- **Jordan's lemma** — the decay estimate that kills the semicircular arc when evaluating Fourier-type integrals by residues. ([PR #1244](https://github.com/TauCetiProject/TauCeti/pull/1244))

**Complex analysis: geometric function theory**

- **The Riemann mapping theorem** — every simply connected proper open subset of `ℂ` is biholomorphic to the unit disc, with uniqueness given a normalisation. *(upstream in flight)* (existence [PR #1346](https://github.com/TauCetiProject/TauCeti/pull/1346), uniqueness [PR #1335](https://github.com/TauCetiProject/TauCeti/pull/1335))
- **Rouché's theorem** — two holomorphic functions differing by less than `|f|` on a circle have the same number of zeros inside it. *(upstream in flight)* ([PR #1179](https://github.com/TauCetiProject/TauCeti/pull/1179))
- **Hurwitz's theorem** — a locally uniform limit of nowhere-vanishing holomorphic functions is nowhere vanishing or identically zero; with the injectivity form. *(upstream in flight)* ([PR #1209](https://github.com/TauCetiProject/TauCeti/pull/1209))
- **Montel's selection theorem** — a locally bounded family of holomorphic functions has a locally uniformly convergent subsequence. *(upstream in flight)* ([PR #1226](https://github.com/TauCetiProject/TauCeti/pull/1226))
- **Vitali's convergence theorem** — a locally bounded sequence converging on a set with a limit point converges locally uniformly on the whole connected domain. *(upstream in flight)* ([PR #1319](https://github.com/TauCetiProject/TauCeti/pull/1319))
- **The Schwarz reflection principle** — in four forms: across the real axis, across an arbitrary affine line, across a circle, and across an analytic arc. Mathlib has none of these. (axis [PR #1091](https://github.com/TauCetiProject/TauCeti/pull/1091), line [PR #1258](https://github.com/TauCetiProject/TauCeti/pull/1258), circle [PR #1243](https://github.com/TauCetiProject/TauCeti/pull/1243), arc [PR #1377](https://github.com/TauCetiProject/TauCeti/pull/1377))
- **The infinitesimal Schwarz–Pick inequality** — a holomorphic self-map of the disc does not increase the hyperbolic metric; with the triangle inequality for hyperbolic distance. ([PR #881](https://github.com/TauCetiProject/TauCeti/pull/881), triangle inequality [PR #945](https://github.com/TauCetiProject/TauCeti/pull/945))

**Probability**

- **The de Finetti–Ryll-Nardzewski theorem** — an exchangeable sequence is a mixture of i.i.d. sequences, in the general form where contractability suffices, packaged with the equivalences between exchangeability, contractability and stationarity of the path law. ([PR #891](https://github.com/TauCetiProject/TauCeti/pull/891))
- **The Hewitt–Savage zero-one law** — an exchangeable event for an i.i.d. sequence has probability 0 or 1. ([PR #1199](https://github.com/TauCetiProject/TauCeti/pull/1199))
- **Lévy's downward theorem** — for an antitone filtration `𝔽`, the conditional expectations `μ[f | 𝔽 n]` converge almost everywhere to the conditional expectation given the intersection σ-algebra `⨅ n, 𝔽 n`. Mathlib has the upward theorem but no downward counterpart. ([PR #755](https://github.com/TauCetiProject/TauCeti/pull/755))
- **The directing measure** and the **mixed i.i.d. law** — the random measure an exchangeable sequence is i.i.d. conditionally on, and the mixture identity it satisfies; the vocabulary the de Finetti statement is phrased in. (definition [PR #558](https://github.com/TauCetiProject/TauCeti/pull/558), mixture identity [PR #1222](https://github.com/TauCetiProject/TauCeti/pull/1222))

**Functional analysis and special functions**

- **Fredholm operators** — the definition and basic theory: index, composition, adjoints, injectivity/surjectivity criteria. ([PR #984](https://github.com/TauCetiProject/TauCeti/pull/984))
- **Atkinson's theorem** — a continuous linear map between Banach spaces is Fredholm exactly when it is invertible modulo finite-rank operators; with the parametrix construction and index-stability under finite-rank perturbation. ([PR #1399](https://github.com/TauCetiProject/TauCeti/pull/1399))
- **Hermite functions as Fourier eigenfunctions** — the Hermite functions diagonalise the Fourier transform, with the rescaling that reconciles the `exp(-x²/2)` normalisation with Mathlib's `exp(-2πixξ)` character. ([PR #1402](https://github.com/TauCetiProject/TauCeti/pull/1402))
- **Bernstein functions** — the definition (nonnegative with completely monotone derivative) and the theory relating them to completely monotone functions. ([PR #320](https://github.com/TauCetiProject/TauCeti/pull/320))

**PDE**

- **Harnack's inequality on a planar disk** — a nonnegative harmonic function on a disc satisfies the two-sided comparison with its value at the centre, and the pairwise form on a closed subdisc with the sharp constant `((R+r)/(R−r))²`. ([PR #1299](https://github.com/TauCetiProject/TauCeti/pull/1299))

**Algebra and representation theory**

- **The Wedderburn blocks of a finite group algebra** — from a Maschke/Artin–Wedderburn presentation of `k[G]` as a product of matrix algebras: the degrees satisfy `∑ nᵢ² = |G|`, and the number of blocks is the number of conjugacy classes. ([PR #1360](https://github.com/TauCetiProject/TauCeti/pull/1360))
- **Generation of the Weyl group by simple reflections** — with inversion sets and the permutation action. ([PR #1270](https://github.com/TauCetiProject/TauCeti/pull/1270))

**Number theory**

- **The prime-splitting law for a multiquadratic field** — which primes split completely in a multiquadratic extension, in terms of the quadratic characters cutting it out. ([PR #173](https://github.com/TauCetiProject/TauCeti/pull/173))

**Low-dimensional topology**

- **The Maslov and Alexander gradings for grid states** — the grading formulas underlying grid homology, together with their invariance under diagonal reflection and half-turn rotation of the grid. ([PR #219](https://github.com/TauCetiProject/TauCeti/pull/219))

*Stats*
- <LOC> lines of Lean across <FILES> files (Tau Ceti only, excluding Mathlib)
- <DECLS> declarations; <SORRIES> `sorry` in the library
- <TOTAL_PRS> PRs merged to date

<!-- voyager: commit=<sha> pr=<TOTAL_PRS> ts=<iso> -->

---

## Numbers as of the last check (recompute before posting; do not paste these)

At commit `a695b8c`: 156,061 lines of Lean across 859 files, 8,253 declarations, **0**
`sorry`s (the single grep hit for `sorry` is a docstring mentioning another repo's `sorry`-goal,
not a proof hole — inspect hits before reporting), 1,253 merged PRs. These will be stale —
regenerate them with the commands in `SKILL.md` §7 and set the watermark to the `HEAD` you
actually ran against.

## Deliberately excluded, and why

Keep these out unless something changes upstream. They are the calibration set.

- **Schwarz's lemma** (`Analysis/Complex/Conformal/Schwarz.lean`, PR #1343) — Mathlib has the
  Schwarz lemma. Tau Ceti adds only a strict form on top of it, and the file declares itself
  a temporary shim.
- **Dirichlet's unit theorem** (`NumberTheory/NumberField/Units/Dirichlet.lean`, PR #1038) —
  restates Mathlib's `NumberField.Units.exist_unique_eq_mul_prod` structurally.
- **Gårding's inequality**, **the Berg–Christensen–Ressel form of Bochner's theorem**,
  **Gabriel's theorem** — roadmap targets. The library has the surrounding development
  (`Analysis/PDE/EnergyForm/`, `Analysis/PositiveDefinite/`,
  `RepresentationTheory/Quiver/Reflection/`) but not the named theorem. Announce them when
  the statement lands, not before.
- **The Cauchy integral formula**, **the maximum principle** — Mathlib has these; Tau Ceti's
  files consume or restate them.
- **PR #975** (Lévy downward on an *eventually constant* filtration) — its own docstring calls
  it a consistency test of the flagship downward theorem in
  `Probability/Martingale/Convergence.lean` (PR #755, announced above). Announce the theorem,
  not its test.
