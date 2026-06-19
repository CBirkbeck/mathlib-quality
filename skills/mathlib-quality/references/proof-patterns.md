# Proof Golf Patterns

Data-driven golfing rules extracted from 3,772 merged mathlib4 PRs,
7,273 before/after reviewer suggestions, and 14,063 reviewer comments.

## Workflow

Two phases: file-wide scan first, then theorem-by-theorem. Verify each
edit compiles before moving on.

### Phase 1: File-wide

1. **Extract helpers for duplicated proof skeletons** — the single
   highest-ROI technique. If 2+ proofs differ only in the lemma applied,
   extract the skeleton into a parameterized helper. Also look for `wlog`
   (symmetric cases), `suffices` (symmetric case splits), and
   `by_cases` hoisting.

2. **Replace with mathlib or derive from neighbours** — use `exact?`,
   `apply?`, or Loogle with the type signature. Reviewers' most common
   comment: "there's already a lemma for this."

3. **Check mechanical patterns** — run through the instant-win table
   below to catch low-hanging fruit across the file.

### Phase 2: Theorem-by-theorem

Work through each declaration. Apply the rules below in order.

---

## The Cardinal Rule: Terminal vs Nonterminal `simp`

This is the single most enforced rule in mathlib code review (282+ reviewer comments).

- **Terminal `simp` must NOT be squeezed.** Leave it as `simp` or `simp [lemmas]`.
  Squeezing terminal simp adds maintenance cost for no benefit.
- **Nonterminal `simp` MUST be squeezed** to `simp only [...]`.
  Use `simp?` to find the minimal lemma set.
- **`simp; rfl` counts as terminal** — no need to squeeze.
- **`simp_all` is preferred** over `simp_all only` for closing goals.

```lean
-- WRONG: squeezing terminal simp
theorem foo : a + 0 = a := by simp only [add_zero]

-- RIGHT: terminal simp left unsqueezed
theorem foo : a + 0 = a := by simp

-- RIGHT: nonterminal simp squeezed
theorem foo : a + 0 = a ∧ True := by
  simp only [add_zero]  -- nonterminal: must squeeze
  trivial
```

---

## Instant Wins (always apply, zero risk)

| Before | After | Occurrences |
|--------|-------|-------------|
| `:= by exact term` | `:= term` | very common |
| `rw [h]; exact e` | `rwa [h]` | common |
| `simp [...]; exact h` | `simpa [...] using h` | 86 |
| `ext x; rfl` | `rfl` | common |
| `simp; rfl` | `simp` | 71 |
| `constructor; exact a; exact b` | `exact ⟨a, b⟩` | common |
| `apply f; exact h` | `exact f h` | common |
| `by_contra h; push_neg at h` | `by_contra!` | common |
| `intro x; exact f x` | `fun x => f x` or `f` | 25 |
| `have h := x; exact h` | `exact x` | 21 |
| `apply X; intro y; ...` | `refine X fun y => ?_` | common |

---

## Tactic Priority Ladder

When closing a goal, try these in order (most automated first):

| Priority | Tactic | Use for | Notes |
|----------|--------|---------|-------|
| 1 | `grind` | General closing | Subsumes many tactic chains (104 examples) |
| 2 | `simp` / `simpa` | Simplification + closing | #1 tactic in mathlib reviews |
| 3 | `aesop` | Logic, membership, set goals | 93 examples |
| 4 | `fun_prop` | Continuity, differentiability, measurability | 80 examples; use `(disch := grind)` |
| 5 | `positivity` | `0 < x`, `0 ≤ x` goals | 60 examples |
| 6 | `gcongr` | Monotonicity, congruence in inequalities | 67 examples |
| 7 | `lia` (preferred) / `omega` | Nat/Int linear arithmetic | Use `lia` as the default; fall back to `omega` only when `lia` fails |
| 8 | `norm_num` / `norm_cast` | Numeric computation, cast goals | 14 examples |
| 9 | `ring` / `ring_nf` | Polynomial equalities | |
| 10 | `field_simp; ring` | Equalities with denominators | 6 examples |
| 11 | `linarith` / `nlinarith` | Linear/nonlinear arithmetic | `nlinarith [hint]` for nonlinear |
| 12 | `decide` / `native_decide` | Decidable propositions | 12 examples; use `decide +kernel` for large |
| 13 | `linear_combination` | Ring goals needing hypotheses | Try when `ring` fails but hyps available |

---

## High-Volume Patterns (data-backed)

### 1. Inline single-use `have` blocks (highest-volume technique)

The most common reviewer suggestion (109 "remove have" comments, 94 "inline/merge" comments).

```lean
-- BEFORE
have h := foo x
exact h.bar

-- AFTER
exact (foo x).bar
```

```lean
-- BEFORE
have hf : Continuous f := by fun_prop
exact hf.comp hg

-- AFTER
exact (by fun_prop : Continuous f).comp hg
-- or even better:
exact fun_prop |>.comp hg
```

**Caveat:** `grind` and `omega` are context-sensitive — keep standalone
`have` blocks when inlining causes timeouts.

### 2. `grind` subsumption (104 examples)

`grind` often subsumes preceding tactics — try deleting what comes before:

```lean
-- These all simplify to just `grind`:
rw [h]; grind          →  grind     -- when h is a local hyp
congr 1; grind         →  grind
simp; grind            →  grind
simp [lemmas] <;> grind →  grind [lemmas]
rw [ht]; omega         →  grind     -- when ht is a substitution

-- grind handles symmetry internally:
grind [lemma.symm]     →  grind [lemma]
```

### 3. `simpa ... using` (86 examples)

When `simp` simplifies the goal enough that the proof finishes with
`exact h` or `assumption`:

```lean
-- BEFORE
simp only [mem_inf, orthogonal_toSubmodule_eq]
exact fun hx ho => inner_self_eq_zero.1 (ho x hx)

-- AFTER
simpa using fun hx ho => inner_self_eq_zero.1 (ho x hx)
```

### 4. `fun_prop` for function property proofs (80 examples)

Replaces manual continuity/differentiability/measurability chains:

```lean
-- BEFORE
exact (continuousAt_fst.sub continuousAt_snd.norm).div
  (continuousAt_fst.sub continuousAt_const) (by linarith)

-- AFTER
exact by fun_prop (disch := grind)
```

### 5. `gcongr` for inequality congruence (67 examples)

Replaces manual monotonicity reasoning in `calc` blocks:

```lean
-- BEFORE
calc _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by
  apply add_le_add_right
  apply div_le_div_of_nonneg_right
  apply mul_le_mul_of_nonneg_right ...

-- AFTER
calc _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
```

### 6. `positivity` for positivity goals (60 examples)

```lean
-- BEFORE
mul_le_mul_iff_right (show (0 : ℝ) < 2 * π from by linarith [pi_pos])

-- AFTER
mul_le_mul_iff_right (by positivity)
```

### 7. `aesop` for structure fields and simple logic (93 examples)

```lean
-- BEFORE
zero' := by intro x; simp [map_zero]
add' := by intro x y; simp [map_add]
neg' := by intro x; simp [map_neg]

-- AFTER
zero' := by aesop
add' := by aesop
neg' := by aesop
```

### 8. `wlog` for symmetric cases (8 examples, high savings)

Eliminates one branch entirely when cases are symmetric:

```lean
-- BEFORE
rcases le_or_gt 0 x with h | h
· <proof for x ≥ 0>
· <symmetric proof for x < 0>

-- AFTER
wlog! h : 0 ≤ x
· simpa [T_eval_neg, abs_mul] using @this n (-x) (by grind) (by grind)
· exact one_le_eval_T_real n (abs_of_nonneg h) ...
```

### 9. `linear_combination` for algebraic goals with hypotheses

Try on EVERY proof that ends in `ring` or `ring_nf` when hypotheses
are in context. Closes goals that `ring` can't when hypotheses are needed.

```lean
-- BEFORE
linear_combination (norm := (push_cast; ring_nf)) h₁ + (n + 2) * h₂

-- AFTER (when simpler combination exists)
linear_combination (norm := (push_cast; ring_nf)) h
```

### 10. Squeeze bare `simp` in nonterminal position (20 examples)

```lean
-- BEFORE (nonterminal simp — fragile)
simp
exact foo

-- AFTER
simp only [relevant_lemma₁, relevant_lemma₂]
exact foo
```

---

## API Shortcuts

| Verbose | Short | When |
|---------|-------|------|
| `continuity` / `measurability` | `fun_prop` | Always prefer `fun_prop` |
| `field_simp` then `ring` | `field_simp; ring` | Denominators + ring eq |
| `push_cast; ring` | `push_cast; ring` | ℝ→ℂ or ℕ→ℤ cast goals |
| `apply foo; exact bar` | `exact foo bar` | Direct application |
| `calc a ≤ b := h1; _ ≤ c := h2` | `le_trans h1 h2` | Two-step calc |
| `refine ⟨..., ?_, ?_⟩ <;> grind` | — | Close multiple similar goals |
| `simp only [def] at h ⊢` | — | Replace `unfold + rw` chains |
| `(by fun_prop : Continuous _).foo` | — | Inline continuity proof |

---

## Anti-Patterns (from reviewer feedback)

### Don't do these

| Anti-pattern | Why | Fix |
|-------------|-----|-----|
| `by exact term` | No-op tactic wrapper | `:= term` |
| Squeeze terminal `simp` | Maintenance cost, no benefit | Leave as `simp` |
| Semicolons in multiline proofs | Banned in mathlib style | Separate lines |
| `repeat` in proofs | Unpredictable behavior | Explicit steps |
| Define data in tactic mode | Poor practice | Use term mode |
| Unfold APIs manually | Fragile | Use named lemmas |
| `erw` when `rw` works | Heavier than needed | Try `rw` first |
| Redundant `show` | Goal is already right type | Remove it (60 examples) |
| Massive `simp only [...]` lists | Hard to maintain | Use `simp` (if terminal) or find better API |

### Don't use these when better tactics exist

| Don't use | Use instead | When |
|-----------|-------------|------|
| `omega` | `lia` | New code (mathlib is migrating) |
| `continuity` | `fun_prop` | Always |
| `measurability` | `fun_prop` | Always |
| Manual `mono` | `gcongr` | Inequality congruence |
| Manual case splits on decidable props | `decide` | Small computations |
| `by_contra; push_neg` | `by_contra!` | Always |
| `push_neg at h` | `push Not at h` | `push_neg` is deprecated |
| `show X from by ...` | `show X by ...` | `from` is redundant when followed by `by` |
| `show X` to rewrite goal | `change X` | `linter.style.show` enforces this when goal actually changes |

---

## Extract API Before Bulling Through Ugly Proofs

When a target proof is more than ~3 ugly lines, or requires structural massaging,
**that is itself a signal that API is missing**. Stop, name the missing API in one
sentence, add it as a public lemma (with `@[simp]` if applicable), then retry the
target proof.

### Signals of missing API

| Signal | What it usually means |
|--------|----------------------|
| `rw [show A = B from rfl]` | A definitional equality should be a named `_eq_` lemma |
| `have hfun := by rw …; rfl` | The `rfl` exit is hiding a missing congruence/coercion lemma |
| `cases ha : foo.order with \| top => simp \| coe a => …` | Missing case-eliminator over the wrapper type |
| `refine X ?_ ?_ <;> exact typeclass_machinery _` | The typeclass step belongs in a single API lemma |
| Three-step round-trips through `IsCuspForm`-style wrappers | Missing coe lemma that lets the surrounding context use the underlying object directly |
| Repeated cast juggling (`push_cast`, `norm_cast`, manual `Int.coe_…`) at multiple call sites | Missing `_coe` API at the wrapper level |

### Concrete before/after (PR #38993)

Reviewer-rejected — bulls through with `rfl` exits and manual typeclass machinery:

```lean
lemma qExpansion_eq_qExpansion_discriminant_mul (f : ModularForm 𝒮ℒ k)
    (hcusp : (qExpansion 1 f).coeff 0 = 0) :
    qExpansion 1 f = qExpansion 1 discriminant *
      qExpansion 1 (CuspForm.discriminantEquiv (toCuspForm f hcusp)) := by
  have hfun : (f : ℍ → ℂ) = discriminant *
      (CuspForm.discriminantEquiv (toCuspForm f hcusp) : ℍ → ℂ) := by
    rw [discriminant_mul_discriminantEquiv]
    rfl
  rw [hfun, ← CuspForm.coe_discriminant]
  refine UpperHalfPlane.qExpansion_mul ?_ ?_ <;>
    exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL
```

Reviewer-accepted — extract one API lemma at the right generality first:

```lean
-- New public API lemma — works for ANY ModularFormClass, not just this target.
protected lemma qExpansion_mul_coe {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] :
    qExpansion h ((⇑f * ⇑g : ℍ → ℂ)) = qExpansion h f * qExpansion h g :=
  qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

-- Target proof now reads as the mathematics, not the plumbing.
lemma qExpansion_eq_qExpansion_discriminant_mul (f : ModularForm 𝒮ℒ k)
    (hcusp : (qExpansion 1 f).coeff 0 = 0) :
    qExpansion 1 f = qExpansion 1 discriminant *
      qExpansion 1 (CuspForm.discriminantEquiv (toCuspForm f hcusp)) := by
  rw [show (⇑f : ℍ → ℂ) = discriminant * (CuspForm.discriminantEquiv (toCuspForm f hcusp) : ℍ → ℂ)
      from (discriminant_mul_discriminantEquiv _).symm, ← CuspForm.coe_discriminant]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _
```

### Anti-pattern

> "The proof works, it's only one PR, let me just fix the cosmetic complaint and move on."

This is exactly what reviewers keep flagging. They don't want compiled ugly code;
they want code that future authors will read and build on. When you can name the
missing API in one sentence, **the cosmetic fix is not the fix** — the API extraction
is the fix.

### Where this rule fires

- **`/cleanup` Phase 4, audit item 13 (MATHLIB):** if no mathlib lemma exists AND the
  proof exhibits any signal above, flag `Refactoring needed: extract API` rather than
  finalising the ugly proof.
- **`/fix-pr-feedback`:** treat reviewer comments saying *"this should be an API lemma"*
  or *"looks like more API lemmas for X"* with higher priority than ordinary golf
  comments — and grep ALL call sites of the underlying object first so the new API
  is named for the broader use case, not just the one-shot context.

---

## Style Notes from Reviewers

- **Dot notation is preferred**: `h.mono_left` over `mono_left h` (frequent reviewer comment)
- **Use `<|` to avoid trailing parentheses**: `f <| by simp` over `f (by simp)`
- **`rcases ... with rfl` auto-substitutes**: no need for subsequent `simp [h]`
- **Register lemmas for automation**: `@[simp]`, `@[grind =]`, `@[fun_prop]`, `@[aesop]`
- **Prefer `obtain ⟨a, b⟩ :=`** over `have h := ...; h.1, h.2`
- **Use `convert`** when the goal is close to a known lemma but not exact

---

## What Doesn't Golf Well

From reviewing thousands of PRs, these resist compression:

- **Analysis boilerplate** — integrability/measurability/continuity proofs
  need new API to simplify further
- **`grind` limitations** — rarely closes goals with `zpow`, `Even`/`Odd`,
  or cast arithmetic
- **Dominated convergence proofs** — each sub-proof (bound, summability,
  pointwise convergence) is already near-minimal
- **Modular form proofs** — specialized API doesn't simplify further

---

## Minimum Value Filter

1-line savings are only worth making if:
- (a) Zero-risk syntax cleanup (e.g., `by exact` → term), OR
- (b) They also improve clarity or performance

Don't churn code for marginal compression.
