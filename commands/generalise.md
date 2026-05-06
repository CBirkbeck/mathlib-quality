---
name: generalise
description: Audit a lemma or definition for assumption-weakening opportunities — try mechanical weakenings, search the literature for the maximally-general form, auto-apply small safe changes, propose big changes for user approval
---

# /generalise — Weaken Assumptions to Maximise Generality

Given a single lemma or definition, find every way its hypotheses can be weakened.
Combines two passes:

1. **Mechanical pass** — drop unused hypotheses, swap typeclasses for weaker ones from the
   catalogue, point-localise global hypotheses. Each candidate is verified by `lean_diagnostic_messages`.
2. **Literature pass** — online search (and ChatGPT, if MCP available) for the maximally
   general form known in the literature. Often the textbook statement is more general
   than what mathlib currently has.

Triage: **small** safe changes are auto-applied. **Big** changes (touch public API,
restate the lemma, change typeclass to one with different operators) get presented to the
user as a numbered menu of options with trade-offs — no auto-apply.

The hard rules:
- **Verify after every weakening attempt.** A weakening that breaks the proof is not a
  weakening; never leave the file in a broken state.
- **Public API changes need user approval.** A weakening that changes the call signature
  of a public lemma (or `simp` lemma) is a big change, full stop.
- **Literature search is mandatory** — the user explicitly asked for it. Skipping it is a
  defect.
- **Every hypothesis must be examined** — produce an artifact (the per-hypothesis status
  table) so a skipped hypothesis is detectable.

## Usage

```
/generalise <file_path> <decl_name>
/generalise <file_path>                # All public declarations in the file (one at a time)
```

A single declaration is the standard mode — generalisation is per-lemma surgery and
shouldn't be batched casually.

---

## Phases

```
PHASE 1  IDENTIFY        find the declaration, its hypotheses, its proof
PHASE 2  CLASSIFY        per-hypothesis: type-class? proposition? value?
PHASE 3  USAGE ANALYSIS  find every use of every hypothesis in the proof body
PHASE 4  MECHANICAL      drop-test + catalogue weakenings; verify each
PHASE 5  LITERATURE      online search for max-generality form (REQUIRED)
PHASE 6  TRIAGE          small safe vs big requires-approval; build the punch-list
PHASE 7  AUTO-APPLY      apply the small changes; verify after each
PHASE 8  USER CHOICE     present big-change options with trade-offs; STOP for approval
PHASE 9  APPLY + REPORT  final apply + verification + report
```

---

## PHASE 1 — Identify

### 1a. Read the declaration

`Read` the file. Locate `decl_name`. Capture:
- Full type signature (every hypothesis, every implicit/instance argument, the conclusion)
- Proof body
- Visibility (`public` / `private`)
- Whether it carries any attributes (`@[simp]`, `@[ext]`, `@[fun_prop]`, etc.) — these
  matter for triage because losing or breaking a `simp` lemma's normal form is a public
  API change.

### 1b. List the dependencies

Capture, for the triage in Phase 6:
- **Call sites within this project** — `Grep` for `decl_name` across all `.lean` files
  outside `.lake/`. List each. This determines blast radius.
- **External use** — if `decl_name` is in a known mathlib PR or the project is itself
  meant to be upstreamed, every signature change is a public API change.

### 1c. Read the references

In Phase 1 of the worker, read these completely:

1. `skills/mathlib-quality/references/generalisation-patterns.md` — the catalogue
2. `skills/mathlib-quality/references/style-rules.md` § "Maximal Generalization of Theorems" — the principle
3. `skills/mathlib-quality/references/mathlib-search.md` — the five-method search framework (used in Phase 5)

In your first response, confirm: "I have read generalisation-patterns.md (catalogue), the
Maximal Generalization section of style-rules.md, and mathlib-search.md."

---

## PHASE 2 — Classify hypotheses

For every parameter to the declaration (whether `(h : P)`, `[Foo X]`, `{x : α}`,
`(x : α)`), classify:

| Class | Examples | Weakening strategy |
|---|---|---|
| **typeclass** | `[CommRing R]`, `[Field K]`, `[NormedSpace 𝕜 E]` | Walk the typeclass hierarchy; try parents from the catalogue |
| **proposition** | `(h : 0 < x)`, `(h : Continuous f)`, `(h : Injective g)` | Drop-test; pointwise weakening; strict→weak |
| **structure value** | `(s : Finset α)`, `(μ : Measure α)` | Generalise to a `Fintype`-indexed family, swap measure for general kernel, etc. |
| **type variable** | `{α : Type*}`, `(R : Type)` | Universe weakening (`Type` → `Type*`); concrete-type → typeclass |
| **decidability** | `[DecidableEq α]`, `[Decidable p]` | Often droppable in classical contexts; verify by trying without |

Print the classification table:

```
| # | Hypothesis (verbatim)        | Class       | Notes                          |
|---|------------------------------|-------------|--------------------------------|
| 1 | [CommRing R]                 | typeclass   | parent: Ring, CommSemiring     |
| 2 | (x : R)                      | structure value | type follows R from #1     |
| 3 | (h : x ≠ 0)                  | proposition | strict; alt: x ∈ Rˣ if Field   |
| 4 | (h2 : Polynomial.IsMonic p)  | proposition | bundled; alt: p.leadingCoeff = 1 |
| 5 | [DecidableEq R]              | decidability | often droppable               |
```

---

## PHASE 3 — Usage analysis

For each hypothesis from Phase 2, find every use in the proof body.

A "use" is one of:
- An explicit appearance of the hypothesis name (`h.mp`, `h ▸ x`, `Finset.sum_eq_zero h`).
- A typeclass-resolved use (`mul_comm` resolved via `[CommRing]` → `[CommMonoid]`).
- An implicit projection (`f.continuousAt` requires `Continuous f`).

For typeclasses, what matters is **which operations** are used. Walk the proof:
- If only `+`, `0`, `add_comm` are used → the proof is over `AddCommMonoid` at most.
- If `*`, `1`, `mul_assoc` are used but not `mul_comm` → `Monoid` is enough, not `CommMonoid`.
- If subtraction (`-`, `sub_self`) appears → need `SubtractionMonoid` or a `Ring`/`Group`.

Print the usage table:

```
### Hypothesis usage in proof of `decl_name`

| # | Hypothesis     | Lines used                  | Operations / lemmas invoked            |
|---|----------------|-----------------------------|----------------------------------------|
| 1 | [CommRing R]   | L42 (mul_comm), L48 (ring)  | mul_comm, ring (uses commutativity)    |
| 2 | (x : R)        | L40, L42, L48               | passed through; no extra operations    |
| 3 | (h : x ≠ 0)    | L46 (mul_ne_zero)           | uses h directly to dispatch nonzero    |
| 4 | (h2 : IsMonic p)| L43 (.leadingCoeff_eq_one) | only via .leadingCoeff_eq_one          |
| 5 | [DecidableEq R]| (none found)                | UNUSED — candidate for drop-test       |
```

A hypothesis with no listed uses is a candidate for the drop-test in Phase 4.

---

## PHASE 4 — Mechanical weakenings (verify each candidate)

For each candidate weakening, the procedure is:

1. **Substitute** the weaker form in the file.
2. Run `lean_diagnostic_messages` on the file.
3. **Compiles?** Record success and keep the change.
4. **Doesn't compile?** Revert with `Edit`. Record the failure with the specific error.

Generate candidates by walking through:

### 4a. Drop-test for every hypothesis flagged "unused" in Phase 3

For each candidate-for-drop:
- Remove the hypothesis from the signature.
- Run diagnostics.
- If clean: record as `drop, safe`. Keep dropped.
- If not: revert. Record the proof line that surprised you.

### 4b. Typeclass-hierarchy weakening (use the catalogue)

For each typeclass hypothesis from Phase 2, walk the parent chain in
`generalisation-patterns.md`. For each parent, try substituting:

```
[CommRing R] → [Ring R]
[CommRing R] → [CommSemiring R]
[Ring R] → [Semiring R]
[Ring R] → [NonAssocRing R]
...
```

After each substitution, run diagnostics. The first parent that compiles is recorded;
keep walking to find the weakest one that still works.

### 4c. Pointwise weakening (global → pointwise)

For each `Continuous f`, `Differentiable f`, `Measurable f`, `Monotone f`-style
hypothesis: if Phase 3 showed it's used at exactly one point/set, try the pointwise form
from the catalogue.

### 4d. Strict → weak

For `0 < x`, `x ≠ 0`, `Injective f` etc., check if the proof's actual use is the weaker
form (e.g., `0 ≤ x`, `x ∈ s`, `LeftInverse g f`).

### 4e. Universe weakening

If the declaration has `Type` (no universe poly), try `Type*`. If it has `Type u`, try
`Type*`.

### 4f. Print the mechanical-weakening status table

This is the artifact for Phase 4. Skipping any candidate without recording why is a
defect.

```
### Mechanical weakenings tried for `decl_name`

| # | Candidate                              | Verified? | Result                                   |
|---|----------------------------------------|-----------|------------------------------------------|
| 4a-1 | DROP `[DecidableEq R]`              | yes       | ✓ compiles → kept                        |
| 4b-1 | `[CommRing R]` → `[Ring R]`         | yes       | ✗ L48 needs `mul_comm` → reverted        |
| 4b-2 | `[CommRing R]` → `[CommSemiring R]` | yes       | ✗ L46 uses subtraction → reverted        |
| 4c-1 | `Continuous f` → `ContinuousAt f x` | n/a       | hypothesis is on g, not f                |
| 4d-1 | `(h : 0 < x)` → `(h : 0 ≤ x)`       | yes       | ✗ L44 uses strict positivity → reverted  |
| 4e-1 | `Type` → `Type*`                    | yes       | ✓ compiles → kept                        |
```

Mechanical pass concluded with: <N applied / M attempted-and-reverted / K not applicable>.

---

## PHASE 5 — Literature search (REQUIRED — do not skip)

The catalogue captures common weakenings, but the maximally-general form of a *theorem*
often lives in the literature, not in the catalogue. The user explicitly wants this
search performed.

For each significant hypothesis still present after Phase 4, search:

### 5a. WebSearch

Query terms:
- The mathematical content: "<theorem statement keywords> generalization"
- The author's name + theorem (if a textbook citation is on the file)
- nLab, Stacks Project, Wikipedia for the canonical formulation

Use the `WebSearch` tool. Capture the top 3 hits per query in your notes.

### 5b. ChatGPT (if `mcp__chatgpt-math__ask_chatgpt_math` is available)

Ask a self-contained question:

```
What is the most general known statement of <theorem in plain mathematical English>?
The version I currently have is <statement with hypotheses>. Are any hypotheses
unnecessary in the literature? In particular, do any of the following stronger
hypotheses have a known weakening?

- <hypothesis 1>
- <hypothesis 2>
...

Cite any standard reference if relevant.
```

### 5c. Mathlib-search

Use the five-method search from `mathlib-search.md` to look for an *existing* generalised
mathlib version. If mathlib already has a more general statement, the right action is
usually to delete the local lemma and use mathlib's directly (per the six strict rules).

### 5d. Literature status block (REQUIRED ARTIFACT)

```
### Literature search status: `decl_name`

[A] WebSearch                queries: <list>          findings: <summary or "none">
[B] ChatGPT                  asked? <yes / no — n/a: reason>   key insight: <…>
[C] Mathlib (5-method)       queries: <list>          findings: <existing in mathlib? more general?>

Maximally-general form found in literature:
<verbatim statement, with citation if there is one>

Implied weakenings on our hypotheses:
- <Hypothesis X> can become <Y> per [Author, Year, Theorem N.M]
- <Hypothesis Z> is unnecessary per the cited proof technique
```

If the literature search is genuinely impossible in this session (no internet, no MCP),
record `n/a: <reason>` for the unavailable channels — do not silently skip.

---

## PHASE 6 — Triage

Take every candidate from Phases 4 and 5, classify each as **small-safe** or
**big-needs-approval**.

### Small-safe (auto-apply in Phase 7) — ALL of these must hold

1. The candidate has been **verified by `lean_diagnostic_messages`** (Phase 4) OR is a
   straightforward translation of a verified candidate.
2. The change does **not** alter the call signature in a way that breaks call sites:
   - Dropping a `[DecidableEq α]` instance argument is safe — instance arguments are
     filled by typeclass resolution, not passed by callers.
   - Weakening `[CommRing R]` to `[Ring R]` is safe IF every call site that provided
     `[CommRing R]` still has it (typeclass resolution finds `Ring` automatically). Verify
     by checking call sites compile.
   - Weakening `[CommRing R]` to `[Ring R]` AND removing other parameters is NOT safe —
     two changes at once.
3. The change does **not** affect any `@[simp]`, `@[ext]`, `@[fun_prop]`, `@[grind]`
   normal form (verified by re-running diagnostics across all files that use the lemma).
4. The change does **not** rename or restructure the lemma's name or argument order.

### Big-needs-approval (Phase 8) — ANY of these makes a change "big"

- Restating the lemma over a different abstract structure (`ℝ` → `LinearOrderedField`).
- Adding or removing any explicit argument (not instance argument).
- Changing argument order.
- Restating the conclusion (e.g., from `=` to `Iff`, or from a single fact to a
  conjunction).
- Touching a `simp`/`ext`/`fun_prop` lemma's normal form.
- Renaming the lemma (e.g., dropping a `_real` prefix).
- A literature finding that requires restating the lemma over different machinery.
- The lemma is `public` and used by other files / external projects.

### Print the triage table

```
### Triage

| # | Candidate                                        | Small-safe? | Why                                  |
|---|--------------------------------------------------|-------------|--------------------------------------|
| 1 | DROP `[DecidableEq R]`                           | small       | instance arg, no call-site impact    |
| 2 | `Type` → `Type*`                                 | small       | universe poly, no semantic change    |
| 3 | `(h : 0 < x)` → `(h : 0 ≤ x)` — verified failed  | n/a         | reverted in Phase 4                  |
| 4 | Real → arbitrary `LinearOrderedField`            | BIG         | restates over different typeclass    |
| 5 | Drop `IsMonic p` per [Mumford 1966, §4]          | BIG         | per literature; restates conclusion  |
```

---

## PHASE 7 — Auto-apply small-safe changes

For each small-safe candidate in the triage:

1. Apply the edit.
2. Run `lean_diagnostic_messages` on the file — must be clean.
3. Run `lean_diagnostic_messages` on every file in the call-site list from Phase 1b — must
   also be clean (call sites must still compile under the weakened typeclass).
4. If any check fails, revert. Move the candidate to Phase 8 (big-needs-approval) for the
   user to look at.
5. Record the applied change with file + line + before/after.

After all small-safe changes are applied, print:

```
### Small changes applied to `decl_name`

| # | Change                          | Verified? | Files re-checked          |
|---|---------------------------------|-----------|---------------------------|
| 1 | dropped [DecidableEq R]         | ✓         | this file + 3 call sites  |
| 2 | Type → Type*                    | ✓         | this file + 3 call sites  |
```

If no small-safe changes existed: record `Small-safe changes: 0` and proceed to Phase 8.

---

## PHASE 8 — Big-change options (STOP — wait for user)

For each big-change candidate in the triage, build a numbered option block. Present them
as a menu — the user picks which (if any) to apply. **Do not apply anything in this phase.**

For each option, include:

- **What changes** — exact before/after of the signature.
- **Why** — the mechanical reason (catalogue) or the literature citation (Phase 5).
- **Blast radius** — how many call sites need updating, plus an estimate of effort.
- **Risk** — what could break (simp normal form? typeclass resolution? downstream proofs?).
- **Trade-off** — what we gain (broader applicability) vs what we lose (sometimes the
  more general form has a longer name or requires more imports at call sites).

```
### Generalisation options for `decl_name` (NOT YET APPLIED)

#### Option A — generalise `ℝ` to arbitrary `LinearOrderedField`

Before:
  theorem foo (x : ℝ) (h : 0 < x) : … := …
After:
  theorem foo {K : Type*} [LinearOrderedField K] (x : K) (h : 0 < x) : … := …

Why:
  Mechanical (Phase 4): `[LinearOrderedField K]` compiles and the proof goes through.
  Literature (Phase 5): "this is the textbook statement in Lang, Algebra, §3.1, where
  it's stated for any ordered field."

Blast radius:
  4 call sites in this project — all currently pass `(x : ℝ)`. Under the generalised
  form, callers don't need to change: type unification fills `K = ℝ`. Verified
  diagnostics-clean on all 4 files when this was tried in Phase 4.

Risk:
  Low. The generalised lemma is strictly stronger; existing callers are unaffected.

Trade-off:
  Gain: usable in any ordered-field context (e.g., the `ℚ` and `ℝ_alg` analogues we'll
  need later).
  Lose: nothing material.

#### Option B — drop `IsMonic p` per [Mumford 1966, §4]

Before:
  theorem bar (p : R[X]) (h : p.IsMonic) : … := …
After:
  theorem bar (p : R[X]) (h : p.leadingCoeff ≠ 0) : … := …

Why:
  Literature (Phase 5): Mumford [1966, §4] proves this with only the weaker `non-zero
  leading coefficient` assumption.

Blast radius:
  6 call sites — 4 of which already prove monicity from a non-zero leading coefficient,
  so they'd simplify by dropping the redundant strengthening.

Risk:
  Medium. Any `simp` lemma that rewrites with `IsMonic p` would need to be checked. Two
  lemmas (`bar_aux₁` and `bar_aux₂`) might need restatement.

Trade-off:
  Gain: more uniform; works for non-monic polynomials too.
  Lose: name `bar` no longer signals monicity to readers — may want to rename to
  `bar_of_leadingCoeff_ne_zero`.

---

Reply with the option letters you want to apply ("apply A, B"; "A only"; "skip
all"; or describe a different variant). Apply will not run until you choose.
```

Then **stop**. Wait for the user's response.

---

## PHASE 9 — Apply chosen big changes + final report

When the user picks options:

### 9a. Apply each chosen option

For each chosen option:
1. Apply the edit (and any consequential edits like renames).
2. Update every call site (use `Grep` to find them, `Edit` to update).
3. Run `lean_diagnostic_messages` on every affected file. Must be clean.
4. Run `lake build` on the affected modules if available.
5. If anything fails, revert that option and report — do not silently leave breakage.

### 9b. Update attribute lemmas if needed

If the change touched a `simp`/`ext`/`fun_prop` lemma:
- Re-check the simp normal form: does the new statement still produce the same canonical form when applied?
- If not, propose a follow-up `@[simp]` lemma to bridge, or remove the attribute and explain.

### 9c. Final report

```
## /generalise report — `decl_name`

### Summary
- Hypotheses examined:        N
- Mechanical weakenings tried: M (P applied, Q reverted)
- Literature suggestions:     L (X chosen by user, Y declined)
- Big-change options offered: B (Z applied, W declined)
- Total changes:              <count>

### Applied
- (small) dropped [DecidableEq R]
- (small) Type → Type*
- (big A) ℝ → LinearOrderedField K — 4 call sites updated, all compile

### Declined
- (big B) drop IsMonic — user wants to keep the monic-named API

### Verification
✓ lean_diagnostic_messages clean on this file
✓ lean_diagnostic_messages clean on 4 call-site files
✓ lake build clean on affected modules
```

### 9d. Record learnings

Each successful generalisation is a `mathlib_discovery`-adjacent learning. Write to
`.mathlib-quality/learnings.jsonl`:

```json
{
  "id": "<short id>",
  "timestamp": "<ISO>",
  "command": "generalise",
  "type": "user_teaching",
  "before_code": "<before signature>",
  "after_code": "<after signature>",
  "pattern_tags": ["generalisation", "<typeclass-weakening / drop-unused / point-localise / etc.>"],
  "description": "<one sentence: what was weakened, why it worked>",
  "math_area": "<area>",
  "accepted": true,
  "source": "agent_suggestion",
  "context": {
    "file_path": "<path>",
    "theorem_name": "<decl_name>",
    "literature_ref": "<citation if Phase 5 found one>"
  }
}
```

If the same pattern recurs, it's a candidate for adding to
`references/generalisation-patterns.md` via `/teach`.

---

## What this command does NOT do

- **Does not refactor proofs.** It changes signatures (and re-verifies). Proof rewrites
  larger than what the changed signature needs go through `/cleanup`.
- **Does not chase generality at the cost of usability.** A generalisation that makes
  callers significantly more verbose (e.g., requiring an extra typeclass argument that
  every call site must explicitly synthesise) is a candidate for the **decline** column,
  not an automatic win.
- **Does not bypass user approval for public-API changes.** If the lemma is `public`,
  every signature change is big.
- **Does not change docstrings without reflecting the change.** If the lemma has a
  docstring referring to "the real version", and we generalise to a field, the docstring
  must be updated to match.

---

## Reference

- `skills/mathlib-quality/references/generalisation-patterns.md` — the mechanical-weakening catalogue
- `skills/mathlib-quality/references/style-rules.md` § "Maximal Generalization of Theorems" — the principle
- `skills/mathlib-quality/references/mathlib-search.md` — used in Phase 5c for the mathlib search
- `commands/cleanup.md` — `/cleanup` Phase 4's MATHLIB audit overlaps; if a literature
  search reveals "this already exists in mathlib", the action moves to a `/cleanup`-style
  delete-and-use-mathlib refactor (per the six strict rules).
