---
name: mathlibable
description: Decide whether a Lean declaration belongs in mathlib. Methodical, gated workflow that combines thorough literature search (WebSearch + ChatGPT MCP + local references + nLab/Stacks/MathOverflow for big decls) with mathlib's five-method exhaustive search, then a generality analysis against the literature-standard form, then a composition check (can mathlib's primitives compose to give us this?), then synthesises a five-bucket verdict — YES-add-as-is | YES-but-generalise-first | NO-mathlib-has-it | NO-composable-from-mathlib | BORDERLINE-needs-human — with required evidence per bucket. The value is in the process: the search is the hard part, and the gates exist to prevent the worker from short-circuiting it. Single declaration per invocation; `--exhaustive` forces the wider literature sweep even for small decls (big decls trigger it automatically).
---

# /mathlibable — Should this declaration be in mathlib?

Take one Lean declaration and answer the question: *should mathlib have this?* The
answer is rarely obvious. The skill exists to do the search work that makes the
answer well-founded — and to refuse to produce a verdict without the evidence.

This is a **hard, slow** workflow. Mathlib's bar isn't "is this true and useful"; it
is "is this the *right* statement at the *right* level of generality, and not
already there in some form we should be reusing?" Getting that right takes
thorough literature + mathlib search. Skipping the search produces wrong verdicts.

## Usage

```
/mathlibable <Foo.bar>                          # Mode A: one declaration; full 10-phase workflow
/mathlibable <file.lean>                        # Mode B: every public decl in this file; orchestrator-worker
/mathlibable <file1.lean> <file2.lean> ...      # Mode B: same, across multiple files
```

There is no `--quick` flag and no `--exhaustive` flag. **Every invocation runs
the full exhaustive literature search.** Mathlib is Bourbaki 2.0 — adding the
*right* declaration in the *right* form requires doing the thorough work every
time. Producing a verdict in five minutes by skipping channels is exactly the
failure mode this skill exists to prevent.

**Mode B is slow by design.** Each public declaration in the file(s) gets its
own full 10-phase workflow (one Agent per decl). On a 30-decl file with the
exhaustive lit search, plan on hours. The orchestrator narrates a one-line
scoreboard between dispatches so you can leave it running. If you only want
to know *which* declarations are worth investing this kind of work in, run
`/overview` first — its Step 9 mathlibable triage assigns each decl to
`SKIP` / `LIKELY-NO` / `LIKELY-YES` / `WORTH-FULL-CHECK` based on cheap
signals only.

## Prerequisites

- `lake build` clean (the declaration must elaborate; we read its full elaborated
  type, not a sorry-placeholder).
- The declaration exists in the current Lean project. Mathlib-tree decls aren't in
  scope — if you want to ask "should this mathlib decl be more general?", use
  `/generalise` instead.
- Optional but **highly valuable**: a `.mathlib-quality/references/` directory of
  source-paper PDFs / notes. The literature search reads these first; with them,
  the standard-form question is often answered in seconds. Without them, the skill
  falls back to WebSearch + ChatGPT MCP + nLab/Stacks; still works, takes longer.

---

## The verdicts (five buckets)

Each verdict requires its own evidence trail. The Phase 7 verdict block is
*rejected* if the supporting artifact is missing or shallow.

| Bucket | When it fires | Required evidence |
|---|---|---|
| `YES-add-as-is` | Literature confirms standard form; the user's Lean form matches it at the right generality; mathlib doesn't have it; composition from mathlib primitives doesn't trivially give it; if it's a one-liner, an exemption from Phase 2b applies; if it's a `def`/`class`/`instance`, Phase 4.5 risk is at most LOW (or each HIGH row is explicitly addressed) | Phase 3 lit table (≥3 channels) + Phase 4 generality analysis ("current form = literature-standard") + Phase 4.5 risk verdict (n/a or NONE/LOW; or HIGH explicitly addressed) + Phase 5 mathlib search (no hit) + Phase 6 composition check (non-trivial) |
| `YES-but-generalise-first` | Literature confirms a strictly more general statement is standard; the user's form is a specialisation; restating in the general form is reasonable | Phase 3 lit table identifying the general form + Phase 4 generality analysis with specific weakenings proposed + Phase 5 mathlib search (no hit on either form) |
| `NO-mathlib-has-it` | Mathlib already has the result (or a more general one we'd specialise from) | Phase 5 mathlib search citing the existing decl by qualified name + the user's form follows from it in ≤1 line (proof sketch shown) |
| `NO-composable-from-mathlib` | Mathlib has the *building blocks*, not the exact form, but the form is a 1–3 mathlib-call composition. No new lemma needed — inline at call sites | Phase 5 mathlib search citing the building blocks + Phase 6 composition sketch ≤3 lines |
| `BORDERLINE-needs-human` | The verdict depends on a judgment call the skill can't make alone (mathematical taste, project policy, audience-narrow result, etc.) | All other phases complete + a numbered list of concrete questions for the user (≤5 questions, each answerable yes/no or with a short response) |

The skill **never silently picks** between buckets when two could fit. If the
evidence is genuinely ambiguous, the verdict is BORDERLINE with the question
spelled out.

---

## Workflow

Eight phases. **Do them in order. Do not skip phases.** Every phase produces a
required artifact; missing artifacts fail the verdict.

```
PHASE 0   DOCTOR                lake build clean; the decl exists and elaborates
PHASE 1   COMPREHEND            read the decl; capture its mathematical statement in prose
PHASE 2   PRELIM CHECKS         BIG/SMALL classification (for narrative; does not gate the lit width);
                                one-line check with defeq/diamond/API exemptions
PHASE 3   LITERATURE            EXHAUSTIVE protocol — always. WebSearch ×≥3 + ChatGPT MCP
                                + local refs + nLab + Stacks + MathOverflow + arXiv + nCatLab
PHASE 4   GENERALITY            (4a-b) compare current form to literature-standard;
                                (4c) modern-mathlib-idiom restatement — Bourbaki 2.0 check
PHASE 4.5 DIAMOND/DEFEQ RISK    for `def`/`class`/`instance` only; six-row risk table
PHASE 5   MATHLIB                five-method exhaustive search (Loogle / LeanSearch / Lean-Finder / grep / lean_local_search)
PHASE 6   COMPOSITION             call-sites grep (first-class composability signal) + can mathlib's primitives compose to give the form?
PHASE 7   VERDICT                one of the five buckets, with evidence trail
PHASE 8   REPORT                 consolidated artifact
```

---

## PHASE 0 — Doctor

### 0a. Lake build clean

```bash
lake build 2>&1 | tail -10
```

If broken, stop. We need the elaborated type of `<Foo.bar>`.

### 0b. Declaration resolves

```bash
# Either via lean_local_search or Grep:
grep -nE "^(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+<bar>" --include="*.lean" -r .
```

If zero matches → "Not found in project. Use the qualified name, or check the spelling.
If you meant a mathlib decl, use /generalise instead."

If multiple matches → ask the user which one (disambiguate by file:line).

### 0c. Baseline block (REQUIRED ARTIFACT)

```
### Baseline (Phase 0)
- lake build:               ✓ clean
- decl `<Foo.bar>`:          ✓ resolved at <file>:<line>
- kind:                      <theorem|lemma|def|abbrev|structure|inductive|class|instance>
- has sorry:                 yes | no
- module docstring summary:  <one line — what the file is about>
```

---

## PHASE 1 — Comprehend

Read the declaration, its docstring, and the proof body (if any). Capture the
**mathematical content** in prose — not the Lean type, the math statement a
mathematician would write on a board.

### 1a. Statement in prose (REQUIRED ARTIFACT)

```
### Statement (Phase 1)

`<Foo.bar>` is <a definition of | a theorem stating> the following:

<2-4 sentence mathematical prose statement, in standard notation, NOT the Lean type>

Variables / typeclasses involved (Lean side):
- <list each parameter with its mathematical role>

Hypotheses (Lean side):
- <list each hypothesis with its mathematical role>

Conclusion (math): <one sentence>

Conclusion (Lean): <the actual Lean type of the result; or "n/a — definition">
```

Skipping this — going straight to literature search without writing the prose
form — is the most common cause of fruitless searches (you search for the
Lean spelling, miss the math literature entirely).

---

## PHASE 2 — Preliminary checks (size + one-line)

Two cheap preliminary checks. **These do NOT gate the literature-search width**
— that's always EXHAUSTIVE. The classification is for narrative clarity in the
report and to inform the worker's framing.

### 2a. Big vs small — for narrative only (REQUIRED ARTIFACT)

A declaration is **BIG** if any of:

- It introduces a **new mathematical structure** (`def`/`class`/`structure` of a
  named concept: a topology, a category structure, a notion of measurability,
  etc.). Vector spaces vs modules is the canonical case — defining
  vector-spaces-as-distinct-from-modules would be BIG.
- It's a **main result** of the project (listed under `## Main results` in the
  module docstring, or named in `.mathlib-quality/plan.md` as a primary goal).
- It's a **theorem named after a person or place** (Riemann–Roch, Cauchy's,
  Bolzano–Weierstrass, etc.) — those are basically guaranteed to be in or near
  the literature in some form.

A declaration is **SMALL** if it's none of the above — typically a helper lemma,
a specialisation, a corollary, or a one-step composition.

```
### Size classification (Phase 2a)

Verdict: BIG | SMALL
Reason: <one line>

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for
the report's framing and for the worker's mental model — it does not gate
which channels Phase 3 runs.)
```

### 2b. One-line check (REQUIRED ARTIFACT)

A **one-line definition** — a `def`/`abbrev`/`structure` whose body is one
substantive line of Lean (excluding signature, the leading `:=`, and trailing
helpers like `by exact …`) — is a strong negative signal for mathlib inclusion.
Most one-liners are better served by using mathlib directly at the call site, or
by being inlined entirely.

But not always. There are three legitimate reasons to ship a one-line
definition to mathlib:

1. **Avoid defeq abuse.** Some downstream proof in the project depends on the
   exact spelling of the right-hand side and the definition serves as a barrier
   — preventing `simp` or unification from unfolding the wrong direction. The
   def is sealed (no `@[reducible]`) precisely so the unfolding doesn't happen
   without explicit `unfold` or rewriting.

2. **Avoid typeclass diamonds.** The def exists so a specific typeclass-search
   path picks the right instance. Without the named anchor, two `Mul` (or
   `Zero` or `AddCommMonoid`) instances would collide; with it, the search
   sees one canonical target.

3. **Mark semantic intent / API stability.** The definition has a *name* and a
   *docstring* even though the body is one line — and that name + docstring
   is the API surface other developments will depend on. Renaming the def
   later (without the named anchor) would break consumers; with it, the def
   itself can be re-implemented behind the same name.

```
### One-line check (Phase 2b)

Body line count: <N substantive lines>
One-liner verdict: ONE-LINER | MULTI-LINE | n/a (kind is theorem/lemma, not def)

If ONE-LINER, exemption check (each row required):
| Exemption                         | Applies? | Evidence                                                 |
|-----------------------------------|----------|-----------------------------------------------------------|
| Avoid defeq abuse                | yes/no   | <if yes: name a downstream proof or sketch that relies on the unfolding being controlled> |
| Avoid typeclass diamonds         | yes/no   | <if yes: name the colliding instances or the path>       |
| Mark semantic intent / API name  | yes/no   | <if yes: name ≥1 consumer that benefits from the stable name> |

Conclusion: ONE-LINER WITHOUT-EXEMPTION | ONE-LINER WITH-EXEMPTION | MULTI-LINE
```

If `ONE-LINER WITHOUT-EXEMPTION`, the worker carries this into Phase 7: the
verdict is biased toward NO-composable-from-mathlib or NO-mathlib-has-it. A
YES verdict on a one-liner without exemption requires Phase 7 to spell out
*explicitly* why the one-liner is justified despite no Phase-2b exemption —
otherwise the verdict gate rejects it.

If `MULTI-LINE` or kind is `theorem`/`lemma`, this section is a one-line
note and the check is skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE, always)

The single most important phase. **The skill exists to do this carefully.**
Skipping or short-circuiting this phase produces wrong verdicts. Workers who
write "searched: didn't find anything" without a full artifact fail the gate.

This phase is **always EXHAUSTIVE**. There is no bounded mode. The user
explicitly chose to run `/mathlibable` because they want the thorough work
done — short-circuiting wastes their explicit ask.

### 3a. Channel protocol (REQUIRED ARTIFACT)

All nine channels are mandatory. Print one row per query attempted —
including queries that returned nothing. A row with `n/a` requires a one-line
reason (e.g., "Stacks Project: not an algebraic-geometry concept").

```
### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "translate of continuous function" definition                                                          | yes  | $`(\tau_a f)(x) := f(x-a)`         | Wikipedia "Translation operator"; standard in harmonic analysis |
|  2 | WebSearch (general form)         | "translation of a function" L^p generality                                                             | yes  | well-defined for any measurable f  | strictly more general — continuity overkill |
|  3 | WebSearch (named-after / aliases)| "shift operator" function definition                                                                   | yes  | same as #1; also called "shift"    | name varies; both standard |
|  4 | ChatGPT MCP                      | "What is the standard mathematical definition of the translate of a function, and at what generality is it usually stated? Has the formulation evolved historically?" | yes  | confirms #2; notes modern abstraction over additive groups | covers historical evolution |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "translation"                                                  | n/a  | (no references dir)                | dir absent — recorded as n/a |
|  6 | nLab                             | <concept name>                                                                                          | ...  | ...                                | ... |
|  7 | nCatLab (if categorical)         | <concept name>                                                                                          | ...  | ...                                | ... |
|  8 | Stacks Project (if alg geom)     | <concept name>                                                                                          | ...  | ...                                | ... |
|  9 | MathOverflow / Math.StackExchange| <concept name> generality                                                                              | ...  | ...                                | ... |
| 10 | recent arXiv (last 5 years)      | <concept name> + topical adjective                                                                      | ...  | ...                                | ... |
```

The protocol passes when:
- **WebSearch ran at least 3 distinct queries at different generality
  levels** (specific form, the most-general form, named-after / common
  aliases).
- **ChatGPT MCP ran at least 1 query asking explicitly for the standard
  form, its generality, and any historical evolution of the formulation.**
- **Local references were checked** (or recorded `n/a` with a one-line
  reason if the directory is absent).
- **nLab was checked.** Even if the concept isn't categorical, nLab often
  has a clean abstract statement.
- **Stacks Project / nCatLab / MathOverflow / arXiv** were each checked or
  recorded `n/a` with reason. "Not an algebraic-geometry concept" is a
  valid `n/a` for Stacks; "not a categorical concept" for nCatLab. But the
  worker must look briefly to decide that.

A skipped channel without an `n/a` reason is a defect; a row that says
`n/a — didn't seem relevant` without further justification is also a
defect. The protocol exists to force the worker to actually look.

### 3c. Literature summary block (REQUIRED ARTIFACT)

After the table:

```
### Literature summary (Phase 3)

Concept identified as: <standard mathematical name(s)>
Sources agree on the standard form: yes | no — <if no, list the variants and where they appear>
Most general standard form: <restate in prose>
Generality dimensions where the literature varies:
  - <dimension 1>: <range from X to Y; the most general is Y>
  - <dimension 2>: ...
Disagreement with the literature: <none | "literature uses … but the user's form …">
```

If the literature search returned NOTHING after the protocol ran in full —
no concept name, no standard form, no analog — that's itself a signal: the
declaration may be too narrow, too specialised, or too project-specific for
mathlib. Note this explicitly; Phase 7 may pick BORDERLINE or NO-composable.

---

## PHASE 4 — Generality analysis

Mathlib's iron rule: **add the most general form that makes sense.** Modules,
not vector spaces. Topological groups, not metric groups. Comm-monoids, not
groups, when the proof goes through.

### 4a. Generality status table (REQUIRED ARTIFACT)

For every parameter / hypothesis of the user's declaration, compare its
strength to what the literature uses:

```
### Generality analysis — `<Foo.bar>`

Literature-standard form (from Phase 3): <restate the most general form>

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | `[NormedSpace ℝ E]`                  | normed real vector space   | locally convex TVS           | yes                 | proof uses norm only for boundedness; could state with `[LocallyConvexSpace ℝ E]` |
| 2 | `(hf : Continuous f)`                | continuous                 | measurable                   | yes                 | proof never uses continuity directly; only integrability |
| 3 | `(s : ℝ)`                             | real scalar                | element of additive group    | yes                 | translation makes sense for any `[AddGroup G]` |
| 4 | `[CompactSpace X]`                    | compact                    | locally compact + condition  | NO                  | proof uses sequential compactness essentially |
```

This is similar to `/generalise`'s mechanical pass but with a
**literature-grounded target** rather than a catalogue lookup. The target is
the most general form Phase 3 identified.

### 4b. Generality verdict (REQUIRED ARTIFACT)

```
### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL | STRICTLY NARROWER THAN STANDARD
Number of weakening opportunities found: K
Proposed restatement (if STRICTLY NARROWER):

<restate the declaration in the most general form, with the new Lean signature>

Cost of restatement: <CHEAP — mechanical rewrite | MODERATE — proof needs adjustments | EXPENSIVE — proof needs new ideas>
```

**Cost note.** EXPENSIVE is not a downgrade. Mathlib is Bourbaki 2.0; spending
significant effort to ship the right form is the work. Cost may inform the
*sequencing* (do it now vs. flag for a future PR) but should not change the
verdict bucket.

If MAXIMALLY GENERAL → Phase 7 considers YES-add-as-is or NO buckets, then
also runs 4c (modernisation may flip a MAXIMALLY GENERAL classical form to
YES-but-generalise-first if a contemporary idiom is cleaner).
If STRICTLY NARROWER → Phase 7 considers YES-but-generalise-first prominently.

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check (REQUIRED ARTIFACT)

The literature-standard form (4a–4b) is one anchor; the *mathlib-idiomatic*
form is another. Even if the literature standard is "maximally general",
mathlib may want a different formulation built from contemporary tools that
compose better with the rest of the library.

Ask each question explicitly. Each row needs an answer.

```
### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                                                 | Applies? | Proposed reformulation                                                                | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | Could "let X be a foo" preambles become **typeclasses / instances** instead of bundled hypotheses?                                       | yes/no   | <if yes: the new signature>                                                            | <which downstream lemmas compose better> |
|  2 | Does the literature use **sequences / metric notions** where **filters / nets / topological notions** would generalise more cleanly?    | yes/no   | <if yes: the filter/topological restatement>                                            | <e.g. unifies with all filter-based limit API> |
|  3 | Does the literature **construct** an object where a **universal-property class** would characterise it?                                 | yes/no   | <if yes: the universal-property class>                                                  | <auto-specialises to the existing concrete construction> |
|  4 | Does the literature use **set-with-closure-predicate** where a **bundled-substructure type** would compose with mathlib's lattices?     | yes/no   | <if yes: the bundled type>                                                              | <lattice API, quotients, sums, intersections> |
|  5 | Does the literature treat a **vector-space / metric / field-specific** result that **mathlib's typeclass hierarchy** would weaken to modules / pseudometric / (semi)ring? | yes/no   | <if yes: the weakened-typeclass restatement>                                            | <scalar restriction/extension lemmas, full module API> |
|  6 | Does the literature give a **1-categorical** statement that has a **higher-categorical or ∞-categorical** generalisation mathlib is moving toward? | yes/no   | <if yes: the higher-categorical statement>                                              | <future-proofs against the categorification effort> |
|  7 | Does the result mention a **concrete index (ℕ, ℤ, ℝ)** that would generalise to **arbitrary additive groups / monoids / ordered structures**? | yes/no   | <if yes: the index-generalised form>                                                    | <unifies with the rest of the project's algebraic structure> |
|  8 | **Concrete-via-abstract:** the statement mentions a concrete named object (`E2`, `π`, a specific group, …), but does the *proof body* use only abstract properties the named object happens to satisfy? (See "How to check Q8" below — adversarial diagnostic.) | yes/no   | <if yes: the abstract restatement, with the concrete result becoming a one-line corollary>                                            | <abstracts the result so other concrete witnesses can reuse the same proof> |
```

Rows do not have to all be `yes`. Most decls will hit 1–3 of these at most.
Rows that don't apply are answered `no` with a one-line reason (e.g., "this
is a finite combinatorial identity; no topology to filter-ise").

#### How to check Q8 — the concrete-via-abstract diagnostic

A frequent failure mode that Q1–Q7 miss: the *statement* mentions a concrete
named object (e.g. `E2`, `π`, a specific topology, a specific group), but
the *proof body*, after one or two unfolding rewrites, never mentions that
object again. From that point forward the proof is working purely with
abstract properties — a q-expansion, summability, polynomial bounds,
analyticity, the universal property — that other objects also have. The
right form is the abstract theorem, with the concrete result as a one-line
specialisation.

**Adversarial diagnostic (run it explicitly for Q8):**

1. Grep the proof body for the named-object identifier (exclude the
   statement line itself).
2. Count occurrences. If the identifier appears in **0 or 1 lines after the
   first `rw [<unfolding lemma>]`**, the proof from that point forward is
   working with abstractions only.
3. If the diagnostic fires, Q8 is **yes**. Propose the abstract restatement
   and frame the concrete result as a corollary:

```lean
-- Original (statement-concrete, proof-abstract)
theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 := by
  rw [E2_eq_tsum_cexp]
  -- ... proof here, never mentions E2 again ...

-- Abstract restatement (the real content)
theorem isBoundedAtImInfty_of_polyBoundedCoeffs
    (f : ℍ → ℂ) (hq : <has q-expansion>) (hpoly : <polynomially-bounded coeffs>)
    (hnonneg : <no negative-exponent terms>) :
    IsBoundedAtImInfty f := ...

-- Concrete result as one-line corollary
theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 :=
  isBoundedAtImInfty_of_polyBoundedCoeffs E2 ⟨..⟩ ⟨..⟩ ⟨..⟩
```

Q8 firing biases Phase 7 strongly toward `YES-but-generalise-first` with
reason `MODERN-IDIOM` (or sometimes `LITERATURE-WEAKENING` if the abstract
form is well-known in the literature). The "modernisation" is the
abstraction of the witness, not just the typeclass shape.

Q1–Q7 only inspect the statement; the diagnostic above inspects the proof
body, which is where this class of "the statement is concrete but the
content isn't" failure mode lives.

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes | no
If yes:
  - Proposed mathlib-idiomatic restatement:
    <new Lean signature, possibly significantly different from the literature form>
  - Cost: <CHEAP | MODERATE | EXPENSIVE>
  - Mathlib downstream this enables: <concrete list of API pieces that compose better>
  - Real mathematical improvement (not just "looks cooler"): <one sentence>
If no:
  - One-line reason this is not a modernisation move
```

**The honesty bar.** "Modernisation" is a real improvement in mathematical
*organisation* — it eliminates a redundancy, composes with more of mathlib,
enables proofs that the literature form blocked, etc. "It looks cooler in
category theory" is not enough. The Phase 7 rationale will require the
worker to point at the specific downstream API improvements; cherry-picked
abstraction for its own sake is rejected.

If Phase 4c says "modern idiom available", Phase 7 may produce
`YES-but-generalise-first` even when Phase 4b said MAXIMALLY GENERAL —
because the "generalise first" target is the contemporary mathlib form,
not the classical literature one.

---

## PHASE 4.5 — Diamond / defeq risk assessment (`def` / `class` / `instance` only)

A definition that *would* belong in mathlib mathematically can still be a bad
addition if it creates typeclass diamonds, introduces defeq problems, or makes
elaboration brittle. This phase asks: *if we added this to mathlib, would it
cause infrastructure trouble?*

**Scope:** runs for `def`, `abbrev`, `structure`, `inductive`, `class`,
`instance`. **Skipped** for `theorem`/`lemma`/`proposition` (those don't
introduce definitional equalities or typeclass-search paths). When skipped,
print a one-line "n/a — declaration kind is <kind>" and move to Phase 5.

### 4.5a. Risk table (REQUIRED ARTIFACT when not skipped)

```
### Diamond / defeq risk — `<Foo.bar>`

| # | Risk                          | Verdict   | Evidence / rationale                                                |
|---|-------------------------------|-----------|---------------------------------------------------------------------|
| 1 | Typeclass diamond            | none/low/HIGH | <if HIGH: name the two instance paths and the common target>     |
| 2 | Reducibility leak            | none/low/HIGH | <`@[reducible]` exposes the body to defeq-checking everywhere; risk if body has non-trivial computation> |
| 3 | Non-canonical unfolding      | none/low/HIGH | <does `simp` or `rfl` unfold this in ways that surprise the user?> |
| 4 | Instance priority collision  | none/low/HIGH | <if this is an `instance`: does it have an explicit priority? Without one, mathlib's default `100` may collide with a near-miss instance> |
| 5 | Universe-polymorphism issues | none/low/HIGH | <does the body force a universe annotation that breaks polymorphic call sites?> |
| 6 | Coercion ambiguity           | none/low/HIGH | <if there's a `CoeFun` or `CoeSort`: does it compete with mathlib's existing coercions?> |
```

The six rows are mandatory. For each, fill `none` / `low` / `HIGH` with at
least a sentence of rationale. A worker who writes `none — no diamond` six
times without checking the actual instance graph has skipped the phase.

### 4.5b. Risk verdict (REQUIRED ARTIFACT)

```
### Risk verdict (Phase 4.5)

Overall risk: NONE | LOW | HIGH
Top risks: <list any rows marked HIGH; or "none">
Recommended mitigations (if HIGH):
- <one mitigation per HIGH row>
```

If overall risk is `HIGH`, Phase 7's verdict gate adds a constraint:
- `YES-add-as-is` requires the worker to address each HIGH-risk row in the
  verdict's rationale (explain why the risk is acceptable / how it's mitigated)
- `YES-but-generalise-first` requires the proposed restatement to NOT
  re-introduce the same risks
- All other buckets are unaffected (NO buckets don't add the def to mathlib;
  BORDERLINE surfaces the risks as numbered questions)

### 4.5c. How to actually check

These risks aren't always obvious from the source. Use these probes:

- **Diamond probe.** `#synth <Foo.bar>` (or `set_option trace.Meta.synthInstance true`)
  to see what typeclass-search picks. If the chosen instance depends on the
  order of imports, that's a near-miss diamond.
- **Reducibility probe.** `example : <body> = <Foo.bar args> := rfl` — if
  `rfl` works without the `@[reducible]` attribute, the def is semi-reducible
  and may surprise downstream consumers. (Often fine; just check.)
- **Coercion probe.** `#check (instance : CoeFun <Foo.bar> _)` and similar
  — does mathlib have a competing coercion path?
- **Universe probe.** Try the def with `Type 0`, `Type 1`, `Type*` and see
  if any universe constraint is forced.

These probes are CHEAP — running them is part of the phase, not optional.

---

## PHASE 5 — Mathlib search

The five-method search from `references/mathlib-search.md`. Read that doc in full
before this phase. Same shape as `/cleanup` Phase 4 audit item 13.

### 5a. Five-method search block (REQUIRED ARTIFACT)

```
### Mathlib search-status: `<Foo.bar>`

[A] Lean-Finder       <queries tried>            <hits / no hits / n/a: reason>
[B] Loogle            <type-pattern queries>     <hits / no hits / n/a: reason>
[C] LeanSearch        <natural-language queries> <hits / no hits / n/a: reason>
[D] Grep mathlib src  <terms tried>              <hits / no hits / n/a: reason>
[E] Name pattern      <lean_local_search terms>  <hits / no hits / n/a: reason>

Searched for both:
  - the user's current form
  - the literature-standard form from Phase 3 (especially important if it's
    more general — mathlib often has the general form even when the specialisation
    feels novel)

Concluded: <one of:>
  - "found in mathlib as <full qualified name>; identical form"
  - "found in mathlib as <full qualified name>; more general form (we'd be a specialisation)"
  - "found a partial match (<name>); covers part of what we want"
  - "found building blocks (<list of mathlib lemmas>); composition would yield our form"
  - "not in mathlib (all 5 methods exhausted, plus the literature-standard form)"
```

The "search for both forms" instruction is load-bearing: mathlib reliably has
the general form (modules, measurable functions, additive groups) even when
the user's form is specific (vector spaces, continuous functions, real scalars).
The general-form search catches NO-mathlib-has-it cases that the user's-form
search would miss.

---

## PHASE 6 — Composition check (+ call-sites signal)

### 6.0. Call-sites grep — first-class composability signal (REQUIRED ARTIFACT)

Before sketching compositions, grep the declaration's own call sites in the
project. The call-site pattern is a first-class composability signal:

```bash
PROJ=<project root>
QUALIFIED="<Foo.bar>"
# Look for both qualified and dot-notation usages
grep -rn "\\b${QUALIFIED//./\\.}\\b" "${PROJ}" \
  --include="*.lean" \
  --exclude-dir=".lake" \
  --exclude-dir="_out" \
  | grep -v "^${PROJ}/<declaring file>"
```

```
### Call sites — `<Foo.bar>`

Internal use count: <K>  (within the same project, NOT counting the declaring file)
External-to-file callers: <N distinct files>

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| Foo/Other.lean:42              | `... Foo.bar h1 h2 ...`                                   |
| Foo/Third.lean:88              | `... hg.add (Foo.bar hf)`                                 |
| Bar.lean:14                    | `... Foo.bar` (dot notation: `.bar`)                      |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `<Foo.bar>`?):
  - <one row per inline re-derivation found; or "(none)">
```

### 6.0.1. What the call-sites pattern tells you

| Pattern | Composability signal | Phase 7 leaning |
|---|---|---|
| K ≥ 3 internal uses, no inline re-derivation elsewhere | Real API; consumers depend on it | YES-* bucket |
| K = 0 internal uses BUT the same statement is re-derived inline at ≥1 site | NO-composable: it's a wrapper that consumers bypass; whether intentionally or because they don't know about it | NO-composable-from-mathlib OR NO-mathlib-has-it (if mathlib has it) |
| K = 0 internal uses, no inline re-derivation | Dead code? Brand new + unused so far? Re-check Step 8 of `/overview` | Junk OR genuinely-new (BORDERLINE) |
| K = 1 internal use only | Possibly the wrong abstraction — could be inlined | Lean toward NO-composable |
| K ≥ 1 use **outside the project** (downstream library) | Public-API signal; consumers exist | YES-* bucket |

The call-sites table is required: a missing table fails the gate (same shape
as Phase 5 / Phase 4). "Didn't grep call sites" is not a valid skip.

### 6.0.2. Feeding back into Phase 2

If the call-sites grep reveals `K = 0` for a one-liner (per Phase 2b) and
no defeq/diamond/API exemption was identified, the case for NO is now
*much* stronger. Phase 7's verdict gate cross-references this: a YES
verdict on a one-liner with `K = 0` and no exemption requires the rationale
to explicitly justify why the def is worth shipping despite having no
current consumers and no exemption — usually because mathlib *should* use
it elsewhere and the API gap is the reason it's unused locally.

### Composition check

Even when mathlib doesn't have our exact form, sometimes it has primitives that
compose trivially to give us the result. In that case, no new lemma is needed —
inline at the call site.

### 6a. Composition attempt (REQUIRED ARTIFACT)

Sketch a proof of the user's statement using only:
- Mathlib's existing decls (cited by qualified name)
- ≤3 chained calls

```
### Composition check (Phase 6)

Can `<Foo.bar>` be derived from mathlib in ≤3 chained calls?

Attempt 1: <sketch — e.g. `Foo.mp (Bar.baz hx)`>
  - Mathlib decls used: <list>
  - Result: succeeds / fails / partial
  - Notes: <if partial, what's missing>

Attempt 2 (if Attempt 1 partial): <different angle>
  - ...

Conclusion: COMPOSABLE | NOT-COMPOSABLE
- If COMPOSABLE: the composition sketch goes in Phase 7's NO-composable evidence
- If NOT-COMPOSABLE: Phase 7 considers the YES verdicts
```

### 6b. Composition heuristics

Don't accept a "composition" that's actually a new proof in disguise:

| Pattern | Composable? |
|---|---|
| `(Foo.bar h).symm` (just `.symm` on existing) | yes |
| `Foo.bar.trans Bar.baz` (`.trans` chain) | yes |
| `Foo.bar (Bar.baz hx)` (one function call) | yes |
| `Foo.bar h |>.choose_spec.2` (projection chain) | yes (1 call) |
| `have h := Foo.bar; have h' := Bar.baz h; exact Quux.zog h'` (multiple `have`s with non-trivial reasoning between) | NO — this is a proof |
| Anything requiring `by rw [...]; ring_nf; aesop` | NO — that's a real proof |
| `simp [Foo.bar, Bar.baz, Quux.zog]` closing the goal | borderline — record as "trivial simp composition; user decides if worth a lemma" |

---

## PHASE 7 — Verdict

Synthesise. One bucket. Required evidence per bucket (see "The verdicts" table at
the top — Phase 7 fails if the required artifact is missing).

### 7a. Verdict block (REQUIRED ARTIFACT)

```
## Verdict: `<Foo.bar>`

**Category:** <YES-add-as-is | YES-but-generalise-first | NO-mathlib-has-it | NO-composable-from-mathlib | BORDERLINE-needs-human>

**Evidence:**
- Literature search (Phase 3): <pointer back to artifact; key finding>
- Generality analysis (Phase 4): <verdict was MAXIMALLY GENERAL | STRICTLY NARROWER>
- Mathlib search (Phase 5): <one-line conclusion>
- Composition check (Phase 6): <COMPOSABLE | NOT-COMPOSABLE>

**Rationale (1–2 paragraphs):**

<Synthesise. Concrete, not "the searches showed". Cite the specific evidence.>

**Refactor-actionable bar (REQUIRED).** The bucket-specific section below is
not optional flavour text — it's the report's load-bearing content. The
report is simultaneously a *refactor plan* (for NO verdicts) and an
*upstreaming plan* (for YES verdicts). A reader should be able to act on
this single decl's section without re-reading the lit search, the Phase
4-6 artifacts, or the mathlib docs. A bare verdict list is insufficient.

<bucket-specific section, mandatory:>

For YES-add-as-is:
  WHY add it (REQUIRED — 1-2 paragraphs, refactor-actionable detail):
    - What new mathematical content does it contribute that mathlib is missing?
    - Cite the *specific gap*: a mathlib TODO, a known-missing API, a recurring
      reformulation users do manually because mathlib lacks the canonical form,
      etc. "Searched and didn't find it" is not enough — name the gap.
    - How does it compose with mathlib's existing API? (Which mathlib lemmas
      would now apply that didn't before?)
  Proposed mathlib location:    <Mathlib/<Area>/<File>.lean>
  Proposed PR title:            "feat(<area>): add <Foo.bar>"
  PR grouping (if applicable):  e.g., "ship with related <Foo.baz> as one PR"
                                — naming any other decls in this batch with
                                related YES verdicts is required so the PR
                                is the right grain.
  Pre-PR checklist before opening:
    - [ ] `/generalise <Foo.bar>` — confirm no easy further weakening
    - [ ] `/cleanup <file> <Foo.bar>` — full audit + diff gates
    - [ ] Pick a mathlib reviewer based on `Mathlib/<Area>/` recent commits

For YES-but-generalise-first:
  Reason for the generalisation: <one or both of:>
    - LITERATURE-WEAKENING: Phase 4b found the user's form strictly narrower than the literature-standard form
    - MODERN-IDIOM (Bourbaki 2.0): Phase 4c found a contemporary mathlib formulation that is a real organisational improvement
  Proposed restatement:
  ```lean
  theorem <new_name> <generalised signature> : <generalised conclusion> := by
    sorry  -- needs work; current proof may or may not survive
  ```
  Estimated cost of regeneralisation: <CHEAP | MODERATE | EXPENSIVE>
  Note: EXPENSIVE does not downgrade the verdict. Mathlib's value is in
        getting the right form, not the cheap form.
  Mathlib downstream this enables (REQUIRED if MODERN-IDIOM):
    - <concrete list — what existing mathlib API composes better with the new form>
    - <what proofs were blocked by the old form>
  Next action: run `/generalise <Foo.bar>` (which will tension against both
  the literature-standard form from Phase 3 and the modern-idiom form from
  Phase 4c) before opening a PR.

For NO-mathlib-has-it:
  WHY not (REQUIRED — refactor-actionable detail):
    - Mathlib already has it. Cite the exact mathlib decl and explain how the
      user's form follows directly (or how it specialises from a more general
      mathlib form). The detail must be enough that a refactor can be planned
      from this entry alone.
  Existing mathlib decl:        `<Mathlib.Qualified.Name>`
  Located at:                   `Mathlib/<Area>/<File>.lean:<line>`
  Our form follows in ≤1 line:
  ```lean
  example : <our statement> := <mathlib_call> ...
  ```
  Call sites in our project (from Phase 6.0):  K
  Refactor plan: at each of those K sites, replace `<Foo.bar> ...` with
                 `<Mathlib.Qualified.Name> ...` (note any argument-order
                 differences — dot notation vs. positional, etc.)
  Next action: delete `<Foo.bar>` from the project; update the K call sites.

For NO-composable-from-mathlib:
  WHY not (REQUIRED — refactor-actionable detail):
    - Mathlib has the building blocks; the user's form is a 1-3 mathlib-call
      composition. Name the building blocks. The composition sketch below
      must be specific enough that inlining is mechanical.
  Mathlib building blocks:      <list of qualified names with full paths>
  Composition sketch (≤3 lines):
  ```lean
  example : <our statement> := <mathlib_call1> (<mathlib_call2> ...)
  ```
  Call sites in our project (from Phase 6.0):  K
  Refactor plan: at each of those K sites, inline the composition above
                 (verify the argument types match; some sites may need
                 light adjustment for implicit-vs-explicit argument flow).
  Next action: delete `<Foo.bar>` from the project; inline the composition at
  every call site.

For BORDERLINE-needs-human:
  Numbered questions (≤5):
    1. <question — answerable yes/no or short response>
    2. ...
  Next action: user answers the questions; re-run `/mathlibable <Foo.bar>` to
  resolve the verdict. (Or commit to a verdict directly — the questions exist
  to surface the judgment, not to bind it.)
```

### 7b. Verdict gate

The verdict block FAILS if:
- The required evidence pointers from the bucket's row in "The verdicts" table
  aren't present in the artifacts from Phases 3–6 (the worker is claiming a
  verdict without the work).
- The bucket is YES-add-as-is but Phase 4b verdict was STRICTLY NARROWER
  THAN STANDARD (the worker should have picked YES-but-generalise-first).
- The bucket is YES-add-as-is but Phase 4c verdict was "modern idiom
  available" AND the modern restatement is a real mathematical improvement
  (the worker should have picked YES-but-generalise-first with reason
  MODERN-IDIOM).
- The bucket is YES-but-generalise-first but no proposed restatement is given,
  OR the proposed restatement does not match the literature-standard / modern-
  idiom target from Phase 4b / 4c.
- The bucket is YES-but-generalise-first with reason MODERN-IDIOM but the
  rationale section lists no concrete mathlib downstream consequences (the
  "looks cooler in category theory" trap — Phase 7 requires real downstream
  evidence).
- The bucket is NO-mathlib-has-it but Phase 5's conclusion was not "found in
  mathlib as …" (the worker invented a decl).
- The bucket is NO-mathlib-has-it but Phase 4c said the mathlib version is
  in an older formulation AND the user's contribution would be the
  modernisation (in that case the verdict is YES-add-as-is, with the
  rationale citing the modernisation per Phase 4c — even though mathlib has
  *something* by that name).
- The bucket is NO-composable-from-mathlib but Phase 6's conclusion was
  NOT-COMPOSABLE.
- The bucket is BORDERLINE but no numbered questions are listed.
- The decl is a one-liner from Phase 2b with `ONE-LINER WITHOUT-EXEMPTION` AND
  the verdict is YES-add-as-is or YES-but-generalise-first without the
  rationale section explicitly addressing why the one-liner is justified.
- The decl is a `def`/`class`/`instance` with Phase-4.5 overall risk `HIGH`
  AND the verdict is YES-add-as-is without the rationale section addressing
  each HIGH-risk row (acceptance reason or mitigation).
- The bucket is **anything other than BORDERLINE** but cost is cited as the
  reason — "too expensive to generalise so we'll ship the narrow form" is a
  BORDERLINE question to the user, not a self-resolving verdict downgrade.
- The Phase 6.0 call-sites table is missing or partial (one row per caller
  required; "internal use count" + "inline-derivation grep" fields filled).
- For YES verdicts: the bucket-specific WHY paragraph names no concrete
  mathlib gap / TODO / missing-API anchor (the "searched and didn't find it"
  trap — Phase 7 requires *naming the gap*, not just asserting absence).
- For NO verdicts: the bucket-specific WHY paragraph does not include the
  refactor plan ("at each of the K call sites, do X") at refactor-actionable
  detail. A bare "use Mathlib.X instead" without naming the K call sites is
  not enough — the gate fails.

Failed verdict → re-run Phase 7 only (artifacts from 3–6 are preserved).

---

## PHASE 8 — Report

The consolidated report is just the concatenation of the required artifacts in
phase order. Print to chat:

```
## /mathlibable report — `<Foo.bar>`

<Phase 0 baseline block>

<Phase 1 statement block>

<Phase 2 size classification block>

<Phase 3 literature table + literature summary block>

<Phase 4 generality status table + generality verdict block>

<Phase 5 mathlib search-status block>

<Phase 6 composition check block>

<Phase 7 verdict block>

---

## Next step

<the bucket's recommended next action, verbatim from Phase 7>
```

---

## Mode B — File / multi-file (orchestrator-worker)

When the argument is a `.lean` file (or multiple), `/mathlibable` enumerates
every public declaration in the file(s), pre-filters obvious skips, then
dispatches one `Agent` per remaining declaration, each running the full
10-phase workflow.

### B0 — Enumerate

Validate every file argument exists, then walk the file extracting declaration
heads. The enumeration regex must cover the **Lean 4 module system** —
declarations appear with `public` (and sometimes `noncomputable` / `protected`)
modifiers, and may carry one or more `@[attr]` prefixes:

```
^\s*(@\[[^\]]+\]\s+)*(noncomputable\s+)?(protected\s+)?(public\s+)?(theorem|lemma|def|abbrev|structure|inductive|class|instance|proposition|corollary|example)\b
```

Examples this regex must match (and the naive `^(theorem|lemma|def|...)`
pattern does NOT):

```lean
public def Foo : ...
@[expose] public def Bar : ...
@[simp] public lemma baz : ...
public instance : Foo X := ...
public theorem main : ...
noncomputable public def Quux : ...
@[simp, fun_prop] public theorem zorg : ...
```

Skip enumeration if the declaration head matches:
- the line begins with `private` / `local` (or `protected private`)
- the file is under `test/` or `examples/` (or `Test/`, `Examples/`)
- the matched name ends in `_aux`
- the immediately preceding docstring (a contiguous `/-- ... -/` ending
  on the line above) starts with `internal` or `auxiliary`

**Naming and qualification.** For each enumerated decl, compute the
*qualified* name as `<NamespaceFromOpenScopes>.<name>` — walk back through
the file's `namespace … end namespace` blocks to build the prefix. Use the
qualified name throughout B1/B2; bare names are unsafe (see B1).

### B1 — Pre-filter (cheap, namespace-aware)

For each enumerated declaration, run the cheap SKIP checks first:

- `private` / `local` modifier (already filtered in B0, but re-check)
- in `test/` or `examples/`
- name ends in `_aux`
- docstring starts with `internal` or `auxiliary`
- the **qualified** name already exists in mathlib — cheap grep over
  `.lake/packages/mathlib/Mathlib/` for the *namespace-aware* pattern
  `\b(theorem|lemma|def|...)\s+<Qualified.Name>\b` (and dot-notation
  variants like `<Namespace>.<name>`). **Do NOT match on bare name alone.**

**The bare-name SKIP is unsafe and has been removed.** Common short names
(`coeFun`, `translateCM`, `continuous_coeFun`, `finite_norm_le`) collide
with unrelated mathlib decls in other namespaces / types and would wrongly
drop genuine contributions. The cheap check stays cheap; it just requires
the qualified name match. A bare-name hit without namespace agreement
records as `MAYBE-COLLISION` and gets a full Agent run (it might be a
genuine contribution; the full workflow's Phase 5 mathlib search will
resolve it).

Record each pre-filtered SKIP decl with verdict `SKIP` and a one-line
reason. They do NOT get a full Agent run.

### B2 — Dispatch (sequential, def-first, with verdict inheritance)

#### Def-first ordering

**Within each file, dispatch defs (`def` / `abbrev` / `structure` /
`inductive` / `class` / `instance`) before their dependent lemmas.** A
lemma's verdict frequently hinges on the verdict of the def it's about;
processing in the wrong order forces the lemma Agent to re-derive
information the def Agent already produced. Across files, dispatch in
import order (a file's defs are evaluated before downstream files'
lemmas).

#### Verdict inheritance for glue lemmas

A *glue lemma* is a lemma whose body is one of:

- `:= rfl`
- `:= Iff.rfl`
- `:= by rfl` / `:= by exact rfl`
- A single `unfold` / direct definitional equality between an alias and
  its definition

If a glue lemma's statement involves a parent def already assessed in this
batch, **inherit the parent's verdict — do NOT dispatch a separate full
Agent run.** Record verdict as `INHERITED-<parent-verdict>` and cite the
parent decl. The lit search + mathlib search would just re-discover what
the parent assessment already established.

#### Re-aim rule (don't blanket-inherit NO)

When the parent def's verdict was `NO-mathlib-has-it` *because mathlib has
a more general def* `D'`, do NOT blanket-inherit NO on a dependent lemma.
Instead, **re-aim** the lemma at `D'`:

- If `D'` has an analogous lemma in mathlib already → record the dependent
  lemma's verdict as `NO-mathlib-has-it` citing the mathlib lemma about
  `D'`. The re-aim was a hit; the lemma is redundant.
- If `D'` has no analogous lemma in mathlib → the lemma may be worth
  contributing, *stated against `D'`*. Dispatch a full Agent run with the
  re-aimed statement (the dispatch args include the re-aim target so the
  worker knows to evaluate the `D'`-stated form, not the original).
  Verdict is likely `YES-but-generalise-first` with the re-aim spelled
  out.

Only blanket-inherit NO when the parent def has no mathlib counterpart
at all (the parent was `NO-composable-from-mathlib` or `BORDERLINE`, not
`NO-mathlib-has-it`).

#### Anonymous instance handling

A `public instance` declaration with no user-given name has no qualified
name to pass as a dispatch handle. For each anonymous instance, synthesize
a handle:

```
<File>__<Line>__inst_<seq>     # e.g., Foo_Bar__lean__115__inst_0
```

Pass this as the dispatch arg and include the file:line and the elaborated
instance signature in the prompt so the Agent can read the actual decl. The
verdict table records the synthesised handle in column 1 with the resolved
signature in the rationale column.

#### Dispatch call

For each surviving (non-inherited, non-anonymous-handled, non-pre-filtered)
declaration, dispatch:

```
Skill(skill="mathlib-quality:mathlibable",
      args="<Qualified.Decl.Name> "
        + "--refs=<absolute path to skills/mathlib-quality/references/> "
        + "[--reaim=<Qualified.D'.Name>]")
```

**`--refs` is mandatory.** Worker subagents resolve `references/*.md`
relative to *their* working directory, not the plugin cache where the docs
live. Pass an absolute path (the orchestrator can compute it from the skill
manifest's location) so Phase 5 (mathlib search) and Phase 7 (verdict
rationale) actually consult the real
`mathlib-search.md` and `mathlibable-verdicts.md`.

**`--reaim`** is included only when the re-aim rule above fires.

**Sequential**, one decl at a time. Each Agent's WebSearch + ChatGPT MCP +
nine-channel lit search is already heavy; running many in parallel doesn't
help and contends on external rate limits.

Between dispatches, the orchestrator emits exactly one line:

```
**K/N decls assessed. R YES-add-as-is, S YES-but-generalise, T NO-mathlib-has-it, U NO-composable, V BORDERLINE, W INHERITED.** Continuing.
```

No "let me check / let me verify / quick sanity check" — those are the
forbidden orchestrator patterns from `/cleanup-all`. The verdict is captured
when the Agent returns; the orchestrator records and moves on.

Each Agent's full Phase-8 report (with all artifacts: lit table, generality
analysis, modern-idiom check, mathlib search, composition check, verdict
rationale, **per-bucket WHY+alternative — see Phase 7**) is stored at
`.mathlib-quality/mathlibable/<decl>.md` for later reference. The
orchestrator only keeps the verdict bucket + one-line rationale in working
memory.

**Persist findings to disk no matter what.** Each Agent run takes minutes
to hours; discarding the full Phase-8 report at the end of a batch is a
serious defect. The orchestrator must verify each `.md` file was written
before recording the verdict in the table.

### B3 — Aggregate

After all dispatches return, build the verdict table (same shape as
`/overview` Step 9c) plus the per-bucket action lists (same shape as Step
9d). Write the aggregated report to `MATHLIBABLE_REPORT.md` in the project
root and print a summary to chat.

### B4 — Summary output

```
## /mathlibable batch report — <files processed>

### Files
- File1.lean (N1 public decls)
- File2.lean (N2 public decls)
- ...

### Totals
- Public decls enumerated:           ∑Ni
- Pre-filtered (SKIP):               K0
- Full /mathlibable runs:            ∑Ni − K0
- Wall time:                          <H>h <M>m

### Verdict counts
- YES-add-as-is:                     V1
- YES-but-generalise-first:          V2
- NO-mathlib-has-it:                 V3
- NO-composable-from-mathlib:        V4
- BORDERLINE-needs-human:            V5

### Per-bucket action lists
[same shape as /overview Step 9d]

Per-decl detail reports: .mathlib-quality/mathlibable/<decl>.md
```

### Mode B caveats

- **No `--parallel` flag.** Sequential is intentional. Lit-search APIs rate-
  limit; ChatGPT MCP serialises; the wall-time gain from parallelism is
  small and the verdict noise from contended API rate-limiting is real.
- **Resume on interruption.** If the orchestrator is interrupted mid-batch,
  re-running on the same file set skips decls that already have a
  `.mathlib-quality/mathlibable/<decl>.md` report — no double-work.
- **Use this OR `/overview --skip-mathlibable` then `/mathlibable <files>`**.
  The latter splits the overview-without-mathlibable from the mathlibable-
  per-file work, useful when you want the structural overview first then
  decide which files are worth the slow per-decl assessment.

---

## What this command does NOT do

- **Auto-submit to mathlib.** Even YES-add-as-is just points at the right file
  and tells the user to open a PR. The actual PR is the user's responsibility
  (and `/pre-submit` covers the pre-submission checklist).
- **Run the generalisation.** YES-but-generalise-first names what would be a
  better statement and hands off to `/generalise`. It does not produce the
  re-proved declaration.
- **Decide for the user on BORDERLINE.** The numbered questions exist to
  surface the judgment; the user makes the call.
- **Re-prove anything.** Phase 6's composition check is a sketch, not a real
  derivation. If the sketch goes through, the user inlines it; the skill does
  not run `lake build` on the composition.
- **Handle multiple declarations.** One decl per invocation. For "should this
  whole file go in mathlib?", run `/overview` first to get the inventory and
  then run `/mathlibable` per public declaration.

---

## Reference

- `skills/mathlib-quality/references/mathlib-search.md` — five-method search
  (Phase 5 reads this in full).
- `skills/mathlib-quality/references/mathlibable-verdicts.md` — verdict
  definitions, worked examples per bucket, the canonical case studies
  (modules-not-vector-spaces, translate-of-continuous-function, etc.).
  Workers read this in Phase 7.
- `skills/mathlib-quality/references/generalisation-patterns.md` — the
  mechanical weakening catalogue. Phase 4 uses it alongside the
  literature-standard form to identify weakening opportunities.
- Related commands:
  - `/generalise <Foo.bar>` — the natural follow-up to YES-but-generalise-first
  - `/cleanup <file> <Foo.bar>` — the natural follow-up to YES-add-as-is (the
    full audit before opening a mathlib PR)
  - `/pre-submit` — the final checklist before opening any mathlib PR
