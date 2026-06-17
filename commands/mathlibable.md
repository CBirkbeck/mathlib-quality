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
/mathlibable <Foo.bar>              # one declaration; literature width auto-picked from size
/mathlibable <Foo.bar> --exhaustive # force the wider literature sweep even for small decls
/mathlibable <Foo.bar> --quick      # only the bounded literature protocol (use sparingly; downgrades the verdict's evidence weight)
```

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
PHASE 0   DOCTOR              lake build clean; the decl exists and elaborates
PHASE 1   COMPREHEND          read the decl; capture its mathematical statement in prose
PHASE 2   SIZE + ONE-LINE     BIG/SMALL classification; one-line check with defeq/diamond/API exemptions
PHASE 3   LITERATURE          bounded protocol always; exhaustive for BIG or --exhaustive
PHASE 4   GENERALITY          compare current form to the literature-standard form
PHASE 4.5 DIAMOND/DEFEQ RISK  for `def`/`class`/`instance` only; six-row risk table
PHASE 5   MATHLIB             five-method exhaustive search (Loogle / LeanSearch / Lean-Finder / grep / lean_local_search)
PHASE 6   COMPOSITION         can mathlib's existing primitives compose to give the form?
PHASE 7   VERDICT             one of the five buckets, with evidence trail
PHASE 8   REPORT              consolidated artifact
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

## PHASE 2 — Size classification + one-line check

Two cheap checks before the expensive literature search.

### 2a. Big vs small (REQUIRED ARTIFACT)

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
### Size classification (Phase 2)

Verdict: BIG | SMALL
Reason: <one line>

Literature-search width auto-picked: EXHAUSTIVE | BOUNDED
(BIG → EXHAUSTIVE automatically; SMALL → BOUNDED; `--exhaustive` overrides to EXHAUSTIVE;
 `--quick` overrides to BOUNDED. EXHAUSTIVE always wins if the user passed it.)
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

## PHASE 3 — Literature search

The single most important phase. **The skill exists to do this carefully.** Skipping
or short-circuiting this phase produces wrong verdicts. Workers who write
"searched: didn't find anything" without an artifact fail the gate.

### 3a. Bounded protocol (ALWAYS runs)

Four channels. Print one row per query attempted, including the queries that
returned nothing.

```
### Literature search table — bounded protocol

| # | Channel               | Query                                                   | Hit? | Standard form found | Notes |
|---|------------------------|---------------------------------------------------------|------|----------------------|-------|
| 1 | WebSearch             | "translate of continuous function" definition           | yes  | $`(\tau_a f)(x) := f(x-a)`` | Wikipedia: "Translation operator"; standard in harmonic analysis |
| 2 | WebSearch             | "shift operator" function definition continuous         | yes  | same as #1; also called "shift"    | name varies; "translate" / "shift" both standard |
| 3 | WebSearch             | "translation of a function" L^p generality              | yes  | well-defined for any measurable f  | strictly more general — continuity is overkill |
| 4 | ChatGPT MCP           | "What is the standard mathematical definition of the translate of a continuous function, and at what level of generality is it usually stated?" | yes  | same as #3 — `L^p` or measurable functions, NOT continuous specifically | confirms the form found in WebSearch |
| 5 | local references      | grep `.mathlib-quality/references/` for "translation"   | n/a  | (no references dir)  | skipped |
| 6 | local references      | (n/a)                                                   | n/a  | n/a                  | n/a — directory absent |
```

The bounded protocol passes when:
- WebSearch ran at least **3 distinct queries** at different generality levels
  (specific form, the most-general form, the "well-known names" form).
- ChatGPT MCP ran at least **1 query** asking explicitly for the standard form
  and its generality.
- Local references were checked (or recorded `n/a` with reason).

`Standard form found` is the most general formulation the search returned.
This is what Phase 4 compares the user's form against.

### 3b. Exhaustive protocol (BIG decls or `--exhaustive`)

On top of the bounded protocol, ALSO check:

```
| # | Channel                          | Query                                | Hit? | Standard form found |
|---|----------------------------------|--------------------------------------|------|----------------------|
| 7 | nLab                            | <concept name>                       | ...  | ...                  |
| 8 | Stacks Project (if alg geom)    | <concept name>                       | ...  | ...                  |
| 9 | MathOverflow / Math.StackExchange| <concept name> generality           | ...  | ...                  |
| 10| recent arXiv (last 5 years)     | <concept name> + adjective           | ...  | ...                  |
| 11| nCatLab (if categorical)        | <concept name>                       | ...  | ...                  |
```

For BIG decls, the exhaustive protocol must show at least three of channels
7–11 attempted (not all are applicable to every concept — record `n/a` with
a reason when not).

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
### Generality verdict (Phase 4)

The current form is: MAXIMALLY GENERAL | STRICTLY NARROWER THAN STANDARD
Number of weakening opportunities found: K
Proposed restatement (if STRICTLY NARROWER):

<restate the declaration in the most general form, with the new Lean signature>

Cost of restatement: <CHEAP — mechanical rewrite | MODERATE — proof needs adjustments | EXPENSIVE — proof needs new ideas>
```

If MAXIMALLY GENERAL → Phase 7 considers YES-add-as-is or NO buckets only.
If STRICTLY NARROWER → Phase 7 considers YES-but-generalise-first prominently.

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

## PHASE 6 — Composition check

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

<bucket-specific section, mandatory:>

For YES-add-as-is:
  Proposed mathlib location:    <Mathlib/<Area>/<File>.lean>
  Proposed PR title:            "feat(<area>): add <Foo.bar>"
  Pre-PR checklist before opening:
    - [ ] `/generalise <Foo.bar>` — confirm no easy further weakening
    - [ ] `/cleanup <file> <Foo.bar>` — full audit + diff gates
    - [ ] Pick a mathlib reviewer based on `Mathlib/<Area>/` recent commits

For YES-but-generalise-first:
  Proposed restatement:
  ```lean
  theorem <new_name> <generalised signature> : <generalised conclusion> := by
    sorry  -- needs work; current proof may or may not survive
  ```
  Estimated cost of regeneralisation: <CHEAP | MODERATE | EXPENSIVE>
  Next action: run `/generalise <Foo.bar>` (which will tension against the
  literature-standard form from Phase 3) before opening a PR.

For NO-mathlib-has-it:
  Existing mathlib decl:        `<Mathlib.Qualified.Name>`
  Located at:                   `Mathlib/<Area>/<File>.lean:<line>`
  Our form follows in ≤1 line:
  ```lean
  example : <our statement> := <mathlib_call> ...
  ```
  Next action: delete `<Foo.bar>` from the project; update call sites to use
  `<Mathlib.Qualified.Name>` directly.

For NO-composable-from-mathlib:
  Mathlib building blocks:      <list of qualified names>
  Composition sketch (≤3 lines):
  ```lean
  example : <our statement> := <mathlib_call1> (<mathlib_call2> ...)
  ```
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
- The bucket is YES-add-as-is but Phase 4 verdict was STRICTLY NARROWER (the
  worker should have picked YES-but-generalise-first).
- The bucket is NO-mathlib-has-it but Phase 5's conclusion was not "found in
  mathlib as …" (the worker invented a decl).
- The bucket is NO-composable-from-mathlib but Phase 6's conclusion was
  NOT-COMPOSABLE.
- The bucket is BORDERLINE but no numbered questions are listed.
- The decl is a one-liner from Phase 2b with `ONE-LINER WITHOUT-EXEMPTION` AND
  the verdict is YES-add-as-is or YES-but-generalise-first without the
  rationale section explicitly addressing why the one-liner is justified.
- The decl is a `def`/`class`/`instance` with Phase-4.5 overall risk `HIGH`
  AND the verdict is YES-add-as-is without the rationale section addressing
  each HIGH-risk row (acceptance reason or mitigation).

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
