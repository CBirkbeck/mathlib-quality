# The Tau Ceti red team: checklist, evidence, Astra, fixes

Companion to `commands/redteam.md`. The stance throughout: **every definition and statement
is wrong until you have tried to break it and failed.** A cell in the audit matrix reads `"ok"`
only when you ran that category's checks on that declaration.

## 1. The checklist

For each declaration, every category. The tools named are the lean-lsp MCP's unless stated.

### correctness — definitions (`def`, `abbrev`, `structure`, `class`, `inductive`, `instance`)

- **Say the standard definition first** — from the roadmap, the file's references, the
  literature, or Astra (prompt A2 can ask). Then compare it with the Lean clause by clause:
  a missing axiom (too weak), an extra one (too strong), quantifier order, direction,
  sign and normalisation conventions, indexing (`Finset.range n` is `{0, …, n-1}`), and the
  degenerate cases (empty, zero, `n = 0`, the trivial group, the zero ring, characteristic 2).
- **Witness test.** Build a standard example: `example : IsFoo standardExample := …`. If
  you cannot, the definition is suspect.
- **Non-witness test.** Refute a standard non-example: `example : ¬ IsFoo nonExample := …`.
  A non-example that satisfies it means the definition is wrong.
- **Value test**, for anything computable: evaluate small cases (`decide`, `norm_num`,
  `rfl`, `simp`) and compare with known values.
- **Mathlib comparison.** If Mathlib has the notion, prove agreement
  (`example : tcFoo x = Mathlib.foo x := …`). Failure means a wrong definition; success
  means a duplicate. Either is a finding.
- **Junk values** (table below): does the definition return Lean's junk value where the
  mathematics has no value, or a different one — and does anything downstream rely on it?
- **Unexercised predicates.** A `Prop`-valued definition, class or hypothesis structure with
  no nontrivial witness and no consumer anywhere: try to prove it unsatisfiable, or always
  true. Either is CRITICAL.
- **Instances.** Does it agree with Mathlib's instance on the same type (a diamond)? Try
  `example : (inst₁ : Foo T) = inst₂ := rfl`, then `with_reducible_and_instances rfl`.

### correctness — theorems

- **Restate it in words**, with every binder and hypothesis, and set it beside its name,
  docstring, the roadmap's statement and the source. Each mismatch is a finding: the
  docstring claiming more, different objects, missing cases, a different quantifier.
- **Contradictory hypotheses.** Try to derive `False` from them, typeclass assumptions
  included: `example <binders> : False := by simp_all` (then `omega`, `aesop`, `grind`,
  `exact?`). Classic pairs: `[Nontrivial G]` with `Nat.card G = 1`; `[Fact (1 < n)]` at
  `n = 1`; `IsEmpty α` with `Nonempty α`.
- **A conclusion that needs no hypotheses.** `lean_minimal_hypotheses`; then try the
  conclusion outright (`rfl`, `simp`, `trivial`, `decide`). Holding with none is vacuity or
  tautology, unless the name and docstring say exactly that.
- **Tautology.** The conclusion is a hypothesis up to defeq (`exact h`, `h.1`, `id`), or the
  two sides of an `=` or `↔` are defeq.
- **Content moved into hypotheses.** A hypothesis that is the hard part of the claim, or a
  structure that bundles it. Compare with the source's hypotheses.
- **Specialisation test.** Instantiate at a standard concrete case and check the conclusion
  is the known fact: `example : <known fact> := decl …`.
- **Junk-value vacuity.** At the degenerate inputs the hypotheses allow, does the statement
  hold for the wrong reason (`Nat.card G ∣ n` when `G` is infinite and `Nat.card G = 0`)?
- **Name against strength.** `_iff` proving one direction, `_eq` proving `≤`, `_unique`
  without uniqueness.
- **Downstream.** Every consumer of a CRITICAL finding inherits it. Sweep them (section 5).

| Lean's junk value | where | the trap |
|---|---|---|
| `0` | `x / 0`, `0⁻¹` | identities "hold" at `0` |
| `0` | `a - b` in `ℕ` when `a < b`; `Int.toNat` of a negative; `Nat.pred 0` | inequalities change meaning |
| `0` | `Nat.card`, `Module.finrank`, `Cardinal.toNat` of something infinite | divisibility and `≤` claims become trivial |
| `0` | `Real.sqrt` of a negative; `Real.log 0`; `Real.log (-x) = Real.log x` | |
| `0` | `sSup ∅`, `sSup` of an unbounded set in `ℝ` | |
| `0` | `deriv` where not differentiable; `∫` of a non-integrable function; `∑'` of a non-summable one | analytic statements hold vacuously |
| `0` | `orderOf` of an element of infinite order; `padicValNat p 0`; `ENNReal.toReal ⊤` | |
| `0` / `⊥` | `Polynomial.natDegree 0` / `Polynomial.degree 0` | |
| arbitrary | `Classical.choose`, `Classical.epsilon` off their hypotheses | |
| everything true | the zero ring, an empty type, `Fin 0` | a missing `[Nontrivial R]` or `[Nonempty α]` |

### generality

- `lean_minimal_hypotheses` on every theorem: explicit hypotheses it does not need.
- **Typeclass weakening**: retry the proof under parents — `Field` → `DivisionRing` or
  `CommRing`, `Group` → `Monoid`, `LinearOrder` → `PartialOrder`, `Fintype` → `Finite`,
  and drop an unused `DecidableEq`. `Skill(mathlib-quality:generalise)` with
  `<file> <decl>` runs the catalogue.
- A special case proved where the general statement is as easy, or is already in the file.
- Over-generalisation too: parameters that never specialise to anything used.
- Count the consumers of a needless assumption: ≥ 3 carrying it makes it MAJOR.

### reuse

- **Mathlib, every declaration, five ways** (`references/mathlib-search.md`): `exact?` at
  the statement (`lean_multi_attempt` in place, or `lean_run_code` with the file's imports),
  `lean_loogle` by type shape, `lean_leansearch` and `lean_leanfinder` by the docstring,
  `lean_state_search` at the goal, and `git grep` in `.lake/packages/mathlib` for the key
  constants. Search the Mathlib pinned in `lake-manifest.json`.
- **Every proof over ~5 lines**: search its goal and its main `have`s. Standard plumbing
  has named lemmas.
- **Definitions assembled from parts**: look for the Mathlib combinator that assembles them.
- **Tau Ceti.** The root `TauCeti.lean` imports nothing, so no single import sees the
  library: `lean_local_search` and `git grep -n -- TauCeti` for the defining expression, the
  distinctive constants, and the concept's names in docstrings. A hit elsewhere is a
  duplicate candidate; prove agreement (`rfl`, `ext`) in a scratch file importing both
  modules to confirm it.
- **Other roadmaps' objects.** When a file builds an object (a group, a ring, a space, a
  functor), grep for other constructions of the same object before accepting this one.
- **General-purpose results.** A statement mentioning only Mathlib notions, which Mathlib
  lacks: run `Skill(mathlib-quality:mathlibable)` on it. A YES verdict is an upstreaming
  candidate — `needs-human`, not a Tau Ceti PR.

### proof

- **Length**: over 30 lines is MINOR, over 50 is MAJOR. Search for a replacement before
  decomposing.
- **Speed**: `lean_profile_proof` on suspects, or `Skill(mathlib-quality:buzz)` on the file.
  Over 1 s is MINOR, over 10 s MAJOR.
- **Brittleness**: long chains of named-lemma `rw`s, `simp only` lists over ~10 lemmas,
  `simpa` closing through unfolding, `erw`, `convert … using` with deep side goals.
- **`change` or `show` without a comment** saying why; reliance on defeq across wrappers
  or coercions.
- **Repeated reasoning**: the same `have` block in several proofs wants a lemma.
- Unexplained `revert`, unused `have`s.

### naming

- Mathlib's conventions (`references/naming-conventions.md`): theorems snake_case,
  describing the conclusion; definitions lowerCamelCase; types, structures and classes
  UpperCamelCase; `_of_` for hypotheses; no typeclass assumptions in names.
- **Tau Ceti's namespace rule** (TauCetiReview `rubrics/naming.md`): material goes in
  `TauCeti`, except dot notation on an existing Lean or Mathlib type, which goes in that
  type's namespace.
- **Doubled namespaces.** A full name written inside its own namespace (`namespace A.B` …
  `theorem A.B.foo`) becomes `A.B.A.B.foo`. The `dupNamespace` linter catches only adjacent
  repeats; read the full names in `lean_file_outline`.
- **Too long.** A name repeating its namespace (`Augmentation.augmentation_foo`), a
  redundant `_of_finite_of_fintype` chain, or over ~50 characters: can a namespace or dot
  notation carry part of it?
- **Overstating** (`_iff`, `_eq`, `_unique`, `_bijective`); a primed name with no unprimed
  one.
- Very long module paths are a placement question.

### api

- Compatibility surface: aliases, `@[deprecated]`, wrappers, forwarding modules.
- Over-exposure and under-exposure: general results left `private`; `@[expose]` without a
  consumer that must unfold.
- Each definition's characteristic API: intro and elim, `_def` and `mem_…_iff`,
  `@[simp]` normal forms, `@[ext]`.
- **Free data**: a structure field no law constrains, so `@[ext]` cannot be derived from
  the fields that matter.
- **Placement**: a statement that mentions only Mathlib notions, with a proof independent of
  this file, belongs in a general file. Imports should be direct and minimal; a whole
  `import Mathlib` is a finding.
- `@[simp]` lemmas that loop or whose left side is not in simp normal form.

### docs

- A module docstring that says what the file does and names its main results, and is
  current.
- A docstring on every public declaration, matching its statement exactly. A docstring
  claiming more than the statement is CRITICAL correctness; a stale one is MINOR docs.
- References for non-trivial mathematics.
- Comments about code that no longer exists. A "defined elsewhere" note points at a reuse
  finding.

### hygiene

Commented-out code; `#check`, `#eval`, `#print`, `#exit`; `set_option trace.*` and
`pp.*`; `set_option linter.* false`; unused `variable`s and imports; stray `example`s;
`TODO`s. (The build runs with `warningAsError` and a 1500-line `longFile` limit, so those
cannot be on `main`; if you find one, CI has a gap — record it `needs-human`.)

## 2. Evidence recipes

Run probes with `lean_run_code` (standalone; include the imports, e.g. the module under
audit) or `lean_multi_attempt` at a position in the file. Paste the probe verbatim into
`evidence.lean` and set `evidence.result`.

| Finding | Probe | `result` |
|---|---|---|
| contradictory hypotheses | `example <binders> : False := by …` | `compiles` |
| conclusion needs no hypotheses | the conclusion alone, or `lean_minimal_hypotheses`'s output | `compiles` |
| tautology | `example <binders> : <hyp> → <conclusion> := id` (or `fun h => h.1`) | `compiles` |
| overstated name or docstring | `example : <what they claim> := by exact decl …`; add a counterexample to the claim if there is one | `fails-as-expected` |
| wrong definition | a value or witness test showing the gap, with the standard value cited | `compiles` |
| too weak or too strong | `example : IsFoo <non-example>` / `example : ¬ IsFoo <standard example>` | `compiles` |
| junk-value vacuity | the statement at the junk input, proved by the junk | `compiles` |
| Mathlib duplicate | `example <binders> : <statement> := <MathlibDecl> …` (or a one-line `simpa using`) | `compiles` |
| Tau Ceti duplicate | `example : <statement> := <other decl> …`, or `example : defA = defB := rfl` / by `ext` | `compiles` |
| redundant hypothesis, strong typeclass | the statement without it, or under the weaker class, with a proof | `compiles` |
| long or slow proof, naming, api, docs | the measurement: line count, profiler time, the name, the grep | `measured` |

`scripts/redteam.py finding` refuses a CRITICAL or MAJOR finding without this. Correctness,
reuse and generality findings need a probe; the others may cite a measurement.

## 3. Astra

Every call: `mcp__chatgpt-math__ask_chatgpt_math` with `model: "gpt-6-astra"` and
`reasoning_effort: "max"`. Where that MCP server is not installed (a machine without Node),
write the question to a file and run `python3 "$RT" astra <file>`: the same model and effort
through the Codex CLI, reading the question on stdin (`REDTEAM_CODEX_HOMES` lists logins
to fall through when one is at its usage limit). Astra cannot see files, so each
question carries everything it needs. The MCP server passes the question as a single
command-line argument, so keep an MCP call under ~100 KB, splitting a larger file at
declaration boundaries with the header and imports repeated in each part; the CLI route has
no such limit.

### A1 — blind pass (one per file, in a background Agent)

```text
You are red-teaming a Lean 4 file from Tau Ceti, a research-mathematics library built on
Mathlib (pinned at <mathlib rev>). Find every problem; nothing is too small, but rank them.
Be adversarial: treat each definition and statement as wrong until you have tried and failed
to break it. In particular:
- does each definition match the standard mathematical one (conventions, signs, indexing,
  degenerate cases, Lean junk values such as x/0 = 0, truncated ℕ subtraction, Nat.card of
  an infinite type = 0)?
- are any theorem's hypotheses contradictory, or its conclusion trivial, tautological, or
  different from what its name and docstring say?
- are hypotheses or typeclass assumptions unused or stronger than needed?
- does Mathlib already have it (name the declaration), or does the file rebuild something?
- names, namespaces, proof length and robustness, documentation, leftovers.
For each problem give: the declaration; the category (correctness | generality | reuse |
proof | naming | api | docs | hygiene); what is wrong; and a concrete test that would show
it (a Lean `example`, a counterexample, or the existing declaration).

File <path> (part <k> of <n>):
```lean
<contents>
```
```

### A2 — refute these claims (one per file, all CRITICAL and MAJOR findings batched)

```text
A red team claims the following problems in a Lean 4 file from Tau Ceti (Mathlib pinned at
<mathlib rev>). For each claim, first try hard to show it wrong: consider conventions under
which the code would be right, whether the "problem" is intended, and whether the evidence
proves what it says. Then answer on its own line:
CLAIM <n>: VERDICT: agrees | disagrees | unsure
followed by your reasons and, if you agree, the fix you would make and what else it affects.

The declarations involved, with the definitions they use:
```lean
<source>
```

CLAIM 1 (<severity>, <category>): <claim>
Evidence (compiled with Lean):
```lean
<probe>
```
Lean's response: <result>
…
```

Record `astra.verdict` and a one-paragraph `astra.summary` per finding. **Lean decides
facts; Astra is a second opinion on whether the fact is the problem claimed.** When Astra
disagrees and the finding stands, `resolution` says why. When Astra's reasoning shows the
finding wrong, record it `refuted`: a loss, but an honest one.

## 4. The fix playbook

| Finding | Fix |
|---|---|
| wrong definition | Correct it to the standard definition, citing the source in the PR; repair every downstream proof (a breaking proof leaned on the error). |
| vacuous or tautological theorem | If the intended statement is clear, restate and prove it — `/develop` and `/beastmode` if the proof needs new work. If it is unclear and unused, delete it. Re-check every consumer. |
| overstated name or docstring | If the statement is what is wanted, fix the name or docstring; otherwise strengthen the statement to match and prove it. |
| Mathlib duplicate | Delete it and point every use at the Mathlib declaration. Keep a specialisation only if it has consumers and saves them real work, as a one-line derivation. |
| Tau Ceti duplicate | Keep the canonical copy — the more general; if equally general, the one with more consumers; if tied, the older. Delete the other, repoint its uses, and move any API it had that the canonical copy lacks. |
| redundant hypothesis, strong typeclass | Remove or weaken it, and update every call site. |
| long proof | Search for a replacement first; otherwise `Skill(mathlib-quality:decompose-proof)`. |
| slow proof | `Skill(mathlib-quality:buzz)`. |
| naming, namespace | Rename and update every use. No alias. |
| compatibility surface | Delete it; repoint uses. |
| missing characteristic API | Add a lemma only where it replaces unfolding in an existing proof, and say so; otherwise it is new material — record it `needs-human`. |
| misplaced material | Move it to its canonical home and update imports. |
| docs, hygiene | Fix them in the file's `chore` PR, alongside `/cleanup`. |

## 5. The pattern sweep

A confirmed CRITICAL or MAJOR finding is rarely alone: the agent that wrote it wrote others.
Turn it into a search — a `git grep -E` for its shape (the hypothesis pair, the doubled
namespace, the junk-prone expression, the duplicated construction) or a probe to run on
every hit — and record each hit as a `suspected` finding in its own file, with the same
`pattern`. `redteam.py next` hunts those files first, and a suspected finding is confirmed
or refuted there like any other.

## 6. The ledger's records

Written only through `scripts/redteam.py`, which validates them. A finding's first record
(leave out `id` to have one assigned; later records carry just the id and the fields that
change):

```json
{"id": "RT-20260928-a1b2c3",
 "file": "TauCeti/GroupTheory/Augmentation.lean",
 "decl": "TauCeti.GroupTheory.Augmentation.augmentation_cohomology_trivial_of_card_eq_one",
 "category": "correctness", "severity": "CRITICAL", "status": "confirmed",
 "claim": "the hypotheses [Nontrivial G] and Nat.card G = 1 are contradictory, so the theorem says nothing",
 "pattern": "contradictory-hypotheses",
 "rubric": "correctness",
 "evidence": {"lean": "example {G : Type*} [Group G] [Finite G] [Nontrivial G] (h : Nat.card G = 1) : False := by\n  have := Finite.one_lt_card (α := G); omega",
              "result": "compiles"},
 "astra": {"verdict": "agrees", "summary": "A nontrivial finite type has at least two elements; …"},
 "resolution": ""}
```

- `status`: `suspected` → `confirmed` or `refuted` → `pr-open` (with `pr`) → `landed`, or
  `superseded` (fixed on `main` by another change first), `rejected` (its PR closed for
  being wrong), `needs-human` (beyond a PR).
- `pattern`: a kebab-case name for the *kind* of error, reused across findings — this is
  what the report counts. Reuse an existing slug when one fits (`python3 "$RT" tally` lists
  them).
- `rubric`: the TauCetiReview rubric that should have caught it (`correctness`, `reuse`,
  `scope`, `attribution`, `api-design`, `generality`, `placement`, `naming`,
  `documentation`, `proof-quality`), or `none` for what no rubric covers.

An audit: `{"file": "<path>", "matrix": {"(file)": {…}, "<declaration>": {"correctness":
"ok", "reuse": "F:RT-…", …}, …}}`.

- Every declaration, and a `(file)` row for the file itself (header, module docstring,
  imports, anything between declarations), each with all eight categories.
- A cell is `"ok"`, `"F:<id>"`, or `"F:<id>,<id>"` when one check found several problems.
- **One defect, one finding.** When another category's check finds a defect already
  recorded, its cell cites that finding rather than recording it twice: wins count findings,
  so a duplicate record is an inflated score.
- Anonymous instances are keyed `instance@L<line>`. The script finds the declarations itself
  and refuses the audit if any is missing.
