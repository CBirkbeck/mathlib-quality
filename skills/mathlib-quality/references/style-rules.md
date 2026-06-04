# Mathlib Style Rules

This is the authoritative style guide for mathlib contributions, based on the official
[leanprover-community style guide](https://leanprover-community.github.io/contribute/style.html).

## File Structure

### Header Format
Every mathlib file requires this exact structure:

```lean
/-
Copyright (c) 2024 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name, Another Author
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic

/-!
# Module Title

Brief description of what this file contains.

## Main definitions

* `Foo`: Description of Foo
* `Bar`: Description of Bar

## Main results

* `foo_bar`: A key theorem about foo and bar

## Implementation notes

Any important implementation decisions.

## References

* [Author, *Title*][citation_key]
-/

namespace MyNamespace
```

**Important header rules:**
- Use "Authors:" (plural) even for a single author
- Authors are comma-separated, no "and"
- No period at end of author line
- Imports placed immediately after copyright with no blank line
- One import per line

### File Length
- **Hard limit**: 1000 lines (nothing should exceed this)
- **Preferred**: 500-800 lines
- **Action**: Split large files by topic; use `#find_home` to verify location

### File Organization (Splitting Large Files)

Large files should be split thematically. Standard organization:

1. **Definitions file** (`Foo/Defs.lean`)
   - Core definitions, structures, classes
   - No proofs beyond `rfl`-level

2. **Basic lemmas** (`Foo/Basic.lean`)
   - Simple properties of definitions
   - API lemmas (membership, coercion, etc.)

3. **Specialized topics** (`Foo/TopicName.lean`)
   - Group related theorems by mathematical theme
   - Each file should be self-contained with clear purpose

**Example split for a 6000-line file:**
```
MyModule/
├── Defs.lean           -- Core definitions (~200 lines)
├── Basic.lean          -- Basic API lemmas (~400 lines)
├── Continuity.lean     -- Continuity results (~500 lines)
├── Integration.lean    -- Integration results (~500 lines)
└── MainTheorem.lean    -- The main result, importing above (~300 lines)
```

**Import structure:**
- Lower files import definitions, not vice versa
- Avoid circular imports
- Each file should compile independently

### Line Length
- **Maximum**: 100 characters
- **Breaking points**: After operators, at commas
- **Continuation**: Align with opening delimiter or indent 2-4 spaces
- **Place operators before line breaks**, not at the start of next lines

## Variable Conventions

Standard variable names used throughout mathlib:

| Variable | Purpose |
|----------|---------|
| `u`, `v`, `w` | Universes |
| `α`, `β`, `γ` | Generic types |
| `a`, `b`, `c` | Propositions |
| `x`, `y`, `z` | Elements of generic types |
| `h`, `h₁`, `h₂` | Assumptions/hypotheses |
| `p`, `q`, `r` | Predicates and relations |
| `s`, `t` | Lists and sets |
| `m`, `n`, `k` | Natural numbers |
| `i`, `j` | Integers |
| `G` | Group |
| `R` | Ring |
| `K`, `𝕜` | Field |
| `E` | Vector space |

## Formatting Rules

### Indentation
- **All declarations** (`def`, `lemma`, `theorem`, `class`, `structure`) start flush-left
- **No indentation** for namespace/section contents
- **Tactic blocks**: 2 spaces from theorem statement
- **Multi-line theorem statements**: subsequent lines indented 4 spaces
- **Proof**: still indented only 2 spaces (not 6)

```lean
-- Good: 2-space indentation for proof
theorem foo_bar_with_very_long_name
    (h₁ : a_very_long_hypothesis_type)
    (h₂ : another_very_long_hypothesis) :
    conclusion := by
  apply something  -- 2 spaces, not 6
  exact h₁

-- Bad: proof indented too much
theorem foo :
    P := by
      apply h  -- Wrong: 6 spaces
```

### Whitespace

**Around operators and colons:**
```lean
-- Good
a + b * c
def foo (x : α) (y : β) : γ := ...
f x y
(a, b)

-- Bad
a+b*c
def foo (x:α)(y:β):γ := ...
f  x  y
( a , b )
```

**Space after `←` in rewrites:**
```lean
-- Good
rw [← add_comm a b]
simp [← h]

-- Bad
rw [←add_comm a b]
```

**No trailing whitespace** on any line.

### Line Breaking

**Declarations (multi-line):**
```lean
-- Good: break at parameters, 4-space continuation
theorem foo_bar_with_very_long_name
    (h₁ : a_very_long_hypothesis_type)
    (h₂ : another_very_long_hypothesis) :
    conclusion := by
  ...

-- Single line if it fits
theorem foo_bar (h : P) : Q := by ...
```

**Place `by` at end of line, never alone:**
```lean
-- Good
theorem foo : P := by
  exact h

-- Bad
theorem foo : P :=
  by exact h

-- Bad
theorem foo : P
    := by exact h
```

### Empty Lines

- **Discouraged inside declarations** (enforced by linter)
- Blank lines separate theorems/definitions
- May omit blank lines for grouped short definitions
- **Exactly one blank line between consecutive declarations** (lemma/theorem/def). Two or more is rejected; zero is rejected.

### No Subsection Dividers Inside Files

Do not add `/-! ### Foo -/` (or `/-! ## Foo -/`) subsection headers inside a Lean file. The only module-level docstring belongs at the top of the file. Subsection dividers below the header are rejected by review and `/cleanup` strips them.

```lean
-- BAD: subsection divider inside a file
/-! ### Surjectivity of `evalE₄E₆` -/

theorem evalE₄E₆_surjective : ... := by ...

/-! ### Injectivity of `evalE₄E₆` -/

-- GOOD: just declarations, no dividers
theorem evalE₄E₆_surjective : ... := by ...

theorem evalE₄E₆_injective : ... := by ...
```

If a chunk of declarations needs a header to be discoverable, the file is probably too large — split it instead.

### Comments in Proofs

**Mathlib proofs should have NO inline comments.** Proofs should be self-documenting through
clear variable names and logical structure. Use docstrings for documentation.

**Narrative `--` comments inside proofs (`-- now apply the IH`, `-- use linearity`, `-- Step 1: ...`) are rejected.** `/cleanup` strips them automatically. The only `--` comments that survive a review pass are those documenting a non-obvious WHY: a hidden constraint, a workaround for a specific bug, or behaviour that would surprise a reader.

**What to avoid:**
```lean
-- Bad: ANY inline comments in proofs
theorem foo : P := by
  -- First we show that A holds
  have hA : A := by
    -- This is because of lemma bar
    exact bar
  -- Now we can use hA to get B
  have hB : B := by
    -- Apply transitivity
    exact trans hA hC
  -- Finally conclude
  exact final_step hB

-- Also bad: "Step N" markers
theorem bar : Q := by
  -- Step 1: Setup
  have h1 := setup_lemma
  -- Step 2: Main argument
  have h2 := main_lemma h1
  -- Step 3: Conclude
  exact h2
```

**What to use instead:**
```lean
-- Good: clean proof with SHORT docstring (no strategy), NO inline comments
/-- The sum of two even numbers is even. -/
theorem foo : P := by
  have hA : A := bar
  have hB : B := trans hA hC
  exact final_step hB

-- Good: no step markers, no explanatory comments
theorem bar : Q := by
  have h1 := setup_lemma
  have h2 := main_lemma h1
  exact h2
```

### Docstring Guidelines

**Docstrings describe the STATEMENT, not the proof.** This is the binding rule
that subsumes the brevity preference: a docstring tells a user browsing the
API *what is claimed*, not *how the proof works*. Drop phrases like:

- "The proof iterates …"
- "By induction on …"
- "Uses Lemma X / Theorem Y / Z"
- "We first establish … then apply …"
- "The proof strategy is …"

Those belong in the PR description or in a comment above the proof body
(rarely), never in the docstring. Reviewers strip them; `/cleanup` strips
them automatically.

```lean
-- Bad: contains proof strategy
/-- **Sturm bound for level-1 modular forms.** If a modular form `f` has
zero coefficient on `q^i` for every `i ≤ k / 12`, then `f` is identically
zero. The proof iterates `CuspForm.discriminantEquiv` (division by `Δ`)
until the weight goes negative, where everything is zero. -/
theorem sturm_bound_levelOne ...

-- Good: statement only
/-- **Sturm bound for level-1 modular forms.** If a modular form `f` has
zero coefficient on `q^i` for every `i ≤ k / 12`, then `f` is identically
zero. -/
theorem sturm_bound_levelOne ...
```

Also: **docstrings should be SHORT** — one sentence stating what is claimed.

```lean
-- Bad: too verbose
/-- This theorem shows that f is continuous. The proof proceeds by first
establishing boundedness on compact sets using the Heine-Borel theorem,
then applying the sequential characterization of continuity. We use the
fact that f is locally Lipschitz to conclude. -/
theorem f_continuous : Continuous f := by ...

-- Good: brief, statement only
/-- `f` is continuous. -/
theorem f_continuous : Continuous f := by ...
```

**Module docstrings** (the top-of-file `/-! … -/` block) MAY describe
overall proof strategy for the file — only per-lemma docstrings are
subject to the statement-not-proof rule.

**Only important public theorems need docstrings:**
```lean
-- Good: main theorem has docstring
/-- The valence formula for modular forms of weight k. -/
theorem valence_formula : ... := by ...

-- Good: helper has no docstring, is private, uses _aux suffix
private theorem valence_formula_aux : ... := by ...
```

**Private/auxiliary lemmas must not have docstrings.** Docstrings are reserved for the public-API surface; a docstring on a `private` lemma is review-rejected and `/cleanup` strips it.

```lean
-- BAD: docstring on a private helper
/-- For even `k ≥ 4`, there exist `a, b ∈ ℕ` with `4a + 6b = k`. -/
private lemma exists_monomial_weight ... := ...

-- GOOD: no docstring on private/aux
private lemma exists_monomial_weight ... := ...
```

If the helper deserves to be documented, it probably deserves to be public (drop `private`); otherwise drop the docstring.

**Rarely acceptable comments (use sparingly):**
- `-- Porting note:` for Lean 3 → 4 migration issues (required for porting PRs)
- Reference to a paper for a highly unusual technique (rare)

**Unacceptable comments (remove all of these):**
- Play-by-play of each tactic
- "Step N" markers
- Restating what the code obviously does
- Explaining what a tactic does
- Summarizing proof strategy (put in docstring if needed)
- Lengthy mathematical exposition (put in module doc)
- TODO comments (use GitHub issues instead)
- Parameter documentation inline with code

### Calc Blocks

```lean
-- Standard format: calc on its own line
calc
  a = b := by ...
  _ = c := by ...
  _ ≤ d := by ...

-- Relations aligned, underscores left-justified
-- Justifications need not have aligned := symbols
```

## Inequality Orientation

**Mathlib convention: every inequality in Lean code is stated with the smaller side on
the left.** Use `≤`, never `≥`. Use `<`, never `>`. Lemma names follow the same
orientation: `a_le_b`, not `b_ge_a`.

This applies to statements, hypotheses, and any inequality in Lean code (the type, the
hypotheses, any `have` with an explicit type). It does NOT apply to docstrings or `--`
comments where the reversed orientation reads more naturally — the rule is about Lean
code.

```lean
-- BAD: ≥ in the statement; name uses _ge_
theorem primeIdealZetaSum_ge_log_minus_bounded (s : ℝ) :
    primeIdealZetaSum K univ s ≥ Real.log (1/(s-1)) - C := ...

-- GOOD: ≤ in the statement; name uses _le_; sides swapped to match
theorem log_minus_bounded_le_primeIdealZetaSum (s : ℝ) :
    Real.log (1/(s-1)) - C ≤ primeIdealZetaSum K univ s := ...
```

Same for strict inequalities:

```lean
-- BAD
lemma f_gt_zero (h : x > 0) : f x > 0 := ...

-- GOOD
lemma zero_lt_f (h : 0 < x) : 0 < f x := ...
```

This is enforced by `/cleanup` audit item 19 + `inequality_orientation_gate` (a hard
gate). Workers emit a per-occurrence inequality scan table for every declaration; any
`≥` or `>` in Lean code is rewritten with sides swapped, and any `_ge_` / `_gt_` name
queues a rename for Phase 5b.

The rewrite is purely syntactic — `a ≥ b` and `b ≤ a` are notational equivalents — so
the gate is about *uniformity across mathlib* so downstream consumers can rely on the
convention (e.g. `simp` lemmas that match on `_ ≤ _` won't fire on `_ ≥ _`).

Source: chebotarev-density learning, 2026-06-02
(`data/community_learnings/archived/2026-06-02_chebotarev-density.jsonl`).

## Mathlib-First Principle

### Always Check Mathlib Before Defining

Before creating any definition, **always check if mathlib already has an equivalent**. Use `exact?`, `apply?`, Loogle, or Moogle to search.

```lean
-- BAD: redefining something mathlib already has
def fundamentalDomain : Set UpperHalfPlane := {z | |z.re| ≤ 1/2 ∧ ‖(z : ℂ)‖ ≥ 1}

-- GOOD: use the mathlib version
-- ModularGroup.fd already exists — use it directly
```

**Key rules:**
- Reuse mathlib definitions everywhere possible
- Build new API/lemmas FOR mathlib's existing definitions rather than creating custom ones
- If replacing a custom def with a mathlib one, update ALL lemmas to use the mathlib def

### Avoid Custom Defs That Mirror Trivial Mathlib Constructions

**Every `def` must be strongly justified and come with good API.** Small wrapper defs whose body is a one-line mathlib expression are junk — inline the expression at use sites.

```lean
-- BAD: trivial wrappers around existing mathlib constructions
def mk2 (a b : ℕ+) : Fin 2 → ℕ+ := ![a, b]
def sigma1 (m : ℕ+) : ℕ := ArithmeticFunction.sigma 1 m

-- GOOD: use mathlib directly at every call site
-- ![a, b]                    -- not mk2 a b
-- ArithmeticFunction.sigma 1 -- not sigma1
```

**Test:** if your `def` is used outside one local proof, has `_apply`/`_def` lemmas, or names a non-trivial mathematical object, keep it. Otherwise inline.

### Junk Defs Without API

A `def foo : T := value` with **no surrounding API** (no `_apply`/`_def` simp lemmas, no users outside one local proof) is junk. Inline `value` at every use site, with a type ascription `(value : T)` if the elaborator needs it.

```lean
-- BAD: bare def, no API, used in one place
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]
-- ... used 13 times as `E₄E₆Weight` with no _apply lemmas

-- GOOD: inline at every site
(![4, 6] : Fin 2 → ℕ)
```

### No Bridge Theorems

When a custom definition duplicates a mathlib definition, do NOT create bridge theorems between them. Instead, migrate all code to use the mathlib definition directly.

```lean
-- BAD: bridge theorem
theorem fd_eq_fd' : (𝒟 : Set ℍ) = 𝒟' := by ...
theorem S0_mem_fd_clean : ... := by rw [fd_eq_fd']; ...

-- GOOD: update ALL code to use the mathlib definition directly
-- Delete custom fundamentalDomain and rewrite every lemma that used it
```

### Inline Trivial Single-Use Existential Lemmas

A private `∃`-existence lemma whose body is `⟨witness, rfl, rfl, ...⟩` and is used only once is junk — write the witness inline at the call site.

```lean
-- BAD: trivial single-use existence lemma
private lemma finsupp_of_fin2 (a b : ℕ) : ∃ d : Fin 2 →₀ ℕ, d 0 = a ∧ d 1 = b :=
  ⟨Finsupp.equivFunOnFinite.invFun ![a, b], rfl, rfl⟩
-- used once

-- GOOD: inline the witness at the call site
obtain ⟨d, hd0, hd1⟩ : ∃ d : Fin 2 →₀ ℕ, d 0 = a ∧ d 1 = b :=
  ⟨Finsupp.equivFunOnFinite.invFun ![a, b], rfl, rfl⟩
```

### Prefer Notation Over Definitions for Simple Compositions

For simple compositions, use notation instead of a `def`. This avoids needing to unfold/simp the definition everywhere.

```lean
-- BAD: unnecessary definition that needs unfolding
def modularFormComp (f : ModularForm (Gamma 1) k) : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex

-- GOOD: transparent notation
local notation "f_ℂ" => (f : ModularForm (Gamma 1) k) ∘ UpperHalfPlane.ofComplex
```

## No Commented-Out Code

**Never put theorems or definitions as comments in a file.** A file with only commented-out theorem statements is completely useless.

```lean
-- BAD: commented-out theorem
-- `valenceFormula_textbook_orbit_finsum :
--     (orderAtCusp' f : ℂ) + ...`

-- GOOD: actual theorem that compiles
theorem valenceFormula_textbook_orbit_finsum ... := ...
```

When moving a theorem into its own file, put the actual theorem statement uncommented and bring in whatever it needs to compile.

## Unused Variables

**Remove unused variables entirely from signatures and call sites. Do NOT add a `_` prefix.**

```lean
-- BAD: underscore prefix
(_hp0_ne_i : p0 ≠ ellipticPointI)

-- GOOD: remove entirely from signature and all call sites
```

## Syntax Preferences

### Use `fun` over `λ`
```lean
-- Good
fun x => x + 1
fun x y => x * y

-- Bad (λ is deprecated)
λ x => x + 1
```

### Use `↦` (mapsto) for lambdas — always

In **lambda** abstractions, always use the Unicode `↦`, never `=>`:

```lean
-- Good
fun x ↦ x + 1

-- BAD — `=>` for a lambda
fun x => x + 1
```

Pattern-match arrows are NOT affected — `| zero => 0`, `| succ n ih => …`,
`match … with | foo => …`, and `cases h with | inl ha => …` all keep `=>`.
The rule applies only to **lambda** abstractions (`fun … ↦ …`).

### Use `<|` over `$`
```lean
-- Good
f <| g x
apply foo <| bar baz

-- Bad ($ is not allowed)
f $ g x
```

### Centered dot for simple functions
```lean
-- Good for simple functions
(· ^ 2)
List.map (· + 1) xs

-- Use fun for complex functions
fun x => x.property.something
```

## Declaration Formatting

### Theorem/Lemma statements
```lean
-- Short: single line
def square (x : ℕ) : ℕ := x * x
theorem foo : a = a := rfl

-- Medium: break after colon
theorem foo_bar_with_long_name (h₁ : P) (h₂ : Q) :
    conclusion := by
  ...

-- Long: break at parameters
theorem foo_bar_with_very_long_name
    (h₁ : a_very_long_hypothesis_type)
    (h₂ : another_very_long_hypothesis) :
    conclusion := by
  ...
```

### Instance declarations with `where`
```lean
-- Good: use where syntax to avoid braces
instance instAddCommMonoidFoo : AddCommMonoid Foo where
  add := ...
  zero := ...
  add_comm := ...

-- Can reference existing instances with __
instance : Foo α where
  bar := __.bar  -- uses existing instance field
```

### Structure definitions
```lean
-- Every field must have a docstring
structure Foo (α : Type*) where
  /-- Documentation for field1 -/
  field1 : α
  /-- Documentation for field2 -/
  field2 : α → α
```

## Tactic Mode

### One tactic per line

**No `tac1; tac2` chains on one line.** Each tactic goes on its own line. The one exception is sequential `rw` calls, which should be **merged** into a single call rather than chained:

```lean
-- BAD: distinct tactics chained with `;`
theorem foo : P := by
  subst hk; rfl
  rw [a]; rw [b]
  rw [...]; ring

-- GOOD: one tactic per line; merge sequential rw
theorem foo : P := by
  subst hk
  rfl
  rw [a, b]    -- merged
  rw [...]
  ring
```

The terminal-only one-liners `:= by exact h`, `:= by simp`, `:= by rfl` are fine on a single line.

### Focused subgoals with `·`
```lean
-- Good: use focusing dots
theorem foo : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- Use <;> to execute on all goals
theorem foo : P ∧ Q := by
  constructor <;> assumption
```

### Terminal simp should NOT be squeezed
```lean
-- Good: terminal simp is fine unsqueezed (more maintainable)
theorem foo : a + 0 = a := by simp

-- Non-terminal simp should use simp only
theorem bar : P := by
  simp only [add_zero]  -- explicit lemmas
  exact h
```

### Have statements
```lean
-- Short: single line
have h : P := by exact hp

-- Long justification: next line, indented 2 spaces
have h : VeryLongType :=
  by exact some_long_proof

-- by always on same line as have
have h : P := by
  apply something
  exact hp
```

## Helper Lemmas and Visibility

### Private vs Public Declarations

**Only declarations intended for use in other files should be public.**

```lean
-- Good: main theorem is public
theorem main_result : P := by
  exact main_result_aux₁ ▸ main_result_aux₂

-- Good: helpers are private with _aux suffix
private theorem main_result_aux₁ : Q := by ...
private theorem main_result_aux₂ : R := by ...
```

### Naming Helper Lemmas

**Use `_aux` suffix for helper lemmas:**
```lean
-- Good naming
private theorem foo_aux : ... := ...
private lemma bar_step_aux : ... := ...
private def helper_aux : ... := ...

-- Bad naming
private theorem foo_helper : ... := ...  -- use _aux instead
theorem foo_aux : ... := ...  -- should be private
```

### When to Use Private

- Lemmas only used within the current file → `private`
- Implementation details → `private`
- Step lemmas in a multi-step proof → `private` with `_aux`
- API lemmas for mathlib → public (no `private`)
- Main theorems → public (no `private`)

## Hypotheses Placement

- **Prefer arguments left of colon** over universal quantifiers/implications
- Pattern-matching is valid exception

```lean
-- Good: hypotheses as arguments
theorem foo (n : ℕ) (h : n > 0) : P n := ...

-- Avoid: hypotheses after colon
theorem foo : ∀ n : ℕ, n > 0 → P n := ...
```

## Import Rules

### Order
1. Mathlib imports (alphabetical)
2. Project imports (alphabetical)
3. Blank line between groups

```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic

import MyProject.Foo
import MyProject.Bar
```

### Minimality
- Import only what you need
- Use `#check` to verify imports are necessary
- Remove unused imports before PR
- Don't rely on transitive imports

## Normal Forms

- Settle on standard form for equivalent statements
- Use simp lemmas to convert other forms to normal form
- Exception: `hne : x ≠ ⊥` in assumptions, `hlt : ⊥ < x` in conclusions

## API Design & Transparency

Three transparency levels:
- **`reducible`**: Created by `abbrev`, unfolds everywhere
- **`semireducible`**: Default for `def`, standard behavior
- **`irreducible`**: Blocks unfolding (requires performance justification)

```lean
-- Default: keep semireducible unless justified
def myDef : α → β := ...

-- Use abbrev for true abbreviations
abbrev MyType := SomeOtherType

-- Use irreducible_def only with performance justification
irreducible_def expensiveDef : α → β := ...
```

**Missing API indicator**: If you need `erw` or `rfl` after `simp`/`rw`, it suggests missing simp lemmas.

## Performance & Profiling

- Authors should benchmark contributions
- Particularly important for: instances, simp lemmas, imports, new definitions
- Comment `!bench` on PR to access Lean FRO benchmarking infrastructure
- Avoid `set_option maxHeartbeats` increases; optimize the proof instead

## Deprecation

```lean
-- Use @[deprecated] attribute with message
@[deprecated (since := "2024-01-15")]
theorem old_name : P := new_name

-- For renames, use deprecated alias
@[deprecated (since := "2024-01-15")]
alias old_name := new_name
```

- Deprecated declarations deletable after 6 months
- Named instances don't require deprecations
- For `to_additive`: ensure deprecation tagged on both versions

### Renaming declarations across namespaces — `protected alias`

When renaming a declaration that *moves between namespaces* (e.g.
`ModularFormClass.qExpansion_smul` → `ModularForm.qExpansion_smul`), don't simply delete
the old qualified name. Add a `protected alias` at the OLD namespace so downstream code
that imports the qualified name still compiles:

```lean
-- After renaming ModularFormClass.qExpansion_smul → ModularForm.qExpansion_smul,
-- add this at the OLD namespace:
namespace ModularFormClass

@[deprecated (since := "yyyy-mm-dd")]
protected alias qExpansion_smul := ModularForm.qExpansion_smul

-- ... etc for every renamed declaration in this namespace

end ModularFormClass
```

`protected` keeps the alias accessible only via the qualified `ModularFormClass.qExpansion_smul`
form (not via dot-notation on a subject), which matches typical downstream usage. Plain
`alias` (non-protected) opens the name to dot-notation too, which is rarely what you want
for a deprecation alias.

This applies to any PR that moves or renames declarations downstream code might import.
[loefflerd review of mathlib4 #38806]

### Moving a file: TWO PRs, no shim in the move PR

When moving a file in mathlib4, **don't leave a deprecation shim at the old path in the
same PR that does the move**. The mathlib convention is a two-PR workflow:

**PR 1 — the move.** In the file-move PR, delete the old file outright (`git rm`). Run
`lake exe mk_all` to drop the now-orphaned import from `Mathlib.lean`. The new file at
the new path is the only copy.

```lean
-- ❌ Wrong: leave a shim at the old path in the move PR
-- old/path/MyFile.lean (kept):
--   module -- shake: keep-all
--   public import new.path.MyFile
--   deprecated_module ...
```

**PR 2 — the deprecation shim, separate and immediate.** In a follow-up PR (sent right
after the move), add the deprecation shim back at the old path:

```lean
-- old/path/MyFile.lean (added in follow-up PR):
deprecated_module "Use new.path.MyFile instead." (since := "yyyy-mm-dd")
```

**Why two PRs?** Git's rename-detection only recognises a file move when the old file
*vanishes entirely* and an identically-content new file appears. A one-line stub at the
old path defeats the heuristic — Git treats the new file as freshly created, and
`git blame` / `git log --follow` lose history. The two-PR split gets both: clean rename
detection in PR 1, downstream-friendly deprecation in PR 2. Tedious but worth it for the
permanent history.

[loefflerd review of mathlib4 #38806]

## Error Messages

```lean
-- Inline names: surrounded by backticks
throwError m!"expected `{expectedType}` but got `{actualType}`"

-- Multiline: on own line and indented via indentD
throwError m!"error occurred:{indentD m!"{details}"}"
```

## Avoid `nonrec`

- Don't use when recursive call conflicts with namespace declaration
- Instead, add namespace to conflicting declaration
- Root namespace conflicts: `nonrec` or `_root_.[...]` both acceptable

## Structure Construction & `@[simps]`

### Use `@[simps -fullyApplied]` for coe-level simp lemmas

When defining a structure-building function, prefer `@[simps -fullyApplied]` over manually writing `_apply` simp lemmas. It auto-generates `⇑(foo f) = ⇑f` (coe-level) rather than `(foo f) z = f z` (fully-applied), which is usually what you want for rewriting.

```lean
-- ❌ Manual _apply lemma
def ModularFormClass.modularForm (f : F) : ModularForm Γ k where ...

@[simp]
lemma ModularFormClass.modularForm_apply (f : F) (z : ℍ) :
    ModularFormClass.modularForm f z = f z := rfl

-- ✓ @[simps -fullyApplied] auto-generates ⇑(modularForm f) = ⇑f
@[simps -fullyApplied]
def ModularFormClass.modularForm (f : F) : ModularForm Γ k where ...
```

### Use `{ f with extra := ... }` for structure extension

When building a subtype/extension from a parent, don't manually re-provide inherited fields:

```lean
-- ❌ Manual field copying
def toCuspForm (f : ModularForm 𝒮ℒ k) (h : ...) : CuspForm 𝒮ℒ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h

-- ✓ `{ f with ... }` inherits parent fields
def toCuspForm (f : ModularForm 𝒮ℒ k) (h : ...) : CuspForm 𝒮ℒ k :=
  { f with zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h }
```

### Add `Iff.rfl` simp lemmas for wrapped defs

When a def wraps a proposition like `f ∈ submodule`, the def isn't reducible, so `simp` can't unfold it. Add an explicit `Iff.rfl` simp lemma:

```lean
def IsCuspForm (f : ModularForm Γ k) : Prop :=
  f ∈ cuspFormSubmodule Γ k

@[simp]
lemma mem_cuspFormSubmodule_iff {f : ModularForm Γ k} :
    f ∈ cuspFormSubmodule Γ k ↔ IsCuspForm f := Iff.rfl
```

### Don't build type-API on submodule terms

When you have `cuspFormSubmodule : Submodule ℂ (ModularForm Γ k)` (a term) and a dedicated type `CuspForm Γ k` with an equiv between them, don't add `FunLike`/`CuspFormClass` instances to the submodule. Use the equiv instead. The term-coerced-as-type pattern is awkward when you already have a dedicated type.

## Unify Related API via Defaults

When two functions (`copy` and `ofSubgroupEq`) share most of their implementation, unify them via default arguments:

```lean
-- ❌ Two separate functions
def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : ModularForm Γ k where ...
def ofSubgroupEq {Γ'} (h : Γ = Γ') (f : ModularForm Γ k) : ModularForm Γ' k where ...

-- ✓ Unified: `copy` with optional subgroup-equality arg
protected def ModularForm.copy {Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularForm Γ k) (f' : ℍ → ℂ)
    (h : f' = ⇑f) (hΓ : Γ = Γ' := by rfl) : ModularForm Γ' k where ...
-- Old callers: `f.copy f' h` still works (Γ' := Γ, hΓ := rfl defaults)
-- Subgroup transport: `f.copy f rfl h` (where h : Γ = Γ')
```

## Drop Unnecessary Syntax

### Drop type annotations on implicit binders when inferable

```lean
-- ❌
IsCuspForm f ↔ ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt f k

-- ✓ Type of c inferable from `IsCusp c Γ`
IsCuspForm f ↔ ∀ {c}, IsCusp c Γ → c.IsZeroAt f k
```

### Use `change` (not `show`) when the tactic actually rewrites the goal

The `linter.style.show` linter enforces this. `show` is for *annotating* the goal you're about to prove (no change in what's behind the colon); `change` is for *rewriting* the goal up to definitional equality.

```lean
-- ❌ `show` used to rewrite the goal — flagged by linter.style.show
  show g z / d z * d z = g z
  rw [div_mul_cancel₀ _ ...]

-- ✓ `change` is the correct tactic when the goal is actually being rewritten
  change g z / d z * d z = g z
  rw [div_mul_cancel₀ _ ...]
```

Rule of thumb: if the goal text differs from what came before, use `change`; if you're only labelling the existing goal for the reader (and removing the line wouldn't change anything), drop the line entirely — the redundant `show T` adds nothing (60+ occurrences of this in PR review data).

### Remove `show X from by` — use `show X by` or drop entirely

```lean
-- ❌ `show X from by ...` — `from` is for term mode, `by` is tactic, redundant
rw [show (0 : ℂ) = cuspFunction 1 f 0 from by
  rw [cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL]; exact h.symm]

-- ✓ `show X by ...` when you need tactics
rw [show (0 : ℂ) = cuspFunction 1 f 0 by
  rw [cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL]; exact h.symm]

-- ✓ Or drop `show X from` if y already has type X
rw [f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)]
```

### Prefer `have`/`let` over `haveI`/`letI` with explicit type

**Key insight**: In Lean 4, the `I` suffix on `haveI`/`letI` stands for **"inline"**, NOT "instance" (common Lean 3-ism that's still sticky). Plain `have :` and `let :` with an explicit type annotation work for instances. Since a recent Lean 4 version, **anonymous `have`/`let`** (no name, just a type) also works — Lean picks them up via typeclass resolution.

```lean
-- ❌ `haveI`/`letI` — Lean 3 habit
haveI : ModularFormClass (ModularForm 𝒮ℒ 0) Γ(1) 0 :=
  Gamma_one_coe_eq_SL ▸ inferInstance

letI : ModularFormClass (ModularForm 𝒮ℒ (0 * card)) 𝒮ℒ 0 := by
  rw [zero_mul]; infer_instance

-- ✓ Plain `have`/`let` with explicit type
have : ModularFormClass (ModularForm 𝒮ℒ 0) Γ(1) 0 :=
  Gamma_one_coe_eq_SL ▸ inferInstance

let : ModularFormClass (ModularForm 𝒮ℒ (0 * card)) 𝒮ℒ 0 := by
  rw [zero_mul]; infer_instance
```

Only use `haveI`/`letI` when you specifically want inlining-time elaboration; not for ordinary instance introduction.

### Anonymous constructor for `mem_range` proofs

```lean
-- ❌ Verbose
f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

-- ✓ Anonymous constructor unfolds membership
f.slash_action_eq' _ ⟨γ, rfl⟩
```

## Avoid `change` — Use `simp_rw` to Unfold

If you're reaching for `change`, it's a strong hint that either:
- API is missing, or
- You can unfold definitions via `simp_rw`.

```lean
-- ❌ change + rw
change Filter.Tendsto f atImInfty (𝓝 0)
rw [show (0 : ℂ) = cuspFunction 1 f 0 by ...]

-- ✓ simp_rw to unfold and rewrite in one step
simp_rw [IsZeroAtImInfty, ZeroAtFilter, ← h,
  ← cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL]
```

## Prefer `simp` over `change` + `rw`

When you have `change X; rw [lemmas]` and `simp [lemmas]` works, prefer `simp`:

```lean
-- ❌
theorem foo : ... := by
  change (Gamma 1).map (mapGL ℝ) = (mapGL ℝ).range
  rw [Gamma_one_top, MonoidHom.range_eq_map]

-- ✓
theorem foo : ... := by
  simp [Gamma_one_top, MonoidHom.range_eq_map]
```

## `DFunLike` Helpers for Function-Like Equalities

When working with equality of `FunLike` instances, use the helpers instead of manually chaining `congr_arg`/`congr_fun`:

```lean
-- ❌ Manual chain
fun _ _ h ↦ DFunLike.ext _ _ fun z ↦ congr_fun (congr_arg DFunLike.coe h) z

-- ✓ DFunLike.congr_fun does the job
fun _ _ h ↦ DFunLike.ext _ _ fun z ↦ DFunLike.congr_fun h z

-- ✓ Better: DFunLike.ext' when types unify
fun _ _ h ↦ DFunLike.ext' (congr_arg DFunLike.coe h)

-- ✓ Subtype version
coe_injective' _ _ h := Subtype.ext (DFunLike.ext' h)
```

- `DFunLike.ext' : ⇑f = ⇑g → f = g` — one-arg extensionality
- `DFunLike.congr_fun : f = g → ∀ x, ⇑f x = ⇑g x` — pointwise from extensional

## `letI` for Instance Definitional Mismatches

When `infer_instance` fails because of propositional-but-not-definitional equalities (e.g., `0 * n = 0` isn't syntactic), use `letI` to provide the instance:

```lean
-- ModularForm.norm has weight `0 * card` — no `[ModularFormClass _ _ 0]` instance found
letI : ModularFormClass (ModularForm 𝒮ℒ (0 * Nat.card _)) 𝒮ℒ 0 := by
  rw [zero_mul]; infer_instance
obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
  (ModularForm.norm 𝒮ℒ (f - .const (f I)))
```

`letI` registers the instance in the local typeclass scope for subsequent calls.

## Maximal Generalization of Theorems

State theorems with the weakest hypotheses possible. A theorem that holds for any `Γ` with `Fact (IsCusp ∞ Γ)` should be stated that way, not specialized to `𝒮ℒ`:

```lean
-- ❌ Specialized
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero
    (f : ModularForm 𝒮ℒ k) (h : valueAtInfty f = 0) : IsZeroAtImInfty f

-- ✓ General — works for any arithmetic subgroup via Fact instance
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero {F : Type*} [FunLike F ℍ ℂ]
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] [Fact (IsCusp ∞ Γ)] [ModularFormClass F Γ k]
    (f : F) (h : valueAtInfty f = 0) : IsZeroAtImInfty f
```

`Fact` instances get automatically synthesized for common concrete subgroups.

## Eliminate Bridge Patterns with API Lemmas

When you see `have : XClass Γ' := eq ▸ ‹_›` bridges repeated in multiple proof bodies, add an API lemma that bridges once:

```lean
-- ❌ Bridge at every use site
lemma exists_one_half_le_im_and_norm_le ... :=
  ⟨..., by
    have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
    simpa only [slash_action_eqn_SL'' _ (mem_Gamma_one γ), ...] using ...⟩

-- ✓ Add API lemma that bridges once
theorem slash_action_eqn_SL [SlashInvariantFormClass F 𝒮ℒ k]
    (f : F) (γ : SL(2, ℤ)) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  slash_action_eqn'' f (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z

-- Callers use directly, no bridge
lemma exists_one_half_le_im_and_norm_le ... :=
  ⟨..., by simpa only [slash_action_eqn_SL _ γ, ...] using ...⟩
```

## Restate Over the Natural Subgroup

Once conversion lemmas exist (like `Gamma_one_coe_eq_SL : ↑Γ(1) = 𝒮ℒ`), restate theorems over the more natural subgroup (`𝒮ℒ`) rather than forcing callers to bridge at every use site. The rule of thumb: the natural subgroup for mathematical content (like modular forms on GL(2, ℝ)) is usually `𝒮ℒ`; keep `Γ(1)` only where the SL(2, ℤ)-specific API (like `slash_action_eqn_SL''` or `mem_Gamma_one`) demands it, and bridge internally.

## API Completeness for Definitions

When you add a `def`, immediately add API lemmas about it (applied form,
unapplied form, structural facts, congruence). A `def` without lemmas is
half-finished.

### The loogle-check

Before submitting, search loogle for the definition's name. If nothing
comes back beyond the `def` itself, the API is incomplete — go back and
add the basic API lemmas. Reviewer feedback consistently flags this as
"please add … lemma" on PRs that ship bare definitions.

### Applied AND unapplied versions

For every equational fact, provide **both** the applied (`X z = …`) and
unapplied (`X = fun z ↦ …`) versions. Different proof contexts want
different shapes — pointwise rewriting wants the applied form;
function-level reasoning (functorial proofs, ext-based arguments) wants
the unapplied form.

```lean
-- Provide both:
lemma foo_apply (f : F) (z : Z) : (foo f) z = … := …
lemma foo (f : F) : foo f = fun z ↦ … := …
```

### Nat/Int convenience versions when statement uses `.toNat`

If your statement uses `Int.toNat` or otherwise treats an `Int`
non-negatively, provide a `Nat` companion so users with `ℕ` don't have
to do toNat gymnastics.

```lean
theorem foo_nat {k : ℕ} (f : F (k : ℤ)) (h : … k …) : … := …

theorem foo {k : ℤ} (f : F k) (h : … k.toNat …) : … := by
  rcases lt_or_ge k 0 with hk | hk
  · …  -- trivial negative case
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  exact foo_nat f (by simpa using h)
```

The `ℕ` version can be primary (with `ℤ` as a corollary) or a convenience
wrapper — either is fine; both versions must exist.

### Don't duplicate definitions that are unwrapped bundled equivs

If `def fooEquiv : T ≃ U where toFun := …` exists, do not also ship a
bare `def foo : T → U := fun t ↦ (fooEquiv t)`. The bare `foo` is the
function-projection of `fooEquiv`; users should call `fooEquiv`
directly. If a transitional `foo` exists, deprecate it.

```lean
-- BAD: duplicated definition
def divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) := …
def discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12) where
  toFun := divDiscriminant
  …

-- GOOD: bundled is primary
def discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12) where
  toFun f := { … inline body … }
  …
@[deprecated discriminantEquiv (since := "YYYY-MM-DD")]
def divDiscriminant (f : CuspForm 𝒮ℒ k) := discriminantEquiv f
```

## Statement Style

### No redundant explicit coercions

Once one side of an equation has a known type via context, Lean
auto-coerces the other side. Strip the unnecessary explicit coercions.

```lean
-- BAD: redundant (Δ : ℍ → ℂ) cast
theorem foo : (Δ : ℍ → ℂ) * (discriminantEquiv f : ℍ → ℂ) = f := …

-- GOOD
theorem foo : Δ * (discriminantEquiv f : ℍ → ℂ) = f := …
```

### Don't `@[simp]` lemmas with bad normal forms

A `@[simp]` lemma whose RHS introduces variables not on the LHS, or
duplicates a variable, gives `simp` an unstable normal form. Don't tag
such lemmas `@[simp]` — leave them as ordinary lemmas, or instead simp
the **unapplied** function-level version which often has a clean LHS.

```lean
-- BAD: z appears once on LHS, twice on RHS → bad simp normal form
@[simp]
lemma discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (discriminantEquiv f) z = f z / Δ z := …

-- BETTER: simp the function-level form
@[simp]
lemma discriminantEquiv_eq (f : CuspForm 𝒮ℒ k) :
    discriminantEquiv f = fun z ↦ f z / Δ z := …
```

## Imports — `public` follows use-site, not need

In the new module system, `public import` makes the imported module
transitively visible to downstream users; non-public `import` keeps it
visible only within the importing file.

The rule for choosing between them is based on **where the import is
used in this file**:

- **If the import is only used in proofs** (tactic bodies, `by …` blocks,
  any code inside `:= by …` or term-mode proofs) — non-public `import`.
  In most cases this is the right default. Proof bodies are an
  implementation detail; downstream users don't need to see the imported
  module to *call* the lemmas you prove.
- **If the import is used in theorem statements, definitions, or any
  other declaration-surface position** (anything that appears in the
  signature a downstream user sees) — `public import`. The module is
  part of the surface of your file; the downstream user can't elaborate
  your statements without it.

```lean
-- Used only in proofs → non-public
import Mathlib.Data.Nat.ModEq                    -- only `Nat.ModEq.symm` in proof bodies
import Mathlib.RingTheory.PowerSeries.Order      -- only in tactic blocks

-- Used in statements/definitions → public
public import Mathlib.Topology.Basic             -- `Continuous` appears in theorem signatures
public import Mathlib.Algebra.Group.Defs         -- `Group` appears in a def
```

**Judgment call: re-exporting for convenience.** It can make sense to
keep an import `public` even when it's not strictly needed by the
declarations, if you want the imported material visible downstream so
dependents don't have to re-import it. This is a *deliberate*
re-export, not the default — make it explicitly, and only when the
ergonomic gain is real (e.g., a small bridge file that exists precisely
to bundle imports for a sub-area).

**Rules of thumb when in doubt:**

- Demote first. If `lake build` of every dependent file still passes
  with the import non-public, leave it demoted.
- Statements that mention *notation* defined in an imported module do
  not automatically force the import to be public — Lean's module loader
  handles transitive notation visibility through the dependent's own
  import graph.
- A `public import` that exists "just to be safe" is wrong by default;
  if you can't name a downstream consumer that needs it, demote it.

## Reviewer-feedback intent

Distinguish reviewer **action items** ("please change X", "should be Y",
"must add Z") from **musings** ("I wonder if W would be cleaner",
parenthetical asides, "TBH I'd prefer…", "perhaps…"). Action items
must be addressed; musings can be acknowledged in a reply and deferred
to a follow-up. Trying to address every musing blows scope and slows
the PR.

Tone signals for "defer":
- "I wonder if …"
- parentheticals
- "TBH" / "personally" / "FWIW"
- "perhaps" / "maybe" / "you might consider"

Tone signals for "action":
- "please change …"
- "should be …" / "must …"
- direct correction with the alternative
- a code suggestion block
