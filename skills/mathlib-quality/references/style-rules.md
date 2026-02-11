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
- **Maximum**: ~1500 lines (consider splitting if larger)
- **Preferred**: 500-1000 lines
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

### Comments in Proofs

**Mathlib proofs should have NO inline comments.** Proofs should be self-documenting through
clear variable names and logical structure. Use docstrings for documentation.

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

**Docstrings should be SHORT** - one sentence describing what it proves, not how.

```lean
-- Bad: too verbose, contains proof strategy
/-- This theorem shows that f is continuous. The proof proceeds by first
establishing boundedness on compact sets using the Heine-Borel theorem,
then applying the sequential characterization of continuity. We use the
fact that f is locally Lipschitz to conclude. -/
theorem f_continuous : Continuous f := by ...

-- Good: brief description only
/-- `f` is continuous. -/
theorem f_continuous : Continuous f := by ...
```

**Only important public theorems need docstrings:**
```lean
-- Good: main theorem has docstring
/-- The valence formula for modular forms of weight k. -/
theorem valence_formula : ... := by ...

-- Good: helper has no docstring, is private, uses _aux suffix
private theorem valence_formula_aux : ... := by ...
```

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

## Syntax Preferences

### Use `fun` over `λ`
```lean
-- Good
fun x => x + 1
fun x y => x * y

-- Bad (λ is deprecated)
λ x => x + 1
```

### Use `↦` (mapsto) in source code
```lean
-- Good
fun x ↦ x + 1

-- Also acceptable
fun x => x + 1
```

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

### One tactic per line (usually)
```lean
-- Good
theorem foo : P := by
  apply h₁
  apply h₂
  exact h₃

-- Acceptable for very short closers
theorem foo : P := by exact h
theorem bar : P := by simp; ring
```

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
