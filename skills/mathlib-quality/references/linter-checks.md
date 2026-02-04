# Mathlib Linter Checks

## Overview

Mathlib includes several linters that automatically check code quality. This document explains each linter, what it catches, and how to fix violations.

## Running Linters

```bash
# Run all linters on a file
lake exe runLinter MyFile.lean

# Run specific linter
lake exe runLinter --only unusedArguments MyFile.lean

# Check linter output in CI
# Linters run automatically on PR
```

## Core Linters

### `unusedArguments`

**What it checks:** Arguments that are not used in the definition.

```lean
-- Bad: y is unused
def foo (x y : Nat) : Nat := x + 1

-- Fix option 1: Remove unused argument
def foo (x : Nat) : Nat := x + 1

-- Fix option 2: Use underscore prefix
def foo (x _y : Nat) : Nat := x + 1

-- Fix option 3: Suppress with attribute (rare)
@[nolint unusedArguments]
def foo (x y : Nat) : Nat := x + 1
```

### `docBlame`

**What it checks:** Public declarations without docstrings.

```lean
-- Bad: no docstring
def importantDef : Type := Nat

-- Good: has docstring
/-- A type alias for natural numbers used in our API. -/
def importantDef : Type := Nat
```

**Exceptions:**
- Private declarations
- Declarations in `Internal` namespaces
- Instances (usually)

### `simpNF`

**What it checks:** Simp lemmas not in normal form.

```lean
-- Bad: LHS can be further simplified
@[simp]
theorem foo : a + 0 + 0 = a := by ring

-- Good: LHS is in simp normal form
@[simp]
theorem foo : a + 0 = a := add_zero a
```

**Common fixes:**
- Remove `@[simp]` if lemma shouldn't be a simp lemma
- Rewrite to put LHS in normal form
- Use `@[simp, nolint simpNF]` if intentional

### `simpComm`

**What it checks:** Simp lemmas that commute arguments without progress.

```lean
-- Bad: just reorders without simplification
@[simp]
theorem add_comm' : a + b = b + a := add_comm a b

-- This would cause simp to loop, so it's rejected
```

### `dupNamespace`

**What it checks:** Declarations with duplicate namespace components.

```lean
-- Bad
namespace Foo
  def Foo.bar := ...  -- Foo.Foo.bar
end Foo

-- Good
namespace Foo
  def bar := ...  -- Foo.bar
end Foo
```

### `checkType`

**What it checks:** Theorems that could be definitions (and vice versa).

```lean
-- Bad: computational content marked as theorem
theorem myComputation : Nat := 42

-- Good: use def for computational content
def myComputation : Nat := 42

-- Bad: proof marked as def
def myLemma : 1 + 1 = 2 := rfl

-- Good: use theorem for proofs
theorem myLemma : 1 + 1 = 2 := rfl
```

### `checkUnivs`

**What it checks:** Universe level issues.

```lean
-- Bad: unnecessarily restrictive universe
def Foo : Type := ...  -- locks to Type 0

-- Good: universe polymorphic
def Foo : Type* := ...
-- or
def Foo.{u} : Type u := ...
```

### `explicitVarsOfIff`

**What it checks:** Iff lemmas where variables should be explicit.

```lean
-- Bad: implicit variable in iff
theorem foo {x : α} : P x ↔ Q x := ...

-- Good: explicit for iff (usually)
theorem foo (x : α) : P x ↔ Q x := ...
```

### `decidableClassical`

**What it checks:** Using `Classical.dec` when `Decidable` instance exists.

```lean
-- Bad: unnecessary classical reasoning
theorem foo [DecidableEq α] (a b : α) : a = b ∨ a ≠ b := by
  by_cases h : a = b  -- uses Classical internally
  ...

-- Good: use decidable instance
theorem foo [DecidableEq α] (a b : α) : a = b ∨ a ≠ b :=
  decidable.em (a = b)
```

### `defLemma`

**What it checks:** Lemmas that are really definitions.

```lean
-- Bad: returns data but called lemma
lemma myFun : α → β := fun x => ...

-- Good: use def for data
def myFun : α → β := fun x => ...
```

### `unusedHavesSuffices`

**What it checks:** Unused `have` or `suffices` in proofs.

```lean
-- Bad: h is never used
theorem foo : P := by
  have h : Q := ...
  exact hp

-- Good: remove unused have
theorem foo : P := by
  exact hp
```

## Style Linters

### `style.cdot`

**What it checks:** Consistent use of `·` for focused goals.

```lean
-- Bad: inconsistent bullet style
theorem foo : P ∧ Q := by
  constructor
  exact hp
  · exact hq  -- inconsistent

-- Good: consistent bullets
theorem foo : P ∧ Q := by
  constructor
  · exact hp
  · exact hq
```

### `style.lambdaSyntax`

**What it checks:** Use of `λ` instead of `fun`.

```lean
-- Bad
def foo := λ x => x + 1

-- Good
def foo := fun x => x + 1
```

### `style.longLine`

**What it checks:** Lines exceeding 100 characters.

```lean
-- Bad
theorem this_is_a_very_long_theorem_name_that_definitely_exceeds_one_hundred_characters_and_should_be_wrapped : P := ...

-- Good
theorem this_is_a_very_long_theorem_name
    (that_definitely_exceeds_one_hundred_characters) : P := ...
```

### `style.setOption`

**What it checks:** Debug/development options left in code.

```lean
-- Bad: debug options in final code
set_option trace.Meta.Tactic.simp true
set_option pp.all true

-- Good: remove before PR
-- (no set_option in final code)
```

Exceptions: `set_option linter.*` for suppressing linters is OK when justified.

## Suppressing Linters

### Per-Declaration

```lean
@[nolint unusedArguments]
def foo (x y : Nat) : Nat := x + 1

@[nolint docBlame, nolint unusedArguments]
def bar ...
```

### Per-Section

```lean
set_option linter.unusedArguments false in
section
  def foo ...
  def bar ...
end
```

### Guidelines for Suppression

1. **Justify:** Add a comment explaining why
2. **Minimize:** Suppress only what's necessary
3. **Review:** Suppressions are scrutinized in PR review
4. **Prefer fixes:** Always try to fix rather than suppress

## CI Checks

Mathlib CI runs linters automatically. To pass:

1. No linter errors on new/modified code
2. Existing suppressions need justification
3. Style checks must pass

## Common Linter Errors and Fixes

| Error | Likely Cause | Fix |
|-------|--------------|-----|
| `unused argument` | Argument not referenced | Remove or prefix with `_` |
| `missing docstring` | Public decl without docs | Add `/-- ... -/` |
| `simp lemma not in simp-normal form` | LHS simplifies further | Rewrite or remove `@[simp]` |
| `duplicate namespace` | Redundant namespace prefix | Remove prefix |
| `line too long` | >100 chars | Break line |
| `λ syntax` | Using `λ` | Change to `fun` |

## Related Commands

```bash
# Check style locally
./scripts/style-checker.sh MyFile.lean

# Run lint on all modified files
git diff --name-only | xargs lake exe runLinter
```
