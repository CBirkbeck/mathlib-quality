# Mathlib Style Rules

## File Structure

### Header Order
Every mathlib file should have this structure:
```lean
/-
Copyright (c) 2024 [Names]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Names]
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

### File Length
- **Maximum**: 1500 lines
- **Preferred**: 500-1000 lines
- **Action**: Split large files by topic

### Line Length
- **Maximum**: 100 characters
- **Breaking points**: After operators, at commas
- **Continuation**: Align with opening delimiter or indent 2 spaces

## Formatting Rules

### Indentation
- **Tactic blocks**: 2 spaces
- **Continuation lines**: 2 spaces or align with delimiter
- **Nested blocks**: Add 2 spaces per level

```lean
-- Good: 2-space indentation
theorem foo : P := by
  apply bar
  · exact h₁
  · exact h₂

-- Bad: inconsistent indentation
theorem foo : P := by
    apply bar  -- 4 spaces is wrong
```

### Whitespace

**Around operators:**
```lean
-- Good
a + b * c
f x y
(a, b)

-- Bad
a+b*c
f  x  y
( a , b )
```

**In type signatures:**
```lean
-- Good
def foo (x : α) (y : β) : γ := ...
theorem bar {α : Type*} [Group α] (a b : α) : a * b = b * a := ...

-- Bad
def foo (x:α)(y:β):γ := ...
```

**No trailing whitespace** on any line.

### Line Breaking

**Function applications:**
```lean
-- Good: break after opening, align arguments
theorem long_theorem_name
    (h₁ : very_long_hypothesis)
    (h₂ : another_hypothesis) :
    conclusion := by
  ...

-- Also good: each argument on its own line
have := very_long_function_name
  argument1
  argument2
  argument3
```

**Tactic sequences:**
```lean
-- Good: one tactic per line in by blocks
theorem foo : P := by
  apply h
  exact rfl

-- Acceptable: short proofs on one line
theorem foo : P := by apply h; exact rfl

-- Bad: mixing styles
theorem foo : P := by apply h
  exact rfl
```

### Calc Blocks
```lean
-- Good: align relation symbols
calc a
    = b := by ...
  _ = c := by ...
  _ ≤ d := by ...

-- Also acceptable
calc
  a = b := by ...
  _ = c := by ...
```

## Syntax Preferences

### Use `fun` over `λ`
```lean
-- Good
fun x => x + 1
fun x y => x * y

-- Bad
λ x => x + 1
λ x y => x * y
```

### Use `<|` over `$`
```lean
-- Good
f <| g x
apply foo <| bar baz

-- Bad
f $ g x
apply foo $ bar baz
```

### Use `change` over `show` in proofs
```lean
-- Good (in tactic mode)
change P
exact hp

-- Bad (in tactic mode)
show P
exact hp
```

### Anonymous constructor syntax
```lean
-- Good
⟨a, b, c⟩
fun ⟨x, y⟩ => ...

-- Also good when clearer
Prod.mk a b
```

## Declaration Formatting

### Theorem/Lemma statements
```lean
-- Good: signature on one line if fits
theorem foo_bar (h : P) : Q := by ...

-- Good: break after colon if needed
theorem foo_bar_with_long_name (h₁ : hypothesis_one) (h₂ : hypothesis_two) :
    conclusion_statement := by
  ...

-- Good: break at parameters if very long
theorem foo_bar_with_very_long_name
    (h₁ : a_very_long_hypothesis_type)
    (h₂ : another_very_long_hypothesis) :
    conclusion := by
  ...
```

### Instance declarations
```lean
-- Good: explicit instance name
instance instAddCommMonoidFoo : AddCommMonoid Foo where
  add := ...
  zero := ...

-- Bad: anonymous instance
instance : AddCommMonoid Foo where ...
```

### Structure definitions
```lean
-- Good
structure Foo (α : Type*) where
  /-- Documentation for field1 -/
  field1 : α
  /-- Documentation for field2 -/
  field2 : α → α

-- Bad: no field documentation
structure Foo (α : Type*) where
  field1 : α
  field2 : α → α
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

## Proof Style

### Prefer term mode for simple proofs
```lean
-- Good: term mode for trivial proofs
theorem foo : a = a := rfl
theorem bar : P → P := id
theorem baz : P → Q → P := fun hp _ => hp

-- Use tactic mode for complex proofs
theorem complex : P := by
  obtain ⟨x, hx⟩ := h
  exact ⟨f x, hf hx⟩
```

### One tactic per line (usually)
```lean
-- Good
theorem foo : P := by
  apply h₁
  apply h₂
  exact h₃

-- Acceptable for very short
theorem foo : P := by exact h

-- Bad: hard to read
theorem foo : P := by apply h₁; apply h₂; exact h₃
```

### Focused subgoals with `·`
```lean
-- Good
theorem foo : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- Bad: no bullet points
theorem foo : P ∧ Q := by
  constructor
  exact hp
  exact hq
```
