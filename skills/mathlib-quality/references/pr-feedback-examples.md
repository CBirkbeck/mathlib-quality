# PR Feedback Examples

This file contains curated examples of common feedback patterns from mathlib PR reviews. These examples are anonymized and focus on the technical content.

## Style Feedback

### Line Length

**Issue:** Lines exceeding 100 characters

```lean
-- Before (too long)
theorem very_long_theorem_name_that_exceeds_the_limit (h₁ : some_hypothesis) (h₂ : another_hypothesis) : conclusion := by

-- After (properly broken)
theorem very_long_theorem_name_that_exceeds_the_limit
    (h₁ : some_hypothesis) (h₂ : another_hypothesis) : conclusion := by
```

**Feedback pattern:** "Line too long, please break at 100 chars"

### Indentation

**Issue:** Incorrect tactic block indentation

```lean
-- Before (wrong indentation)
theorem foo : P := by
    apply h  -- 4 spaces is wrong
    exact hx

-- After (correct 2-space indentation)
theorem foo : P := by
  apply h
  exact hx
```

**Feedback pattern:** "Please use 2-space indentation for tactic blocks"

### Whitespace

**Issue:** Missing or extra whitespace

```lean
-- Before
def foo(x:α):β:= ...
f(x,y)

-- After
def foo (x : α) : β := ...
f (x, y)
```

**Feedback pattern:** "Missing space around colon" / "Space needed before parenthesis"

## Naming Feedback

### Non-Descriptive Names

**Issue:** Theorem names that don't follow the conclusion-of-hypothesis pattern

```lean
-- Before
theorem lemma1 : a + b = b + a := ...
theorem my_theorem : P → Q → P ∧ Q := ...

-- After
theorem add_comm : a + b = b + a := ...
theorem And.intro : P → Q → P ∧ Q := ...
```

**Feedback pattern:** "Please use a descriptive name following mathlib conventions"

### Inconsistent Naming

**Issue:** Names that don't match similar existing lemmas

```lean
-- Before (inconsistent with add_zero)
theorem zero_added : 0 + a = a := ...

-- After (matches existing convention)
theorem zero_add : 0 + a = a := ...
```

**Feedback pattern:** "This should be named X to match the existing Y"

### Hypothesis Names

**Issue:** Non-standard hypothesis names

```lean
-- Before
theorem foo (hypothesis1 : P) (H : Q) : R := ...

-- After
theorem foo (hp : P) (hq : Q) : R := ...
```

**Feedback pattern:** "Use h-prefixed names for hypotheses"

## Documentation Feedback

### Missing Module Docstring

**Issue:** File lacks module documentation

```lean
-- Before (missing)
import Mathlib.Algebra.Group.Basic

namespace Foo

-- After
import Mathlib.Algebra.Group.Basic

/-!
# Foo structures and lemmas

This file defines `Foo` and proves basic properties.

## Main definitions
* `Foo`: A structure representing...

## Main results
* `foo_bar`: Shows that foo implies bar
-/

namespace Foo
```

**Feedback pattern:** "Please add a module docstring"

### Missing Declaration Docstring

**Issue:** Public declaration without documentation

```lean
-- Before
def importantFunction (x : α) : β := ...

-- After
/-- Converts `x` to its corresponding `β` value.

This is useful when... -/
def importantFunction (x : α) : β := ...
```

**Feedback pattern:** "Please add a docstring for this definition"

## Proof Golf Feedback

### Unnecessary Tactics

**Issue:** Proofs longer than necessary

```lean
-- Before
theorem foo : a = a := by
  rfl

-- After
theorem foo : a = a := rfl
```

**Feedback pattern:** "This can just be `rfl`"

### Missing Automation

**Issue:** Manual proofs where automation works

```lean
-- Before
theorem foo (a b : ℤ) : a + b = b + a := by
  induction a
  · simp
  · simp [add_succ]
  · simp [neg_add]

-- After
theorem foo (a b : ℤ) : a + b = b + a := add_comm a b
-- or
theorem foo (a b : ℤ) : a + b = b + a := by ring
```

**Feedback pattern:** "This follows from add_comm" / "Try `ring` here"

### Verbose Have Blocks

**Issue:** Unnecessary intermediate steps

```lean
-- Before
theorem foo (h : P → Q) (hp : P) : Q := by
  have hq : Q := h hp
  exact hq

-- After
theorem foo (h : P → Q) (hp : P) : Q := h hp
```

**Feedback pattern:** "The `have` is unnecessary, just use `h hp` directly"

### Bare simp

**Issue:** Using `simp` without arguments in library code

```lean
-- Before
theorem foo : a + 0 = a := by simp

-- After
theorem foo : a + 0 = a := by simp only [add_zero]
-- or better
theorem foo : a + 0 = a := add_zero a
```

**Feedback pattern:** "Please use `simp only` with explicit lemmas in library code"

## API Design Feedback

### Missing Simp Lemmas

**Issue:** Definitions without corresponding simp lemmas

```lean
-- Before (definition only)
def myFun (x : α) : β := ...

-- After (with simp lemma)
def myFun (x : α) : β := ...

@[simp]
theorem myFun_def (x : α) : myFun x = ... := rfl
```

**Feedback pattern:** "Please add a simp lemma for this definition"

### Instance Visibility

**Issue:** Instance should be scoped or have explicit name

```lean
-- Before
instance : Coe α β := ...

-- After
instance instCoeAlphaBeta : Coe α β := ...
-- or
scoped instance : Coe α β := ...
```

**Feedback pattern:** "Please give this instance an explicit name"

### Namespace Organization

**Issue:** Lemmas in wrong namespace

```lean
-- Before (lemma about Foo.bar in root)
theorem bar_property : Foo.bar x = ... := ...

-- After (in proper namespace)
namespace Foo
theorem bar_property : bar x = ... := ...
end Foo
```

**Feedback pattern:** "This should be in the `Foo` namespace"

## Import Feedback

### Unnecessary Imports

**Issue:** Importing more than needed

```lean
-- Before
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Basic  -- not actually used

-- After
import Mathlib.Topology.Basic
```

**Feedback pattern:** "This import doesn't seem to be used"

### Missing Imports

**Issue:** Relying on transitive imports

```lean
-- Feedback: "Please add explicit import for X, don't rely on transitive imports"
```

## Performance Feedback

### Slow Proofs

**Issue:** Proofs that take too long to compile

```lean
-- Before (slow)
theorem foo : P := by
  simp [everything]  -- takes 30 seconds

-- After (fast)
theorem foo : P := by
  simp only [specific_lemmas]  -- takes 0.5 seconds
```

**Feedback pattern:** "This proof is slow, please optimize"

### Heartbeat Issues

**Issue:** Proof exceeds default heartbeat limit

```lean
-- Before
set_option maxHeartbeats 400000 in
theorem foo : P := by ...

-- After (optimized to not need the option)
theorem foo : P := by ...
```

**Feedback pattern:** "Please optimize the proof to not need maxHeartbeats increase"

## Common Response Patterns

When addressing feedback:

1. **Acknowledge the issue:** "Fixed the line length issue"
2. **Explain if unclear:** "Changed to X because Y"
3. **Ask if uncertain:** "Should this be X or Y?"
4. **Verify compilation:** Always ensure changes compile
5. **Address all comments:** Don't miss any feedback items
