# /cleanup - Full File Cleanup

Clean up a Lean file to meet mathlib standards.

## Usage

```
/cleanup [file_path]
```

If no file is specified, operates on the currently open file.

## Workflow

### Step 1: Initial Analysis

Read the target file and assess:
- File length (flag if >1500 lines)
- Line lengths (flag any >100 chars)
- Import organization
- Module docstring presence

### Step 2: Header Cleanup

1. **Copyright header** - Ensure proper format:
   ```lean
   /-
   Copyright (c) YEAR [Names]. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: [Names]
   -/
   ```

2. **Imports** - Organize alphabetically, remove unused:
   ```lean
   import Mathlib.Algebra.Group.Basic
   import Mathlib.Data.Set.Basic
   ```

3. **Module docstring** - Add or improve:
   ```lean
   /-!
   # Module Title

   Brief description.

   ## Main definitions
   * `Foo`: Description

   ## Main results
   * `foo_bar`: Description
   -/
   ```

### Step 3: Formatting Fixes

For each declaration, check and fix:

1. **Indentation** - Ensure 2-space indentation in tactic blocks
2. **Line breaks** - Break lines >100 chars appropriately
3. **Whitespace** - Fix spacing around operators, colons, parentheses
4. **Syntax preferences**:
   - `fun` over `λ`
   - `<|` over `$`
   - `change` over `show` in tactic mode

### Step 4: Naming Review

Check declaration names against conventions:
- `snake_case` for lemmas/theorems
- `UpperCamelCase` for types
- Descriptive names following "conclusion of hypotheses" pattern

Flag non-conforming names but don't auto-rename (requires user decision).

### Step 5: Documentation Check

For each public declaration:
- Check for docstring presence
- Suggest docstring content if missing

### Step 6: Proof Opportunities

Identify obvious golfing opportunities:
- Term-mode candidates (simple `by exact x` → `x`)
- Automation opportunities (`ring`, `linarith`, `omega`)
- Unnecessary `have` blocks

### Step 7: Compile Verification

After all changes:
1. Save the file
2. Run `lean_diagnostic_messages` to check for errors
3. If errors introduced, revert problematic changes

## Output Format

```
## Cleanup Report for [filename]

### Summary
- Lines: X (Y lines changed)
- Declarations: N
- Issues found: M
- Issues fixed: K

### Changes Made
1. Fixed line length on lines: 45, 78, 123
2. Fixed indentation in: theorem foo, lemma bar
3. Replaced λ with fun: 3 occurrences
4. Added module docstring

### Manual Review Needed
1. Line 56: Consider renaming `lemma1` to descriptive name
2. Line 89: Missing docstring for `importantDef`
3. Line 120: Proof could potentially be golfed

### Compilation Status
✓ File compiles without errors
```

## Reference

See `skills/mathlib-quality/references/style-rules.md` for complete rules.

## Example

Before:
```lean
import Mathlib.Data.Set.Basic
theorem foo(x:Nat):x+0=x:= by
    simp
```

After:
```lean
import Mathlib.Data.Set.Basic

/-!
# Basic theorems

Simple arithmetic lemmas.
-/

theorem foo (x : Nat) : x + 0 = x := by
  simp only [add_zero]
```
