---
name: cleanup
description: Full file cleanup to mathlib standards
---

# /cleanup - Full File Cleanup

Clean up a Lean file to meet mathlib standards.

## Usage

```
/cleanup [file_path]
```

If no file is specified, operates on the currently open file.

## Workflow

### Step 1: Collect Lint Diagnostics

**Before doing anything else**, run `lean_diagnostic_messages` on the file to get ALL warnings and errors from Lean's built-in linters. These are the same yellow/red underlines shown in VS Code.

```
lean_diagnostic_messages(file_path="/path/to/File.lean")
```

This returns diagnostics in the format: `"l{line}c{col}-l{line}c{col}, severity: {N}\n{message}"`
- Severity 1 = error (red), Severity 2 = warning (yellow), Severity 3 = info (blue)

**Group the warnings by line number** and print a summary:

```
## Lint Diagnostics for File.lean

### Errors (must fix)
- l45: type mismatch...

### Warnings (fix all)
- l12: unused variable `hp0_ne_i` [linter.unusedVariables]
- l34: line has 115 characters [style.longLine]
- l56: `$` is not allowed, use `<|` [style.dollarSyntax]
- l78: unused `have` [linter.unusedHavesSuffices]
- l90: declaration uses `sorry` [linter.sorry]
- l102: `set_option maxHeartbeats` [style.setOption]
```

These diagnostics are your **primary TODO list**. Every warning must be addressed.

**Common Lean/Mathlib linter warnings you will see:**
| Linter | Warning | Fix |
|--------|---------|-----|
| `unusedVariables` | Unused parameter | Remove from signature and call sites (do NOT underscore) |
| `unusedHavesSuffices` | Unused `have`/`suffices` | Remove or inline |
| `style.longLine` | Line >100 chars | Break line |
| `style.dollarSyntax` | `$` used | Replace with `<|` |
| `style.lambdaSyntax` | `λ` used | Replace with `fun` |
| `style.setOption` | Disallowed `set_option` | Decompose proof instead of bumping heartbeats |
| `style.cdot` | Incorrect `·` usage | Fix bullet formatting |
| `style.show` | `show` in tactic mode | Replace with `change` |
| `unusedArguments` | Unused function argument | Remove or use `_` |
| `simpNF` | Simp lemma not in normal form | Fix statement |
| `docBlame` | Public decl without docstring | Add one-sentence docstring |

### Step 1b: Initial Analysis

Read the target file and also assess:
- File length (flag if >1000 lines)
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

### Step 3: Build Declaration List

Extract every declaration from the file into an ordered list:

```
1. def myFoo (line 25)
2. lemma bar_thing (line 40)
3. theorem main_result (line 65)
...
```

Print this list. Then process each declaration **one at a time**, in order, applying the FULL checklist below.

### Step 4: Per-Declaration Checklist (THE CORE LOOP)

**For EACH declaration in the list**, apply ALL of the following checks. Do not skip any. Print the declaration name before checking it.

#### CHECK 0: Lint Warnings (from Step 1)
- List ALL lint warnings from Step 1 that fall within this declaration's line range
- These are **mandatory fixes** — address every single one
- Common fixes: remove unused variables (entirely, not underscore), remove unused `have`/`suffices`, fix line length, replace `$` with `<|`, replace `λ` with `fun`, replace `show` with `change`

#### CHECK 1: Mathlib-First
- Could this `def` be replaced by a mathlib definition? Search with `exact?`, Loogle, or by name.
- If a mathlib equivalent exists: replace with it. Do NOT create a bridge theorem.
- For simple compositions: prefer `local notation` over a `def`.

#### CHECK 2: Naming
- `lemma`/`theorem` (returns Prop) → `snake_case`
- `def` (returns data) → `lowerCamelCase`
- `structure`/`inductive` (Type) → `UpperCamelCase`
- Helper lemmas → `snake_case` + `_aux` suffix, mark `private`
- Theorem names should follow "conclusion_of_hypothesis" pattern
- American English (`Factorization` not `Factorisation`)
- If renamed: update ALL usages across the file

#### CHECK 3: Unused Variables
- Any parameter with an unused variable warning? → Remove entirely from signature and all call sites. Do NOT add `_` prefix.

#### CHECK 4: Formatting
- 2-space indentation in tactic blocks
- Lines ≤ 100 chars (break at parameters, operators)
- `by` at end of line, never alone on its own line
- `fun` over `λ`, `<|` over `$`
- Proper whitespace around operators and colons

#### CHECK 5: Comments
- Remove ALL inline comments from proofs
- No "Step N" markers, no play-by-play
- No commented-out code (theorems as comments = unacceptable)
- If this is a key public theorem: add ONE-SENTENCE docstring (what, not how)
- Private/helper lemmas: NO docstring

#### CHECK 6: Proof Structure
- `set_option maxHeartbeats`? → Decompose the proof into helper lemmas instead
- Proof >30 lines? → Flag for decomposition
- `∧` in theorem statement? → Split into separate lemmas, combine with `⟨left, right⟩`
- Any `constructor`/`by_cases`/`match`/`induction` branch >10 lines? → Extract into private helper lemma

#### CHECK 7: Proof Golf
- Consecutive trivial `have h := foo x` lines? → Inline them: `exact bar (foo x)`
- `by exact h` → just `h`
- `by rfl` → `rfl`
- Single-use `have` with trivial RHS? → Inline at usage site
- Can `ring`, `linarith`, `omega`, `grind`, `simp`, or `aesop` close the goal? → Use them
- `rw [...]; exact h` → `rwa [...]`
- Redundant tactics? → Remove

#### CHECK 8: Visibility
- Only used within this file? → `private`
- Helper for one main result? → `private` with `_aux` suffix
- API lemma for reuse? → public, no `private`

After checking all 8 items, **make the fixes** for that declaration, then move to the next one.

### Step 5: Post-Loop File-Level Checks

After processing all declarations:

1. **File length** - Still >1000 lines? → Split by topic
2. **Import minimality** - Remove unused imports
3. **Import order** - Mathlib imports first (alphabetical), then project imports

### Step 6: Compile Verification & Lint Re-check

After all changes:
1. Save the file
2. Run `lean_diagnostic_messages` on the file again
3. **Compare with Step 1 diagnostics:**
   - All original warnings should be resolved
   - No new errors should be introduced
   - If new warnings appeared (from code you moved/rewrote), fix them now
4. If errors were introduced, revert the problematic changes
5. Repeat until `lean_diagnostic_messages` returns `[]` (empty = clean)

## Output Format

```
## Cleanup Report for [filename]

### Summary
- Lines: X (Y lines changed)
- Declarations: N
- Names fixed: K
- Other issues fixed: M

### Naming Fixes
| Old Name | New Name | Reason |
|----------|----------|--------|
| `fooBar` | `foo_bar` | snake_case for lemmas |
| `Lemma1` | `bound_of_compact` | descriptive name |

### Other Changes Made
1. Fixed line length on lines: 45, 78, 123
2. Fixed indentation in: theorem foo, lemma bar
3. Stripped inline comments from proofs
4. Inlined 5 single-use `have` statements

### Compilation Status
✓ File compiles without errors
```

## Reference

See:
- `skills/mathlib-quality/references/naming-conventions.md` - Full naming guide
- `skills/mathlib-quality/references/style-rules.md` - Complete style rules

## Example

Before:
```lean
import Mathlib.Data.Set.Basic

-- My custom lemma for addition
theorem myAddLemma(x:Nat):x+0=x:= by
    -- This is obvious
    simp
```

After:
```lean
import Mathlib.Data.Set.Basic

/-!
# Basic theorems

Simple arithmetic lemmas.
-/

/-- Addition of zero on the right. -/
theorem add_zero_right (x : Nat) : x + 0 = x := by simp only [add_zero]
```

### Final Step: Record Learnings

After completing all changes and showing the report, capture what was learned.

**For each significant change made**, write a JSON entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "cleanup",
  "type": "<style_correction|naming_fix|golf_pattern|decomposition|mathlib_discovery|failed_pattern>",
  "before_code": "<original code snippet, max 500 chars>",
  "after_code": "<resulting code snippet, max 500 chars>",
  "pattern_tags": ["<relevant pattern names>"],
  "description": "<1-2 sentence description of the change>",
  "math_area": "<analysis|algebra|topology|number_theory|combinatorics|order|category_theory|measure_theory|other>",
  "accepted": true,
  "source": "<agent_suggestion|user_correction>",
  "context": {
    "file_path": "<relative path>",
    "theorem_name": "<if applicable>"
  }
}
```

**What to capture from cleanup:**
- Each naming correction (before/after name with reason)
- Each non-trivial style fix (e.g., `by` placement, comment removal with proof restructuring)
- Each proof that was golfed or decomposed during cleanup
- Each mathlib lemma discovered that replaced custom code
- Each suggestion the user rejected (with `"accepted": false`)
- Each time the user corrected your suggestion (with `"source": "user_correction"`)

**What NOT to capture:**
- Trivial whitespace fixes
- Line length adjustments
- Import reordering
- Mechanical rule applications (adding missing docstrings, fixing indentation)

**Keep it lightweight** - only 1-5 entries per command run, capturing the most interesting/novel learnings.
