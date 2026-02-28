---
name: check-style
description: Validate code against mathlib style rules
---

# /check-style - Style Validation

Validate a Lean file against mathlib style rules without making changes.

## Usage

```
/check-style [file_path]
```

If no file is specified, operates on the currently open file.

## What It Checks

### 1. File Structure
- [ ] File length ≤ 1500 lines
- [ ] Has copyright header
- [ ] Has module docstring after imports
- [ ] Imports are organized (Mathlib first, alphabetical)

### 2. Line Formatting
- [ ] All lines ≤ 100 characters
- [ ] No trailing whitespace
- [ ] Consistent line endings

### 3. Indentation
- [ ] 2-space indentation in tactic blocks
- [ ] Proper alignment of continuation lines
- [ ] Consistent indentation throughout

### 4. Syntax Preferences
- [ ] `fun` instead of `λ`
- [ ] `<|` instead of `$`
- [ ] `change` instead of `show` in tactic mode
- [ ] No redundant parentheses

### 5. Naming Conventions
- [ ] `snake_case` for lemmas/theorems
- [ ] `UpperCamelCase` for types/structures
- [ ] Descriptive hypothesis names (h-prefix)
- [ ] Instance names follow `inst` pattern

### 6. Documentation
- [ ] Module docstring present
- [ ] Public declarations have docstrings
- [ ] Docstrings are informative

### 7. Code Quality
- [ ] No bare `simp` (use `simp only`)
- [ ] No `sorry`
- [ ] No debug `set_option`
- [ ] No unnecessary `have` blocks (flagged, not auto-detected)

## Output Format

```
## Style Check: [filename]

### ✓ Passing Checks
- File length: 234 lines (OK)
- Copyright header: Present
- Module docstring: Present

### ✗ Issues Found

#### Line Length (3 violations)
- Line 45: 112 chars (max 100)
- Line 78: 105 chars (max 100)
- Line 123: 108 chars (max 100)

#### Indentation (2 violations)
- Line 56: Expected 2 spaces, found 4
- Line 89: Inconsistent indentation in tactic block

#### Syntax (1 violation)
- Line 34: Use `fun` instead of `λ`

#### Documentation (2 missing)
- Line 67: `importantDef` lacks docstring
- Line 90: `helperFunction` lacks docstring

#### Naming (1 suggestion)
- Line 45: `lemma1` - consider more descriptive name

### Summary
- Total checks: 15
- Passing: 11
- Failing: 4
- Suggestions: 1

### Severity
🔴 3 must-fix issues (line length, indentation)
🟡 1 should-fix issue (syntax preference)
🟢 2 suggestions (documentation, naming)
```

## Severity Levels

| Level | Description | Action |
|-------|-------------|--------|
| 🔴 Must Fix | Will fail CI/PR review | Fix before PR |
| 🟡 Should Fix | Strong convention | Fix unless justified |
| 🟢 Suggestion | Improvement opportunity | Consider fixing |

## Reference Files

For detailed rules, see:
- `references/style-rules.md` - Formatting rules
- `references/naming-conventions.md` - Naming patterns
- `references/linter-checks.md` - Automated linters

## Comparison with Linters

This command checks style issues that may not be caught by Lean's built-in linters:
- Line length (linters don't always catch this)
- Specific formatting preferences
- Naming convention suggestions
- Documentation completeness

Run both `/check-style` and the official linters for complete coverage.

### Final Step: Record Learnings

After completing the style check and showing the report, capture any notable findings.

**For each non-obvious style issue found**, write a JSON entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "check-style",
  "type": "style_correction",
  "before_code": "<the offending code snippet, max 500 chars>",
  "after_code": "",
  "pattern_tags": ["<relevant pattern names>"],
  "description": "<1-2 sentence description of the style issue>",
  "math_area": "<analysis|algebra|topology|number_theory|combinatorics|order|category_theory|measure_theory|other>",
  "accepted": true,
  "source": "agent_suggestion",
  "context": {
    "file_path": "<relative path>",
    "theorem_name": "<if applicable>"
  }
}
```

**What to capture from check-style:**
- Recurring style issues that indicate project-level patterns (e.g., consistently wrong `by` placement)
- Naming convention violations that suggest the user needs guidance
- Unusual patterns not covered by standard rules

**What NOT to capture:**
- Individual line length violations
- Trivial whitespace issues
- Standard linter-catchable issues

**Keep it lightweight** - only 1-3 entries per command run, focusing on patterns rather than individual violations.
