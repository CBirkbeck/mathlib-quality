---
name: pre-submit
description: Pre-PR submission checklist
---

# /pre-submit - Pre-PR Submission Checklist

Final verification before submitting a PR to mathlib.

## Usage

```
/pre-submit [file_path or directory]
```

## Checklist

### 1. Compilation
- [ ] `lake build` succeeds without errors
- [ ] No warnings in modified files
- [ ] All `sorry` removed
- [ ] No `#check`, `#print`, `#eval` debugging statements

### 2. File Quality

For each modified file:
- [ ] File length ≤ 1500 lines
- [ ] All lines ≤ 100 characters
- [ ] Proper copyright header
- [ ] Module docstring present
- [ ] Imports organized and minimal

### 3. Code Quality
- [ ] No bare `simp` (use `simp only`)
- [ ] No `set_option maxHeartbeats`
- [ ] No `set_option trace.*`
- [ ] No `set_option pp.*`
- [ ] Instance names are explicit
- [ ] Naming follows conventions

### 4. Documentation
- [ ] All public definitions have docstrings
- [ ] All public theorems have docstrings (if non-obvious)
- [ ] Docstrings are informative and accurate

### 5. Linter Compliance
- [ ] No linter errors
- [ ] Any `@[nolint]` is justified

### 6. PR Metadata
- [ ] PR title follows format: `feat/fix/refactor/docs(area): description`
- [ ] PR description explains the changes
- [ ] Related issues linked

## Workflow

### Step 1: Build Check
```bash
lake build
```

Verify no errors in output.

### Step 2: Run Style Check
```
/check-style [modified_files]
```

Address all 🔴 and 🟡 issues.

### Step 3: Run Linters
```bash
lake exe runLinter [modified_files]
```

Fix any linter errors.

### Step 4: Search for Debug Artifacts
```lean
-- Search for these patterns and remove if found:
sorry
#check
#print
#eval
set_option trace
set_option pp
set_option maxHeartbeats
```

### Step 5: Documentation Review

For each public declaration:
1. Check docstring exists
2. Verify docstring is accurate
3. Ensure docstring explains purpose

### Step 6: Final Compilation
```bash
lake build
```

Ensure clean build.

## Output Format

```
## Pre-Submit Check: [project/files]

### ✓ Build Status
- Compilation: ✓ Successful
- Warnings: 0
- Errors: 0

### ✓ File Quality
| File | Lines | Max Line | Header | Docstring |
|------|-------|----------|--------|-----------|
| Foo.lean | 234 | 98 | ✓ | ✓ |
| Bar.lean | 456 | 95 | ✓ | ✓ |

### ✓ Code Quality
- sorry: 0 found
- Debug options: 0 found
- Bare simp: 0 found

### ✓ Documentation
- Public declarations: 15
- With docstrings: 15
- Missing: 0

### ✓ Linters
- Errors: 0
- Warnings: 0

### PR Checklist
- [ ] Title format: `feat(Algebra): add FooBar lemmas`
- [ ] Description written
- [ ] Related issues: #1234

### Ready for Submission: ✓

---

To submit:
1. Create branch: `git checkout -b feat/foo-bar`
2. Commit changes: `git commit -m "feat(Algebra): add FooBar lemmas"`
3. Push: `git push -u origin feat/foo-bar`
4. Create PR via GitHub
```

## Common Issues

### sorry Still Present
```
✗ Found sorry at:
  - Foo.lean:45
  - Bar.lean:123

Action: Complete these proofs before submission
```

### Debug Options Left In
```
✗ Found debug options:
  - Foo.lean:12: set_option trace.Meta.Tactic.simp true
  - Bar.lean:34: set_option maxHeartbeats 400000

Action: Remove debug options
```

### Missing Docstrings
```
✗ Missing docstrings:
  - Foo.lean:67: def importantFunction
  - Bar.lean:89: theorem keyResult

Action: Add docstrings for public API
```

### Linter Failures
```
✗ Linter errors:
  - Foo.lean:45: unused argument 'x'
  - Bar.lean:67: simp lemma not in normal form

Action: Fix linter errors or add justified @[nolint]
```

## PR Title Format

```
type(scope): description

Types:
- feat: New feature
- fix: Bug fix
- refactor: Code restructuring
- docs: Documentation only
- style: Formatting only
- perf: Performance improvement
- test: Adding tests
- chore: Maintenance

Scope: Area of mathlib (Algebra, Topology, Analysis, etc.)

Examples:
- feat(Algebra/Ring): add comm_ring instance for Foo
- fix(Topology): correct definition of LocallyCompact
- docs(Analysis/Calculus): improve docstrings for derivative lemmas
- refactor(Data/List): simplify proof of length_append
```

## Reference

- Full style guide: `references/style-rules.md`
- Naming conventions: `references/naming-conventions.md`
- Linter rules: `references/linter-checks.md`

### Final Step: Record Learnings

After completing the pre-submit check and showing the report, capture any notable findings.

**For each significant issue found**, write a JSON entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "pre-submit",
  "type": "<style_correction|naming_fix|golf_pattern|failed_pattern>",
  "before_code": "<the problematic code, max 500 chars>",
  "after_code": "<the fix if applied, max 500 chars>",
  "pattern_tags": ["<relevant pattern names>"],
  "description": "<1-2 sentence description of what was caught in pre-submit>",
  "math_area": "<analysis|algebra|topology|number_theory|combinatorics|order|category_theory|measure_theory|other>",
  "accepted": true,
  "source": "agent_suggestion",
  "context": {
    "file_path": "<relative path>",
    "theorem_name": "<if applicable>"
  }
}
```

**What to capture from pre-submit:**
- Issues that other commands missed (indicates gaps in earlier passes)
- Recurring patterns across files (e.g., same linter issue in multiple places)
- Things the user chose to defer or override

**What NOT to capture:**
- Issues already captured by earlier `/cleanup` or `/check-style` runs
- Standard compilation warnings

**Keep it lightweight** - only 1-3 entries per command run, focusing on lessons for future runs.
