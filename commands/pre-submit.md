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

Each step has a **required artifact** (a status block) and a **hard-stop condition**.
Skipping a step is detectable in the missing artifact; the per-step status blocks roll up
into the final report. Hard-stop on any step means /pre-submit reports `NOT READY FOR
SUBMISSION` — the user has to fix the issue before re-running.

### Step 1: Build Check (required artifact)

```bash
lake build 2>&1 | tee /tmp/pre-submit-build.log
```

Print the artifact:

```
[Step 1] lake build:    <PASS — exit 0, 0 errors, N warnings>
                        OR
                        <FAIL — exit X, M errors; see /tmp/pre-submit-build.log>
```

**Hard stop on FAIL.** The project must compile before any further check makes sense.

### Step 2: Run Cleanup (required artifact)

```
/cleanup [modified_files]
```

`/cleanup` runs its full 9-phase workflow — Doctor (Phase 0) → audit → file-level fixes →
per-decl golf → refactoring → final verification → simplify pass → report. Capture
`/cleanup`'s Phase-7 report and embed its summary here:

```
[Step 2] /cleanup:      <PASS-CLEAN — diagnostics clean, all gates pass, simplify pass-through>
                        <PASS-WITH-CHANGES — N issues fixed; gates clean; simplify fixed M things>
                        <FAIL — /cleanup ended in Overall: FAIL on gate <name>>
```

**Hard stop on FAIL.** Do not proceed if `/cleanup` couldn't reach a clean state.

If `/cleanup` was already run this session (e.g., the user ran it manually), confirm
its Phase-7 report is dated within this session and re-run if not.

### Step 3: Run Linters (required artifact)

```bash
lake exe runLinter [modified_files] 2>&1 | tee /tmp/pre-submit-linter.log
```

```
[Step 3] runLinter:     <PASS — 0 errors, 0 warnings>
                        <PASS-WITH-NOLINT — 0 errors; N suppressed via @[nolint], all justified>
                        <FAIL — N errors; see /tmp/pre-submit-linter.log>
```

**Hard stop on FAIL.** Linter errors block CI; fix or justify with a `@[nolint]` (and
record the justification — bare suppression without reason is itself a defect).

### Step 4: Search for Debug Artifacts (required artifact)

Grep the modified files (or whole project) for forbidden patterns:

```bash
grep -rn "sorry\b" --include="*.lean" .
grep -rn "^\s*#\(check\|print\|eval\|reduce\)\b" --include="*.lean" .
grep -rn "set_option \(trace\.\|pp\.\|maxHeartbeats\|maxRecDepth\)" --include="*.lean" .
grep -rn "^\s*axiom \|^\s*constant " --include="*.lean" .
```

Required artifact:

```
[Step 4] Debug-artifact scan:
  sorry:                <count> — files: <list, or "(none)">
  #check / #print / #eval / #reduce: <count> — locations: <or "(none)">
  set_option (trace/pp/maxHeartbeats/maxRecDepth): <count> — locations: <or "(none)">
  axiom / constant declarations: <count> — locations: <or "(none)">

  Result: <PASS — all counts zero>
          <FAIL — list non-zero categories>
```

**Hard stop on any non-zero count** unless:
- A `set_option linter.* false in <decl>` is the only set_option (acceptable when
  justified with a comment explaining why).
- The user explicitly opts in (e.g., a project that intentionally uses `axiom`).

### Step 5: Axiom Check on Public Declarations (required artifact — this catches hidden sorries)

For every public theorem in the modified files:

```lean
#print axioms decl_name
```

Acceptable axioms: `propext`, `Quot.sound`, `Classical.choice`. Anything else (especially
`sorryAx`) is a defect.

```
[Step 5] Axiom check on public decls:
  Total decls checked: N
  Standard axioms only: M
  Hidden sorryAx found: <count>; decls: <list>
  Other unexpected axioms: <count>; decls: <list>

  Result: <PASS — only standard axioms> / <FAIL — see lists>
```

**Hard stop on any sorryAx.** A `sorryAx` in a "public" theorem means a `have` somewhere
in its proof has `sorry` — a hidden incomplete proof. Find and prove it.

### Step 6: Documentation Review (required artifact)

For each public declaration in modified files:

```
[Step 6] Public-API documentation:
  Total public decls: N
  With docstring (1+ sentence): M
  Missing docstring: <count>; decls: <list>

  Result: <PASS — every public decl documented> / <FAIL — list missing>
```

**Hard stop on missing docstrings** for `theorem` / `def` / `structure` / `class`. Helper
lemmas (`private` / `_aux` suffix) should NOT have docstrings — that's a separate check
already done by `/cleanup` Phase 4.

### Step 7: Final Compilation (required artifact)

```bash
lake build 2>&1 | tee /tmp/pre-submit-build-final.log
```

```
[Step 7] lake build (final): <PASS / FAIL>
```

**Hard stop on FAIL.** This re-checks after Step 2's `/cleanup` may have made changes.

## Output Format (required — every section must appear)

```
## Pre-Submit Check: [project/files]

[Step 1] lake build:                <PASS / FAIL>
[Step 2] /cleanup:                  <PASS-CLEAN / PASS-WITH-CHANGES / FAIL>
[Step 3] runLinter:                 <PASS / PASS-WITH-NOLINT / FAIL>
[Step 4] Debug-artifact scan:       <PASS / FAIL>
[Step 5] Axiom check:               <PASS / FAIL>
[Step 6] Public-API documentation:  <PASS / FAIL>
[Step 7] lake build (final):        <PASS / FAIL>

### ✓ Build Status (Step 1 + 7)
- Compilation: ✓ Successful (initial + final)
- Warnings: 0
- Errors: 0

### ✓ Cleanup Result (Step 2)
- /cleanup Overall: pass
- Issues fixed across phases: <count>
- Simplify-pass outcome: <pass-through / issues-found-and-fixed>

### ✓ File Quality (collected from /cleanup Phase 7 + Step 6)
| File | Lines | Max Line | Header | Docstring (% public) |
|------|-------|----------|--------|----------------------|
| Foo.lean | 234 | 98 | ✓ | 100% |
| Bar.lean | 456 | 95 | ✓ | 100% |

### ✓ Debug-artifact scan (Step 4)
- sorry:               0 found
- #check / #print / #eval: 0 found
- set_option (debug):  0 found
- axiom / constant:    0 found

### ✓ Axiom check (Step 5)
- Public decls inspected: N
- Standard axioms only: N
- sorryAx: 0
- Other unexpected: 0

### ✓ Documentation (Step 6)
- Public declarations: 15
- With docstrings: 15
- Missing: 0

### ✓ Linters (Step 3)
- Errors: 0
- Warnings: 0
- @[nolint] suppressions: <count, with one-line justification per>

### Ready for submission: ✓

---

To submit:
1. Create branch: `git checkout -b feat/foo-bar`
2. Commit changes: `git commit -m "feat(Algebra): add FooBar lemmas"`
3. Push: `git push -u origin feat/foo-bar`
4. Create PR via GitHub
```

### What "ready for submission" means

`Ready for submission: ✓` is printed **only when every step's artifact reports PASS** (or
PASS-WITH-CHANGES / PASS-WITH-NOLINT). A single FAIL elsewhere means the report ends with:

```
### NOT READY FOR SUBMISSION

Failing steps:
- [Step N] <step name>: <one-line reason>

Run /cleanup to fix code-quality issues. Address linter errors. Add missing docstrings.
Re-run /pre-submit when fixed.
```

Required-artifact discipline: if any of the 7 step blocks is missing from the report,
that step wasn't run — that's a `/pre-submit` defect, treat as FAIL on that step.

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
- Issues already captured by earlier `/cleanup` runs
- Standard compilation warnings

**Keep it lightweight** - only 1-3 entries per command run, focusing on lessons for future runs.
