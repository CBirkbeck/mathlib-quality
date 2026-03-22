---
name: cleanup
description: Full file cleanup to mathlib standards
---

# /cleanup - Full File Cleanup (Two-Pass Architecture)

Combined cleanup + golfing with systematic annotation-then-fix approach.

## Usage

```
/cleanup [file_path]
```

If no file is specified, operates on the currently open file.

## Architecture

**Problem**: Agents forget or skip issues when auditing and fixing simultaneously.

**Solution**: Separate annotation from implementation:
1. **Pass 1 (Audit)**: Go declaration by declaration. Check EVERY rule. Annotate with `-- FIXME:` comments. **Do NOT fix anything.**
2. **Pass 2 (Fix)**: Dispatch parallel agents, each handling a batch of declarations. They implement the FIXME fixes and remove the comments.
3. **Pass 3 (Refactor)**: Handle cross-cutting changes (renames, removals) from the refactoring list.

---

## ⚠️ CRITICAL: Two-Pass Enforcement

**Pass 1 is AUDIT ONLY.** You MUST complete the full audit of ALL declarations before making ANY changes to the code (other than adding FIXME comments and fixing the header).

**DO NOT:**
- Fix a bug you notice while auditing — add a FIXME instead
- Golf a proof while reading it — add a FIXME instead
- Rename anything while auditing — add to REFACTORING LIST instead
- "Quickly fix" a formatting issue — add a FIXME instead

**The ONLY changes allowed during Pass 1 are:**
- Adding `-- FIXME:` comment lines above declarations
- Fixing the file header (Step 2)

If you catch yourself about to edit non-comment code during Pass 1, STOP. Add a FIXME comment instead.

**After Pass 1 completes**, you must print the full Audit Summary and REFACTORING LIST, then proceed to Pass 2.

---

## Pass 1: Audit

### Step 1: Collect Lint Diagnostics

**Before doing anything else**, run `lean_diagnostic_messages` on the file.

```
lean_diagnostic_messages(file_path="/path/to/File.lean")
```

**Group warnings by line number** and print a summary:

```
## Lint Diagnostics for File.lean

### Errors (must fix)
- l45: type mismatch...

### Warnings (fix all)
- l12: unused variable `hp0_ne_i` [linter.unusedVariables]
- l34: line has 115 characters [style.longLine]
- l56: `$` is not allowed, use `<|` [style.dollarSyntax]
```

**Common linter warnings:**
| Linter | Fix |
|--------|-----|
| `unusedVariables` | Remove parameter entirely (NOT underscore) |
| `unusedHavesSuffices` | Remove or inline |
| `style.longLine` | Break line |
| `style.dollarSyntax` | Replace `$` with `<|` |
| `style.lambdaSyntax` | Replace `λ` with `fun` |
| `style.setOption` | Decompose proof instead |
| `style.cdot` | Fix `·` formatting |
| `style.show` | Replace `show` with `change` |
| `docBlame` | Add one-sentence docstring |

### Step 2: Header Cleanup (Fix Immediately)

These are file-level, fix them now without annotation:

1. **Copyright header** — proper format
2. **Imports** — alphabetical, remove unused
3. **Module docstring** — add or improve (one at TOP of file only)

### Step 3: Build Declaration List

Extract every declaration into an ordered list:

```
1. def myFoo (line 25, 15 lines)
2. lemma bar_thing (line 40, 8 lines)
3. theorem main_result (line 65, 45 lines)
...
```

Print this list. This is your audit roadmap.

### Step 4: Audit Each Declaration (THE CORE LOOP)

For EACH declaration, run through the mandatory audit procedure below.

**Do NOT fix anything.** Only add `-- FIXME:` comments and REFACTORING LIST entries.

**You MUST print the structured audit report for each declaration.** This is not optional. The report forces you to actually check each item. If you skip the report, you will miss issues.

---

#### Per-Declaration Audit Procedure

For every declaration, print a report in EXACTLY this format. Every line MUST have an answer — either the issues found or "OK".

```
### Auditing: `declaration_name` (lines N-M, K lines)

1. LINT WARNINGS: [list each warning from Step 1 in this range, or "none"]
2. HAVE SCAN: [list EVERY `have` in the proof — see detailed procedure below, or "no haves"]
3. NAMING: [OK / needs rename to `X` — reason]
4. LINE PACKING: [list lines that break too early, or "all lines filled to ~100"]
5. BY PLACEMENT: [list any `by` on own line, or "OK"]
6. FORMAT OTHER: [λ→fun, $→<|, show→change, empty lines, indentation, or "OK"]
7. COMMENTS: [list inline comments/section markers, or "clean"]
8. DOCSTRING: [needs adding / needs removing / needs shortening / "OK"]
9. TERM MODE: [list `by exact`, `by rfl`, eta-reducible, or "none"]
10. AUTOMATION: [list multi-step blocks where grind/fun_prop/omega might work, or "none spotted"]
11. VISIBILITY: [should be private / needs _aux / "OK"]
12. STRUCTURE: [proof length, ∧ in statement, branches >10 lines, maxHeartbeats, or "OK"]
13. MATHLIB: [could replace with mathlib? / "checked, no replacement"]

FIXMEs to add: [numbered list of all FIXME comments to add above this declaration]
REFACTORING: [any items for the refactoring list, or "none"]
```

After printing this report, add ALL listed FIXME comments above the declaration in the file.

---

#### Item 2: HAVE SCAN (Most Commonly Missed — Do This Carefully)

**This is the #1 most skipped check. You MUST do it for every declaration.**

For each `have` statement in the proof, you must explicitly list it and classify it:

```
2. HAVE SCAN:
   - line 52: `have h1 := lemma1 x` — NO by, used 1x at line 55 → INLINE
   - line 53: `have h2 : T := foo y` — NO by, used 1x at line 58 → INLINE
   - line 55: `have h3 := by exact bar` — HAS by → KEEP
   - line 60: `have h4 := baz z` — NO by, used 2x at lines 62,65 → KEEP (multi-use)
   - line 63: `have h5 : T := by linarith` — HAS by → KEEP
```

**Classification rules (apply mechanically):**

| Pattern | Has `by`? | Used how many times? | Action |
|---------|-----------|---------------------|--------|
| `have h := expr` | NO | 1 | **INLINE** → FIXME |
| `have h : T := expr` | NO | 1 | **INLINE** → FIXME |
| `have h := expr` | NO | 2+ | KEEP |
| `have h := by ...` | YES | any | KEEP |
| `have h : T := by ...` | YES | any | KEEP |
| `haveI ...` | — | — | KEEP (instance) |

**How to check usage count**: Search for the variable name in the rest of the proof. Count occurrences after the `have` line. If it appears exactly once → INLINE.

**FIXME format for each inlinable have:**
```
-- FIXME: [GOLF] inline `have h1 := lemma1 x` (line 52) — single-use, replace `h1` with `lemma1 x` at line 55
```

---

#### Item 4: LINE PACKING (Second Most Commonly Missed)

**Lines must fill to ~100 characters. Do NOT break lines at 50-60 chars when there is room.**

Check each of these:

**Signatures**: Can parameters be packed onto fewer lines?
```lean
-- BAD: 4 lines at ~40 chars each
theorem foo
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
-- GOOD: 2 lines at ~90 chars each
theorem foo (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
```

**`simp only` / `rw` lists**: Can lemma names be packed tighter?
```lean
-- BAD: 4 lines at ~40 chars
  simp only [ne_eq, mul_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true,
    ofReal_eq_zero, Real.pi_ne_zero,
    I_ne_zero, or_self]
-- GOOD: 2 lines at ~90 chars
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
    Real.pi_ne_zero, I_ne_zero, or_self]
```

**Expressions**: Can `have`, `rw [show ...]`, etc. fit on fewer lines?

**Return types**: Does the conclusion fit on the `:` line?

For each line that breaks too early:
```
-- FIXME: [FORMAT] pack lines N-M to fill to ~100 chars (currently ~55 chars)
```

---

#### Items 3, 5-13: Remaining Checks

**3. NAMING**: lemma/theorem→`snake_case`, def→`lowerCamelCase`, structure→`UpperCamelCase`. Follow `conclusion_of_hypothesis`. If rename needed → REFACTORING LIST.

**5. BY PLACEMENT**: `by` must be at end of preceding line, never alone. Each violation → `-- FIXME: [FORMAT] ...`

**6. FORMAT OTHER**: `fun` over `λ`, `<|` over `$`, `change` over `show`, 2-space indent, no empty lines inside declarations.

**7. COMMENTS**: Remove ALL inline comments in proofs. No commented-out code. No section markers.

**8. DOCSTRING**: Public theorem/def needs ONE-SENTENCE docstring. Private/helper needs NO docstring. Verbose docstrings need shortening.

**9. TERM MODE**: `by exact h` → `h`. `by rfl` → `rfl`. `fun x => f x` → `f`. `constructor; exact a; exact b` → `⟨a, b⟩`.

**10. AUTOMATION**: Could `grind`, `fun_prop`, `omega`, `ring`, `aesop` close any multi-step block? `rw [...]; exact h` → `rwa`. `simp; exact h` → `simpa using h`. Consecutive `rw` → merge.

**11. VISIBILITY**: Only used in file → `private`. Helper → `private` + `_aux`.

**12. STRUCTURE**: Proof >30 lines → flag for `/decompose-proof`. `∧` in statement → split. Branch >10 lines → extract. `set_option maxHeartbeats` → decompose instead.

**13. MATHLIB**: Could this def/lemma be replaced by mathlib? If so → REFACTORING LIST.

---

#### FIXME Comment Syntax

```lean
-- FIXME: [CATEGORY] description
```

Categories: `LINT`, `GOLF`, `FORMAT`, `COMMENT`, `VISIBILITY`, `STRUCTURE`

Cross-cutting changes go to REFACTORING LIST instead (renames, removals, mathlib replacements).

```
REFACTORING LIST:
1. RENAME `fooBar` → `foo_bar` — update usages at lines 80, 95, 120
2. REMOVE `def myHelper` (line 40) — duplicates `Mathlib.Foo.bar`. Update sites: 70, 85
```

---

### Step 5: Print Audit Summary

After auditing ALL declarations:

```
## Audit Summary for [filename]

### FIXME Comments Added
| Declaration | Line | Issues |
|-------------|------|--------|
| `fooBar` | 25 | LINT, GOLF×2, COMMENT |
| `main_theorem` | 65 | STRUCTURE, GOLF×3, FORMAT |
| `small_helper` | 90 | VISIBILITY |
| ... | ... | ... |

Total: N issues across M declarations

### REFACTORING LIST
1. RENAME `fooBar` → `foo_bar` — update usages at lines 80, 95, 120
2. REMOVE `def myHelper` (line 40) — duplicates `Mathlib.Foo.bar`. Call sites: 70, 85
3. MATHLIB `def customCond` (line 15) — replace with `[DiscreteTopology S]`. Sites: 55, 130

### Declarations with No Issues
- `clean_lemma` (line 100) ✓
- `another_clean` (line 115) ✓
```

**Ask the user to confirm before proceeding to Pass 2.** Show them the audit and refactoring list. They may want to adjust priorities or skip some items.

---

## Pass 2: Fix (Parallel Agents)

### Grouping Strategy

Group annotated declarations into batches of 3-5 declarations. Each batch should:
- Contain declarations that are **close together** in the file (minimize context needed)
- **NOT** include declarations involved in REFACTORING LIST items (those are handled in Pass 3)
- **NOT** span declarations with interdependencies (if B calls A, put them in the same batch with A first)

Skip declarations with ONLY `[STRUCTURE]` issues — those are handled by `/decompose-proof`.

### Dispatching Fix Agents

For each batch, dispatch an agent using the `Agent` tool. Use `subagent_type="general-purpose"`.

**Agent prompt template:**

```
Fix FIXME-annotated declarations in [file_path].

Read the file. Your batch covers lines [start_line] to [end_line], containing these declarations:
- `decl_1` (line N): [LINT] unused var, [GOLF] inline have, [COMMENT] remove comments
- `decl_2` (line M): [FORMAT] by placement, [GOLF] try grind
- `decl_3` (line P): [VISIBILITY] make private

For EACH `-- FIXME:` comment in your range:
1. Implement the fix exactly as described
2. Delete the FIXME comment line after implementing the fix
3. For [GOLF] items involving automation (grind, fun_prop, omega): test with lean_multi_attempt before committing
4. After fixing ALL items on a declaration, run lean_diagnostic_messages to verify no new errors

Rules:
- Remove unused variables from BOTH the signature AND all call sites within the file
- When inlining `have`, verify it's truly single-use by searching for the variable name
- When trying automation, if it fails silently move on — don't force it
- Do NOT touch declarations outside your line range
- Do NOT handle any REFACTORING LIST items
- Do NOT try to fix [STRUCTURE] items — those are for /decompose-proof
- Leave [STRUCTURE] FIXME comments in place
```

**Dispatch all batches in parallel** using multiple Agent tool calls in a single message. The batches are independent by construction so they won't conflict.

### Collecting Results

Wait for all agents to complete. Check:
- Any compilation errors introduced → fix them directly
- Any FIXME comments that agents couldn't resolve → note for user
- Verify no non-STRUCTURE FIXME comments remain

---

## Pass 3: Refactoring

Work through the REFACTORING LIST one item at a time. These are cross-cutting changes that affect multiple declarations.

**Priority order:**
1. **MATHLIB replacements** — remove defs that duplicate mathlib, replace with type classes
2. **REMOVE** — delete unnecessary declarations, update call sites
3. **RENAME** — rename + update all usages

For EACH item:
1. Make the change
2. Find and update ALL affected call sites (use Grep to find usages)
3. Run `lean_diagnostic_messages` to verify
4. Fix any errors before moving to next item

**For renames:** Use `replace_all: true` in the Edit tool to rename across the file in one shot.

---

## Pass 4: Final Verification

1. Run `lean_diagnostic_messages` on the full file
2. Compare with Step 1 diagnostics — all original warnings should be resolved
3. Grep for remaining `-- FIXME:` comments:
   - `[STRUCTURE]` comments should remain (for `/decompose-proof`)
   - All other FIXME comments should be gone
4. If new issues appeared, fix them directly

---

## Output Format

```
## Cleanup Report for [filename]

### Pass 1: Audit
- Declarations audited: N
- Issues found: M (LINT: a, NAMING: b, FORMAT: c, GOLF: d, COMMENT: e, VISIBILITY: f, STRUCTURE: g)
- Refactoring items: R

### Pass 2: Fixes Applied
- Agent batches dispatched: B
- Issues resolved: M
- By category: LINT(a), FORMAT(c), GOLF(d), COMMENT(e), VISIBILITY(f)

### Pass 3: Refactoring
- Renames: [old → new, ...]
- Mathlib replacements: [removed → mathlib, ...]
- Removals: [what was removed]

### Pass 4: Verification
✓ File compiles without errors
✓ No non-STRUCTURE FIXME comments remaining
✓ Original lint warnings resolved

### Remaining for /decompose-proof
- `theorem_X` (line N): 45 lines, needs decomposition
- `theorem_Y` (line M): ∧ in statement, needs splitting

### Summary
| Change Type | Count |
|-------------|-------|
| Lint fixes | a |
| Names fixed | b |
| Formatting fixes | c |
| Proofs golfed | d |
| Comments removed | e |
| Visibility changes | f |
| Mathlib replacements | g |
```

---

## Reference

For the complete rules applied during auditing:
- `skills/mathlib-quality/SKILL.md` — comprehensive style reference
- `skills/mathlib-quality/references/naming-conventions.md` — full naming guide
- `skills/mathlib-quality/references/style-rules.md` — formatting rules
- `skills/mathlib-quality/references/proof-patterns.md` — golf patterns
- `skills/mathlib-quality/references/mathlib-quality-principles.md` — core principles from PR analysis

For golf pattern examples:
- `skills/mathlib-quality/examples/inline_have.md` — 77 have-inlining examples
- `skills/mathlib-quality/examples/term_mode.md` — 311 term mode conversions
- `skills/mathlib-quality/examples/simp_golf.md` — 311 simp simplifications
- `skills/mathlib-quality/examples/automation.md` — 1144 automation examples

---

## Learnings

After completing all passes, record significant learnings to `.mathlib-quality/learnings.jsonl` (create if needed).

**What to capture** (1-5 entries per run):
- Non-trivial golf patterns (before/after with technique)
- Mathlib discoveries that replaced custom code
- Naming corrections with reasoning
- User rejections or corrections

**What NOT to capture:**
- Trivial whitespace/formatting fixes
- Mechanical `by exact → term` conversions
- Import reordering

See `skills/mathlib-quality/learning/schema.md` for the JSON schema.
