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

For EACH declaration, go through ALL checks below. **Do NOT fix anything yet.**

For each issue found:
- Add a `-- FIXME: [CATEGORY] description` comment **ABOVE** the declaration
- If the change affects OTHER declarations (rename, remove, replace with mathlib), add to the **REFACTORING LIST** instead

#### FIXME Comment Format

```lean
-- FIXME: [LINT] unused variable `hp0_ne_i` — remove from signature and call sites
-- FIXME: [NAMING] rename to `foo_bar` — snake_case for lemmas returning Prop
-- FIXME: [FORMAT] `by` on own line (line 48) — move to end of preceding line
-- FIXME: [GOLF] inline `have h1 := lemma1 x` (line 52) — single-use, no proof block
-- FIXME: [GOLF] try `grind` on lines 54-60 — multi-step case analysis
-- FIXME: [COMMENT] remove inline comments (lines 50-51, 53)
-- FIXME: [VISIBILITY] make `private` — only used within this file
-- FIXME: [STRUCTURE] proof is 45 lines — flag for /decompose-proof
theorem fooBar (x : ℝ) (hp0_ne_i : ...) : ... := by
  ...
```

#### Refactoring List Format

Track these separately (NOT as code comments). Print after auditing all declarations:

```
REFACTORING LIST:
1. RENAME `fooBar` → `foo_bar` — update usages at lines 80, 95, 120
2. REMOVE `def myHelper` (line 40) — duplicates `Mathlib.Foo.bar`. Update sites: 70, 85
3. MATHLIB `def customCondition` (line 15) — replace with `[DiscreteTopology S]`
```

---

#### The Audit Checklist

Print the declaration name before each audit. Check ALL items — do not skip.

**CHECK 0: Lint Warnings**
- List ALL lint warnings from Step 1 within this declaration's line range
- Each becomes `-- FIXME: [LINT] ...`
- Common: unused variables (remove entirely), unused have/suffices, long lines, `$`→`<|`, `λ`→`fun`, `show`→`change`

**CHECK 1: Mathlib-First**
- Could this `def` be replaced by a mathlib definition? Quick search with `exact?` or Loogle
- If yes → add to REFACTORING LIST (affects call sites)
- For simple 1-3 line compositions → note preference for `local notation` or direct mathlib use

**CHECK 2: Naming**
- `lemma`/`theorem` (returns Prop) → must be `snake_case`
- `def` (returns data) → must be `lowerCamelCase`
- `structure`/`inductive` → must be `UpperCamelCase`
- Theorem name should follow `conclusion_of_hypothesis` pattern
- American English (`Factorization` not `Factorisation`)
- If rename needed → add to REFACTORING LIST (must update all usages file-wide)

**CHECK 3: Unused Variables**
- Parameters with unused lint warnings → `-- FIXME: [LINT] unused variable 'x' — remove from signature and all call sites`
- Do NOT prefix with `_` — remove entirely

**CHECK 4: Formatting**
- 2-space indentation in tactic blocks
- `by` at end of preceding line, never alone on its own line
- `fun` over `λ`, `<|` over `$`
- Proper whitespace around operators and colons
- No empty lines inside declarations
- Each issue → `-- FIXME: [FORMAT] ...`

**CHECK 4b: Line Length — MAXIMIZE to 100 chars (CRITICAL)**

Lines must be ≤100 chars, but equally important: **fill lines to ~100 chars**. Do NOT break lines at 50-60 characters when there is room. Short lines waste vertical space.

Flag lines that break too early:
- **Signatures**: Multiple parameters should be on the same line until ~100 chars
  `-- FIXME: [FORMAT] pack parameters onto fewer lines — currently breaking at ~60 chars`
- **`simp only` lists**: Pack lemma names to fill the line, not 2-3 per line
  `-- FIXME: [FORMAT] pack simp list to fill lines to ~100 chars`
- **Expressions**: Keep `have`, `rw`, `show` expressions on one line when they fit
  `-- FIXME: [FORMAT] expression fits on one line — remove unnecessary line breaks`
- **Return types**: Keep conclusion on `:` line when it fits
  `-- FIXME: [FORMAT] return type fits on signature line — merge`

Example of what to flag:
```lean
-- BAD: breaks at ~50 chars, wastes 5 lines
  simp only [ne_eq, mul_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true,
    ofReal_eq_zero, Real.pi_ne_zero,
    I_ne_zero, or_self]
-- Should be 2 lines:
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
    Real.pi_ne_zero, I_ne_zero, or_self]

-- BAD: one parameter per line when they fit together
theorem foo
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
-- Should be:
theorem foo (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ...) :
```

**CHECK 5: Comments & Docstrings**
- Any inline comments in proofs → `-- FIXME: [COMMENT] remove inline comments`
- Commented-out code → `-- FIXME: [COMMENT] remove commented-out code`
- Section markers (`/-! ## ... -/`) → `-- FIXME: [COMMENT] remove section marker`
- Missing docstring on important public theorem/def → `-- FIXME: [COMMENT] add one-sentence docstring`
- Docstring on helper/private lemma → `-- FIXME: [COMMENT] remove docstring from helper`
- Verbose multi-paragraph docstring → `-- FIXME: [COMMENT] shorten docstring to one sentence`

**CHECK 6: Proof Structure** (flag for `/decompose-proof`, don't fix here)
- `set_option maxHeartbeats` → `-- FIXME: [STRUCTURE] remove maxHeartbeats — decompose proof instead`
- Proof >30 lines → `-- FIXME: [STRUCTURE] proof is N lines — needs /decompose-proof`
- `∧` in theorem statement → `-- FIXME: [STRUCTURE] split ∧ into separate lemmas`
- Any constructor/by_cases/rcases branch >10 lines → `-- FIXME: [STRUCTURE] branch (lines X-Y) >10 lines — extract to helper`

**CHECK 7: Proof Golf**

Go through the proof line by line. For each golfing opportunity:

- Single-use `have foo := bar` (no `by`) → `-- FIXME: [GOLF] inline have 'foo' (line N) — single-use, no proof block`
- Single-use `have foo : T := bar` (no `by`) → same
- `by exact h` → `-- FIXME: [GOLF] 'by exact h' → 'h' (line N)`
- `by rfl` → `-- FIXME: [GOLF] 'by rfl' → 'rfl' (line N)`
- `fun x => f x` → `-- FIXME: [GOLF] eta-reduce (line N)`
- `rw [...]; exact h` → `-- FIXME: [GOLF] use rwa (line N)`
- `simp; exact h` → `-- FIXME: [GOLF] use simpa (line N)`
- `constructor; exact a; exact b` → `-- FIXME: [GOLF] use ⟨a, b⟩ (line N)`
- `intro h; exact f h` → `-- FIXME: [GOLF] eta-reduce to f (line N)`
- Consecutive `rw` → `-- FIXME: [GOLF] merge rw calls (lines N-M)`
- Multi-step tactic block that automation might close → `-- FIXME: [GOLF] try grind/fun_prop/omega on lines N-M`
- Redundant tactic → `-- FIXME: [GOLF] redundant tactic (line N)`
- Trailing comma in simp list → `-- FIXME: [GOLF] trailing comma (line N)`

**`have` inlining decision tree:**
1. `have h := bar` (no type, no `by`) → **INLINE** unless used 2+ times
2. `have h : T := bar` (typed, no `by`) → **INLINE** unless used 2+ times
3. `have h := by ...` or `have h : T := by ...` → **KEEP** (has proof content)
4. Any `have` used 2+ times → **KEEP**

**CHECK 8: Visibility**
- Only used within this file → `-- FIXME: [VISIBILITY] make private`
- Helper for one result → `-- FIXME: [VISIBILITY] make private, add _aux suffix`
- Already private but missing `_aux` suffix → `-- FIXME: [VISIBILITY] add _aux suffix`

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
