---
name: cleanup
description: Full file cleanup to mathlib standards
---

# /cleanup - Cleanup + Golf

Audit and fix every declaration against mathlib standards, then apply golfing rules.
Works on a whole file or a single declaration.

## Usage

```
/cleanup [file_path]                -- clean entire file
/cleanup [file_path] [decl_name]    -- clean one declaration
```

---

## Mode: Single Declaration

When given a specific declaration name, skip file-wide setup and go straight to
per-declaration work on just that one proof:

1. Read the file, find the declaration
2. Run `lean_diagnostic_messages` on the file
3. Do the full audit + golf (steps A–D below) on that declaration
4. Verify compilation
5. Print the before/after report

---

## Mode: Full File

### Step 1: Setup (Main Agent)

#### 1a: Collect Lint Diagnostics

Run `lean_diagnostic_messages` on the file. Group warnings by line number and print.

#### 1b: Header Cleanup

Fix file-level issues now: copyright header, import order, module docstring.

#### 1c: Batch Mechanical Replacements (Do This BEFORE Per-Declaration Work)

**Do all global find-replace operations in ONE pass, using `Edit` with `replace_all: true`.**
Do NOT do these one at a time during per-declaration audits — they get reverted by the LSP
rebuilding the file between edits.

Run these replacements on the ENTIRE file in sequence:

1. `show` → `change` (in tactic mode — be careful not to replace `show` in term mode)
2. `λ` → `fun` (if any remain after linter)
3. `$` → `<|` (if any remain after linter)

**Procedure:**
```
1. Read the file
2. For each replacement: use Edit with replace_all: true
3. After ALL replacements are done: run lean_diagnostic_messages ONCE
4. Fix any compilation errors from the replacements
5. Do NOT run lean_diagnostic_messages between individual replacements
```

**Why batch?** The Lean LSP rebuilds the file after each edit. If you make 312 individual
`show→change` replacements with diagnostic checks between each one, the rebuilds can interfere
with pending edits. Doing them all at once avoids this.

**For `show` → `change` specifically:**
- Only replace in tactic mode (after `by`, inside tactic blocks)
- Do NOT replace `show` in term mode or in docstrings
- If unsure, grep for `show` and check each occurrence before bulk replacing
- Use a pattern like: replace `\n  show ` with `\n  change ` (with leading whitespace + newline
  to avoid term-mode `show`)

#### 1d: Build Declaration List

List every declaration with line numbers and proof length:

```
1. def myFoo (lines 25-35, 10 lines)
2. lemma bar_thing (lines 40-52, 12 lines)
3. theorem main_result (lines 65-130, 65 lines)
...
```

---

### Step 2: Process Declarations One By One

**One declaration per agent.** Each declaration gets its own dedicated agent with full
focus. Do NOT batch multiple declarations — the agent should think deeply about finding
the cleanest possible proof for each one.

Dispatch each declaration as a worker agent using the `Agent` tool with
`subagent_type="general-purpose"`. Multiple agents can run in parallel if the
declarations don't depend on each other.

**Include the FULL worker prompt below in each agent dispatch.** Do not abbreviate or
summarize — the workers need the actual rules.

---

## Per-Declaration Procedure (used by both modes)

### Worker Agent Prompt

```
You are cleaning up a SINGLE Lean 4 declaration in [file_path].

**Your entire job is this one declaration. Give it your full attention.**
Think deeply about the cleanest, shortest proof possible. The goal is to
minimize the number of tactics — ideally find a one-liner or term-mode proof.

Lint diagnostics for this file:
[paste the lint warnings from Step 1a]

Your declaration:
- `decl_name` (lines N-M)

## DO EXACTLY THIS:

### A. Print the audit report

You MUST print this report. Every item MUST have an answer.

```
### Auditing: `decl_name` (lines N-M, K lines)

1. LINT: [warnings in this range from diagnostics, or "none"]
2. HAVE SCAN: [see procedure below — list EVERY have]
3. SET_OPTION: [any `set_option maxHeartbeats` / `set_option maxRecDepth`? — MUST remove]
4. SIMP SQUEEZE: [any bare `simp`? any badly formatted `simp only`? — use simp?]
5. NAMING: [OK / rename to X — reason]
6. LINE PACKING: [lines breaking too early? use #check as reference — see below]
7. BY PLACEMENT: [any `by` on own line, or "OK"]
8. FORMAT: [indent, empty lines, other formatting, or "OK"]
9. COMMENTS: [inline comments in proof, or "clean"]
10. DOCSTRING: [needs adding/removing/shortening, or "OK"]
11. VISIBILITY: [should be private / needs _aux, or "OK"]
12. STRUCTURE: [proof length, ∧ in statement, branches >10 lines — attempt fix]
13. MATHLIB: [could replace with mathlib, or "no replacement found"]

Issues to fix: [numbered list — every issue MUST have a concrete action, not "flag for later"]
Refactoring needed: [cross-declaration changes, or "none"]
```

### B. Deep golf

Now focus completely on making this proof as clean and short as possible.
Read the proof carefully. Understand what it's doing mathematically. Then
ask: what is the SHORTEST way to express this?

Try to find a one-liner or term-mode proof first. If that fails, minimize
tactics systematically using the rules below.

#### Instant wins (always apply if pattern matches):
- `:= by exact term` → `:= term`
- `:= by rfl` → `:= rfl`
- `rw [h]; exact e` → `rwa [h]`
- `simp [...]; exact h` → `simpa [...] using h`
- `simp [...]; rfl` → just `simp [...]`
- `constructor; · exact a; · exact b` → `exact ⟨a, b⟩`
- `apply f; exact h` → `exact f h`
- `by_contra h; push_neg at h` → `by_contra! h`
- `fun x => f x` → `f` (eta-reduce)
- Single-use `have h := x; ... h` → inline `x` at use site
- `apply X; intro y` → `refine X fun y => ?_`
- Redundant `show T` when goal is already `T` → remove
- `have h := ...; ... h.1 ... h.2` → `obtain ⟨a, b⟩ := ...`
- Consecutive `rw [a]; rw [b]` → `rw [a, b]`
- Terminal `simp only [...]` → unsqueeze to `simp` (don't squeeze terminal simp!)
- Nonterminal bare `simp` → squeeze to `simp only [...]` via `simp?`
- Use dot notation: `Monotone.comp hf hg` → `hf.comp hg`
- Use `<|` to avoid trailing parens: `f (by simp)` → `f <| by simp`

#### Automation upgrades (try each, keep if it compiles):
For multi-line tactic blocks, try replacing with automation. Use `lean_multi_attempt`:
1. `grind` / `grind [relevant_lemmas]` on the whole proof
2. Delete tactics before `grind` — it often subsumes preceding steps
3. `fun_prop` / `fun_prop (disch := grind)` for Continuous/Differentiable/Measurable goals
4. `positivity` for `0 < x`, `0 ≤ x` goals
5. `gcongr` for inequality congruence in calc blocks
6. `omega` / `lia` for Nat/Int arithmetic (prefer `lia`)
7. `aesop` for logic/membership/simple structure goals
8. `norm_num` / `norm_cast` for numeric/cast goals
9. `decide` / `decide +kernel` for decidable propositions
10. `field_simp; ring` for denominator equalities
11. `linear_combination` for ring goals with hypotheses in context
12. `wlog` when two case branches are symmetric
13. Collapse 2-step `calc` to `le_trans h1 h2` etc.
14. `refine ⟨?_, ?_⟩ <;> grind [...]` for multiple similar goals

#### Cleanup:
- `erw` → try `rw` first
- `continuity`/`measurability` → `fun_prop`
- `omega` → `lia` in new code
- `simp_all only` → `simp_all` for closing goals
- Remove `set_option maxHeartbeats` (never acceptable — fix the proof)

#### Step back and think:
After applying mechanical rules, look at the proof again holistically:
- Can the ENTIRE proof be replaced by a single tactic? (`grind`, `simp`, `aesop`, `decide`)
- Can you find a better mathlib lemma that makes the proof trivial?
- Is there a term-mode proof that's shorter than the tactic proof?
- Can `have` blocks be composed into a single expression?
- Are there redundant steps that don't actually change the goal?
- Would a completely different proof strategy be shorter?

**Try `exact?` or `apply?`** if you're stuck — they might find a one-liner you missed.

### C. Verify compilation

Run `lean_diagnostic_messages` after applying all changes. Fix any breakage.

### D. Report

Print before/after line counts. Note any refactoring needed for other declarations.
```

Dispatch all declaration agents. Multiple can run in parallel if declarations are independent.

---

## Detailed Procedures

### HAVE SCAN (Do This Carefully)

For EVERY `have` in the proof, list it and classify:

```
2. HAVE SCAN:
   - L52: `have h1 := lemma1 x` — no by, used 1x at L55 → INLINE
   - L53: `have h2 : T := foo y` — no by, used 1x at L58 → INLINE
   - L55: `have h3 := by linarith` — has by → KEEP
   - L60: `have h4 := baz z` — no by, used 2x at L62,65 → KEEP
```

Rules:
| Pattern | Has by? | Uses | Action |
|---------|---------|------|--------|
| `have h := expr` | NO | 1 | INLINE — replace h with expr at use site |
| `have h : T := expr` | NO | 1 | INLINE — replace h with expr at use site |
| `have h := expr` | NO | 2+ | KEEP |
| `have h := by ...` | YES | any | KEEP |
| `have h : T := by ...` | YES | any | KEEP |

To inline: delete the have line, substitute the RHS where h was used.

### LINE PACKING (Use Lean's Formatting As Guide)

**Fill lines to ~100 chars. Do NOT break at 50-60 chars.**

Use `#check @theorem_name` to see how Lean formats the type, and match that compactness.

```lean
-- BAD: breaks lines way too early (~40 chars each)
theorem foo
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :

-- GOOD: fills to ~100 chars
theorem foo (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
```

**Packing rules for signatures:**
- Put as many parameters on each line as fit within ~100 chars
- Break BETWEEN `)(` parameter boundaries, not within parameters
- Continuation lines indent 4 spaces
- Return type on `:` line if it fits, otherwise next line indented 4

### SET_OPTION (MUST Remove)

**`set_option maxHeartbeats` and `set_option maxRecDepth` are NOT acceptable in mathlib.**

If you find one:
1. Delete the `set_option` line
2. Run `lean_diagnostic_messages` — if the proof now times out:
   a. Try `grind` or other automation on the proof (use lean_multi_attempt)
   b. Try inlining haves and simplifying first (often reduces heartbeats enough)
   c. If still timing out: extract the largest `have` blocks (>8 lines) into private helper
      lemmas above the theorem — this splits the elaboration work
   d. If STILL timing out after extraction: report as "needs /decompose-proof" but
      the `set_option` line must STILL be deleted — do not leave it in
3. The `set_option` line must be gone when you're done. No exceptions.

### SIMP SQUEEZE (Use simp? — Do Not Manually Format)

**Do NOT manually arrange `simp only` lemma lists. Use `simp?` and apply its suggestion.**

For each `simp` call in the proof:

**A. Bare `simp` (no `only`) — non-terminal:**
Non-terminal `simp` without `only` is NOT allowed in mathlib. MUST squeeze.
1. Temporarily replace `simp` with `simp?` in the file
2. Run `lean_diagnostic_messages` — look for info message "Try this: simp only [...]"
3. Replace `simp?` with the suggestion exactly as formatted
4. Verify compilation

**B. Bare `simp` — terminal (closing the goal):**
Terminal `simp` is acceptable. Do NOT squeeze it. Check if `grind` or `simp_all` is shorter.

**C. Existing `simp only [...]` with bad formatting:**
1. Temporarily replace `simp only [...]` with `simp?`
2. Run `lean_diagnostic_messages` to get the suggestion
3. Replace with the suggestion — it will have correct formatting

### REMAINING ITEMS (Quick Reference)

5. NAMING: lemma/theorem→snake_case, def→lowerCamelCase, structure→UpperCamelCase.
   conclusion_of_hypothesis pattern. American English.
7. BY PLACEMENT: `by` at end of preceding line, NEVER alone on own line.
8. FORMAT: 2-space indent, no empty lines in decls.
9. COMMENTS: Remove ALL inline comments from proofs. No commented-out code.
10. DOCSTRING: Public theorem/def → one sentence. Private/helper → none.
11. VISIBILITY: Only used in file → private. Helper → private + _aux.

### STRUCTURE (Attempt Fixes, Don't Just Flag)

**Do NOT just write "flag for later." Attempt the fix.**

- **Proof >30 lines**: After applying all golfing, if still >30 lines, extract the largest
  `have ... := by` blocks as private helpers above the theorem.
- **∧ in theorem statement**: Split into `foo_left` and `foo_right` lemmas, combine with `⟨foo_left, foo_right⟩`.
- **Branch >10 lines** (constructor/by_cases/rcases): Extract each branch as a private helper lemma.

---

## Step 3: Refactoring (Main Agent, full-file mode only)

After all workers complete, collect their "Refactoring needed" items.

Work through them one at a time:
1. Make the change
2. Update ALL affected call sites (use Grep)
3. Verify with `lean_diagnostic_messages`

Priority: mathlib replacements > removals > renames.

---

## Step 4: Final Verification (Main Agent)

1. Run `lean_diagnostic_messages` — should be clean
2. Check for any remaining `-- FIXME:` comments (only `[STRUCTURE]` should remain)

---

## Output Format

```
## Cleanup Report for [filename]

### Declarations Processed: M total

### Per-Declaration Results
| Declaration | Issues Found | Fixed | Skipped |
|-------------|-------------|-------|---------|
| `foo_bar` | 5 | 5 | 0 |
| `main_thm` | 3 | 2 | 1 (grind failed) |

### Refactoring Completed
- Renamed: [list]
- Removed: [list]
- Mathlib replaced: [list]

### Verification
✓ File compiles without errors
✓ No remaining FIXME comments (except STRUCTURE)

### Flagged for /decompose-proof
- `theorem_X` (line N): 45 lines
```

---

## Reference

- `skills/mathlib-quality/references/golfing-rules.md` — full golfing rules checklist
- `skills/mathlib-quality/references/proof-patterns.md` — data-driven patterns from 7,273 PR suggestions
- `skills/mathlib-quality/references/` — naming, style rules

## Learnings

After completing, record significant learnings to `.mathlib-quality/learnings.jsonl`.
Only capture non-trivial patterns (1-5 entries). See `skills/mathlib-quality/learning/schema.md`.
