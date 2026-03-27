---
name: cleanup-all
description: Run /cleanup on every file in the project, tracked file by file
---

# /cleanup-all - Project-Wide Cleanup

Run the full `/cleanup` procedure on every `.lean` file in the project. Each file gets its own
dedicated agent so nothing is skipped.

## Usage

```
/cleanup-all [directory]
```

If no argument, processes all `.lean` files (excluding `.lake/`, `build/`).

---

## Why This Command Exists

When told "run /cleanup on all files," agents:
- Skip files (especially later ones as they get tired)
- Rush through files without doing the full 15-item audit
- Lose context and forget rules after processing a few files

This command fixes that by giving EACH FILE its own dedicated agent with the full rules.

---

## Procedure

### Step 1: Enumerate All Files

Find every `.lean` file:

```bash
find [directory] -name "*.lean" -not -path "./.lake/*" -not -path "./build/*" | sort
```

Print the full file list with line counts:

```
## Files to Clean (N total)

| # | File | Lines | Status |
|---|------|-------|--------|
| 1 | Foo/Bar.lean | 450 | pending |
| 2 | Foo/Baz.lean | 200 | pending |
| 3 | Helpers.lean | 800 | pending |
| ... | ... | ... | ... |
```

**Ask the user to confirm the file list before proceeding.** They may want to skip certain files
or prioritize specific ones.

### Step 2: Process Files One By One

**Process files sequentially, ONE AT A TIME.** Do not try to do multiple files in parallel —
each file needs full attention.

For each file:

#### 2a: Announce the file

```
## Processing file 3/N: Helpers.lean (800 lines)
```

#### 2b: Dispatch a dedicated cleanup agent

Dispatch an agent using the `Agent` tool with `subagent_type="general-purpose"`.

**The agent prompt MUST include the FULL cleanup worker instructions.** Read the contents of
`commands/cleanup.md` — find the worker prompt section (starting with "Your declarations") and
include it verbatim. Do NOT summarize or abbreviate the rules.

**Agent prompt structure:**

```
You are running /cleanup on [file_path]. This is file [X] of [N] in a project-wide cleanup.

IMPORTANT: This file gets your FULL attention. Do not rush. Do every check on every declaration.

Step 1: Run lean_diagnostic_messages on the file. Print all warnings.

Step 2: Fix the file header (copyright, imports, module docstring).

Step 3: List every declaration with line numbers.

Step 4: For EACH declaration, do the following:

  A. Print the mandatory 15-item audit report:

  ### Auditing: `decl_name` (lines N-M, K lines)

  1. LINT: [warnings or "none"]
  2. HAVE SCAN: [list EVERY have — classify as INLINE or KEEP]
  3. SET_OPTION: [any set_option? MUST remove]
  4. SIMP SQUEEZE: [any bare simp? badly formatted simp only? use simp?]
  5. NAMING: [OK / rename needed]
  6. LINE PACKING: [lines breaking too early? use #check as reference]
  7. BY PLACEMENT: [violations or "OK"]
  8. FORMAT: [λ, $, show, indent, empty lines, or "OK"]
  9. COMMENTS: [inline comments or "clean"]
  10. DOCSTRING: [action needed or "OK"]
  11. TERM MODE: [by exact, by rfl, eta, or "none"]
  12. AUTOMATION: [grind/fun_prop opportunities or "none"]
  13. VISIBILITY: [private needed or "OK"]
  14. STRUCTURE: [>30 lines, ∧, branches >10 — attempt fix]
  15. MATHLIB: [replacement found or "checked, none"]

  Issues to fix: [numbered list]

  B. Implement ALL fixes from the report.
  C. Verify with lean_diagnostic_messages after each declaration.

Step 5: After all declarations, run lean_diagnostic_messages on the full file.
  Report: original warnings vs remaining warnings.

[INCLUDE THE FULL ITEM 2 (HAVE SCAN), ITEM 4 (SIMP SQUEEZE), ITEM 6 (LINE PACKING),
 ITEM 3 (SET_OPTION), AND ITEM 14 (STRUCTURE) PROCEDURES FROM cleanup.md]
```

**CRITICAL: Include the detailed procedures for items 2, 3, 4, 6, and 14 in the agent prompt.**
These are the most commonly skipped checks. If you just say "see cleanup.md," the agent won't
read it. Paste the actual rules.

#### 2c: Verify the agent's work

After the agent completes, verify:
1. Run `lean_diagnostic_messages` on the file — should be clean (or only STRUCTURE items remaining)
2. Check that the agent actually printed audit reports (did it skip declarations?)
3. If the agent skipped declarations or didn't fix issues, re-dispatch for the missed items

#### 2d: Update progress

```
## Progress: 3/N complete

| # | File | Lines | Status | Issues Fixed |
|---|------|-------|--------|--------------|
| 1 | Foo/Bar.lean | 450 | ✓ done | 12 |
| 2 | Foo/Baz.lean | 200 | ✓ done | 5 |
| 3 | Helpers.lean | 800 | ✓ done | 18 |
| 4 | Main.lean | 600 | ⏳ next | - |
| ... | ... | ... | pending | - |
```

### Step 3: Final Project Verification

After ALL files are processed:

1. Run `lean_diagnostic_messages` on each file one more time
2. Build the full project to verify everything compiles together:
   ```bash
   lake build
   ```
3. Print the final report

### Step 4: Final Report

```
## Cleanup-All Report

### Summary
- Files processed: N/N ✓
- Total issues fixed: M
- Total lint warnings resolved: L
- Remaining STRUCTURE items: S (for /decompose-proof)

### Per-File Results
| File | Declarations | Issues Fixed | Remaining |
|------|-------------|-------------|-----------|
| Foo/Bar.lean | 15 | 12 | 1 (STRUCTURE) |
| Foo/Baz.lean | 8 | 5 | 0 |
| ... | ... | ... | ... |

### Files Flagged for /decompose-proof
- Helpers.lean: `theorem_X` (45 lines), `theorem_Y` (38 lines)
- Main.lean: `main_result` (62 lines)

### Compilation
✓ Full project builds successfully
```

---

## Key Rules for This Command

1. **ONE file at a time.** Do not batch files. Each file gets a dedicated agent with full context.

2. **FULL rules in every agent prompt.** Do not say "refer to cleanup.md." Paste the actual
   HAVE SCAN procedure, SIMP SQUEEZE procedure, LINE PACKING procedure, SET_OPTION procedure,
   and STRUCTURE procedure into every agent prompt. Agents won't read external files.

3. **Verify after each file.** Run lean_diagnostic_messages. If issues remain, re-dispatch.

4. **Track progress visibly.** Print the progress table after each file. The user must be able
   to see that every file was processed.

5. **Do not skip files.** Every `.lean` file in the list must be processed. If a file is already
   clean, the agent should confirm this by printing audit reports showing "OK" for each check.

6. **Handle cross-file renames in a final pass.** If a cleanup agent reports "Refactoring needed:
   rename X used in other files," collect these and handle them after all files are processed.

---

## Reference

- `commands/cleanup.md` — the per-file cleanup procedure (items 2, 3, 4, 6, 14 procedures)
- `skills/mathlib-quality/agents/declaration-fixer-prompt.md` — agent rules reference
