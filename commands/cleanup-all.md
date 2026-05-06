---
name: cleanup-all
description: Run /cleanup on every file in the project, tracked file by file
---

# /cleanup-all — Project-Wide Cleanup

Run the full `/cleanup` procedure on every `.lean` file in the project. Each file gets its
own dedicated agent so nothing is skipped.

## Usage

```
/cleanup-all [directory]
```

If no argument, processes all `.lean` files (excluding `.lake/`, `build/`).

---

## Why this command exists

When told "run /cleanup on all files," a single agent will:
- Skip files (especially later ones as context fills up)
- Rush the per-file 7-phase workflow
- Lose context and forget rules after a few files

This command fixes that by giving EACH FILE its own dedicated agent with the full rules and
its own context window.

---

## Procedure

### Step 1 — Enumerate files

```bash
find [directory] -name "*.lean" -not -path "./.lake/*" -not -path "./build/*" | sort
```

Print the full file list with line counts and ask the user to confirm before proceeding:

```
## Files to clean (N total)

| # | File | Lines | Status |
|---|------|-------|--------|
| 1 | Foo/Bar.lean | 450 | pending |
| 2 | Foo/Baz.lean | 200 | pending |
| 3 | Helpers.lean | 800 | pending |
...
```

### Step 2 — Process files one at a time

**Sequentially, one file per agent.** Do not batch.

For each file:

#### 2a. Announce

```
## Processing file 3/N: Helpers.lean (800 lines)
```

#### 2b. Dispatch a per-file cleanup agent

Use the `Agent` tool with `subagent_type="general-purpose"`. The worker prompt is below — paste
it verbatim, substituting the file path and progress numbers.

```
You are running /cleanup on [file_path]. This is file X of N in a project-wide cleanup.

This file gets your FULL attention. Do not rush. Take as long as you need.

Your job is to execute the full Mode B (Whole File) workflow from `commands/cleanup.md`,
which is seven phases:

  PHASE 1  PREPARE                  collect context
  PHASE 2  STYLE AUDIT              full punch-list, no fixes yet
  PHASE 3  FILE-LEVEL FIXES         work the file-level items from the punch-list
  PHASE 4  PER-DECLARATION GOLF     one worker per declaration
  PHASE 5  REFACTORING              cross-declaration changes
  PHASE 6  FINAL VERIFICATION       diagnostic-clean, compiles, no FIXMEs
  PHASE 7  REPORT                   one consolidated report

Step 1 of YOUR work: Read `commands/cleanup.md` in full so you know exactly what each phase
requires. The prompt for the per-declaration sub-worker (Phase 4) lives there verbatim —
copy it as-is into each Agent dispatch.

Then execute Phases 1–7 on [file_path]. Do not skip phases. The user has explicitly
demanded methodical, no-shortcut cleanup — every audit item gets a concrete answer, every
golfing rule gets considered, every declaration gets its own focused sub-worker in Phase 4.

When done, output the Phase 7 report.
```

#### 2c. Verify the agent's work

After the agent reports done:

1. `lean_diagnostic_messages` on the file — must be clean (or only `[STRUCTURE]` items remaining).
2. Confirm the agent printed the Phase 7 report.
3. Spot-check that the Phase 4 status block shows golf rules considered for at least one declaration.
4. If the agent skipped any phase or declaration, re-dispatch with explicit instructions on what was missed.

#### 2d. Update progress

```
## Progress: 3/N complete

| # | File | Lines | Status | Issues fixed | Saved (lines) |
|---|------|-------|--------|--------------|---------------|
| 1 | Foo/Bar.lean | 450 | ✓ done | 12 | -34 |
| 2 | Foo/Baz.lean | 200 | ✓ done |  5 | -8  |
| 3 | Helpers.lean | 800 | ✓ done | 18 | -120 |
| 4 | Main.lean    | 600 | ⏳ next |    |     |
...
```

### Step 3 — Final project verification

After all files done:

1. `lean_diagnostic_messages` on each file again.
2. `lake build` to ensure the whole project still compiles together.
3. Print the final report.

### Step 4 — Final report

```
## /cleanup-all report

### Summary
- Files processed: N/N ✓
- Total issues fixed: M
- Total lint warnings resolved: L
- Total lines saved: ΔL

### Per-file results
| File | Declarations | Issues fixed | Saved | Notes |
|------|-------------|--------------|-------|-------|
| Foo/Bar.lean | 15 | 12 | -34 | 1 STRUCTURE flagged |
| Foo/Baz.lean | 8  |  5 |  -8 |                     |
| ... | ... | ... | ... | ... |

### Cross-file refactoring (collected from Phase 5 reports)
- Renamed `wt_*` → `weight_*` across 3 files (24 call sites)
- Removed bridge lemma `splits_id_iff_*` (mathlib used directly in 4 files)

### Files flagged for /decompose-proof
- Helpers.lean: `theorem_X` (38 lines after golfing)
- Main.lean: `main_result` (62 lines)

### Files flagged for /split-file
- Big.lean (1,847 lines)

### Compilation
✓ lake build succeeded
```

---

## Key rules for this command

1. **One file per agent.** Each file gets its own dedicated context and worker. No batching.
2. **The per-file worker runs the FULL 7-phase /cleanup workflow.** Don't accept "I did a quick pass." Phase 4 dispatches *another* level of agents (one per declaration) — that's by design.
3. **Verify after each file.** `lean_diagnostic_messages`. If issues remain, re-dispatch.
4. **Track progress visibly.** Print the progress table after each file so the user can see no file was skipped.
5. **Cross-file refactoring goes in the final pass.** When per-file workers report `Refactoring needed: rename X across files`, collect these and handle in Step 4 (or after all files are processed if it's safer to do once).

---

## Reference

- `commands/cleanup.md` — the per-file 7-phase workflow (the per-file worker reads this)
- `skills/mathlib-quality/references/golfing-rules.md` — full golfing rules checklist (per-declaration sub-workers in Phase 4 read this)
