---
name: cleanup-all
description: Project-wide cleanup using an orchestrator-worker pattern. The main session is the orchestrator — it does NOT read files, run lean_* tools, or edit. It dispatches batched per-file Agent calls with tight prompts (working dir + branch + build state + sequence + target), then narrates progress in one-line scoreboards between dispatches. Actual work happens in fresh subagent contexts so the orchestrator's context stays light and the session sustains across many hours / days. The proven pattern from a 28-day, 9000-message, 395-dispatch marathon.
---

# /cleanup-all — Project-Wide Cleanup (Orchestrator Mode)

Run the full `/cleanup` workflow over every `.lean` file in the project, sustained
across hours or days, without exhausting the orchestrator's context.

The trick: the main session is an **orchestrator**, not an implementer. The
orchestrator dispatches batched `Agent` calls, each with a tight prompt and a
concrete target, then narrates progress in one-line scoreboards between
dispatches. The file reading, the LSP calls, the edits, and the per-declaration
golf all happen in **subagent contexts** — each starts fresh, does its batch,
returns a summary. The orchestrator never holds the work in its own context.

This pattern was observed in a real production session that ran for **28 days
across 23 active days**, dispatched **395 Agent calls**, spawned **790 subagent
contexts** (workers spawning sub-workers), and survived **3 auto-compactions**
without losing the through-line. The mechanism is the orchestrator/worker
split, not heroic context management.

## Usage

```
/cleanup-all [directory]
```

If no argument, processes all `.lean` files under the project root (excluding
`.lake/`, `build/`, `.git/`).

---

## The orchestrator's role (binding)

You are the **orchestrator**. Your job is to dispatch and track. You do **NOT**:

- Read project `.lean` files — workers do that, they need the fresh context for it
- Run `lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`, or any
  `lean_*` LSP query
- Use `Edit` or `Write` on project files
- Run `lake build` yourself (workers do that as the first check of every batch)
- Spot-check the worker's diff or rerun their LSP queries

You **DO**:

- Enumerate files (one `find` call, once)
- Bucket files by size for batched dispatch
- Dispatch `Agent` calls following the verbatim prompt template below
- Maintain a one-line scoreboard between dispatches
- Collect per-batch summaries from the workers' reports
- Dispatch one final verification Agent at the end
- Print the consolidated report at the very end

This split is what makes the marathon sustainable. The orchestrator's context
stays light — just the scoreboard and the dispatch log. The 200k context per
worker is spent on the actual cleanup. When auto-compaction fires on the
orchestrator (rare; the context is small), the scoreboard + remaining file
list is enough state to continue from.

## Anti-patterns (binding)

The same self-rejection discipline that applies in `/beastmode` applies here.
Specifically, before sending any user-visible text or making any non-dispatch
tool call:

- **No "let me verify" tool calls between dispatches.** No `Bash lake build`,
  no `lean_diagnostic_messages`, no `Read` on a project file. Those are the
  worker's job. If you find yourself reaching for one, dispatch the next
  Agent instead.
- **No mid-orchestration status paragraphs.** Output between dispatches is
  one scoreboard line, then the next `Agent` call. Not a progress table
  after every file. The progress table appears once at the end.
- **No "Continuing now." preambles.** Just dispatch.
- **No "Let me check the next file" announcements.** Just dispatch.
- **No goal types or diff fragments pasted into the orchestrator's text.**
  If you see one, the worker should have summarised it — re-read their
  summary, not the underlying state.
- **No "Want me to keep going?"** The user invoked `/cleanup-all`. Keep going.

Forbidden patterns (literal — strip and dispatch):

```
"Let me verify ..."             "Let me check ..."
"Let me run lake build to ..."  "Let me read the file first ..."
"Quick sanity check ..."        "Status update: ..."
"Continuing now ..."            "Ready for the next file?"
"Want me to keep going?"        "Should I continue?"
"Let me spot-check ..."         "Let me confirm the worker's ..."
```

If the orchestrator drafts any of those, the whole draft is the defect.
Strip and dispatch.

---

## Procedure

### Step 1 — Enumerate (one Bash call)

```bash
find [directory] -name "*.lean" \
  -not -path "*/.lake/*" -not -path "*/build/*" -not -path "*/.git/*" \
  -exec wc -l {} \; | sort -n
```

Capture the list with line counts. Print a one-screen summary:

```
## Project inventory

Files: N total
- Tiny (<100 lines): K files
- Small (100-300): K files
- Medium (300-700): K files
- Large (700+): K files

Total lines: T

Build state (one-shot check):
```

Then run **once** at the start:

```bash
lake build 2>&1 | tail -5
```

Record "Build is clean." or "Build broken at <file>:<line>". If broken, **stop
and report** — the marathon needs a clean baseline; workers can't tell what
they introduced versus what was already broken.

### Step 2 — Bucket by size

Group files into batches by line-count range. Batch sizes are calibrated so
each worker has ≈700-1500 lines of code to consider — within one fresh 200k
context.

| Range | Files per batch |
|---|---|
| < 100 lines | 6-10 |
| 100-300 lines | 3-5 |
| 300-700 lines | 1-2 |
| 700+ lines | 1 |

Order batches **largest first**. Big files have the most opportunity for line
savings and surface refactoring issues that propagate to dependents; doing
them first means later batches benefit.

Within a batch, list files in import-graph order if known; otherwise
alphabetical. Workers process the listed order sequentially.

### Step 3 — Batched dispatch loop

For each batch, dispatch **one `Agent` call** (`subagent_type: general-purpose`,
foreground — wait for the result). Use this verbatim prompt template; only
substitute the bracketed fields:

```
You are running /cleanup on a batch of files in a project-wide cleanup.

Working dir: [absolute project root path]
Current branch: [branch name from `git branch --show-current`]
Build is clean. (Verified by orchestrator at session start.)

Files in this batch (work SEQUENTIALLY, in this order):
1. [path/to/File1.lean] ([N1] lines)
2. [path/to/File2.lean] ([N2] lines)
...

Target: complete the full Mode B (Whole File) `/cleanup` workflow on every file
in the list. Do not stop after one file; finish the batch.

For each file:

  PHASE 1  PREPARE                  collect context, read references
  PHASE 2  STYLE AUDIT              full punch-list, no fixes yet
  PHASE 3  FILE-LEVEL FIXES         file-level items from the punch-list
  PHASE 4  PER-DECLARATION GOLF     **one Agent dispatch per declaration**
                                    (you are allowed and expected to spawn
                                    sub-workers here — Phase 4 of /cleanup
                                    documents the per-declaration prompt)
  PHASE 5  REFACTORING              cross-declaration changes
  PHASE 6  FINAL VERIFICATION       lake build + diff gates
  PHASE 7  REPORT                   per-file summary

Before starting file 1, read `commands/cleanup.md` in full so you know what each
phase requires — especially the Phase 4 sub-worker prompt and the diff-gate
rules from `references/cleanup-gates.md`. Apply every rule in
`references/golfing-rules.md`; the audit will not be accepted if any rule
slot is blank.

Return a single compact summary at the end of the batch, in this exact shape:

  ## Batch summary

  | File | Before | After | Δ | Rules applied | Notes |
  |------|--------|-------|---|---------------|-------|
  | File1.lean | 450 | 416 | -34 | 1.4, 1.10, 2.7, 3.3 | 1 STRUCTURE flagged |
  | File2.lean | 312 | 285 | -27 | 1.1, 1.9, 2.1 | clean |
  ...

  Cross-file refactoring spotted (for the orchestrator to schedule):
  - rename wt_* → weight_* (caller sites: ...)
  - bridge lemma Foo.bar_aux removable (mathlib has Foo.bar directly)

  Files needing /decompose-proof (proofs >50 lines after golfing):
  - File1.lean: `theorem_X` (58 lines)

  Files needing /split-file (>1500 lines after cleanup):
  - (none)

  Build state after batch: ✓ clean / ✗ broken at <file>:<line>

Do **not** include intermediate per-phase status in the summary; the summary
is what the orchestrator sees. Per-phase status blocks live in your own
context for your own reference.

If a file in the batch genuinely cannot be cleaned without user input (e.g.
the file's main theorem statement is wrong), include it in the summary
table with status "blocked: <one-line reason>" and continue with the next
file in the batch. Do not stop the batch.
```

That is the entire orchestrator → worker prompt. About 1200 characters
substantive, plus the file list. Do not embellish.

### Step 4 — Between dispatches: scoreboard, not analysis

After each batch returns, the orchestrator emits exactly one line:

```
**T lines remaining. K/N files done (P%).** Continuing.
```

— where T is the cumulative line count across remaining files, K is the
count of files marked ✓, N is the total, P is K/N as a percentage. Then
the orchestrator dispatches the next batch.

That is the **entire** output between dispatches. No table updates. No
"the worker reported X". No "I noticed Y in their summary". No
verification. The scoreboard is the only narration.

Examples of acceptable orchestrator turns:

```
**45,212 lines remaining. 12/89 files done (13%).** Continuing.
[Agent dispatch for batch 13]
```

```
**42,815 lines remaining. 18/89 files done (20%).** Continuing.
[Agent dispatch for batch 19]
```

If a worker's summary names cross-file refactoring or `/decompose-proof`
candidates, store them in your internal dispatch log — do **not** narrate
them mid-loop. They appear once in the final report.

### Step 5 — Cross-file refactoring pass (one dispatch, optional)

After all per-file batches return, if multiple batches flagged the same
cross-file refactor (a rename that touches N files, a removable bridge
lemma, etc.), dispatch **one final** `Agent` call to handle the
cross-file pass:

```
Working dir: [project root]
Current branch: [branch]
Build is clean.

Cross-file refactoring queue (collected from per-file workers):

1. Rename `wt_*` → `weight_*`. Call sites identified:
   - File1.lean:45, File1.lean:88
   - File3.lean:120
2. Remove bridge lemma `Foo.bar_aux` (mathlib has `Foo.bar` directly).
   Call sites in 4 files: ...

Apply each refactor end-to-end: every call site, every dependent file,
`lake build` clean at the end. Return a summary.
```

If no cross-file work was flagged, skip Step 5.

### Step 6 — Final verification (one dispatch)

Dispatch one final `Agent` to run the project-wide verification:

```
Working dir: [project root]
Current branch: [branch]

Run the project-wide post-cleanup verification:

1. `lake build` — must succeed, no warnings on the changed files.
2. `lake exe runLinter` (or the project's lint command) — must be clean.
3. Spot-check the main project theorem(s) — list and `#print axioms` each;
   confirm only the standard set.
4. Diff stats: total lines removed across the cleanup, by directory.

Return a compact verification report.
```

### Step 7 — Final report (orchestrator, once)

Only at the very end, after Step 6 returns, the orchestrator prints the
consolidated report:

```
## /cleanup-all report

### Summary
- Files processed: N/N ✓
- Total lines before: T_before
- Total lines after:  T_after
- Net reduction:      ΔT (P%)
- Cross-file refactors: K applied
- Files flagged for /decompose-proof: K (listed below)
- Files flagged for /split-file: K (listed below)

### Per-file results (aggregated from worker summaries)
| File | Δ | Rules applied | Notes |
|------|---|---------------|-------|
| ...  | ...| ...           | ...   |

### Cross-file refactoring applied
- ...

### Files needing /decompose-proof
- ...

### Files needing /split-file
- ...

### Compilation
✓ lake build clean
✓ runLinter clean
✓ Main theorems: <list> — axioms clean
```

---

## Why this works (and why the previous approach didn't)

**Previous approach.** One file per Agent, orchestrator does `lean_diagnostic_messages`
between files, full progress table updated after every file. The orchestrator's
context fills with file paths, diagnostic outputs, and table renderings. At
~30 files, the orchestrator runs out of context, the user has to restart the
session, the dispatch log is lost.

**Orchestrator pattern.** The orchestrator's job is choreography:
enumerate → bucket → dispatch → scoreboard → dispatch → scoreboard → ...
→ final dispatch → report. Its context contains the file list and the
dispatch log. That's it. A 28-day session is feasible because the
orchestrator's context grows ~one line per batch.

The work happens in workers. Each worker gets a fresh ~200k context for
its batch (3-5 files for medium-size). Worker reads the files, runs the
LSP, dispatches its own per-declaration Phase-4 sub-workers, runs the
build, returns a summary. The summary is what the orchestrator sees —
maybe 30 lines per batch.

Math: an 89-file project at 3-5 files per batch = ~25 batches. Orchestrator
context: ~25 × (30-line summary + scoreboard) = ~1000 lines. That fits
comfortably in one window, with room for the initial enumeration.

Workers spawn sub-workers (Phase 4 dispatches per-declaration). A real
production run logged 395 outer dispatches but 790 subagent contexts —
the recursion is doing its job.

---

## Key rules summary

1. **Orchestrator does not read files, edit files, or run LSP queries.**
   Workers do.
2. **One Agent dispatch per batch.** Batch size depends on file size
   (Tiny: 6-10, Small: 3-5, Medium: 1-2, Large: 1).
3. **Verbatim prompt template.** Working dir + branch + build state +
   file list + sequential target. ~1200 chars substantive.
4. **One-line scoreboard between dispatches.** No analysis prose, no
   table updates, no verification round-trips.
5. **Final report only at the end.** Not after every file.
6. **Workers can spawn sub-workers.** Phase 4 of `/cleanup` is built
   for this — the per-declaration prompt lives in `commands/cleanup.md`.
7. **Build verification happens in workers**, not in the orchestrator.
   The orchestrator's only build check is the one-shot baseline at
   Step 1.

---

## Reference

- `commands/cleanup.md` — the per-file 7-phase workflow workers execute
- `commands/beastmode.md` — same orchestrator-vs-implementer split; the
  self-rejection protocol there applies to `/cleanup-all`'s orchestrator
  too (no "Continuing now", no goal-pasting, no mid-turn status reports)
- `skills/mathlib-quality/references/golfing-rules.md` — full rule list
  workers apply in Phase 4
- `skills/mathlib-quality/references/cleanup-gates.md` — diff gates
  workers run in Phase 6
