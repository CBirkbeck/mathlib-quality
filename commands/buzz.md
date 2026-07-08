---
name: buzz
description: Profile Lean declarations, find the slow ones, trace-diagnose the root cause, and fix them until each elaborates fast — ideally under a second. Statements never change; maxHeartbeats never goes up.
---

# /buzz — Make Slow Proofs Fast

Find every declaration that elaborates slowly, work out **why** from the profiler and the
traces, and fix it — target: each declaration under **one second** on the current machine.

The workflow this command automates is the one a mathlib reviewer applies to an AI-written
PR: compile each file and watch the orange bars (the editor's still-elaborating indicator);
for the few declarations whose bars linger, read the traces, find the issue, fix it — and
then check the *other* slow declarations for the **same issue** before diagnosing them from
scratch, because slow declarations written by the same author at the same time almost
always share one root cause. That propagation step ("it's the same issue") is what makes
the human version of this workflow fast, and it is binding here (Phase 5).

`/buzz` is a performance scalpel, not a general cleaner:

- **Not golfing.** `/cleanup` makes proofs short and idiomatic; `/buzz` makes them fast.
  A proof can get *longer* here (a squeezed simp, an ascribed `have`) if that's what speed
  costs. Run `/cleanup` afterwards if the edit got verbose.
- **Not decomposition.** When the honest fix is splitting the proof, `/buzz` flags
  `/decompose-proof` rather than doing the surgery itself.
- **The anti-`maxHeartbeats` tool.** Everywhere else in this plugin, `set_option
  maxHeartbeats` is deleted on sight (`/cleanup` 3.7, `/pre-submit`) with the instruction
  "optimize the proof instead" — `/buzz` is where that instruction gets carried out.

All measurement techniques, trace-reading instructions, and the root-cause taxonomy live
in `references/profiling.md`. Read it before Phase 3.

## Usage

```
/buzz                       # PR mode: sweep the .lean files changed vs the default branch
                            # (merge-base diff + uncommitted changes)
/buzz <file.lean>           # sweep one file
/buzz <file.lean> <decl>    # one declaration, straight to Phase 3
/buzz --all                 # sweep every project .lean file (slow; use for audits)
/buzz --budget <ms>         # per-declaration elaboration budget (default 1000)
```

## Hard rules (binding)

1. **Statements never change.** Signature, hypotheses, instance arguments, universes,
   conclusion — byte-identical. Only proof bodies (and purely local scaffolding above
   them) may be edited. `theorem_statement_protected` and `definition_protected` from
   `references/cleanup-gates.md` run on the diff in Phase 6.
2. **Limits never go up.** Adding or raising `maxHeartbeats`, `synthInstance.maxHeartbeats`
   or `maxRecDepth` is forbidden — that hides the defect this command exists to remove.
   *Removing* an existing raise (because the fixed proof no longer needs it) is a win and
   should be attempted for every declaration in scope.
3. **No trust downgrades.** No `sorry`, no new axioms, no `native_decide`.
4. **Profiling scaffolding is temporary.** Every `set_option profiler/trace.*/diagnostics
   … in` and every `count_heartbeats in` wrapper added while diagnosing MUST be reverted.
   Phase 6 greps for leftovers; any hit is a gate failure.
5. **Global changes are flagged, not applied.** New shortcut instances, instance-priority
   edits, file-wide `attribute [-simp]`, restating a helper at a different abstraction
   level — these can be the right fix but they change public API. Collect them in the
   Phase 7 report as a numbered menu for the user (same policy as `/generalise` big
   changes). Locally-scoped variants (`… in` syntax) may be applied directly.
6. **Every fix is measured.** No before/after numbers → the fix didn't happen. Wall-clock
   from the sweep is the target metric; heartbeats (`count_heartbeats in`, temporary) are
   the deterministic cross-check recorded alongside.

## Phases

```
PHASE 0  DOCTOR       baseline lake build of the target modules; abort if broken
PHASE 1  SWEEP        one profiled compile per file — the headless orange-bar watch
PHASE 2  RANK         per-decl timing table; SLOW = over budget; punch list worst-first
PHASE 3  DIAGNOSE     worst decl: profile → trace → classify against the taxonomy
PHASE 4  FIX          apply the pattern fix; verify; re-measure; iterate or defer
PHASE 5  PROPAGATE    test the found root cause on every remaining slow decl FIRST
PHASE 6  GATES        statements unchanged, no limit raises, no scaffolding, build clean
PHASE 7  REPORT       before/after table, root causes, deferrals, flagged big changes
```

### PHASE 0 — Doctor

Resolve the target file set:

- **PR mode (bare `/buzz`)**: changed `.lean` files = `git diff --name-only
  <merge-base with default branch>..HEAD -- '*.lean'` plus any dirty files from
  `git status --porcelain`. If the set is empty, say so and suggest `/buzz <file>` or
  `/buzz --all`; stop.
- **File / decl / `--all` modes**: as given.

Then `lake build <module>` for each target file's module. Must pass — `/buzz` measures and
edits working code only. If the baseline is broken: **BROKEN BASELINE**, report, stop
(same policy as `/beastmode` B4). Record the build time; a warm cache matters for honest
sweep numbers.

### PHASE 1 — Sweep (the headless orange-bar watch)

For each target file, one profiled compile (imports come from the olean cache, so the
timings are this file's own):

```bash
lake env lean -Dprofiler=true -Dprofiler.threshold=100 Path/To/File.lean
```

Parse the output: timing messages are anchored to source positions — map each position to
its declaration (via the file outline) and record the total and the dominant category
(`typeclass inference`, `simp`, `tactic execution`, `type checking`, `compilation`, …).
Wall-clock jitters; re-run the sweep once for any declaration within ±25% of the budget
before classifying it.

In single-declaration mode, skip the sweep and go straight to Phase 3 (but still take a
baseline measurement of that declaration first — `lean_profile_proof` or a temporary
`count_heartbeats in`).

**Required artifact — sweep table** (also the skeleton of the Phase 7 report):

```
## /buzz sweep — <scope>, budget 1000ms

| Decl | File:line | Elab time | Dominant category | Over budget? |
|------|-----------|-----------|-------------------|--------------|
| Foo.bar_baz        | Foo.lean:142 | 4.8s  | typeclass inference | SLOW |
| Foo.qux_of_bar     | Foo.lean:203 | 2.1s  | typeclass inference | SLOW |
| Foo.abc            | Foo.lean:77  | 1.3s  | simp                | SLOW |
| (all others)       | —            | <1s   | —                   | ok  |

Existing maxHeartbeats overrides in scope: Foo.lean:140 (400000) — removal attempted in Phase 4.
```

### PHASE 2 — Rank

SLOW = elaboration over the budget (default 1000ms). Sort worst-first; that order is the
work queue. Declarations already carrying a `set_option maxHeartbeats` raise are SLOW by
definition regardless of measured time (the raise is the evidence), and join the queue.

If nothing is over budget: print the sweep table with a `FAST BOARD — nothing over
<budget>ms` line and stop. `/buzz` invents no work.

### PHASE 3 — Diagnose (worst declaration first)

Escalation ladder — stop at the first rung that names the culprit:

1. **`lean_profile_proof`** on the declaration — tactic-level hotspots, no file edits.
   Often this alone names the guilty line ("the `nlinarith` at :148 is 90% of the time").
2. **`set_option trace.profiler true in`** (with `set_option trace.profiler.threshold 50`)
   temporarily prefixed to the declaration; read the tree via
   `lean_diagnostic_messages`; walk the dominant child down to where the time
   concentrates. Revert the edit as soon as the tree is captured.
3. **Targeted trace** for the suspected cause, one at a time, scoped with `in`:
   `trace.Meta.synthInstance` / `trace.Meta.isDefEq` /
   `trace.Meta.Tactic.simp.rewrite` / `diagnostics`. Revert after reading.
4. **Classify** against the taxonomy in `references/profiling.md` (instance-synthesis
   blowup / fat simp / defeq blowup / heavy terminal automation / mvar churn / coercion
   churn / duplicated subterms / kernel replay).

**Required artifact — diagnosis block** (one per diagnosed declaration):

```
### Diagnosis: Foo.bar_baz (4.8s)
- Hotspot: `rw [mul_assoc]` loop at Foo.lean:150-156 — 4.1s of 4.8s
- Dominant trace node: Meta.synthInstance — `Module ℂ (⨂[ℝ] …)` re-searched 41×
- Root cause class: 1 (instance-synthesis blowup), re-search-per-rewrite variant
- Evidence: trace.profiler tree captured at <turn>; synthInstance trace shows the
  identical query at every rewrite step
```

A fix applied without a diagnosis block is a defect — pattern-guessing is how "fixes" that
change nothing get committed.

### PHASE 4 — Fix

Apply the taxonomy's fix pattern for the diagnosed class (`references/profiling.md`, fixes
listed per cause in preference order). Then:

1. `lean_diagnostic_messages` on the file — clean (the proof still proves).
2. Re-measure the declaration the same way it was measured before (sweep command, plus
   `count_heartbeats in` cross-check, then revert the wrapper).
3. **Success** = under budget. Log `before → after` (ms and heartbeats).
4. **Improved but still over budget** = keep going: next fix pattern for the class, or
   re-diagnose (the first cause can mask a second — a fat simp often hides behind an
   instance blowup).
5. **Stuck** — only after at least 3 distinct fix attempts, each measured (the same
   ≥3-attempts evidence bar as `/beastmode`'s G4): mark **DEFERRED** with the attempts
   listed, and name the follow-up — usually `/decompose-proof <decl>` (elaboration work is
   real; split it), occasionally a flagged big change (rule 5) that would fix it pending
   user approval.
6. If the declaration carried a `maxHeartbeats` raise, delete it now and confirm the fixed
   proof compiles without it. A deferred declaration keeps its existing raise (removal
   blocked — say so in the report); it never gets a bigger one.

### PHASE 5 — Same-issue propagation (binding order)

Before running Phase 3 on slow declaration #2..#N: **test root cause #1 against each of
them first.**

1. Cheap signature check — does the declaration match the same pattern? (Same dominant
   profiler category from the Phase 1 sweep; grep for the same source pattern — the same
   unfolding simp, the same `erw`, the same repeated instance-heavy rewrite.)
2. If it matches: apply the same fix pattern directly, verify + re-measure (Phase 4 steps
   1-3). Log it as `same issue as <first decl>`.
3. Only declarations that *don't* match (or don't respond — measured) get their own full
   Phase 3 diagnosis, and their root cause joins the propagation set for the remainder.

This ordering is the point of the command. One PR's slow declarations nearly always share
an author-pattern; diagnosing each from scratch wastes the strongest signal available.

### PHASE 6 — Gates

Run on the cumulative diff (definitions per `references/cleanup-gates.md`):

| Gate | Expected |
|------|----------|
| `theorem_statement_protected` | ✓ — no statement line changed |
| `definition_protected` | ✓ — no def changed |
| no-limit-raise | ✓ — `grep -n "set_option \(maxHeartbeats\|synthInstance.maxHeartbeats\|maxRecDepth\)"` over touched files shows **no new lines** vs baseline (fewer is the goal) |
| no-scaffolding | ✓ — `grep -n "set_option \(profiler\|trace\.\|diagnostics\)\|count_heartbeats in"` over touched files shows nothing added by this session |
| `lake_build_file` | ✓ — every touched module builds |
| `cumulative_no_unintended_breakage` | ✓ — downstream call sites still compile |
| re-sweep | ✓ — Phase 1 sweep re-run on touched files; every fixed decl measured under budget in the final state (fixes can interact) |

Any gate failure: fix or revert the offending edit; a `/buzz` session never ends with a
red gate.

### PHASE 7 — Report

```
## /buzz report — <scope>, budget 1000ms

| Decl | Before | After | Speedup | Root cause | Fix |
|------|--------|-------|---------|------------|-----|
| Foo.bar_baz    | 4.8s / 310k hb | 0.4s / 21k hb | 12× | instance re-search per rw | haveI the Module instance once |
| Foo.qux_of_bar | 2.1s / 150k hb | 0.3s / 18k hb | 7×  | same issue as bar_baz     | same fix |
| Foo.abc        | 1.3s / 95k hb  | 0.6s / 40k hb | 2×  | fat terminal simp         | squeezed (perf exception, noted) |

- maxHeartbeats raises removed: 1 (Foo.lean:140) · added: 0
- Deferred (still over budget): <none | list with attempts + suggested follow-up>
- Flagged big changes needing approval:
  1. Add shortcut instance `Module ℂ (⨂[ℝ] M N)` — would also fix <decls>; public API.
- Scaffolding check: clean (no profiler/trace/diagnostics/count_heartbeats left behind)
- File wall-clock: Foo.lean 11.2s → 3.9s
```

Chat-only, like `/project-status` — no sidecar files. If a fix pattern felt reusable
beyond the taxonomy, suggest `/teach` to record it.

## Interplay with the other commands

- **`/cleanup`** deletes `maxHeartbeats` raises (3.7) and has a blunt timeout ladder
  (grind → inline haves → extract helpers). When that ladder fails, or when you want the
  *reason* not just a workaround, `/buzz` is the trace-driven follow-up. Conversely, after
  a `/buzz` fix that made a proof more verbose, `/cleanup <file> <decl>` re-golfs it —
  keeping the timing (re-measure after; golf must not undo the perf fix).
- **`/decompose-proof`** is where `/buzz` sends declarations whose elaboration work is
  genuinely irreducible — five 200ms helpers beat one 1s monolith.
- **`/pre-submit`** greps for the limit raises and leftover `set_option`s that `/buzz`'s
  gates also enforce; running `/buzz` on the PR's files before `/pre-submit` is the
  natural order.

## Reference

- `skills/mathlib-quality/references/profiling.md` — measurement how-to, trace reading,
  root-cause taxonomy with fix patterns (the knowledge base for Phases 3–5)
- `skills/mathlib-quality/references/cleanup-gates.md` — statement/def protection gates
- `skills/mathlib-quality/references/golfing-rules.md` § 3.7 — maxHeartbeats removal
- `commands/decompose-proof.md` — the follow-up for irreducibly heavy proofs
