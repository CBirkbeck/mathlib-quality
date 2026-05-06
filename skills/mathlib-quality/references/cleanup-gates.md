# Cleanup Gates

`/cleanup` runs verification **gates** at three points:

- **Phase 0 (pre-flight doctor)**: baseline gates — the file/project must be in a known
  state before we start, otherwise we can't tell what breakage we introduced.
- **Phase 4 (per-worker)**: diff gates — each Phase-4 worker produces a focused diff
  against its declaration; gates run on that diff and a gate failure reverts the worker's
  changes.
- **Phase 6 (final verification)**: file/project gates — the cumulative file-level diff
  is gated, plus a build of the affected modules.

The gates are inspired by [frenzymath/shouyi](https://github.com/frenzymath/shouyi) — a
batch processor that uses gates to accept/reject AI-generated diffs in mathlib. We're
borrowing the gate pattern, not the worktree-batch architecture: our workers edit in
place; the gates run on the diff captured against the pre-edit state.

## Gate catalogue

### `lake_build_file` — per-file build succeeds

**What it checks.** `lake build <Module>` exits 0 for the affected file's module, where
`<Module>` is the file path translated to a module name (e.g.,
`Mathlib/Algebra/Foo.lean` → `Mathlib.Algebra.Foo`).

**When it runs.** Phase 6, after all Phase-4 workers have completed and Phase 5
refactoring is done. Optionally per-worker (Phase 4 step 5b) for files that build
independently within a few seconds.

**Why it's stronger than `lean_diagnostic_messages`.** LSP diagnostics catch most errors,
but `lake build` also checks: import-graph effects, transitive build-only-fails-fresh
errors, the actual compilation pipeline CI uses. A green LSP is *necessary but not
sufficient* — a green `lake build` is the real bar.

**Implementation.**

```bash
# translate file path → module name
MODULE=$(echo "$FILE_PATH" | sed -e 's|/|.|g' -e 's|\.lean$||')
lake build "$MODULE"
```

Exit-status zero = pass. Capture stderr on failure for the report.

---

### `lake_build` — full project builds

**What it checks.** `lake build` (no argument) succeeds at project scope.

**When it runs.** Phase 0 (baseline — must be green before /cleanup can start) and Phase
6 final (after all workers + refactoring).

**Why both ends.** The Phase-0 baseline establishes that pre-existing breakage isn't ours.
The Phase-6 final verifies our cumulative changes haven't broken anything outside the
files we touched (e.g., a dropped declaration whose call sites we missed).

**Implementation.**

```bash
lake build
```

If `lake exe cache get` is available and the cache is stale, run that first. Failure
captures stderr and aborts the workflow (Phase 0) or fails the cumulative gate (Phase 6).

---

### `definition_protected` — `def` / `abbrev` lines unchanged unless explicitly refactoring

**What it checks.** No line beginning with `def` or `abbrev` is added or removed in the
diff, **unless** the worker's declared action for this declaration was JUNK DEF inlining
(audit item 14) or a generalisation that explicitly touches the def signature.

**When it runs.** Phase 4 per-worker, after the worker completes its edits.

**Why.** The most common silent failure mode for AI golf workers is: while compressing
a proof body, the worker also rewrites the *definition* — changes its signature, its
body, or its visibility — without realising. Definitions are public API; modifications
need to be explicit refactoring decisions, not collateral damage from golfing.

**Implementation (diff-based grep, against worker's pre-edit baseline):**

```bash
git diff --no-color -- "$FILE" | grep -E '^\+(def|abbrev) ' && echo FAIL_ADD
git diff --no-color -- "$FILE" | grep -E '^-(def|abbrev) ' && echo FAIL_REMOVE
```

If the worker's audit reported one of:
- `JUNK DEF: inline at use sites`
- `GENERALISE: <a typeclass change to a def's signature>`
- `Refactoring needed: rename of this def`

then a `def`/`abbrev` line change is *expected* and the gate passes for that decl.
Otherwise it's a defect — revert and re-dispatch.

---

### `theorem_statement_protected` — theorem/lemma signature unchanged unless explicitly refactoring

**What it checks.** A line beginning with `theorem` or `lemma` should match before/after
**unless** the worker's declared action included one of:
- `NAMING: rename to <new>`
- `STRUCTURE: split conjunction`, ∧-split, branch-extraction
- `GENERALISE`-flagged big-change (handled by Phase 5's `/generalise` escalation, not
  this worker)

**When it runs.** Phase 4 per-worker.

**Why.** Same as `definition_protected`. Statements drift during golfing — a worker
might "tighten" `theorem foo : a = b ↔ c` to `theorem foo : a = b → c` because that's
what the proof actually established, when the original `↔` was correct and the proof
was almost right. Or it may add/drop hypotheses as a "small" change. These are public
API changes and must come from an explicit refactoring action, not from golf.

**Implementation.**

```bash
git diff --no-color -- "$FILE" | grep -E '^\+(theorem|lemma) ' && echo FAIL_ADD_DECL
git diff --no-color -- "$FILE" | grep -E '^-(theorem|lemma) ' && echo FAIL_REMOVE_DECL
```

A `+`/`-` pair on `theorem`/`lemma` lines = signature changed. Allowed if the worker's
declared action covers it; otherwise a defect.

---

### `docstring_only_changes` — diff is comment-only (narrow-scope mode)

**What it checks.** Every `+` and `-` line in the diff is either inside a `/-! ... -/` /
`/-- ... -/` block, or is a `--` comment line. No code changes.

**When it runs.** Only when invoked in narrow-scope mode (`/cleanup --docstrings-only
[file]`). Not enabled by default.

**Why.** Sometimes the user only wants to add or fix docstrings, not change any code.
This gate makes that scope explicit and prevents the worker from silently doing more.

**Implementation.** Walk the diff line-by-line tracking comment-block state; record any
`+`/`-` line that's NOT inside a comment as a violation. (The shouyi reference
implementation handles `/- ... -/` block depth and string escaping; we do the same.)

---

### `cumulative_no_unintended_external_breakage` — call-site files still compile

**What it checks.** The set of files that `Grep`-import or use any declaration from this
file all still pass `lean_diagnostic_messages` and (optionally) `lake build`.

**When it runs.** Phase 5 refactoring (after each refactor) and Phase 6 final.

**Why.** /cleanup edits one file but renames + signature changes propagate. A rename
that misses one call site is a regression. A typeclass weakening that doesn't propagate
correctly through the import graph is a regression. This gate catches both.

**Implementation.**

```bash
# collect call-site files
CALL_SITES=$(rg -l --type-add 'lean:*.lean' --type lean "<decl_name>" path/to/project)

# verify each
for F in $CALL_SITES; do
  # LSP check
  lean_diagnostic_messages on F  # via the MCP tool
  # optional: lake build for the module
done
```

A failure on any call-site file is a regression to this cleanup. Surface it in the
final report and revert if it can't be fixed in-place.

---

## Gate report format

Each Phase-4 worker emits a gate-status block. Each Phase-6 final report includes the
file-level gate block. Format:

```
### Gate status — `decl_name` (Phase-4) or <file_path> (Phase-6)

| Gate                                | Result | Details                          |
|-------------------------------------|--------|----------------------------------|
| lake_build_file                     | ✓ pass | <module> built in 4s             |
| definition_protected                | ✓ pass | no def/abbrev lines changed      |
| theorem_statement_protected         | ✗ FAIL | line 47 `theorem foo` removed    |
| cumulative_no_unintended_breakage   | ✓ pass | 4 call-site files clean          |
| (optional) docstring_only_changes   | n/a    | not in docstrings-only mode      |

Overall: FAIL — `theorem_statement_protected`
```

A gate failure with `Overall: FAIL` triggers the recovery procedure:

1. **Phase 4 per-worker.** Revert the worker's edits (`git checkout -- <file>` against
   the pre-worker SHA). Re-dispatch the worker with the gate failure included in the
   prompt: "previous attempt failed `theorem_statement_protected` — line 47 changed
   when no rename or split was declared. Try again, leaving the statement intact."
2. **Phase 6 final.** Stop. Print the gate failure. Don't claim cleanup succeeded.
   Report to the user; let them decide (manual fix, re-run with adjusted scope, etc.).

## Pre-flight doctor (Phase 0)

The doctor establishes a known-good baseline before any work starts. If the baseline
isn't green, /cleanup can't tell what breakage it introduced — better to halt than to
work blind.

Doctor checks:

| # | Check | What | If it fails |
|---|---|---|---|
| 1 | `lake exe cache get` | Optional — speeds up build if available | continue (warning only) |
| 2 | `lake build` | Whole-project build green | ABORT /cleanup; print "baseline broken; fix or run with `--skip-baseline-build`" |
| 3 | `lean_diagnostic_messages` on the target file | LSP responsive on this file | ABORT; LSP issues will mask real errors |
| 4 | `lake exe runLinter <module>` if available | Linter clean on the target file | continue (treated as Phase-2 audit input, not a hard fail) |

The doctor's output goes into the Phase-6 final report so the user can see what the
baseline was.

## When to skip gates

The gates trade speed for safety. For:

- **Single-file experimental tinkering** — gates can be skipped via `/cleanup --no-gates`.
  Useful when the user is iterating quickly and accepts the risk.
- **`/cleanup-all` on huge projects** — `lake_build` after every file is too slow; run
  per-file `lake_build_file` per file, run full `lake_build` only at the end.
- **Files outside any package** — the lake gates don't apply; `lean_diagnostic_messages`
  is the only available signal.

In all skip cases, the report MUST record `gates: skipped` explicitly. Silent skipping
is a defect, the same as silent rule-skipping in the audit.
