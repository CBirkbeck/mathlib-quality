---
name: bump-mathlib
description: Bump mathlib version and fix resulting breakage
---

# /bump-mathlib - Bump Mathlib and Fix Breakage

Update the mathlib dependency (or merge upstream for mathlib PRs), build, and fix all errors caused by the bump.

## Usage

```
/bump-mathlib                    # Auto-detect context and bump to latest
/bump-mathlib <commit-or-date>   # Bump to a specific mathlib version/date
```

## Workflow

### Step 1: Detect Context

Determine whether this is:

**A) A standalone project using mathlib as a dependency**
- Has `lakefile.lean` or `lakefile.toml` with a mathlib dependency
- Check for `require mathlib` in lakefile

**B) A mathlib PR (working directly in mathlib4)**
- Check: `git remote -v` shows `leanprover-community/mathlib4`
- Or: current repo IS mathlib4

Report which context was detected before proceeding.

### Step 2: Perform the Bump

#### Context A: Standalone Project

1. **Read the current lakefile** (`lakefile.lean` or `lakefile.toml`)
2. **Find the current mathlib revision** (look for `require mathlib` with a `rev` or commit hash)
3. **Update to the target version:**
   - If no target specified: update to latest mathlib `master`
   - If target specified: use that commit/tag
4. **Run `lake update mathlib`** to update the lockfile

```bash
# Update lake-manifest.json
lake update mathlib
```

#### Context B: Mathlib PR

1. **Ensure upstream remote exists:**
   ```bash
   git remote -v | grep upstream || git remote add upstream https://github.com/leanprover-community/mathlib4.git
   ```
2. **Fetch upstream:**
   ```bash
   git fetch upstream
   ```
3. **Merge upstream master:**
   ```bash
   git merge upstream/master
   ```
4. If there are **merge conflicts**, resolve them:
   - For files only modified in upstream: accept theirs
   - For files modified in both: present conflicts to user for guidance
   - For files only modified locally: keep ours

### Step 3: Fetch Cached Artifacts (verification gate)

**CRITICAL: Always fetch the Mathlib cache before building**, otherwise compilation will take hours.

```bash
lake exe cache get
```

This downloads precompiled `.olean` files for all mathlib modules. Wait for it to complete before proceeding to build.

If `cache get` fails, try:
```bash
lake exe cache get!   # Force re-download
```

**Verification gate — do NOT skip:** before moving to Step 4 (build), verify the cache
fetch actually completed. Print this block with the timestamp:

```
✓ Cache fetched at <ISO timestamp>
  Last cache file mtime: <output of `find .lake/build -name "*.olean" -printf "%T+\n" | sort | tail -1`>
  Cache size: <output of `du -sh .lake/build` or equivalent>
```

If the timestamp is stale (older than the start of this command run), or `cache get` exited
non-zero, re-run before proceeding. A skipped cache fetch is the #1 cause of
multi-hour-stuck bump runs.

**If `cache get` fails with mismatched hashes** and the lakefile lists multiple dependencies (e.g. `mathlib` and `doc-gen4`) that share a transitive `Cli` requirement at different revisions: reorder so that `[[require]] mathlib` comes **last** in `lakefile.toml`. The last-listed `require` wins on transitive-version resolution, so Mathlib's pinned `Cli` version takes precedence and the cache hash matches. Re-run `lake update mathlib` then `lake exe cache get`.

### Step 4: Build and Collect Errors

Build the project/PR files and collect all errors:

```bash
lake build 2>&1 | tee /tmp/mathlib-bump-errors.log
```

**For mathlib PRs**, build only the files in the PR to save time:
```bash
# Find files changed in the PR
git diff --name-only upstream/master -- '*.lean' > /tmp/changed_files.txt

# Build only those files (convert paths to module names)
# e.g., Mathlib/Algebra/Group/Basic.lean → Mathlib.Algebra.Group.Basic
```

Also use `lean_diagnostic_messages` on each changed file for precise error locations.

Parse the build output and categorize errors:
- **Unknown identifier** - A name was removed or renamed
- **Type mismatch** - A signature changed
- **Failed to synthesize instance** - An instance was removed or restructured
- **Unknown namespace** - A namespace was renamed or removed
- **Unused import** - A file was moved or split
- **Other errors** - Anything else

### Step 5: Consult the Mathlib Changelog

**CRITICAL: Use the changelog to understand what changed.**

For each error involving a changed/missing name, fetch the changelog:

```
WebFetch: https://mathlib-changelog.org/v4
```

Search the changelog page for:
- The old name that's broken (e.g., `Finset.sum_congr`)
- The namespace that changed
- Recent deprecations

The changelog lists:
- **Renamed declarations** with old → new mappings
- **Removed declarations** with suggested replacements
- **API changes** (signature changes, new/removed arguments)
- **Moved declarations** (which file they're now in)

**Search strategy:**
1. Search for the exact broken identifier name
2. Search for the namespace prefix (e.g., if `Foo.bar` broke, search for `Foo`)
3. Search for the general area (e.g., "Finset", "Topology")

If the changelog doesn't have the answer, also try:
- `lean_loogle` to find the new name by type signature
- `lean_leansearch` to find replacements by description
- `grep` in `.lake/packages/mathlib/` for the old name (may find deprecation alias)

### Step 6: Fix Errors Iteratively

For each error, apply the appropriate fix:

#### Unknown Identifier / Renamed
```lean
-- Old name removed or renamed
-- 1. Check changelog for new name
-- 2. Check for deprecation alias:
#check @old_name  -- may show deprecation message

-- Apply rename
-- Before:
exact Finset.sum_congr rfl h
-- After (if renamed):
exact Finset.sum_congr_arg rfl h
```

#### Type Mismatch / Signature Change
```lean
-- A function's type changed (new argument, different order, etc.)
-- 1. Check changelog for details
-- 2. Check the new signature:
#check @the_function

-- Adapt call sites to new signature
```

#### Failed to Synthesize Instance
```lean
-- An instance was removed or its path changed
-- 1. Check if instance was moved to a different import
-- 2. Check if the type class hierarchy changed
-- 3. May need to add a new import or provide instance manually
```

#### Import Changes
```lean
-- A file was moved or split
-- 1. Check changelog for new location
-- 2. Update import path
-- Before:
import Mathlib.Data.Foo
-- After:
import Mathlib.Data.Foo.Basic
```

**After each fix:**
1. Re-check the file compiles: `lean_diagnostic_messages`
2. If the fix introduces new errors, address those too
3. Move to the next error

### Step 7: Verify Full Build

After all fixes:

```bash
lake build
```

Ensure zero errors. If errors remain, go back to Step 5.

### Step 8: Report

## Output Format

```
## Mathlib Bump Report

### Context
- Type: [Standalone project / Mathlib PR]
- Previous version: [commit hash or rev]
- New version: [commit hash or rev]

### Errors Found: N
| # | File | Error Type | Old Name/API | New Name/API | Status |
|---|------|-----------|-------------|-------------|--------|
| 1 | Foo.lean:45 | Renamed | `old_name` | `new_name` | ✓ Fixed |
| 2 | Bar.lean:12 | Signature | `f (a) (b)` | `f (a) (b) (c)` | ✓ Fixed |
| 3 | Baz.lean:78 | Import | `Mathlib.X` | `Mathlib.X.Basic` | ✓ Fixed |

### Changes Made
- [list of files modified and what changed]

### Compilation Status
✓ All files compile successfully after bump
```

## Tips

### Common Bump Breakage Patterns

1. **`simp` lemmas renamed** - Very common. Check changelog, often just a name change.
2. **Namespace reorganization** - Imports change. Follow the changelog. (e.g. `card_eq_pow_finrank` → `Module.card_eq_pow_finrank`.)
3. **New arguments added** - Functions gain new typeclass arguments. Usually inferred automatically; if not, provide explicitly.
4. **Deprecation removals** - If you were using a deprecated alias, it may have been removed after 6 months. Switch to the canonical name.
5. **Universe changes** - Rare but impactful. Check if universe parameters changed.
6. **Predicate refactor (binary → unary)** - A common shape: a predicate `P i x` taking a hom `i` and an object `x` is replaced by `P (x.map i)` (apply the hom first, then take the unary predicate). Affected APIs lose the hom-argument lemmas (e.g. `_id_iff_*` no longer needed). Concrete example from `v4.29.1`:
   - `Polynomial.Splits i f` (binary) → `Polynomial.Splits (f.map i)` (unary)
   - `splits_of_splits_of_dvd i hf hg dvd` → `Splits.of_dvd hg hf (Polynomial.map_dvd _ dvd)` — divisibility must be lifted through the hom by hand
   - `rw [← splits_id_iff_splits]; exact IsAlgClosed.splits _` → `exact IsAlgClosed.splits _` — the bridge lemma is obsolete
7. **Field-name `IsX` normalization** - Structure fields named `not_unit`, `is_unit`, etc. are being renamed to match the `IsUnit` / `IsX` predicate convention: `Irreducible.not_unit` → `Irreducible.not_isUnit`. When a field rename breaks, check whether the matching predicate has an `Is`-prefixed name and update accordingly.
8. **Primed variants for direct conclusions** - Look for a `'`-suffixed variant when an existing lemma needs awkward rearrangement. E.g. `List.le_maximum_of_mem` requires `(h_eq : maximum l = m)`; `List.le_maximum_of_mem'` returns `(a : WithBot α) ≤ maximum l` directly from membership alone.

### Efficient Debugging

- Fix errors **file by file**, starting from files with fewest dependencies
- After fixing imports, rebuild before tackling other errors (import fixes often resolve cascading errors)
- Use `lake build TargetModule` to build individual modules during iteration

## Reference

- **Mathlib Changelog**: https://mathlib-changelog.org/v4
- `lean_loogle` - Search by type signature when a name changed
- `lean_leansearch` - Search by description when looking for replacements

### Final Step: Record Learnings

After completing the bump and showing the report, capture what was learned.

**For each significant fix**, write a JSON entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "bump-mathlib",
  "type": "<api_rename|api_change|import_change|instance_change|deprecation_removal|other>",
  "before_code": "<code that broke, max 500 chars>",
  "after_code": "<fixed code, max 500 chars>",
  "pattern_tags": ["<relevant pattern names, e.g. 'rename', 'new_argument', 'moved_import'>"],
  "description": "<1-2 sentences: what changed in mathlib and how the fix was applied>",
  "math_area": "<analysis|algebra|topology|number_theory|combinatorics|order|category_theory|measure_theory|other>",
  "accepted": true,
  "source": "agent_suggestion",
  "context": {
    "file_path": "<relative path>",
    "theorem_name": "<if applicable>",
    "mathlib_commit": "<new mathlib commit hash>"
  }
}
```

**What to capture from bump-mathlib:**
- Each non-trivial API change that required manual fixing
- Patterns that appear across multiple files (e.g., same rename needed everywhere)
- Surprising changes not obvious from the changelog
- Fixes that required searching beyond the changelog

**What NOT to capture:**
- Simple import path updates
- Automatic deprecation renames (one-to-one swaps found directly in changelog)

**Keep it lightweight** - only 1-5 entries per command run, capturing the most interesting/novel breakage patterns.
