---
name: overview
description: Generate project declaration inventory for consolidation analysis
---

# /overview - Project Declaration Inventory

Generate a structured overview of every declaration in the project, showing what each does, how it's proven, and what it depends on. Use this to find consolidation opportunities, junk definitions, and missing API.

## Usage

```
/overview [directory_or_file]
```

If no argument, scans all `.lean` files in the current project (excluding `.lake/`).
If a directory, scans all `.lean` files in that directory recursively.
If a single file, analyzes just that file.

Output: writes `PROJECT_OVERVIEW.md` in the project root.

---

## Step 1: Find Files

Find all `.lean` files in the project (excluding `.lake/`, `build/`):

```bash
find . -name "*.lean" -not -path "./.lake/*" -not -path "./build/*" | sort
```

Print the file list.

---

## Step 2: Dispatch Per-File Analysis Agents

For each file (or batch of 2-3 small files), dispatch a worker agent.

**Worker agent prompt:**

```
Analyze all declarations in [file_path]. Read the file completely.

For EVERY declaration (def, lemma, theorem, instance, structure, class, abbrev),
produce an entry in EXACTLY this format:

### `[kind] [name] : [abbreviated type]`
- **What**: [one sentence — what it defines/proves, in plain math language]
- **How**: [one sentence — key proof technique or construction method]
- **Uses**: [list of OTHER declarations from THIS file that appear in the proof/definition body]
- **Visibility**: [public / private / scoped]
- **Lines**: [line range, total lines]

Rules:
- "What" should be plain language, not just restating the type. E.g., "The Cauchy principal
  value integral of f" not "A function from ℝ to ℂ"
- "How" should name the KEY technique: "dominated convergence", "compactness + continuity",
  "by grind", "unfold + fun_prop", "case split on finiteness", etc.
  For definitions, describe the construction: "defined as the limit of...", "the set of all..."
- "Uses" means project declarations only (from this file), NOT mathlib imports.
  List each one. If none, write "none (mathlib only)"
- Keep type signatures abbreviated — show the shape, not every hypothesis.
  E.g., `Continuous fooBar` not the full 5-line signature.

Also note:
- Any `set_option maxHeartbeats` or `set_option maxRecDepth` on the declaration
- Proof length if >15 lines

At the end, add a section:

### File Summary
- Total declarations: N (X defs, Y lemmas/theorems, Z instances)
- Declarations not used by anything else in this file: [list names]
- Declarations used by 3+ others: [list names — these are key API]

Return ONLY the structured output, no commentary.
```

Dispatch file analysis agents in parallel (up to 5-6 at a time for large projects).

---

## Step 3: Collect and Assemble

After all workers complete, assemble the full overview document:

```markdown
# Project Overview: [project_name]

Generated: [date]

## Summary
- Files: N
- Definitions: X
- Lemmas/Theorems: Y
- Instances: Z
- Total declarations: T

## Table of Contents
- [File1.lean](#file1)
- [File2.lean](#file2)
...

---

## File: [path/to/File1.lean]

[paste worker output for File1]

---

## File: [path/to/File2.lean]

[paste worker output for File2]

---

...
```

---

## Step 4: Cross-File Dependency Analysis

After assembling all files, scan for cross-file dependencies:

1. For each file, check its `import` lines for project-internal imports
2. Build a simple dependency summary:

```markdown
## Cross-File Dependencies

### Import Graph
- `File1.lean` imports: [nothing / File2, File3]
- `File2.lean` imports: [File1]
- `File3.lean` imports: [File1, File2]

### Key Declarations Used Across Files
- `fooBar` (File1): used in File2 (3 times), File3 (5 times) — core API
- `myHelper` (File1): used in File2 only (1 time) — candidate for inlining
```

To find cross-file usage, grep for declaration names from each file across all other files.

---

## Step 5: Consolidation Analysis

Add a final section analyzing the overview for improvement opportunities. Look for:

### A. Generalization Candidates

Scan for declarations with:
- Similar names (e.g., `foo_for_real`, `foo_for_complex` → parametric `foo`)
- Similar type patterns (e.g., both prove `Continuous _` with similar hypotheses)
- Similar proof structures (same sequence of tactics/lemmas)

```markdown
### Generalization Candidates

1. **`bound_for_f` + `bound_for_g`** (File1.lean)
   - Both prove `‖_ x‖ ≤ C` with identical proof structure
   - → Generalize to `norm_bound (h : Property φ) : ‖φ x‖ ≤ C`

2. **`foo_continuous_real` + `foo_continuous_complex`** (File2.lean)
   - Same proof, different scalar fields
   - → Parametrize over `{𝕜 : Type*} [NontriviallyNormedField 𝕜]`
```

### B. Junk / Removable Declarations

Flag declarations that are:
- **Unused**: not referenced by any other declaration in the project
- **Wrapper lemmas**: just call 1-2 mathlib lemmas (should be inlined at call sites)
- **Overly specific**: only used once and could be inlined
- **Duplicating mathlib**: note candidates for `/check-mathlib`

```markdown
### Potentially Removable

1. **`def myHelper`** (File1.lean, line 30)
   - Used only once, by `main_theorem`
   - Could be inlined or replaced with local `let`

2. **`lemma bridge_result`** (File2.lean, line 50)
   - Just calls `Continuous.comp` then `foo_continuous`
   - Inline at the 2 call sites instead
```

### C. Missing API / Repeated Patterns

Look for patterns that appear in multiple proofs:
- Same `have` block appearing in 2+ proofs → extract as shared lemma
- Same proof structure repeated → identify the missing abstraction
- Proofs that would be simpler if a certain lemma existed

```markdown
### Missing API

1. **`continuity_of_composition`** — pattern appears in 4 proofs
   - Lines: File1:45, File1:80, File2:30, File3:55
   - All prove `Continuous (f ∘ g)` with similar setup
   - → Add a shared lemma

2. **`bound_from_compactness`** — used manually in 3 proofs
   - Always: get compact set, apply extreme value, extract bound
   - → Add helper that wraps this pattern
```

---

## Step 6: Write the Overview

Write the complete document to `PROJECT_OVERVIEW.md` in the project root.

Print a summary to the conversation:

```
## Overview Complete

Wrote PROJECT_OVERVIEW.md

### Quick Stats
- Files: N, Declarations: M
- Unused declarations: K (candidates for removal)
- Generalization candidates: G pairs
- Missing API patterns: P

### Top Priorities
1. [most impactful consolidation opportunity]
2. [second most impactful]
3. [third]
```

---

## Reference

For checking if declarations duplicate mathlib, use `/check-mathlib`.
For cleaning up individual files after consolidation, use `/cleanup`.
For decomposing long proofs found during review, use `/decompose-proof`.
