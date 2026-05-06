---
name: split-file
description: Split large files (>1500 lines) into focused modules
---

# /split-file - Split Large Lean Files

Split a large Lean file (>1500 lines) into smaller, focused modules.

## Usage

```
/split-file [file_path]
```

## Splitting Strategy

### Step 1: Analyze the File

1. Get the file outline using `lean_file_outline`
2. List all declarations with their line numbers
3. Group declarations by naming prefix (e.g., `cauchyPrincipalValue*`, `residue*`)

### Step 2: Identify Natural Groupings

Group declarations by the **object they work on**, identified by naming patterns:

| Prefix Pattern | Suggested File |
|----------------|----------------|
| `cauchyPrincipalValue*` | `CauchyPrincipalValue.lean` |
| `residue*`, `Residue*` | `Residue.lean` |
| `pv_*`, `PV*` | `PrincipalValue.lean` |
| `winding*`, `Winding*` | `WindingNumber.lean` |
| `integral_*` | `Integration.lean` |
| Core definitions | `Basic.lean` or `Defs.lean` |

### Step 3: Determine Split Structure

**Option A: Two-file split** (for 1500-3000 lines)
```
Module/
├── Basic.lean      -- Core definitions + simple lemmas
└── Theorems.lean   -- Main results (imports Basic)
```

**Option B: Multi-file split** (for >3000 lines)
```
Module/
├── Defs.lean       -- Core definitions only
├── Basic.lean      -- API lemmas (imports Defs)
├── Topic1.lean     -- Grouped lemmas (imports Basic)
├── Topic2.lean     -- Grouped lemmas (imports Basic)
└── Main.lean       -- Main theorems (imports all above)
```

### Step 4: Execute the Split

For each new file:

1. **Create the file** with proper header:
```lean
/-
Copyright (c) 2024 [Author]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Author]
-/
import [necessary imports]

/-!
# [Module Title]

[Brief description]

## Main definitions/results

* `foo`: Description
-/
```

2. **Move declarations** preserving order (dependencies must come before dependents)

3. **Update imports** in all affected files

4. **Verify each file compiles** before proceeding to next

### Step 5: Verify

1. Run `lake build` on each new file
2. Ensure no circular imports
3. Check that downstream files still compile

## Example: Splitting ResidueTheory.lean

**Before:** `ResidueTheory.lean` (2969 lines)

**Analysis:**
- `cauchyPrincipalValue*` declarations: ~800 lines
- `residue*` declarations: ~600 lines
- Main theorems: ~400 lines
- Supporting lemmas: ~1100 lines

**After:**
```
ResidueTheory/
├── CauchyPrincipalValue.lean  -- PV definitions & lemmas (~800 lines)
├── Residue.lean               -- Residue definitions & lemmas (~600 lines)
├── Integration.lean           -- Integration helpers (~500 lines)
└── ResidueTheorem.lean        -- Main theorems (imports above, ~400 lines)
```

## Important Rules

1. **Preserve declaration order** - Dependencies must come before dependents
2. **No circular imports** - Lower files import higher, not vice versa
3. **Each file should compile independently**
4. **Keep related items together** - Don't split a definition from its basic API
5. **Update all downstream imports** - Check what imports the original file
6. **Maximum 1500 lines per file** - Split further if needed

## Naming Conventions for Split Files

| File Type | Naming |
|-----------|--------|
| Definitions only | `Defs.lean` |
| Basic API | `Basic.lean` |
| Topic-specific | `TopicName.lean` (UpperCamelCase) |
| Main theorems | `Main.lean` or original name |

## Workflow

```
1. /split-file path/to/LargeFile.lean
2. Agent analyzes and proposes split structure
3. STOP — wait for explicit user approval (mandatory pause)
4. Agent executes split incrementally
5. Agent verifies all files compile
6. User reviews and commits
```

### Step 3 — Awaiting user approval (mandatory pause)

After producing the proposed split structure, **stop**. Do not start writing new files.
Print this exact line:

```
AWAITING USER APPROVAL ON SPLIT PLAN — reply "approve" / "go ahead" / "looks good" to
execute the split, or describe changes you want first.
```

Then wait. Possible responses:
- **Approve** → proceed to step 4
- **Change** ("rename file X to Y", "move declarations A and B to a different module",
  "merge groups C and D") → update the plan, re-print it, wait again
- **Cancel** → leave the original file untouched; user can resume later

A split is a high-blast-radius operation (creates new files, edits imports, may break
downstream). Never auto-execute without explicit approval. The plan is approved by the
user, not by you.

### Step 5 — Per-file verification gate

After writing each new file, run `lean_diagnostic_messages` on it before moving to the
next. If the new file has errors, fix them before proceeding. Do not accumulate broken
files.

Final verification: `lake build` must succeed on the affected modules. If the user has CI,
also note that any cross-file rename may need a follow-up pass. Print:

```
✓ All N split files compile
✓ lake build succeeded on affected modules
✓ Original file is empty / removed (whichever was planned)
```

If any check fails, do NOT mark the split as done — list what's broken and stop.

### Final Step: Record Learnings

After completing the split and verifying compilation, capture what was learned.

**For each file split**, write a JSON entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "split-file",
  "type": "file_split",
  "before_code": "<original file name and line count>",
  "after_code": "<resulting file structure: names and line counts>",
  "pattern_tags": ["<e.g. split_by_prefix, split_by_topic, defs_and_theorems>"],
  "description": "<1-2 sentence description of the splitting strategy and groupings chosen>",
  "math_area": "<analysis|algebra|topology|number_theory|combinatorics|order|category_theory|measure_theory|other>",
  "accepted": true,
  "source": "<agent_suggestion|user_correction>",
  "context": {
    "file_path": "<relative path to original file>",
    "theorem_name": ""
  }
}
```

**What to capture from split-file:**
- The splitting strategy used (by naming prefix, by topic, defs vs theorems, etc.)
- How declarations were grouped and why
- Any dependency challenges encountered

**What NOT to capture:**
- The mechanical details of moving code between files
- Import updates

**Keep it lightweight** - typically 1 entry per split describing the overall strategy.
