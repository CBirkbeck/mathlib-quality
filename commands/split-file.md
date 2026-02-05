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
3. User approves or modifies plan
4. Agent executes split incrementally
5. Agent verifies all files compile
6. User reviews and commits
```
