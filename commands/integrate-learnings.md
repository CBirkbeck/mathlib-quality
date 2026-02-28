---
name: integrate-learnings
description: Process community learning contributions into reference docs and RAG index
---

# /integrate-learnings - Integrate Community Learnings

For repo maintainers: process community learning contributions (from `/contribute` PRs) into the reference docs and RAG index.

## Usage

```
/integrate-learnings
/integrate-learnings --dry-run   (preview without modifying files)
```

## Prerequisites

- Must be run from within the mathlib-quality repo itself
- Community learnings exist in `data/community_learnings/*.jsonl`

## Workflow

### Step 1: Load All Contributions

Read all JSONL files from `data/community_learnings/`:

```bash
ls data/community_learnings/*.jsonl
```

Parse each file and collect all entries into a single list.

If no files found:
```
No community learnings found in data/community_learnings/.
Contributions arrive via `/contribute` PRs from users.
```

### Step 2: Validate and Deduplicate

For each entry:
1. **Validate JSON structure** - must have required fields (command, type, description)
2. **Deduplicate** - same before_code + after_code = duplicate (keep most recent)
3. **Filter** - remove entries with empty descriptions or missing type

Report:
```
## Validation Report
- Total entries: 150
- Valid: 142
- Invalid (missing fields): 5
- Duplicates removed: 3
- Ready to integrate: 134
```

### Step 3: Categorize for Integration

Group validated entries by destination:

| Entry Type | Destination |
|------------|-------------|
| `golf_pattern` (accepted, with code) | RAG index (`data/pr_feedback/rag_index.json`) |
| `style_correction` (recurring) | `references/style-rules.md` |
| `naming_fix` (recurring) | `references/naming-conventions.md` |
| `mathlib_discovery` | `references/pr-feedback-examples.md` |
| `user_teaching` (general) | `references/proof-patterns.md` or style rules |
| `failed_pattern` | Negative examples in RAG index |
| `decomposition` | `examples/decompose_proof.md` |

### Step 4: Integrate into RAG Index

For golf patterns with before/after code:

1. Run `scripts/merge_learnings.py` to convert entries to RAG format
2. Merge into `data/pr_feedback/rag_index.json`
3. Update `data/pr_feedback/rag_index_focused.json` if patterns match existing categories

```bash
python3 scripts/merge_learnings.py --input data/community_learnings/ --output data/pr_feedback/rag_index.json
```

### Step 5: Update Reference Docs

For frequently recurring patterns (3+ occurrences across contributions):

1. **Style rules**: Add new rules to `references/style-rules.md`
2. **Naming conventions**: Add new patterns to `references/naming-conventions.md`
3. **PR feedback examples**: Add curated examples to `references/pr-feedback-examples.md`

Only add patterns that appear in multiple contributions (community consensus).

### Step 6: Update Example Files

For patterns with clear before/after:
- Golf patterns → appropriate `examples/*.md` file
- Decomposition patterns → `examples/decompose_proof.md`

### Step 7: Rebuild RAG Index

```bash
python3 scripts/build_rag_index.py
```

### Step 8: Archive Processed Files

Move processed contribution files to `data/community_learnings/archived/`:

```bash
mkdir -p data/community_learnings/archived
mv data/community_learnings/*.jsonl data/community_learnings/archived/
```

## Output Format

```
## Integration Report

### Input
- Contribution files: 5
- Total entries: 134
- After dedup: 128

### Integrated

#### RAG Index (+23 entries)
- Golf patterns added: 18
- Failed patterns added: 5
- New total: 1,928 examples

#### Reference Docs Updated
- style-rules.md: +2 rules (by-placement in match blocks, where-syntax for instances)
- naming-conventions.md: +1 pattern (Fin-related naming)
- pr-feedback-examples.md: +3 examples

#### Example Files Updated
- examples/automation.md: +4 grind examples
- examples/inline_have.md: +2 examples

### Not Integrated (Manual Review Needed)
- 8 entries lack code examples (description-only teachings)
- 3 entries have ambiguous patterns
- 2 entries contradict existing rules (flagged for review)

### Archived
- Moved 5 files to data/community_learnings/archived/
```

## Manual Review Items

Some entries need human judgment:

1. **Contradictions** - If a contributed pattern contradicts existing rules, flag it
2. **Project-specific** - Some teachings may be project-specific, not universal
3. **Ambiguous** - Entries without clear before/after need interpretation

These are listed in the report for maintainer review.
