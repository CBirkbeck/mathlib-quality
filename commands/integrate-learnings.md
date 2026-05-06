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

#### 5a. Count occurrences (required artifact)

Print the occurrence count for every distinct `pattern_tags` set:

```
| Pattern (representative description) | Occurrences | Sources                                   | Eligible for ref docs? (≥3) |
|--------------------------------------|-------------|-------------------------------------------|------------------------------|
| junk_def / inline_def                | 4           | 2026-05-03_mathlib4, 2026-04-21_mathlib4  | yes                          |
| splits_api / unary_predicate         | 3           | 2026-05-06 leanbridge bump (×3)            | yes                          |
| review-meta-pattern                  | 1           | 2026-04-29 loefflerd                      | no — single source           |
| ...                                  |             |                                           |                              |
```

The 3+ rule is the consensus filter; below threshold and a pattern stays in the RAG index
but does NOT propagate to the reference docs. Patterns with 1–2 occurrences from a single
contributor are NOT community consensus.

#### 5b. Apply to reference docs (only the eligible patterns)

1. **Style rules**: Add new rules to `references/style-rules.md`
2. **Naming conventions**: Add new patterns to `references/naming-conventions.md`
3. **PR feedback examples**: Add curated examples to `references/pr-feedback-examples.md`

Only add patterns that appear in multiple contributions (community consensus).

#### 5c. Manual-review gate (REQUIRES USER APPROVAL)

Some entries can't be auto-merged. Before completing Step 5, print the
`REQUIRES MANUAL REVIEW` block and **stop** until the user weighs in:

```
## REQUIRES MANUAL REVIEW — auto-integration paused

The following entries can't be merged automatically. Review each and tell me what to do
("integrate as <pattern>", "drop", "modify and integrate"):

### Contradictions with existing reference docs
- <id>: pattern says X; existing rule in <file>:<section> says Y. Reconcile.

### Below-threshold patterns flagged as important
- <id>: only 1 occurrence but the contributor marked it as critical. Keep in RAG only?
  Or promote to ref docs anyway?

### Ambiguous patterns (no clear before/after)
- <id>: description-only entry; no code example. Treat as guidance text in <file>?
  Or drop?

### Project-specific patterns (may not generalise)
- <id>: tagged as <project>-specific. Generic enough to add to ref docs, or skip?
```

Without user input on every item in this block, the integration is incomplete. Don't
proceed to Step 6 until the block is empty or every item has a user decision logged.

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
