---
name: integrate-learnings
description: Process community learning contributions into reference docs
---

# /integrate-learnings — Integrate community learnings into the reference docs

For repo maintainers: process community learning contributions (from `/contribute`
PRs) into the skill's reference documentation. Contributions land as JSONL files in
`data/community_learnings/`; this command reads them, counts occurrences, and
propagates the eligible ones into `references/style-rules.md`,
`references/naming-conventions.md`, `references/proof-patterns.md`,
`references/pr-feedback-examples.md`, etc. — wherever the teaching belongs.

Workers read the reference docs directly. There is no RAG index, no MCP server,
no `merge_learnings.py`; the reference docs are the single source of truth.

## Usage

```
/integrate-learnings
/integrate-learnings --dry-run   (preview without modifying files)
```

## Prerequisites

- Must be run from within the mathlib-quality repo itself
- Community learnings exist in `data/community_learnings/*.jsonl`

## Workflow

### Step 1 — Load all contributions

```bash
ls data/community_learnings/*.jsonl
```

Parse each file (JSONL: one JSON object per line). Skip `.gitkeep`.

If no files found:

```
No community learnings to process in data/community_learnings/.
Contributions arrive via `/contribute` PRs from users.
```

### Step 2 — Validate and deduplicate

For each entry:

1. **Validate JSON structure** — must have required fields (`command`, `type`,
   `description`).
2. **Dedup** — same `before_code` + `after_code` is a duplicate (keep the most
   recent). For entries without code (pure teachings), dedup by `description`
   prefix.
3. **Filter** — drop entries with empty descriptions or missing `type`.

Report:

```
## Validation Report
- Total entries: 150
- Valid: 142
- Invalid (missing fields): 5
- Duplicates removed: 3
- Ready to integrate: 134
```

### Step 3 — Count occurrences (consensus filter)

Group validated entries by `pattern_tags`. Print the occurrence count:

```
| Pattern (representative description)  | Occurrences | Sources                                   | Eligible for ref docs? (≥3) |
|---------------------------------------|-------------|-------------------------------------------|------------------------------|
| junk_def / inline_def                 | 4           | 2026-05-03_mathlib4, 2026-04-21_mathlib4  | yes                          |
| splits_api / unary_predicate          | 3           | 2026-05-06 leanbridge bump (×3)           | yes                          |
| review-meta-pattern                   | 1           | 2026-04-29 loefflerd                      | no — single source           |
```

The 3+ rule is the **consensus filter**. Below threshold, a single-source teaching
does NOT propagate to the reference docs automatically — it goes through the
manual-review gate in Step 5 instead. The user can promote a single-source teaching
to the reference docs if the contributor has named-reviewer authority or the
teaching is a meta-rule that doesn't lend itself to repetition.

### Step 4 — Categorise for reference-doc integration

Group eligible entries by destination:

| Entry type | Destination |
|------------|-------------|
| `style_correction` (recurring) | `references/style-rules.md` |
| `naming_fix` (recurring) | `references/naming-conventions.md` |
| `golf_pattern` (with code) | `references/proof-patterns.md` (Anti-Patterns or Examples) |
| `mathlib_discovery` | `references/pr-feedback-examples.md` |
| `user_teaching` (general) | `references/proof-patterns.md` or `references/style-rules.md` (judge by content) |
| `failed_pattern` | `references/proof-patterns.md` § Anti-Patterns |
| `decomposition` | `examples/decompose_proof.md` |

### Step 5 — Manual-review gate (REQUIRES USER APPROVAL)

Some entries can't be auto-merged. Before completing Step 6, print the
`REQUIRES MANUAL REVIEW` block and **stop** until the user weighs in:

```
## REQUIRES MANUAL REVIEW — auto-integration paused

The following entries can't be merged automatically. Review each and tell me what
to do ("integrate as <pattern>", "drop", "modify and integrate"):

### Contradictions with existing reference docs
- <id>: pattern says X; existing rule in <file>:<section> says Y. Reconcile.

### Below-threshold patterns flagged as important
- <id>: only 1 occurrence but the contributor marked it as critical. Keep
  archived only, or promote to ref docs anyway?

### Ambiguous patterns (no clear before/after)
- <id>: description-only entry; no code example. Treat as guidance text in
  <file>? Or drop?

### Project-specific patterns (may not generalise)
- <id>: tagged as <project>-specific. Generic enough to add to ref docs, or skip?
```

Without user input on every item in this block, the integration is incomplete.
Don't proceed to Step 6 until the block is empty or every item has a user
decision logged.

### Step 6 — Apply to reference docs (only the eligible + user-approved patterns)

1. **Style rules** — add new rules to `references/style-rules.md`. New sections at
   sensible locations; never bury them at the bottom unless the doc has a "Misc"
   section.
2. **Naming conventions** — add new patterns to `references/naming-conventions.md`.
3. **Proof patterns** — add new entries to `references/proof-patterns.md`. If the
   teaching is an *anti-pattern*, put it under Anti-Patterns; if a positive
   pattern, under Examples.
4. **PR feedback examples** — add curated entries to
   `references/pr-feedback-examples.md` (the human-readable summary; workers read
   this directly).
5. **Decomposition examples** — add to `examples/decompose_proof.md`.

Only add patterns that:
- (a) appear in **3+ contributions** (community consensus), OR
- (b) Were user-approved in Step 5's manual-review gate.

Single-source teachings stay in `data/community_learnings/archived/` for record
but do not propagate to the reference docs.

### Step 7 — Archive processed files

Move processed contribution files to `data/community_learnings/archived/`:

```bash
mkdir -p data/community_learnings/archived
mv data/community_learnings/*.jsonl data/community_learnings/archived/
```

The archive is the durable record of every contribution received (not the
propagation channel — the reference docs are that).

## Output format

```
## Integration Report

### Input
- Contribution files: 5
- Total entries: 134
- After dedup: 128

### Reference Docs Updated
- style-rules.md: +2 rules (by-placement in match blocks, where-syntax for instances)
- naming-conventions.md: +1 pattern (Fin-related naming)
- proof-patterns.md: +3 entries (2 anti-patterns, 1 example)
- pr-feedback-examples.md: +3 examples

### Examples Updated
- examples/automation.md: +4 grind examples
- examples/inline_have.md: +2 examples

### Not integrated
- 8 entries: description-only teachings without code → recorded as archived only
- 3 entries: below-threshold (1 occurrence) → recorded as archived only
- 2 entries: contradicted existing rules → user dropped after review

### Archived
- Moved 5 files to data/community_learnings/archived/
```

## What this command does NOT do

- **Build a searchable index.** There is no RAG, no MCP server, no JSON dump. The
  reference docs are read by workers directly; that's the propagation channel.
- **Re-run on already-archived files.** Files in `archived/` are skipped. To
  re-process a teaching, move it back to `data/community_learnings/` and re-run.
- **Auto-resolve contradictions with existing reference docs.** Those land in the
  manual-review gate in Step 5; the user decides which version wins.

## Manual review items

Some entries need human judgment:

1. **Contradictions** — flag if a contributed pattern contradicts an existing rule.
2. **Project-specific** — some teachings may be project-specific, not universal.
3. **Ambiguous** — entries without clear before/after need interpretation.

These appear in Step 5's REQUIRES MANUAL REVIEW block. The user's decision is
binding.
