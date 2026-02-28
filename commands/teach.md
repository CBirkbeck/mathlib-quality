---
name: teach
description: Teach the skill a new pattern or project convention
---

# /teach - Teach a Pattern or Convention

Explicitly teach the mathlib-quality skill something it should remember for this project.

## Usage

```
/teach "always use grind before omega for Fin goals in this project"
/teach "in this codebase, prefer explicit universe variables"
/teach  (interactive mode - will prompt for input)
```

## What You Can Teach

### Project-Specific Conventions
```
/teach "always use grind before omega for Fin goals"
/teach "in this project, helper lemmas go in the Aux namespace"
/teach "we use Module.lean not Defs.lean for definition files"
```

### Golf Patterns Discovered
```
/teach "fun_prop closes Continuous goals about our custom FooMap after simp [FooMap]"
/teach "grind [bar_def] handles all Bar.card goals in one step"
```

### Before/After Examples
```
/teach
```
Then provide a before/after code example when prompted.

### Things to Avoid
```
/teach "don't use omega for goals involving Fin.castSucc - it loops"
/teach "aesop times out on goals with more than 3 Set.mem hypotheses in this project"
```

## Workflow

### Step 1: Parse the Teaching

Analyze the user's input to extract:
1. **The pattern or rule** being taught
2. **The category** (golf, style, naming, structure, avoidance)
3. **Any code examples** (before/after if provided)
4. **The math area** if identifiable

### Step 2: Categorize

Determine the learning type:

| Input Pattern | Type | Example |
|---------------|------|---------|
| "always/prefer/use X" | `user_teaching` | "always use grind for Fin goals" |
| "don't/avoid/never X" | `user_teaching` (negative) | "don't use omega for Fin.castSucc" |
| Before/after code | `golf_pattern` or `style_correction` | Code example pair |
| "in this project..." | `user_teaching` | Project convention |
| Naming preference | `naming_fix` | "use _aux not _helper" |

### Step 3: Write the Learning Entry

Write a structured entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "teach",
  "type": "user_teaching",
  "before_code": "<before code if provided, otherwise empty>",
  "after_code": "<after code if provided, otherwise empty>",
  "pattern_tags": ["<extracted pattern tags>"],
  "description": "<the teaching, preserved as close to the user's words as possible>",
  "math_area": "<detected area or 'other'>",
  "accepted": true,
  "source": "user_teaching",
  "context": {
    "file_path": "",
    "theorem_name": "",
    "project": "<project name from git remote if available>"
  }
}
```

### Step 4: Confirm

Show the user what was recorded:

```
Recorded learning:
- Type: user_teaching
- Pattern: use_grind
- Description: "Always try grind before omega for Fin goals in this project"
- Stored in: .mathlib-quality/learnings.jsonl

This will be used in future /cleanup and /golf-proof runs on this project.
```

## Interactive Mode

If `/teach` is invoked without arguments, prompt the user:

```
What would you like to teach? You can:

1. **State a rule**: "always prefer X over Y for Z goals"
2. **Show a before/after**: Paste code showing the pattern
3. **Flag an avoidance**: "don't use X because Y"
4. **Set a convention**: "in this project, use X for Y"

What's the teaching?
```

If the user provides a before/after example, ask:
```
What pattern does this demonstrate? (e.g., "use grind for membership goals")
```

## Output Format

```
## Teaching Recorded

**Type:** user_teaching
**Pattern tags:** use_grind, fin_goals
**Description:** Always try grind before omega for Fin goals in this project.
**Math area:** combinatorics

Stored in `.mathlib-quality/learnings.jsonl`. This will influence future suggestions.

To see all recorded learnings: check `.mathlib-quality/learnings.jsonl`
To contribute learnings back: `/contribute`
```

## Examples

### Teaching a Golf Pattern
```
> /teach "grind [Finset.card_filter] closes most Finset.card goals"

## Teaching Recorded

**Type:** user_teaching
**Pattern tags:** use_grind, finset_card
**Description:** grind [Finset.card_filter] closes most Finset.card goals
**Math area:** combinatorics

Stored in `.mathlib-quality/learnings.jsonl`.
```

### Teaching an Avoidance
```
> /teach "don't use aesop on goals with coercions - it loops in this project"

## Teaching Recorded

**Type:** user_teaching (avoidance)
**Pattern tags:** avoid_aesop, coercion_goals
**Description:** Don't use aesop on goals with coercions - it loops in this project.
**Math area:** other

Stored in `.mathlib-quality/learnings.jsonl`.
```

### Teaching with Before/After
```
> /teach
What would you like to teach?
> Here's a pattern: `simp [FooMap]; fun_prop` closes all Continuous goals about FooMap

## Teaching Recorded

**Type:** user_teaching
**Pattern tags:** use_fun_prop, simp_then_fun_prop
**Description:** simp [FooMap]; fun_prop closes all Continuous goals about FooMap
**Math area:** topology

Stored in `.mathlib-quality/learnings.jsonl`.
```
