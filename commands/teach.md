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

### Step 4: Confirm and Warn About Contribution

Show the user what was recorded, and **warn them that it will be contributed**:

```
Recorded learning:
- Type: user_teaching
- Pattern: use_grind
- Description: "Always try grind before omega for Fin goals in this project"
- Stored in: .mathlib-quality/learnings.jsonl

⚠️  This teaching will be automatically contributed to the mathlib-quality
    community repo (github.com/CBirkbeck/mathlib-quality) so all users
    can benefit. File paths will be anonymized. Code snippets in
    before/after examples will be included as-is.

    Proceed with contribution? [y/n]
```

**If the user declines**, skip the contribution but keep the local learning:
```
Teaching saved locally only. You can contribute later with /contribute.
```

### Step 5: Auto-Contribute

If the user confirms (or does not decline), automatically contribute the teaching to the community repo.

**5a. Sanitize the entry for contribution:**
- Strip full file paths → keep filename only
- Replace project-specific names with generic identifiers if the user requests
- Keep code snippets as-is (they demonstrate the pattern)

**5b. Generate the contribution file:**

Determine project identifier:
```bash
git remote get-url origin 2>/dev/null | sed 's/.*\///' | sed 's/\.git$//'
```

File name: `data/community_learnings/<date>_<project-hash>.jsonl`
- Append the new teaching entry to the file if it already exists for today
- Create a new file otherwise

**5c. Create or update the PR:**

```bash
# Check if there's already an open learnings PR for this project
EXISTING_PR=$(gh pr list --repo CBirkbeck/mathlib-quality --state open \
  --search "learnings: patterns from" --json number,headRefName \
  --jq '.[0].headRefName // empty')

if [ -n "$EXISTING_PR" ]; then
  # Push to the existing branch to update the PR
  git checkout "$EXISTING_PR"
  # Append new entry, commit, push
else
  # Create new branch and PR
  BRANCH="learnings/$(date +%Y%m%d)-$(head -c 8 /dev/urandom | xxd -p | head -c 8)"
  gh pr create \
    --repo CBirkbeck/mathlib-quality \
    --title "learnings: teaching from $(date +%Y-%m-%d)" \
    --body "## Community Teaching Contribution

### Entry
- **Type:** user_teaching
- **Pattern:** [pattern tags]
- **Description:** [the teaching]

---
Auto-contributed by mathlib-quality \`/teach\` command."
fi
```

**5d. Report the result:**
```
✓ Teaching contributed to community repo.
  PR: https://github.com/CBirkbeck/mathlib-quality/pull/XX

  The maintainers will review and integrate this into the reference docs.
```

If the contribution fails (network error, auth issue):
```
Teaching saved locally in .mathlib-quality/learnings.jsonl.
⚠️  Auto-contribution failed: [reason]
    You can retry later with /contribute.
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

⚠️  This teaching will be auto-contributed to the community repo.
    File paths will be anonymized. Code snippets included as-is.
    Proceed? [y/n]

> y

✓ Contributed to community repo.
  PR: https://github.com/CBirkbeck/mathlib-quality/pull/XX
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

⚠️  This will be auto-contributed to the community repo. Proceed? [y/n]
> y
✓ Contributed: PR #42
```

### Teaching an Avoidance
```
> /teach "don't use aesop on goals with coercions - it loops in this project"

## Teaching Recorded

**Type:** user_teaching (avoidance)
**Pattern tags:** avoid_aesop, coercion_goals
**Description:** Don't use aesop on goals with coercions - it loops in this project.
**Math area:** other

⚠️  This will be auto-contributed to the community repo. Proceed? [y/n]
> n
Teaching saved locally only. Contribute later with /contribute.
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

⚠️  This will be auto-contributed to the community repo. Proceed? [y/n]
> y
✓ Contributed: PR #43
```
