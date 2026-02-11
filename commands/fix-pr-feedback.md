---
name: fix-pr-feedback
description: Address PR reviewer comments
---

# /fix-pr-feedback - Handle PR Reviewer Comments

Parse and address feedback from mathlib PR reviews.

## Usage

```
/fix-pr-feedback <PR_number>
/fix-pr-feedback --comments "<pasted comments>"
```

## Workflow

### Step 1: Gather Feedback

**From PR number:**
```bash
gh pr view <PR_number> --repo leanprover-community/mathlib4 --json comments
gh api repos/leanprover-community/mathlib4/pulls/<PR_number>/comments
```

**From pasted comments:**
Parse the provided text for actionable feedback.

### Step 2: Categorize Feedback

Group comments by type:

| Category | Examples |
|----------|----------|
| **Style** | Line length, formatting, whitespace |
| **Naming** | Rename declaration, follow convention |
| **Documentation** | Add docstring, improve description |
| **Proof Golf** | Shorter proof, use automation |
| **API Design** | Change visibility, add lemma, namespace |
| **Correctness** | Bug in logic, wrong type |

### Step 3: Prioritize

Order by importance:
1. 🔴 **Correctness** - Must fix, affects functionality
2. 🔴 **Required changes** - Reviewer explicitly requires
3. 🟡 **Style/conventions** - Standard compliance
4. 🟢 **Suggestions** - Nice to have

### Step 4: Address Each Item

For each feedback item:

1. **Understand** - What exactly is being requested?
2. **Locate** - Find the relevant code
3. **Plan** - Determine the fix
4. **Apply** - Make the change
5. **Verify** - Ensure it compiles
6. **Note** - Record what was done

### Step 5: Verify All Changes

After all fixes:
```bash
lake build  # Ensure compilation
lake exe runLinter  # Check linters
```

### Step 6: Report

Generate summary of changes made.

## Output Format

```
## PR Feedback Resolution: #1234

### Feedback Summary
- Total comments: 8
- Actionable items: 6
- Questions to clarify: 2

### Changes Made

#### Style (3 items)
1. ✓ Line 45: Shortened line to 98 chars (was 115)
2. ✓ Line 67: Fixed indentation (4→2 spaces)
3. ✓ Line 89: Changed λ to fun

#### Naming (1 item)
1. ✓ Renamed `lemma1` to `add_pos_of_pos` (Line 56)

#### Documentation (1 item)
1. ✓ Added docstring to `importantDef` (Line 78)

#### Proof Golf (1 item)
1. ✓ Simplified proof of `foo_bar` using ring tactic (Line 90-95)

### Questions for Reviewer
1. Line 120: "Should this be an instance or a def?" - Need clarification
2. Line 145: "Consider adding X" - Is this required or optional?

### Compilation Status
✓ All changes compile successfully
✓ No new linter warnings

### Next Steps
1. Push changes: `git push`
2. Reply to reviewer comments explaining changes
3. Wait for re-review
```

## Common Feedback Patterns

### "Please shorten this line"
```lean
-- Find line, break appropriately
-- Before
theorem very_long_name (h₁ : hyp1) (h₂ : hyp2) (h₃ : hyp3) : conclusion := by ...

-- After
theorem very_long_name
    (h₁ : hyp1) (h₂ : hyp2) (h₃ : hyp3) : conclusion := by
  ...
```

### "Please add a docstring"
```lean
-- Before
def foo (x : α) : β := ...

-- After
/-- Brief description of what foo does.

Longer explanation if needed. -/
def foo (x : α) : β := ...
```

### "This can be golfed"
```lean
-- Look for automation or term mode
-- Before
theorem foo : P := by
  have h := bar
  exact h

-- After
theorem foo : P := bar
```

### "Please rename to X"
```lean
-- Rename and check all usages
-- Update any references in docstrings
```

### "Use simp only"
```lean
-- Before
theorem foo : ... := by simp

-- After
theorem foo : ... := by simp only [relevant_lemmas]
```

### "This should be in namespace X"
```lean
-- Move declaration into namespace
-- Update any qualified references
```

## Handling Unclear Feedback

If feedback is unclear:
1. Quote the specific comment
2. Explain your interpretation
3. Ask for clarification if needed
4. Make your best attempt if confident

## Responding to Reviewers

Template for PR comment after fixes:
```markdown
Thanks for the review! I've addressed the feedback:

- Fixed line lengths on lines 45, 67, 89
- Renamed `lemma1` to `add_pos_of_pos`
- Added docstring to `importantDef`
- Golfed proof of `foo_bar`

Questions:
- Regarding the comment on line 120, should this be an instance or a def?

Ready for re-review.
```

## Reference

See `references/pr-feedback-examples.md` for curated examples of common feedback patterns and their solutions.
