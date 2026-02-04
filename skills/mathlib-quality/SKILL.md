# Mathlib Quality Skill

## Activation Triggers

This skill activates when:
- Working with `.lean` files intended for mathlib contribution
- User mentions "mathlib style", "cleanup", "golf", "PR submission", or "pre-submit"
- User asks to fix reviewer feedback on a mathlib PR
- User wants to check code against mathlib conventions

## Overview

This skill helps bring Lean 4 code up to mathlib standards by:
1. Enforcing style rules (line length, formatting, indentation)
2. Checking naming conventions
3. Ensuring proper documentation
4. Golfing proofs to be shorter and cleaner
5. Preparing code for PR submission

## Available Commands

| Command | Description |
|---------|-------------|
| `/cleanup` | Full file cleanup to mathlib standards |
| `/check-style` | Validate without making changes |
| `/golf-proof` | Optimize specific proofs |
| `/pre-submit` | Pre-PR submission checklist |
| `/fix-pr-feedback` | Address reviewer comments |

## Core Style Rules (Quick Reference)

### File Structure
- **Line length**: 100 characters max
- **File length**: 1500 lines max (prefer splitting)
- **Header order**: Copyright, module docstring, imports

### Formatting
- **Indentation**: 2 spaces for tactic blocks
- **Prefer**: `fun` over `λ`, `<|` over `$`
- **Prefer**: `change` over `show` in proofs
- **No trailing whitespace**

### Naming Conventions
- **Lemmas/theorems**: `snake_case`
- **Types/structures**: `UpperCamelCase`
- **Type variables**: `α`, `β`, `γ` (then `ι`, `κ`)
- **Hypotheses**: `h`, `h₁`, `h₂` or descriptive `hf`, `hg`
- **Instances**: `i` prefix or descriptive

### Documentation Requirements
- Module docstring after imports
- Docstrings for public declarations
- Brief, clear descriptions

## Workflow Guidance

### When Preparing a PR

1. **First pass**: Run `/check-style` to see all issues
2. **Apply fixes**: Run `/cleanup` to auto-fix what's possible
3. **Golf proofs**: Run `/golf-proof` on verbose proofs
4. **Final check**: Run `/pre-submit` before creating PR

### When Handling PR Feedback

1. Copy reviewer comments or provide PR number
2. Run `/fix-pr-feedback`
3. Verify each fix compiles
4. Re-run `/pre-submit` before pushing

## Reference Files

For detailed guidance, see:
- `references/style-rules.md` - Complete formatting rules
- `references/naming-conventions.md` - Naming patterns
- `references/proof-patterns.md` - Proof golf techniques
- `references/pr-feedback-examples.md` - Real feedback examples
- `references/linter-checks.md` - Automated linter rules

## Integration with Lean 4 Tools

This skill works alongside the `lean4-theorem-proving` skill:
- Use Lean LSP tools to verify changes compile
- Use `lean_diagnostic_messages` to check for errors after edits
- Use `lean_goal` to verify proof state during golfing

## Common Mistakes to Avoid

1. **Overly long lines** - Break at operators, align continuations
2. **Unnecessary `have` blocks** - Inline simple terms
3. **Non-descriptive names** - Use conclusion-of-hypotheses pattern
4. **Missing docstrings** - Every public declaration needs one
5. **`simp` without arguments** - Use `simp only [...]` in library code
6. **Trailing `sorry`** - Remove all before submission
7. **Debug options** - Remove `set_option trace.*`
