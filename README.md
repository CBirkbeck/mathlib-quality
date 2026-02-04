# Mathlib Quality

A Claude Code skill plugin for cleaning up, golfing, and bringing Lean 4 code up to mathlib standards before PR submission.

## Installation

### From GitHub (Recommended)

```bash
claude /plugin marketplace add CBirkbeck/mathlib-quality
```

### Local Installation

```bash
claude /plugin install ~/mathlib-quality
```

## Features

### Commands

| Command | Description |
|---------|-------------|
| `/cleanup` | Full file cleanup to mathlib standards |
| `/check-style` | Validate code against style rules (no changes) |
| `/golf-proof` | Optimize and shorten proofs |
| `/pre-submit` | Pre-PR submission checklist |
| `/fix-pr-feedback` | Address PR reviewer comments |

### What It Checks

- **Style**: Line length, indentation, whitespace, syntax preferences
- **Naming**: Convention compliance, descriptive names
- **Documentation**: Module docstrings, declaration docstrings
- **Code Quality**: No `sorry`, no debug options, proper `simp` usage
- **Proof Optimization**: Opportunities for automation and simplification

## Usage Examples

### Preparing Code for PR

```
# Check style issues
/check-style MyFile.lean

# Apply automatic fixes
/cleanup MyFile.lean

# Optimize proofs
/golf-proof theorem_name

# Final verification
/pre-submit MyFile.lean
```

### Handling PR Feedback

```
# Process feedback from PR #1234
/fix-pr-feedback 1234

# Or paste specific comments
/fix-pr-feedback --comments "Please shorten line 45..."
```

## Reference Documentation

The `skills/mathlib-quality/references/` directory contains detailed guidance:

- **style-rules.md** - Complete formatting and style rules
- **naming-conventions.md** - Naming patterns and conventions
- **proof-patterns.md** - Proof golfing techniques
- **pr-feedback-examples.md** - Common feedback patterns
- **linter-checks.md** - Mathlib linter rules

## Scripts

### Style Checker

Local style validation:

```bash
./scripts/style_checker.sh MyFile.lean
./scripts/style_checker.sh --all  # Check all .lean files
```

### PR Feedback Scraping

Scrape PR feedback for reference (privacy-preserving):

```bash
python scripts/scrape_pr_feedback.py
python scripts/categorize_feedback.py
```

**Privacy Note**: The scraping scripts do NOT collect personal information (names, usernames, emails). Only technical content is extracted.

## Quick Reference

### Style Rules

- Line length: **100 chars max**
- File length: **1500 lines max**
- Indentation: **2 spaces** for tactic blocks
- Use `fun` not `λ`
- Use `<|` not `$`
- Use `simp only [...]` not bare `simp`

### Naming Conventions

- Lemmas/theorems: `snake_case`
- Types/structures: `UpperCamelCase`
- Pattern: `conclusion_of_hypothesis`
- Hypotheses: `h`, `h₁`, `hf`, `hx`

### Required Documentation

- Module docstring after imports
- Docstrings for public declarations
- Copyright header at file start

## Integration

This skill works alongside the `lean4-theorem-proving` skill:

- Uses Lean LSP tools to verify changes compile
- Uses `lean_diagnostic_messages` to check for errors
- Uses `lean_goal` to verify proof state during golfing

## Contributing

1. Fork the repository
2. Make changes
3. Test locally: `claude /plugin install ~/mathlib-quality`
4. Submit PR

## License

MIT License - See LICENSE file
