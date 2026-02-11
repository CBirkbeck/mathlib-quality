# Claude Context: mathlib-quality

## Project Purpose
A Claude Code skill plugin for cleaning up, golfing, and bringing Lean 4 code up to mathlib standards before PR submission.

## Current Status
**Version:** 0.1.0 (Initial commit)

### Completed
- Plugin architecture with 5 commands defined in `commands/`
- Reference documentation in `skills/mathlib-quality/references/`
- Data collection scripts in `scripts/`
- Lean 4 integration docs in `.claude/docs/lean4/`

### In Progress / TODO
1. **Testing the Plugin** - Need to verify commands work in Claude Code with actual Lean files

### Data Collection - COMPLETED (2026-02-04)
**PR Feedback Scraping:**
- Scraped 1,500 merged PRs from leanprover-community/mathlib4
- Collected 4,986 human reviewer feedback items (bot comments filtered)
- **2,588 GitHub suggestion blocks with before/after code** (gold data!)

**Data Files:**
| File | Items | Description |
|------|-------|-------------|
| `suggestions_before_after.json` | 2,588 | Before/after code examples |
| `proof_golf_feedback.json` | 2,786 | Proof simplification |
| `api_design_feedback.json` | 1,471 | API design comments |
| `style_feedback.json` | 997 | Style feedback |
| `general_feedback.json` | 880 | General comments |
| `documentation_feedback.json` | 435 | Doc feedback |
| `naming_feedback.json` | 191 | Naming feedback |
| `imports_feedback.json` | 176 | Import feedback |
| `performance_feedback.json` | 43 | Performance feedback |

### Recently Completed (2026-02-04)
- Updated `style-rules.md` with official mathlib conventions (variable conventions, `by` placement, terminal simp rules, API transparency, deprecation, etc.)
- Updated `naming-conventions.md` with comprehensive symbol tables, American English spelling, acronym rules
- Updated `pr-feedback-examples.md` with full review categories (style, naming, docs, location, improvements, library integration)
- Created new `mathlib-search.md` with Loogle patterns, search strategies, import guidelines
- **Data Analysis Complete:**
  - Deduplicated suggestions: 2,481 unique (from 2,588 raw)
  - 1,779 suggestions with actual before code
  - Created `analyze_suggestions.py` for categorized pattern extraction
  - Generated `clean_examples_by_category.json` with 44 curated examples
  - Added real PR review examples to `pr-feedback-examples.md`
  - Pattern analysis: 509 `+by`, 311 `-simp`, 169 `-rfl` (term mode conversions)

## Key Files

| File | Purpose |
|------|---------|
| `.claude-plugin/plugin.json` | Plugin manifest and command definitions |
| `skills/mathlib-quality/SKILL.md` | Main skill activation triggers |
| `commands/*.md` | Individual command implementations |
| `skills/mathlib-quality/references/*.md` | Style rules, naming, patterns |
| `scripts/scrape_pr_feedback.py` | GitHub PR feedback scraper |
| `scripts/categorize_feedback.py` | Feedback pattern analyzer |
| `scripts/analyze_suggestions.py` | Before/after suggestion analyzer |
| `scripts/style_checker.sh` | Local Lean file style validation |

## Commands Available
- `/cleanup` - Full file cleanup to mathlib standards
- `/check-style` - Style validation (non-destructive)
- `/golf-proof` - Proof optimization
- `/pre-submit` - Pre-PR submission checklist
- `/fix-pr-feedback` - Address reviewer comments

## Next Steps
1. ~~Run `scrape_pr_feedback.py` to collect real PR review data from mathlib4~~ ✅
2. ~~Run `categorize_feedback.py` to analyze patterns~~ ✅
3. ~~Update `pr-feedback-examples.md` with real curated examples~~ ✅
4. **Test all commands with actual Lean files** (current priority)
5. Consider adding more automation tactics to proof-patterns.md
6. Fine-tune categorization to extract more golf/style patterns

## Notes
- The scraper uses GitHub CLI (`gh`) and requires authentication
- Privacy-preserving: no personal info collected, only code patterns
- Target repo: leanprover-community/mathlib4
