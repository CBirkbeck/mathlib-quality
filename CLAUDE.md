# Claude Context: mathlib-quality

## Project Purpose
A Claude Code skill plugin for cleaning up, golfing, and bringing Lean 4 code up to mathlib standards before PR submission.

## Current Status
**Version:** 0.11.0

### Completed
- Plugin architecture with 5 commands defined in `commands/`
- Reference documentation in `skills/mathlib-quality/references/`
- Data collection scripts in `scripts/`
- Lean 4 integration docs in `.claude/docs/lean4/`

### In Progress / TODO
1. **Testing the Plugin** - Need to verify commands work in Claude Code with actual Lean files

### Data Collection - UPDATED (2026-04-01)
**PR Feedback Scraping:**
- Scraped 3,772 merged PRs from leanprover-community/mathlib4
- Collected 14,063 human reviewer feedback items (bot comments filtered)
- **7,273 GitHub suggestion blocks with before/after code** (gold data!)

**Data Files:**
| File | Items | Description |
|------|-------|-------------|
| `suggestions_before_after.json` | 7,273 | Before/after code examples |
| `proof_golf_feedback.json` | 6,782 | Proof simplification |
| `api_design_feedback.json` | 3,566 | API design comments |
| `style_feedback.json` | 2,390 | Style feedback |
| `general_feedback.json` | 2,199 | General comments |
| `documentation_feedback.json` | 1,020 | Doc feedback |
| `naming_feedback.json` | 467 | Naming feedback |
| `imports_feedback.json` | 406 | Import feedback |
| `performance_feedback.json` | 92 | Performance feedback |

### Recently Completed (2026-04-01)
- **Data refresh:** Re-scraped to 3,772 PRs (from 1,500), 7,273 suggestions (from 2,588)
- **RAG index rebuild:** Now indexes all 8 feedback categories (was 3), 5,752 indexed examples (was 1,905)
- **Golfing rules extraction:** Analyzed all suggestions to extract data-driven golfing patterns
  - Rewrote `proof-patterns.md` with verified rules backed by occurrence counts
  - Updated MCP `get_mathlib_quality_principles` with comprehensive rules
  - Key findings: terminal simp rule (DON'T squeeze), `lia` preferred over `omega`,
    `grind` subsumption patterns, `simpa using` as #1 golf pattern
- Updated `style-rules.md` with official mathlib conventions
- Updated `naming-conventions.md` with comprehensive symbol tables
- Updated `pr-feedback-examples.md` with full review categories
- Created `mathlib-search.md` with Loogle patterns, search strategies

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
- `/develop` - Plan and execute a mathematical development with ticket-based project management
- `/cleanup` - Audit + golf declarations (whole file or single declaration with golfing rules checklist)
- `/cleanup-all` - Run /cleanup on every file in the project, one at a time, with progress tracking
- `/decompose-proof` - Break long proofs into helpers (two-pass: analysis with DECOMPOSE plans → parallel agent decomposition)
- `/overview` - Project declaration inventory — lists every def/lemma/theorem with descriptions, dependencies, and consolidation analysis
- `/check-style` - Style validation (non-destructive)
- `/check-mathlib` - Find mathlib equivalents to avoid duplication
- `/pre-submit` - Pre-PR submission checklist
- `/fix-pr-feedback` - Address reviewer comments
- `/bump-mathlib` - Bump mathlib version and fix resulting breakage
- `/setup-chatgpt` - Set up ChatGPT MCP server for mathematical second opinions (requires ChatGPT desktop app + Plus/Pro)

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
