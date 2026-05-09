# Claude Context: mathlib-quality

## Project Purpose
A Claude Code skill plugin for cleaning up, golfing, and bringing Lean 4 code up to mathlib standards before PR submission.

## Current Status
**Version:** 0.22.0

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
- `/develop` - **Planning-only.** Searches mathlib, designs API, drafts proof sketches from user-provided sources, writes detailed self-contained tickets (Statement + numbered Proof Sketch + Mathlib Lemmas + Sources + Generality Decision per ticket). Stops once the board is approved. Workers run via `/extended-work`.
- `/extended-work` - **Execution-only.** Single-ticket focused work session; picks the next available ticket and works it to completion or concrete approach error. Strict no-complain / no-pivot / no-divergence mode. Stop conditions are explicit: DONE / PROOF-SKETCH FAILURE / MATHLIB GAP / SCOPE-DEFINITION ERROR / DEPENDENCY NOT MET — each requires a concrete report (which step failed, what was tried, why each attempt failed, replanning suggestion). Vague excuses like "this is a multi-week effort" are forbidden.
- `/cleanup` - **9-phase methodical workflow**: doctor (baseline build, abort if broken) → prepare → style-audit punch-list → file-level fixes → per-declaration deep golf (with diff gates) → refactoring → final-gates + cumulative checks → **Phase 6.5 hand-off to the built-in `/simplify` skill for holistic review** → report. Absorbed `/check-style` (Phase 2 audit), `/check-mathlib` (Phase 4 item 13: five-method search + six strict rules + common-equivalents lookup — `references/mathlib-search.md`), the inline mechanical pass of `/generalise` (Phase 4 item 18), and shouyi-style diff gates (`references/cleanup-gates.md`).
- `/cleanup-all` - Run /cleanup on every file in the project, one at a time, with progress tracking
- `/decompose-proof` - Break long proofs into helpers (two-pass: analysis with DECOMPOSE plans → parallel agent decomposition)
- `/overview` - Project declaration inventory — lists every def/lemma/theorem with descriptions, dependencies, and consolidation analysis
- `/project-status` - **Mathematician's snapshot driven by un-formalising the Lean code (not the ticket file) — chat summary + live browser dashboard.** Source of truth is the project's `.lean` files. Server (`scripts/project_status_server.py`) walks every `.lean` file, extracts every declaration with its body, infers the dependency graph from references in proof bodies, and overlays ticket statuses by declaration name. Agent's job on each invocation: read every declaration's body and write English annotations (math name, 1-3 sentence description, proof-state narrative for sorries, ingredients in scope, what-would-help for blockers) to `.mathlib-quality/.status_annotations.json`. Body-hash caching skips unchanged declarations on re-runs. The dashboard at `http://127.0.0.1:8765/` renders the un-formalisation (clickable tree from the call graph, arrow-key nav, KaTeX, Lean syntax highlighting) and live-updates structural data every 3 s. Drill-down by declaration name: `/project-status fooBar_comp` (unqualified) or `/project-status MyProj.fooBar_comp` (qualified). Flags: `--no-browser`, `--skip-unformalise`, `--stop`. Tickets demoted to a status-overlay role.
- `/expert-review` - Two-mode external-review workflow. Mode 1 produces a self-contained `REVIEW_BRIEF.md` (no Lean, no file paths) with goals, plan, references, established results, in-progress work, blockers, numbered questions, then **stops and waits**. Mode 2 (`/expert-review --reply`) takes the reviewer's response, maps it onto the questions, and proposes ticket/work-order updates — applies only after user approval. State persists in `.mathlib-quality/expert-review/<date>/`. Ticket names allowed where mathematically meaningful.
- `/generalise` - Weaken a lemma's or def's assumptions. Tries mechanical weakenings from `references/generalisation-patterns.md` (typeclass parents, drop-unused, point-localise, strict→weak); does a mandatory literature search (WebSearch + ChatGPT MCP + mathlib search). Small safe changes auto-apply with verification; big changes (public-API, renames, restating) become a numbered options menu for user approval — no auto-apply.
- `/pre-submit` - Pre-PR submission checklist
- `/fix-pr-feedback` - Address reviewer comments. Fetches all comments, implements fixes locally, **stops for explicit user approval before pushing**, then watches CI to completion (using `gh pr checks --watch` in background as the wake mechanism).
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
