# mathlib-quality

A [Claude Code](https://docs.anthropic.com/en/docs/claude-code) skill plugin for cleaning up, golfing, and bringing Lean 4 code up to [mathlib](https://github.com/leanprover-community/mathlib4) standards before PR submission.

Includes a RAG system built from **4,600+ real mathlib PR review comments** with before/after code examples, and specialized agents for proof golfing, decomposition, and style enforcement.

## What It Does

When working on Lean 4 files destined for mathlib, this plugin gives Claude Code deep knowledge of mathlib's conventions and common reviewer feedback. It can:

- **Enforce style rules** -- line length, `by` placement, indentation, naming conventions, docstring format
- **Golf proofs** -- shorten proofs using automation (`grind`, `fun_prop`, `omega`, `aesop`), term mode conversion, `have` inlining, and patterns learned from thousands of real PR reviews
- **Decompose long proofs** -- break proofs >30 lines into focused helper lemmas with proper naming
- **Check for mathlib duplication** -- search mathlib for existing lemmas before writing new ones
- **Prepare PRs** -- run a comprehensive pre-submission checklist
- **Fix reviewer feedback** -- parse and address PR review comments
- **Split large files** -- break files >1500 lines into focused modules

## Installation

### Step 1: Add the Marketplace

In Claude Code, run:

```
/plugin marketplace add CBirkbeck/mathlib-quality
```

Then install the plugin from the **Discover** tab in the `/plugin` menu, or run:

```
/plugin install mathlib-quality
```

### Alternative: Local Installation

Clone the repo and install from a local path:

```bash
git clone https://github.com/CBirkbeck/mathlib-quality.git
```

Then in Claude Code:

```
/plugin marketplace add /path/to/mathlib-quality
```

### Step 2: Set Up the RAG Server (Recommended)

The plugin includes a RAG (Retrieval Augmented Generation) system that lets Claude Code search 4,600+ PR review examples. To enable it, run the `/setup-rag` command inside Claude Code:

```
/setup-rag
```

This will check dependencies, configure the MCP server in your project's `.mcp.json`, and verify everything works. You can also run the setup script directly:

```bash
cd /path/to/mathlib-quality
./setup.sh
```

## Commands

| Command | Description |
|---------|-------------|
| `/cleanup` | Full file cleanup to mathlib standards |
| `/check-style` | Validate code against style rules (non-destructive) |
| `/golf-proof` | Optimize and shorten proofs |
| `/decompose-proof` | Break long proofs into helper lemmas |
| `/split-file` | Split large files (>1500 lines) into focused modules |
| `/check-mathlib` | Find mathlib equivalents to avoid duplication |
| `/pre-submit` | Pre-PR submission checklist |
| `/fix-pr-feedback` | Address PR reviewer comments |
| `/setup-rag` | Configure the RAG MCP server |

## Usage

### Preparing Code for a PR

```
# 1. Check style issues (no changes made)
/check-style MyFile.lean

# 2. Apply automatic fixes
/cleanup MyFile.lean

# 3. Optimize proofs
/golf-proof theorem_name

# 4. Final verification before submitting
/pre-submit MyFile.lean
```

### Handling PR Feedback

```
# Process feedback from a PR
/fix-pr-feedback 1234

# Or paste specific comments
/fix-pr-feedback --comments "Please shorten line 45..."
```

### Breaking Up Long Proofs

```
# Decompose proofs >30 lines into helper lemmas
/decompose-proof MyFile.lean
```

## RAG System

The plugin ships with a searchable index of **4,600+ PR review comments** scraped from merged mathlib4 PRs. This includes **2,588 before/after code suggestions** -- real examples of how reviewers asked contributors to improve their code.

### With the MCP Server (after `/setup-rag`)

Once configured, the RAG tools are available automatically in Claude Code:

- `search_golf_examples(code="have h := foo; simp [h]")` -- find similar code and how reviewers improved it
- `search_by_pattern(pattern="use_grind")` -- find examples of specific transformations
- `search_by_topic(topics=["continuity"])` -- find topic-specific examples
- `get_mathlib_quality_principles()` -- get synthesized quality rules

### With the Query Script

```bash
# Find examples similar to your code
python3 scripts/query_rag.py --code "have h := foo; simp [h]"

# Find transformation pattern examples
python3 scripts/query_rag.py --pattern use_grind
python3 scripts/query_rag.py --pattern use_fun_prop

# Search by tactic usage
python3 scripts/query_rag.py --tactics simp have exact

# Search by mathematical topic
python3 scripts/query_rag.py --topic continuity
```

Available patterns: `simp_to_simpa`, `use_grind`, `use_fun_prop`, `use_aesop`, `use_omega`, `term_mode`, `remove_redundant`

## Quick Reference

### Key Style Rules

- Line length: **100 chars max**
- File length: **1500 lines max** (split if larger)
- Proof length: **50 lines max** (target <15)
- `by` always at **end of preceding line**, never on its own line
- Use `fun x =>` not `λ x,`
- Use `simp only [...]` for non-terminal simp
- No comments inside proofs
- No empty lines inside declarations

### Naming Conventions

**Different conventions for different declaration types:**

| Declaration | Returns | Convention | Example |
|-------------|---------|------------|---------|
| `lemma`/`theorem` | `Prop` | `snake_case` | `continuous_of_bounded` |
| `def` | Data | `lowerCamelCase` | `cauchyPrincipalValue` |
| `structure` | Type | `UpperCamelCase` | `ModularForm` |

Lemma naming pattern: `conclusion_of_hypothesis` (e.g., `norm_le_of_mem_ball`)

## Project Structure

```
mathlib-quality/
├── commands/                    # Slash command implementations
│   ├── cleanup.md
│   ├── check-style.md
│   ├── golf-proof.md
│   ├── decompose-proof.md
│   ├── split-file.md
│   ├── check-mathlib.md
│   ├── pre-submit.md
│   ├── fix-pr-feedback.md
│   └── setup-rag.md
├── skills/mathlib-quality/
│   ├── SKILL.md                 # Main skill definition
│   ├── references/              # Style rules, naming, patterns
│   ├── examples/                # Curated before/after examples
│   └── agents/                  # Specialized agent prompts
├── mcp_server/
│   └── mathlib_rag.py           # MCP server for RAG queries
├── scripts/                     # Build, query, and scraping tools
├── data/pr_feedback/            # RAG indexes and curated examples
└── setup.sh                     # One-step setup script
```

## Integration with Lean 4

This skill works alongside the [`lean4-theorem-proving`](https://github.com/cmu-l3/lean4-theorem-proving) Claude Code skill:

- Uses Lean LSP tools to verify changes compile after each edit
- Uses `lean_diagnostic_messages` to check for errors
- Uses `lean_goal` to verify proof state during golfing

## Acknowledgements

This plugin builds on work from several sources:

- **[kim-em/botbaki](https://github.com/kim-em/botbaki)** -- Style conventions, naming rules, and formatting guidelines for mathlib contributions were incorporated from the botbaki repository.
- **[Cameron Freer's proof golfing agent](https://github.com/cfreer/lean-golf)** -- The proof golfing methodology and agent design draws on Cameron Freer's work on automated proof optimization for Lean 4.
- **[leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)** -- The RAG system is built from public PR review comments on merged mathlib4 pull requests. Only technical content is collected; no personal information is scraped.

## Contributing

1. Fork the repository
2. Make changes
3. Test locally: `/plugin marketplace add /path/to/your/fork`
4. Submit a PR

## License

MIT License -- see [LICENSE](LICENSE)
