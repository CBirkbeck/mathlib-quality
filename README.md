# mathlib-quality

A [Claude Code](https://docs.anthropic.com/en/docs/claude-code) skill plugin for developing, proving, cleaning up, and bringing Lean 4 code up to [mathlib](https://github.com/leanprover-community/mathlib4) standards.

Built on **14,000+ real mathlib PR review comments** with **7,273 before/after code suggestions**, extracted into concrete golfing rules and quality principles.

## What It Does

### Develop New Mathematics (`/develop`)

The flagship command. Plans and executes a full mathematical development with:

- **Project planning** -- creates a comprehensive plan from your references, searches mathlib exhaustively, designs API for every new definition
- **Ticket management** -- breaks work into trackable tickets with dependencies, parallel capacity, and proof sketches
- **Focused workers** -- one agent per ticket, deep focus on finding the cleanest proof possible
- **Resume & takeover** -- pick up where you left off, or take over an existing project with full audit
- **Quality enforced throughout** -- no sorry placeholders, no new axioms, 50-line proof limit with auto-decomposition, periodic cleanup passes
- **Maximum generality** -- always prove in the most general setting, never take shortcuts

### Clean Up Existing Code (`/cleanup`)

Audit and golf declarations against mathlib standards:

- **13-item audit** per declaration (lint, have scan, simp squeeze, naming, structure, mathlib check, ...)
- **30+ golfing rules** applied systematically (data-driven from 7,273 PR suggestions)
- **One agent per declaration** with deep focus on shortest proof
- Works on a whole file or a single declaration

### Additional Tools

- **Golf proofs** -- automation upgrades (`grind`, `fun_prop`, `positivity`, `gcongr`), term mode conversion, `have` inlining
- **Decompose long proofs** -- break proofs >30 lines into focused helper lemmas
- **Check for mathlib duplication** -- search mathlib before writing new definitions
- **Prepare PRs** -- comprehensive pre-submission checklist
- **Fix reviewer feedback** -- parse and address PR review comments

## Installation

### Option 1: Claude Code Plugin

```
/plugin marketplace add CBirkbeck/mathlib-quality
/plugin install mathlib-quality
```

### Option 2: Local Clone

```bash
git clone https://github.com/CBirkbeck/mathlib-quality.git
```

Then in Claude Code:

```
/plugin marketplace add /path/to/mathlib-quality
```

### Optional: RAG MCP Server

The plugin includes a searchable index of PR review examples. To enable:

```
/setup-rag
```

### Optional: ChatGPT MCP Server

Get mathematical second opinions from ChatGPT during Lean 4 work. After setup,
Claude Code gains an `ask_chatgpt_math` tool for verifying claims, finding
Mathlib API hints, or getting unstuck on formalization problems.

**Requirements:**
- [ChatGPT desktop app](https://chatgpt.com/download) (provides the Codex CLI binary)
- ChatGPT Plus/Pro subscription
- Node.js >= 18

Run the setup command and it will walk you through everything:

```
/setup-chatgpt
```

The command locates the Codex CLI, creates an MCP server at
`~/.claude/mcp-servers/chatgpt-math/`, installs dependencies, and adds the
server to your project's `.mcp.json`. Restart Claude Code after setup to
activate the new tool.

## Commands

| Command | Description |
|---------|-------------|
| `/develop` | Plan and execute a mathematical development with ticket management |
| `/cleanup` | Audit + golf (whole file or single declaration) |
| `/cleanup-all` | Run /cleanup on every file in the project |
| `/check-style` | Validate code against style rules (non-destructive) |
| `/decompose-proof` | Break long proofs into helper lemmas |
| `/check-mathlib` | Find mathlib equivalents to avoid duplication |
| `/pre-submit` | Pre-PR submission checklist |
| `/fix-pr-feedback` | Address PR reviewer comments |
| `/bump-mathlib` | Bump mathlib version and fix breakage |
| `/setup-rag` | Configure the RAG MCP server |
| `/setup-chatgpt` | Configure ChatGPT MCP server for mathematical second opinions |

## Usage

### Developing New Mathematics

```
/develop                   # Start a new development (plan, tickets, prove)
/develop --continue        # Resume from existing tickets
/develop --status          # Show current ticket board
/develop --takeover        # Take over an existing project
```

**How `/develop` works:**

1. **Plan** -- asks for your goal and references, searches mathlib exhaustively, designs API, creates ticket board with dependency graph
2. **Execute** -- dispatches one worker per ticket; each searches mathlib, drafts statements, proves via multi-cycle approach, decomposes proofs >50 lines
3. **Enforce** -- no sorry placeholders, no new axioms (`#print axioms` checked), maximum generality, periodic `/cleanup` passes
4. **Resume** -- on restart, deep-scans project state, cross-references tickets with reality, updates plan with user

### Cleaning Up Code

```
/cleanup MyFile.lean                # Clean entire file
/cleanup MyFile.lean theorem_name   # Clean one declaration
/cleanup-all                        # Clean every file in project
```

**How `/cleanup` works:**

For each declaration, a dedicated agent:
1. Runs 13-item audit (lint, have scan, simp squeeze, naming, line packing, ...)
2. Applies 30+ golfing rules (instant wins + automation upgrades)
3. Steps back to think holistically about the shortest possible proof
4. Verifies compilation

### Preparing a PR

```
/check-style MyFile.lean       # Check style (non-destructive)
/cleanup MyFile.lean            # Fix everything
/pre-submit MyFile.lean         # Final checklist
```

### Handling PR Feedback

```
/fix-pr-feedback 1234              # Process feedback from PR #1234
/fix-pr-feedback --comments "..."  # Or paste specific comments
```

## Key Rules (from 14,000+ PR reviews)

### The Cardinal Rule: Terminal vs Nonterminal `simp`

- **Terminal `simp` must NOT be squeezed** -- leave as `simp` or `simp [lemmas]`
- **Nonterminal `simp` MUST be squeezed** to `simp only [...]`
- This is the #1 most enforced rule in mathlib reviews (282+ comments)

### Tactic Priority (try in order)

| Priority | Tactic | Use for |
|----------|--------|---------|
| 1 | `grind` | General closing (subsumes many chains) |
| 2 | `simp` / `simpa` | Simplification (DON'T squeeze terminal) |
| 3 | `aesop` | Logic, membership, set goals |
| 4 | `fun_prop` | Continuity, differentiability, measurability |
| 5 | `positivity` | `0 < x`, `0 <= x` goals |
| 6 | `gcongr` | Inequality congruence |
| 7 | `lia` | Nat/Int arithmetic (preferred over `omega`) |
| 8 | `norm_num` | Numeric computation |
| 9 | `ring` / `field_simp; ring` | Polynomial/field equalities |

### Top Golfing Patterns

| Before | After |
|--------|-------|
| `:= by exact term` | `:= term` |
| `rw [h]; exact e` | `rwa [h]` |
| `simp [...]; exact h` | `simpa [...] using h` |
| `constructor; exact a; exact b` | `exact <a, b>` |
| `apply f; exact h` | `exact f h` |
| `by_contra h; push_neg at h` | `by_contra! h` |
| `fun x => f x` | `f` (eta-reduce) |
| `have h := x; exact h` | `exact x` |

### Style Rules

- Line length: **100 chars max**
- Proof length: **50 lines max** (decompose if longer)
- `by` at **end of preceding line**, never on its own line
- No comments inside proofs
- No `sorry` in committed code
- No new axioms

### Naming Conventions

| Declaration | Convention | Example |
|-------------|------------|---------|
| `lemma`/`theorem` | `snake_case` | `continuous_of_bounded` |
| `def` | `lowerCamelCase` | `cauchyPrincipalValue` |
| `structure` | `UpperCamelCase` | `ModularForm` |

Pattern: `conclusion_of_hypothesis` (e.g., `norm_le_of_mem_ball`)

## Data

Built from scraping **3,772 merged mathlib4 PRs**:

| Data | Count |
|------|-------|
| Reviewer feedback items | 14,063 |
| Before/after code suggestions | 7,273 |
| RAG indexed examples | 5,752 |
| Proof golf examples | 6,782 |
| Style feedback items | 2,390 |
| API design feedback | 3,566 |

All data is privacy-preserving -- only technical content is collected, no personal information.

## Project Structure

```
mathlib-quality/
├── commands/                    # Slash command implementations
│   ├── develop.md               # Mathematical development engine
│   ├── cleanup.md               # Audit + golf
│   ├── cleanup-all.md           # Project-wide cleanup
│   ├── decompose-proof.md
│   ├── check-style.md
│   ├── check-mathlib.md
│   ├── pre-submit.md
│   ├── fix-pr-feedback.md
│   ├── setup-rag.md
│   └── setup-chatgpt.md         # ChatGPT MCP server setup
├── skills/mathlib-quality/
│   ├── SKILL.md                 # Main skill definition
│   └── references/              # Style, naming, golfing rules, proof patterns
├── mcp_server/
│   └── mathlib_rag.py           # MCP server for RAG queries
├── scripts/                     # Scraping, analysis, and query tools
└── data/pr_feedback/            # RAG indexes (built from PR reviews)
```

## Acknowledgements

- **[kim-em/botbaki](https://github.com/kim-em/botbaki)** -- Style conventions and formatting guidelines
- **[cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills)** -- Multi-cycle proving approach and proof golfing methodology
- **[leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)** -- PR review data (public, technical content only)

## Contributing

1. Fork the repository
2. Make changes
3. Test locally: `/plugin marketplace add /path/to/your/fork`
4. Submit a PR

## License

MIT License -- see [LICENSE](LICENSE)
