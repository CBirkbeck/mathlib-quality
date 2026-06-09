# mathlib-quality

A [Claude Code](https://docs.anthropic.com/en/docs/claude-code) skill plugin for developing, proving, cleaning up, and bringing Lean 4 code up to [mathlib](https://github.com/leanprover-community/mathlib4) standards.

Built on **14,000+ real mathlib PR review comments** with **7,273 before/after code suggestions**, extracted into concrete golfing rules and quality principles.

## What It Does

### Develop New Mathematics — Plan with `/develop`, then Execute with `/beastmode`

The development workflow is **split into planning and execution** to prevent the "agent
reconsiders the whole approach mid-proof" failure mode. `/develop` does the strategic
thinking; `/beastmode` does the tactical implementation; neither does the other's
job.

**`/develop` — planning only.**

- **Comprehensive plan** from your references; exhaustive mathlib search; API design for every new declaration.
- **Detailed self-contained tickets.** Every proof/definition ticket contains the full **Lean Statement**, a numbered **Proof Sketch** citing sources, the **Mathlib lemmas needed** (verified to exist), the **Sources** with bibliographic info, and the **Generality decision**. Detailed enough that no replanning is needed once execution starts.
- **Algorithmic cleanup-cadence**: every 3 proof tickets per file → cleanup ticket; per-file finals; pre-milestone `/cleanup-all`; final-of-everything cleanup. The cadence is verified at planning time and re-checked at every resume audit.
- **Resume & takeover modes**: `--continue` audits the ticket board against the current code and proposes updates (including missing cleanup tickets); `--takeover` creates a plan for an existing project. Both end with a hand-off to `/beastmode`.
- **No execution.** Once the board is approved, `/develop` stops.

**`/beastmode` — marathon execution. Stops at nothing — but stays on-target.**

- **Pick a ticket, finish the goal.** No matter how deep the path goes. When a sub-step needs a missing lemma, missing dependency, or sub-result that isn't on the board, the worker spawns a sub-ticket *in /develop's ticket-template format* and immediately works it. When the parent's sketch turns out to be wrong as a strategy, the worker invokes `/develop --continue` to replan inline and keeps going.
- **On-target vigilance, continuously.** Before each sub-ticket and step, the worker confirms: serves the plan's main goal? stays in the project's mathematical area? a refinement, not a divergence? Vigilance is *for* on-target work, not against it.
- **Scope growth that stays on-target is great news.** A "two lemmas" step turning out to need ten is more mathematics captured — exactly the point of the marathon. The harder the work, the more energy goes in (Super Saiyan ethos: the stronger the opponent, the stronger you get).
- **No recursion cap, no time budget.** "It's late", "this is taking a while", "we're 5 sub-tickets deep", "let me try a different approach" — none of these are legitimate stops.
- **Only legitimate stops**: DONE / SCOPE-DEFINITION ERROR (statement actually wrong) / OFF-TRACK (drift onto material genuinely outside the project's mathematical area, with concrete evidence) / BROKEN BASELINE (`lake build` broken on entry).
- **Quality enforced throughout** — no `sorry`, no new axioms (`#print axioms` checked), maximum generality, gates run on the diff before marking the ticket done.

### Clean Up Existing Code (`/cleanup`)

Methodical 8-phase workflow for any Lean file. Replaces what used to be three commands (`/check-style`, `/check-mathlib`, plus the original `/cleanup`):

- **Phase 0 — Doctor**: pre-flight `lake build` baseline check; aborts if the project doesn't currently compile (we can't tell what we broke without a clean baseline)
- **Phase 2 — Style audit**: full numbered punch-list; what was the standalone `/check-style`
- **Phase 3 — File-level fixes**: copyright + module docstring (CREATED if missing) + imports + subsection-divider strip + `set_option` removal + batched mechanical replacements
- **Phase 4 — Per-declaration deep cleanup**: one worker per decl; **18-item audit** with required status blocks for golf rules (1.1 → 3.7), the **five-method mathlib search** (formerly `/check-mathlib`), and **inline `/generalise` mechanical pass** with literature search for public decls
- **Phase 5 — Refactoring**: cross-declaration items (renames, junk-def inlining, mathlib replacements, big-change generalisations escalated to standalone `/generalise`)
- **Phase 6 — Final verification**: file-level **gates** (definition_protected, theorem_statement_protected, lake_build_file, cumulative_no_unintended_breakage) — borrowed from [shouyi](https://github.com/frenzymath/shouyi)
- One agent per declaration, deep focus on shortest proof; 60+ rules from `golfing-rules.md` and `proof-patterns.md` applied systematically (data-driven from 7,273 PR suggestions)

### Additional Tools

- **`/project-status`** — chat-only mathematical status report. Reads the project's `.lean` files (plus `plan.md` / `tickets.md` if present) and answers four questions in mathematical English: what result is the worker on, what (if anything) is blocked and what is mathematically missing, how does the current work connect to the overall goal, and how far along is the whole project. **Three-tier progress** — code-level coverage (declarations sorry-free), main-goal chain coverage (only the dependency closure of the main result), and distance-to-unconditional (parametric hypotheses on the main goal still to discharge). Unicode math only, no LaTeX. Read-only — no server, no browser.
- **`/generalise`** — weaken assumptions on a single lemma/def: typeclass-hierarchy walk, drop-test, point-localise, strict→weak, plus mandatory literature search; auto-applies small safe changes, presents big changes as a numbered approval menu (also runs inline as part of `/cleanup` Phase 4)
- **`/decompose-proof`** — break proofs >30 lines into focused helper lemmas (with mandatory user approval gate before dispatch)
- **`/expert-review`** — produce a self-contained mathematical brief (`REVIEW_BRIEF.md`) for an external reviewer with no repo access; pure math, no Lean, no file paths; then in Mode 2 (`--reply`) integrate the reviewer's response into ticket-board updates
- **`/blueprint`** — author or update the project's [verso-blueprint](https://github.com/leanprover/verso-blueprint) — the Verso-based Lean-native artifact behind verso-sphere-packing, verso-flt, verso-carleson, verso-noperthedron, verso-algebraic-combinatorics. Chapter files are `.lean` modules; statements use `:::theorem "label" (lean := "Foo.bar")` directives; dep-graph edges use `{uses "label"}[]`; math is KaTeX (``$`...` `` inline, ``$$`...` `` display). Verso auto-computes completion status from `(lean := …)` — no manual `\leanok` to maintain. Seven-phase workflow: doctor → enumerate (diff against existing chapters) → plan → prose context → author (one worker per declaration; Verso directives only) → cross-link pass → hand-off (`./scripts/ci-pages.sh`; verify `_out/site/html-multi/`). Whole-project default; modes for single-file, `--decl <Foo.bar>` (single decl + closure), `--update` (drift-only), `--check` (inventory + diff), `--migrate-from-latex [<dir>]` (one-shot mechanical 1:1 conversion of a legacy `leanblueprint` LaTeX tree)
- **`/unformalise`** — turn one Lean declaration into mathematics. Unicode terminal render by default (Γ, ℂ, ℍ, →, ≤ — readable in chat); then `[b]` blueprint as Verso / `[v]` Verso markup to stdout / `[m]` Markdown / `[n]` terminal-only. Non-interactive: `--verso`, `--md`, `--blueprint`. The conversational front door for `/blueprint --decl`
- **`/fix-pr-feedback`** — fetch every PR comment, fix locally, **stop for explicit user approval before pushing**, then watch CI to completion (`gh pr checks --watch` runs in background as the wake-timer). Every commit and any PR-description update follows binding conventions: short imperative subject, concrete bullet body, dependencies surfaced via a `Depends on #1234` line, Claude co-author footer.
- **`/bump-mathlib`** — bump mathlib version and fix the resulting breakage; documents recurring patterns from upstream evolution (Splits binary→unary refactor, IsX field-name normalisation, etc.)
- **`/pre-submit`** — final pre-PR checklist
- **`/overview`** — project-wide declaration inventory: every `def`/`lemma`/`theorem` with descriptions, dependencies, and consolidation analysis
- **`/split-file`** — split files >1000 lines (with mandatory user approval gate)

## Installation

### Option 1: Claude Code Plugin

```
/plugin marketplace add CBirkbeck/mathlib-quality
/plugin install mathlib-quality
```

Also install the [lean4-skills](https://github.com/cameronfreer/lean4-skills) plugin,
which provides the Lean 4 theorem proving workflows that mathlib-quality builds on:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4
```

### Option 2: Local Clone

```bash
git clone https://github.com/CBirkbeck/mathlib-quality.git
```

Then in Claude Code:

```
/plugin marketplace add /path/to/mathlib-quality
```

### Lean LSP MCP Server (Highly Recommended)

Nearly all commands (`/develop`, `/cleanup`, `/decompose-proof`, etc.) depend on
the [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) server for sub-second
feedback instead of 30+ second `lake build` cycles. It provides tools like
`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, `lean_loogle`, and more.

**Prerequisites:**
- [uv](https://docs.astral.sh/uv/getting-started/installation/) (Python package manager)
- A Lean 4 project with `lakefile.lean`
- Run `lake build` once in your project before starting (the LSP server needs oleans)

**Setup** (run from your Lean project root):

```bash
# User-scoped (recommended) — available in all your projects
claude mcp add --transport stdio --scope user lean-lsp -- uvx lean-lsp-mcp

# Or project-scoped — shared via .mcp.json
claude mcp add --transport stdio --scope project lean-lsp -- uvx lean-lsp-mcp
```

User-scoped (`--scope user`) is recommended — it is more reliable for keeping MCP
tools visible inside subagents.

Restart Claude Code after adding. Verify by checking that tools like `lean_goal`
and `lean_diagnostic_messages` appear.

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
| `/develop` | **Planning only, with binding methodical-decomposition pre-work.** Mathlib search, API design, then a per-result decomposition pass: prose proof + ordered lemma list + **`:= by sorry` skeleton stated in the project's Lean files (must `lake build` clean)** + **verbatim source quotes per leaf** + Lean ↔ source match paragraphs + per-leaf provability check. Saved as `decomposition.md`; tickets only after every leaf verified. **`--decompose` flag** runs just this pre-work pass and stops, for iterating on the decomposition before committing to a ticket board. |
| `/beastmode` | **Marathon execution. Stops at nothing — but stays on-target.** Pick a ticket and finish the goal — spawn sub-tickets in `/develop`'s format for missing lemmas, replan via `/develop --continue` for wrong strategies, no recursion cap, no time budget. **Super Saiyan ethos**: scope growth that stays on-target is great news, not a stop signal. **Multi-session work is the target, not an exit.** Only stops: DONE / SCOPE-DEFINITION ERROR / OFF-TRACK (genuine, with concrete evidence) / BROKEN BASELINE. |
| `/cleanup` | Style audit + cleanup + golf (whole file or single declaration). **10-phase** methodical workflow with per-worker phase checklist; Phase 5 split into 5a (non-rename refactoring) and 5b (dedicated rename pass — workers append to `.mathlib-quality/renames.jsonl`, Phase 5b applies them repo-wide in one sequential pass). Absorbed `/check-style` (Phase 2 audit) and `/check-mathlib` (Phase 4 item 13: five-method search-status block + six strict mathlib-replacement rules). |
| `/cleanup-all` | **Orchestrator-worker marathon.** Main session dispatches batched `Agent` calls with tight prompts (working dir + branch + build + file list + target); workers do all file reading, LSP, edits, and build verification in fresh contexts. Between dispatches the orchestrator emits a one-line scoreboard, nothing else. The pattern that sustained a real 28-day, 9000-message, 395-dispatch cleanup session. |
| `/project-status` | Chat-only mathematical status: what's the worker on, what's blocked + missing, how it connects to the goal, how far along. **Three-tier progress** (code-level / main-goal chain / parametric-hypotheses discharged). Unicode math, no LaTeX. |
| `/overview` | Project-wide declaration inventory: every `def`/`lemma`/`theorem` with descriptions, dependencies, consolidation analysis |
| `/expert-review` | Two-mode external review: produce a self-contained math brief (`REVIEW_BRIEF.md`), wait for the reviewer's response, then integrate their guidance into the ticket board |
| `/generalise` | Weaken assumptions on a lemma or definition: mechanical weakenings + literature search; auto-apply small safe changes, propose big changes as a numbered menu |
| `/decompose-proof` | Break long proofs into helper lemmas |
| `/split-file` | Split files >1000 lines (with approval gate) |
| `/pre-submit` | Pre-PR submission checklist |
| `/fix-pr-feedback` | Fetch PR comments → fix → STOP for approval → push → watch CI. Every commit and PR-description update follows binding conventions (short imperative subject, concrete bullet body, `Depends on` line, Claude co-author footer). |
| `/bump-mathlib` | Bump mathlib version and fix breakage |
| `/blueprint` | **Author or update the project's verso-blueprint** — Verso-based Lean-native dep-graph artifact (verso-sphere-packing/verso-flt/verso-carleson-style). Wraps [`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint); focuses on high-quality unformalisations. Seven phases (doctor → enumerate → plan → prose context → author → cross-link → hand-off). Modes: whole project, single file, `--decl <Foo.bar>`, `--update`, `--check`, `--migrate-from-latex [<dir>]` (one-shot mechanical conversion from legacy `leanblueprint` LaTeX). Conventions + Verso-specific deployment gotchas in `references/blueprint-conventions.md`. |
| `/unformalise` | **Turn one Lean declaration into mathematics.** Unicode terminal render by default (Γ, ℂ, ℍ, →, ≤); then `[b]` blueprint as Verso / `[v]` Verso to stdout / `[m]` Markdown / `[n]` terminal-only. Non-interactive flags `--verso`, `--md`, `--blueprint`. Modes: single decl, `--closure`, whole file. The conversational front door for `/blueprint --decl`. |
| `/teach` | Record a project-specific pattern or convention |
| `/contribute` | Push local learnings back as a PR to this repo |
| `/setup-chatgpt` | Configure ChatGPT MCP server for mathematical second opinions |

## Usage

### Developing New Mathematics

```
# Plan
/develop                   # Plan a new development (creates the ticket board)
/develop --decompose       # Run ONLY Phase 1e (skeleton + source quotes + feasibility), no tickets
/develop --continue        # Audit ticket board against the code, propose updates
/develop --status          # Show current ticket board
/develop --takeover        # Plan a takeover of an existing project

# Execute
/beastmode                 # Pick the next available ticket and work it to completion
/beastmode --ticket T042   # Specific ticket
/beastmode --resume        # Resume an in_progress ticket from its progress notes

# Check status between sessions
/project-status            # Chat report: what's the worker on, what's blocked, how far from the goal

# Finish
/pre-submit                # Final-review checklist after all tickets are done
```

**How `/develop` works (planning):**

1. **Gather context** — goal, references, scope.
2. **Study references** — read user-provided papers / books to extract the canonical statements and proof outlines that will populate tickets.
3. **Search mathlib** exhaustively for existing relevant definitions and lemmas.
4. **Design the API** — maximally general typeclasses, namespace conventions, what to define vs. import.
5. **Write the plan** in `.mathlib-quality/plan.md`.
6. **Create detailed tickets** — every ticket gets full **Statement**, **Proof Sketch**, **Mathlib lemmas needed**, **Sources**, **Generality decision**.
7. **(Optional)** ChatGPT plan validation if MCP available.
8. **User approval.** After approval, `/develop` stops.

**How `/beastmode` works (execution):**

1. **Pick** — auto-pick the next ticket whose dependencies are done, or honour `--ticket TXXX`.
2. **Read** the ticket fully. If any required field (Statement / Proof Sketch / Mathlib lemmas / Sources / Generality) is missing, refuse to start and ask the user to re-run `/develop` to complete the ticket.
3. **Pre-work checks** — dependencies actually done; `lake build` baseline clean.
4. **State** the declaration verbatim from the ticket's Statement field.
5. **Prove** by walking the proof sketch step by step; verify each cited mathlib lemma exists; use `lean_multi_attempt` aggressively; checkpoint progress in the ticket as you go.
6. **Verify** — diagnostics clean, no sorry, axiom check, `lake build` clean.
7. **Gates** on the diff (definition_protected, theorem_statement_protected, etc.).
8. **Post-proof cleanup (Phase 6.5, mandatory).** Before mark-done, invokes `Skill(skill="mathlib-quality:cleanup", args="<file> <decl_name>")` on every NEW declaration the ticket produced. `/cleanup` runs its full 10-phase workflow (including 5b rename pass and 6.5 simplify hand-off); the per-decl phase-checklist enforcement is `/cleanup`'s own responsibility. Decompose flags spawn `/decompose-proof` sub-tickets (recorded in the ticket's progress notes; G6 sequence-continuation picks them up). Rename queue is drained inside `/cleanup`'s Phase 5b. Gate failures from `/cleanup` block the ticket from being marked done — either the cleanup itself is reverted or the proof itself is the issue (Tier-B SCOPE/DEFINITION-ERROR).
9. **Mark done** + report. If a hard-stop condition fires instead, the report names which step failed, what was tried, and a concrete replanning suggestion.

**Staying alive across turns (the Stop hook).** A model ends its turn after a few minutes of work — that's harness mechanics, not a beastmode bug, and it's why earlier versions stalled. The plugin ships a guarded `Stop` hook (`hooks/beastmode_stop.sh`): while a marathon is active it refuses the turn-end and re-prompts the agent, so one `/beastmode` session sustains across many turns instead of stopping at 2–3 minutes — **even when launched bare, with no `/loop`.** It is gated by a sentinel file (`.mathlib-quality/beastmode_active`) that `/beastmode` writes on start and removes only at a genuine terminal state, and it is fail-safe (inert for every non-beastmode session). To pause or stop: press **Esc**, or `rm .mathlib-quality/beastmode_active`; a progress budget also auto-releases after `BEASTMODE_MAX_BLOCKS` turns (default 30) with no `.lean`/ticket change. The hook spans turns *within* a session; for boards too big for one context window, wrap it as `/loop /beastmode`, which spans *across* sessions.

**When all tickets are done**, run `/pre-submit` for the final-review checklist (no `sorry` anywhere, no new axioms, full project build clean, etc.).

### Cleaning Up Code

```
/cleanup MyFile.lean                # Clean entire file
/cleanup MyFile.lean theorem_name   # Clean one declaration
/cleanup-all                        # Clean every file in project
```

**How `/cleanup` works (10 phases, methodical, no skipping):**

0. **Doctor** — pre-flight: `lake exe cache get`, `lake build` (must pass — without a clean baseline we can't tell what breakage we introduced), LSP responsive on the target file. Aborts if the baseline is broken.
1. **Prepare** — read the file, run `lean_diagnostic_messages`, read the five reference docs (golfing-rules, proof-patterns, mathlib-search, generalisation-patterns, cleanup-gates), build the declaration list.
2. **Style audit** — complete numbered punch-list (file-level + linter findings + per-declaration light scan). No fixes yet. Replaces what used to be `/check-style`.
3. **File-level fixes** — copyright, **module docstring (CREATED if missing)**, imports, subsection dividers, file-level `set_option`, batch mechanical replacements (`λ`→`fun`, `$`→`<|`, `push_neg`→`push Not`).
4. **Per-declaration deep cleanup** — one dedicated agent per declaration. The worker reads the reference docs, runs the **18-item audit** with required status blocks for: every golfing rule (1.1 → 3.7), the **five-method mathlib search** (with the six strict mathlib-replacement rules — replaces `/check-mathlib`), the **inline mechanical generalisation pass** (catalogue-driven typeclass-hierarchy walk, drop-test, pointwise / strict→weak), and (for public decls) a literature search. Then runs the **per-worker diff gates** on the worker's edits before completing — including the hard `structure_gate` / `naming_gate` / `line_packing_gate`: audit items 12/5/6 are pass/fail, not deferrable, so a worker that leaves a long body ("signature locked" is not a valid excuse — a `private` helper above the decl is not a signature change), a scheme-number name (`m6_2_…`, `multipass_…`), or one-hypothesis-per-line signatures is re-dispatched, not accepted.
5. **Refactoring (split into 5a + 5b).**
   - **5a — Non-rename refactoring:** cross-declaration items from Phase 4 worker reports — mathlib replacements, junk-def inlining, big-change generalisations escalated to standalone `/generalise` (which has the user-approval gate on big changes).
   - **5b — Rename pass:** Phase 4 workers never rename in place (parallel workers would race on shared call sites). They append `{old, new, scope, file, …}` JSON to `.mathlib-quality/renames.jsonl`. Phase 5b reads the queue, dedupes, conflict-checks, then applies each rename sequentially across the whole repo with `Grep` + `Edit replace_all` + `lean_diagnostic_messages` between each. The queue is truncated when done.
6. **Final verification** — file-level diff gates (`lake_build_file`, `lake_build`, `definition_protected`, `theorem_statement_protected`, `cumulative_no_unintended_breakage`). Untraceable signature changes are gate failures; only continues if Phase 6 is `pass`.
6½. **Simplify pass** — hand off to the **built-in `/simplify` skill** (provided by Claude Code) for a holistic review. Where `/cleanup` is checklist-driven, `/simplify` is holistic — it spots duplicated proof skeletons across the file, cross-cutting issues the per-declaration workers missed, and quality issues that don't match any specific rule. If `/simplify` makes changes, the gates from Phase 6 are re-run on the new state. Required artifact: simplify-pass status block.
7. **Report** — one consolidated report including the Phase-0 baseline, the audit punch-list, per-declaration before/after, refactoring done, gate-status table, and the simplify-pass outcome.

**No-skipping enforcement.** `/cleanup`'s anti-skip defence sits on four mechanisms: required artifacts (status blocks the agent must emit — golf-rule status, mathlib search-status, generalisation status, gate status, simplify status; missing or blank cells = step skipped), verification gates between phases (`lake build` baseline, diagnostics-clean), diff gates on edits (definition_protected, theorem_statement_protected — catches *out-of-scope* edits), and user-approval pauses for high-blast-radius actions. The Phase-7 report's required-section list lets a missing artifact fail the report.

### Preparing a PR

```
/cleanup MyFile.lean            # Audit + fix + golf (one command)
/pre-submit MyFile.lean         # Final checklist
```

### Authoring a Blueprint

The skill targets [`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint) —
the Verso-based Lean-native blueprint tool. Chapter files are `.lean` modules under
`<Project>/Chapters/`; statements use `:::theorem "label" (lean := "Foo.bar")` directives;
dep-graph edges use `{uses "label"}[]`; math is KaTeX. **Verso auto-computes completion
status** from the `(lean := …)` reference — no manual `\leanok` to keep in sync.

```
/blueprint                              # Whole project: enumerate every public decl → write <Project>/Chapters/*.lean
/blueprint <file.lean>                  # Only this file's declarations
/blueprint --decl <Foo.bar>             # One declaration + its dependency closure (non-interactive)
/blueprint --update                     # Re-sync after Lean changes (drift / stale refs only)
/blueprint --check                      # Inventory + drift report; author nothing
/blueprint --migrate-from-latex [<dir>] # Mechanical 1:1 conversion of a legacy leanblueprint LaTeX tree
                                        # (default <dir>: blueprint/src/) → <Project>/Chapters/*.lean

/unformalise <Foo.bar>                  # Render as Unicode in terminal; then [b/v/m/n]
/unformalise <Foo.bar> --closure        # …also recursively render its dependencies
/unformalise <file.lean> --md           # Whole file, Markdown to stdout (good for PR descriptions)
```

**`/blueprint` and `/unformalise` cover the same core job — unformalising Lean
declarations into mathematical prose with `(lean := …)` / `{uses}` annotations.**
The split is by ergonomics, not capability:

| Goal | Use |
|---|---|
| "Show me what this theorem says, then maybe blueprint it" | `/unformalise Foo.bar` |
| "Add this result and everything it uses to the blueprint" | `/blueprint --decl Foo.bar` |
| "Bootstrap or sync the whole project's blueprint" | `/blueprint` |
| "Convert our old LaTeX leanblueprint to Verso" | `/blueprint --migrate-from-latex` |

**How `/blueprint` works (7 phases):**

0. **Doctor** — verso-blueprint scaffold present (`<Project>/Chapters/`, `<Project>/Blueprint.lean`, `<Project>Main.lean`, `scripts/ci-pages.sh`); `lake build` clean; `lake env lean --run` probe healthy. If the scaffold is missing, Phase 0 stops with copy-template instructions pointing at [`leanprover/verso-blueprint/project_template/`](https://github.com/leanprover/verso-blueprint/tree/main/project_template).
1. **Enumerate** — walk public decls; diff against existing chapter files to compute four sets: **New** / **Existing-OK** / **Stale** (Lean decl no longer exists) / **Drift** (signature changed).
2. **Plan** — print inventory; user confirms scope (hard pause). Blueprint authoring is heavyweight — one worker per declaration — and a wrong scope is expensive.
3. **Prose context** — read `.mathlib-quality/references/`, module docstrings, any prior `/develop` `decomposition.md` ONCE into `.mathlib-quality/blueprint/prose_context.md`. Workers consume from there in Phase 4 — references aren't re-read per worker.
4. **Author** — one `Agent` per declaration. Worker reads Lean + prose context + adjacent chapter chunks; produces a Verso directive `:::theorem "label" (lean := "Foo.bar")` with the statement in math notation (no Lean plumbing); optionally a `:::proof "label"` block with a paragraph-level sketch in math English (not a tactic transcript); `{uses "..."}[]` for dep-graph edges; writes to the chapter file.
5. **Cross-link pass** — main agent collects every label and `{uses "X"}[]` across `<Project>/Chapters/`; orphan `{uses}` references resolved by add / rename / remove; stale `(lean := "X")` references from Phase 1 repaired against the current Lean tree; new chapter files wired into `<Project>/Blueprint.lean` (`import` + `{include 0 ...}`).
6. **Hand-off** — `./scripts/ci-pages.sh` runs the full Verso build + render to `_out/site/html-multi/`. Any failure surfaces as an exact Lean error (stale `(lean := …)`, KaTeX macro error, unclosed `:::`). No multi-pass `latexmk`, no `\leanok` to maintain, no `api-docs: true` flag to remember.
7. **Report** — single consolidated report with per-phase required artifacts.

The conventions, anti-patterns, four worked examples, and the Verso-specific **deployment & CI gotcha catalogue** live in `skills/mathlib-quality/references/blueprint-conventions.md` — workers read this in full before authoring.

#### Migrating from a legacy LaTeX `leanblueprint`

```
/blueprint --migrate-from-latex                       # default reads blueprint/src/
/blueprint --migrate-from-latex <path/to/latex/dir>   # custom location
```

Mechanical 1:1 translation: each `.tex` file becomes one chapter file; `\begin{theorem}\label{thm:foo}\lean{Foo.bar}\uses{a,b}\leanok ...\end{theorem}` becomes `:::theorem "foo" (lean := "Foo.bar") ... ::: ` with `{uses "a"}[]`, `{uses "b"}[]` at end of body; `\leanok` is dropped (Verso auto-computes); math `$...$` becomes ``$`...```` and `\[...\]` becomes ``$$`...````; `\newcommand`s migrate to `tex_prelude`. The migration is syntax-level — for any chunk whose prose reads awkwardly post-translation, re-author with `/unformalise --blueprint <decl>` for polish. Custom LaTeX macros (tikz, xy-pic, etc.), `\cite{...}`/`\bibliography`, and project-specific environments are flagged for manual review.

### Handling PR Feedback

```
/fix-pr-feedback 1234              # Process feedback from mathlib PR #1234
/fix-pr-feedback --comments "..."  # Or paste specific comments
```

**How `/fix-pr-feedback` works (8 phases, push-gated):**

1. **Fetch** — pull every review comment, issue comment, and PR-review summary via `gh api`.
2. **Triage** — numbered punch-list with severity (🔴 must-fix, 🟡 should-fix, 🟢 question, ⚪ resolved) and category (golf / style / naming / api-design / correctness / …).
3. **Implement** — fix each item in priority order (correctness → naming → golf → style → docs → questions); for proof rewrites, dispatches `/cleanup`-Phase-4-style workers.
4. **Coverage check** — re-fetches comments and cross-references by id; any comment not in the action log is treated as a defect and addressed before continuing.
5. **STOP for user approval** — prints the full report (changes, deferred items with reasons, drafted replies for the reviewer) and **waits for explicit OK to push**. No silent push.
6. **Push + watch CI** — once approved, `git push` then `gh pr checks --watch` in the background. The runtime auto-notifies when checks finish — that's the wake-timer.
7. **CI follow-up** — if CI fails, diagnose, fix, return to Phase 5 (still no push without approval).
8. **Final report + learnings** — once green, summarise and write learnings.

## Design Philosophy: Methodical Phases + Required Artifacts

The recent rewrites of `/cleanup`, `/fix-pr-feedback`, `/develop`, `/beastmode`,
`/project-status`, `/expert-review`, `/generalise`, `/decompose-proof`, `/split-file`,
`/integrate-learnings`, `/bump-mathlib`, and `/overview` all follow a single pattern:

1. **Multi-step procedures with explicit phase numbers.** A workflow that says "do X, then Y, then Z" silently drops Y when the agent gets tired. A workflow with `PHASE 1` … `PHASE 8` makes phase-skipping visible.
2. **Required artifacts.** Each phase produces a structured output — a punch-list, a status block, a gate-status table, a per-hypothesis classification table. The artifact is the proof the phase actually ran. Skipping a step is detectable in the missing or malformed artifact.
3. **No silent skipping.** Every rule, every search method, every hypothesis, every comment, every reviewer point gets explicit status: `applied`, `tried-and-failed`, `n/a: <reason>`. Blank entries are defects. Recent example: `/cleanup`'s Phase-4 worker emits a per-rule status line for every entry in `golfing-rules.md` (sections 1.1 through 3.7), so a worker that silently skipped automation upgrades produces a report with missing rules.
4. **Verification gates between phases.** A phase doesn't complete until its check passes. The `/cleanup` Phase-4 worker can't move past Step 5 without `lean_diagnostic_messages` being clean *and* the diff gates (definition-protection, theorem-statement-protection, lake-build-file) passing. The Phase-0 doctor blocks the whole workflow if the project doesn't currently build.
5. **User-approval pauses for high-blast-radius actions.** Pushing to a remote (`/fix-pr-feedback` Phase 5), executing a file split (`/split-file`), dispatching decomposition (`/decompose-proof`), applying big-change generalisations (`/generalise` Phase 8), and integrating ambiguous community learnings (`/integrate-learnings` 5c) all stop at an explicit `AWAITING USER APPROVAL` line and wait. No silent push, no silent overwrite, no "while we're here".
6. **Cleanup discipline as algorithm, not vibe.** `/develop`'s cleanup-cadence is "every 3 proof tickets per file → cleanup ticket; finals per file; pre-milestone cleanup-all; final cleanup-all", checked at every ticket pickup and every replanning. "Insert a cleanup every 3-5 proof tickets" was getting skipped; an algorithm with a verify-count check before saving the board doesn't.
7. **Diff-level gating, not just LSP diagnostics.** Borrowed from [shouyi](https://github.com/frenzymath/shouyi): every AI-generated edit gets diff-checked against gates that catch *categorical* mistakes (touched a `def` line that wasn't supposed to change; modified a `theorem` statement during what was supposed to be a proof-only golf). LSP diagnostics catch type errors; gates catch policy violations.

The throughline: **enforcement happens through artifacts the agent must emit, not through
guidelines the agent should remember.**

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

## Project Structure

```
mathlib-quality/
├── commands/                    # Slash command implementations
│   ├── develop.md               # Planning-only: mathlib search, API design, detailed tickets
│   ├── beastmode.md             # Marathon execution: spawn sub-tickets, replan, stop at nothing
│   ├── cleanup.md               # Style audit + fix + golf (10-phase, 4 hard gates incl. inequality orientation)
│   ├── cleanup-all.md           # Project-wide cleanup (one /cleanup per file)
│   ├── decompose-proof.md       # Break long proofs into helper lemmas (with approval gate)
│   ├── expert-review.md         # Two-mode external review: brief → wait → integrate reply into tickets
│   ├── generalise.md            # Weaken hypotheses; mechanical pass + literature search; user approval for big changes
│   ├── split-file.md            # Split files >1000 lines (with approval gate)
│   ├── overview.md              # Per-declaration project inventory
│   ├── project-status.md        # Chat-only mathematical status: three-tier progress, on-target / blockers
│   ├── pre-submit.md            # Final pre-PR checklist
│   ├── fix-pr-feedback.md       # 8 phases: fetch → fix → coverage check → STOP → push → watch CI
│   ├── bump-mathlib.md          # Bump mathlib + fix breakage (cache verification gate)
│   ├── blueprint.md             # Author/update the project's verso-blueprint
│   ├── unformalise.md           # Render one Lean decl as mathematics (Unicode / Verso / Markdown)
│   ├── teach.md                 # Record a project-specific pattern
│   ├── contribute.md            # Push local learnings back as a PR
│   ├── integrate-learnings.md   # (maintainers) merge contributed learnings into the reference docs
│   └── setup-chatgpt.md         # Configure the ChatGPT MCP server
├── skills/mathlib-quality/
│   ├── SKILL.md                 # Main skill definition
│   └── references/              # Authoritative reference docs read by workers:
│       ├── style-rules.md           # File structure, formatting, deprecation, inequality orientation
│       ├── naming-conventions.md    # snake_case/camelCase/UpperCamelCase + symbol dictionary
│       ├── golfing-rules.md         # Phase 1/2/3 rules (instant wins, automation, cleanup)
│       ├── proof-patterns.md        # Curated patterns + anti-patterns
│       ├── mathlib-search.md        # Five-method exhaustive search + six strict rules
│       ├── generalisation-patterns.md  # Typeclass-weakening catalogue
│       ├── cleanup-gates.md         # Diff gates for /cleanup (borrowed from shouyi)
│       ├── blueprint-conventions.md # Verso authoring + CI deployment gotchas
│       ├── pr-feedback-examples.md  # Curated review-category examples
│       └── linter-checks.md         # Mathlib's built-in linters
├── scripts/
│   └── style_checker.sh         # Local Lean file style validation
└── data/
    └── community_learnings/     # /contribute submissions; archived/ once merged
```

## Acknowledgements

This plugin builds on tools, ideas, and writing from across the Lean / mathlib
community. In particular:

### Skill design and tooling

- **[frenzymath/shouyi](https://github.com/frenzymath/shouyi)** — the **gates pattern** that
  `/cleanup` uses in Phase 0 (pre-flight `lake build` doctor), Phase 4 (per-worker diff
  gates), and Phase 6 (file-level cumulative gates). Shouyi treats every AI-generated
  edit as a diff that must pass programmatic gates (`definition_protected`,
  `theorem_statement_protected`, `lake_build_file`, `docstring_only_changes`) before
  acceptance — a structurally more robust pattern than "edit, then diagnose afterwards".
  See `references/cleanup-gates.md`.
- **[cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills)** —
  multi-cycle proving approach and proof-golfing methodology, plus the Lean 4
  development workflows that `/develop` builds on.
- **[oOo0oOo/lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)** — the MCP server
  that gives every command sub-second feedback (`lean_goal`, `lean_diagnostic_messages`,
  `lean_multi_attempt`, `lean_loogle`, etc.) instead of 30+ second `lake build` cycles.
  Nearly every command depends on it.
- **[delta-lab-ai/Lean-Finder](https://huggingface.co/spaces/delta-lab-ai/Lean-Finder)**
  — AI-powered mathlib search supporting both type signatures and natural-language
  queries; method (A) of the five-method search-status block in `/cleanup`'s Phase-4
  MATHLIB audit. See `references/mathlib-search.md`.
- **[kim-em/botbaki](https://github.com/kim-em/botbaki)** — style conventions and
  formatting guidelines that informed early versions of `style-rules.md`.

### Authoritative content sources

- **[leanprover-community style guide](https://leanprover-community.github.io/contribute/style.html)**
  — the canonical reference for `references/style-rules.md`. All file-structure rules,
  formatting conventions, indentation, line-length, and tactic-mode style come from
  here.
- **[leanprover-community naming guide](https://leanprover-community.github.io/contribute/naming.html)**
  — the canonical reference for `references/naming-conventions.md` (snake_case for
  lemmas, lowerCamelCase for defs, the symbol dictionary, the `conclusion_of_hypothesis`
  pattern, etc.).
- **[leanprover-community PR review guide](https://leanprover-community.github.io/contribute/pr-review.html)**
  — informs the review-categories structure in `references/pr-feedback-examples.md`.

### Community contributors

Each archived JSONL in `data/community_learnings/archived/` represents lessons learned by
other Lean users on real projects (Eisenstein series cleanup, Hecke algebra formalisation,
modular forms PR reviews, version-bump breakage, file-deprecation conventions, blueprint
deployment, inequality orientation, etc.). When consensus emerges across multiple
contributions (3+ occurrences), `/integrate-learnings` propagates the teaching into the
relevant reference doc.

## Contributing

1. Fork the repository
2. Make changes
3. Test locally: `/plugin marketplace add /path/to/your/fork`
4. Submit a PR

## License

MIT License -- see [LICENSE](LICENSE)
