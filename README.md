# mathlib-quality

A [Claude Code](https://docs.anthropic.com/en/docs/claude-code) skill plugin for developing, proving, cleaning up, and bringing Lean 4 code up to [mathlib](https://github.com/leanprover-community/mathlib4) standards.

Twenty-one commands spanning the whole workflow: **plan → prove → cleanup → assess mathlib-fit → blueprint → self-review → PR**. Every workflow is methodical, phase-numbered, and gated (missing artifacts fail the step); mathematical judgement is enforced through required evidence rather than through post-hoc review.

## Sibling: [`MQSlim`](https://github.com/CBirkbeck/MQSlim)

A [parallel slim plugin](https://github.com/CBirkbeck/MQSlim) that shadows this
one — same workflows, same load-bearing rails, restated in the "trust frontier-
model judgement; minimal instructions" style Anthropic's skill-authoring guide
explicitly recommends. Load both together and pick per task by typing `/cleanup`
(verbose, gated) vs. `/clnup` (slim). MQSlim tests the hypothesis that
frontier models produce better output when the prompts state the goal + the
gates that catch real failures, and then get out of the way.

## What It Does

### Develop New Mathematics — Plan with `/develop`, then Execute with `/beastmode`

The development workflow is **split into planning and execution** to prevent the "agent
reconsiders the whole approach mid-proof" failure mode. `/develop` does the strategic
thinking; `/beastmode` does the tactical implementation; neither does the other's
job.

**`/develop` — planning only.**

- **Comprehensive plan** from your references; exhaustive mathlib search; API design for every new declaration.
- **One conclusion per declaration.** A result whose statement would bundle several independently-provable conclusions (a top-level `∧`-chain, source parts (i)/(ii)/(iii)) is split at planning time — one lemma per part, each with its own name and minimal hypotheses; any kept bundle is a one-line `⟨…⟩` assembly. Long theorem statements never get born. Exceptions (shared-witness existentials, simultaneous-induction bundles) in `references/statement-splitting.md`.
- **Detailed self-contained tickets.** Every proof/definition ticket contains the full **Lean Statement**, a numbered **Proof Sketch** citing sources, the **Mathlib lemmas needed** (verified to exist), the **Sources** with bibliographic info, and the **Generality decision**. Detailed enough that no replanning is needed once execution starts.
- **Algorithmic cleanup-cadence**: every 3 proof tickets per file → cleanup ticket; per-file finals; pre-milestone `/cleanup-all`; final-of-everything cleanup. The cadence is verified at planning time and re-checked at every resume audit.
- **Resume & takeover modes**: `--continue` audits the ticket board against the current code and proposes updates (including missing cleanup tickets); `--takeover` creates a plan for an existing project. Both end with a hand-off to `/beastmode`.
- **No execution.** Once the board is approved, `/develop` stops.

**`/beastmode` — marathon execution. Stops at nothing — but stays on-target.**

- **Pick a ticket, finish the goal.** No matter how deep the path goes. When a sub-step needs a missing lemma, missing dependency, or sub-result that isn't on the board, the worker spawns a sub-ticket *in /develop's ticket-template format* and immediately works it. When the parent's sketch turns out to be wrong as a strategy, the worker invokes `/develop --continue` to replan inline and keeps going.
- **Statements stay small (Tier A5).** A ticket or would-be sub-ticket whose statement bundles several independently-provable conclusions is split before proving: one sub-ticket per part, then the bundled declaration is discharged as a one-line `⟨…⟩` assembly. Spawned sub-tickets are born single-conclusion.
- **On-target vigilance, continuously.** Before each sub-ticket and step, the worker confirms: serves the plan's main goal? stays in the project's mathematical area? a refinement, not a divergence? Vigilance is *for* on-target work, not against it.
- **Scope growth that stays on-target is great news.** A "two lemmas" step turning out to need ten is more mathematics captured — exactly the point of the marathon. The harder the work, the more energy goes in (Super Saiyan ethos: the stronger the opponent, the stronger you get).
- **No recursion cap, no time budget.** "It's late", "this is taking a while", "we're 5 sub-tickets deep", "let me try a different approach" — none of these are legitimate stops.
- **Only legitimate stops**: DONE / SCOPE-DEFINITION ERROR (statement actually wrong) / OFF-TRACK (drift onto material genuinely outside the project's mathematical area, with concrete evidence) / BROKEN BASELINE (`lake build` broken on entry).
- **Quality enforced throughout** — no `sorry`, no new axioms (`#print axioms` checked), maximum generality, gates run on the diff before marking the ticket done.

### Clean Up Existing Code (`/cleanup`)

Methodical **11-phase** workflow for any Lean file. Absorbed what were once three separate commands (`/check-style`, `/check-mathlib`, and the original `/cleanup`):

- **Phase 0 — Doctor**: pre-flight `lake build` baseline check; aborts if the project doesn't currently compile.
- **Phase 2 — Style audit**: full numbered punch-list (file-level + linter findings + per-declaration light scan). No fixes yet.
- **Phase 3 — File-level fixes**: copyright + module docstring (CREATED if missing) + imports (skipped on Lean module-system files) + section headers preserved (`/-! ## -/` headers are standard mathlib practice; only contentless ones removed) + `set_option` removal + batched mechanical replacements (`λ` → `fun`, `$` → `<|`, `push_neg` → `push Not`, `haveI`/`letI` → anonymous `have`/`let`).
- **Phase 4 — Per-declaration deep cleanup**: one dedicated agent per declaration, **sequential on the same file** (parallel workers silently clobber each other's edits). **22-item audit** with required status blocks: every golfing rule, the **five-method mathlib search** (with the six strict mathlib-replacement rules), the **inline mechanical generalisation pass**, plus specific checks including **normal-form**, **syntactic generality**, **superfluous-typeclass** audit (Yang Stage 5), **cast audit**, **instance-name audit**, and the **inequality orientation** check.
- **Phase 5 — Refactoring (split into 5a + 5b)**. Phase-4 workers never rename in place — parallel workers race on shared call sites. They append to `.mathlib-quality/renames.jsonl`. **5a** applies non-rename cross-file refactoring; **5b** drains the rename queue with a repo-wide sequential pass.
- **Phase 6 — Final verification + gates**: `definition_protected`, `theorem_statement_protected`, `lake_build_file`, `cumulative_no_unintended_breakage` — borrowed from [shouyi](https://github.com/frenzymath/shouyi) — plus the four hard **content gates** (`naming_gate`, `line_packing_gate` with per-line arithmetic check, `structure_gate`, `inequality_orientation_gate`).
- **Phase 6.5 — Simplify pass**: hand off to the built-in `/simplify` skill for a holistic sweep; re-run gates if it modified anything.
- **Phase 6.6 — Buzz pass**: hand off to `/buzz` — profiled sweep of the file, trace-driven fixes for anything over the elaboration budget (<1s per declaration); deferrals feed `/decompose-proof`, big performance changes are flagged for approval. Clean AND fast.
- **Phase 7 — Report**: one consolidated report with all required-artifact status blocks.

Every phase produces a required artifact; missing or blank artifacts fail the phase. Worker phase-checklists surface skipped steps.

### Make Slow Proofs Fast (`/buzz`)

The workflow a mathlib reviewer applies to an AI-written PR, automated: compile each file and watch the **orange bars** (the editor's still-elaborating indicator); for the few declarations whose bars linger, read the traces, find the issue, fix it — then check the other slow declarations for the **same issue** before diagnosing them from scratch. Target: **every declaration elaborates in under a second**.

- **Sweep** — one profiled compile per target file (`lake env lean -Dprofiler=true`), producing a per-declaration timing table. PR mode by default (files changed vs the default branch); also single file, single declaration, `--all`, and `--budget <ms>` (default 1000).
- **Diagnose worst-first** — escalation ladder: `lean_profile_proof` → `trace.profiler` tree → targeted traces (`synthInstance` / `isDefEq` / `simp.rewrite` / `diagnostics`), classified against the **eight-cause taxonomy** in `references/profiling.md` (instance-synthesis blowup, fat simp, defeq blowup, heavy terminal automation, metavariable churn, coercion churn, duplicated subterms, kernel replay) — each cause with its trace signature and fixes in preference order.
- **Same-issue propagation (binding)** — root cause #1 is tested against every remaining slow declaration *before* any fresh diagnosis. One PR's slow declarations nearly always share an author-pattern; this "it's the same issue" step is what makes the human version of the workflow fast, and it is a required phase here.
- **Measured fixes only** — before/after in wall-clock and heartbeats (`count_heartbeats`, temporary); a declaration is only deferred after ≥3 measured fix attempts, and deferrals route to `/decompose-proof` (five 200ms helpers beat one 1s monolith).
- **Hard rules** — statements stay byte-identical; `maxHeartbeats` / `synthInstance.maxHeartbeats` / `maxRecDepth` are never raised (existing raises get *removed*); no `native_decide`; all profiling scaffolding is gate-checked out of the final diff; API-touching fixes (shortcut instances, instance priorities, file-wide attributes) are flagged for user approval, never auto-applied.
- **Runs automatically as `/cleanup` Phase 6.6** — and therefore inside `/beastmode`'s mandatory post-proof cleanup and every `/cleanup-all` worker. Freshly-proven declarations get profiled and fixed before their ticket is marked done; standalone `/buzz` remains the tool for PR-wide sweeps.

### Decide What Belongs in Mathlib (`/mathlibable`)

Slow, methodical, ten-phase workflow that decides whether a single Lean declaration belongs in mathlib. Every invocation runs the full **exhaustive nine-channel literature sweep** (WebSearch ×≥3 + ChatGPT MCP + local refs + nLab + nCatLab + Stacks + MathOverflow + arXiv) — there is no `--quick` flag; the slowness is the point.

- **Phase 3 — literature** grounds the analysis in what the field actually calls this + at what generality.
- **Phase 4a-c — generality vs literature-standard form AND Bourbaki 2.0 modern-idiom check** (contemporary typeclass / filter / universal-property / bundled-type / module / higher-categorical formulations) + **Q8 concrete-via-abstract** (proof-outruns-the-statement diagnostic) + **Q9 false-generalisation guard** (widening that preserves mathematical content, not just elaboration).
- **Phase 4.5 — diamond/defeq risk** for `def`/`class`/`instance`.
- **Phase 4.6 — proof strategy optimality** (Yang Stage 3): filters over ε-δ; point-free algebra; *shortest path modulo what SHOULD be in mathlib*, not modulo what currently is.
- **Phase 5 — mathlib five-method search** on the user's form AND the literature-standard form AND the modern-idiom form.
- **Phase 5.5 — statement shape** (Yang Stage 5): normal form (RHS convention; avoid O(n²) equivalence-lemma explosion), syntactic generality (mathematically-equivalent form easier to apply), superfluous typeclasses.
- **Phase 6 — composition check** (≤3 mathlib calls?) + call-sites signal.

**Verdict in one of five buckets**, each with required documented evidence:

| Bucket | Fires when |
|---|---|
| `YES-add-as-is` | Novel + maximally general + non-trivial. Rationale must NAME the specific mathlib gap. |
| `YES-but-generalise-first` | Novel in some form, but user's form is strictly narrower AND generalisation is mechanically reachable (Phase 4 verified). Positive evidence required (specific hypothesis to drop + verified weakening). |
| `NO-mathlib-has-it` | Cite the existing mathlib decl by full qualified name; ≤1-line follow-from. |
| `NO-composable-from-mathlib` | Building blocks in mathlib; composition sketch ≤3 lines. |
| `BORDERLINE-needs-human` | Numbered questions ≤5 for the user. |

**Cost is NOT a verdict factor** — EXPENSIVE generalisations are explicitly worth doing (mathlib is Bourbaki 2.0). The Phase-7 verdict gate rejects unsupported verdicts, cost-based downgrades, and unverified "looks generalise-able" YES-but-generalise-first (five named false-positive routing classes catalogued in `references/mathlibable-verdicts.md`).

**Mode A**: single declaration per invocation. **Mode B**: `/mathlibable <file.lean>` or multi-file — orchestrator-worker with one Agent per public decl (def-first ordering, verdict inheritance for `:= rfl` glue lemmas, re-aim when parent is `NO` because of a more-general mathlib def). Also runs as **`/overview` Step 9** for project-wide mathlibable assessment.

### Additional Tools

- **`/project-status`** — chat-only mathematical status report. Reads the project's `.lean` files (plus `plan.md` / `tickets.md` if present) and answers four questions in mathematical English: what result is the worker on, what (if anything) is blocked and what is mathematically missing, how does the current work connect to the overall goal, and how far along is the whole project. **Three-tier progress** — code-level coverage (declarations sorry-free), main-goal chain coverage (only the dependency closure of the main result), and distance-to-unconditional (parametric hypotheses on the main goal still to discharge). Unicode math only, no LaTeX. Read-only — no server, no browser.
- **`/generalise`** — weaken assumptions on a single lemma/def: typeclass-hierarchy walk, drop-test, point-localise, strict→weak, plus mandatory literature search; auto-applies small safe changes, presents big changes as a numbered approval menu (also runs inline as part of `/cleanup` Phase 4)
- **`/decompose-proof`** — break proofs >30 lines into focused helper lemmas (with mandatory user approval gate before dispatch)
- **`/buzz`** — make slow proofs fast (target: each declaration elaborates in <1s). Sweeps the changed files with one profiled compile each, trace-diagnoses the worst declaration to a named root cause (instance-synthesis blowup, fat simp, defeq blowup, heavy automation, …), applies a measured fix, then tests the *same* root cause on the other slow declarations before diagnosing them fresh. Statements stay byte-identical; `maxHeartbeats` raises are removed, never added; the trace-reading and fix-pattern knowledge lives in `references/profiling.md`. Also runs automatically as `/cleanup`'s Phase 6.6, so beastmode-proven declarations and `/cleanup-all` sweeps get buzzed too
- **`/expert-review`** — produce a self-contained mathematical brief (`REVIEW_BRIEF.md`) for an external reviewer with no repo access; pure math, no Lean, no file paths; then in Mode 2 (`--reply`) integrate the reviewer's response into ticket-board updates
- **`/blueprint`** — author or update the project's [verso-blueprint](https://github.com/leanprover/verso-blueprint) — the Verso-based Lean-native artifact behind verso-sphere-packing, verso-flt, verso-carleson, verso-noperthedron, verso-algebraic-combinatorics. Chapter files are `.lean` modules; statements use `:::theorem "label" (lean := "Foo.bar")` directives; dep-graph edges use `{uses "label"}[]`; math is KaTeX (``$`...` `` inline, ``$$`...` `` display). Verso auto-computes completion status from `(lean := …)` — no manual `\leanok` to maintain. Seven-phase workflow: doctor → enumerate (diff against existing chapters) → plan → prose context → author (one worker per declaration; Verso directives only) → cross-link pass → hand-off (`./scripts/ci-pages.sh`; verify `_out/site/html-multi/`). Whole-project default; modes for single-file, `--decl <Foo.bar>` (single decl + closure), `--update` (drift-only), `--check` (inventory + diff), `--migrate-from-latex [<dir>]` (one-shot mechanical 1:1 conversion of a legacy `leanblueprint` LaTeX tree)
- **`/unformalise`** — turn one Lean declaration into mathematics. Unicode terminal render by default (Γ, ℂ, ℍ, →, ≤ — readable in chat); then `[b]` blueprint as Verso / `[v]` Verso markup to stdout / `[m]` Markdown / `[n]` terminal-only. Non-interactive: `--verso`, `--md`, `--blueprint`. The conversational front door for `/blueprint --decl`
- **`/fix-pr-feedback`** — fetch every PR comment, fix locally, **stop for explicit user approval before pushing**, then watch CI to completion (`gh pr checks --watch` runs in background as the wake-timer). Every commit and any PR-description update follows binding conventions: short imperative subject, concrete bullet body, dependencies surfaced via a `Depends on #1234` line, Claude co-author footer.
- **`/bump-mathlib`** — bump mathlib version and fix the resulting breakage; documents recurring patterns from upstream evolution (Splits binary→unary refactor, IsX field-name normalisation, etc.)
- **`/pre-submit`** — final pre-PR checklist
- **`/self-review`** — **N rounds of neutral, independent review-and-implement before a PR (default 3; `/self-review n` sets n).** Each round spawns a **fresh, unbiased review `Agent`** (a new dispatch per round, never `SendMessage`, so no round anchors on the last), applying techniques from the built-in `/review`/`/code-review` (verify-before-report, steelman the author's choice) and `/check-style`, specialised to four Lean dimensions: **(1) definition necessity** (is much lost if a `def` were `notation`/`abbrev`/inlined?), **(2) generalisation** (how far and in what way, tested where cheap), **(3) automation** (best use of `simp`/`grind`/`aesop`/`fun_prop`/project-local tactics — *deterministic automation beats a long non-deterministic hand-rolled proof*, claims tested via `lean_multi_attempt`), and **(4) mathlib naming/style**. The driving instance then reports the findings to the user (and to the PR thread if one exists; `--no-pr` forces chat-only), **implements every suggestion** (a change that breaks the build is attempted → reverted → documented for the next round, never silently skipped), reports the summary, and relaunches until n rounds are done. The reviewer stays objective and self-sceptical yet decisive, and **never rubber-stamps — not even on the final round**; termination is the loop's fixed n, not the reviewer's call. No commits, no pushes — changes are left in the working tree. Scope: bare = changed files vs base; also `<file>`, `<file> <decl>`
- **`/overview`** — **project survey + per-decl mathlibable assessment.** Per-file inventory + cross-file analyses (mathlib API audit, moral duplications, generalisation opportunities, missing API, junk identification) + **Step 9 Mathlibable Assessment**: dispatches one `/mathlibable` Agent per non-skipped public decl running the full 10-phase exhaustive workflow. Aggregates verdicts into per-bucket action lists in `PROJECT_OVERVIEW.md` (open mathlib PR / run `/generalise` / delete + reuse / inline composition / open questions). Per-decl detail reports go to `.mathlib-quality/overview/mathlibable/<decl>.md`. Step 9 is hours-long on big projects; pass `--skip-mathlibable` for a faster draft view that runs all other steps
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
| `/develop` | **Planning only, with binding methodical-decomposition pre-work.** Mathlib search, API design, then a per-result decomposition pass: prose proof + ordered lemma list (**one leaf per part** — multi-part results never become one long declaration; kept bundles are one-line `⟨…⟩` assemblies) + **`:= by sorry` skeleton stated in the project's Lean files (must `lake build` clean)** + **verbatim source quotes per leaf** + Lean ↔ source match paragraphs + per-leaf provability check. Saved as `decomposition.md`; tickets only after every leaf verified. **`--decompose` flag** runs just this pre-work pass and stops, for iterating on the decomposition before committing to a ticket board. |
| `/beastmode` | **Marathon execution. Stops at nothing — but stays on-target.** Pick a ticket and finish the goal — spawn sub-tickets in `/develop`'s format for missing lemmas, split multi-part statements one sub-ticket per part (Tier A5), replan via `/develop --continue` for wrong strategies, no recursion cap, no time budget. **Super Saiyan ethos**: scope growth that stays on-target is great news, not a stop signal. **Multi-session work is the target, not an exit.** Only stops: DONE / SCOPE-DEFINITION ERROR / OFF-TRACK (genuine, with concrete evidence) / BROKEN BASELINE. |
| `/cleanup` | Style audit + cleanup + golf (whole file or single declaration). **11-phase** methodical workflow with per-worker phase checklist; Phase 5 split into 5a (non-rename refactoring) and 5b (dedicated rename pass — workers append to `.mathlib-quality/renames.jsonl`, Phase 5b applies them repo-wide in one sequential pass); ends with the Phase 6.5 `/simplify` and Phase 6.6 `/buzz` (performance) hand-offs. Absorbed `/check-style` (Phase 2 audit) and `/check-mathlib` (Phase 4 item 13: five-method search-status block + six strict mathlib-replacement rules). |
| `/cleanup-all` | **Orchestrator-worker marathon.** Main session dispatches batched `Agent` calls with tight prompts (working dir + branch + build + file list + target); workers do all file reading, LSP, edits, and build verification in fresh contexts. Between dispatches the orchestrator emits a one-line scoreboard, nothing else. The pattern that sustained a real 28-day, 9000-message, 395-dispatch cleanup session. |
| `/project-status` | Chat-only mathematical status: what's the worker on, what's blocked + missing, how it connects to the goal, how far along. **Three-tier progress** (code-level / main-goal chain / parametric-hypotheses discharged). Unicode math, no LaTeX. |
| `/overview` | **Project survey + per-decl mathlibable assessment.** Per-file inventory + cross-file analyses (mathlib API audit, duplications, generalisation, missing API, junk) + **Step 9 Mathlibable Assessment**: dispatches one `/mathlibable` Agent per non-skipped public decl running the full 10-phase exhaustive workflow. Aggregates verdicts into per-bucket action lists in `PROJECT_OVERVIEW.md`. `--skip-mathlibable` for the faster draft view. |
| `/expert-review` | Two-mode external review: produce a self-contained math brief (`REVIEW_BRIEF.md`), wait for the reviewer's response, then integrate their guidance into the ticket board |
| `/generalise` | Weaken assumptions on a lemma or definition: mechanical weakenings + literature search; auto-apply small safe changes, propose big changes as a numbered menu |
| `/decompose-proof` | Break long proofs into helper lemmas |
| `/buzz` | **Profile → trace → fix slow declarations (target <1s each).** Headless "orange-bar watch": one profiled compile per file → per-decl timing table → trace-driven diagnosis (`trace.profiler`, `synthInstance`, `isDefEq`, simp traces) against the eight-cause taxonomy in `references/profiling.md` → measured fixes. **Same-issue propagation**: the first root cause is tested on every other slow decl before any fresh diagnosis. Statements never change; `maxHeartbeats` never goes up (existing raises get removed); profiling scaffolding is gate-checked out of the final diff. PR mode by default (changed files vs default branch); also `<file>`, `<file> <decl>`, `--all`, `--budget <ms>`. |
| `/split-file` | Split files >1000 lines (with approval gate) |
| `/pre-submit` | Pre-PR submission checklist |
| `/self-review` | **N rounds of neutral, independent review-and-implement before a PR (default 3).** Each round spawns a **fresh, unbiased review `Agent`** (new dispatch per round, not `SendMessage`) applying `/review` + `/check-style` techniques across four Lean dimensions — **definition necessity** (`def` vs notation), **generalisation** (how far/in what way), **automation** (deterministic automation beats a hand-rolled non-deterministic proof; claims tested via `lean_multi_attempt`), **mathlib naming/style** — then reports findings to the user (and to the PR thread if one exists), implements **every** suggestion (build-breaking ones attempted → reverted → documented, never silently skipped), reports the summary, and relaunches until N rounds are done. Steelmans before reporting; **never rubber-stamps, even on the final round** — termination is the loop's fixed N. No commits/pushes. Scope: bare = changed files vs base, `<file>`, `<file> <decl>`, `--no-pr`. |
| `/fix-pr-feedback` | Fetch PR comments → fix → STOP for approval → push → watch CI. Every commit and PR-description update follows binding conventions (short imperative subject, concrete bullet body, `Depends on` line, Claude co-author footer). |
| `/bump-mathlib` | Bump mathlib version and fix breakage |
| `/mathlibable` | **Decide whether a Lean declaration belongs in mathlib.** Slow, methodical, ten-phase gated workflow. Every invocation runs the full **EXHAUSTIVE** literature sweep (WebSearch ×≥3 + ChatGPT MCP + local refs + nLab + nCatLab + Stacks + MathOverflow + arXiv) — no `--quick` flag. Generality analysis vs literature-standard AND the **Bourbaki 2.0 modern-mathlib-idiom check** (contemporary typeclass / filter / universal-property / bundled-type / module / higher-categorical formulations). Diamond/defeq risk assessment for `def`/`class`/`instance`. Mathlib five-method search on the user's form, the literature-standard form, AND the modern-idiom form. Composition check (≤3 mathlib calls?). Verdict in one of five buckets (`YES-add-as-is`, `YES-but-generalise-first`, `NO-mathlib-has-it`, `NO-composable-from-mathlib`, `BORDERLINE-needs-human`), each with required documented evidence. Cost is NOT a verdict factor — EXPENSIVE generalisations are explicitly worth doing (mathlib is Bourbaki 2.0). **Mode A**: single declaration per call. **Mode B**: `/mathlibable <file.lean>` or multi-file — orchestrator-worker dispatches one Agent per public decl sequentially with one-line scoreboard between; writes `MATHLIBABLE_REPORT.md`. Also runs as `/overview` Step 9 in the same shape. Bourbaki 2.0 philosophy + canonical modernisation cases (modules / filters / `Submodule` / measure-triple / universal-property limits) + worked examples per bucket in `references/mathlibable-verdicts.md`. |
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
8. **Post-proof cleanup (Phase 6.5, mandatory).** Before mark-done, invokes `Skill(skill="mathlib-quality:cleanup", args="<file> <decl_name>")` on every NEW declaration the ticket produced. `/cleanup` runs its full 11-phase workflow (including 5b rename pass, 6.5 simplify hand-off, and 6.6 buzz performance pass); the per-decl phase-checklist enforcement is `/cleanup`'s own responsibility. Decompose flags spawn `/decompose-proof` sub-tickets (recorded in the ticket's progress notes; G6 sequence-continuation picks them up). Rename queue is drained inside `/cleanup`'s Phase 5b. Gate failures from `/cleanup` block the ticket from being marked done — either the cleanup itself is reverted or the proof itself is the issue (Tier-B SCOPE/DEFINITION-ERROR).
9. **Mark done** + report. If a hard-stop condition fires instead, the report names which step failed, what was tried, and a concrete replanning suggestion.

**Staying alive across turns (the Stop hook).** A model ends its turn after a few minutes of work — that's harness mechanics, not a beastmode bug, and it's why earlier versions stalled. The plugin ships a guarded `Stop` hook (`hooks/beastmode_stop.sh`): while a marathon is active it refuses the turn-end and re-prompts the agent, so one `/beastmode` session sustains across many turns instead of stopping at 2–3 minutes — **even when launched bare, with no `/loop`.** It is gated by a sentinel file (`.mathlib-quality/beastmode_active`) that `/beastmode` writes on start and removes only at a genuine terminal state, and it is fail-safe (inert for every non-beastmode session). To pause or stop: press **Esc**, or `rm .mathlib-quality/beastmode_active`; a progress budget also auto-releases after `BEASTMODE_MAX_BLOCKS` turns (default 30) with no `.lean`/ticket change. The hook spans turns *within* a session; for boards too big for one context window, wrap it as `/loop /beastmode`, which spans *across* sessions.

**When all tickets are done**, run `/pre-submit` for the final-review checklist (no `sorry` anywhere, no new axioms, full project build clean, etc.).

### Cleaning Up Code

```
/cleanup MyFile.lean                # Clean entire file
/cleanup MyFile.lean theorem_name   # Clean one declaration
/cleanup-all                        # Clean every file in project
```

**How `/cleanup` works (11 phases, methodical, no skipping):**

0. **Doctor** — pre-flight: `lake exe cache get`, `lake build` (must pass — without a clean baseline we can't tell what breakage we introduced), LSP responsive on the target file. Aborts if the baseline is broken.
1. **Prepare** — read the file, run `lean_diagnostic_messages`, read the six reference docs (`golfing-rules`, `proof-patterns`, `mathlib-search`, `generalisation-patterns`, `cleanup-gates`, `mathlib-review-stages`), build the declaration list.
2. **Style audit** — complete numbered punch-list (file-level + linter findings + per-declaration light scan). No fixes yet. Replaces what used to be `/check-style`.
3. **File-level fixes** — copyright, **module docstring (CREATED if missing)**, imports (skipped on Lean module-system files — `public import` is semantic), section headers preserved (only contentless ones removed), file-level `set_option`, batch mechanical replacements (`λ`→`fun`, `$`→`<|`, `push_neg`→`push Not`, `haveI`/`letI`→anonymous `have`/`let`).
4. **Per-declaration deep cleanup** — one dedicated agent per declaration, **sequential on the same file** (parallel workers silently clobber each other's edits — the second worker's Edit sees a file that has drifted since its Read). The worker reads the reference docs, runs the **22-item audit** with required status blocks for: every golfing rule (1.1 → 3.7), the **five-method mathlib search** (six strict mathlib-replacement rules — replaces `/check-mathlib`), the **inline mechanical generalisation pass** (catalogue-driven typeclass-hierarchy walk, drop-test, pointwise / strict→weak) with a **"beware false generalisations"** check, and (for public decls) a literature search. Also audits: **inequality orientation** (item 19; `≤` not `≥`, `<` not `>`), **normal form** (item 20; RHS convention), **syntactic generality** (item 21), **import fanout** (item 22), **casts** (item 23; drop redundant ascriptions), **instance-name** (item 24; anonymous by default). Then runs the **per-worker diff gates** — including the hard `structure_gate` / `naming_gate` / `line_packing_gate` / `inequality_orientation_gate`: pass/fail, not deferrable. `line_packing_gate` uses per-line arithmetic (`current + 1 + next-token ≤ 100`). `naming_gate` forbids single-letter public names, scheme-number patterns, and `_ge_` / `_gt_` orientation-rule violations.
5. **Refactoring (split into 5a + 5b).**
   - **5a — Non-rename refactoring:** cross-declaration items from Phase 4 worker reports — mathlib replacements, junk-def inlining, big-change generalisations escalated to standalone `/generalise` (which has the user-approval gate on big changes).
   - **5b — Rename pass:** Phase 4 workers never rename in place (parallel workers would race on shared call sites). They append `{old, new, scope, file, …}` JSON to `.mathlib-quality/renames.jsonl`. Phase 5b reads the queue, dedupes, conflict-checks, then applies each rename sequentially across the whole repo with `Grep` + `Edit replace_all` + `lean_diagnostic_messages` between each. The queue is truncated when done.
6. **Final verification** — file-level diff gates (`lake_build_file`, `lake_build`, `definition_protected`, `theorem_statement_protected`, `cumulative_no_unintended_breakage`). Untraceable signature changes are gate failures; only continues if Phase 6 is `pass`.
6½. **Simplify pass** — hand off to the **built-in `/simplify` skill** (provided by Claude Code) for a holistic review. Where `/cleanup` is checklist-driven, `/simplify` is holistic — it spots duplicated proof skeletons across the file, cross-cutting issues the per-declaration workers missed, and quality issues that don't match any specific rule. If `/simplify` makes changes, the gates from Phase 6 are re-run on the new state. Required artifact: simplify-pass status block.
6⅔. **Buzz pass** — hand off to **`/buzz`** for performance: one profiled compile of the file, trace-driven diagnosis and measured fixes for every declaration over the elaboration budget (default 1s). Statements stay byte-identical, limits are never raised, and any `maxHeartbeats` raise still present gets removed. Declarations that stay over budget after ≥3 measured attempts are deferred to `/decompose-proof`; big performance changes (shortcut instances etc.) are flagged for user approval. Required artifact: buzz-pass status block.
7. **Report** — one consolidated report including the Phase-0 baseline, the audit punch-list, per-declaration before/after, refactoring done, gate-status table, and the simplify- and buzz-pass outcomes.

**No-skipping enforcement.** `/cleanup`'s anti-skip defence sits on four mechanisms: required artifacts (status blocks the agent must emit — golf-rule status, mathlib search-status, generalisation status, gate status, simplify status, buzz status; missing or blank cells = step skipped), verification gates between phases (`lake build` baseline, diagnostics-clean), diff gates on edits (definition_protected, theorem_statement_protected — catches *out-of-scope* edits), and user-approval pauses for high-blast-radius actions. The Phase-7 report's required-section list lets a missing artifact fail the report.

### Making Slow Proofs Fast

```
/buzz                               # PR mode: profile the files changed vs the default branch
/buzz MyFile.lean                   # Sweep one file
/buzz MyFile.lean slow_theorem      # One declaration, straight to diagnosis
/buzz --all                         # Every project file (audit mode)
/buzz --budget 500                  # Tighter per-decl budget (default 1000ms)
```

**How `/buzz` works:** doctor (baseline build must be green) → **sweep** (one profiled compile per file; per-decl timing table; SLOW = over budget, and any declaration carrying a `maxHeartbeats` raise is SLOW by definition) → **diagnose** the worst declaration down the trace ladder to a named root cause (required diagnosis block with evidence — no pattern-guessing) → **fix + re-measure** (success = under budget; both ms and heartbeats recorded) → **propagate** the root cause across the remaining slow declarations before diagnosing any of them fresh → **gates** (statement protection, no limit raises, no leftover profiling scaffolding, build clean, final re-sweep) → before/after report with speedups, removed raises, deferrals, and an approval menu for any API-touching fix. If nothing is over budget, it prints `FAST BOARD` and stops — `/buzz` invents no work.

### Preparing a PR

```
/cleanup MyFile.lean            # Audit + fix + golf (one command; ends with the /buzz pass)
/buzz                           # Or standalone: profile changed files; trace + fix slow decls
/mathlibable Foo.bar            # Is this decl the right shape for mathlib?
/self-review 3                  # 3 rounds of fresh, independent review-and-implement on the diff
/pre-submit MyFile.lean         # Final checklist
```

### Assessing Mathlib-Fit

```
/mathlibable Foo.bar                          # single decl — full 10-phase workflow
/mathlibable Foo/Bar.lean                     # every public decl in file (sequential)
/mathlibable Foo/Bar.lean Baz.lean            # multi-file batch
/overview                                     # project survey + /mathlibable per public decl (Step 9)
/overview --skip-mathlibable                  # faster survey without the Step 9 lit-search sweep
```

Every `/mathlibable` invocation runs the full exhaustive workflow described above; verdicts + per-decl detail reports go to `.mathlib-quality/mathlibable/<decl>.md`. `/overview` aggregates verdicts into per-bucket action lists in `PROJECT_OVERVIEW.md`.

The mental model — Yang's [six stages of reviewing a mathlib PR](skills/mathlib-quality/references/mathlib-review-stages.md), ordered global-to-local:

1. Do we want this result in mathlib? (interest, applications beyond this PR, belongs-elsewhere routing to Archive/CSLib/downstream)
2. Do we want this generality? (encompass every case mathematicians care about; ease downstream development; beware false generalisations)
3. Is the proof strategy optimal? (*shortest path modulo what SHOULD be in mathlib, not modulo what IS*)
4. Is the proof executed correctly?
5. Are results stated correctly in Lean? (normal form; syntactic generality; superfluous typeclasses)
6. Are results presented correctly? (file placement, imports, docstring depth)

`/mathlibable` covers Stages 1–5; `/cleanup` covers Stages 5–6. Stage 5 is the overlap.

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
`/integrate-learnings`, `/bump-mathlib`, and `/overview` — and new commands like `/buzz` —
all follow a single pattern:

1. **Multi-step procedures with explicit phase numbers.** A workflow that says "do X, then Y, then Z" silently drops Y when the agent gets tired. A workflow with `PHASE 1` … `PHASE 8` makes phase-skipping visible.
2. **Required artifacts.** Each phase produces a structured output — a punch-list, a status block, a gate-status table, a per-hypothesis classification table. The artifact is the proof the phase actually ran. Skipping a step is detectable in the missing or malformed artifact.
3. **No silent skipping.** Every rule, every search method, every hypothesis, every comment, every reviewer point gets explicit status: `applied`, `tried-and-failed`, `n/a: <reason>`. Blank entries are defects. Recent example: `/cleanup`'s Phase-4 worker emits a per-rule status line for every entry in `golfing-rules.md` (sections 1.1 through 3.7), so a worker that silently skipped automation upgrades produces a report with missing rules.
4. **Verification gates between phases.** A phase doesn't complete until its check passes. The `/cleanup` Phase-4 worker can't move past Step 5 without `lean_diagnostic_messages` being clean *and* the diff gates (definition-protection, theorem-statement-protection, lake-build-file) passing. The Phase-0 doctor blocks the whole workflow if the project doesn't currently build.
5. **User-approval pauses for high-blast-radius actions.** Pushing to a remote (`/fix-pr-feedback` Phase 5), executing a file split (`/split-file`), dispatching decomposition (`/decompose-proof`), applying big-change generalisations (`/generalise` Phase 8), and integrating ambiguous community learnings (`/integrate-learnings` 5c) all stop at an explicit `AWAITING USER APPROVAL` line and wait. No silent push, no silent overwrite, no "while we're here".
6. **Cleanup discipline as algorithm, not vibe.** `/develop`'s cleanup-cadence is "every 3 proof tickets per file → cleanup ticket; finals per file; pre-milestone cleanup-all; final cleanup-all", checked at every ticket pickup and every replanning. "Insert a cleanup every 3-5 proof tickets" was getting skipped; an algorithm with a verify-count check before saving the board doesn't.
7. **Diff-level gating, not just LSP diagnostics.** Borrowed from [shouyi](https://github.com/frenzymath/shouyi): every AI-generated edit gets diff-checked against gates that catch *categorical* mistakes (touched a `def` line that wasn't supposed to change; modified a `theorem` statement during what was supposed to be a proof-only golf). LSP diagnostics catch type errors; gates catch policy violations.

The throughline: **enforcement happens through artifacts the agent must emit, not through
guidelines the agent should remember.**

## Key Rules

The reference docs (`references/style-rules.md`, `references/naming-conventions.md`, `references/proof-patterns.md`, `references/pr-feedback-examples.md`, `references/mathlib-quality-principles.md`) were originally seeded from a scraped corpus of 3,772 mathlib PRs / 14,063 review comments; the scraped data itself was removed in v0.46.0 once the curated docs took over as the live propagation channel. Contributions flow in via `/contribute` PRs and get propagated into the reference docs by `/integrate-learnings`.

### The Cardinal Rule: Terminal vs Nonterminal `simp`

- **Terminal `simp` must NOT be squeezed** -- leave as `simp` or `simp [lemmas]`
- **Nonterminal `simp` MUST be squeezed** to `simp only [...]`

### Inequality Orientation

Lean code uses `≤` not `≥`, `<` not `>`, **smaller side on the left**. Lemma names follow: `a_le_b` not `b_ge_a`. Docstrings may keep `≥`/`>` where prose reads naturally; the rule is about Lean code. Enforced by `inequality_orientation_gate`.

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

- Line length: **100 codepoints max** (characters, not bytes — `∑ ⧸ ↦` count as 1) — but pack signature lines *toward* 100, including joining `: conclusion :=` onto the last hypothesis line when it fits (per-line arithmetic check enforced by `line_packing_gate`; don't break at 60 when the next token fits)
- Proof length: **50 lines max** (decompose if longer)
- `by` at **end of preceding line**, never on its own line
- **Preserve proof comments** — "'No comments in proofs' is NOT a mathlib style requirement" (maintainer feedback; rule reversed in v0.58.0). Golf re-anchors signpost comments to the rewritten steps; docstring proof-sketches relocate *into* the proof body. Only wrong/stale or tactic-restating comments are removable, with justification
- No `sorry` in committed code
- No new axioms
- No `haveI` / `letI` — Lean 3 habit; the `I` stood for "inline", not "instance". Use anonymous `have :` / `let :` (typeclass resolution picks them up just as well)
- No single-letter public names (`def m`, `theorem f`) — undiscoverable in mathlib search and autocomplete
- No global `noncomputable instance : DecidableEq X := Classical.decEq _` — "as useful as a chocolate teapot" and can shadow genuine `Decidable` instances downstream; use the `classical` tactic in proofs or `open scoped Classical in` before a specific noncomputable def
- No redundant type ascriptions (`(g.det.val : ℝ)` when `g.det.val` is already ℝ) — keep only genuine cross-type coercions

### Naming Conventions

| Declaration | Convention | Example |
|-------------|------------|---------|
| `lemma`/`theorem` | `snake_case` | `continuous_of_bounded` |
| `def` | `lowerCamelCase` | `cauchyPrincipalValue` |
| `structure` | `UpperCamelCase` | `ModularForm` |

Pattern: `conclusion_of_hypothesis` (e.g., `norm_le_of_mem_ball`).

Forbidden name patterns (auto-fail `naming_gate`):
- Scheme numbers: `\d+_\d+_\d+_` (e.g. `miyake_4_6_5_…`), `m\d+_` (e.g. `m6_2_…`), `multipass_`, numeric `_aux\d+`
- Abbreviations: `wt`, `whomog`, `thm`, `eqn`, `imp`, `soln`, `mvpoly`
- Single-letter public names
- `_ge_`, `_gt_` (inequality-orientation rule)

Renames queue to `.mathlib-quality/renames.jsonl` and apply in Phase 5b (repo-wide, sequential) — Phase-4 workers never rename in place.

### Performance Rules

- **Every declaration under ~1 second of elaboration** — reviewers compile files and watch the orange bars; a lingering bar draws a comment. `/buzz` is the workflow (and runs automatically as `/cleanup` Phase 6.6).
- **Never raise `maxHeartbeats`** (or `synthInstance.maxHeartbeats` / `maxRecDepth`) — a raise hides the defect and taxes every future build. Diagnose the root cause from the traces instead (`references/profiling.md`).
- **Measure → fix → re-measure.** A performance "fix" without before/after numbers (ms + heartbeats) is a guess.
- **One root cause per PR.** Slow declarations written by the same author at the same time almost always share it — test the first diagnosis against the rest before diagnosing any of them fresh.
- **When speed and brevity conflict, speed wins** — a squeezed simp or an added `haveI` is accepted where it's the measured hotspot fix; golf never undoes a perf fix.

### Design Buzzphrases (durable heuristics)

- **Shortest path modulo what SHOULD be in mathlib**, not modulo what IS currently in mathlib. Missing API is a separate follow-up, not something to route around.
- **Comments explain _why_, not _what_.** The what is in the code.
- **Rules are meant to be breached. Breaches are meant to be documented.**
- **The best comment is when it is unnecessary.**
- **Mathlib is Bourbaki 2.0.** Adding the *right* declaration in the *right* form is worth the effort — cost is not a reason to ship the wrong shape.
- **Watch the orange bars.** Slow elaboration is a reviewable defect, not a taste question — every declaration under a second.
- **"It's the same issue."** Diagnose one slow declaration thoroughly; test the others against that root cause before diagnosing them fresh.

## Project Structure

```
mathlib-quality/
├── commands/                    # Slash command implementations
│   ├── develop.md               # Planning-only: mathlib search, API design, detailed tickets
│   ├── beastmode.md             # Marathon execution: spawn sub-tickets, replan, stop at nothing
│   ├── cleanup.md               # Style audit + fix + golf (11-phase, 4 hard gates incl. inequality orientation)
│   ├── cleanup-all.md           # Project-wide cleanup (one /cleanup per file)
│   ├── decompose-proof.md       # Break long proofs into helper lemmas (with approval gate)
│   ├── buzz.md                  # Profile → trace → fix slow declarations (<1s each; no maxHeartbeats raises)
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
├── commands/
│   ├── mathlibable.md           # Slow 10-phase workflow: is this the right shape for mathlib? (5 verdict buckets)
│   ├── cleanup-all.md           # Orchestrator-worker project-wide cleanup
│   └── ...                      # (all 22 commands)
├── skills/mathlib-quality/
│   ├── SKILL.md                 # Main skill definition
│   └── references/              # Authoritative reference docs read by workers:
│       ├── style-rules.md              # File structure, formatting, deprecation, inequality orientation
│       ├── naming-conventions.md       # snake_case/camelCase/UpperCamelCase + symbol dictionary
│       ├── golfing-rules.md            # Phase 1/2/3 rules (instant wins, automation, cleanup)
│       ├── proof-patterns.md           # Curated patterns + anti-patterns
│       ├── mathlib-search.md           # Five-method exhaustive search + six strict rules
│       ├── mathlib-review-stages.md    # Yang's six-stage framework: /mathlibable and /cleanup both read
│       ├── mathlibable-verdicts.md     # Verdict definitions, worked cases per bucket, false-positive routing, anti-pattern catalogue
│       ├── generalisation-patterns.md  # Typeclass-weakening catalogue + inversion check
│       ├── cleanup-gates.md            # Diff gates for /cleanup (borrowed from shouyi)
│       ├── statement-splitting.md      # One-conclusion-per-declaration rule (multi-part statements)
│       ├── profiling.md                # Measurement how-to, trace reading, slow-proof root-cause taxonomy
│       ├── blueprint-conventions.md    # Verso authoring + CI deployment gotchas
│       ├── pr-feedback-examples.md     # Curated review-category examples
│       ├── mathlib-quality-principles.md  # Core quality principles
│       └── linter-checks.md            # Mathlib's built-in linters
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
- **The public mathlib-review talk framework** — the six-stage global-to-local
  review order (want this in mathlib? / right generality? / proof strategy
  optimal? / executed correctly? / stated correctly? / presented correctly?)
  that structures `references/mathlib-review-stages.md` and gates `/mathlibable`
  Phases 3–7 and `/cleanup` audit items 20/21/22.

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
