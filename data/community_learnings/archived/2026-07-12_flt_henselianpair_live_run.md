# Live-run feedback: /cleanup + /buzz + /simplify on FLT/Slop/HenselianPair (2026-07-12)

Feedback from a real run of the plugin on an open FLT PR (7 files, 92 declarations, ~1700
lines of commutative-algebra Lean on Henselian pairs, destined for mathlib; reviewed by the
FLT project lead, a mathlib maintainer). Integrated into v0.58.0: items 1–6. Items 7–8
deferred by the maintainer's decision (cost surfacing / light tier; quality-regression
lens incl. the simp-unsqueeze rule).

Integration summary (v0.58.0):

- **P0.1 (comment stripping) — REVERSED** in cleanup item 9, style-rules § Comments in
  Proofs, SKILL.md ×2, README, declaration-fixer-prompt; new `Comments-preserved:` worker
  artifact + Phase-6a comment-preservation check.
- **P0.2 (build gate / hallucinated lemma)** — LSP-unavailable-is-not-a-pass rule in
  /cleanup and /cleanup-all; Phase-6 build gates became cited tool-call gates; new
  Phase-6a new-identifier verification artifact.
- **P1.3 (section dividers)** — rule was factually wrong (mathlib has ~2,500 across ~900
  files); reversed in cleanup 3.3/A.4/6a, style-rules, SKILL.md.
- **P1.4 (module system)** — dialect probe in cleanup Phase 1a; A.3 imports + item-11
  visibility skip on module files; /buzz + profiling.md sweep via `lake lean <file> -- -D…`.
- **P1.5 (line packing)** — conclusion line participates in packing (`: conclusion :=`
  joins the last hypothesis line when it fits); widths are codepoints (`wc -m`), not bytes.
- **P2.6 (.mcp.json)** — removed from the repo and gitignored; /setup-chatgpt owns the
  machine-local config; /mathlibable degrades gracefully without `ask_chatgpt_math`.

---

## Original feedback (verbatim)

**Context.** I (Claude, driving Claude Code) ran `/cleanup`, then `/buzz`, then `/simplify` on
an open FLT PR: `FLT/Slop/HenselianPair/` — 7 files, 92 declarations, ~1700 lines of
commutative-algebra Lean (Henselian pairs, following the Stacks project), explicitly destined
for upstreaming to mathlib. The reviewer is the FLT project lead. This is feedback grounded in
what actually happened on that run, ordered by severity. Overall the tool did real, valuable
work — but two issues would have shipped a broken, worse PR if the run hadn't been checked by
hand.

### What worked well (keep doing this)

- **The core golf is genuinely good.** Per-declaration workers replaced a 5-step `calc` with a
  single rewrite through the right mathlib lemma (`IsCoprime.add_mul_left_right_iff`), collapsed
  `rwa [show …, show …]` chains into `simpa`, and turned multi-line `have`+unit-constructor
  proofs into one-liners. Net −220 lines (~13%) with every theorem statement preserved.
- **Statement/definition protection works.** After the whole run, a normalized diff showed all
  92 signatures and all 9 `def` bodies byte-identical to the original. The `theorem_statement_protected`
  discipline is exactly right and it held.
- **`/buzz` correctly did nothing.** It profiled, found every declaration elaborates <100 ms,
  and stopped. No busywork, no false positives. Good.
- **`/simplify`'s adversarial-verify step earned its keep.** One of its own "confirmed" findings
  was stale (described pre-golf code); the verify pass and a code re-read caught it before it was
  applied.

### P0 — would have shipped real damage

#### 1. Audit item 9, "strip ALL narrative `--` inside the proof," is wrong and actively harmful.

This was the single biggest problem. The workers deleted **22 inline signpost comments** across
the proofs ("factor out the linear factor over `R/I`", "lift the factorisation to `R`", "CRT
identifies `S` with `(R⧸I)×(R⧸M)`", …) and, separately, deleted proof-sketch paragraphs from
three docstrings without relocating them. The reviewer — a mathlib maintainer — flagged this
six times in a row and asked for every one back, with the general instruction:

> "Don't delete helpful comments from proofs. 'No comments in proofs' is NOT a mathlib style
> requirement — many maintainers believe there *should* be more comments in proofs, it's just
> that people don't write them."

**Recommended change.** Reverse this rule. During golf, *preserve* proof comments and re-anchor
them to the rewritten steps. The right principle is the opposite of the current one: mathlib is
under-documented; keep the signposts. Two sub-cases:
- Inline `--` proof comments: never delete; move them to the corresponding golfed step.
- Proof-sketch prose that lives in a *docstring*: it's correct to remove it from the docstring
  (docstrings should say *what*, not *how*), **but relocate it into the proof body as one-line
  comments**, don't delete it.

#### 2. A hallucinated lemma name shipped and broke the build; the Phase-6 build gate did not catch it.

A worker wrote `isUnit_of_mul_eq_one` (doesn't exist; the real lemma is `IsUnit.of_mul_eq_one`,
with the element implicit). It broke `Idempotents.lean`. The worker couldn't catch it because,
under parallel execution, the Lean LSP server was contended and many workers reported they
could not elaborate their file at all ("import lockout"); they honestly returned
`diagnostics_clean:false`, and the run still reported **0 failures**. Nothing surfaced the break
until a full `lake build` was run by hand afterwards.

**Recommended changes.**
- **Phase 6 must run a real `lake build` on every touched module and treat any failure as a hard,
  non-skippable stop.** The current "defer `lake_build_file` to Phase 6" escape, combined with
  per-worker LSP failure, means a whole run can report success while the code doesn't compile.
- **"Every mathlib lemma name must be verified to exist" needs enforcement, not just a prompt
  line.** A cheap post-hoc check (grep each newly-introduced identifier against the mathlib
  source / a `#check`) would have caught this. As written, it relies on the worker's good
  intentions, and a worker that can't run the LSP has none available.
- Treat any worker that returns `diagnostics_clean:false` as **not done**, and re-run it (or
  fail the file) rather than counting it as a pass.

### P1 — wrong or missing rules

#### 3. The section-divider rule (Phase 3.3) is factually wrong.

The command says every `/-! ## … -/` divider below the module docstring "is rejected by
review; delete them." Mathlib itself contains **2517 such dividers across 876 files**. On a
normal mathlib file this rule vandalises structure. (It was a no-op here only because these
files happen to have none.) Recommend deleting the rule.

#### 4. The plugin is unaware of the Lean module system.

These files (and a growing set of mathlib-adjacent projects) begin with `module` /
`public import …` / `@[expose] public section`. Three rules misfire on such files:
- the import-ordering audit (A.3) and the `private`-visibility advice (item 11) assume classic
  `import` and don't apply;
- `/buzz`'s profiling command `lake env lean -Dprofiler=true <file>` throws a spurious
  "definition not exposed" type-mismatch on module files — it needs the `--setup <setup.json>`
  that `lake build` passes, or it can't profile them at all.

Recommend detecting a leading `module` and adapting (skip import/visibility rewrites; pass
`--setup` when profiling).

#### 5. The line-packing gate misses the conclusion line, and should be specified in codepoints.

- The gate packs hypothesis lines but left the **conclusion dangling on its own line** —
  `… (hbI : b - 1 ∈ I) :` then `a = b :=` — in ~25 places where `… : a = b :=` fits within 100.
  Mathlib style puts the conclusion on the last hypothesis line when it fits. The reviewer
  flagged this too. The gate should treat the `: conclusion :=` as part of the packing check.
- The gate talks about "100 chars"; make explicit that it's **codepoints, not bytes**. These
  files are full of `∑ ∈ ⧸ ≤ ↦ ⊥` (3 bytes each), so a byte-based length check invents phantom
  >100 violations and a naive fix would wrongly break correct lines.

### P2 — ergonomics

#### 6. `.mcp.json` hardcodes the author's machine.

`"command": "node", "args": ["/home/chris/.claude/mcp-servers/chatgpt-math/server.js"]` — this
fails on every other machine, so a broken MCP server shows up each session and `/mathlibable`
silently loses one of its literature channels. Make it configurable or degrade gracefully when
absent.

#### 7. Cost and parallelism should be surfaced, and a lighter tier offered. *(DEFERRED)*

A full tier-A Phase-4 worker cost ~45 min and ~128k tokens *per declaration*; a 50-declaration
file is a serial critical path (~13 h) because parallel workers on one file race on edits. Two
asks: (a) state this cost up front so the user can choose scope; (b) offer a reduced pass for
glue/wrapper/`:= rfl` lemmas — `/mathlibable` already has "verdict inheritance for `:= rfl`
glue"; the same idea belongs in `/cleanup`, where running a five-method mathlib search plus a
literature search on `foo_apply := rfl` is pure ceremony. Also note that parallel workers across
*different* files still overwhelm a single shared LSP server (this is what caused issue #2).

#### 8. The gates don't catch silent *quality* regressions. *(DEFERRED)*

The gates are well-designed to catch the AI's structural failure modes (batching, deferring,
signature drift). But several regressions passed every gate because they're semantically fine
and mechanically clean:
- deleting useful comments (item 9 above);
- downgrading `simp only [Polynomial.map_id]` to a bare `simp` — no line saved, strictly less
  robust, and it undid a deliberate choice by the original author.

A final "did this change remove documentation or robustness for no benefit?" review — the kind
`/simplify` is closest to — would catch these. Consider making that lens explicit.

---

*One-line summary: the golf engine and the statement-protection gates are strong; the two things
that need fixing most are (a) stop deleting proof comments, and (b) make a real `lake build` an
unconditional gate so a hallucinated lemma name can't pass as success.*
