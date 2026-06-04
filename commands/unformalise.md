---
name: unformalise
description: Turn a Lean declaration into mathematics. Renders the statement and a paragraph-level proof sketch as Unicode in the terminal by default (Γ, ℂ, →, ≤ — readable in chat without any math renderer). Optionally outputs Verso markup (`--verso`), Markdown (`--md`), or appends the result to the project's verso-blueprint as a Verso `:::theorem "label" (lean := "Foo.bar") ... :::` chunk (`--blueprint`). Single-declaration default; `--closure` walks the dependency closure; a whole `.lean` file is also allowed. Shares the unformalisation logic with `/blueprint` Phase 4 (same prose-quality rules from `references/blueprint-conventions.md`).
---

# /unformalise — Turn Lean into mathematics

Take a Lean declaration and render its **mathematical statement** plus a
**paragraph-level proof sketch** in standard mathematical English. Default output is
Unicode in the terminal — readable directly in chat, without a LaTeX renderer.

This is the conversational front-door for the same unformalisation logic that
`/blueprint` Phase 4 uses to author whole-project blueprints. Use `/unformalise` when
you want to *see* the math first; use `/blueprint` when you want to *commit* the math
to the project artifact.

## Usage

```
/unformalise <Foo.bar>                  # single declaration, Unicode in terminal (default)
/unformalise <Foo.bar> --closure        # decl + dependency closure (every {uses} target)
/unformalise <file.lean>                # every public declaration in the file
/unformalise <Foo.bar> --verso          # print Verso directives to stdout (no blueprint write)
/unformalise <Foo.bar> --md             # print GitHub-flavoured Markdown to stdout
/unformalise <Foo.bar> --blueprint      # append to <Project>/Chapters/ as Verso (same as /blueprint --decl)
/unformalise <Foo.bar> --statement-only # skip the proof sketch
```

After the terminal Unicode render, the command asks what you want next (blueprint /
Verso / Markdown / nothing). The `--verso` / `--md` / `--blueprint` flags skip that
prompt — useful when wiring this into a pipeline or another command.

## Prerequisites

- Project is a Lean 4 project that builds clean (`lake build` exits 0). The skill
  uses `lean_local_search` / `Grep` to locate declarations; a broken build leaves the
  LSP unable to resolve names.
- For `--blueprint` output: the verso-blueprint scaffold exists at the project root
  (the `project_template/` layout from `leanprover/verso-blueprint` has been copied
  in — `<Project>/Chapters/`, `<Project>/Blueprint.lean`, `<Project>Main.lean`,
  `scripts/ci-pages.sh`). See `/blueprint` Phase 0 for bootstrap instructions.
- For best quality: `.mathlib-quality/references/` directory of source-paper notes
  and/or a `.mathlib-quality/blueprint/prose_context.md` from a prior `/blueprint`
  run. The skill works without them but leans more heavily on Lean docstrings.

---

## How it works

Five phases. Lightweight — most invocations finish in one or two worker calls.

```
PHASE 0  RESOLVE        find <Foo.bar> in the project; capture source location + docstring
PHASE 1  CONTEXT        read prose context (cached) or build a minimal one on demand
PHASE 2  UNFORMALISE    convert type → math prose; sketch proof; produce both Unicode and Verso markup
PHASE 3  RENDER         display the Unicode block in the terminal
PHASE 4  EMIT           act on the requested output flag (or ask interactively)
```

---

## PHASE 0 — Resolve

Find what the user asked about.

### 0a. Single-declaration form

```
/unformalise <Foo.bar>
```

1. `Grep -nE "(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+<bar>"`
   across `.lean` files (excluding `.lake/`, `blueprint/`, `test/`).
2. If multiple matches, ask the user which one (qualified names disambiguate; show
   `file:line` for each candidate).
3. If zero matches, fail with a one-line "not found" message and a suggestion to use
   `lean_local_search` for fuzzy matching.

### 0b. File form

```
/unformalise path/to/File.lean
```

Run `/blueprint`'s Phase 1a enumeration on the single file — list every public
declaration in source order. Skip `private`, `local`, examples, auto-generated decls.

### 0c. Closure form

```
/unformalise <Foo.bar> --closure
```

Start from `<Foo.bar>`; recursively walk every name in its Lean proof body via
`lean_local_search` to build the transitive closure of project-local declarations
referenced. Cap depth at 5 levels by default (override with `--max-depth N`).

Mathlib declarations are NOT part of the closure — they're considered "external" and
appear in the sketch as cited references without their own `/unformalise` chunk.

### 0d. Capture (REQUIRED per resolved decl)

For each resolved declaration, capture:
- qualified name (e.g. `ModularForm.qExpansion_mul`)
- file path + line number
- kind (`def` / `theorem` / `lemma` / ...)
- full signature (including hypotheses)
- docstring (if any)
- proof body (needed to sketch from, not transcribe)
- sorry-free status (grep proof body for `sorry`)
- dependencies (names invoked in the proof body — for `{uses "..."}[]` if `--blueprint`)

---

## PHASE 1 — Context

The skill needs notation + framing context to produce "the project's mathematical
prose" rather than "generic mathematical prose translated word-for-word from Lean".

### 1a. Check for cached prose context

```bash
test -f .mathlib-quality/blueprint/prose_context.md && cat
```

If present, load it. This file is produced by `/blueprint` Phase 3 and contains:
project narrative, notational conventions, source mappings per Lean module, citation
references. Reusing it across `/unformalise` invocations keeps prose consistent.

### 1b. Build a minimal context on demand

If no cached context exists, build a lightweight one ad-hoc:

1. Read the module docstring of the file containing the target declaration (catches
   "## Main definitions" / "## Main results" / "## References" / notation introductions).
2. Read `README.md` head (first 100 lines) for project narrative.
3. Skim `.mathlib-quality/references/*.md` if present (`ls` first; only read files
   whose title plausibly relates to the decl's topic).
4. If `.mathlib-quality/decomposition.md` exists from a prior `/develop`, search it
   for the decl's name; if matched, use that prose as authoritative.

Don't bother caching the minimal context to disk unless `--cache-context` is set —
small invocations should stay light.

---

## PHASE 2 — Unformalise (one Agent per declaration)

For each resolved declaration, dispatch one Agent. **The unformalisation rules are the
same as `/blueprint` Phase 4** — read `references/blueprint-conventions.md` in full
before the worker starts.

### Worker Agent Prompt

````
You are unformalising ONE Lean declaration into mathematics.

Source declaration: `<qualified.name>` in `<file_path>:<line>`
Kind: <theorem|definition|lemma|proposition|corollary|definition>
Lean proof complete (sorry-free): yes | no
Output modes requested: <terminal | verso | md | blueprint> (one or more — produce all)

## Step 1 — Read inputs

1. Read `<file_path>` around line `<line>` — capture full declaration including
   docstring and proof body.
2. Read the prose context block (passed inline by the main agent in this prompt) —
   notation conventions and source mappings apply.
3. If output mode includes `blueprint`, read any existing `<Project>/Chapters/`
   chunks for adjacent declarations so the new chunk matches their notation, label
   style, and prose register.

## Step 2 — Unformalise the statement

Convert the Lean type to mathematical prose, following the three rules from
`references/blueprint-conventions.md`:

1. **Drop Lean-only plumbing.** Typeclass arguments, universe annotations, decidability
   instances, `FunLike`/`SetLike` instances — none of these appear in math statements.
2. **Use the project's notation.** If the prose context says "$q_h(f)$ denotes …", use
   `q_h(f)`, not `qExpansion h f`.
3. **Spell out variable types in prose.** "Let $f$ be a modular form of weight $k$ on
   $\Gamma$" before the displayed math.

Produce TWO renderings of the statement:

### Unicode version (for terminal display)

Use Unicode characters directly — no LaTeX commands. Examples:

- `\Gamma`         → `Γ`
- `\mathbb{C}`     → `ℂ`
- `\mathbb{Z}`     → `ℤ`
- `\mathbb{N}`     → `ℕ`
- `\mathbb{R}`     → `ℝ`
- `\mathbb{H}`     → `ℍ`
- `\mathbb{Q}`     → `ℚ`
- `\le`            → `≤`
- `\ge`            → `≥`
- `\ne`            → `≠`
- `\to`            → `→`
- `\implies`       → `⇒`
- `\Leftrightarrow`→ `⇔`
- `\cdot`          → `·`
- `\times`         → `×`
- `\circ`          → `∘`
- `\in`            → `∈`
- `\subset`        → `⊂`
- `\subseteq`      → `⊆`
- `\cup` / `\cap`  → `∪` / `∩`
- `\sum_n`         → `Σₙ` or `∑` (use `∑` for display lines; `Σ` is OK inline)
- `\prod_n`        → `∏`
- `\int`           → `∫`
- `\partial`       → `∂`
- `\sqrt{x}`       → `√x` (or `√(...)` with parens if the radicand has structure)
- `\frac{a}{b}`    → `a/b` inline; for displayed fractions in the terminal, use
                      a two-line layout if the prose is on a `display` line, OR
                      use the inline form `a/b` with explicit parentheses
- subscripts        → `q_h(f)` literal; or use `qₕ(f)` for compact display
- superscripts      → `x^k` literal; or `xᵏ` for unambiguous single-char cases
- `\alpha…\omega`   → `α … ω` (Unicode greek)
- `\mathcal{...}`   → use the bold/italic Unicode where unambiguous (𝓜, 𝓕, 𝓞);
                      otherwise prefix with the script name in prose: "the sheaf M"

For symbols WITHOUT a clean Unicode equivalent (e.g. `\widetilde`, `\overline`,
matrix environments, multi-line displays), keep the LaTeX-like form `\widetilde{X}`
but mark the terminal display block as "raw KaTeX excerpt — render in your head" so
the reader knows what they're looking at. Do NOT fall back to ASCII art.

### Verso version (always produce — used if any output mode requests verso/md/blueprint)

Same statement, in Verso markup. Math is KaTeX:
- inline: ``$`...` ``
- display: ``$$`...` ``

Wrap the whole statement in the appropriate Verso directive:
- `:::definition "label" (lean := "Foo.bar")` … `:::`
- `:::theorem "label" (lean := "Foo.bar")` … `:::`
- `:::lemma`, `:::proposition`, `:::corollary` analogously

Pick the kind by the *mathematical role*, not the Lean keyword.

## Step 3 — Sketch the proof

If the declaration is anything except a `definition` or a one-line trivial corollary,
produce a one-to-two-paragraph proof sketch.

Same rules as `/blueprint` Phase 4:
- Mathematical prose, NOT a Lean tactic transcript.
- Cite dependencies by name. In Unicode: "by the q-expansion-mul lemma". In Verso:
  `{uses "q-expansion-mul"}[]` for dependency-graph edges, `{bpref "q-expansion-mul"}[]`
  for prose-only links.
- For definitions: skip the proof block entirely.
- For trivial corollaries: a one-sentence sketch is fine ("Direct specialisation of
  {bpref "main-result"}[].").
- **Do NOT emit `\leanok` in Verso output.** Verso auto-computes status from the
  `(lean := "X")` reference — there is no `\leanok` directive.

Produce the sketch in BOTH Unicode and Verso form, just like the statement.

## Step 4 — Output

Return a structured block. The main agent will format it for the requested output
modes.

```
### Result: `<qualified.name>`

Kind:               <theorem|definition|lemma|...>
File:               <path>:<line>
Sorry-free:         yes | no
Dependencies:       [list of qualified Lean names referenced in the proof]

--- Unicode statement ---
Let <variables>...
    <display equation in Unicode>

--- Unicode proof sketch ---
<paragraph or two; or "(none — definition)" / "(none — trivial corollary)">

--- Verso statement ---
:::<theorem|definition|lemma|proposition|corollary> "<kebab-case-label>" (lean := "<qualified.name>")
<statement in KaTeX math + prose>
:::

--- Verso proof sketch ---
:::proof "<kebab-case-label>"
<sketch in KaTeX math + prose, with {uses "..."}[] for graph edges>
:::

--- Notes ---
- Unicode rendering caveats: <if any symbols had no clean Unicode equiv, list them>
- Label proposed: <kebab-case-label> (if --blueprint requested; main agent checks for clash)
- Dependencies marked as external (mathlib, not project-local): <list>
- Verso status: auto-computed from `(lean := "...")` — no \leanok emitted
```
````

---

## PHASE 3 — Render to terminal

For each result from Phase 2, print to chat using this format:

```
═══ Theorem  ModularForm.qExpansion_mul ═══ Foo/QExpansion.lean:42 ═══

  Let f, g : ℍ → ℂ be functions whose cusp functions are analytic at 0,
  and let h > 0 be a strict period of Γ. Then

      q_h(fg) = q_h(f) · q_h(g).

  ── Proof sketch ──────────────────────────────────────────────────────

  By the definition of the q-expansion and uniqueness of analytic
  factorisation at the cusp, the cusp function of fg equals the product
  of the cusp functions of f and g. The q-expansion of a product of
  analytic functions at the cusp factors as the product of their
  q-expansions, giving the claim.

  ── Status ────────────────────────────────────────────────────────────

  Lean proof:    complete (sorry-free)  ✓
  Dependencies:  ModularForm.qExpansion · AnalyticAt · ModularForm.cuspFunction

═══════════════════════════════════════════════════════════════════════
```

Style notes:
- `═══` and `──` for separators — readable in monospace, no Markdown abuse.
- Statement and sketch indented by 2 spaces.
- Dependencies on one line, separated by ` · `; truncate to 5 items with "(+N more)"
  if longer.
- For definitions, omit the "Proof sketch" sub-section.
- For multiple declarations (file mode or `--closure`), print one block per decl in
  topological order (dependencies first); separate blocks with a blank line.
- If the unformalisation has caveats (Unicode-unsupported symbols, label clash, etc.),
  print them after the closing `═══` line as `Note: <text>`.

---

## PHASE 4 — Emit (act on output flag, or ask)

### 4a. Non-interactive flags

If the invocation had any of `--verso`, `--md`, `--blueprint`, emit accordingly and
return — do NOT prompt.

#### `--verso`

Print the raw Verso directive block (statement + proof) to stdout. Don't write to
any file. Useful for piping into another command or pasting into a draft chapter.

#### `--md`

Wrap the unformalised math in a GitHub-flavoured Markdown block:

```
## ModularForm.qExpansion_mul

**Source:** `Foo/QExpansion.lean:42`

Let $f, g \colon \mathbb{H} \to \mathbb{C}$ be functions ...

$$
  q_h(fg) = q_h(f) \cdot q_h(g).
$$

### Proof sketch

By the definition of the $q$-expansion ...
```

GitHub's math renderer (`$...$` and `$$...$$`) handles the result. Useful for PR
descriptions, issue comments, and design docs — note this is **GitHub-flavoured
math**, not the project's Verso/KaTeX syntax (different delimiters).

#### `--blueprint`

Append the Verso chunk to `<Project>/Chapters/<chapter>.lean`, computing the chapter
from the source-file path the same way `/blueprint` Phase 1b does. Then run the
cross-link pass on the affected chapter file only (orphan `{uses}` check). If the
chapter file didn't exist, also append the `import` + `{include}` to
`<Project>/Blueprint.lean`. Print the `/blueprint`-style result block:

```
Written to:        <Project>/Chapters/Foo/QExpansion.lean
Action:            appended (or replaced if an entry with the same (lean := "X") existed)
Label:             qexpansion-mul
Cross-link:        ✓ all {uses} resolved (or ✗ <orphan list>)
Blueprint.lean:    ✓ import + {include} present  (or "added" if new chapter)

To rebuild and verify the dep-graph: ./scripts/ci-pages.sh
```

### 4b. Interactive prompt (default)

If no output flag was given, after Phase 3's terminal render, ask:

```
What next?
  [b] add to blueprint as Verso
  [v] print as Verso markup
  [m] print as Markdown
  [n] nothing — terminal-only
```

Accept the user's response and execute the corresponding 4a branch (or do nothing for
`n`). For ambiguous responses, ask again — don't guess.

---

## Output examples

### Single declaration, terminal-only

```
/unformalise ModularForm.qExpansion_mul
```

Output: Phase 3 block as shown above, followed by the `[b/l/m/n]` prompt.

### Single declaration, direct to blueprint

```
/unformalise ModularForm.qExpansion_mul --blueprint
```

Output: Phase 3 block + Phase 4a `--blueprint` write report.

### Whole file, Markdown for a PR description

```
/unformalise Foo/QExpansion.lean --md
```

Output: one Markdown block per public declaration in `Foo/QExpansion.lean`,
topologically ordered.

### Single declaration + dependency closure

```
/unformalise ModularForm.qExpansion_mul --closure
```

Output: one Phase 3 block per declaration in the closure (dependencies first, target
last), then ONE `[b/l/m/n]` prompt that applies to all chunks at once (or "b-some"
to selectively blueprint a subset).

---

## What this command does NOT do

- **Build the PDF / HTML.** That's `leanblueprint pdf` / `leanblueprint web`. The
  terminal Unicode render is the closest thing this command offers to a "view".
- **Verify the unformalisation against the Lean source.** A `\lean{X}` reference in
  the LaTeX is checked syntactically (X exists in the project) but not semantically
  (the math statement is faithful to the Lean type). Faithful unformalisation is a
  worker-judgement call; for high-stakes results, eyeball the terminal output before
  appending to the blueprint.
- **Replace existing blueprint chunks silently.** If `--blueprint` is invoked and a
  chunk with the same `(lean := "X")` already exists, the skill REPLACES it but prints
  "Action: replaced" in the result block — never appends a duplicate.
- **Author results that have no Lean counterpart.** Every chunk has `(lean := "X")`
  and `X` must elaborate in the current project. If you want to blueprint a result
  that's only in a source paper, state it as `:= sorry` in Lean first (and `/develop`
  can scaffold this for you).

---

## Reference

- `skills/mathlib-quality/references/blueprint-conventions.md` — the canonical
  LaTeX conventions, anti-patterns, worked examples, and deployment gotchas.
  Workers read this in Phase 2.
- `commands/blueprint.md` — the project-wide batch version of this skill. Use
  `/blueprint --decl` for a non-interactive variant of `/unformalise --blueprint`.

## Learnings

After a non-trivial unformalisation, record significant prose patterns to
`.mathlib-quality/learnings.jsonl` (`type: user_teaching`). Particularly valuable:
notation choices that worked well for the project's domain; symbols that lacked a
clean Unicode equivalent and how the worker handled them; cases where the Lean
statement was a bad fit for math prose (heuristic for "this declaration probably
needs API extraction before it can be unformalised cleanly").
