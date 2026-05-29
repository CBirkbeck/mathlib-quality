---
name: blueprint
description: Author or update the project's blueprint — a LaTeX document that pairs each Lean declaration with its mathematical statement and a paragraph-level proof sketch, building a dependency graph viewable as HTML or PDF. Uses the standard `leanblueprint` Python tool (the one behind sphere-packing, flt-regular, PFR, carleson) so the user gets `leanblueprint pdf` / `leanblueprint web` / `leanblueprint checkdecls` for free; this skill focuses on authoring high-quality unformalisations. Reads the Lean source, docstrings, project references in `.mathlib-quality/references/`, and any existing `decomposition.md` / `plan.md` artifacts from `/develop`. Per-declaration orchestrator-worker pattern: one worker per declaration, with a final main-agent cross-link / `\uses{}` validation pass.
---

# /blueprint — Unformalise a Lean project into a high-quality blueprint

Produce or update a project's blueprint: a LaTeX document in which every public
declaration appears as `\begin{theorem}` (or `\begin{definition}` / `\begin{lemma}` /
`\begin{proposition}`) with:

- the mathematical statement (not the Lean type) in standard LaTeX,
- `\lean{Qualified.Lean.Name}` linking the prose statement to the Lean declaration,
- `\uses{label1, label2, ...}` capturing every dependency (defs used, lemmas invoked),
- `\leanok` when the Lean proof is complete (`sorry`-free),
- a `\begin{proof}` block containing a paragraph-level **mathematical** sketch — not a
  Lean tactic transcript — with its own `\uses{...}` cross-links.

The blueprint is the artifact that lets a mathematician *read* the project (HTML graph
or PDF) without ever opening a `.lean` file. Sphere-packing, flt-regular, PFR, carleson,
PFR-distance, and the polynomial-Freiman-Ruzsa projects all ship one. This command
produces the same shape of artifact.

This skill does NOT bootstrap a blueprint repo from scratch — it expects `leanblueprint
init` has already been run (see Phase 0). It does NOT build the final HTML/PDF — that's
`leanblueprint pdf` / `leanblueprint web`, also Phase 0 territory. It *does* the hard
part: producing high-quality, mathematically faithful unformalisations.

## Usage

```
/blueprint                          # whole project (default)
/blueprint <file.lean>              # only this file's declarations
/blueprint --decl <Foo.bar>         # ★ only this declaration + its dependency closure
/blueprint --update                 # re-sync: add stubs for new decls, flag stale \lean{} refs
/blueprint --check                  # author nothing; just enumerate inventory and report drift
```

### Sibling command: `/unformalise`

For ad-hoc interactive use — "show me what this Lean theorem says, in maths" — use
`/unformalise <Foo.bar>` instead. `/unformalise` renders the result as Unicode in the
terminal first and offers to append it to the blueprint after you've eyeballed the
prose. `/blueprint --decl` skips the terminal-preview step and writes directly to
`blueprint/src/`. Use whichever fits the flow:

| Goal | Use |
|---|---|
| "Show me what this theorem says, then maybe blueprint it" | `/unformalise Foo.bar` |
| "Add this result and everything it uses to the blueprint, no preview" | `/blueprint --decl Foo.bar` |
| "Bootstrap or sync the whole project's blueprint" | `/blueprint` |

## Prerequisites

- Project is a Lean 4 project that builds clean (`lake build` exits 0).
- `blueprint/` directory exists at the project root — created by running
  `leanblueprint init` (interactive: prompts for GitHub user, project name, etc.).
  If it doesn't, Phase 0 stops with instructions.
- `leanblueprint` Python package installed (`pip install leanblueprint` or via pipx).
- Optional but valuable: a `.mathlib-quality/references/` directory of source-paper PDFs
  / notes, OR an existing `decomposition.md` / `plan.md` from a prior `/develop` run.
  Both substantially improve unformalisation quality. The skill works without them but
  the resulting prose leans more heavily on Lean docstrings.

---

## Mode A: Whole project (the default)

Seven phases. **Do them in order. Do not skip phases.**

```
PHASE 0  DOCTOR                    blueprint/ exists, lake build clean, leanblueprint installed
PHASE 1  ENUMERATE                 list every public decl; map to chapter; diff against existing blueprint
PHASE 2  PLAN                      print inventory; user confirms before authoring
PHASE 3  PROSE CONTEXT             read references + existing decomposition.md / plan.md once
PHASE 4  AUTHOR                    one worker per declaration → LaTeX statement + proof sketch
PHASE 5  CROSS-LINK PASS           main agent validates every \uses{...} resolves; fixes orphans
PHASE 6  HAND-OFF                  run `leanblueprint checkdecls`; tell user to build
PHASE 7  REPORT                    one consolidated report
```

---

## PHASE 0 — Doctor (pre-flight)

Three independent checks, all required to pass before authoring starts:

### 0a. `blueprint/` exists and is initialised

```bash
test -d blueprint/src && test -f blueprint/src/content.tex && echo "blueprint OK" || echo "blueprint MISSING"
```

If MISSING, stop with the instruction block:

```
blueprint/ not found (or not initialised by `leanblueprint init`).

Run, from the project root:

  pip install leanblueprint     # or pipx install leanblueprint
  leanblueprint init

The init prompts for: GitHub user/repo, project title, author, license, and the
Lean module to base the dep-graph on. After init succeeds (you'll see blueprint/
with src/, print.tex, web.tex, plastex.cfg), re-run /blueprint.
```

### 0b. Lake build clean

```bash
lake build 2>&1 | tail -20
```

If the build is broken, stop. Blueprint authoring requires the project compiles —
otherwise `\lean{X}` references can't be validated and `leanblueprint checkdecls` will
flag every entry as missing.

### 0c. `leanblueprint` Python package importable

```bash
python3 -c "import leanblueprint; print(leanblueprint.__version__)" 2>&1
```

If not installed, stop with the install instruction (`pip install leanblueprint`).

### 0d. Baseline block (REQUIRED ARTIFACT)

```
### Baseline (Phase 0)
- blueprint/ initialised:          ✓
- lake build:                       ✓ clean
- leanblueprint installed:          ✓ (version X.Y.Z)
- Project Lean modules:             N files, M total declarations (will refine in Phase 1)
- Existing blueprint coverage:      K \lean{X} references currently in blueprint/src/
- Phase 4 will be skipped on:       <list of decls explicitly marked private or in test files>
```

---

## PHASE 1 — Enumerate (Main agent)

### 1a. Walk the Lean source tree

```bash
find . -name "*.lean" -not -path "./.lake/*" -not -path "./blueprint/*" -not -path "./test/*"
```

For each `.lean` file, list:
- public `def` / `abbrev` / `structure` / `inductive` / `class` / `instance` (skip `private` / `local`)
- public `lemma` / `theorem` / `proposition` / `example` (skip `private` / examples used only for testing)

Use `Grep` with patterns or the LSP `mcp__lean-lsp__lean_local_search` per file. Capture
for each: qualified name, kind (`def`/`thm`/...), source file, line number, has-sorry
status (so we know whether to emit `\leanok`).

### 1b. Map decls to chapters

The leanblueprint convention is one chapter per source file (or per directory). Decide
the mapping. Defaults that work well:

- Files at the project root → top-level chapters (one chapter per file).
- Files in a subdirectory (e.g. `Foo/Bar/Baz.lean`) → chapter named `Foo/Bar/Baz` (use
  slashes-to-underscores for the `.tex` filename: `blueprint/src/Foo_Bar_Baz.tex`).

If the project has an obvious narrative ordering (e.g. `1_Basic.lean`, `2_Convergence.lean`,
`3_MainTheorem.lean`), preserve it via `\input{}` order in `blueprint/src/content.tex`.

### 1c. Diff against existing blueprint

Read every existing `blueprint/src/**/*.tex` file. Grep `\lean{...}` for the list of
already-blueprint'd declarations. Compute four sets:

- **New** — Lean decls with no corresponding `\lean{X}` in any blueprint file.
- **Existing OK** — `\lean{X}` exists, and Lean decl `X` still exists at the named file.
- **Stale (rename casualty)** — `\lean{X}` exists but Lean decl `X` no longer exists
  anywhere. Either it was renamed (and the blueprint needs `X` updated to the new name)
  or it was removed (and the blueprint chunk should be deleted).
- **Drift (signature changed)** — `\lean{X}` exists and `X` exists, but the Lean type
  doesn't match the blueprint statement. Detected heuristically by checking whether the
  hypotheses listed in the LaTeX `\begin{theorem}` correspond to the parameters Lean
  reports for `X`. Flagged for re-author rather than silently overwritten.

### 1d. Inventory block (REQUIRED ARTIFACT)

```
### Inventory (Phase 1)
- Lean source files scanned:            N
- Public declarations found:            M
  - definitions:                        Md
  - theorems / lemmas / propositions:   Mt
  - other:                              Mo
- Chapters planned:                     C

| Status     | Count | Notes                                            |
|------------|-------|--------------------------------------------------|
| New        | K1    | will be authored in Phase 4                      |
| Existing OK| K2    | will be left untouched unless --update           |
| Stale      | K3    | listed below — main agent fixes refs in Phase 5  |
| Drift      | K4    | listed below — will be re-authored in Phase 4    |

Stale references (Lean decl no longer exists):
- blueprint/src/foo.tex:42  \lean{Foo.oldName}  — was Foo.oldName ever renamed?
- ...

Drift references (signature changed):
- blueprint/src/bar.tex:18  \lean{Bar.thm}  — Lean now takes [DecidableEq α] which the LaTeX statement omits
- ...
```

---

## PHASE 2 — Plan (Main agent; pauses for user)

Print the inventory from Phase 1d, then a one-sentence plan summary:

```
**Plan.** Author K1 new declarations + re-author K4 drifted ones. Fix K3 stale refs in
Phase 5. K2 existing entries untouched.

Confirm to proceed (or ask for scope changes — e.g. "only author the Foo/Bar chapter
this time", "skip declarations matching pattern X", "treat all existing as drifted and
re-author from scratch").
```

**This is a hard pause.** Do not start Phase 3 until the user replies. Blueprint
authoring is heavyweight (one worker per decl); confirming scope avoids the "I authored
the whole library when you wanted one chapter" failure mode.

---

## PHASE 3 — Prose context (Main agent; runs once)

Read everything that informs the unformalisation, then summarise into a compact
**Prose Context** document that workers consume in Phase 4.

### 3a. Read project references

```
ls .mathlib-quality/references/                  # if exists — usually source-paper notes
ls references/                                    # some projects use this name
ls papers/                                        # some use this
test -f README.md && head -100 README.md
test -f .mathlib-quality/plan.md && cat .mathlib-quality/plan.md
test -f .mathlib-quality/decomposition.md && cat .mathlib-quality/decomposition.md
```

For each reference file found, capture: title, author(s), what it proves, the
mathematical conventions/notation used (this is what makes the blueprint coherent
across chapters — the notation in the blueprint should match the source).

### 3b. Read module docstrings

For every Lean file from Phase 1a, read its module docstring (the `/-! ... -/` block at
the top with `# Title`, `## Main definitions`, `## Main results`, `## References`).
These usually contain the project's preferred prose statements of the results, which
workers should mirror.

### 3c. Read any existing decomposition.md

If a prior `/develop` run produced `.mathlib-quality/decomposition.md`, it contains
verbatim source quotes + Lean-source matches per leaf — exactly the kind of prose the
blueprint wants. Treat it as a high-priority source.

### 3d. Prose Context artifact

Save to `.mathlib-quality/blueprint/prose_context.md`. Format:

```markdown
# Prose Context for Blueprint Authoring

## Project narrative
<one paragraph: what does this project prove, in mathematical terms>

## Notational conventions
- $h$ denotes ... (matches Foo.lean docstring + Smith 2024)
- $q_h(f)$ denotes ... (matches Bar.lean line 42)
- ...

## Source mappings (per Lean module)

### Foo/Bar.lean
- Module docstring summary: ...
- Cited references: Smith 2024 §3.2, Jones 2025 Thm 1.4
- Key declarations: Foo.bar, Foo.baz, ...
- Notation locally: ...

### Foo/Baz.lean
- ...

## High-priority unformalisation sources
1. `.mathlib-quality/decomposition.md` (if present): authoritative prose proofs
2. Module docstrings under `## Main results`: project-preferred statements
3. Inline lemma docstrings: per-decl prose
4. Cited references: ground truth for notation and statement framing
```

This file is the **single source of truth** workers in Phase 4 read. Don't have workers
re-read the references individually — that wastes worker context.

---

## PHASE 4 — Author (one worker per declaration)

For each declaration in the **New** + **Drift** lists from Phase 1d, dispatch one
`Agent` call. The worker reads the Lean source, the prose-context file, and any prior
blueprint chapters it can `\uses{}`, then writes ONE LaTeX block into the correct
`blueprint/src/*.tex` file.

### Worker Agent Prompt

````
You are authoring ONE blueprint entry for the declaration `<qualified.lean.name>` in
the Lean project at `<project root>`.

Source declaration: `<file_path>:<line>`
Kind: definition | theorem | lemma | proposition
Lean proof complete (no `sorry`): yes | no
Chapter to write into: `blueprint/src/<chapter>.tex`

## Step 1 — Read the inputs

1. The declaration itself + its docstring:
   - Read `<file_path>` around line `<line>`. Capture the full declaration: signature,
     docstring, and proof body (the proof body is needed for the sketch — you'll
     unformalise it, not transcribe it).
2. The prose context:
   - Read `.mathlib-quality/blueprint/prose_context.md` in full. The "Source mappings"
     section for `<file_path>` is most relevant; the "Notational conventions" section
     applies globally.
3. Any existing blueprint chunk for adjacent declarations:
   - Read `blueprint/src/<chapter>.tex` if it exists. Match its notation, label style,
     and prose register.

## Step 2 — Unformalise the statement

Convert the Lean type into LaTeX. Rules:

a. **Use the project's notation, not Lean's.** If the prose context says
   "$q_h(f)$ denotes …", use `q_h(f)` in the LaTeX, not `qExpansion h f`.

b. **Drop Lean-only plumbing.** `[FunLike F α β]` typeclass arguments, `{α : Type*}`
   universe annotations, decidability instances — none of these belong in a math
   statement. Only mathematical hypotheses (positivity, membership, analytic-ness, …)
   appear in the LaTeX.

c. **Spell out variable types in prose.** Lean's `(f : ModularForm Γ k)` becomes
   "Let $f$ be a modular form of weight $k$ on $\Gamma$" before the displayed math.

d. **Use \(...\) for inline math and equation displays for long expressions.**

### Statement template

```latex
\begin{theorem}[Optional short name]
  \label{thm:<descriptive-kebab-or-snake-label>}
  \lean{<exact.qualified.Lean.Name>}
  \uses{<comma,separated,labels,of,every,definition,and,lemma,referenced>}
  \leanok                  % only if Lean proof has no `sorry`
  <Prose hypotheses, then the conclusion as a display.>
\end{theorem}
```

Use `\begin{definition}`, `\begin{lemma}`, `\begin{proposition}` analogously. For
purely computational definitions where prose adds nothing, the body can be a single
`\[ ... \]` display.

## Step 3 — Sketch the proof

For declarations where the Lean proof is non-trivial, add a `\begin{proof}` block
**after** the theorem block.

### Sketch rules

- **Mathematical prose, NOT Lean tactic transcription.** A reader who has never
  opened the .lean file should understand the proof. Saying "by `simp` and `omega`"
  is not acceptable. Saying "by linearity of the integral and the elementary bound
  $|e^{ix}| \le 1$" is.
- **One or two paragraphs is usually right.** Multi-page proofs sketch the strategy
  and decompose into `\uses{lem:...}` invocations of the helper lemmas — those are
  authored as their own blueprint entries.
- **`\uses{}` in the proof block** lists every lemma/definition the sketch invokes.
  This is what populates the dep-graph edges.
- **`\leanok` inside the proof block** asserts the Lean tactic-proof goes through.
  Include it iff the Lean proof has no `sorry`.

### Proof template

```latex
\begin{proof}
  \uses{<labels of dependencies invoked in this sketch>}
  \leanok                  % only if Lean proof has no `sorry`
  <Paragraph sketching the strategy, citing dependencies by name or via \cref{lem:foo}.>
\end{proof}
```

### What NOT to write in the proof

- `by simp [foo, bar]` (tactic transcript)
- "Lean unfolds the definition and applies functoriality" (Lean-implementation talk)
- A line-by-line reflection of the tactic proof
- "(See the Lean source for details.)" — the *whole point* of the blueprint is that
  the reader doesn't need to.

### When to omit \begin{proof}

- For definitions (`\begin{definition}` blocks don't take proofs).
- For one-line trivial corollaries — e.g. an obvious specialisation. A `\leanok` on
  the theorem block is sufficient; no proof block needed.
- For results the source cites without proof (axiom-style): a `\begin{proof}` with
  one sentence "Cited from [Ref §X.Y]." is fine.

## Step 4 — Write the file

Use `Edit` (not `Write`) to append or modify the chunk in `blueprint/src/<chapter>.tex`.

- If the file exists and contains an entry with the same `\lean{X}`, REPLACE that
  entry's full block (theorem + proof).
- If the file exists and doesn't have this entry, APPEND in the order that matches the
  Lean source file (so dependencies come before dependents — the dep-graph reads
  cleanly).
- If the file doesn't exist, CREATE it with a one-line section header
  (`\section{<Chapter name>}\label{sec:<chapter>}` or `\chapter{...}` depending on the
  project's `print.tex` style — match what neighbouring chapters use).
- If you create a new chapter file, also append `\input{<chapter>}` to
  `blueprint/src/content.tex` in the appropriate position.

## Step 5 — Report

Return one block:

```
### Result: `<qualified.lean.name>`

Chapter file:    blueprint/src/<chapter>.tex
Action:          created | appended | replaced
Statement size:  N LaTeX lines
Proof sketch:    M LaTeX lines (or "none — definition" / "none — trivial corollary")
Lean proof complete: yes (\leanok emitted) | no (\leanok omitted)
\uses{} dependencies declared:
  - lem:foo
  - def:bar
  - ...
References cited from prose context:
  - Smith 2024 §3.2
  - ...
Notation matches project convention:
  - $q_h$, $\Gamma$, $f$ — all match Foo.lean docstring + Smith 2024
Open questions for main agent (if any):
  - none | "I used label thm:foo-mul; if a sibling chapter already defines that, you'll
            need to disambiguate in Phase 5"
```
````

### Dispatching workers

For each declaration in **New** + **Drift**:

1. **Order matters for the dep-graph.** A declaration that uses another should be
   authored AFTER its dependency, so the worker can read the dependency's existing
   blueprint entry and reference it via `\uses{}` correctly. Topological-sort by
   dependency closure within the project.
2. Dispatch one `Agent` call per declaration. Wait for completion. Capture the report.
3. Workers may run in parallel within the SAME chapter file ONLY when they don't
   `\uses{}` each other. Two workers editing the same `chapter.tex` simultaneously is
   a race — serialize per-file.
4. Track an internal log of `(decl_name → chapter_file → label_written)` so Phase 5
   can validate cross-links.

### Forbidden Phase 4 shortcuts

- **Batched worker:** dispatching one Agent to "author the whole chapter" instead of
  one Agent per declaration. Same failure mode as `/cleanup` Phase 4 — workers
  optimise for visible wins and skip declarations that don't fit the narrative they
  built. One declaration per worker.
- **Skipping unformalisation:** writing `\begin{theorem}<Lean source verbatim, just
  wrapped in latex>\end{theorem}` instead of converting to math prose. The whole
  purpose of a blueprint is the unformalisation; a Lean-shaped theorem statement
  fails the purpose. Detection: any LaTeX `\begin{theorem}` block containing camelCase
  identifiers, `:=`, `→` (vs `\to` / `\implies`), `[...]` typeclass brackets is
  forbidden.
- **Empty proof sketch:** `\begin{proof}\leanok\end{proof}` with no prose. If the
  result is non-trivial, sketch the strategy. If it IS trivial, omit the proof block
  entirely — don't ship empty proofs.

---

## PHASE 5 — Cross-link pass (Main agent)

After every Phase 4 worker has returned, walk the produced LaTeX to validate the
dep-graph.

### 5a. Collect labels and references

```bash
grep -rh '\\label{' blueprint/src/ | sed -E 's/.*\\label\{([^}]+)\}.*/\1/' | sort -u > /tmp/labels
grep -rh '\\uses{'  blueprint/src/ | sed -E 's/.*\\uses\{([^}]+)\}.*/\1/' | tr ',' '\n' | sed 's/^ *//;s/ *$//' | sort -u > /tmp/uses
```

### 5b. Orphan check

```bash
comm -23 /tmp/uses /tmp/labels
```

Any line in the result is a `\uses{X}` claim whose `X` doesn't exist as a `\label{}`
anywhere. For each orphan, the main agent does ONE of:

1. **Add the missing dependency** — usually because the dependency is a definition in
   another file that wasn't included in the Phase 1 enumeration. Dispatch a one-off
   worker to author it.
2. **Rename the reference** — the worker used the wrong label (e.g. `thm:foo-mul`
   when the real label is `thm:foo_mul`). Patch with `Edit`.
3. **Remove the reference** — the worker over-attributed (e.g. claimed a dependency on
   a definition that isn't actually used in the prose). Patch with `Edit`.

### 5c. Stale-ref repair (from Phase 1d)

For every Stale entry from Phase 1d (`\lean{X}` where Lean decl `X` no longer exists):

1. Search the Lean source for a successor: `grep -rE "(theorem|lemma|def|abbrev) <X-without-prefix>" --include="*.lean"`.
2. If a likely successor exists with a similar name, update the `\lean{X}` to the new
   name. Re-verify the statement still matches.
3. If no successor, the result was deleted — remove the blueprint chunk.

### 5d. Cross-link report

```
### Phase 5 — Cross-link pass
- Labels defined:               L
- \uses{} references made:      U
- Orphan refs resolved:         O   (by add / rename / remove)
- Stale \lean{} fixed:          S   (by rename / remove)
```

---

## PHASE 6 — Hand-off to `leanblueprint`

The blueprint LaTeX is now self-consistent. Hand off to the standard tool for build +
verification.

### 6a. Rebuild `blueprint/lean_decls` before `checkdecls`

`leanblueprint checkdecls` reads from `blueprint/lean_decls`, which is **regenerated
by `leanblueprint web`** — not re-derived on the fly. After Phase 4 / 5 renames or
new entries, the stale file gives misleading "X is missing" reports.

```bash
rm -rf blueprint/web blueprint/lean_decls
leanblueprint web 2>&1 | tail -20         # populates blueprint/lean_decls
leanblueprint checkdecls 2>&1 | tail -40
```

Any `checkdecls` failure after the rebuild is a defect in Phase 4 or Phase 5c —
re-run those for the offending entries.

### 6b. Pre-push checklist (REQUIRED ARTIFACT before declaring blueprint ready)

These four checks catch the failure modes that CI will otherwise catch days later.
Skipping them is a defect; print the block whether they pass or fail.

```
### Pre-push checklist (Phase 6)
- leanblueprint web rebuild:        ✓ / ✗
- leanblueprint checkdecls exit 0:  ✓ / ✗
- leanblueprint pdf builds:         ✓ / ✗
- print.log undefined-ref count:    K (must be 0)
```

The PDF build + undefined-ref count is what CI scores you on. Run:

```bash
leanblueprint pdf 2>&1 | tail -20
grep -c "undefined" blueprint/print/print.log   # must print 0
```

If the count is non-zero, the typical cause is one of:

- **A LaTeX macro error mid-file aborted pdflatex** so the `.aux` never populated.
  Scan `blueprint/print/print.log` for the FIRST `! Undefined control sequence` or
  `Missing { inserted` — not the downstream `undefined reference` warnings, which are
  symptoms. Define the missing macro in `blueprint/src/macros/common.tex` (e.g. add
  `\newcommand{\re}{\operatorname{Re}}`); brace subscripts that include `\mathop`s
  (e.g. `\delta_{\inf}` not `\delta_\inf`).
- **latexmk default 2-pass build didn't converge.** Set in `blueprint/src/latexmkrc`:
  ```perl
  $max_repeat = 5;
  $force_mode = 1;
  ```
  Re-run `leanblueprint pdf`.

See `references/blueprint-conventions.md § Deployment & CI gotchas` for the catalogue.

### 6c. CI configuration check (one-shot, on first deploy)

If the project's GitHub Pages workflow exists, verify the docgen-action step includes
`api-docs: true`. Without it, the dep-graph viewer's "Lean" links produce 404s in
production.

```bash
grep -nE "api-docs:" .github/workflows/*.yml 2>/dev/null
```

If the grep returns nothing AND `.github/workflows/blueprint.yml` (or similar) exists,
add `api-docs: true` to the docgen-action step (don't auto-edit without confirming —
it touches CI config). Flag this in the Phase 7 report.

### 6d. Tell the user how to view / iterate

```
Blueprint authored and verified. To view locally:

  leanblueprint pdf            # → blueprint/print/print.pdf
  leanblueprint web            # → blueprint/web/  (HTML + dep-graph)
  python3 -m http.server -d blueprint/web/        # serve the web view

To re-sync after Lean code changes: /blueprint --update
To unformalise + add one specific result: /blueprint --decl <Foo.bar>  (or /unformalise)
```

### 6e. Optional: open the dep-graph

If `--open` was passed, build the web view and open the dep-graph index. Otherwise skip.

---

## PHASE 7 — Report

Required artifacts (a missing section = the corresponding phase wasn't completed —
treat as a defect and re-run):

- **Baseline (Phase 0)** — proves doctor ran
- **Inventory (Phase 1)** — proves enumeration happened
- **Plan + user confirmation (Phase 2)** — proves scope was confirmed
- **Prose context written (Phase 3)** — file path exists and was populated
- **Phase 4 per-declaration results** — one row per New / Drift entry
- **Phase 5 cross-link report** — proves orphans/stales were resolved
- **Phase 6 hand-off** — `checkdecls` clean

```
## /blueprint report — <project root>

### Baseline (Phase 0)
- blueprint/ initialised:           ✓
- lake build:                        ✓ clean
- leanblueprint installed:           ✓ (v0.0.18)
- Project files scanned:             47
- Public declarations:               203

### Inventory (Phase 1)
- New:           K1
- Existing OK:   K2
- Stale:         K3
- Drift:         K4
- Chapters touched: C

### Plan (Phase 2)
User confirmed scope: <restate user's reply or "default whole-project plan accepted">

### Prose context (Phase 3)
File: .mathlib-quality/blueprint/prose_context.md
Sources synthesised: <N reference files, M module docstrings, decomposition.md present/absent>

### Phase 4 per-declaration results
| Declaration                         | Chapter file              | Action  | Stmt L | Pf L | Lean? |
|-------------------------------------|---------------------------|---------|--------|------|-------|
| `Foo.qExpansion_mul`                | blueprint/src/Foo.tex     | created |   6    |  4   | ✓     |
| `Foo.qExpansion_eq_disc_mul`        | blueprint/src/Foo.tex     | created |   5    |  3   | ✓     |
| `Bar.helper`                        | blueprint/src/Bar.tex     | replaced|   3    | none | ✓     |
| ...                                                                                       |

### Phase 5 cross-link pass
- Labels defined:    137
- \uses{} refs:      214
- Orphans resolved:    2 (1 added, 1 renamed)
- Stale fixed:         3 (3 renamed)

### Phase 6 hand-off
- leanblueprint checkdecls:  ✓ clean (203/203 Lean refs resolve)
- Build instructions printed.

### Totals
- New blueprint chunks:        K1
- Drifted entries re-authored: K4
- Cross-file refs validated:   <number>
- Project coverage:            <K2+K1+K4>/<M public decls> (P%)
```

---

## Mode B: Single file

```
/blueprint <file.lean>
```

Same workflow, but Phase 1 enumeration scope is just `<file.lean>`. Phase 5 still runs
project-wide because a chunk in this file may add `\uses{}` to labels defined elsewhere.

## Mode C: Single declaration + dependency closure

```
/blueprint --decl <Foo.bar>
```

Phase 1 enumeration scope is `<Foo.bar>` and the transitive closure of declarations it
uses, computed by walking `mcp__lean-lsp__lean_local_search` for each invoked name.
Useful for incrementally building a blueprint as you finish each top-level result.

## Mode D: Update / drift-only sweep

```
/blueprint --update
```

Phases 0–2 as usual. Phase 4 authors only **Drift** entries (signature changed); skips
New (use the default mode for that). Phase 5 still fixes stales.

## Mode E: Check-only

```
/blueprint --check
```

Runs Phases 0, 1, 2 (inventory + diff) and STOPS — no authoring. Use to audit
blueprint freshness without committing time to authoring. Output is just the Phase 1d
inventory block.

---

## What this command does NOT do

- **Build the PDF / HTML.** That's `leanblueprint pdf` / `leanblueprint web` — Phase 6
  prints the commands. Build is out of scope because it depends on a working LaTeX
  install and can be slow.
- **Bootstrap the `blueprint/` repo from scratch.** That's `leanblueprint init`,
  which is interactive and asks the user for project metadata. Phase 0 stops with
  instructions if missing.
- **Re-prove the project.** A blueprint chunk's `\leanok` is asserted from the
  *current* state of the Lean file. If a declaration has `sorry`, the blueprint
  records that (no `\leanok`); it doesn't try to discharge sorries. Use `/beastmode`
  for that.
- **Author informal lemmas with no Lean counterpart.** Every blueprint entry must have
  a real `\lean{X}` and `X` must exist in the Lean source. "Pure prose" blueprint
  entries are out of scope; if a result is in the source paper but not yet in Lean,
  it belongs in `decomposition.md` (planning) not in the blueprint.

---

## Reference

- `skills/mathlib-quality/references/blueprint-conventions.md` — LaTeX conventions,
  worked examples, common-mistakes catalogue (Phase 4 workers read this).
- [`leanblueprint` GitHub](https://github.com/PatrickMassot/leanblueprint) — upstream
  tool documentation.
- Example blueprints worth reading for style:
  - [Sphere Packing](https://github.com/teorth/SphericalPacking) — recent, well-curated.
  - [FLT-Regular](https://github.com/leanprover-community/flt-regular) — older but
    canonical for number-theory projects.
  - [PFR](https://github.com/teorth/pfr) — Tao's project; dense dep-graph; good
    `\uses{}` discipline.
  - [Carleson](https://github.com/fpvandoorn/carleson) — large project; good chapter
    structure.

## Learnings

After completing, record significant patterns to `.mathlib-quality/learnings.jsonl`.
Particularly valuable: notation conventions that worked / didn't work across the
project, recurring orphan-ref patterns (which suggests a missing definition file),
sketch length that turned out to be too terse or too verbose in review.
