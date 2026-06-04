---
name: blueprint
description: Author or update the project's verso-blueprint — a Verso-based Lean module pairing each declaration with its mathematical statement and a paragraph-level proof sketch, producing an interactive HTML dep-graph + progress summary. Uses the standard `leanprover/verso-blueprint` tooling (the one behind verso-sphere-packing, verso-flt, verso-carleson, verso-noperthedron); this skill focuses on authoring high-quality unformalisations. Statements use Verso directives (`:::theorem "label" (lean := "Foo.bar")`), dep-graph edges use `{uses "label"}[]`, math is KaTeX (``$`...` `` inline, ``$$`...` `` display). Lean status (sorry-free vs. in-progress) is auto-computed from the `(lean := …)` reference — no manual `\leanok` to keep in sync. Reads the Lean source, docstrings, project references in `.mathlib-quality/references/`, and any existing `decomposition.md` / `plan.md` artifacts from `/develop`. Per-declaration orchestrator-worker pattern with a final cross-link / `{uses}` validation pass.
---

# /blueprint — Unformalise a Lean project into a Verso blueprint

Produce or update a project's blueprint: a Verso document where every public
declaration appears as a `:::definition` / `:::theorem` / `:::lemma` / `:::proposition`
/ `:::corollary` block with:

- the mathematical statement (not the Lean type) in standard mathematical prose with
  KaTeX math,
- `(lean := "Qualified.Lean.Name")` linking the prose statement to one or more Lean
  declarations,
- `{uses "label"}[]` directives capturing dependency-graph edges,
- a `:::proof "label"` block holding a paragraph-level **mathematical** sketch — not
  a Lean tactic transcript — with its own `{uses}` cross-links.

Verso auto-computes the completion status (sorry-free vs. in-progress) from the
referenced Lean declarations' state. There is no `\leanok` directive in Verso; the
graph colour comes from the declaration state directly, so the blueprint and the
formal side cannot drift out of sync.

The published Verso blueprints worth eyeballing for style:
[`verso-sphere-packing`](https://github.com/ejgallego/verso-sphere-packing),
[`verso-flt`](https://github.com/ejgallego/verso-flt),
[`verso-carleson`](https://github.com/ejgallego/verso-carleson),
[`verso-noperthedron`](https://github.com/ejgallego/verso-noperthedron),
[`verso-algebraic-combinatorics`](https://github.com/ejgallego/verso-algebraic-combinatorics).

This skill does NOT bootstrap a verso-blueprint repo from scratch — it expects the
project_template has been copied into the project (see Phase 0). It does NOT build
the HTML site — that's `./scripts/ci-pages.sh`, also Phase 0 / Phase 6 territory. It
*does* the hard part: producing high-quality, mathematically faithful unformalisations.

## Usage

```
/blueprint                              # whole project (default)
/blueprint <file.lean>                  # only this file's declarations
/blueprint --decl <Foo.bar>             # ★ only this declaration + its dependency closure
/blueprint --update                     # re-sync: add stubs for new decls, flag stale `(lean := …)`
/blueprint --check                      # author nothing; just enumerate inventory and report drift
/blueprint --migrate-from-latex [<dir>] # convert an old leanblueprint LaTeX tree (default: blueprint/src/)
                                        #   into Verso chapter files (mechanical 1:1)
```

### Sibling command: `/unformalise`

For ad-hoc interactive use — "show me what this Lean theorem says, in maths" — use
`/unformalise <Foo.bar>` instead. `/unformalise` renders the result as Unicode in the
terminal first and offers to append it to the blueprint after you've eyeballed the
prose. `/blueprint --decl` skips the terminal-preview step and writes directly to
the chapter file:

| Goal | Use |
|---|---|
| "Show me what this theorem says, then maybe blueprint it" | `/unformalise Foo.bar` |
| "Add this result and everything it uses to the blueprint, no preview" | `/blueprint --decl Foo.bar` |
| "Bootstrap or sync the whole project's blueprint" | `/blueprint` |

## Prerequisites

- Project is a Lean 4 project that builds clean (`lake build` exits 0).
- A verso-blueprint scaffold exists at the project root — specifically, the layout
  the [`leanprover/verso-blueprint` project template](https://github.com/leanprover/verso-blueprint/tree/main/project_template) produces:
  ```
  <Project>/Chapters/         # chapter modules
  <Project>/Blueprint.lean    # top-level (includes chapters, adds {blueprint_graph} / {blueprint_summary})
  <Project>Main.lean          # generator entry point
  scripts/ci-pages.sh         # local build + render script
  ```
- The Verso toolchain is available via `lake` (no separate Python install required —
  unlike the legacy leanblueprint stack).
- Optional but valuable: a `.mathlib-quality/references/` directory of source-paper
  PDFs / notes, OR an existing `decomposition.md` / `plan.md` from a prior `/develop`
  run. Both substantially improve unformalisation quality. The skill works without
  them but the resulting prose leans more heavily on Lean docstrings.

---

## Mode A: Whole project (the default)

Seven phases. **Do them in order. Do not skip phases.**

```
PHASE 0  DOCTOR                    project_template copied, lake build clean, lake env reachable
PHASE 1  ENUMERATE                 list every public decl; map to chapter; diff against existing blueprint
PHASE 2  PLAN                      print inventory; user confirms before authoring
PHASE 3  PROSE CONTEXT             read references + existing decomposition.md / plan.md once
PHASE 4  AUTHOR                    one worker per declaration → Verso directives in chapter file
PHASE 5  CROSS-LINK PASS           main agent validates every {uses} and (lean := …) resolves
PHASE 6  HAND-OFF                  run scripts/ci-pages.sh; verify _out/site/html-multi/ exists
PHASE 7  REPORT                    one consolidated report
```

---

## PHASE 0 — Doctor (pre-flight)

Three independent checks, all required to pass before authoring starts.

### 0a. verso-blueprint scaffold exists

```bash
PROJ="$(ls *.lean 2>/dev/null | grep -v Main.lean | head -1 | sed 's/.lean$//')"
test -d "${PROJ}/Chapters" \
  && test -f "${PROJ}/Blueprint.lean" \
  && test -f "${PROJ}Main.lean" \
  && test -f "scripts/ci-pages.sh" \
  && echo "verso-blueprint scaffold OK" \
  || echo "scaffold MISSING"
```

If MISSING, stop with the instruction block:

```
verso-blueprint scaffold not found.

verso-blueprint is the leanprover-official Lean-native blueprint tool. It ships
a copyable starter under `project_template/`. To install it into your project:

  # one-time bootstrap — copy the template into your project root
  git clone https://github.com/leanprover/verso-blueprint /tmp/verso-blueprint
  cp -r /tmp/verso-blueprint/project_template/.github .
  cp -r /tmp/verso-blueprint/project_template/scripts .
  cp -r /tmp/verso-blueprint/project_template/ProjectTemplate <YourProjectName>
  cp /tmp/verso-blueprint/project_template/ProjectTemplate.lean <YourProjectName>.lean
  cp /tmp/verso-blueprint/project_template/ProjectTemplateMain.lean <YourProjectName>Main.lean
  cp /tmp/verso-blueprint/project_template/lakefile.lean blueprint-lakefile.lean   # merge with your existing lakefile
  cp /tmp/verso-blueprint/project_template/lean-toolchain blueprint-lean-toolchain # reconcile with your toolchain

  # Rename references from `ProjectTemplate` to your project name throughout:
  find <YourProjectName> <YourProjectName>.lean <YourProjectName>Main.lean \
       -type f -name "*.lean" -exec sed -i '' 's/ProjectTemplate/<YourProjectName>/g' {} \;

  # Then:
  lake update
  ./scripts/ci-pages.sh

After ci-pages.sh succeeds (you'll see `_out/site/html-multi/`), re-run /blueprint.

Reference: https://github.com/leanprover/verso-blueprint/blob/main/doc/GETTING_STARTED.md
```

### 0b. Lake build clean

```bash
lake build 2>&1 | tail -20
```

If the build is broken, stop. Blueprint authoring requires the project compiles —
otherwise `(lean := "X")` references can't be elaborated and the cross-link pass is
meaningless.

### 0c. `lake env lean --run` works

```bash
echo 'def main : IO Unit := IO.println "ok"' > /tmp/_blueprint_probe.lean
lake env lean --run /tmp/_blueprint_probe.lean 2>&1 | tail -5
rm /tmp/_blueprint_probe.lean
```

If `lake env` is unhealthy, the Phase-6 hand-off (`./scripts/ci-pages.sh`) will fail.
Stop with the actual error message.

### 0d. Baseline block (REQUIRED ARTIFACT)

```
### Baseline (Phase 0)
- verso-blueprint scaffold:         ✓ (Chapters/, Blueprint.lean, Main.lean, ci-pages.sh)
- lake build:                        ✓ clean
- lake env lean --run probe:         ✓
- Project Lean modules:              N files, M total declarations (will refine in Phase 1)
- Existing blueprint coverage:       K `(lean := "X")` references currently in chapters
- Phase 4 will be skipped on:        <list of decls explicitly marked private or in test files>
```

---

## PHASE 1 — Enumerate (Main agent)

### 1a. Walk the Lean source tree

```bash
find . -name "*.lean" \
  -not -path "./.lake/*" \
  -not -path "./_out/*" \
  -not -path "./<Project>/Chapters/*" \
  -not -path "./<Project>/Blueprint.lean" \
  -not -path "./<Project>Main.lean" \
  -not -path "./test/*"
```

For each `.lean` file, list:
- public `def` / `abbrev` / `structure` / `inductive` / `class` / `instance` (skip `private` / `local`)
- public `lemma` / `theorem` / `proposition` (skip `private` / examples)

Use `Grep` or the LSP `mcp__lean-lsp__lean_local_search` per file. Capture for each:
qualified name, kind, source file, line number, has-sorry status (Verso will pick this
up automatically, but it's useful for the Phase-1 inventory).

### 1b. Map decls to chapters

Default: one chapter file per source-tree directory or per Lean file. If `<Project>`
already has chapter files under `<Project>/Chapters/`, group new decls into the
existing chapter whose name best matches the source path.

For new chapters, create `<Project>/Chapters/<Name>.lean` with the standard preamble
(see "Chapter file preamble" below) and also add to `<Project>/Blueprint.lean`:

```lean
import <Project>.Chapters.<Name>
-- and inside the #doc body, add:
{include 0 <Project>.Chapters.<Name>}
```

Both lines (import and `{include}`) are required.

### 1c. Diff against existing blueprint

Read every existing `<Project>/Chapters/*.lean`. Grep for `(lean := "...")` to
list already-blueprint'd declarations. Compute four sets:

- **New** — Lean decls with no corresponding `(lean := "X")` in any chapter.
- **Existing OK** — `(lean := "X")` exists and Lean decl `X` still exists.
- **Stale (rename casualty)** — `(lean := "X")` exists but Lean decl `X` no longer
  exists. Either renamed (update to new name) or removed (delete the directive).
- **Drift (signature changed)** — `(lean := "X")` exists and `X` exists, but the
  Lean type doesn't match the prose statement. Heuristic check: do the hypotheses
  named in the prose appear in the Lean type? Flagged for re-author rather than
  silently overwritten.

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
- <Project>/Chapters/Foo.lean:42  (lean := "Foo.oldName")  — was Foo.oldName ever renamed?
- ...

Drift references (signature changed):
- <Project>/Chapters/Bar.lean:18  (lean := "Bar.thm")  — Lean now takes [DecidableEq α] which the prose omits
- ...
```

---

## PHASE 2 — Plan (Main agent; pauses for user)

Print the inventory from Phase 1d, then a one-sentence plan summary:

```
**Plan.** Author K1 new declarations + re-author K4 drifted ones. Fix K3 stale refs in
Phase 5. K2 existing entries untouched.

Confirm to proceed (or ask for scope changes — e.g. "only author the QExpansion chapter
this time", "skip declarations matching pattern X", "treat all existing as drifted and
re-author from scratch").
```

**This is a hard pause.** Do not start Phase 3 until the user replies.

---

## PHASE 3 — Prose context (Main agent; runs once)

Same as the LaTeX-stack version of this skill: read everything that informs the
unformalisation, synthesise into `.mathlib-quality/blueprint/prose_context.md`,
workers consume from there.

### 3a. Read project references

```
ls .mathlib-quality/references/                  # if exists — usually source-paper notes
ls references/                                    # some projects use this name
ls papers/                                        # some use this
test -f README.md && head -100 README.md
test -f .mathlib-quality/plan.md && cat .mathlib-quality/plan.md
test -f .mathlib-quality/decomposition.md && cat .mathlib-quality/decomposition.md
```

### 3b. Read module docstrings

For every Lean file from Phase 1a, read its module docstring (the `/-! ... -/` block
at the top with `# Title`, `## Main definitions`, `## Main results`, `## References`).

### 3c. Read any existing decomposition.md

If a prior `/develop` run produced `.mathlib-quality/decomposition.md`, it contains
verbatim source quotes + Lean ↔ source matches per leaf — exactly the prose the
blueprint wants. Treat as high-priority source.

### 3d. Prose Context artifact

Save to `.mathlib-quality/blueprint/prose_context.md`. Format:

```markdown
# Prose Context for Blueprint Authoring

## Project narrative
<one paragraph: what does this project prove, in mathematical terms>

## Notational conventions
- $`h` denotes ... (matches Foo.lean docstring + Smith 2024)
- $`q_h(f)` denotes ... (matches Bar.lean line 42)
- ...

## Source mappings (per Lean module)

### Foo/Bar.lean
- Module docstring summary: ...
- Cited references: Smith 2024 §3.2, Jones 2025 Thm 1.4
- Key declarations: Foo.bar, Foo.baz, ...
- Notation locally: ...

## High-priority unformalisation sources
1. `.mathlib-quality/decomposition.md` (if present): authoritative prose proofs
2. Module docstrings under `## Main results`: project-preferred statements
3. Inline lemma docstrings: per-decl prose
4. Cited references: ground truth for notation and statement framing
```

This file is the single source of truth workers in Phase 4 read.

---

## PHASE 4 — Author (one worker per declaration)

For each declaration in the **New** + **Drift** lists from Phase 1d, dispatch one
`Agent` call. The worker reads the Lean source, the prose-context file, and any prior
chapter chunks it can `{uses}`, then writes ONE Verso block into the correct chapter
file.

### Chapter file preamble (for new chapter files)

If the worker is creating a new chapter file `<Project>/Chapters/<Name>.lean`, the
preamble is:

```lean
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "<Chapter Title>" =>

-- directives go here
```

The worker also has to update `<Project>/Blueprint.lean` to import + include the
new chapter (main agent handles this in Phase 5 if not done inline).

### Worker Agent Prompt

````
You are authoring ONE blueprint entry for the declaration `<qualified.lean.name>` in
the Lean project at `<project root>`.

Source declaration: `<file_path>:<line>`
Kind: definition | theorem | lemma | proposition | corollary
Lean proof complete (no `sorry`): yes | no   (for context — Verso auto-computes)
Chapter to write into: `<Project>/Chapters/<Chapter>.lean`

## Step 1 — Read the inputs

1. The declaration itself + its docstring:
   - Read `<file_path>` around line `<line>`. Capture the full declaration:
     signature, docstring, and proof body. You'll unformalise the type and sketch
     the proof body — never transcribe Lean tactics.
2. The prose context:
   - Read `.mathlib-quality/blueprint/prose_context.md` in full. The "Source
     mappings" section for `<file_path>` is most relevant; "Notational conventions"
     applies globally.
3. Any existing blueprint chunk for adjacent declarations:
   - Read `<Project>/Chapters/<Chapter>.lean` if it exists. Match its notation,
     label style, and prose register.
4. The conventions reference (mandatory):
   - Read `skills/mathlib-quality/references/blueprint-conventions.md` in full.
     It documents Verso directives, KaTeX math syntax, the three
     high-quality-unformalisation rules, and the anti-pattern catalogue.

## Step 2 — Pick a label

Labels are global identifiers, used by `{uses}` and `{bpref}` from other chunks.
Convention: kebab-case mathematical name (NOT the Lean name).

```
"q-expansion-mul"            (NOT "qExpansion_mul")
"modular-forms-finite-dim"   (NOT "ModularFormFiniteDim")
"mertens-bound"              (NOT "mertensBound")
```

Globally unique across `<Project>/Chapters/`. The Phase-5 cross-link pass enforces
uniqueness; pick descriptive names from the start.

## Step 3 — Unformalise the statement

Convert the Lean type to KaTeX-math prose. Three rules (from
`blueprint-conventions.md`):

1. **Drop Lean-only plumbing.** Typeclass arguments, universe annotations,
   decidability instances, `FunLike`/`SetLike` instances — none belong in the prose.
2. **Use the project's notation.** Prose context says ``$`q_h(f)` ``? Use that.
3. **Spell out variable types in prose.** "Let $`f` be a modular form of weight
   $`k` on $`\Gamma`" before the displayed math.

### Statement template

```
:::definition "<kebab-case-label>" (lean := "<Qualified.Lean.Name>")
<Prose hypotheses, then the conclusion as a display.>
:::
```

`:::theorem`, `:::lemma`, `:::proposition`, `:::corollary` analogous. For
purely computational definitions where prose adds nothing, the body can be a
single display: `$$`<expression>.``.

Math syntax:
- inline:  ``$`...` ``
- display: ``$$`...` ``

KaTeX is the renderer. Verso lints during elaboration — undefined `\foo` macros
surface as build errors. If you need a project-wide macro, declare it once in a
chapter `tex_prelude`.

### Optional metadata

Most workers emit only `(lean := "...")`. Other metadata mirrors what neighbouring
chapters do:

```
:::theorem "label" (lean := "Foo.bar")
                   (parent := "addition_core")
                   (tags := "modular-forms")
                   (priority := "high")
...
:::
```

## Step 4 — Sketch the proof

For non-trivial declarations, follow the statement with a `:::proof "label"` block.

### Sketch rules

- **Mathematical prose, NOT Lean tactic transcription.** A reader who has never
  opened the .lean file should understand the strategy.
- **One or two paragraphs is usually right.** Long proofs sketch the spine and
  invoke helper lemmas via `{uses "label"}[]` — the helpers are authored as their
  own blueprint entries.
- **`{uses "label"}[]` inside the proof block** lists every lemma/definition the
  sketch invokes; these become the proof-edge entries in the dep-graph.
- **Empty payload `[]`** lets Verso pick the rendered text automatically.

### Proof template

```
:::proof "<label>"
<Paragraph sketching the strategy. Cite dependencies via {uses "..."}[].>
:::
```

### What NOT to write in the proof

- `by simp [foo, bar]` (tactic transcript)
- "Lean unfolds the definition and applies functoriality" (implementation talk)
- "(See the Lean source for details.)" — the *whole point* of the blueprint is
  that the reader doesn't need to.

### When to omit `:::proof`

- For definitions (`:::definition` blocks don't take proofs).
- For one-line trivial corollaries — Verso's auto-progress reads the Lean state
  directly; no `:::proof` needed.
- For results the source cites without proof: a `:::proof` with one sentence
  "Cited from {bpref "smith-2024"}[Smith 2024 §3.2]." is fine.

### No `\leanok` — Verso auto-computes status

Status (sorry-free vs. in-progress) comes from the `(lean := "X")`-referenced
declaration's elaborated state. **Don't emit `\leanok`** — it's not a Verso
directive and is silently ignored. The dep-graph colours nodes by reading the
linked Lean's state directly.

## Step 5 — Write the file

Use `Edit` (not `Write`) to append or modify the chunk in
`<Project>/Chapters/<Chapter>.lean`.

- If the file exists and contains a directive with the same `(lean := "X")`,
  REPLACE that entry's full block (statement + optional proof).
- If the file exists and doesn't have this entry, APPEND in dependency order
  (every definition before its consumers; every helper before the theorem that
  uses it).
- If the file doesn't exist, CREATE it with the chapter preamble (see "Chapter
  file preamble" above) and a one-line section header in the prose, then append
  the new chunk.
- If you create a new chapter file, also flag in your report that
  `<Project>/Blueprint.lean` needs an `import` and `{include}` — main agent
  handles that in Phase 5.

## Step 6 — Report

Return one block:

```
### Result: `<qualified.lean.name>`

Chapter file:        <Project>/Chapters/<Name>.lean
Action:              created | appended | replaced
Label written:       <kebab-case-label>
(lean := "...")      <full Lean name list>
Statement size:      N lines
Proof sketch:        M lines (or "none — definition" / "none — trivial corollary")
{uses} dependencies declared:
  - other-label-1
  - other-label-2
References cited from prose context:
  - Smith 2024 §3.2
Notation matches project convention:
  - $`q_h`, $`\Gamma`, $`f` — all match Foo.lean docstring + Smith 2024
New chapter file created? yes / no
  (if yes: Blueprint.lean needs `import <Project>.Chapters.<Name>` + `{include 0 ...}`)
Open questions for main agent (if any):
  - none | "I picked label `q-expansion-mul`; if a sibling chapter has the same
            label, you'll need to disambiguate in Phase 5"
```
````

### Dispatching workers

For each declaration in **New** + **Drift**:

1. **Order matters for the dep-graph.** Declarations that use another should be
   authored AFTER their dependencies, so the worker can reference the dependency's
   existing label via `{uses "..."}[]`. Topological-sort within the project.
2. Dispatch one `Agent` call per declaration. Wait for completion. Capture the report.
3. Workers may run in parallel within the SAME chapter file ONLY when they don't
   `{uses}` each other. Two workers editing the same chapter file simultaneously
   is a race — serialize per-file.
4. Track an internal log of `(decl_name → chapter_file → label_written)` for the
   Phase-5 validation.

### Forbidden Phase 4 shortcuts

- **Batched worker:** dispatching one Agent to "author the whole chapter" instead
  of one Agent per declaration. Same failure mode as `/cleanup` Phase 4. One
  declaration per worker.
- **Skipping unformalisation:** writing the Lean type verbatim inside a `:::theorem`
  block, just wrapped in the directive. Detection: any directive body containing
  camelCase identifiers, `:=`, raw `→` (vs ``$`\to` ``), `[...]` typeclass brackets,
  or `\leanok` is forbidden.
- **Empty proof sketch:** `:::proof "x":::` with no prose. If the result is
  non-trivial, sketch the strategy. If it IS trivial, omit the proof block entirely.

---

## PHASE 5 — Cross-link pass (Main agent)

After every Phase 4 worker has returned, validate the dep-graph.

### 5a. Collect labels and `{uses}` references

```bash
PROJ="<Project>"
# Labels are the strings inside `"..."` after `:::definition`, `:::theorem`, etc.
grep -rhE ':::(definition|theorem|lemma|proposition|corollary)\s+"[^"]+"' "${PROJ}/Chapters/" \
  | sed -E 's/.*:::(definition|theorem|lemma|proposition|corollary)\s+"([^"]+)".*/\2/' \
  | sort -u > /tmp/labels

# {uses "..."} references
grep -rhE '\{uses\s+"[^"]+"\}' "${PROJ}/Chapters/" \
  | grep -oE '"[^"]+"' \
  | tr -d '"' \
  | sort -u > /tmp/uses
```

### 5b. Orphan check

```bash
comm -23 /tmp/uses /tmp/labels
```

Any line is a `{uses "X"}[]` whose `X` doesn't exist as a label. For each orphan:

1. **Add the missing dependency** — usually because the dependency is a
   declaration in another file not in the Phase-1 enumeration. Dispatch a one-off
   worker to author it.
2. **Rename the reference** — the worker used a slightly wrong label (e.g.
   `"foo-mul"` when the real label is `"foo_mul"`). Patch with `Edit`.
3. **Remove the reference** — the worker over-attributed. Patch with `Edit`.

### 5c. Stale `(lean := "X")` repair (from Phase 1d)

For every Stale entry from Phase 1d:

1. Search the Lean source for a successor: `grep -rE "(theorem|lemma|def|abbrev) <name>" --include="*.lean"`.
2. If a likely successor exists, update `(lean := "X")` to the new name.
3. If no successor, the result was deleted — remove the chunk.

### 5d. Blueprint.lean `import` + `{include}` sync

For every new chapter file created in Phase 4, ensure `<Project>/Blueprint.lean`
has both:

```lean
import <Project>.Chapters.<Name>
-- and inside the #doc body:
{include 0 <Project>.Chapters.<Name>}
```

Place the `{include}` in the position that preserves narrative order
(definitions before consumers).

### 5e. Cross-link report

```
### Phase 5 — Cross-link pass
- Labels defined:               L
- {uses} references made:       U
- Orphan refs resolved:         O   (by add / rename / remove)
- Stale (lean := "X") fixed:    S   (by rename / remove)
- New chapters wired in:        W   (import + {include} added to Blueprint.lean)
```

---

## PHASE 6 — Hand-off to verso-blueprint build

### 6a. Run `./scripts/ci-pages.sh`

```bash
./scripts/ci-pages.sh 2>&1 | tail -40
```

This script runs `lake build <Project>` then
`lake env lean --run <Project>Main.lean --output _out/site`. Any failure here is a
defect in Phase 4 or Phase 5 — re-run those for the offending entries.

The most common failures:
- **Stale `(lean := "X")`** — caught by Verso's elaborator with the exact line
  number. Phase 5c should have caught this; re-run.
- **KaTeX error** — `\foo` macro undefined in math inside a `:::` directive.
  Either declare in `tex_prelude` or use a standard KaTeX command.
- **Unclosed `:::`** — typo in a directive. Verso reports the offending line.

### 6b. Verify the site rendered

```bash
test -f _out/site/html-multi/index.html && echo "site rendered" || echo "site MISSING"
```

If missing despite `ci-pages.sh` succeeding, check `_out/site/` for the actual
output directory — Verso emits a few flavours of HTML output.

### 6c. Tell the user how to view / iterate

```
Blueprint authored and rendered. To view:

  python3 -m http.server -d _out/site/html-multi/        # local preview
  open http://localhost:8000                              # macOS; xdg-open on Linux

To re-sync after Lean code changes:                /blueprint --update
To unformalise + add one specific result:          /blueprint --decl <Foo.bar>
                                              or:  /unformalise <Foo.bar>
```

If the project has the standard GitHub Pages workflow from the template
(`.github/workflows/pages.yml`), commits to `main` deploy automatically to
`https://<user>.github.io/<repo>/`.

### 6d. Optional: open the dep-graph

If `--open` was passed and the project has a sensible default browser, run a
local server and open the rendered index. Otherwise skip.

---

## PHASE 7 — Report

Required artifacts (a missing section = the corresponding phase wasn't completed):

- **Baseline (Phase 0)** — proves doctor ran
- **Inventory (Phase 1)** — proves enumeration happened
- **Plan + user confirmation (Phase 2)** — proves scope was confirmed
- **Prose context written (Phase 3)** — file path exists and was populated
- **Phase 4 per-declaration results** — one row per New / Drift entry
- **Phase 5 cross-link report** — proves orphans/stales/imports were resolved
- **Phase 6 hand-off** — ci-pages.sh exited 0, `_out/site/html-multi/` exists

```
## /blueprint report — <project root>

### Baseline (Phase 0)
- verso-blueprint scaffold:         ✓
- lake build:                        ✓ clean
- lake env lean --run probe:         ✓
- Project files scanned:             47
- Public declarations:               203

### Inventory (Phase 1)
- New:           K1
- Existing OK:   K2
- Stale:         K3
- Drift:         K4
- Chapters touched: C
- New chapter files created: W

### Plan (Phase 2)
User confirmed scope: <restate user's reply or "default whole-project plan accepted">

### Prose context (Phase 3)
File: .mathlib-quality/blueprint/prose_context.md
Sources synthesised: <N reference files, M module docstrings, decomposition.md present/absent>

### Phase 4 per-declaration results
| Declaration                         | Chapter file                  | Action  | Stmt L | Pf L | (lean := …) |
|-------------------------------------|-------------------------------|---------|--------|------|--------------|
| `Foo.qExpansion_mul`                | <Project>/Chapters/Foo.lean   | created |   6    |  4   | ✓            |
| `Foo.qExpansion_eq_disc_mul`        | <Project>/Chapters/Foo.lean   | created |   5    |  3   | ✓            |
| `Bar.helper`                        | <Project>/Chapters/Bar.lean   | replaced|   3    | none | ✓            |
| ...                                                                                              |

### Phase 5 cross-link pass
- Labels defined:    137
- {uses} refs:       214
- Orphans resolved:    2 (1 added, 1 renamed)
- Stale (lean := …) fixed: 3 (3 renamed)
- New chapters wired into Blueprint.lean: 1

### Phase 6 hand-off
- ./scripts/ci-pages.sh:             ✓ exit 0
- _out/site/html-multi/index.html:   ✓ exists
- Build/render instructions printed.

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

Same workflow, but Phase 1 enumeration scope is just `<file.lean>`. Phase 5 still
runs project-wide because a chunk in this file may add `{uses}` to labels defined
elsewhere.

## Mode C: Single declaration + dependency closure

```
/blueprint --decl <Foo.bar>
```

Phase 1 enumeration scope is `<Foo.bar>` and the transitive closure of declarations
it uses, computed by walking `mcp__lean-lsp__lean_local_search`. Useful for
incrementally building a blueprint as you finish each top-level result.

Mathlib declarations are NOT part of the closure — they're "external" and don't
get their own blueprint chunk.

## Mode D: Update / drift-only sweep

```
/blueprint --update
```

Phases 0–2 as usual. Phase 4 authors only **Drift** entries; skips New (use the
default mode for that). Phase 5 still fixes stales.

## Mode E: Check-only

```
/blueprint --check
```

Runs Phases 0, 1, 2 (inventory + diff) and STOPS — no authoring. Use to audit
blueprint freshness without committing time to authoring.

---

## Mode F: Migrate from a legacy LaTeX blueprint

```
/blueprint --migrate-from-latex                       # default: reads blueprint/src/
/blueprint --migrate-from-latex <path/to/latex/dir>   # custom location
```

For projects that already have a LaTeX-stack blueprint (the `\begin{theorem}\lean{...}
\uses{...}\leanok ... \end{theorem}` form, built with `leanblueprint pdf` / `web`) and
want to switch to verso-blueprint. The migration is **mechanical**: it parses every
`.tex` file and emits the corresponding Verso chunks 1:1 with the original prose. It
does NOT re-author or restyle — that's a manual follow-up via `/unformalise` per chunk
if you want polish.

### Pre-flight

The legacy LaTeX tree must exist:

```bash
test -d blueprint/src && ls blueprint/src/*.tex 2>/dev/null | head
```

If the LaTeX tree is at a non-default location, pass it as the first argument.

The verso-blueprint scaffold must ALSO exist (run Phase 0 from Mode A first if not —
the migration writes into `<Project>/Chapters/`).

### Migration mapping (mechanical, 1:1)

| LaTeX construct | Verso translation |
|---|---|
| `\begin{theorem}\label{thm:foo}\lean{Foo.bar}\uses{a,b}\leanok ...\end{theorem}` | `:::theorem "foo" (lean := "Foo.bar") ... :::` with `{uses "a"}[]`, `{uses "b"}[]` at end of body |
| `\begin{definition}\label{def:foo}\lean{Foo.bar} ...\end{definition}` | `:::definition "foo" (lean := "Foo.bar") ... :::` |
| `\begin{lemma}` / `\begin{proposition}` / `\begin{corollary}` | `:::lemma` / `:::proposition` / `:::corollary` (same shape) |
| `\begin{proof}\uses{thm:a}\leanok ...\end{proof}` | `:::proof "foo" ... :::` with `{uses "a"}[]` in body (proof attaches by `"foo"` matching the preceding theorem's label) |
| `\label{thm:foo}` | Bare label `"foo"` — Verso drops the type prefix (`thm:`, `def:`, `lem:`, `prop:`, `cor:`) |
| `\lean{Foo.bar, Foo.baz}` | `(lean := "Foo.bar, Foo.baz")` (unchanged comma-separated list) |
| `\uses{def:a, thm:b}` | `{uses "a"}[]`, `{uses "b"}[]` — split into individual directives, drop type prefixes |
| `\leanok` | **delete** (Verso auto-computes from `(lean := …)`) |
| `\cref{thm:foo}` in prose | `{bpref "foo"}[]` (non-edge link; the dependency edge is already accounted for by the `\uses{}` translation) |
| `$...$` | ``$`...``` |
| `\[ ... \]` or `$$...$$` | ``$$`...```` |
| `\section{<Title>}\label{sec:foo}` | Drop — chapter title comes from `#doc (Manual) "<Title>" =>` |
| `\newcommand{\foo}{\bar}` from a preamble | `tex_prelude "\\def\\foo{\\bar}"` at top of chapter (per chapter that needs it) |
| `blueprint/src/Foo.tex` | `<Project>/Chapters/Foo.lean` (one chapter file per `.tex`) |
| `\input{Foo}` in `blueprint/src/content.tex` | `import <Project>.Chapters.Foo` + `{include 0 ...}` in `<Project>/Blueprint.lean` |

### Migration workflow

```
PHASE M0  PRE-FLIGHT     legacy LaTeX tree exists, verso scaffold exists, lake build clean
PHASE M1  ENUMERATE      walk *.tex; list every \begin{X}\label{...}\lean{...} block
PHASE M2  PLAN           print inventory (N chunks across K LaTeX files → K chapter files); user confirms
PHASE M3  TRANSLATE      one worker per `.tex` file: emit a single Verso chapter file with all chunks
PHASE M4  WIRE           update <Project>/Blueprint.lean with imports + includes for every new chapter
PHASE M5  VERIFY         run ./scripts/ci-pages.sh; surface translation defects
PHASE M6  REPORT         per-file translation summary + manual-review queue
```

### Phase M3 worker prompt (per `.tex` file)

````
You are translating ONE LaTeX blueprint file into a Verso blueprint chapter.

Input file:   blueprint/src/<Name>.tex
Output file:  <Project>/Chapters/<Name>.lean
Project name: <Project>

## Step 1 — Read the LaTeX file

Read `<input file>` in full. Identify every block of the form:

  \begin{<env>}
    \label{<type>:<label>}
    \lean{<list>}           (optional)
    \uses{<list>}           (optional)
    \leanok                 (optional)
    <body>
  \end{<env>}

where `<env>` ∈ {`definition`, `theorem`, `lemma`, `proposition`, `corollary`,
`remark`, `notation`}. Also identify every `\begin{proof}...\end{proof}` block
(which belongs to the immediately preceding theorem-like environment).

Capture preamble macros (`\newcommand{\foo}{\bar}`) if any — they map to a
`tex_prelude` block at the top of the Verso chapter.

## Step 2 — Translate each block

Emit the corresponding Verso directive (table above). Important details:

- The label `<type>:<name>` becomes the bare label `"<name>"` (drop the prefix).
- `(lean := "...")` is the verbatim list from `\lean{...}`.
- `\uses{a, b, c}` → three separate `{uses "a"}[]`, `{uses "b"}[]`, `{uses "c"}[]`
  directives, placed on a single line at the END of the body, prefixed by
  "Depends on:" if the original LaTeX had no narrative anchor for them.
- `\leanok` is DROPPED — Verso auto-computes status.
- Body math: `$...$` → ``$`...```` ; `\[...\]` or `$$...$$` → ``$$`...```` .
- `\cref{X:foo}` in body prose → `{bpref "foo"}[]` (non-edge link; the
  dependency edge is already in the translated `\uses{}`).
- Other inline LaTeX commands (`\emph`, `\textbf`, `\textit`, `\cite`,
  `\url`) — pass through; Verso accepts a LaTeX-ish subset in prose.
  Unknown macros may surface as KaTeX errors at build time; flag them.

## Step 3 — Write the chapter file

Emit:

```lean
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "<Chapter Title — from `\section{...}` or the input filename>" =>

<tex_prelude block if any custom \newcommands were found>

<one Verso directive per LaTeX block, in source order>
```

Use `Write` to create the file (overwrite if it exists — the migration is a
mechanical refresh).

## Step 4 — Report

Return:

```
### Migrated: blueprint/src/<Name>.tex → <Project>/Chapters/<Name>.lean

Chunks translated:
  - definitions:   Nd
  - theorems:      Nt
  - lemmas:        Nl
  - propositions:  Np
  - corollaries:   Nc
  - proofs:        Npf
  - remarks/notation: Nr
\leanok dropped:   Nleanok
\uses split:       Nu_in → Nu_out separate {uses} directives
tex_prelude:       yes / no — N \newcommand macros migrated
Translation defects (REQUIRES MANUAL REVIEW):
  - <line N>: unrecognised LaTeX macro \customFoo — passed through verbatim; will
              likely surface as a KaTeX error
  - <line N>: math block contains \widetilde and \overrightarrow stacked — KaTeX
              may render differently
  - <line N>: \uses{} list had 14 entries — high coupling; review whether all
              should be edges
Open questions for main agent:
  - none | "Chapter file inherits title 'Section 3' from the .tex section;
            confirm in Phase M4 whether to rename"
```
````

### Phase M4 — Wire chapters into Blueprint.lean

For every new chapter file, append to `<Project>/Blueprint.lean`:

```lean
import <Project>.Chapters.<Name>
```

at the imports block, AND

```
{include 0 <Project>.Chapters.<Name>}
```

inside the `#doc (Manual) "..." =>` body, in the position that matches the original
LaTeX `\input{}` order from `blueprint/src/content.tex` (if it exists) — preserves the
narrative flow.

### Phase M5 — Verify the migration builds

```bash
./scripts/ci-pages.sh 2>&1 | tail -40
```

The most likely failures and their fixes:

| Error | Likely cause | Fix |
|---|---|---|
| `unknown declaration 'Foo.bar'` | `\lean{Foo.bar}` referenced a name that doesn't exist in current Lean | Rename in chapter or remove the `(lean := "...")` |
| `KaTeX parse error: \customFoo` | Custom macro not declared in `tex_prelude` | Either add to `tex_prelude` block or replace with standard KaTeX |
| `expected ':::', got '::'` | `:::` typo in a directive | Lean error line is exact; fix |
| `label "foo" redefined` | Two chapters used the same label | Disambiguate (the original LaTeX had unique labels — usually a translation bug) |

### Manual-review queue (REQUIRED ARTIFACT)

After Phase M5, print:

```
## REQUIRES MANUAL REVIEW — migration not 1:1 perfect

LaTeX features that don't translate cleanly:
- <Project>/Chapters/Foo.lean:42 — original used \widetilde inside an array; KaTeX
                                    renders \widetilde over single chars only.
                                    Consider replacing with `\tilde` or splitting the
                                    array into separate displays.
- <Project>/Chapters/Bar.lean:18 — body referenced \cite{smith2024} — Verso has no
                                    BibTeX equivalent. Replace with prose attribution
                                    ("by Smith [2024, §3.2]") or a {bpref} to a
                                    bibliography chapter.

Custom \newcommand macros migrated to tex_prelude (verify they render):
- \re := \operatorname{Re}      (Chapters/Analysis.lean)
- \NN := \mathbb{N}             (Chapters/Basic.lean)
- ...

Prose that was structured by \begin{enumerate} / \begin{itemize}:
- Verso accepts Markdown bullets (- foo / + bar / 1. baz). The translator passed
  the LaTeX environments through verbatim — they may need conversion to Markdown
  for the rendered HTML to format correctly.

\uses{} lists with > 5 entries (high coupling — worth a manual look):
- <Project>/Chapters/Main.lean:217  thm "main-result" had 9 {uses} edges
- ...
```

### Phase M6 — Final report

```
## /blueprint --migrate-from-latex report

### Input
- LaTeX root:               blueprint/src/
- LaTeX files:              17
- LaTeX chunks total:       342 (definitions + theorems + lemmas + …)

### Output
- Verso chapters written:   17 (one per .tex file)
- Blueprint.lean wired:     17 imports + 17 includes added
- tex_prelude blocks:       6 (chapters that needed custom macros)
- \leanok directives dropped: 198 (Verso auto-computes status)
- \uses{} entries split:    489 in → 489 out (one Verso {uses} per LaTeX label)

### Phase M5 build
- ./scripts/ci-pages.sh:    ✓ exit 0
- _out/site/html-multi/:    ✓ exists

### Manual review needed
- KaTeX-incompatible LaTeX:   N items (listed above)
- Custom macros migrated:      M items (verify render)
- High-coupling \uses:         K items (consider {bpref} for non-essential links)

### Next steps
- Eyeball the rendered HTML at _out/site/html-multi/.
- For any chunk whose prose reads awkwardly post-translation, re-author with
  /unformalise --blueprint <decl-name> (it'll respect the new chunk's label).
- Remove the legacy blueprint/ directory once the Verso version is verified.
```

### Caveats

- **Mathematical fidelity is preserved; stylistic polish is not.** The migration is a
  syntax-level translation. If the original LaTeX prose was awkward, the Verso prose
  is awkward too. Re-author chunks via `/unformalise --blueprint` for polish.
- **Custom LaTeX macros may not survive.** KaTeX supports a large LaTeX subset, but
  packages like `tikz`, `xy-pic`, `cancel`, and project-specific `\newcommand` stacks
  often don't translate. The translator emits `tex_prelude` for `\newcommand`s, but
  for diagrams or unusual environments, expect manual cleanup.
- **`\cite` and `\bibliography` are not auto-translated** — Verso's bibliography
  rendering is via `blueprint_bibliography` and a separate Verso-side mechanism. The
  migration passes `\cite{...}` through; replace with prose attribution or a
  `{bpref}` to a manually-authored bibliography chapter.
- **One-shot migration.** Re-running `--migrate-from-latex` overwrites the
  Verso chapter files. Don't re-author Verso chunks AND re-migrate without backing up
  first.

---

## What this command does NOT do

- **Bootstrap the verso-blueprint scaffold from scratch.** That's a one-time
  `cp -r project_template/ ...` from `leanprover/verso-blueprint`. Phase 0 stops
  with instructions if missing.
- **Build a PDF.** verso-blueprint produces HTML only. The dep-graph is interactive
  HTML at `_out/site/html-multi/`.
- **Re-prove the project.** Verso reads the *current* Lean state for auto-progress.
  If a declaration has `sorry`, the blueprint shows it in-progress; it doesn't try
  to discharge sorries. Use `/beastmode` for that.
- **Author informal lemmas with no Lean counterpart.** Every blueprint entry has
  `(lean := "X")` and `X` must elaborate. "Pure prose" entries belong in
  `decomposition.md` (planning), not in the blueprint.

---

## Reference

- `skills/mathlib-quality/references/blueprint-conventions.md` — Verso directives,
  worked examples, anti-patterns, deployment gotchas. Workers read this in Phase 4.
- [`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint) —
  upstream tool. `doc/MANUAL.md` is the canonical directive reference.
- Example blueprints worth reading for style:
  - [`verso-sphere-packing`](https://github.com/ejgallego/verso-sphere-packing)
  - [`verso-flt`](https://github.com/ejgallego/verso-flt)
  - [`verso-carleson`](https://github.com/ejgallego/verso-carleson)
  - [`verso-noperthedron`](https://github.com/ejgallego/verso-noperthedron)
  - [`verso-algebraic-combinatorics`](https://github.com/ejgallego/verso-algebraic-combinatorics)

## Learnings

After completing, record significant patterns to `.mathlib-quality/learnings.jsonl`
— notation conventions that worked / didn't across the project, recurring orphan
patterns (suggests a missing definition file), sketch lengths that turned out too
terse or too verbose.
