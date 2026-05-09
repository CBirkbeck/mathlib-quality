---
name: project-status
description: Mathematician's snapshot of a /develop project — chat summary + live browser dashboard. The agent un-formalises the project's Lean code into mathematical English so the dashboard renders maths, not just signatures.
---

# /project-status — Mathematician's Project Snapshot

A read-only view of an in-progress mathematical formalisation. The audience is
an expert mathematician who wants to glance between work sessions, spot
bottlenecks, and offer guidance — without reading any Lean code.

## Source of truth: the .lean code, not the ticket file

The project's `.lean` files are the source of truth. The ticket file
(`tickets.md`) is a status overlay only — it tells us which declarations are
open / in_progress / done, but it does **not** supply the mathematical
content. Every command run, the agent:

1. Discovers every declaration in the project (the server scans `.lean` files).
2. For each declaration, **un-formalises** the Lean code into mathematical
   English: a short math name, a 1-3 sentence description of what's being
   asserted, and (for declarations with `sorry`) a narrative of where the
   proof currently sits.
3. Writes the un-formalisation to `.mathlib-quality/.status_annotations.json`.
4. The server merges that sidecar into every dashboard snapshot, so the
   browser renders mathematics rather than raw Lean signatures.

The ticket file's role: matched by declaration name, it adds the worker's
`open` / `in_progress` / `blocked` status and the Progress timeline.
Declarations with a `sorry` but no matching ticket are flagged "unticketed
sorries".

## Usage

```
/project-status                       # combined chat snapshot + open live browser dashboard
/project-status fooBar_comp           # per-declaration zoom in chat (unqualified name)
/project-status MyProj.fooBar_comp    # per-declaration zoom in chat (fully qualified)
/project-status --no-browser          # chat snapshot only; do not start dashboard
/project-status --skip-unformalise    # use existing annotations, do not re-annotate
/project-status --stop                # kill the running dashboard server
```

The default invocation does **all four** of:

1. Start the dashboard server (background, idempotent).
2. Fetch the structural snapshot (every declaration with its full body).
3. **Un-formalise** the project's Lean code into mathematical English and
   write the JSON sidecar (this is the bulk of the work).
4. Open the browser tab AND print the chat snapshot.

The dashboard stays open between invocations and live-updates structural
data every 3 s. The mathematical un-formalisation refreshes only when this
command is re-run — it is the agent's work, not the server's.

## Phase 0 — Launch the live server

Skip on `--stop` (which just kills the server) or any drill-down (the user
is asking for a chat brief; an already-running dashboard keeps live-updating
in the background).

```bash
nohup python3 <plugin-root>/scripts/project_status_server.py > /dev/null 2>&1 &
```

(Or use the `Bash` tool with `run_in_background: true`.) Wait briefly and
read the URL:

```bash
python3 <plugin-root>/scripts/project_status_server.py --status
```

Print one line in chat: `🌐 Live dashboard: <url>`. Then `open <url>` (macOS)
or `xdg-open <url>` (Linux) to launch the browser.

For `--stop`:

```bash
python3 <plugin-root>/scripts/project_status_server.py --stop
```

Print the result and exit.

## Phase 1 — Fetch the structural snapshot

```bash
curl -s http://127.0.0.1:<port>/api/structure
```

The response is a JSON object with:

- `title`, `main_goal_lean` (from `plan.md`)
- `decls`: a list of declaration dicts, each with:
  - `name` (fully qualified), `local_name`, `kind`, `file_path`, `line_range`
  - `namespace`, `is_private`
  - `lean_signature` — the declaration head through `:= by` / `:=` / `where`
  - `lean_body_full` — every line of the declaration block, verbatim, for
    you to read and un-formalise
  - `has_sorry`, `sorry_lines`, `haves` (each `{name, type_hint}`)
  - `depends_on` — internal references found in the body (other project decls)
  - `depended_on_by` — inverse
  - `body_hash` — sha256 prefix; use this to skip re-annotating unchanged decls
  - `ticket_id`, `ticket_status`, `progress_entries` — overlay from `tickets.md`
  - `status` — computed: `done` / `in_progress` / `blocked` / `open` /
    `has_sorry_no_ticket`

If the snapshot is empty (no `.lean` files, or the server is not running),
report and stop. Don't fabricate content.

## Phase 2 — Un-formalise (the heart of this command)

For every declaration in the structural snapshot, write English annotations.
Read the existing `.mathlib-quality/.status_annotations.json` first; **skip**
any declaration whose `body_hash` matches the existing entry. This makes
re-runs cheap on large projects.

For each declaration that needs un-formalising, produce:

### `math_name` (always)
4-10 words of plain English describing **what the declaration is or claims**.
Not the Lean identifier. Not a sentence with a verb if a noun phrase fits.

Examples:

| Lean | math_name |
|---|---|
| `theorem fooBar_comp : fooBar s (g ∘ f) = fooBar (s.image f) g` | "FooBar commutes with composition" |
| `theorem eisensteinSeries_holomorphic (k : ℕ) (hk : 4 ≤ k) : Holomorphic (E k)` | "Holomorphy of the Eisenstein series" |
| `def cauchyPrincipalValue (f : ℝ → ℂ) : ℂ` | "Cauchy principal value of an integral" |
| `lemma norm_le_of_compact (hK : IsCompact K) : ‖f x‖ ≤ M` | "Norm bound of a continuous function on a compact set" |

For `def` and `structure` declarations, the math name is the noun (the
mathematical object being defined). For `theorem`/`lemma`, it's the
result (the conclusion paraphrased).

### `description` (always, 1-3 sentences)
Plain mathematical English — what this declaration asserts. The reader is
a peer mathematician who reads the math name and wants the precise
statement at a glance. Refer to the Lean signature to get the type
shape correctly. Use mathematical notation (∑, ℝ, τ, etc.) where natural.
Do NOT use Lean tactic vocabulary ("rewrite using", "applies").

Examples:

> The Eisenstein series $E_k(\tau) = \sum_{(c,d) \neq 0} (c\tau + d)^{-k}$
> is holomorphic on the upper half-plane $\mathbb{H}$ for every weight $k \geq 4$.

> Asserts that the FooBar product distributes through function composition:
> applying $g \circ f$ over $s$ gives the same product as $g$ over $s.\mathrm{image}\, f$.
> The hypothesis is that $\alpha, \beta, \gamma$ are commutative monoids.

### `proof_state_english` (only if `has_sorry`, 2-4 sentences)
Read the `lean_body_full`. Identify what the worker has built (auxiliary
`have`s, intermediate goals, case splits) and translate to mathematical
claims. Identify what the remaining `sorry` would prove — the local goal,
read from the surrounding context. State all of this in mathematical
English.

Example:

> The worker has reduced the goal to showing the partial sums $S_N(\tau) =
> \sum_{|c|+|d| \leq N} (c\tau+d)^{-k}$ converge uniformly on each compact
> subset of $\mathbb{H}$. The auxiliary bound `h_summable` establishes
> $\sum_n n^{-k} < \infty$, which provides the dominant series. The
> remaining sorry asks to interchange the limit $N \to \infty$ with the
> evaluation at $\tau$ — the standard Weierstrass M-test argument that
> mathlib's library should already cover.

If the body is essentially empty (just `sorry`), say so:

> The declaration is stated but no proof has been started. The next move
> is whatever the proof sketch suggests — see the ticket if one exists.

### `ingredients_in_scope` (only if `has_sorry`, 2-6 bullets)
Each bullet is one phrase naming a mathematical fact available at the
sorry. Source from: hypotheses of the declaration; established `have`
statements (translated mathematically); conclusions of dependency
declarations the body uses; standard mathlib facts the body imports.

Example bullets:

- "Termwise holomorphy of $(c\tau + d)^{-k}$ for fixed $(c,d) \neq 0$ — established by `h_termwise`"
- "Absolute summability $\sum_n n^{-k} < \infty$ for $k \geq 4$ — from dependency `absolute_summability`"
- "The compact set $K \subset \mathbb{H}$ has positive distance from the boundary"
- "Mathlib's Weierstrass M-test: `tendsto_uniformly_of_summable`"

### `what_would_help` (only if status is `blocked` or appears stuck, 2-4 bullets)
Concrete mathematical guidance the mathematician could give. Alternative
strategy, hypothesis relaxation, literature pointer, decomposition
suggestion. NOT generic encouragement.

Examples:

- "Try Morera's theorem: integrate around any triangle in $\mathbb{H}$ and use Cauchy's theorem on each summand"
- "If the statement is relaxed to weight $k \geq 6$, the dominant series is $\sum n^{-6}$ which mathlib has more directly"
- "Serre, *Cours d'arithmétique*, Ch. VII §2 gives this as Lemma 1; the trick is to bound by a fixed-radius shell"

### Project-level annotation

After per-declaration annotations, write the project-level fields:

- **`project_goal_english`** (one paragraph) — what this whole project is
  trying to prove, in mathematical English. Compose by reading: the
  `plan.md` main paragraph (if any); the math_names and descriptions of
  the project's roots (the declarations nothing depends on); any
  `tickets.md` introduction.

- **`project_main_decls`** (1-5 declaration names) — the declarations that
  best represent the project's main results. By default the roots from
  the structural snapshot. Trim trivial roots (basic API lemmas, deprecated
  shims) so the dashboard's "Top-level results" section is the result the
  reader actually cares about.

### Write the file

Write to `.mathlib-quality/.status_annotations.json` in this shape:

```json
{
  "version": 1,
  "generated_at": "<ISO timestamp now>",
  "project_goal_english": "...",
  "project_main_decls": ["MyProj.main_theorem"],
  "declarations": {
    "MyProj.fooBar_comp": {
      "math_name": "FooBar commutes with composition",
      "description": "Asserts that the fooBar product distributes through function composition.",
      "proof_state_english": null,
      "ingredients_in_scope": null,
      "what_would_help": null,
      "body_hash": "abc123def456",
      "annotated_at": "2026-05-09T10:30:00Z"
    },
    "MyProj.eisensteinSeries_holomorphic": {
      "math_name": "Holomorphy of the Eisenstein series",
      "description": "...",
      "proof_state_english": "...",
      "ingredients_in_scope": ["...", "..."],
      "what_would_help": ["...", "..."],
      "body_hash": "...",
      "annotated_at": "..."
    }
  }
}
```

**Merge with existing annotations.** Read the existing file first.
For each declaration:
- If it doesn't appear in the structural snapshot anymore (deleted from
  code), drop its annotation.
- If its existing `body_hash` matches the current snapshot's `body_hash`,
  keep the existing annotation entry verbatim.
- Otherwise re-annotate.

This keeps the cost of re-runs proportional to *changed* declarations,
not total declarations.

## Phase 3 — Open browser

After writing the JSON, open the dashboard URL (already known from Phase 0).
The page will pick up the new annotations on its next 3 s poll.

## Phase 4 — Chat snapshot

Print the same content as the dashboard's project overview, in markdown.

```markdown
# Project Status — <Project Title>

<project_goal_english — one paragraph>

## Progress

[████████░░░░░░░░░░░░] <percent>% — <done> / <total> declarations done

✅ Done: <D>   🚧 In Progress: <P>   ⏳ Open: <O>   🚨 Blocked: <B>   🟣 Unticketed: <U>

## Top-level results

<For each name in project_main_decls:>
- <status icon> **<math_name>** — <description's first sentence>
  ↳ Zoom: `/project-status <local_name>`

## Current frontier

<For every declaration with status in {in_progress, blocked, has_sorry_no_ticket},
ordered by status (blocked → in_progress → has_sorry_no_ticket):>

### <math_name>  ·  <local_name>

<description (1 sentence)>

```lean
<lean_signature>
```

**Where the proof currently sits.** <proof_state_english>

**Ingredients in scope.**
- <ingredient 1>
- <ingredient 2>

**What would help** (only if `what_would_help` is populated)
- <bullet 1>
- <bullet 2>

↳ Zoom: `/project-status <local_name>` (full brief)

---

<continue for each frontier declaration>

## Drill in

`/project-status <decl-name>`        full mathematical brief on one declaration
`/project-status --skip-unformalise` refresh the chat snapshot without re-annotating
🌐 Live dashboard: <url>             interactive tree, arrow-key navigation
```

## Drill-down — `/project-status <decl-name>`

In chat, render the full per-declaration brief — same content as the
dashboard's detail panel, in markdown:

```markdown
# <math_name>  ·  <local_name>

**Status:** <status pill>      **File:** <file_path>:<line_start>
**Kind:** <kind>      **Ticket:** <ticket_id> (<ticket_status>) (only if ticketed)

<description (full)>

## Lean signature

```lean
<lean_signature>
```

## Where the proof currently sits  (only if has_sorry)

<proof_state_english>

## Ingredients in scope  (only if has_sorry)

- <ingredients_in_scope bullets>

## What would help  (only if blocker)

- <what_would_help bullets>

## Auxiliary `have` statements  (only if any)

- `<name>` : `<type_hint>`
- ...

## Connections

- **Depends on:** <comma-separated math_names with local_name in monospace, links to `/project-status <name>`>
- **Used by:** <same shape>

## Worker progress  (only if ticketed and has progress_entries)

- <verbatim progress entries>
```

## Tone — mandatory

The same tone rules as the chat snapshot apply at every drill-down level.

**Forbidden phrases and patterns:**

- "this is a hard problem", "challenging", "difficult", "complex", "non-trivial"
- "this is taking a long time", "the worker is struggling", "stuck for a while"
- "we're making slow progress", "this is a big effort"
- "the worker tried but couldn't"  →  say *what* was tried and *what* the gap is
- "this seems impossible"  →  say *what hypothesis is missing*
- Estimates of how long anything will take
- Apologies, hedging ("unfortunately", "alas", "regrettably")
- Sympathy for the worker

**Required posture:** describe the mathematics. Where the proof is. What has
been established. What the next step asks. What ingredient is missing. The
reader is a peer who can give technical advice once they see the state.

## Off-track detection

The server already exposes (via `status` and `ticket_status`) when:

- A declaration has `sorry` but its ticket says `done` → flagged `blocked`
  (status mismatch — file lags ticket)
- A declaration has `sorry` and no ticket → flagged `has_sorry_no_ticket`
  (unticketed work, possibly scope creep)

Surface these in the chat snapshot's "Current frontier" with appropriate
icons. The agent does not have to compute them; they're in the snapshot.

## Implementation rules (binding)

1. **Mathematical English, not Lean.** Math names, descriptions, proof-state
   narratives, ingredients, what-would-help — all English. Lean appears only
   inside fenced code blocks (the verbatim `lean_signature`, and progress
   entries when quoted as evidence). Never explain a proof in tactics.

2. **No tactic vocabulary in prose.** "applies dominated convergence",
   "rewrites using", "uses simp_rw" — these belong in the proof, not in the
   un-formalisation. Translate to mathematics: "interchanges the limit and
   sum", "substitutes the identity", "expands by lemma X".

3. **Read the live code.** Do not rely on tickets for content. The agent
   should read `lean_body_full` from the structural snapshot for every
   declaration with `has_sorry`, and base `proof_state_english` on what it
   sees in the body — not on speculation, and not on ticket sketches alone.

4. **Body-hash caching.** Skip re-annotating any declaration whose
   `body_hash` matches the existing annotation. Re-runs on large projects
   should take seconds, not minutes.

5. **Don't fabricate.** If a declaration is opaque (just `sorry` with no
   structure), say so: "The declaration is stated but the proof has not
   been started." Don't invent ingredients or strategies that aren't in
   the code.

6. **Read-only on the project.** No edits to `.lean` files, no `lake build`,
   no mathlib search. Side effects: spawning the dashboard server, writing
   `.mathlib-quality/.status_annotations.json` and `.status_server.pid`,
   opening a browser tab.

7. **Be honest about state.** If `plan.md` is missing, project_goal_english
   may have to be assembled from the math_names of the roots — say so in
   the goal paragraph if needed. If the server isn't running and won't
   start, fall back to chat-only mode and report the failure.

## Performance notes

- The server caches `.lean` parses by file mtime, so repeated polling is
  cheap even on large projects.
- The agent's un-formalisation is the expensive step. Use the body_hash
  cache aggressively — only re-annotate declarations that have changed.
- For projects with many done declarations, you can produce shorter
  `description` fields (one short sentence) since they're not the focus
  of the dashboard. Spend the budget on `proof_state_english` and
  `what_would_help` for sorries.

## Failure modes

- **No `.lean` files** → "No Lean code found in this project. /project-status
  requires `.lean` files to render."
- **Server fails to start** → fall back to `--no-browser` behaviour and
  report.
- **`.mathlib-quality/` is read-only** → cannot write annotations; report
  and continue with chat snapshot from the structural data only.
- **Body parse error on a malformed file** → skip that file, list it in a
  "Could not parse" section at the end of the chat snapshot.
