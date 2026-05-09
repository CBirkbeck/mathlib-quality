---
name: project-status
description: Mathematician-friendly snapshot of an in-progress /develop project — main goal, dependency tree, blockers, weighted progress bar. Pure mathematical narrative; Lean statements as code blocks but no code spelunking.
---

# /project-status — Mathematician's Project Snapshot

A read-only view of an in-progress mathematical formalisation. Designed for the case
where a non-Lean expert mathematician wants to glance at the project between worker
sessions and understand:

- What is the main goal, in plain mathematical English?
- What chain of intermediate results connects it to the lemma the worker just proved
  and the one currently being attempted?
- Where exactly is the worker stuck — at which step of which proof, and what kind of
  mathematics is missing?
- How much is left?

**Pure mathematical language.** Lean statements appear as code blocks (so the
mathematician can see exactly what was stated), but proof sketches, blockers, and
descriptions are in English. Never paste tactic-level proof text. Never reference
file paths or build errors. The reader has no Lean and no repo access — they have a
chalkboard and an opinion.

This is **read-only with respect to the project**. The agent never edits
project files, never builds, never runs `lean_diagnostic_messages`. It does
spawn a small local HTTP server (Python stdlib only) for the live dashboard,
and writes a PID file at `.mathlib-quality/.status_server.pid` to manage it.
That is the only side effect.

## Usage

```
/project-status                # combined chat snapshot + open live browser dashboard
/project-status T014           # ticket zoom in chat (dashboard already open auto-focuses)
/project-status T014 step 4    # step zoom in chat
/project-status T014/4         # shorthand for the above
/project-status --no-browser   # chat snapshot only; do not start dashboard
/project-status --stop         # kill the running dashboard server
```

This command does two things in parallel on the default invocation:

1. **Live browser dashboard** — starts a local HTTP server (Python stdlib, no
   dependencies) and opens it in the default browser. The dashboard renders a
   clickable mathematical dependency tree on the left and a per-ticket detail
   panel on the right. Arrow keys navigate, Enter focuses, `/` searches,
   `Esc` returns to the project overview. The page polls `/api/status` every
   3 seconds and live-updates as tickets and `.lean` files change. The server
   is idempotent — re-running this command reuses the existing server.

2. **Chat snapshot** — the same combined snapshot in markdown form, rendered
   directly into the chat so the user does not have to switch context to see
   the state. Drill-down (`/project-status T014` etc.) is chat-only zoom.

Three zoom levels — project / ticket / step. The default view is the combined
snapshot. Zoom levels are reached by passing a ticket ID (and optionally a
step). Every chat view ends with a navigation footer listing the next moves so
the reader can walk around the project without leaving the chat.

## Argument parsing (binding)

Parse arguments as follows. Whitespace-separated.

| Args                                   | Dispatch                                                |
|----------------------------------------|---------------------------------------------------------|
| (none)                                 | **combined snapshot** + open dashboard                  |
| `--no-browser`                         | **combined snapshot** in chat only, do not open browser |
| `--stop`                               | kill running dashboard server, no chat output           |
| `--dashboard-only`                     | open dashboard, skip chat snapshot                      |
| matches `^T\d+$` or `^CLEANUP-\w+$`    | **ticket-zoom** in chat (dashboard untouched)           |
| matches `^T\d+/\d+$` etc.              | **step-zoom** in chat (split on `/`)                    |
| ticket ID followed by `step N`         | step-zoom in chat                                       |
| anything else                          | error: list valid ticket IDs                            |

Ticket-ID matching is case-insensitive and tolerates `T014`, `t14`, `T-014`. If the
ID is unknown, list the closest 3 by Levenshtein and stop.

When a ticket-zoom or step-zoom is requested, do **not** also start the
dashboard — the user is drilling in via chat. The dashboard, if already running
from a previous invocation, keeps live-updating in the background.

## Phase −1 — Launch the live dashboard (default and `--dashboard-only` only)

Skip this phase entirely on `--no-browser`, `--stop`, or any drill-down (ticket
or step zoom).

Run the server in the background. The server itself handles idempotency
(checks `.mathlib-quality/.status_server.pid`; if already running, just
re-prints the URL). The slash command must:

1. Verify the server script exists at
   `<plugin-root>/scripts/project_status_server.py`. If not, abort with a clear
   message (the plugin install is broken).
2. Start the server detached, so it survives the slash command exiting:
   ```bash
   nohup python3 <plugin-root>/scripts/project_status_server.py > /dev/null 2>&1 &
   ```
   (Or use the `Bash` tool with `run_in_background: true`.)
3. Wait briefly (≤ 1 s) for the server to write its PID file, then read the URL:
   ```bash
   python3 <plugin-root>/scripts/project_status_server.py --status
   ```
   This prints `http://127.0.0.1:<port>/` if the server is running, or nothing
   if it is not.
4. Open the URL in the user's default browser:
   - macOS:  `open <url>`
   - Linux:  `xdg-open <url>`
   - Windows / WSL: `start <url>` (rare in this project's audience, but handle)
5. Print one line in chat: `🌐 Live dashboard: <url>`. Do this BEFORE the chat
   snapshot so the user can click through immediately.

If the server fails to start (e.g., no Python 3, no free port in 8765-8794),
report the error and continue with the chat snapshot only.

For `--stop`:

```bash
python3 <plugin-root>/scripts/project_status_server.py --stop
```

Print the result and exit.

## Inputs (read-only)

- `.mathlib-quality/plan.md` — the project plan (main goal, sources, references)
- `.mathlib-quality/tickets.md` — the ticket board (every ticket with Statement,
  Proof Sketch, Status, Depends on, Progress checkpoints)
- `.lean` files referenced by tickets — read in two modes:
  - **For `done` tickets**: count `sorry` occurrences, cross-check the claim. Do not
    analyse proof content.
  - **For `in_progress` and `blocked` tickets**: read the declaration in full. The
    point of this command is to isolate the bottleneck. The Progress notes alone are
    not enough — read what the worker has actually attempted: the partial proof
    above the `sorry`, any auxiliary `have` statements, and the current declaration
    signature (which may have drifted from the ticket's stated Statement). This is
    where the agent grounds the mathematical narrative in real code, not speculation.

If `.mathlib-quality/tickets.md` does not exist:

```
No /develop project found in this directory. Run /develop to create a ticket
board, or change to the project's working directory.
```

Stop.

## Phase 0 — Parse the ticket board

Open `.mathlib-quality/tickets.md` and extract every ticket. For each, capture:

| Field | How to extract |
|---|---|
| ID | The `[Tnnn]` or `[CLEANUP-n]` token in the heading `### [...] Title` |
| Title | The remainder of that heading, after the bracketed ID |
| Status | `^- \*\*Status\*\*: (open\|in_progress\|done\|blocked)` |
| File | `^- \*\*File\*\*: (.+)$` |
| Depends on | `^- \*\*Depends on\*\*: (.+)$` (comma-separated IDs, or `none`) |
| Type | `^- \*\*Type\*\*: (.+)$` (lemma / def / def + API lemmas / cleanup / milestone) |
| Statement | The Lean code block under `#### Statement` |
| Sketch steps | Numbered lines `^[0-9]+\.` under `#### Proof sketch` (or `#### Proof Sketch`) — count and capture each step's text |
| Sources | The list under `#### Sources` |
| Mathlib lemmas | The list under `#### Mathlib lemmas needed` |
| Progress entries | Lines under `**Progress**:` — each is `<ISO timestamp>: <note>`, parse timestamp and note |

Open `.mathlib-quality/plan.md` and capture:

- Project title (top `#` heading or first sentence)
- Main goal — the first paragraph or section that describes what is being formalised
  in mathematical English
- Sources — the bibliography section if present

## Phase 1 — Compute progress

**Weighted by sketch step count.** For each ticket:

```
weight(t) =
  | count of numbered sketch steps        if ticket has a numbered Proof Sketch
  | 1                                      otherwise (cleanup tickets, definitions, milestones)
```

Then:

```
done_weight     = sum of weight(t) for tickets with status = done
total_weight    = sum of weight(t) for all tickets
percent         = round(100 * done_weight / total_weight)
```

Counts (independent of weighting): `done`, `in_progress`, `open`, `blocked` ticket counts.

## Phase 2 — Detect blockers and isolate the actual bottleneck

A ticket is a "blocker" (= worth surfacing in the blockers view) if **any** of:

1. Its Status is `blocked`.
2. Its Status is `in_progress` and the **latest** Progress entry contains any of:
   - `PROOF-SKETCH FAILURE`
   - `MATHLIB GAP`
   - `SCOPE / DEFINITION ERROR` or `SCOPE-DEFINITION ERROR`
   - `DEPENDENCY NOT MET`
   - `BLOCKED`
3. Its Status is `in_progress` and the most recent Progress timestamp is more than
   7 days old (= worker has stopped progressing).

For each blocker ticket, **read the file** and isolate the bottleneck. This is the
core of the command — Progress notes are a summary, the file is the truth. From
the file:

- **Stuck step**: locate the `sorry` (or all sorries) in the in-progress declaration.
  Map its position back to the proof sketch: which numbered step is the proof
  currently between? The last closed step is the one above the sorry; the stuck
  step is the one the sorry would discharge. If multiple sorries, list each.
- **What the worker has actually built**: read the partial proof above the
  sorry. Identify the auxiliary `have` statements, intermediate goals, case
  splits. Translate these into mathematical English (e.g., "the worker has
  established that f is bounded on each compact subset, but cannot pass to the
  limit"). Do not paste tactic text into the description; describe the math.
- **Off-track detection**: compare the current declaration in the file against
  the ticket's stated Statement. Differences to flag:
  - Signature drift (added or removed hypotheses, changed conclusion)
  - Renamed declaration
  - Auxiliary lemmas added that aren't in the ticket sketch (= scope creep, or
    legitimate decomposition the ticket didn't anticipate)
  - The declaration has been split into helpers since the ticket was written
- **Mathematical context the worker has relied on**: list the lemmas (custom
  ones from this project, not generic mathlib citations) that are used above
  the sorry. The mathematician reading this can spot if a wrong lemma is being
  invoked or a hypothesis is misapplied.

The blocker brief presents these in mathematical English, not as a code dump.

## Phase 3 — Render the requested view

Three views, dispatched per the argument-parsing table above:

- **Default (no args)** — combined snapshot (this section)
- **`<ID>`** — ticket-zoom (next section)
- **`<ID> step <N>`** — step-zoom (section after that)

---

### Default view — combined snapshot

One single render. Sections in this exact order:

```markdown
# Project Status — <Project Title>

<one-paragraph plain-English summary of the main goal, drawn from plan.md;
do NOT paste Lean here>

## Progress

[████████░░░░░░░░░░░░] <percent>%
<done_weight> / <total_weight> weighted sketch steps complete
<done_count> / <total_count> tickets done

✅ Done: <D>   🚧 In Progress: <P>   ⏳ Open: <O>   🚨 Blocked: <B>

⚠ <K> off-track flags — see Blockers section below
<(omit this line entirely if K = 0)>

## Counts by status × type

|        | Proof | Cleanup | Definitions | Milestones | Total |
|--------|-------|---------|-------------|------------|-------|
| Done   |       |         |             |            |       |
| InProg |       |         |             |            |       |
| Open   |       |         |             |            |       |
| Block  |       |         |             |            |       |

(Definitions = Type contains "def". Milestones = Type contains "milestone" or
ID starts CLEANUP-FINAL.)

## Dependency Chain

<ASCII tree, top-down. Root nodes are the main theorems (tickets with no
dependents). For each node:
- Status icon: ✅ done, 🚧 in_progress, ⏳ open, 🚨 blocked
- Bracketed ID
- A **mathematical name** (English description from the sketch's intro line,
  NOT the verbatim ticket title if it's a structural label like "Prove fooBar_comp")
- An indented one-line Lean statement, truncated to ~80 chars with `…` if longer
- For in-progress / blocked nodes: a `⤷` line summarising the stuck step or blocker keyword
Sort siblings: blockers first, then in_progress, then open, then done. Within
each status tier, by ticket ID ascending. If the graph has multiple roots,
print each as a separate tree, blank line between. If cycles: report and abort.>

```
🚧 [T020] Main theorem: modular forms of weight ≥ 4 form a finite-dimensional space
        dim_modularForms_lt_top : Module.Finite ℂ (ModularForm Γ k)
├── 🚧 [T014] Holomorphy of the Eisenstein series
│        eisensteinSeries_holomorphic (k : ℕ) (hk : 4 ≤ k) : Holomorphic (E k)
│        ⤷ Stuck on step 4: dominated convergence on compact sets
│   ├── ✅ [T013] Termwise holomorphy of (cτ+d)^{-k}
│   └── ✅ [T012] Absolute summability of |cτ+d|^{-k} for k ≥ 4
├── 🚨 [T010] q-expansion principle
│        ⤷ MATHLIB GAP: Fourier expansion of periodic holomorphic function
└── ✅ [T002] FooBar commutes with composition
        fooBar_comp : fooBar s (g ∘ f) = fooBar (s.image f) g
```

## Current Frontier

<For every in_progress ticket — usually one or two — render this block:>

### [<ID>] <Mathematical name in English, not the ticket title verbatim>

<1-2 sentence English description of what this lemma/theorem says,
 paraphrased from the proof sketch's intro line>

```lean
<the Lean Statement, verbatim from tickets.md>
```

**Stuck on:** step <N> of <total> — "<the step's text in English>"
**Last touched:** <ISO timestamp of latest Progress entry>
**Latest worker note:** "<the last Progress line, verbatim>"
↳ Zoom: `/project-status <ID>` (full brief) · `/project-status <ID> step <N>` (this step only)

<If there are no in_progress tickets, replace this whole section with:>
> No ticket is currently in progress. The next ready ticket is `[<next ID>]
> <math name>` — its dependencies are all done and a worker can pick it up via
> `/extended-work`.

## Blockers

<For every blocker ticket from Phase 2, render the full brief below.
Separator `---` between briefs. If there are no blockers:>
> No blocker tickets detected. Every `in_progress` ticket has fresh Progress
> entries (< 7 days) and no hard-stop keyword. Workers are progressing.

<Brief template per blocker ticket:>

### [<ID>] <Mathematical name in English>

**What is being proved.** <2-4 sentences in plain mathematical English
describing the statement and its mathematical content. Paraphrase from sketch
intro + Sources. The reader is a mathematician — use ordinary mathematical
prose, not Lean jargon.>

**Lean statement.**
```lean
<the Statement code block, verbatim>
```

**Proof sketch (where we are).** <Numbered list of the sketch steps. ✅ closed,
🚧 currently being attempted (the stuck step), ⏳ not yet attempted. English,
not tactics.>

1. ✅ <step 1 description in English>
2. ✅ <step 2 description in English>
3. ✅ <step 3 description in English>
4. 🚧 <step 4 description in English>       ← STUCK HERE
5. ⏳ <step 5 description in English>

**What the worker has built so far.** <2-4 sentences in mathematical English
describing the actual partial proof read from the file. Translate `have`
statements and intermediate goals into mathematical claims. Do not paste
tactic text. The state of play as a mathematician would describe it, looking
at the worker's blackboard.>

**Where the proof currently sits.** <1-2 sentences: which sketch step the
sorry would discharge, and what the local goal is in mathematical terms.
If multiple sorries, name each.>

**Off-track flags** (only if present)
<Only render this section if Phase 2 detected drift. Bullets:
- Signature drift: "ticket states ∀ k ≥ 4 ...; current declaration has ∀ k ≥ 6"
- Renamed declaration
- Scope creep: "the file contains 3 auxiliary lemmas not anticipated in the sketch"
- Decomposition: "the ticket's single statement has been split into N helpers"
Omit section entirely if no flags.>

**What would help.** <Concrete mathematical guidance the mathematician can
give: alternative strategy, hypothesis relaxation, literature pointer,
decomposition suggestion. Mention mathlib lemma names only if the gap *is*
a specific missing lemma; even then, frame it mathematically first.>

**Worker notes (latest 3).** <Verbatim Progress entries — the only
Lean-flavoured content in this section.>

- 2026-05-08T14:22 — PROOF-SKETCH FAILURE: step 4 — no mathlib lemma matches
- 2026-05-08T13:55 — closed step 3 (Finset.prod_image)
- 2026-05-08T13:40 — closed step 2 (Finset.prod_comp)

↳ Zoom: `/project-status <ID>` · `/project-status <ID> step <stuck N>`

---

## Oldest in-progress ticket

[<ID>] <math name> — opened <ISO date of first Progress entry>
                  — last touched <ISO date of latest Progress entry>
                  — <days> days since last activity

## Naive ETA

<elapsed> days elapsed (from earliest done-ticket Progress entry to latest entry).
At the current rate (<done_weight> / <elapsed> = X weighted steps/day), the
remaining <total_weight - done_weight> weighted steps would land in ~<Y> days.

⚠ Naive estimate. Doesn't account for blockers, ticket-size variance, parallel
work, the typical fact that the harder steps cluster at the end.

## Cleanup-cadence health

<If `.mathlib-quality/cleanup_audit.md` or similar exists from a recent
/develop --continue R3 audit, summarise. Otherwise:>
(No recent cleanup-cadence audit on file. Run `/develop --continue` to refresh.)

## Drill in

`/project-status <ID>`            zoom into one ticket (full brief)
`/project-status <ID> step <N>`   zoom into one sketch step
```

---

### View: ticket-zoom — `/project-status <ID>`

The mathematician saw something interesting in the overview / tree / blockers
view and wants the full mathematical brief on one ticket. Render:

```markdown
# [<ID>] <Mathematical name in English>

<Status icon> <Status word> · weight <W> · last touched <ISO> · depth <D> in dependency chain

## What this proves

<2-5 sentences in plain mathematical English. Describe the statement, why it is
needed for the project (= which downstream ticket depends on this), and the
intuition. Pull from the ticket's Sources where helpful. The reader is a peer
mathematician, not a student — be precise, not pedagogical.>

## Lean statement

```lean
<verbatim Statement field from the ticket>
```

If the live declaration in the file differs, render a second block labelled
`Live declaration in file (drift detected)`:

```lean
<the actual current signature, read from the file>
```

## Proof sketch — step by step

<Numbered list. For each step, show:
- Status icon (✅ closed / 🚧 current / ⏳ open)
- One-line English description (paraphrased from the sketch text)
- For closed steps: a one-line note on which lemma or argument discharged it,
  drawn from the Progress entries that mention `closed step N`.
- For the current step: the local goal, paraphrased into mathematics from the
  sorry's surrounding context (read the .lean file). Example:
  "🚧 4. Apply dominated convergence on compact sets — local goal: show that
   ∑_{c,d ≠ 0} (cτ+d)^{-k} converges uniformly on every compact K ⊂ ℍ."
- For open steps: the planned approach, in one line.>

1. ✅ <step 1 — closed by …>
2. ✅ <step 2 — closed by …>
3. 🚧 <step 3 — current; local goal: …>
4. ⏳ <step 4 — planned: …>

## Mathematical context

<Read the `.lean` file. List, in mathematical English:
- The auxiliary `have` statements the worker has built above the sorry
  (translated to math: "the worker has shown |a_n(τ)| ≤ M_n with ∑ M_n < ∞")
- Custom lemmas from this project that the proof leans on (by ticket ID where
  possible — these are local citations the mathematician can cross-reference)
- Mathlib lemmas the ticket's `Mathlib lemmas needed` field listed, with a
  one-line gloss on each: "Finset.prod_comp — distributes a product through
  a composition"
This section is the working blackboard. Keep it factual, not narrative.>

## Sources cited by this ticket

<List the bibliography entries from the ticket's Sources field, verbatim.>

## Where this fits in the project

- **Depended on by:** <list of tickets with their math names; "(none)" if a leaf>
- **Depends on:** <list of tickets with their math names; "(none)" if a root>

## Off-track flags <(only if any)>

<As in blockers view — signature drift, scope creep, etc. Omit section if none.>

## Worker progress (full timeline)

<Every Progress entry, verbatim, in chronological order. The mathematician
can see the trajectory. This is the only place tactic-flavoured content
appears in this view.>

- 2026-05-08T14:22 — PROOF-SKETCH FAILURE: step 4 …
- 2026-05-08T13:55 — closed step 3 (Finset.prod_image)
- ...

## Drill in further

`/project-status <ID> step <N>`  zoom into a single sketch step
`/project-status blockers`        all stuck tickets, mathematical briefs
`/project-status tree`            see this ticket's place in the dependency chain
`/project-status overview`        back to the project snapshot
```

If the ticket's status is `done`, simplify: show Statement, the sketch with
all steps closed (with their closing notes), the final Progress timeline, and
"Depended on by" — skip the Mathematical context and Off-track sections.

If the ticket has no Proof Sketch on file, render: "No proof sketch was
recorded for this ticket. Run `/develop --continue` to refresh the board."
Then continue rendering the rest (Statement, dependencies, Progress) as
usual.

---

### View: step-zoom — `/project-status <ID> step <N>` or `<ID>/<N>`

The mathematician wants the deepest level: one specific step of one ticket's
proof. Render:

```markdown
# [<ID>] step <N> of <total> — <one-line step description>

Part of: <ticket math name>      [/project-status <ID> for the full ticket brief]
Status: <✅ closed / 🚧 current / ⏳ open>

## The mathematical step

<2-4 sentences in mathematical English. What does this step actually do in the
argument? What is the input (= what's been established by previous steps)? What
is the output (= what this step concludes, ready for the next step)?

For mathematical content: be specific. Don't say "apply dominated convergence";
say "interchange ∑_{n} and the limit τ' → τ on the compact set K, using the
uniform absolute summability bound Σ M_n < ∞ established in step 2".>

## Local goal (read from the proof state)

<If status is current (= the sorry that is currently being attempted is in this
step): describe the local Lean goal at the sorry in mathematical English. Look
at the file: what's the type of the sorry? Translate it.

If status is closed: state what the goal *was* before this step's tactic, and
what it *became* after — both in mathematical English.

If status is open: predict the goal that this step will face when the previous
steps land, based on the ticket sketch.>

## What's been tried (current step only)

<For the current step, list — in mathematical English, not tactic text — every
approach the worker has attempted. Sources:
- Progress entries between the previous `closed step` and now
- `have` statements in the file that didn't pan out (look for ones followed by
  later rewrites or that don't appear used downstream)
- Worker reports of MATHLIB GAP, PROOF-SKETCH FAILURE etc.

Each attempt as a bullet:
- "Tried using a dominated convergence theorem from mathlib (the integral form);
  the hypothesis shape didn't match — that lemma needs an L¹ majorant whereas
  we have a series majorant."
- "Tried bounding the partial sums uniformly first, then taking the limit — got
  stuck on uniform convergence on the boundary of K."

If status is closed, show what *did* work, with a one-line note. If open,
omit this section.>

## Mathematical ingredients in scope

<List the facts/lemmas/hypotheses available at this step:
- From earlier closed steps in the ticket
- From dependency tickets (other tickets this one depends on; reference by math name)
- From mathlib lemmas listed in the ticket
- From hypotheses of the declaration

This is the "working set" a mathematician would write on the side of the
blackboard. Bullets, terse, mathematical.>

## What would discharge this step

<Concrete suggestions — for open or current steps only:
- A specific mathematical move ("apply Abel summation")
- A literature pointer ("this is Lemma 3 in Serre Ch. VII §2")
- A hypothesis weakening if the current shape is too strong
- A decomposition of the step into smaller sub-steps if it's compound
Each as one bullet, one or two sentences. No padding.>

## Worker notes for this step

<Filter the ticket's Progress entries to those that name `step <N>` or fall
between `closed step <N-1>` and `closed step <N>`. Verbatim. Chronological.>

- 2026-05-08T14:22 — PROOF-SKETCH FAILURE: step 4 — no mathlib lemma matches
- 2026-05-08T14:05 — step 4: trying tendsto_integral_of_dominated_convergence
- 2026-05-08T13:58 — step 4: starting

## Drill in further

`/project-status <ID>`            back to the full ticket brief
`/project-status <ID> step <N±1>` adjacent step (if it exists)
`/project-status overview`        project snapshot
```

If `<N>` is out of range, list the available step numbers with their
one-line descriptions and stop.

If the ticket has no Proof Sketch, this view is not available — return:
"Step zoom requires a proof sketch on the ticket. Run `/develop --continue`
to refresh the ticket board, or use `/project-status <ID>` for the
ticket-level brief."

---

## Tone — mandatory

This command exists so a mathematician can spot the bottleneck and give targeted
guidance. The tone is **mathematical reportage**: describe the state of play, not
the difficulty of the work.

**Forbidden phrases and patterns:**

- "this is a hard problem", "challenging", "difficult", "complex"
- "this is taking a long time", "the worker is struggling", "stuck for a while"
- "we're making slow progress", "this is a big effort", "non-trivial"
- "the worker tried but couldn't"  →  say *what* was tried and *what* the gap is
- "this seems impossible"  →  say *what hypothesis is missing*
- Estimates of how long anything will take, except in the explicit ETA section
  of `progress` view (which is labelled naive)
- Apologies, hedging ("unfortunately", "alas", "regrettably")
- Sympathy for the worker

**Required posture:** describe the mathematics. Where the proof is. What has been
established. What the next step asks. What ingredient is missing. The reader is a
peer who can give technical advice once they see the state — they do not need
preamble.

Compare:

| BAD (rhetorical) | GOOD (descriptive) |
|---|---|
| "Step 4 is proving very challenging." | "Step 4 reduces to interchanging sum and limit on a compact set." |
| "The worker has been stuck on this for days." | "The latest closed step is step 3 (2026-05-06); no further closures since." |
| "This is a tough one — the mathlib API doesn't quite fit." | "The worker needs a uniform absolute bound that is summable in the index and constant in the point; mathlib's nearest match handles the L¹ case." |
| "Unfortunately the proof sketch underestimated this step." | "The sketch's step 4 conflates two facts: termwise holomorphy and dominated convergence." |

The mathematician decides whether something is hard. Don't pre-empt that judgement.

## Off-track detection

Beyond surfacing blockers, this command flags when the worker has drifted from the
plan. A mathematician glancing at the status should notice immediately if:

- The in-progress declaration has a different signature than the ticket states
  (added or removed hypotheses, generalised, specialised, renamed)
- The proof has decomposed into helper lemmas the ticket sketch did not anticipate
- The worker is operating on a declaration not in any ticket
- A `done` ticket's declaration still has `sorry` (the cross-check)
- A ticket is `in_progress` but the file contains no declaration matching its name

Surface these as **Off-track flags** in the blockers view brief and as a count
in the overview footer:

```
⚠ 2 off-track flags — see /project-status blockers for details
```

If there are zero flags, omit the line.

## Implementation rules (binding)

1. **Mathematical English, not Lean.** Descriptions, sketch step labels, blocker
   reasoning, "what the worker has built" are in English. Lean appears only inside
   fenced code blocks (the verbatim Statement field, and the latest Progress
   entries which are quoted as evidence). Never explain a proof in tactics.

2. **No file paths in the rendered output.** The mathematician doesn't read
   `.lean` files. (The agent reads them — but doesn't display the paths.)

3. **Paraphrase ticket titles.** A title like "Prove fooBar_comp" is a label, not
   a mathematical statement. Read the Statement and write a one-line English
   description for the math name. Example:

   - Title: "Prove fooBar_comp"
   - Math name: "FooBar commutes with composition"

4. **Read-only on the project.** No edits to any file under the project root. No
   `lake build`. The agent may use the Read tool on `.lean` files for in-progress
   and blocked tickets to ground the bottleneck description in the actual partial
   proof. No mathlib search calls (those belong to `/extended-work` and
   `/develop`). The only side effects are: starting/stopping the live dashboard
   server (via the script in `scripts/project_status_server.py`), writing
   `.mathlib-quality/.status_server.pid`, and opening a browser tab.

5. **Use the live context.** For each in-progress and blocked ticket, the agent
   MUST read the actual file content of the in-progress declaration. The whole
   point of this command is to isolate the bottleneck from real code, not to
   parrot Progress notes. An agent that skips file reads has done the user's
   work poorly.

6. **Honesty.** If the ticket board is incomplete (sketches missing, Progress
   entries missing), say so. Do not synthesise content the tickets don't contain.
   "No proof sketch on file for this ticket" is an acceptable line. If the
   in-progress file content disagrees with the ticket, report both — don't
   silently reconcile.

7. **Fail loud.** If `.mathlib-quality/tickets.md` is malformed (e.g., a ticket
   missing a Status), report which ticket and continue rendering the rest, marking
   the malformed one explicitly.

## Example session

```
$ /project-status

# Project Status — Modular Forms of Weight k ≥ 4

We are formalising the classical theory of modular forms for SL₂(ℤ), aiming
at the finite-dimensionality theorem dim Mₖ(Γ) < ∞ for k ≥ 4. Following Serre,
Cours d'arithmétique, Chapter VII.

## Progress

[████████░░░░░░░░░░░░] 38% — 12/30 tickets, 84/220 weighted steps

✅ Done: 12   🚧 In Progress: 2   ⏳ Open: 14   🚨 Blocked: 2

## Current Frontier

### [T014] Holomorphy of the Eisenstein series

The Eisenstein series E_k(τ) = Σ_{(c,d) ≠ 0} (cτ+d)^{-k} converges absolutely
for k ≥ 4 and defines a holomorphic function on the upper half plane.

```lean
theorem eisensteinSeries_holomorphic (k : ℕ) (hk : 4 ≤ k) :
    Holomorphic (eisensteinSeries k) := by sorry
```

**Stuck on:** step 4 of 5 — "Apply dominated convergence on compact sets"
**Last touched:** 2026-05-08T14:22
**Latest worker note:** "PROOF-SKETCH FAILURE: step 4 — no mathlib lemma matches; need Morera's"

## Top Blockers

1. **[T014]** Holomorphy of the Eisenstein series — stuck applying dominated
   convergence. The mathlib lemma the worker tried is for integrals, not series
   of holomorphic functions; the right ingredient is a uniform absolute summable
   bound on each compact set.

2. **[T010]** q-expansion principle — needs a Fourier expansion of a periodic
   holomorphic function. Worker reports a MATHLIB GAP.

## More

`/project-status tree` — mathematical dependency chain
`/project-status blockers` — full briefs on every stuck ticket
`/project-status progress` — counts and ETA estimate
```
