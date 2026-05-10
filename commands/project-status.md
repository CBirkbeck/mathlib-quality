---
name: project-status
description: Chat-only mathematical status of a /develop project. The agent reads the project's .lean files, identifies the result the worker is currently on (or blocked on), and reports in mathematical English what's being proved, where the proof sits, how it connects to the overall goal, and how far along the whole project is. No server, no browser, no sidecar files. Read-only.
---

# /project-status — What is the worker doing, and how does it fit?

A chat-only status report. The agent reads the project's `.lean` code (and
`.mathlib-quality/plan.md` and `.mathlib-quality/tickets.md` if they exist),
un-formalises into mathematical English, and answers four questions:

1. **What mathematical result is the worker currently on?**
2. **What (if anything) is blocked, and what is missing?**
3. **How does the current work connect to the project's overall goal?**
4. **How far along is the whole project?**

The audience is an expert mathematician glancing between work sessions. The
report is mathematical reportage — not Lean tactics, not difficulty rhetoric.

This command is **read-only** on every file. It does not start servers, open
browsers, or write sidecar JSONs.

## Inputs

- `.mathlib-quality/plan.md` (if present) — project goal, sources
- `.mathlib-quality/tickets.md` (if present) — status overlay (`open` /
  `in_progress` / `done` / `blocked`) per ticket, matched to declarations
  by name. Tickets are a status hint, not a content source.
- Every `.lean` file under the project root, skipping `.lake/`, `.git/`,
  `build/`, `node_modules/`, `.mathlib-quality/`, `.venv/`, `__pycache__/`.

## Phase 1 — Discover declarations

For every `.lean` file in scope, find every top-level declaration (theorem /
lemma / def / abbrev / instance / structure / inductive / class). For each:

- Fully-qualified name (apply enclosing `namespace ... end`) and local name
- Kind, file path, line range
- Signature: from the declaration head through the first `:=` or `:= by`
- Whether the body contains `sorry`
- The auxiliary `have` statements in the body (name and type hint)
- The internal references in the body (other project declarations whose
  names appear in the body — used to chain a declaration up to the
  project's main results)

## Phase 2 — Identify the current focus

The worker's current focus is, in priority order:

1. **Tickets marked `in_progress`** — match to a declaration by name. The
   ticket's most recent Progress entry tells you the timestamp.
2. **Declarations with `sorry`** whose `.lean` file mtime is within the
   last few days (= recent activity, even without ticket).
3. **Tickets marked `blocked`** — these need explicit attention.

Pick the most recently active one or two as "currently working on". List
any blocked tickets/declarations separately.

If nothing is in_progress and nothing has recent edits, say so plainly:
"No active work detected. The next ready declaration is `<name>`, whose
dependencies are all done."

## Phase 3 — Distill the project's overall goal

In one paragraph of mathematical English, state what the project is
trying to prove. Sources to combine:

- `plan.md`'s opening paragraph
- The project's **top-level theorems** — declarations of kind `theorem` or
  `lemma` that no other declaration uses (= leaves of the "depended-on-by"
  relation, = the user-facing outputs)

If `plan.md` is missing, distil the goal from the top-level theorems'
signatures alone. Don't fabricate content the project doesn't contain. If
genuinely unclear, say so.

## Phase 4 — Connect current work to the goal

For each declaration the worker is on, trace the dependency chain upward:
this lemma is used by X, which is used by Y, which proves the project's
main theorem Z. Express the chain in mathematical English using math names
(not Lean identifiers) where you can. One or two sentences per declaration.

## Phase 5 — Compute progress

Simple counts:

- `done` = body contains no `sorry`
- `has_sorry` = body contains `sorry`
- `percent = done / (done + has_sorry)`

This is a coarse measure. If the project has detailed proof sketches in
`tickets.md`, you may report a step-weighted percentage instead (each
ticket contributes one weight per numbered sketch step). The simple count
is usually fine and faster.

## Phase 6 — Render the report

The whole report is markdown. Length: a few short paragraphs total. The
mathematician can ask follow-ups. Don't dump everything; answer the four
questions cleanly.

```markdown
# Project Status — <Project Title>

## Overall goal

<one paragraph in mathematical English describing what this project is
trying to prove. Pull from plan.md and the top-level theorems. Don't paste
Lean code here.>

## Currently working on

### <math name, 4-10 words of English>

```lean
<the Lean signature, verbatim>
```

<2-3 sentences of mathematical English: what does this declaration assert?
The reader is a peer mathematician — be precise, not pedagogical.>

**Where the proof currently sits.** <2-4 sentences. Read the body.
Translate the auxiliary `have` statements into mathematical claims ("the
worker has shown f is bounded on each compact set and that the partial
sums are Cauchy"). Identify what the remaining `sorry` would prove,
expressed mathematically. Do not paste tactic text.>

**How this connects to the overall goal.** <1-3 sentences. Trace the
dependency chain in mathematical names: this lemma is needed for X, which
proves Y, which is the project's main result Z.>

(repeat the block for each declaration the worker is currently on; usually
one or two)

## Blocked  (only if any)

### <math name>

<one sentence: what does this declaration assert?>

**What is missing.** <2-3 sentences in mathematical English. State the
mathematical gap precisely: a hypothesis is too strong, a mathlib lemma
has the wrong shape, a proof strategy hits a step that requires X.
Do NOT say "this is hard" or "the worker is struggling".>

**What would help.** <2-3 concrete bullets. Alternative proof strategy,
hypothesis relaxation, literature pointer. Mathematical guidance, not
encouragement.>

## Progress

[████░░░░░░░░] <percent>% — <done> of <total> declarations have a complete
proof; <has_sorry> still contain `sorry`.

<one or two sentences. What's done, what's the current frontier, what's
ahead. Examples:
- "The basic API for FooBar is in place. The current frontier is the
  holomorphy of Eisenstein series; q-expansion is blocked."
- "All definitions are recorded; only the main convergence theorem and
  three of its supporting lemmas remain."
>
```

## Tone — mandatory

The forbidden phrases and required posture from previous versions still
apply.

**Forbidden:**
- "this is hard / challenging / difficult / non-trivial / complex"
- "the worker is struggling / stuck for a while / making slow progress"
- "this is taking a long time / is a big effort"
- Time estimates of how long anything will take
- Apologies, hedging ("unfortunately", "alas", "regrettably")
- Sympathy for the worker

**Required:** describe the mathematics. Where the proof is. What has been
established. What the next step asks. What ingredient is missing. The
mathematician decides what's hard.

## Implementation rules (binding)

1. **Mathematical English, not Lean.** Math names, descriptions, proof-state
   narratives, "how this connects" — all English. Lean appears only inside
   fenced code blocks (the verbatim signature of the declaration in focus).
   Never explain a proof in tactics. Never use Lean tactic vocabulary
   ("rewrite using", "applies", "uses simp_rw") in prose — translate to
   mathematics.

2. **Don't fabricate.** If a body is just `sorry`, say "the declaration is
   stated but the proof has not been started". Don't invent strategies the
   code doesn't contain. Don't invent a project goal richer than what's in
   `plan.md` plus the top-level signatures.

3. **No file paths in the rendered output.** The mathematician doesn't read
   `.lean` files. (The agent reads them — but doesn't display the paths.)

4. **Read-only.** No edits. No `lake build`. No mathlib search. The agent
   reads files with the `Read` tool, walks the project with `Bash` (for
   `find`/`grep`-style discovery if useful), and that's it.

5. **Be concise.** A few paragraphs. The mathematician asks follow-up
   questions if they want more.

## Drill-down

If the user asks a follow-up like "tell me more about T014" or "what
exactly is missing in `eisensteinSeries_holomorphic`?", expand on that
specific declaration in the same mathematical-English style: more detail
on the partial proof, more `have` statements translated, more context on
the overall goal. Still no tactic text.

## Failure modes

- **No `.lean` files in the project** → "No Lean code found in this
  directory. Run `/project-status` from the project root."
- **No `plan.md` and no top-level theorems** → state the goal as best you
  can from whatever theorems exist, and note explicitly that there is no
  recorded high-level goal.
- **Every declaration is `done`** → "All declarations have complete
  proofs. The project may be ready for `/pre-submit`."
- **No declarations with sorry have any recent activity** → "No active
  work detected." Then list the open declarations briefly, in
  dependency order.
