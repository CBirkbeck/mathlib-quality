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

## Self-contained for a cold reader (binding principle)

The reader has **not** followed the formalisation closely and **cannot**
open any file. Everything they need to understand the state of play must
be in the report itself. Concretely:

- **Define what is non-standard.** The first time a project-specific
  notion appears (`eisensteinSeries`, `cauchyPrincipalValue`,
  `fooBar`, etc.), state its mathematical content in one phrase:
  "the Eisenstein series E_k(τ) = ∑_{(c,d) ≠ 0} (cτ + d)^(−k)",
  not "eisensteinSeries (the project's main object)".

- **Translate structural moves.** When the proof body uses Lean's
  structural tactics (`obtain`, `refine`, `constructor`, `have`, `use`),
  do not say "the worker obtains a witness" or "splits into cases".
  Say *what* the witness is, *what* the cases are, *what* the parametric
  intermediate claim asserts. The reader doesn't know Lean tactics; they
  know mathematics.

- **Spell out parametric / universally-quantified intermediate results.**
  When the proof builds a fact of shape "for every ε > 0 there is N such
  that …", state the universal claim explicitly. Don't hide it behind a
  name like `h_cauchy`.

- **Name the witnesses.** When the proof chooses a specific bound,
  constant, or function, say what it is. "The worker chose M = π²/6 as
  the upper bound, motivated by ∑ n⁻² = π²/6." Not "fixes a constant".

- **List sub-goals.** When the goal has been refined into several parts,
  list every part in mathematical terms and mark each as discharged or
  outstanding.

If the body has no structural complexity (e.g. a near-one-line proof or
just `sorry`), the report can be brief. Length follows content.

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
- `total = done + has_sorry`
- `percent = round(100 × done / total)` (with `total = 0` → `percent = 0`)

This is a coarse measure. If the project has detailed proof sketches in
`tickets.md`, you may report a step-weighted percentage instead (each
ticket contributes one weight per numbered sketch step). The simple count
is usually fine and faster.

**Progress bar (binding).** The progress line is a single mandatory
string. Do not improvise the format, the bar width, the bar characters,
or omit any field.

```
[<20-cell bar>] <percent>% — <done>/<total> declarations sorry-free, <has_sorry> with sorry
```

- The brackets `[` and `]` are mandatory.
- The bar is exactly 20 cells. Filled cells = `round(percent / 5)`.
  Empty cells = `20 − filled`.
- Use `█` for filled and `░` for empty. ASCII fallback only if you have
  evidence the user's terminal mangles those characters: `#` for filled,
  `-` for empty, still 20-cell. Do not use other characters (no `▰`, no
  `▱`, no `=`, no `■`).
- The percentage is mandatory even at 0% or 100%. Show as a plain
  integer with `%` suffix, no decimals.
- Both counts (`done`/`total` and `has_sorry`) are mandatory.
- The literal word "declarations" stays — it tells the reader what's
  being counted.

Worked examples (note every field is present in every case):

```
0%    [░░░░░░░░░░░░░░░░░░░░] 0% — 0/30 declarations sorry-free, 30 with sorry
25%   [█████░░░░░░░░░░░░░░░] 25% — 8/30 declarations sorry-free, 22 with sorry
38%   [████████░░░░░░░░░░░░] 38% — 12/32 declarations sorry-free, 20 with sorry
50%   [██████████░░░░░░░░░░] 50% — 15/30 declarations sorry-free, 15 with sorry
100%  [████████████████████] 100% — 14261/14261 declarations sorry-free, 0 with sorry
```

**The 100% case (binding).** If the bar shows 100% (= every named
declaration is sorry-free), the "Currently working on" and "Blocked"
sections cannot legitimately describe new proof work — there is none.
The active work, if any, is necessarily something else: an axiom audit,
a refactor, a generalisation, decomposition of a proof, performance
tuning, or work happening in a sub-step / scratch file the discovery
walk missed. State this honestly. Two acceptable shapes:

- "All 14261 declarations are sorry-free. The active work is a refactor
  of the projector-compatibility lemmas to remove a custom axiom — no
  new theorems, just changing how existing ones are proved."

- "All named declarations are sorry-free, but the discovery walk only
  scanned files under `<root>/Project/`; there is residual work in
  `<other path>` that this report didn't see. Re-run from the wider
  root, or pass the path explicitly."

What you must NOT do at 100%:

- Show the bar at 100% AND describe new lemma-proving as "active work"
  in the same report. That is internally inconsistent. Either the bar
  is wrong (rare — investigate where the missed sorries are) or the
  active-work framing is wrong (rephrase as refactor / audit / etc.).

## Phase 6 — Render the report

The whole report is markdown. Length follows content: brief if the proof
is essentially trivial, longer when there's structural complexity to
unpack. Aim for the report to be a self-contained briefing for a
mathematician parachuting in cold.

```markdown
# Project Status — <Project Title>

## Overall goal

<One paragraph in mathematical English describing what this project is
trying to prove. Pull from plan.md and the top-level theorems. Define any
non-standard notions. Don't paste Lean code here.>

## Currently working on

### <math name in 4-10 words of English>

```lean
<the Lean signature, verbatim>
```

**What this asserts.** <2-4 sentences in mathematical English. Be precise.
Define every non-standard term the first time it appears
(e.g. "the Eisenstein series E_k(τ) = ∑_{(c,d) ≠ 0} (cτ + d)^(−k)",
not "eisensteinSeries"). Use Unicode mathematical symbols directly — no LaTeX.>

**Setup** (only when needed: ambient hypotheses, parameters, structures).
<List what the variables are and what context they live in. Skip this
subsection if the signature alone is self-evident.>

**Where the proof currently sits.** <One or two paragraphs. Read the
body. Translate every structural step into mathematics:

- For each auxiliary `have` the worker has established, state the
  mathematical claim it makes. If it's parametric ("for every ε > 0
  there is N with …"), spell out the universal claim. Mark whether
  the `have` was needed only for the current attempt or is a genuine
  intermediate result.
- For each `obtain`, `let`, or `use`, name the witness mathematically.
  "The worker fixes M = π²/6 as the dominant bound, since
  ∑ₙ n⁻² = π²/6" — not "obtains a witness M".
- If the goal has been refined into sub-goals (`refine ⟨?_, ?_, ?_⟩`,
  `constructor`, `cases`), list every sub-goal mathematically and
  mark which are discharged and which remain.
- When the proof leans on a project-internal lemma, gloss what that
  lemma says in math — don't just name it. "This step uses the
  absolute-summability lemma (which states ∑ₙ n^(−k) < ∞ for k ≥ 4)".

If the body is essentially `sorry` with no structural progress, say
"The declaration is stated but the proof has not been started" and stop.

>

**What discharging the sorry would establish.** <1-2 sentences. The
local goal at the sorry, in mathematical English. Be concrete — say
exactly what would be proved next, not "the next step".>

**How this connects to the overall goal.** <Trace the chain explicitly,
in math names. "This lemma states X. It feeds Y (the q-expansion
principle), which combines with Z (absolute convergence) to give the
project's main result W." Two or three sentences when the chain is
long; one sentence when short.>

(repeat the block for each declaration the worker is currently on; usually
one or two)

## Blocked  (only if any)

### <math name>

```lean
<the Lean signature, verbatim>
```

**What this asserts.** <Same as above, 2-4 sentences in math English.>

**Where the proof got stuck.** <One paragraph. Same level of detail as
"Where the proof currently sits": translate structural steps, name
witnesses, list sub-goals. The reader needs to see the partial proof
the worker built, not just "couldn't finish".>

**What is mathematically missing.** <2-4 sentences. State the gap
precisely: a hypothesis is too strong; a mathlib lemma has the wrong
shape; the proof strategy hits a step requiring a fact the project
doesn't have. Frame it as a mathematical question, not a Lean question.>

**What would help.** <2-4 concrete bullets. Alternative proof strategy,
hypothesis relaxation, literature pointer, suggestion to decompose the
step. Mathematical guidance, not encouragement.>

## Progress

[<20-cell bar>] <percent>% — <done>/<total> declarations sorry-free, <has_sorry> with sorry
(See Phase 5 for the binding format. Every field above is mandatory —
the brackets, the percentage, both counts, the word "declarations".)

<One or two sentences placing the current frontier in the project's arc.
"The basic API is in place; the main holomorphy result is the current
frontier; the q-expansion principle is blocked on a missing Fourier
expansion lemma." — not "lots of work left".>
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
   ("rewrite using", "applies", "uses simp_rw", "obtains a witness",
   "splits into cases") in prose — translate to mathematics.

2. **Self-contained.** A reader who has not seen the code, who cannot open
   any file, must understand the state of play from the report alone.
   This is the binding principle. If you find yourself writing a sentence
   the cold reader couldn't decode without context, expand it: define the
   notion, state the witness, spell out the parametric claim.

3. **Translate every structural move.** Every `have`, `obtain`, `refine`,
   `let`, `use`, `cases` in the proof body becomes mathematics in the
   report. Never paraphrase as "the worker obtains a witness" or "splits
   into cases" — name the witness, list the cases. Parametric `have`s
   become explicit universal claims.

4. **Don't fabricate.** If a body is just `sorry`, say "the declaration is
   stated but the proof has not been started" and move on. Don't invent
   strategies, witnesses, or sub-goals the code doesn't contain. Don't
   invent a project goal richer than what's in `plan.md` plus the
   top-level signatures.

5. **Unicode math, not LaTeX.** The chat is shown in a terminal; LaTeX
   delimiters render as literal source (`$\mathbb{R}$` shows as
   `$\mathbb{R}$`, not as ℝ) and that's hard to read. Use Unicode math
   characters directly: ℝ ℂ ℕ ℤ ℚ ℍ τ ε δ π η ω σ α β γ Σ Π ∫ ∂ ∇ ∀ ∃ ∈
   ∉ ⊂ ⊆ ⊇ ∪ ∩ ∅ ≤ ≥ ≠ ≈ → ↔ ⇒ ∞ ⌊⌋ ⌈⌉. For exponents, prefer Unicode
   superscripts when natural (n², x³, ⁻¹) and fall back to caret
   notation when not (n^k, (cτ+d)^(−k)). Same for subscripts: ₀…₉ ₊ ₋
   when they exist, underscore notation otherwise. **Do not use any
   LaTeX delimiters (`$...$`, `\(...\)`, `\[...\]`) or commands
   (`\sum`, `\mathbb`, `\frac`, `\tau`, etc.).**

6. **No file paths in the rendered output.** The mathematician doesn't
   read `.lean` files. The agent reads them — but doesn't display the paths.

7. **Read-only.** No edits. No `lake build`. No mathlib search. The agent
   reads files with the `Read` tool, walks the project with `Bash` (for
   `find` / `grep`-style discovery if useful), and that's it.

8. **Length follows content.** A near-trivial proof gets two sentences. A
   proof with sub-goal decomposition, parametric intermediate results, or
   chosen witnesses gets a paragraph or two. Don't pad; don't be terse
   for terseness's sake.

## Worked example: terse vs thorough

Suppose the worker is on a lemma whose body looks like:

```lean
theorem eisensteinSeries_holomorphic (k : ℕ) (hk : 4 ≤ k) :
    Holomorphic (eisensteinSeries k) := by
  obtain ⟨M, hM_pos, hM_bound⟩ := exists_dominant_bound hk
  have h_summable : Summable (fun n : ℕ => M / (n : ℝ)^k) := by
    exact summable_const_div_pow_of_lt hk hM_pos
  have h_termwise : ∀ n, Holomorphic (fun τ => term n τ) := termwise_holomorphic
  refine holomorphic_of_uniform_limit ?_ ?_
  · exact h_summable
  · sorry
```

**Terse (don't):**

> The worker has shown a dominant bound exists and is summable, and that
> each term is holomorphic. The remaining sorry needs uniform convergence.

This tells the cold reader nothing concrete. They cannot guess what M is,
what the parametric `h_termwise` actually says, what the sub-goal split is.

**Thorough (do):**

> The proof reduces holomorphy of the series to two ingredients via
> `holomorphic_of_uniform_limit`, which says: a uniform limit of
> holomorphic functions is holomorphic provided the convergence is
> dominated by a summable bound.
>
> The worker has chosen M > 0 from the auxiliary lemma
> `exists_dominant_bound`; concretely, M depends only on k and dominates
> |(cτ + d)^(−k)| uniformly on the upper half-plane ℍ. The auxiliary
> fact ∑ₙ M / n^k < ∞ for k ≥ 4 has been established (one of the two
> ingredients). Termwise holomorphy of each (cτ + d)^(−k) has also been
> established via the parametric lemma `termwise_holomorphic`, which
> asserts that for every fixed (c, d) ≠ 0 the map τ ↦ (cτ + d)^(−k) is
> holomorphic on ℍ.
>
> The goal has been split into two sub-goals: (a) summability of the
> dominant series — discharged using `h_summable`; (b) uniform bound of
> the series partial sums by the dominant series — outstanding.
> Sub-goal (b) is the remaining sorry.
>
> **What discharging the sorry would establish.** A pointwise bound
> |E_k(τ) − S_N(τ)| ≤ ∑_{n > N} M / n^k holding uniformly for τ in any
> compact subset of ℍ, where S_N is the N-th partial sum.

Notice: every name from the body has been translated to a mathematical
claim. The witness M is characterised. The parametric `termwise_holomorphic`
is spelled out as a universal claim. The two sub-goals from `refine` are
listed and marked. All math symbols are Unicode — no LaTeX.

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
