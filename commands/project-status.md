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

## Phase 5 — Compute progress (three tiers)

A flat declaration count understates mathematical distance to the goal:
thousands of supporting lemmas weight the same as the actual frontier,
so the bar pegs at 100% while the main result is still conditional.
Compute three views; report all three in Phase 6.

### Tier 1 — Code-level coverage (coarse)

The flat count.

- `done` = declarations whose body contains no `sorry`
- `has_sorry` = declarations whose body contains `sorry`
- `total = done + has_sorry`
- `percent = round(100 × done / total)` (`total = 0` → `percent = 0`)

This includes scratch chains and orthogonal work. Useful as a sanity
check, not as the main metric.

### Tier 2 — Main-goal chain coverage

First identify the project's **main goal(s)** — the user-facing theorem(s)
the project exists to prove. Sources, in order of priority:

1. `plan.md` names a specific declaration → use it.
2. The top-level public theorems / lemmas (kind = `theorem`/`lemma`,
   not `private`, not used by any other declaration). If there are
   one or two such, those are the main goal(s).
3. If there's a clear naming pattern in the user-facing theorems (e.g.
   `fermatLastTheoremFor_thirtyseven_*`), report each as a main goal.
4. If genuinely unclear, say so and skip Tier 2.

Compute the **dependency closure** of each main goal: every declaration
the main goal transitively uses (follow `depends_on` chains). Then:

- `main_done` = sorry-free declarations in the closure
- `main_total` = total declarations in the closure
- `main_percent = round(100 × main_done / main_total)`

Crucially, this **excludes** parallel chains the main goal doesn't use
(scratch, orthogonal explorations, alternate-route experiments). On a
project with `6709/6714` Tier 1 and 5 sorries in a parallel scratch
chain, Tier 2 is `100%` if the main chain is clean — and the report
should say so plainly, not bury the user in an unrelated bar.

### Tier 3 — Conditional → unconditional progress (deepest metric)

Read each main goal's **signature**. List every hypothesis. Classify:

- **Ambient** — typeclass instances (`[CommMonoid α]`), index variables
  (`(n : ℕ)`, `(p : ℕ)`), standard mathlib propositions (`p.Prime`,
  `0 < n`, `Fintype α`). These are inputs to the statement, not
  assumptions to discharge.
- **Parametric assumption** — a hypothesis whose type names a
  project-defined `Prop` (or `def X : Prop := …` somewhere in the
  project). Examples: `(h : Vandiver37PlusCoprime)`,
  `(h : EigenspaceCondition p k)`. These are conditional inputs.

Detection rule: a hypothesis is parametric iff its type refers (by name)
to a declaration in the project's own decl set. Anything resolving to
mathlib or stdlib only is ambient.

For each parametric assumption, check whether the project also contains
a sorry-free theorem of the same type — that is the **discharge**. If
present, the assumption is `discharged`. If not, it is `still
parametric`.

The project becomes unconditional when every parametric assumption of
every main goal is discharged. Report:

- `parametric_count` = total parametric hypotheses across all main goals
- `discharged_count` = how many of those have a sorry-free discharge
- `still_parametric` = `parametric_count − discharged_count`

If a main goal has zero parametric assumptions, it is already
unconditional — say so explicitly.

### Bar-rendering rules (apply to all tiers)

Each bar follows the same template. Do not improvise width, characters,
or fields.

```
[<20-cell bar>] <percent>% — <tier-specific description>
```

- The brackets `[` and `]` are mandatory.
- The bar is exactly 20 cells. Filled cells = `round(percent / 5)`.
  Empty cells = `20 − filled`.
- Use `█` for filled and `░` for empty. ASCII fallback only if you have
  evidence the user's terminal mangles those characters: `#` for filled,
  `-` for empty, still 20-cell. Do not use other characters (no `▰`, no
  `▱`, no `=`, no `■`).
- The percentage is mandatory even at 0% or 100%. Plain integer + `%`,
  no decimals.

Tier-specific descriptions:

```
Tier 1: 38% — 12/32 declarations sorry-free, 20 with sorry
Tier 2: 75% — 18/24 declarations on the main-goal closure are sorry-free
Tier 3: 33% — 1/3 parametric assumptions discharged
```

Worked examples for the bar itself (any tier):

```
0%    [░░░░░░░░░░░░░░░░░░░░] 0% — …
25%   [█████░░░░░░░░░░░░░░░] 25% — …
38%   [████████░░░░░░░░░░░░] 38% — …
50%   [██████████░░░░░░░░░░] 50% — …
75%   [███████████████░░░░░] 75% — …
100%  [████████████████████] 100% — …
```

### The 100% case (binding, tier-aware)

It is **expected and normal** for Tier 1 to be at or near 100% while
Tiers 2 and 3 are not. That gap is the whole point of the three-tier
view: a project can have 6709/6714 declarations sorry-free and still
be far from its mathematical goal.

The binding rule applies to **Tier 2** (main-goal chain coverage) and
**Tier 3** (parametric inputs):

- If Tier 2 is at 100%, every declaration the main goal depends on is
  sorry-free. New lemma-proving cannot legitimately be the "active
  work" *on the main chain*. Active work is either: discharging
  parametric assumptions (Tier 3), an off-chain refactor / axiom
  audit, or work in a parallel scratch chain — say which.
- If Tier 3 is at 100%, the project's main goal is unconditional. Say
  so plainly. If the user is still framing active work, it is either
  optimisation/refactoring or a new goal.

What you must NOT do:

- Show Tier 1 at 100% and quietly imply the project is done. The reader
  needs Tiers 2 and 3 to know whether the *main result* is unconditional.
- Hide a parallel scratch chain inside the Tier 1 number without
  surfacing it. If the 5 outstanding sorries are off-chain, name the
  chain ("the Furtwängler residue-symbol scratch under `Reflection.…`")
  and say it is not on the main goal's import path.

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

### Code-level (all declarations)
[<20-cell bar>] <percent>% — <done>/<total> declarations sorry-free, <has_sorry> with sorry
(Coarse: includes scratch chains and parallel/orthogonal work. <one-line note about where the with-sorry declarations live, e.g. "the 5 outstanding are in the Furtwängler residue-symbol scratch chain, off the main import path".>)

### Main-goal chain
The main goal is **<math name>** (`<lean_name>`).
[<20-cell bar>] <main_percent>% — <main_done>/<main_total> declarations on the main-goal closure are sorry-free
(<one-line note: which chain is excluded, e.g. "Excludes the Furtwängler scratch and the parallel Vandiver-IV exploration.">)

### Distance to unconditional goal
<If the main goal has parametric assumptions:>
The main goal is currently conditional on <N> parametric hypothesis(es):
[<20-cell bar>] <tier3_percent>% — <discharged>/<N> assumptions discharged

- 🚧 `<hypothesis_name>` — <math description in 1-2 sentences>. Still parametric.
- ✅ `<hypothesis_name>` — <math description>. Discharged via `<theorem_name>`.
- ...

<If parametric_count = discharged_count = 0:>
The main goal is unconditional — no parametric assumptions in its
signature. ✅

<One paragraph in mathematical English placing the current frontier in
the project's arc. State which chain is closed, which assumption is the
next to discharge, and what mathematical move is needed. Example:

"The main FLT37 chain is sorry-free; the project becomes unconditional
once the Vandiver37PlusCoprime hypothesis is discharged (currently the
sole remaining parametric input). The route is the rank-one Pollaczek
specialisation: with the projector-compatibility lemmas just landed,
the chain to discharging Vandiver37PlusCoprime — eigenspace
surjectivity → Nakayama-rank-one → atomic rank-one at Λ = ℤ_37 → Kučera
→ Cor 8.19 contrapositive — is mechanical from existing
infrastructure."
>

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
