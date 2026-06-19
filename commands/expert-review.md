---
name: expert-review
description: Produce a self-contained mathematical briefing (no Lean, no file paths) for an external reviewer with no repo access — goals, plan, status, blockers, references, numbered questions
---

# /expert-review — Briefing for an External Mathematical Reviewer

Produce a single, self-contained mathematical document describing where the project is,
what we're trying to do, what's done, what's stuck, and what we'd like the reviewer to
weigh in on. Written for a mathematician who has **no access** to the repo, the Lean code,
or the ticket board — only this document.

The output is `REVIEW_BRIEF.md` in the project root.

The hard rules:
- **No Lean code** unless a specific definition is mathematically essential and there's no
  natural-language equivalent. Even then, render it like a mathematical statement, not
  a piece of source code (no tactic blocks, no `:= by`, no syntax peculiarities).
- **No file paths, no line numbers.** The reviewer sees mathematics, not project metadata.
  Refer to "the main theorem" and "Lemma 3.4" — never to `Mathlib/Foo/Bar.lean:123`.
- **Self-contained**: every notation introduced is defined; every cited result is stated
  (or has its statement faithfully summarised); every reference has a full citation.
- **Detailed.** A reviewer should be able to read this in isolation and give substantive
  guidance. Err on the side of more detail, not less.

What the brief **may** include (the user has explicitly allowed this):
- **Ticket system details and ticket names.** If the project uses a ticket board (e.g. via
  `/develop`), describe its shape ("we have N tickets across these mathematical sub-goals")
  and use ticket names where they're mathematically meaningful (`valenceFormula_main`,
  `q_expansion_principle`). They're useful as a structural device for the "In progress" /
  "Targets" sections — the reviewer doesn't need to *open* a ticket, but referring to one by
  name lets the user follow the brief back to their work board afterwards. Drop opaque
  ticket IDs (numeric or hash-style); keep mathematical names.

## Usage

The skill has two modes:

```
# Mode 1 — produce a brief and stop, waiting for the reviewer to reply
/expert-review                       # Brief covering the whole project
/expert-review <topic_or_subdir>     # Brief restricted to one mathematical topic / subtree
/expert-review --update              # Refresh the existing brief without re-asking context

# Mode 2 — integrate the reviewer's reply (run after they answer)
/expert-review --reply                       # Will prompt you to paste the reply
/expert-review --reply <path/to/reply.md>    # Reply lives in a file
```

When you re-invoke `/expert-review` with a brief already on disk and no `--reply` flag, the
skill asks whether you want to start a fresh brief (Mode 1) or you have a reply to integrate
(Mode 2).

---

## Phases

Mode 1 (producing the brief) runs Phases 1–9. Mode 2 (processing the reply) runs Phases 10–13.

```
# Mode 1 — produce the brief, then wait
PHASE 1   CONTEXT       ask the user 4–6 questions to scope the brief
PHASE 2   GATHER        read everything in the repo (code, READMEs, commits, tickets, comments)
PHASE 3   EXTRACT       pull definitions, theorems, dependencies; translate Lean → math English
PHASE 4   RECONSTRUCT   goals, plan, references, status from project artifacts
PHASE 5   STUCK         identify sorries, axioms, TODOs, blockers, open mathematical questions
PHASE 6   DRAFT         write the brief
PHASE 7   USER REVIEW   show the draft, refine (especially the Questions section)
PHASE 8   FINALISE      polish, save brief + state snapshot, print summary
PHASE 9   STOP — DELIVER  tell user to send the brief; STOP and wait for them to return with a reply

# Mode 2 — integrate the reply (run when the user comes back with the reviewer's response)
PHASE 10  INTAKE        load saved state, read the reviewer's reply
PHASE 11  INTERPRET     map reply onto questions; surface advice, concerns, new directions
PHASE 12  PROPOSE       propose ticket / work-order changes; do NOT apply yet
PHASE 13  APPROVE + APPLY  wait for user OK, then update tickets.md, save reply for posterity
```

---

## PHASE 1 — Context (ask user first; everything else depends on the answers)

Don't start gathering until you have these answers. Ask all questions in one message so the
user can answer them together. Use the `AskUserQuestion` tool when available.

1. **Audience.** Who's the reviewer? (Specific person? An advisor? "A senior expert in
   modular forms"? "Anyone qualified in p-adic Hodge theory"?) Their background shapes how
   much context to include.
2. **Goal of the brief.** Why are we sending this? Pick the one that fits best:
   - Strategic guidance ("does the overall approach make sense?")
   - Specific blocker ("we're stuck on X — how would you proceed?")
   - Soundness check ("are these definitions the right ones?")
   - Reference recommendation ("what's the right paper for Y?")
   - Pre-submission read ("anything obviously wrong before we submit?")
3. **Scope.** Whole project? One subtopic? A specific result?
4. **Burning questions.** What specific questions does the user already want answered? Get
   the user's actual list — don't synthesise, don't paraphrase. We'll add agent-surfaced
   questions in Phase 5.
5. **Notation preferences.** Any conventions the reviewer expects? (E.g.,
   "use `q = e^{2πi z}` written `𝕢 z`"; "use Tate's convention for L-functions".)
6. **Length budget.** Cap or open-ended? Default: as long as needed.

Print the answers back so the user can correct them, then proceed.

---

## PHASE 2 — Gather (read the repo)

Use the `Explore` subagent for breadth, the `Read` tool for the specific files you need.

### 2a. Project surface

- `README.md`, `README.txt`, `*.md` in the root
- Top-level docstrings in the main files (the `/-! # ... -/` blocks)
- `CLAUDE.md` if present (often has the project's own explanation of itself)
- `lakefile.toml` / `lakefile.lean` (project name, dependencies)

### 2b. Mathematical content

Find every public `def`, `lemma`, `theorem`, `structure`, `class`, `instance` in the project
(excluding `.lake/`, `build/`, mathlib itself).

```bash
find . -name "*.lean" -not -path "./.lake/*" -not -path "./build/*" | sort
```

For each file, read it — the **proofs**, not just the signatures. The mathematical argument
matters; the tactics do not.

### 2c. Plan and status artifacts

- **Ticket system.** If the project uses `/develop`, tickets live in
  `.mathlib-quality/tickets/` (or similar). For each, capture: the **ticket name**
  (mathematically meaningful — keep), the **status** (open/in-progress/blocked/done), the
  **mathematical statement** the ticket tracks, the **dependency graph** (which tickets
  block which), and any **notes** the user wrote on the ticket. We'll use the names and
  the dependency structure as a structural device in §6 / §7 of the brief; the user has
  explicitly allowed this. Discard opaque numeric/hash IDs.
- `PROJECT_OVERVIEW.md` if `/overview` was run — uses-from-project info already structured
- Recent `git log` (last 30 commits): what's been worked on lately
- Open issues / PRs (via `gh`) on the project repo — describes ongoing concerns
- Any `TODO`, `FIXME`, `NOTE` comments in `.lean` files

### 2d. References and citations

Sources of citation info to harvest:

- Module docstrings (`/-! ... ## References ... -/`) — primary source
- Comments above key definitions (mathematicians often note "following [Author24, §5]")
- Project README references / bibliography
- `references/` or `docs/` folders
- Commit messages mentioning papers
- Existing user-supplied PDFs / `.bib` in the repo

Capture as much bibliographic data as the project provides. If the reference is incomplete
("Section 3 of Diamond–Shurman"), note that and ask the user in Phase 7.

### 2e. Recent activity log

```bash
git log --since="2 months ago" --oneline --no-merges
```

Plus:
- `lake build` / CI status if available
- Recent tickets that have been closed (what's been completed lately)
- Recent tickets that are open or in-progress (what we're working on now)

---

## PHASE 3 — Extract (Lean → mathematics)

For each public declaration the reviewer needs to see, produce a mathematical rendering.

### Translation rules

| Lean → Math |
|---|
| `theorem foo (h : P) : Q` → "**Theorem 3.4.** Suppose $P$. Then $Q$." |
| `def fooBar : T := value` → "**Definition.** $\mathrm{fooBar}$ is defined to be $\dots$" |
| `IsCuspForm` → "is a cusp form" |
| `ModularForm Γ k` → "$M_k(\Gamma)$" or "modular forms of weight $k$ on $\Gamma$" |
| Variable conventions (`G`, `R`, `K`, `𝕜`) → use the convention the user specified in 1.5 |
| `:= by simp [foo, bar]` → omit; the reviewer doesn't need to see the proof script |
| `private lemma` → omit unless its statement is mathematically interesting |
| Ticket name like `valence-formula-main` → keep as a structural label in §6 / §7 (the user has allowed this); drop opaque numeric IDs |

### What to keep, what to drop

| Keep | Drop |
|---|---|
| Statements of public theorems | Tactic proofs |
| Statements of definitions (in math notation) | Lean type-class machinery (`[FunLike F α β]`, `[Fact …]`) unless mathematically essential |
| Hypotheses in mathematical English | `[DecidableEq α]`-style constraints |
| Mathematical structure (chapters, sections) | File structure |
| Cross-references between mathematical results | File-path cross-references |
| Custom notation (with explicit definition) | Lean's metavariable / universe machinery |

### Statements

Render every public theorem the reviewer needs to see in the form:

```
**Theorem (informal-name).** *Let $X$, $Y$, $Z$ be as above. Suppose $H_1$, $H_2$. Then
$C$.*
```

Where the *informal name* is descriptive (e.g., "valence formula for level-1 modular forms"),
not a code identifier (`valenceFormula_levelOne_aux₁`).

If a result has a long signature in Lean, that's a sign the mathematical content needs
unpacking. State it the way a textbook would.

### Proof sketches

For *key* established results (the main theorems, not every intermediate lemma), include a
**proof sketch** of 3–10 lines describing the mathematical argument:

> *Sketch.* Apply Theorem 2.1 with $f$ the dominant function on $K$. The bound on
> $\|f\|$ comes from compactness (Heine–Borel); pointwise convergence is by the
> assumed locally-uniform convergence; integrability is by dominated convergence.
> Take the limit and identify the integrand. ∎

These sketches let the reviewer judge correctness without reading proofs.

For intermediate lemmas that aren't of intrinsic interest, just state them and note
"established by routine compactness / direct computation / etc."

---

## PHASE 4 — Reconstruct goals, plan, references

### 4a. Goals (top-level objective)

Read everything from Phase 2 and write 1–3 sentences describing the project's goal in
mathematical terms. The user gave their version in 1.2 — reconcile what the user said with
what the artifacts show. If they disagree, that's its own item for the questions section.

### 4b. Plan

The user's plan, as the artifacts reveal it. Read tickets and recent commits in
chronological order; reconstruct the strategy:

> The strategy is to: (1) establish the analytic framework on the upper half-plane via X;
> (2) transfer to the algebraic side via the $q$-expansion principle; (3) deduce the main
> theorem from a finite-dimensionality argument.

If the project doesn't have explicit tickets, infer the plan from the file/section
structure of the public results. Be honest about how much you're inferring vs. quoting.

### 4c. References

For every citation source from 2d, produce a full bibliographic entry:

> [Diamond–Shurman 2005] Fred Diamond and Jerry Shurman. *A First Course in Modular
> Forms*. Graduate Texts in Mathematics 228. Springer, 2005.
>
> [Loeffler–Zerbes 2014] David Loeffler and Sarah Livia Zerbes. "Iwasawa theory and
> p-adic L-functions over $\mathbb{Z}_p^2$-extensions." *Int. J. Number Theory* 10
> (2014), no. 8, 2045–2095.

Group references by topic if it helps. If a reference is incomplete in the project,
mark it `[needs full citation: …]` and ask in Phase 7.

### 4d. State of the art

If the project artifacts mention what's known in the literature ("the unrestricted version
is open"; "the case $k = 4$ was done by [X]"), include that — the reviewer needs to know
where this sits in the wider field.

---

## PHASE 5 — Stuck points (the most important section to get right)

This is what the user actually wants the reviewer's help on. Be specific.

### 5a. Sorries / axioms

```bash
grep -rn "sorry" --include="*.lean" .
grep -rn "axiom " --include="*.lean" .
```

Each `sorry` is a place we don't yet have a proof. For each, render mathematically:

> **Open lemma 1.** *Let $f \in M_k(\Gamma_1(N))$. Then the $q$-expansion of $f$ has
> integral coefficients if and only if $f$ takes values in a number field.*
> Status: `sorry`. We've reduced the problem to showing X but the descent step in §3.2
> of [Author Y] doesn't directly apply because of Z.

Each axiom we've added (not those from mathlib core) is a place we've declared something
unproven. Same treatment.

### 5b. TODOs and FIXMEs

```bash
grep -rn "TODO\|FIXME\|XXX" --include="*.lean" --include="*.md" .
```

Filter out the ones that are pure code-quality (inline a `have`, rename a variable). Keep
the ones that flag mathematical work ("TODO: prove the surjectivity here", "FIXME: this
might require a stronger hypothesis").

### 5c. Failed attempts

Read the recent commit history for `WIP`, `try`, `revert`, `attempt`, `back out`. If the
project has comments like `-- this approach didn't work because…` or `/- ATTEMPTED:
…`, surface those.

### 5d. Implicit blockers

Even when no `sorry` is present, sometimes the project is stuck because:

- A result is proven but in less generality than aimed for ("we need this for all
  $\Gamma$, but only have it for $\mathrm{SL}_2(\mathbb{Z})$").
- Quantitative bounds aren't tight enough.
- The proof goes through but feels wrong / overly long, suggesting the mathematics isn't
  the right framing.
- Mathlib doesn't have a lemma we expected, and we don't know whether to upstream it,
  work around, or wait.

These are valuable for the reviewer to weigh in on. Surface them explicitly.

---

## PHASE 6 — Draft `REVIEW_BRIEF.md`

Use the template below. Adapt the section structure to the project — e.g., a project on a
single theorem will have one "Main result" section; a project on a body of results will
have several.

### Template

```markdown
# Review brief — <Project name>

*Prepared <YYYY-MM-DD> for <reviewer audience>. Self-contained: no repo access required.*

## 1. Goal

<1–3 sentences in mathematical English. What we're trying to prove / construct / develop.>

> Example: "We aim to prove the valence formula for the action of $\mathrm{SL}_2(\mathbb{Z})$
> on weight-$k$ holomorphic modular forms, in the form $\sum_{p} \mathrm{ord}_p(f) =
> k/12$, and apply it to deduce the dimension formulas $\dim M_k = \lfloor k/12 \rfloor +
> 1 - \delta_{k \equiv 2 \,(\mathrm{mod}\, 12)}$ for $k$ even, $k \geq 4$."

## 2. Background and references

### 2.1. Setting

<What objects are we working with? Conventions on notation, sign, normalisation. Anything
the reviewer needs to fix in their head before reading on.>

### 2.2. References

<Full bibliographic citations. If we cite [DS05, §1.4], the reviewer should be able to
find it without us telling them where. Group by topic if it helps.>

### 2.3. State of the art

<Where does this sit in the literature? Has the result been proved before? In what
generality?>

## 3. Strategy

<The plan. 3–7 sentences describing the mathematical approach. If there are intermediate
milestones, list them.>

## 4. Definitions

<Self-contained statements of every custom definition the reviewer needs. Use math
notation. If a definition is "the same as [DS05, §3.1]", say so AND restate it.>

> Example:
> **Definition 4.1.** A *cusp form of weight $k$ on $\Gamma$* is a holomorphic modular
> form $f \in M_k(\Gamma)$ satisfying $\lim_{\mathrm{Im}(z) \to \infty} f(z) = 0$, and
> similarly at every cusp of $\Gamma$.

## 5. Established results

<Statements of every theorem we've proved that the reviewer should know about. Order
mathematically (foundations first), not chronologically.>

> **Theorem 5.1 (informal name).** *Statement.*
>
> *Sketch.* <3–10 line proof sketch in math English, naming the key idea and the
> auxiliary results used.> ∎

For each established theorem:
- Name it informally (descriptive, like a textbook).
- Statement in math notation.
- Sketch unless it's truly routine.
- If it's a black-box use of [Reference X, Theorem Y], say so.

## 6. In progress

<Theorems whose statement is fixed but the proof isn't yet complete. For each: what's the
current status, what subgoals remain, what's tried, what's working. If the project tracks
work via tickets, the ticket name can be used as the section header.>

> **Working on: dimension formula in even weights $k \geq 4$** (ticket `dim-Mk-even`).
> Status: have the inequality $\dim M_k \leq \lfloor k/12 \rfloor + 1$ via the valence
> formula. Reverse inequality reduces to constructing $\lfloor k/12 \rfloor + 1$
> linearly independent forms — currently using Eisenstein series $E_4$, $E_6$ and the
> discriminant $\Delta$. Stuck on the case $k \equiv 2 \pmod{12}$ where the dimension
> drops by 1; the construction needs to detect this.
>
> Depends on: `valence-formula-SL2Z` (done) and `Eisenstein-q-expansion` (done).
> Blocks: `dimension-formula-Gamma-N` (not yet attempted).

## 7. Targets (not yet attempted)

<Theorems we want to prove eventually but haven't started. Include them so the reviewer
can comment on whether the chosen statement is the right one. Group by ticket name when
useful.>

## 7a. Ticket board (optional)

<If the user wants the reviewer to see the project structure, include a compact view of
the ticket board. Format:

> | Ticket | Mathematical statement | Status | Depends on |
> |---|---|---|---|
> | `valence-formula-SL2Z` | $\sum_p \mathrm{ord}_p(f) = k/12$ for $f \in M_k$, $k$ even | done | – |
> | `Eisenstein-q-expansion` | $E_k(z) = 1 - \tfrac{2k}{B_k}\sum_{n\geq 1}\sigma_{k-1}(n)q^n$ | done | – |
> | `dim-Mk-even` | $\dim M_k = \lfloor k/12 \rfloor + 1 - \delta_{k\equiv 2}$ | in progress | `valence-formula-SL2Z`, `Eisenstein-q-expansion` |
> | `dimension-formula-Gamma-N` | analogous formula for $\Gamma_0(N)$, $\Gamma_1(N)$ | not started | `dim-Mk-even` |

Skip this subsection if the project doesn't have tickets, or if the user would rather
present only the mathematical content.>

## 8. Where we're stuck

<This section is the heart of the brief. Be specific. Each item should describe the
mathematical obstacle, what we've tried, and why it didn't work.>

> **Stuck point 8.1.** *The descent argument from $\Gamma_1(N)$ to $\Gamma_0(N)$.*
>
> The strategy is to exploit the determinant character to descend results from
> $\Gamma_1(N)$ to $\Gamma_0(N)$. We have the descent for the dimension formula (via
> the trace formula) but the analogous descent for the valence formula breaks because
> [specific reason]. We tried [approach 1] which gives the wrong answer at primes
> dividing $N$, and [approach 2] which requires a result on Hecke operators that we
> don't have.

## 9. Open mathematical questions for the reviewer

<Numbered, focused questions. The reviewer should be able to answer these with one
paragraph each. Mix:
 - questions the user asked to include (Phase 1.4)
 - questions surfaced during Phase 5
 - meta-questions about strategy>

> **Q1.** Does the splitting in §8.1 admit a descent that doesn't go through the trace
> formula? If so, what's the cleanest reference for it?
>
> **Q2.** Our normalisation of $E_2$ matches [DS05] but not [Zagier]. Will the reviewer
> have a preference? (Both work; the choice is propagated through about a dozen lemmas
> and we'd like to fix it before going further.)
>
> **Q3.** Is the level of generality in §4.2 — modular forms over an arbitrary
> arithmetic subgroup, $\mathrm{Fact}(\mathrm{IsCusp})$ at every cusp — the right one
> for downstream applications, or should we restrict to congruence subgroups now and
> generalise later?

## 10. Auxiliary technical results (appendix)

<Optional. Lemmas the reviewer doesn't need to read carefully, but might want to spot-check.
Include only the statement, not the proof.>

## 11. Document metadata

- Project name: <name>
- Brief generated: <YYYY-MM-DD>
- Length: <approximate page / word count>
- Build status at time of writing: <e.g., compiles cleanly; 3 sorries remaining>
- Recent commit context: <last commit date / summary of recent activity>
```

### Notation sanity-check before saving

Read the brief end-to-end. Ask:
- Is every notation defined before it's used? (Don't use $E_k$ in §3 if it's defined in §4.)
- Are there any Lean *syntax* tokens that leaked through? (`_aux`, `:=`, `by`, `theorem` as
  a keyword.) Replace with math. **Note:** mathematically meaningful camelCase ticket
  names like `valenceFormula_main` are allowed in the "In progress" / "Targets" sections —
  the goal is no Lean *syntax*, not no camelCase. Erase only the source-code residue.
- Are file paths anywhere? (Search for `.lean`, `Mathlib/`.) None should remain.
- Is every citation in §2.2 actually used in the body? (And vice versa.)
- Are the questions in §9 phrased as questions, not as statements?

---

## PHASE 7 — User review (refinement)

Print the draft (or its outline + first few sections) and ask the user three things:

1. **Goal alignment.** "Section 1 says X is the goal. Is that right?" — get a direct
   confirm/correct.
2. **Question wording.** "Section 9 has Qs 1–6. Are these phrased the way you want? Should
   I add or remove any?" — questions are the most user-specific part.
3. **Tone and detail level.** "Is this the right level of detail for the audience you have
   in mind?" — sometimes the user wants 2 pages, sometimes 20.

Iterate until the user is satisfied. Do NOT save `REVIEW_BRIEF.md` until they OK it.

---

## PHASE 8 — Finalise (save brief + state for Mode 2)

The brief is saved both as a convenient artifact in the project root **and** as part of a
dated session folder so Mode 2 can find it later.

### 8a. Save the brief

Save `REVIEW_BRIEF.md` to the project root.

Also save it to a dated session folder:

```
.mathlib-quality/expert-review/<YYYY-MM-DD>/brief.md
```

(use `<YYYY-MM-DD-N>` if a brief was already generated today, with `N` an incrementing index).

### 8b. Save state for Mode 2 (CRITICAL — Mode 2 depends on this)

Write `.mathlib-quality/expert-review/<YYYY-MM-DD>/state.md` with the following contents:

```markdown
# Expert-review session state

- Generated: <ISO timestamp>
- Audience: <answer from Phase 1.1>
- Goal of brief: <answer from Phase 1.2>
- Scope: <answer from Phase 1.3>
- Reply received: false
- Reply integrated: false

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | <text> |
| Q2 | <text> |
| ... |

## Ticket-board snapshot at brief time

<copy of `.mathlib-quality/tickets.md` if it exists, OR a summary if there's no ticket
system yet — list of open mathematical sub-goals as we understood them>

## Stuck points (from §8 of brief)

<numbered list, one line each, for cross-reference in Mode 2>

## Reference list (from §2.2 of brief)

<short cite tags, for cross-reference in Mode 2>
```

This file is the *only* persistent record of what we asked. When the reviewer comes back,
Mode 2 reads it to know what was asked and what the project state was at brief time.

### 8c. Print summary

```
## Review brief saved: REVIEW_BRIEF.md
                       .mathlib-quality/expert-review/2026-05-06/brief.md
   State saved:        .mathlib-quality/expert-review/2026-05-06/state.md

Sections:    11
Length:      ~6 pages (3,400 words)
Definitions: 12 (all stated in math notation)
Theorems established: 8 (7 with sketches, 1 cited as [DS05, Thm 3.5.1])
In progress: 2
Stuck points: 3
Questions for reviewer: 6
References: 9 with full citations

Self-containment check: ✓
- No file paths
- No Lean syntax
- All notation defined
- All citations used
```

If the user wants to edit the brief by hand, that's fine — but warn them: re-running
`/expert-review --update` regenerates from scratch and overwrites the dated copy too.

---

## PHASE 9 — Stop. Deliver. Wait for the reviewer.

Tell the user explicitly that we're waiting:

```
## Brief delivered. Waiting for reviewer.

Ready to send. Suggested delivery channels:
- Email — paste REVIEW_BRIEF.md into the body, or attach as .md / .pdf
- ChatGPT / Claude — paste as a system prompt or first turn
- In-person meeting — print as PDF
- Slack / Zulip — paste; the math notation is LaTeX, recipient can render

When the reviewer replies, return here and run:

    /expert-review --reply               # I'll prompt you to paste it
    /expert-review --reply <path>        # Or point me at a file

I'll keep the saved state in .mathlib-quality/expert-review/<date>/ until you come back —
no time limit, no need to keep this conversation open.
```

Then **stop**. Do not poll, do not auto-resume, do not do other work in this session under
the assumption a reply will arrive. The user comes back when they have the reply.

---

## PHASE 10 — Intake (Mode 2 entry point)

The user invoked `/expert-review --reply` (with or without a file path).

### 10a. Find the brief this reply is for

List `.mathlib-quality/expert-review/*/state.md`, sort by date descending. Pick the most
recent one whose `Reply received: false` is set.

If multiple are pending: ask the user which one this reply is for. Print a short menu:

```
There are 2 pending briefs:
  [1] 2026-04-22  audience: "mathlib reviewer"  goal: "specific blocker on descent argument"
  [2] 2026-05-06  audience: "advisor"            goal: "soundness check on definitions"
Which is this reply for? (1, 2, or `c` to cancel)
```

### 10b. Load the state

Read the chosen `state.md` so you have:
- The exact questions Q1..QN that were asked
- The ticket-board snapshot at brief time
- Stuck points and references

Read the corresponding `brief.md` too — you'll cross-reference reviewer comments back to
brief content.

### 10c. Read the reply

If `--reply <path>`: `Read` the file.

If `--reply` with no path: tell the user to paste the reply now. Wait for a single user
message containing the reply text. (If the reply is huge / multi-part, the user can drop
it into a file and re-invoke with `--reply <path>`.)

Save the reply verbatim to `.mathlib-quality/expert-review/<YYYY-MM-DD>/reply.md` (same
session folder as the brief). This is the canonical record.

### 10d. Reconcile state with current reality

Time has passed since the brief was generated. Before mapping the reply onto today's
project, do a quick re-scan:

- Has the ticket board changed? (Compare current `.mathlib-quality/tickets.md` to the
  snapshot in `state.md`.)
- Have any of the open lemmas in §8 of the brief been resolved? (Re-grep for `sorry` in
  the locations listed.)
- Are the references still the right ones, or has the user added new ones?

Note any drift in the working log. If drift is significant ("we've already solved Q4
since sending the brief"), surface that during interpretation — the reviewer's advice on
Q4 may now be irrelevant or partially obsolete.

---

## PHASE 11 — Interpret the reply

This is the careful read. Reviewers don't always answer in numbered order, sometimes give
opinions you didn't ask for, sometimes raise concerns, and occasionally reject a premise.

Build the **interpretation table**: one row per substantive reviewer point.

```
| # | Reviewer point (verbatim quote or paraphrase) | Maps to | Type | Confidence |
|---|----------------------------------------------|---------|------|------------|
| 1 | "Use the trace formula for descent — see [Hida 1985]" | Q1 (descent argument) | direct answer + new ref | high |
| 2 | "Your normalisation is fine; pick whichever you prefer" | Q2 (normalisation) | direct answer | high |
| 3 | "Don't generalise to non-congruence subgroups yet" | Q3 (generality) | direct answer; pushes back on user preference | high |
| 4 | "I'd be careful about Definition 4.2 — it's stronger than needed" | not in our questions | unprompted criticism | medium (need clarification) |
| 5 | "What about the case k = 1? Does your dimension formula even make sense?" | not in our questions | concern raised | high |
| 6 | "I assume you're aware of [Diamond–Im 2005]" | mentioned in passing | reference suggestion | low (just a name-drop) |
| 7 | (no comment)                                  | Q4, Q5, Q6 | UNANSWERED | — |
```

**Categorise the type:**
- *direct answer* — addresses one of our Qs explicitly
- *new ref* — points at a paper/book we should consult
- *concern raised* — flags something we hadn't worried about
- *pushes back on user preference* — disagrees with a choice the user made
- *unprompted criticism* — comment on something we didn't ask about
- *unprompted praise / agreement* — useful to record (validates an approach)
- *meta* — comment about the brief itself ("you should structure differently"; not a math point)
- *UNANSWERED* — Q from the brief that the reviewer didn't address; record this so we know what's still open

Rate **confidence** in your interpretation:
- *high* — clear direct mapping
- *medium* — your interpretation is plausible but the user should confirm
- *low* — you're guessing; flag for user clarification

Print the interpretation table before moving on.

---

## PHASE 12 — Propose ticket / work-order updates (do NOT apply)

For each reviewer point, work out the implication for the project. The categories:

| Implication | Concrete action |
|---|---|
| **Modify ticket** | Change scope, priority, hypothesis, blocker status, or notes on an existing ticket |
| **Add ticket** | Reviewer suggested new work; create a ticket |
| **Remove ticket** | Reviewer said the work isn't needed (e.g., cited a paper that already does it) |
| **Mark blocked** | Reviewer flagged a missing prerequisite |
| **Mark unblocked** | Reviewer answered a question that was holding a ticket up |
| **Reorder priority** | Reviewer said "do X before Y" |
| **No change (note only)** | Reviewer's point is informational; record it but no ticket touched |
| **Needs user judgement** | The implication isn't clear — only the user can decide |

Build the **proposed-changes table**:

```
| # | Reviewer point | Proposed action | Rationale |
|---|----------------|-----------------|-----------|
| 1 | Use trace formula for descent  | NEW ticket: `descent-via-trace-formula` (depends on existing `valence-formula-SL2Z`); mark `descent-direct-attempt` as superseded; add reference [Hida 1985] to bibliography | Reviewer gave a concrete strategy; old ad-hoc approach can be retired |
| 2 | Normalisation is fine          | No ticket change; record decision in project notes | Just settles the question |
| 3 | Don't generalise to non-congruence yet | MODIFY ticket `dimension-formula-general`: narrow scope to congruence subgroups only; add note explaining the deferral | Reviewer pushed back; user should confirm we're following the advice |
| 4 | Definition 4.2 might be stronger than needed | NEW ticket (LOW priority): `audit-definition-4.2-generality` — investigate weakening | Concern raised; not urgent but should be checked |
| 5 | What about k = 1?              | NEW ticket: `dimension-formula-k-equals-1` (BLOCKED on user input — do we even claim this case?) | Concern raised; user must scope this |
| 6 | [Diamond–Im 2005] reference    | No ticket; add reference to project bibliography | Just a name-drop |
| 7 | (UNANSWERED Qs Q4, Q5, Q6)     | No ticket; flag for the user — re-ask in next round? | Reviewer didn't address |
```

For each "Proposed action" that touches a ticket, draft the *exact* ticket-board edit
(in `develop.md`'s ticket format) so the user can review the diff:

```markdown
### [T042] descent-via-trace-formula
- **Status**: open
- **File**: <best guess from project structure>
- **Depends on**: <existing ticket name(s)>
- **Parallel**: <yes/no>
- **Description**: Implement descent argument via the trace formula, following
  [Hida 1985]. Replaces the ad-hoc descent in T030.
- **Reference**: Hida, "Galois representations into GL_2(Z_p[[X]]) attached to
  ordinary cusp forms", Invent. Math. 1985.
- **Reviewer guidance**: <reviewer login if known>, <date>: "Use the trace
  formula for descent — see [Hida 1985]"
```

Show the user the proposed-changes table AND every proposed ticket-board diff.

**Do not apply yet.**

---

## PHASE 13 — Approve + Apply

Wait for user input. Three possible responses:

- **Approve all** ("ok apply", "go ahead", "all good") — apply every proposed change.
- **Approve selectively** ("apply 1, 3, 4; skip 2; change 5 to ...") — apply only the
  approved subset, with any user-specified modifications.
- **Reject** ("don't apply any") — record the reply and decisions, but make no ticket
  edits. The reply file stays as evidence of the discussion.

### 13a. Apply

For each approved change:

- **Modify ticket**: edit the matching block in `.mathlib-quality/tickets.md`. Add a
  trailing note: `- **Reviewer guidance** (<reviewer>, <date>): <one-line summary>`.
- **Add ticket**: append to `.mathlib-quality/tickets.md` (or insert in dependency order).
- **Remove ticket**: don't delete; mark `Status: superseded` with a reason and a pointer
  to the replacement ticket. Tickets are an audit trail.
- **Update bibliography**: the project's reference list (wherever it lives) gets the new
  citation. If it lives in `references/`, add it there.

### 13b. Save the integration record

Write `.mathlib-quality/expert-review/<YYYY-MM-DD>/integration.md`:

```markdown
# Reply integration — <date>

Reply received from <reviewer> on <date>.
Brief: ../<YYYY-MM-DD>/brief.md
Reply: ../<YYYY-MM-DD>/reply.md

## Interpretation summary

<short version of Phase 11 table>

## Changes applied

- T042 added (`descent-via-trace-formula`)
- T030 marked `superseded`
- T015 modified: scope narrowed to congruence subgroups
- ...

## Changes rejected by user

- (none) or list

## Open questions remaining (the reviewer didn't answer these)

- Q4, Q5, Q6: ...

## Decisions recorded but not actioned

- Normalisation choice settled (per Q2): we keep the user's preferred form.
```

### 13c. Update the state file

Open `.mathlib-quality/expert-review/<YYYY-MM-DD>/state.md` and flip:

```
- Reply received: true (date: <ISO>)
- Reply integrated: true (date: <ISO>)
```

So Mode 2 doesn't pick this session up again.

### 13d. Final report

Print a short summary of what was applied and what's still open:

```
## /expert-review --reply applied

Reviewer: <login or name>
Reply length: ~800 words
Points addressed: 7
  - Direct answers: 3
  - New refs: 2
  - Concerns raised: 1
  - Unprompted: 1
Unanswered Qs: 3 (Q4, Q5, Q6 — consider re-asking next round)

Ticket changes applied:
  + 2 new tickets
  ~ 1 modified
  - 1 superseded

Open mathematical questions still on the table:
  - dimension formula in non-congruence case (deferred per reviewer)
  - k = 1 case (new — needs scoping)

Files updated:
  .mathlib-quality/tickets.md
  .mathlib-quality/expert-review/2026-05-06/state.md
  .mathlib-quality/expert-review/2026-05-06/integration.md
  references/bibliography.md  (or wherever)

Saved for posterity:
  .mathlib-quality/expert-review/2026-05-06/reply.md
```

If the user wants to start the next round (new questions surfaced from this reply, or
follow-up to the same reviewer), they invoke `/expert-review` again to produce a fresh
brief — the saved session folder gives full context for the conversation history.

---

## What this command does NOT do

- **Doesn't share code.** This is the point — the brief is for someone with no repo access.
  If the reviewer needs to see the code, they need access; the brief is for the
  mathematical conversation.
- **Doesn't prove anything.** Open lemmas stay open in the brief; we surface them, not
  fix them.
- **Doesn't push to anywhere.** Output is purely local.
- **Doesn't replace `/overview`.** `/overview` is for internal consolidation analysis (code
  level). `/expert-review` is for external mathematical discussion.

---

## Reference

- `/develop` — if the project uses ticket-based development, the tickets become primary
  source material for the plan and "in progress" sections.
- `/overview` — if `PROJECT_OVERVIEW.md` exists, it's a useful structured input for
  Phase 2's gathering, but the brief is *not* an overview — strip code-level content.
- `mcp__chatgpt-math__ask_chatgpt_math` — if available, can be used in Phase 7 to
  pre-screen the questions in §9 ("would a senior mathematician find these questions
  well-posed?").

---

## Final Step: Record Learnings

If during gathering you discover patterns that should be in the reference docs (mathlib
conventions the project uses, custom notation that should be standardised, etc.), record
them to `.mathlib-quality/learnings.jsonl`.

```json
{
  "id": "<short id>",
  "timestamp": "<ISO>",
  "command": "expert-review",
  "type": "<user_teaching|mathlib_discovery|other>",
  "before_code": "",
  "after_code": "",
  "pattern_tags": ["expert-review-finding"],
  "description": "<what was surfaced — e.g. 'project is following [Author24] but the convention X conflicts with mathlib's Y'>",
  "math_area": "<area>",
  "accepted": true,
  "source": "agent_suggestion",
  "context": {
    "project": "<name>"
  }
}
```

Keep it lightweight — only entries that are reusable beyond this one project.
