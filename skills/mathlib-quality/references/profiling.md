# Profiling Slow Declarations — Tools, Trace Reading, Root Causes

How to find out *why* a Lean declaration is slow and what actually fixes it. This is the
knowledge base behind `/buzz`; `/cleanup` (maxHeartbeats removal) and `/decompose-proof`
(structural splits) consume it too. The prime directive matches mathlib review policy
(`style-rules.md` § Performance & Profiling): **never raise `maxHeartbeats` — find the
issue and optimize the proof instead.** A limit raise doesn't fix slow code; it hides it
and taxes every future build and every downstream user.

## Measuring

### The sweep — one profiled compile per file (the headless "orange-bar watch")

In VS Code the Lean extension shows orange bars on lines still elaborating; slow
declarations are the ones whose bars linger. The headless equivalent is a single profiled
compile of the file (imports come from cache, so timings are per-declaration, not
per-import):

```bash
lake env lean -Dprofiler=true -Dprofiler.threshold=100 Path/To/File.lean
```

Every command whose elaboration exceeds the threshold (ms) prints timing messages anchored
at its source position — `elaboration took 1.2s` plus category lines such as `typeclass
inference`, `simp`, `tactic execution`, `type checking` (kernel replay), `compilation`,
`interpretation`. Map positions to declarations and you have the per-decl hot list from one
compile. Wall-clock varies run to run (±20% is normal); re-run once before trusting a
borderline number.

### Deterministic cross-check — heartbeats

Wall-clock depends on the machine; heartbeats don't. For a stable before/after comparison,
temporarily wrap the declaration (requires `import Mathlib.Util.CountHeartbeats`):

```lean
count_heartbeats in
theorem foo … := by …
```

It reports the heartbeats used. Default budget is 200 000 (`maxHeartbeats`); as a very rough
machine-dependent anchor, ~25k–100k heartbeats ≈ 1 second. Judge the *target* in wall-clock,
record *improvements* in heartbeats. Remove the wrapper when done — it is scaffolding.

### Per-declaration deep dive

- **`lean_profile_proof`** (MCP tool) — tactic-level hotspots for one theorem without
  editing the file. Try this first; it answers "which tactic line burns the time".
- **`set_option trace.profiler true in`** placed on the declaration — the full elaboration
  tree with per-node times, as info diagnostics (read via `lean_diagnostic_messages`).
  Set `set_option trace.profiler.threshold 50` too, or the tree is unreadably huge.
- **`set_option diagnostics true in`** — counters instead of times: which definitions got
  unfolded how many times, instance counts, congruence stats. The tool for "*what* is
  being done a million times" once you know *where* the time goes.
- Targeted traces, one hypothesis at a time (each makes output big — scope with `in`):
  - `set_option trace.Meta.synthInstance true in` — every instance search, with failures
  - `set_option trace.Meta.isDefEq true in` — unification/defeq checking
  - `set_option trace.Meta.Tactic.simp.rewrite true in` — every rewrite a `simp` call used
- Optional flamegraph for gnarly cases:
  `lake env lean -Dtrace.profiler=true -Dtrace.profiler.output=prof.json File.lean`, load
  `prof.json` in the Firefox Profiler UI.

All of these are **temporary scaffolding**. They are added to read, then removed. A file
that ships with `set_option profiler`/`trace.*`/`diagnostics` or a `count_heartbeats in`
wrapper has a leftover-scaffolding defect (`/pre-submit` and `/buzz`'s gates grep for it).

## Reading a `trace.profiler` tree

Times nest: each node's time includes its children. Walk down the **dominant child** at
every level until the time stops concentrating — the node where it lands names the culprit:

| Dominant node | Meaning |
|---------------|---------|
| `Meta.synthInstance` | typeclass instance search (cause 1) |
| `Meta.isDefEq` | unification / definitional-equality checking (cause 3) |
| `simp` / `Tactic.simp` | a simp call doing too much (cause 2) |
| a terminal-tactic node (`nlinarith`, `aesop`, `decide`, `omega`, `grind`) | heavy automation (cause 4) |
| `Elab.step` churn with many small retries | postponed metavariables / missing expected type (cause 5) |
| `type checking` (in the profiler categories) | kernel replay of the finished term (cause 8) |
| `compilation` | the compiler on a `def` that doesn't need executable code (cause 8) |

Two declarations slow for the same reason show the same dominant-node signature. **Check
that first** — in practice one PR's slow declarations almost always share a single root
cause, because they share an author and a pattern (`/buzz` Phase 5 is built on this).

## Root-cause taxonomy

### 1. Instance-synthesis blowup

**Signature.** `Meta.synthInstance` dominates; the trace shows the same instance searched
repeatedly (once per rewrite step), or a single search wandering a huge class hierarchy,
or — worst — a *failing* search retried at every step (failures aren't cached across
elaboration points).

**Fixes, in order:**
1. Synthesize once, reuse: `haveI := inst` / `letI := inst` before the expensive block, so
   every later step finds it by assumption instead of by search.
2. Give the elaborator the instance explicitly at the call site: `@lemma _ _ inst …` or
   named-argument syntax, when one call is the offender.
3. If the search is slow because the goal's type is only *defeq* to the instance's type
   (e.g. searching on an unfolded `Submodule.carrier` form), `show`/ascribe the folded form
   first — this is really cause 3 wearing cause 1's clothes.
4. A missing "shortcut" instance (mathlib adds these deliberately, e.g. direct instances
   avoiding a long parent chain) is a real fix but a **public API change — flag it for the
   user**, don't add silently.

### 2. Fat or looping `simp`

**Signature.** A `simp` node dominates; `trace.Meta.Tactic.simp.rewrite` shows hundreds of
rewrites, rewrites that undo each other, or one unfolding lemma (`simp [myDef]`) blowing
the goal up before the rest of the set grinds it back down.

**Fixes, in order:**
1. `simp?` → `simp only [the lemmas actually used]` for every **non-terminal** simp (the
   style rules require this anyway).
2. Shrink the goal *before* the simp: `rw` the one key equation first, or split the
   conjunction/cases so each simp sees a small goal.
3. Replace `simp [myDef]` unfolding with the definition's API lemmas (`myDef_apply`,
   `myDef_eq …`); if the API lemma doesn't exist, that's the missing piece to add.
4. A slow **terminal** simp may be squeezed for performance — an accepted, benchmarked
   exception to the "terminal simp stays unsqueezed" style rule. Note it in the report.

### 3. Unification / defeq blowup

**Signature.** `Meta.isDefEq` dominates. Classic triggers: `erw` (its whole job is
unification-up-to-unfolding); `rw`/`exact` where the lemma's LHS matches the goal only
after unfolding definitions (defeq abuse); numeric literals unified through `OfNat`/cast
towers; unifying two large terms that differ deep inside.

**Fixes, in order:**
1. Pin types early: `show <the folded form>`, type-ascribe `have h : T := …`, so
   elaboration never explores the unfolded route.
2. Replace `erw [foo]` with `rw [show a = b from rfl, foo]` or with the missing `@[simp]`
   API lemma that makes plain `rw` fire — `erw` is both a style smell and a perf bug.
3. State a `have`/helper at the abstraction level the lemmas expect, rewrite there, then
   convert once — instead of forcing every step to cross the defeq gap.
4. For literal/cast churn: `norm_num`/`push_cast` once up front, not per step (see cause 6).

### 4. Heavy terminal automation

**Signature.** One tactic node is the whole cost: `decide` (kernel-evaluates a decision
procedure), `nlinarith`/`polyrith` (searching certificate space), `aesop`/`grind` with a
big rule set, `omega` on a huge arithmetic goal.

**Fixes, in order:**
1. Ask the tactic what it found and inline it: `aesop?` / `exact?` / `polyrith` output →
   `exact <the proof>` or `linear_combination <certificate>`.
2. Downgrade to the targeted tool: `decide` → `norm_num`/`simp`; `nlinarith` →
   `positivity`/`gcongr`/`bound`; general `aesop` → the two lemmas it actually used.
3. Feed it a smaller goal: split cases first, `clear` irrelevant hypotheses (aesop and
   nlinarith costs scale with context size).
4. `native_decide` is **never** the fix (banned — it's an axiom-grade trust extension).

### 5. Missing expected type / metavariable churn

**Signature.** No single dominant leaf; the tree is wide, full of small re-elaborations
and postponed nodes. Typical sources: big anonymous-constructor terms `⟨…, …, …⟩` with no
expected type, `refine`/placeholder pyramids where every `_` is solved late, unascribed
`fun x => …` chains.

**Fixes:** type-ascribe the big term (`(⟨…⟩ : TheType)`); break the construction into named
`have h : T := …` steps (types written out); move information-rich arguments first so
unification pins the metavariables early.

### 6. Coercion churn

**Signature.** `push_cast`/`norm_cast`/simp-with-cast-lemmas nodes recur throughout the
proof; the same `((n : ℕ) : ℝ)`-tower is normalised at every step.

**Fixes:** cross the cast bridge once — `push_cast` at the start (or state the helper
lemma entirely in the target type), then work cast-free; `exact_mod_cast` once at the end
rather than `norm_cast` per step.

### 7. Duplicated large subterms

**Signature.** `diagnostics` unfold-counters show the same big term (a `Finset.sum`, a
matrix product, an integral) elaborated many times; the source visibly repeats it.

**Fixes:** `set x := <big term> with hx` (or a `have`/`let`) so it is elaborated once;
generalize it (`generalize h : bigTerm = x`) when the proof doesn't need its structure.

### 8. Kernel replay / compilation overhead

**Signature.** Elaboration is fine but the profiler's `type checking` category is large —
the kernel re-checks the term without the elaborator's caches. Triggers: `decide` again,
proofs-by-`rfl` that force heavy reduction, enormous proof terms from macro-heavy tactics.
Or: `compilation` is large on a `def` whose executable code nobody needs.

**Fixes:** replace reduction-heavy `rfl`/`decide` with simp-lemma chains (`norm_num`);
shrink the term via the causes above; mark data-irrelevant defs `noncomputable` (or
`irreducible` post-API) so the compiler skips them. If the *statement's* definitions force
the blowup, that's a design issue for `/develop`, not a proof patch.

## What is never a fix

- Raising `maxHeartbeats`, `synthInstance.maxHeartbeats`, or `maxRecDepth` — forbidden by
  `style-rules.md`, deleted on sight by `/cleanup` 3.7, blocked by `/pre-submit`.
- `native_decide`, `sorry`, new axioms.
- Changing the theorem's statement, hypotheses, or generality to dodge the slow step —
  statements are protected (`cleanup-gates.md` `theorem_statement_protected`). If the
  statement itself is the problem, that's a `/develop --continue` conversation.
- Silent global changes: file-wide `attribute [-simp]`, instance-priority edits, new
  shortcut instances. These can be *right*, but they change API for every user — flag them
  for user approval (same policy as `/generalise` big changes). Locally-scoped variants
  (`attribute [-simp] foo in`, `set_option … in`) are fine.

## Rules of thumb

- **One root cause per PR.** Slow declarations by the same author at the same time almost
  always share the cause. Diagnose one thoroughly; *test* the others against that
  signature before starting fresh (this is `/buzz` Phase 5, and it is why the workflow is
  fast in practice).
- **Measure → fix → re-measure.** A "fix" without a before/after number is a guess. Keep
  the numbers (ms and heartbeats) for the report.
- **Under a second is the bar** for a single declaration on a normal dev machine; mathlib
  reviewers watch orange bars, and a decl that keeps one lingering draws a comment.
  `count_heartbeats` well under six figures is the deterministic proxy.
- **If every fix pattern fails**, the elaboration work is real and the proof is doing too
  much in one declaration — split it (`/decompose-proof`): five 200ms lemmas beat one 1s
  monolith, and the helpers get cached across rebuilds.
