---
name: decompose-proof
description: Break long proofs into helper lemmas
---

# /decompose-proof - Two-Pass Proof Decomposition

**CRITICAL: No proof should exceed 50 lines. Target: main theorems <15 lines.**

Break long proofs into helper lemmas by understanding the mathematical structure first, then implementing.

## Usage

```
/decompose-proof [file_path]
/decompose-proof [theorem_name]
```

If no argument, operates on the currently open file.

## Architecture

**Problem**: Agents rush into decomposition without fully understanding the proof. They miss mathlib lemmas, create single-use helpers with bad names, and forget to consolidate.

**Solution**: Separate analysis from implementation:
1. **Pass 1 (Analysis)**: Identify ALL proofs needing decomposition. For each, study the mathematics and write a detailed decomposition plan as a comment block above the proof.
2. **Pass 2 (Decompose)**: Dispatch parallel agents, each handling one proof. They study the proof, search mathlib, then implement the plan.
3. **Pass 3 (Consolidate)**: Review all new helpers for duplicates and shared patterns.

---

## Pass 1: Analysis

### Step 1: Identify Candidates

Read the entire file and build a table of ALL proofs by length:

```
## Proof Length Report

| Declaration | Lines | Action |
|-------------|-------|--------|
| `main_theorem` | 65 | CRITICAL (>50) — aggressive decomposition |
| `helper_result` | 38 | MUST decompose (>30) |
| `medium_proof` | 22 | CONSIDER decomposition (15-30) |
| `small_lemma` | 12 | OK |
```

Also flag structural issues **regardless of length**:
- `∧` in theorem statement → MUST split
- `constructor` with any branch >10 lines → MUST extract branches
- `by_cases`/`rcases`/`match`/`induction` with any branch >10 lines → MUST extract branches
- `set_option maxHeartbeats` → MUST decompose (remove the set_option)

### Step 2: Study Each Candidate

For EACH proof flagged for decomposition, read it carefully **before writing any plan**. Answer these questions (write answers in your reasoning, not in the file):

1. **What is the theorem proving?** (plain language, 1-2 sentences)
2. **What are the key mathematical steps?** (3-5 bullet points, using math language like "establish bound", "show convergence", NOT "apply lemma X")
3. **What independent facts are being established?** (each is a candidate helper)
4. **What estimates/bounds appear?** (`have h : ‖...‖ ≤ ...` blocks are extraction candidates)
5. **Are there cases/branches >10 lines?** (mandatory extraction)
6. **Are there repeated patterns across proofs?** (consolidation candidates)

### Step 3: Write Decomposition Plans

For each candidate, add a `/- DECOMPOSE: ... -/` comment block **ABOVE** the declaration.

The plan MUST include:
- Current line count and target
- Mathematical summary
- Numbered list of planned helpers with: name, what it proves, hypotheses, whether to search mathlib
- Structural splits (∧, cases)
- Consolidation notes (patterns shared with other proofs)
- Potential refactoring (definitions to review)

#### Plan Format

```lean
/- DECOMPOSE: 65 lines → target <15 lines
   MATH: Proves convergence of integral via dominated convergence theorem.
   PLAN:
   1. Extract bound (lines 45-58) → `norm_bound_of_continuous_on_compact`
      Proves: ‖f x‖ ≤ C for x ∈ K
      Hyps: (hf : ContinuousOn f K) (hK : IsCompact K)
      SEARCH MATHLIB: IsCompact.exists_bound_of_continuousOn
   2. Extract domination (lines 60-78) → `dominated_pointwise_bound`
      Proves: ∀ n, ‖f_n x‖ ≤ g x
      Hyps: (hbound : ∀ n x, ‖f_n x‖ ≤ g x) — try to generalize
      SEARCH MATHLIB: eventually_of_forall
   3. Split ∧ in conclusion → `main_left` + `main_right`
   CONSOLIDATE: Bound pattern in (1) also used in `theorem_B` (line 120)
   REFACTOR: Check if `def myHelper` (line 30) can be removed after decomposition
-/
theorem main_theorem : P ∧ Q := by
  ...
```

#### Plan for Case/Branch Extraction

```lean
/- DECOMPOSE: 55 lines → target <10 lines
   MATH: Proves property P by case analysis on whether condition holds.
   PLAN:
   1. Extract true case (lines 72-90) → `foo_of_condition`
      Proves: condition → P
      Hyps: (h : condition) + relevant context
   2. Extract false case (lines 91-115) → `foo_of_not_condition`
      Proves: ¬condition → P
      Hyps: (h : ¬condition) + relevant context
   Main theorem becomes:
     by_cases h : condition
     · exact foo_of_condition h
     · exact foo_of_not_condition h
-/
theorem foo : P := by
  by_cases h : condition
  · -- 19 lines
  · -- 25 lines
```

#### Plan for Conjunction Splitting

```lean
/- DECOMPOSE: 48 lines → target 1 line (term mode)
   MATH: Establishes two independent properties of f.
   PLAN:
   1. Extract left conjunct → `f_continuous`
      Proves: Continuous f
      Hyps: existing hypotheses
   2. Extract right conjunct → `f_bounded`
      Proves: ∃ M, ∀ x, ‖f x‖ ≤ M
      Hyps: existing hypotheses
   Main theorem becomes: ⟨f_continuous, f_bounded⟩
-/
theorem f_properties : Continuous f ∧ ∃ M, ∀ x, ‖f x‖ ≤ M := by
  ...
```

### Step 4: Print Analysis Summary

```
## Decomposition Plan for [filename]

### Proofs to Decompose (by priority)
1. `main_theorem` (line 65, 65 lines → target <15)
   - Extract 2 helpers + split ∧
   - Mathlib search: dominated convergence, compactness bound
2. `helper_result` (line 130, 38 lines → target <15)
   - Extract 2 case branches
   - No mathlib search needed (domain-specific)

### Consolidation Opportunities
- Bound pattern in `main_theorem` helper #1 also applies to `theorem_B`
- Case analysis structure shared between `helper_result` and `other_result`

### Definitions to Review After Decomposition
- `def myHelper` (line 30) — may be removable
- `def customBound` (line 50) — may duplicate mathlib
```

### Awaiting user approval (mandatory pause)

**STOP HERE.** Do not dispatch Pass 2 agents until the user has approved the plan.

Print this exact line to the user:

```
AWAITING USER APPROVAL ON DECOMPOSITION PLAN — reply "approve" / "go ahead" / "looks
good" to start Pass 2, or describe changes you want first.
```

Then wait for an approval message. Possible responses:
- **Approve** → proceed to Pass 2
- **Change** ("rename helper #2 to X", "skip proof Y") → update the plan, re-print it, wait again
- **Cancel** → stop, leave `/- DECOMPOSE: ... -/` plan comments in place; user can resume later

Do NOT dispatch Pass-2 agents on your own initiative. The plan is approved by the user, not
by you.

---

## Pass 2: Decompose (Parallel Agents)

### Dispatching Agents

For each proof needing decomposition, dispatch an agent using the `Agent` tool with `subagent_type="general-purpose"`.

**Agent prompt template:**

```
You are decomposing a long proof in [file_path].

Read the file. Find the `/- DECOMPOSE: ... -/` comment above `[theorem_name]` (around line N).
Follow the decomposition plan. For EACH planned helper:

1. SEARCH MATHLIB FIRST
   Use lean_loogle, lean_leansearch, lean_local_search.
   If mathlib already has it → use mathlib directly, do NOT create a helper.

2. If creating a helper:
   - State as generally as possible — minimize hypotheses
   - Can it be weakened? (e.g., Differentiable → ContinuousOn)
   - Name mathematically in snake_case: `norm_bound_of_compact`, NOT `aux1`
   - Make it `private` unless genuinely reusable in other files
   - Place it ABOVE the main theorem
   - If it's a simple invocation of 1-3 mathlib lemmas → don't create it, use inline

3. After creating all helpers:
   - Rewrite the main theorem to use them
   - Main theorem MUST be <15 lines
   - Try term mode if possible
   - Goal: main theorem reads as a clear outline of the argument

4. Golf each helper:
   - Try grind, fun_prop, omega, ring, aesop on each (use lean_multi_attempt)
   - Inline single-use have statements
   - Convert to term mode where possible

5. Remove the `/- DECOMPOSE: ... -/` comment block

6. Run lean_diagnostic_messages after EACH helper to verify compilation

CRITICAL RULES:
- Understand the mathematics before extracting
- No single-use helpers — if you can't generalize it, keep it inline
- Search mathlib EXHAUSTIVELY: lean_loogle + lean_leansearch + lean_local_search
- If mathlib has it, USE IT — don't create a wrapper
- Name helpers by what they PROVE, not structural position
- Verify compilation at every step

REQUIRED REPORT FORMAT (the agent MUST print this to its caller; missing fields are
defects, like the /cleanup Phase-4 status block):

```
### Decomposition: [theorem_name]

1. MATH UNDERSTANDING (1-3 sentences in plain mathematical English of what the proof does):
   <explanation>

2. MATHLIB SEARCH (one row per planned helper):
   | Helper             | lean_loogle queries tried | lean_leansearch queries tried | found in mathlib? |
   |--------------------|---------------------------|-------------------------------|-------------------|
   | norm_bound_of_compact | "Continuous → ..."    | "compact bounded continuous"  | no                |
   | finite_support     | "DiscreteTopology → Finite" | "discrete compact finite"  | yes (DiscreteTopology.finite) — using directly |
   ...

3. HELPERS CREATED:
   | Helper name         | Generality (weakest hyps used)  | Visibility | Lines | Used in main? |
   |---------------------|---------------------------------|------------|-------|---------------|
   | norm_bound_of_compact | [Compact K] [Continuous f]    | private    | 8     | yes           |
   ...
   Helpers NOT created (kept inline because <1-3 mathlib calls or not generalizable):
   - <reason>

4. MAIN THEOREM:
   Before: <N> lines     After: <M> lines    (target: <15)
   Term-mode proof? <yes/no — if no, why>

5. GOLF PASS PER HELPER:
   | Helper | grind tried | fun_prop tried | other tactics tried | result |
   |--------|-------------|----------------|---------------------|--------|
   | norm_bound_of_compact | yes (failed) | yes (failed) | omega (n/a) | original kept |
   ...

6. VERIFICATION:
   ✓ DECOMPOSE comment block removed
   ✓ lean_diagnostic_messages clean after each helper
   ✓ Main theorem <15 lines (or report `STRUCTURE: <N> lines, see notes`)
```

If any field of this report is missing, the work is not done — the dispatcher will
re-dispatch.
```

**Dispatch agents in parallel** using multiple Agent tool calls in a single message. Each agent works on a different proof, so they won't conflict.

**Exception**: If two proofs share context (e.g., planned consolidation between them), put them in the SAME agent or handle sequentially.

### Collecting Results

Wait for all agents to complete. For each:
- Verify the main theorem is now <15 lines
- Check no compilation errors
- Verify DECOMPOSE comments were removed

---

## Pass 3: Consolidate

After all decompositions are complete, review the file as a whole:

### Check for Duplicate Helpers

Look across all newly created helpers:
- Do any prove the same or similar things?
- Can two similar helpers be merged into one parameterized version?

```lean
-- Before: two similar helpers
private lemma bound_for_f : ‖f x‖ ≤ C := by [same structure]
private lemma bound_for_g : ‖g x‖ ≤ C := by [same structure]

-- After: one parameterized helper
private lemma norm_bound (h : SomeProperty φ) : ‖φ x‖ ≤ C := by ...
```

### Review Helper Visibility

- Is any helper genuinely useful outside this file? → make it public (no `private`)
- Is any helper genuinely useful only once? → could it be kept inline instead?
- Does any helper duplicate something now in mathlib (after searching)? → use mathlib

### Review Definitions

After decomposition, revisit definitions in the file:
- Are any definitions now unused? → remove
- Are any definitions now clearly matching mathlib concepts? → replace with mathlib
- Are any definitions too specific? → try to generalize

### Final Compilation

Run `lean_diagnostic_messages` on the full file. Fix any remaining issues.

---

## Pass 3.5: Helper Hygiene (REQUIRED before any PR)

**Mechanically-extracted helpers inherit the ambient context of the proof they
came from.** Sections, typeclasses, whole-family hypotheses, the parent theorem's
docstring framing, brittle inline reshapes — none of these were stated *for the
helper*, they came along for the ride. Reviewers catch every one of them. A
pre-PR `/cleanup` curates each helper to the minimum its own statement needs;
running this before opening the PR avoids the review round-trip.

For every newly extracted helper, run the five-item curation check below.

### 3.5.1 — Generality (drop unused inherited context)

The helper is now its own declaration; it doesn't get the parent section's
typeclasses by default — but if you copy-pasted from the parent's signature,
unused ones came with the helper. Audit per parameter:

- **Drop unused typeclasses.** `[Finite ι]` inherited from the ambient section
  but never used in the helper's proof → delete.
- **Turn `∀`-family hypotheses into pointwise.** `(hcop : ∀ i, ¬ (p : ℤ) ∣ d i)`
  when the proof only uses `hcop i` for one specific `i` → restate as
  `{i : ι} (hcop_i : ¬ (p : ℤ) ∣ d i)`. The pointwise form is strictly weaker
  and makes the helper easier to apply at call sites.

Per helper, fill in:

```
| Inherited param                 | Used in proof? | Action            |
|---------------------------------|----------------|-------------------|
| `[Finite ι]`                   | no             | DROP              |
| `(hcop : ∀ i, ¬ (p : ℤ) ∣ d i)` | only at `i = i_0` | POINTWISE  |
| `[IsGalois ℚ K]`                | yes (1 site)   | keep              |
```

### 3.5.2 — Real-name encoding (use mathlib's object names, name the criterion)

Helper names from mechanical extraction often abbreviate the mathlib object
(`legendre` instead of `legendreSym`) or describe a vague property
(`split_lemma`) rather than the actual mathematical criterion.

- Use the **real mathlib object name**. `legendreSym`, not `legendre`. `qExpansion`,
  not `q`. `Module.rank`, not `dim`. Grep mathlib for the exact name.
- Encode the **actual hypothesis/criterion** in the helper name, not a vague
  label.

```lean
-- Bad: vague label, wrong object name
private theorem legendre_eq_one_of_complete_split ...

-- Good: mathlib object name + the actual criterion that delivers the conclusion
private theorem legendreSym_eq_one_of_ncard_primesOver_eq_finrank ...
```

### 3.5.3 — Placement (move generic infrastructure to generic files)

A helper extracted because the parent's proof needed it doesn't automatically
belong in the parent's file. If the helper is generic infrastructure (e.g. it
talks about `Ideal` / `IsGalois` / `primesOver` / abstract typeclasses without
mentioning the parent's specific concept), **move it to the appropriate generic
file as a public lemma** rather than leaving it `private` next to the specialised
parent.

Per helper, answer:
- Is this helper specific to the parent's concept (e.g. multiquadratic-splitting-
  specific machinery)? → keep `private` here.
- Or is it a generic fact about the underlying structures? → move to the
  appropriate generic file (find the analogous mathlib location) and make
  `public`. Update imports.

### 3.5.4 — Statement-level docstrings (proof narration goes inside)

Helper docstrings describe the statement, not the proof. Move proof narration
into `--` comments inside the proof body.

```lean
-- Bad: docstring narrates the proof
/-- Helper for the splitting law: we apply the orbit-stabiliser lemma to the
prime ideal Q, then use the fact that the Galois group acts transitively on
the primes over `(p)`, and conclude by counting. -/
private lemma legendreSym_eq_one_of_... ...

-- Good: docstring describes the statement; narrative inside
/-- `legendreSym p (d i) = 1` when `p` splits completely in `K`. -/
private lemma legendreSym_eq_one_of_... ... := by
  -- Orbit-stabiliser on Q; transitive Galois action on primesOver (p); count.
  ...
```

### 3.5.5 — Document brittle inherited steps

When the helper's proof has a step that depends on a definitional equality,
a `fun _ => rfl` defeq across a wrapper, a `show … by ring` reshape, or any
other "this is fragile if mathlib changes the unfolding" step, add a one-line
comment explaining what's brittle and why. This isn't proof narration (the
docstring rule above) — it's a maintenance warning for the next person who
touches it.

```lean
private lemma foo ... := by
  -- BRITTLE: the `show … by ring` reshape depends on `Foo.bar` unfolding to a
  -- specific normal form; if `Foo.bar` is restated, this needs updating.
  show ... by ring
  ...
```

### 3.5.6 — Curation report (REQUIRED ARTIFACT)

After the per-helper check, print:

```
### Helper hygiene curation report

For each extracted helper:

| # | Helper name (final)                                  | Generality drops          | Renamed from               | Moved to file              | Brittle steps |
|---|------------------------------------------------------|---------------------------|-----------------------------|----------------------------|---------------|
| 1 | `legendreSym_eq_one_of_ncard_primesOver_eq_finrank` | dropped `[Finite ι]`; `∀ i, hcop` → pointwise | `legendre_eq_one_of_complete_split` | (same — specific) | none |
| 2 | `nucleusAtPrime_smul_aux`                           | (none)                    | (no rename)                 | moved to `Algebra/NumberTheory/Generic.lean` | 1 (documented) |
| ...                                                                                                                                                                                       |
```

Each `Generality drops` cell must be either "(none)" with a one-line reason or
the concrete list of dropped/weakened parameters. A row that reads "(none)"
with no reason is a defect — re-run 3.5.1 for that helper.

---

## Core Rules

### Structural Rules (MANDATORY — apply regardless of proof length)

1. **No `∧` in theorem statements** → Split into separate lemmas, combine with `⟨left, right⟩`
2. **No constructor branch >10 lines** → Extract both branches as lemmas
3. **No case branch >10 lines** → Extract all branches (`by_cases`, `rcases`, `match`, `induction`)
4. **No proof >50 lines** → Aggressive decomposition required
5. **Target: main theorems <15 lines** → Should read as an outline

### Before Creating ANY Helper

1. **Search mathlib** — `lean_loogle`, `lean_leansearch`, `lean_local_search`
2. **Can it be stated more generally?** — Weaker hypotheses = more reusable
3. **Would it be useful elsewhere?** — If single-use and can't generalize, keep inline
4. **Is it just combining 1-3 mathlib calls?** → Don't create it, use mathlib directly

### Helper Design

- `private` by default (public only if genuinely reusable in other files)
- `snake_case` names describing what they prove
- `_aux` suffix when helper is specific to one parent theorem
- Minimal hypotheses (weaker assumptions = more reusable)
- Golf aggressively after extraction (isolated lemmas often become one-liners)

### Naming Helpers (Mathematical, NOT Structural)

```lean
-- Good: describes the mathematics
private lemma norm_bound_of_continuous_on_compact : ...
private lemma integral_vanishes_on_small_set : ...
lemma disjoint_balls_of_separated : ...  -- public, genuinely reusable

-- Bad: structural reference
private lemma main_theorem_aux1 : ...   -- what does aux1 prove?
private lemma step_2 : ...             -- meaningless
private lemma helper : ...             -- non-descriptive
```

### Generalization Checklist

Before extracting a helper:
- [ ] Can I remove specific type parameters? (e.g., `ℂ` → `𝕜`)
- [ ] Can I weaken hypotheses? (e.g., `Differentiable` → `ContinuousOn`)
- [ ] Does it depend on the specific object, or just properties?
- [ ] Would this be useful in a different theorem?

---

## Mathematical Decomposition Patterns

### ε-δ Arguments
Extract: `delta_for_epsilon` + `bound_from_delta`

### Dominated Convergence
Extract: integrability + domination bound + pointwise convergence

### Compactness Arguments
Extract: set compactness + extremal value on compact

### Case Analysis
Extract each case as a separate lemma

### Long Calculations
Break into named steps using `.trans` chains

### Repeated Estimates
Same estimate with different inputs → parameterized helper

---

## Output Format

```
## Decomposition Report for [filename]

### Pass 1: Analysis
- Proofs analyzed: N
- Flagged for decomposition: M
- Planned helpers: K

### Pass 2: Decomposition
| Theorem | Before | After | New Helpers | Mathlib Used |
|---------|--------|-------|-------------|--------------|
| `main_theorem` | 65 | 8 | 2 | `norm_sum_le` |
| `helper_result` | 38 | 5 | 2 | — |

### Mathlib Discoveries
- Replaced custom bound with `IsCompact.exists_bound_of_continuousOn`
- Used `norm_sum_le` instead of manual triangle inequality

### Pass 3: Consolidation
- Merged `bound_for_f_aux` and `bound_for_g_aux` into `norm_bound_of_property`
- Removed unused `def customBound`

### Final Metrics
| Metric | Before | After |
|--------|--------|-------|
| Longest proof | 65 | 12 |
| Proofs >50 lines | 2 | 0 |
| Proofs >30 lines | 3 | 0 |
| New helpers | 0 | 5 |

### Verification
✓ File compiles without errors
✓ No DECOMPOSE comments remaining
✓ All proofs ≤50 lines
```

---

## Reference

For decomposition patterns and examples:
- `skills/mathlib-quality/SKILL.md` — thresholds, structural rules
- `skills/mathlib-quality/examples/decompose_proof.md` — decomposition examples
- `skills/mathlib-quality/references/proof-patterns.md` — proof techniques
- `skills/mathlib-quality/agents/proof-decomposer-prompt.md` — agent reference

---

## Learnings

After completing, record decomposition decisions to `.mathlib-quality/learnings.jsonl`.

**What to capture** (1-3 entries):
- Significant decomposition strategies (proof structure → helper structure)
- Mathlib lemmas that replaced custom helpers
- Shared logic consolidated across proofs
- Strategies the user rejected or modified

See `skills/mathlib-quality/learning/schema.md` for the JSON schema.
