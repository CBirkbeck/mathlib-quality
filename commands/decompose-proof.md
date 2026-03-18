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

**Ask the user to confirm before proceeding to Pass 2.** Show them the plan. They may want to adjust helper names, skip certain proofs, or add notes.

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
