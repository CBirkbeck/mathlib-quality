---
name: decompose-proof
description: Break long proofs into helper lemmas
---

# /decompose-proof - Aggressive Proof Decomposition

**CRITICAL: No proof should exceed 50 lines. Target: main theorems <15 lines.**

Break long proofs into helper lemmas by understanding the mathematical structure.

## Usage

```
/decompose-proof [theorem_name]
/decompose-proof [file_path:line_number]
/decompose-proof --all [file_path]
```

## Core Principles

1. **Search mathlib FIRST** - Before creating ANY helper, check if mathlib already has it
2. **Generalize, don't specialize** - No single-use helpers; make lemmas reusable
3. **Review definitions too** - Not just proofs; definitions may duplicate mathlib
4. **Result by result** - Careful, systematic review of EVERY declaration
5. **Understand before extracting** - Know the mathematics, not just the syntax
6. **Split conjunctions** - Avoid `∧` in theorem statements; prove parts separately then combine
7. **Split large constructors** - If `constructor` has parts >10 lines, extract to lemmas
8. **Split large cases** - If `by_cases`/`rcases` branches are >10 lines, extract to lemmas

## Step 0: Strip Inline Comments

**Mathlib proofs must be comment-free.** Before decomposing:

1. **Remove ALL inline comments** from proofs - no exceptions
2. **Add docstrings ONLY to key public theorems** - one sentence describing the result
3. **Do NOT add docstrings to helper lemmas** - they're implementation details

```lean
-- BEFORE (bad - comments inflate line count)
theorem main_result : P := by
  -- First we establish that f is continuous on the compact set K
  -- This follows from the assumption hf combined with...
  have hcont := hf.continuousOn
  -- Now we can apply the extreme value theorem
  -- which gives us the existence of a maximum
  obtain ⟨x, hx, hmax⟩ := hK.exists_forall_ge hcont
  -- Finally we conclude using the bound
  exact bound_from_max hmax

-- AFTER (good - comment-free, docstring on key theorem only)
/-- Continuous functions on compact sets achieve their maximum. -/
theorem main_result : P := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_forall_ge hf.continuousOn
  exact bound_from_max hmax
```

**Docstring rules:**
- ONE sentence describing what the theorem proves
- NO proof strategy or implementation details
- Only on **key public theorems** (not helpers, not private lemmas)

## Structural Decomposition Rules

### Rule 1: Avoid `∧` in Theorem Statements

**CRITICAL:** Theorems with `∧` in the conclusion should be split into separate lemmas.

```lean
-- BAD: Single theorem proving a conjunction
theorem main_result : P ∧ Q := by
  constructor
  · -- 30 lines proving P
  · -- 40 lines proving Q

-- GOOD: Separate lemmas, then combine
lemma main_result_left : P := by
  -- 30 lines (can be further decomposed if needed)

lemma main_result_right : Q := by
  -- 40 lines (can be further decomposed if needed)

theorem main_result : P ∧ Q := ⟨main_result_left, main_result_right⟩
```

**Why:** Each part can be independently tested, reused, and golfed.

### Rule 2: Split Large `constructor` Branches

If a proof uses `constructor` and **either branch is >10 lines**, extract both branches to lemmas.

```lean
-- BAD: Long constructor branches
theorem foo : A ∧ B := by
  constructor
  · have h1 := ...
    have h2 := ...
    -- 15+ lines for A
  · have h3 := ...
    have h4 := ...
    -- 20+ lines for B

-- GOOD: Extract each branch
private lemma foo_left : A := by
  have h1 := ...
  have h2 := ...
  -- 15 lines (now easier to golf)

private lemma foo_right : B := by
  have h3 := ...
  have h4 := ...
  -- 20 lines (now easier to golf)

theorem foo : A ∧ B := ⟨foo_left, foo_right⟩
```

### Rule 3: Split Large Case Branches

If a `by_cases`, `rcases`, or pattern match has **any branch >10 lines**, extract each branch.

```lean
-- BAD: Long case branches
theorem bar : P := by
  by_cases h : condition
  · -- 25 lines handling true case
  · -- 30 lines handling false case

-- GOOD: Extract each case
private lemma bar_of_condition (h : condition) : P := by
  -- 25 lines (now can be independently golfed)

private lemma bar_of_not_condition (h : ¬condition) : P := by
  -- 30 lines (now can be independently golfed)

theorem bar : P := by
  by_cases h : condition
  · exact bar_of_condition h
  · exact bar_of_not_condition h
```

**Same applies to:**
- `rcases` with multiple patterns
- `match` expressions
- `if`/`else` chains
- `induction` with multiple cases

### Rule 4: The 10-Line Threshold

**10 lines is the trigger for extraction.** If ANY of these exceed 10 lines:
- A branch in `constructor`
- A case in `by_cases`/`rcases`
- A branch in pattern matching
- A single `have` block

Then it MUST be extracted to a helper lemma.

```lean
-- This 12-line have block should be extracted
have big_lemma : Complex := by
  line1
  line2
  -- ... 10 more lines

-- Extract it:
private lemma big_lemma_aux : Complex := by
  line1
  line2
  -- ... 10 more lines

-- Use it:
have big_lemma : Complex := big_lemma_aux
```

## Philosophy

Long proofs are **always** a sign that the mathematical structure hasn't been properly captured.
Every proof has a natural decomposition based on its mathematical content:

- **Estimates** become bound lemmas
- **Constructions** become existence lemmas
- **Case analyses** become case-specific lemmas
- **Limit arguments** become convergence lemmas
- **Algebraic manipulations** become identity lemmas

**Your job: Read the proof, understand the mathematics, extract the structure.**

## Thresholds

| Length | Action |
|--------|--------|
| <15 lines | Ideal, leave alone |
| 15-30 lines | Consider decomposition |
| 30-50 lines | **Must decompose** |
| >50 lines | **Critical - aggressive decomposition required** |

## Workflow

### Step 0.5: Search Mathlib First

**CRITICAL: Before creating ANY helper lemma, search mathlib.**

Use these tools to check if mathlib already has what you need:

```bash
# Type pattern search - find lemmas by signature
lean_loogle "Continuous → Bounded"
lean_loogle "IsCompact → ∃ x, ∀ y, ‖f y‖ ≤ ‖f x‖"
lean_loogle "Finset.sum _ _ ≤ _"

# Natural language search - describe what you need
lean_leansearch "continuous function on compact set is bounded"
lean_leansearch "sum over finite set is bounded by max times cardinality"
lean_leansearch "dominated convergence theorem"

# Local name search - check if name exists
lean_local_search "continuousOn_compact"
lean_local_search "norm_sum_le"
```

**Common patterns that ARE in mathlib:**
- Continuous functions on compact sets are bounded → `IsCompact.exists_bound_of_continuousOn`
- Norm of sum ≤ sum of norms → `norm_sum_le`
- Differentiable implies continuous → `Differentiable.continuous`
- Dominated convergence → `MeasureTheory.tendsto_integral_of_dominated_convergence`
- Triangle inequality variants → `norm_add_le`, `norm_sub_le`, `dist_triangle`

**If mathlib has it, USE IT. Don't create a helper.**

### Step 1: Understand the Mathematics

**Before touching any code**, answer these questions:

1. **What is the theorem actually proving?**
   - State it in plain mathematical language
   - Identify the key mathematical objects involved

2. **What are the key steps in the mathematical argument?**
   - NOT "apply lemma X" but "establish boundedness", "show convergence", etc.
   - Write out the proof strategy in 3-5 bullet points

3. **What are the independent mathematical facts being used?**
   - These become candidate helper lemmas
   - Look for statements that could be stated and proved separately

4. **What estimates or bounds are being established?**
   - Every `have h : ‖...‖ ≤ ...` is a candidate for extraction
   - Every `have h : ... < ε` is a candidate

5. **Are there similar arguments repeated?**
   - Same estimate with different inputs → parameterized helper
   - Same structure in multiple cases → shared helper

### Step 2: Identify Mathematical Components

Read through the proof and label each section by its mathematical role:

```lean
theorem big_theorem : P := by
  -- [SETUP: 5 lines] Introduce notation, unfold definitions
  -- [ESTIMATE 1: 15 lines] Establish bound on term A  ← EXTRACT
  -- [ESTIMATE 2: 12 lines] Establish bound on term B  ← EXTRACT
  -- [CONVERGENCE: 20 lines] Show limit exists         ← EXTRACT
  -- [ASSEMBLY: 8 lines] Combine pieces                ← Keep in main theorem
```

### Step 3: Design the Helper Lemmas

For each extractable component, design its statement:

1. **What does it prove?** (the conclusion)
2. **What does it need?** (the hypotheses - minimize these!)
3. **What should it be called?** (reflect the mathematics, use `snake_case`)

**Naming rules for helpers:**
- Use `snake_case` (NOT `camelCase`)
- Follow "conclusion_of_hypotheses" pattern
- Use `_aux` suffix for private helpers that reference the parent theorem
- Name should describe what the lemma proves, not just "helper" or "aux1"

**Good helper names:**
```lean
-- Good: Describes what it proves in snake_case
private lemma norm_bound_of_continuous_on_compact : ...
private lemma limit_of_dominated_convergence : ...
private lemma integral_vanishes_on_small_set : ...

-- Good: _aux suffix when tied to specific parent theorem
private lemma main_theorem_aux : ...           -- for main_theorem
private lemma valence_formula_bound_aux : ...  -- for valence_formula

-- Bad: wrong case or non-descriptive
private lemma bigTheoremAux1 : ...    -- wrong: camelCase
private lemma helper : ...            -- wrong: non-descriptive
private lemma Lemma1 : ...            -- wrong: UpperCase + number
```

**Check existing names too:** If the parent theorem has a non-conforming name, fix it first.

### Step 3.5: Generalize Before Extracting

**CRITICAL: Don't create single-use helpers.**

Before extracting ANY helper, ask:
1. Can this lemma be stated more generally?
2. Would this be useful in other contexts in this file? In other files?
3. Are the hypotheses minimal, or tied to specific context?
4. Does mathlib already have a more general version?

```lean
-- BAD: Single-use helper tied to specific context
private lemma residue_theorem_step1 (γ : PiecewiseC1Curve) (S0 : Finset ℂ)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS0 : ∀ s ∈ S0, s ∈ U) :
    ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∉ S0 → DifferentiableAt ℂ f (γ.toFun t) := ...

-- GOOD: General lemma that could be useful elsewhere
lemma differentiableAt_of_mem_open_diff_finite {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ S)) (z : ℂ)
    (hz : z ∈ U) (hz' : z ∉ S) : DifferentiableAt ℂ f z := ...
```

**Generalization checklist:**
- [ ] Can I remove specific type parameters? (e.g., `ℂ` → `𝕜`)
- [ ] Can I weaken hypotheses? (e.g., `Differentiable` → `ContinuousOn`)
- [ ] Does the lemma depend on the specific curve/set/function, or just properties?
- [ ] Would this be useful if I were writing a different theorem?

**If you can't generalize, consider:**
- Maybe the logic is inherently specific → keep it inline
- Maybe you're extracting too small a piece → extract larger chunk
- Maybe the proof approach needs rethinking

### Step 4: Extract with Minimal Hypotheses

When extracting a `have` block:

```lean
-- Before: hypotheses scattered throughout proof
theorem main : P := by
  have h1 : A := ...
  have h2 : B := ...
  have key : C := by  -- Uses h1, h2, and some assumptions
    [20 lines]
  exact finish key

-- After: helper has only what it needs
private lemma key_lemma (h1 : A) (h2 : B) : C := by [golfed]

theorem main : P := by
  have h1 : A := ...
  have h2 : B := ...
  exact finish (key_lemma h1 h2)
```

**Minimize hypotheses aggressively:**
- If the helper only uses `h1`, don't include `h2`
- If the helper only uses `hf.continuousOn`, take `ContinuousOn f s` not `Differentiable ℝ f`
- Weaker hypotheses → more reusable lemmas

### Step 5: Look for Shared Structure

After extraction, scan for consolidation opportunities:

**Pattern: Same proof, different objects**
```lean
-- Before
private lemma bound_for_f : ‖f x‖ ≤ C := by [same structure]
private lemma bound_for_g : ‖g x‖ ≤ C := by [same structure]

-- After
private lemma norm_bound (h : SomeProperty φ) : ‖φ x‖ ≤ C := by ...
-- Apply as: norm_bound hf, norm_bound hg
```

**Pattern: Repeated estimate with parameters**
```lean
-- Before: Same argument for ε/3, ε/3, ε/3
have h1 : ‖a‖ < ε/3 := by [10 lines]
have h2 : ‖b‖ < ε/3 := by [10 lines]
have h3 : ‖c‖ < ε/3 := by [10 lines]

-- After
private lemma small_norm (δ : ℝ) (hδ : 0 < δ) (x : X) (hx : P x) : ‖f x‖ < δ := by [5 lines]
-- Apply as: small_norm (ε/3) (by linarith) a ha, etc.
```

### Step 6: Restructure the Main Theorem

The main theorem should now read as an **outline of the argument**:

```lean
/-- The main result: [one sentence description] -/
theorem main_theorem (hyp1 : A) (hyp2 : B) : Conclusion := by
  -- Step 1: Establish the bound
  have hbound := norm_bound_lemma hyp1
  -- Step 2: Apply convergence
  have hconv := convergence_lemma hyp2 hbound
  -- Step 3: Conclude
  exact final_step hconv
```

Or better, in term mode:
```lean
theorem main_theorem (hyp1 : A) (hyp2 : B) : Conclusion :=
  final_step (convergence_lemma hyp2 (norm_bound_lemma hyp1))
```

### Step 7: Golf Everything

After decomposition:
1. Apply `/golf-proof` patterns to each helper
2. Many helpers become one-liners after isolation
3. The main theorem often becomes term-mode

## Mathematical Decomposition Patterns

### Analysis Proofs

**Pattern: ε-δ argument**
```lean
-- Extract: "for all ε, there exists δ" part
private lemma delta_for_epsilon (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, P δ ε := ...

-- Extract: "given δ, the bound holds" part
private lemma bound_from_delta (δ : ℝ) (hδ : 0 < δ) (h : d x y < δ) : ‖f x - f y‖ < ε := ...
```

**Pattern: Dominated convergence**
```lean
-- Extract: the dominating function exists and is integrable
private lemma dominating_function_integrable : Integrable g μ := ...

-- Extract: the pointwise bound
private lemma pointwise_dominated (x : X) : ‖f n x‖ ≤ g x := ...

-- Main theorem assembles these
theorem limit_of_integrals : ... := MeasureTheory.tendsto_integral_of_dominated_convergence ...
```

**Pattern: Compactness argument**
```lean
-- Extract: the set is compact
private lemma target_set_compact : IsCompact K := ...

-- Extract: the function achieves its bound on compact sets
private lemma achieves_bound_on_compact (hK : IsCompact K) : ∃ x ∈ K, f x = ⨆ y ∈ K, f y := ...
```

### Algebraic Proofs

**Pattern: Long calculation**
```lean
-- Break calc chains into named steps
private lemma step1 : a = b := by ring
private lemma step2 : b = c := by simp [foo_def]
private lemma step3 : c = d := by ring

theorem result : a = d := step1.trans (step2.trans step3)
```

**Pattern: Case analysis on algebraic structure**
```lean
-- Extract each case
private lemma case_zero (h : x = 0) : P := ...
private lemma case_nonzero (h : x ≠ 0) : P := ...

theorem result : P := by
  by_cases h : x = 0
  · exact case_zero h
  · exact case_nonzero h
```

### Topology Proofs

**Pattern: Open/closed set arguments**
```lean
-- Extract: the set is open
private lemma target_is_open : IsOpen U := ...

-- Extract: the point is in the interior
private lemma point_in_interior : x ∈ interior S := ...
```

**Pattern: Continuity of constructed function**
```lean
-- Extract: continuity of each piece
private lemma piece1_continuous : Continuous f₁ := ...
private lemma piece2_continuous : Continuous f₂ := ...

-- Main theorem combines
theorem constructed_continuous : Continuous F := piece1_continuous.add piece2_continuous
```

## Aggressive Decomposition Checklist

For proofs >50 lines, you MUST:

- [ ] Write out the mathematical argument in plain language (3-5 sentences)
- [ ] Identify at least 3 independent mathematical facts to extract
- [ ] Extract all `have` blocks >8 lines
- [ ] Extract all case splits where each case is >10 lines
- [ ] Look for repeated patterns and parameterize them
- [ ] Ensure main theorem is <15 lines after decomposition
- [ ] Golf all extracted helpers
- [ ] Check for consolidation opportunities across the file

## Output Format

```markdown
## Decomposition Report: [file_name]

### Mathematical Analysis

**Theorem X** (was 75 lines):
- Proves: [plain language description]
- Key steps:
  1. Establish continuity bound
  2. Apply dominated convergence
  3. Take limit
- Extracted: 4 helpers

### Helpers Created

| Helper | Mathematical Content | Lines |
|--------|---------------------|-------|
| `continuity_bound` | ‖f x‖ ≤ C on compact K | 12→4 |
| `dominated_bound` | |f_n| ≤ g pointwise | 15→6 |
| `limit_exists` | lim f_n exists a.e. | 20→8 |
| `integral_limit` | ∫f_n → ∫f | 10→3 |

### Main Theorem After

```lean
theorem X : ... := by
  have hbound := continuity_bound hK hf
  have hdom := dominated_bound hg
  exact integral_limit hbound hdom (limit_exists hf')
```
(8 lines, down from 75)

### Shared Helpers Identified

- `continuity_bound` also useful for theorem Y
- Consolidated `foo_aux` and `bar_aux` into `common_bound`

### Final Metrics

| Metric | Before | After |
|--------|--------|-------|
| Longest proof | 75 lines | 12 lines |
| Proofs >50 lines | 3 | 0 |
| Proofs >30 lines | 5 | 0 |
| Total helpers added | 0 | 12 |
```

## Reviewing Definitions

**Don't just review proofs - review EVERY definition too.**

For each definition in the file:

1. **Does mathlib already have this?**
   ```bash
   lean_loogle "CauchyPrincipalValue"
   lean_leansearch "principal value integral"
   ```

2. **Is it stated optimally?**
   - Could it use existing mathlib structures?
   - Is it more general than needed, or too specific?

3. **Is the API complete?**
   - Are there missing basic lemmas that would help?
   - Does it have the right simp lemmas?

```lean
-- BAD: Reinventing mathlib concepts
def myBoundedFunction (f : ℝ → ℝ) : Prop := ∃ M, ∀ x, ‖f x‖ ≤ M

-- GOOD: Use mathlib's Bornology.IsBounded or BoundedContinuousFunction
```

## Result-by-Result Review

**This is a careful, systematic process.** For EVERY declaration:

1. Read and understand it
2. Search mathlib for existing versions
3. Check if it can be generalized
4. Check if the proof can be shortened
5. Check naming conventions

Don't rush. Quality over speed.

## Remember

1. **Search mathlib FIRST** - Don't reinvent what exists
2. **Generalize, don't specialize** - No single-use helpers
3. **Understand first, code second** - Know the mathematics before extracting
4. **Name mathematically** - Helper names should describe what they prove
5. **Minimize hypotheses** - Weaker assumptions = more reusable lemmas
6. **Review definitions too** - Not just proofs
7. **Main theorems are outlines** - They should read as clear summaries
8. **50 lines is the absolute maximum** - Most proofs should be <20 lines
9. **Golf aggressively after extraction** - Isolated lemmas are often trivial

### Final Step: Record Learnings

After completing decomposition and showing the report, capture what was learned.

**For each decomposition decision**, write a JSON entry to `.mathlib-quality/learnings.jsonl` (create the file and directory if they don't exist):

```json
{
  "id": "<generate a short unique id>",
  "timestamp": "<current ISO timestamp>",
  "command": "decompose-proof",
  "type": "decomposition",
  "before_code": "<original proof structure summary, max 500 chars>",
  "after_code": "<decomposed structure: helper names and main theorem, max 500 chars>",
  "pattern_tags": ["<e.g. split_conjunction, extract_case, extract_have, parameterize_helper>"],
  "description": "<1-2 sentence description of the decomposition strategy and result>",
  "math_area": "<analysis|algebra|topology|number_theory|combinatorics|order|category_theory|measure_theory|other>",
  "accepted": true,
  "source": "<agent_suggestion|user_correction>",
  "context": {
    "file_path": "<relative path>",
    "theorem_name": "<the theorem that was decomposed>"
  }
}
```

**What to capture from decompose-proof:**
- Each significant decomposition (what was the proof structure, what helpers were extracted)
- Mathlib lemmas discovered that replaced custom helpers
- Shared logic that was consolidated across proofs
- Decomposition strategies that the user rejected or modified

**What NOT to capture:**
- Trivial extractions (obvious case splits)
- The golfing of individual helpers (that's golf-proof's domain)

**Keep it lightweight** - only 1-3 entries per command run, capturing the structural decisions.
