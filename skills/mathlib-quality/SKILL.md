# Mathlib Quality Skill

## Activation Triggers

This skill activates when:
- Working with `.lean` files intended for mathlib contribution
- User mentions "mathlib style", "cleanup", "golf", "PR submission", or "pre-submit"
- User asks to fix reviewer feedback on a mathlib PR
- User wants to check code against mathlib conventions

## Overview

This skill helps bring Lean 4 code up to mathlib standards by:
1. Enforcing style rules (line length, formatting, indentation)
2. Checking naming conventions
3. Ensuring proper documentation
4. Golfing proofs to be shorter and cleaner
5. Preparing code for PR submission

## Available Commands

| Command | Description |
|---------|-------------|
| `/cleanup` | Full file cleanup to mathlib standards |
| `/check-style` | Validate without making changes |
| `/golf-proof` | Optimize specific proofs |
| `/decompose-proof` | Break long proofs into helper lemmas |
| `/split-file` | Split large files (>1500 lines) into focused modules |
| `/pre-submit` | Pre-PR submission checklist |
| `/fix-pr-feedback` | Address reviewer comments |

## Core Style Rules (Quick Reference)

### File Structure
- **File names**: `UpperCamelCase.lean` (e.g., `TopologicalSpace.lean`)
- **Line length**: 100 characters max
- **File length**: 1500 lines max (MUST split if larger)
- **Proof length**: **50 lines absolute max** (target <15 lines for main theorems)
- **Header order**: Copyright, module docstring, imports
- **Comments in proofs**: NONE - mathlib proofs should be comment-free
- **Module system**: New files should have `module` keyword before imports

### Formatting
- **Indentation**: 2 spaces for continuation lines, 4 for multi-line theorem statements
- **`by` placement**: Always at END of preceding line (not on its own line)
- **Focusing dot**: Use `·` (not indented) for subgoals
- **One tactic per line** (preferred)
- **Prefer**: `fun x ↦ ...` over `λ x, ...`
- **Prefer**: `<|` over `$` to avoid parentheses
- **Prefer**: `change` over `show` in proofs
- **No trailing whitespace**
- **No empty lines inside declarations**

### `by` Placement (CRITICAL)
```lean
-- CORRECT: by at end of preceding line
theorem foo : P := by
  exact h

-- WRONG: by on its own line
theorem foo : P :=
  by exact h
```

### Subgoal Focusing
```lean
-- Use focusing dot · at column 0
theorem foo : P ∧ Q := by
  constructor
· exact hp
· exact hq
```

### Instance Syntax
Use `where` syntax for structure/class instances:
```lean
instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
```

### Naming Conventions

**CRITICAL: Different naming conventions for defs vs lemmas/theorems!**

| Declaration Type | Returns | Case Style | Example |
|------------------|---------|------------|---------|
| `lemma`/`theorem` | `Prop` | `snake_case` | `continuous_of_bounded` |
| `def` | Data (ℂ, ℝ, Set, etc.) | `lowerCamelCase` | `cauchyPrincipalValue` |
| `structure`/`inductive` | Type | `UpperCamelCase` | `ModularForm` |
| Structure fields | - | `lowerCamelCase` or `snake_case` | `toFun`, `map_one'` |

**Key rule:** Look at what the declaration **returns**:
- Returns a **Prop** (statement to prove) → `snake_case`
- Returns **data** (number, set, function, etc.) → `lowerCamelCase`
- Defines a **Type** → `UpperCamelCase`

**Examples:**
```lean
-- Lemmas/theorems (return Prop) → snake_case
theorem continuous_of_uniform : Continuous f := ...
lemma norm_le_of_mem_ball : ‖x‖ ≤ r := ...

-- Defs returning data → lowerCamelCase
def cauchyPrincipalValue (f : ℝ → ℂ) : ℂ := ...
def residueAtPole (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := ...
def fundamentalDomain : Set ℂ := ...

-- Types → UpperCamelCase
structure ModularForm where ...
inductive BoundarySegment where ...
```

### Variable Conventions

| Type | Variables |
|------|-----------|
| Universes | `u`, `v`, `w` |
| Generic types | `α`, `β`, `γ` |
| Propositions | `a`, `b`, `c` |
| Type elements | `x`, `y`, `z` |
| Assumptions | `h`, `h₁`, `h₂` or `hf`, `hg` |
| Predicates | `p`, `q`, `r` |
| Lists/Sets | `s`, `t` |
| Naturals | `m`, `n`, `k` |
| Integers | `i`, `j`, `k` |
| Groups | `G`, `H` |
| Rings | `R`, `S` |
| Fields | `K`, `𝕜` |
| Vector spaces | `E`, `F` |

### Additional Conventions
- **Acronyms as groups**: `LE`, `Ne` (not `Le`, `NE`)
- **American English**: `Factorization` not `Factorisation`
- **Helper lemmas**: `_aux` suffix, must be `private`
- **Prop-valued classes**: "Is" prefix for nouns (`IsNormal`), no prefix for adjectives

### Naming Check and Fix (CRITICAL)
**All lemma/definition names MUST follow mathlib conventions.** When cleaning up a file:

1. **Check every declaration name** against the naming rules
2. **Rename non-conforming declarations** to follow conventions
3. **Update ALL usages** of renamed declarations in the file

**Common naming issues to fix:**
| Bad Name | Good Name | Rule |
|----------|-----------|------|
| `myLemma` | `my_lemma` | snake_case for lemmas |
| `Lemma1` | `lemma_one` or descriptive | no numbers, snake_case |
| `fooAux` | `foo_aux` | snake_case with _aux suffix |
| `helper` | `main_theorem_aux` | name should reference parent |
| `Factorisation` | `Factorization` | American English |
| `continuous_Function` | `continuous_function` | consistent snake_case |

### Symbol Dictionary for Naming

| Symbol | Name in identifiers |
|--------|---------------------|
| `∨` | `or` |
| `∧` | `and` |
| `→` | `imp` or `of` (hypothesis) |
| `↔` | `iff` (often omitted) |
| `¬` | `not` |
| `∀` | `forall` or `all` |
| `∃` | `exists` |
| `=` | `eq` (often omitted) |
| `≠` | `ne` |
| `∈` | `mem` |
| `∪` | `union` |
| `∩` | `inter` |
| `⋃` | `iUnion` (indexed) |
| `⋂` | `iInter` (indexed) |
| `\` | `sdiff` |
| `ᶜ` | `compl` |
| `+` | `add` |
| `-` | `sub` (binary) or `neg` (unary) |
| `*` | `mul` |
| `^` | `pow` |
| `/` | `div` |
| `•` | `smul` |
| `∣` | `dvd` |
| `≤` | `le` or `ge` (swapped) |
| `<` | `lt` or `gt` (swapped) |
| `⊔` | `sup` |
| `⊓` | `inf` |
| `⨆` | `iSup` (indexed) |
| `⨅` | `iInf` (indexed) |

### Hypothesis Ordering: `C_of_A_of_B`

For theorem `A → B → C`, name it `C_of_A_of_B` (hypotheses in appearance order):
```lean
-- Good: hypotheses in order of appearance
add_pos_of_pos_of_pos    -- conclusion: add_pos; hyps: pos, pos
continuous_of_uniform    -- conclusion: continuous; hyp: uniform
norm_bound_of_compact    -- conclusion: norm_bound; hyp: compact

-- Use abbreviations
pos, neg, nonpos, nonneg  -- replace zero_lt, lt_zero, le_zero, zero_le

-- Bad names
lemma1, helper, aux      -- non-descriptive
myCustomLemma            -- wrong case
```

### Structural Lemma Naming

| Pattern | Naming |
|---------|--------|
| Extensionality | `.ext` (marked `@[ext]`), `.ext_iff` |
| Injectivity | `f_injective` (Function.Injective), `f_inj` (bidir, `@[simp]`) |
| Induction (Prop) | `T.induction_on` (value first), `T.induction` (constructors first) |
| Recursion (Type) | `T.recOn` (value first), `T.rec` (constructors first) |

### Predicate Positioning
Most predicates are **prefixes**: `isClosed_Icc`, `isOpen_ball`

Exceptions (suffixes, like atoms): `_injective`, `_surjective`, `_bijective`, `_monotone`, `_antitone`

### Documentation Requirements
- Module docstring after imports (at the TOP of the file only)
- Docstrings ONLY for important public theorems and all definitions
- Keep docstrings **1-2 consecutive lines** describing what it proves/defines
- **NO blank lines inside docstrings** - must be consecutive lines
- **FORBIDDEN in docstrings:**
  - Proof strategies or ideas (e.g., "**Proof idea**: ...")
  - Technical notes (e.g., "**Note**: The hypothesis...")
  - Multi-paragraph explanations
  - Implementation details
  - Bullet points explaining the proof
  - References to other proof assistants (e.g., Isabelle, HOL)
- **NO section markers** (`/-! ## Section Name -/`) throughout the file
  - Only the module docstring at the very top is allowed
  - Results should be separated by a single blank line

### Comments in Proofs
- **NO inline comments in proofs** - mathlib proofs must be comment-free
- Do NOT add docstrings to helper/private lemmas
- Do NOT explain proof steps in docstrings - the code should be self-documenting

### Helper Lemmas and Visibility
- Helper lemmas use `_aux` suffix (e.g., `foo_aux`, `bar_step_aux`)
- Helper lemmas should be `private`
- Only results intended for use in other files/mathlib should be public
- If a lemma is only used within the file, make it private

## Workflow Guidance

### When Preparing a PR

1. **First pass**: Run `/check-style` to see all issues
2. **Apply fixes**: Run `/cleanup` to auto-fix what's possible
3. **Golf proofs**: Run `/golf-proof` on verbose proofs
4. **Final check**: Run `/pre-submit` before creating PR

### When Handling PR Feedback

1. Copy reviewer comments or provide PR number
2. Run `/fix-pr-feedback`
3. Verify each fix compiles
4. Re-run `/pre-submit` before pushing

## Reference Files

**Start here - comprehensive guide from PR analysis:**
- `references/mathlib-quality-principles.md` - **Core quality principles** (synthesized from 4,600+ PR reviews)

For detailed guidance:
- `references/style-rules.md` - Complete formatting rules
- `references/naming-conventions.md` - Naming patterns (defs vs lemmas distinction)
- `references/proof-patterns.md` - Proof golf techniques
- `references/pr-feedback-examples.md` - Real feedback examples
- `references/linter-checks.md` - Automated linter rules

**Pattern-specific examples (load based on proof content):**
- `examples/inline_have.md` - Inline `have` blocks (77 PR examples)
- `examples/term_mode.md` - Convert to term mode (311 `exact` removals)
- `examples/simp_golf.md` - Simplify simp usage (311 `simp` removals)
- `examples/automation.md` - Use `grind`/`fun_prop` (1144 automation suggestions)
- `examples/decompose_proof.md` - Break long proofs into helper lemmas

## Integration with Lean 4 Tools

This skill works alongside the `lean4-theorem-proving` skill:
- Use Lean LSP tools to verify changes compile
- Use `lean_diagnostic_messages` to check for errors after edits
- Use `lean_goal` to verify proof state during golfing

## Common Mistakes to Avoid

1. **Overly long lines** - Break at operators, align continuations
2. **Verbose proofs** - Golf aggressively; one-liners are ideal
3. **Unnecessary `have` blocks** - Inline `have foo := bar` unless used 2+ times
   - `have h := lemma x` → inline as `lemma x` where used
   - `have h : T := by ...` → keep (has proof content) or extract as helper
4. **Non-descriptive names** - Use conclusion-of-hypotheses pattern
5. **Verbose docstrings** - Keep them short (one sentence), no proof strategies
6. **Docstrings on helpers** - Only important public theorems need docstrings
7. **Non-terminal `simp` without arguments** - Use `simp only [...]` for non-terminal simp
   - Terminal `simp` (closing the goal) should NOT be squeezed unless performance is poor
8. **Trailing `sorry`** - Remove all before submission
9. **Debug options** - Remove `set_option trace.*`
10. **ANY comments in proofs** - Proofs should be comment-free; use docstrings for documentation
11. **Not using `fun_prop`** - Prefer `fun_prop` over `continuity`/`measurability`
12. **Monolithic files** - Split files > 1500 lines by theme
13. **Public helpers** - Helper lemmas should be `private` with `_aux` suffix
14. **Non-private internal lemmas** - Only export what other files need
15. **Long proofs (>50 lines)** - CRITICAL: decompose into helpers; target <15 lines for main theorems
16. **Duplicated proof logic** - Extract shared patterns into parameterized common helpers
17. **Not understanding the mathematics** - Before decomposing, describe the proof in plain language
18. **`by` on its own line** - ALWAYS put `by` at end of preceding line
19. **Using `λ` instead of `fun`** - Use `fun x ↦ ...`
20. **Empty lines inside declarations** - Keep declarations compact

## Deprecation Format

When renaming/removing public declarations, use:
```lean
@[deprecated (since := "YYYY-MM-DD")]
alias old_name := new_name

-- With explanation
@[deprecated "Use foo_bar instead" (since := "YYYY-MM-DD")]
theorem old_theorem ...
```
Deprecations can be removed after 6 months.

## Proof Decomposition

**Rule: No proof should exceed 50 lines. Target: main theorems <15 lines.**

Long proofs indicate the mathematical structure hasn't been properly captured. Every proof
decomposes naturally based on its mathematical content.

### Thresholds
| Length | Action |
|--------|--------|
| <15 lines | Ideal |
| 15-30 lines | Consider decomposition |
| 30-50 lines | **Must decompose** |
| >50 lines | **Critical - aggressive decomposition required** |

### The Decomposition Process (CRITICAL)

**This is a careful, systematic process. Do it right, not fast.**

#### Step 1: Identify Long Proofs
Scan the file and list ALL proofs >30 lines with their line numbers and counts.

#### Step 2: Understand the Complete Proof
Before touching any code, read the entire proof and answer:
1. What is the theorem proving (in plain language)?
2. What are the key mathematical steps in the argument?
3. What independent facts are being established?
4. What estimates/bounds appear?
5. Are there `cases`, `by_cases`, `rcases` that split into independent branches?
6. Are there repeated patterns across different proofs?

#### Step 3: Search Mathlib FIRST
**Before extracting ANY helper, search mathlib** to see if it already exists:
```
lean_loogle "Continuous → Bounded"           -- Type pattern search
lean_leansearch "continuous function on compact is bounded"  -- Natural language
lean_local_search "continuousOn_compact"     -- Local name search
```

Many "helper lemmas" are already in mathlib. Use them instead of writing new ones.

#### Step 4: Generalize Before Extracting
**CRITICAL: Don't create single-use helpers.** Before extracting, ask:
- Can this lemma be stated more generally?
- Would this be useful in other contexts?
- Are the hypotheses minimal, or tied to specific context?

```lean
-- BAD: Single-use helper tied to specific context
private lemma residue_theorem_step1 (γ : PiecewiseC1Curve) (S0 : Finset ℂ)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) : ... := ...

-- GOOD: General lemma that could be useful elsewhere
lemma norm_sum_le_of_disjoint_balls {S : Finset ℂ} {ε : ℝ} (hε : 0 < ε)
    (h_disjoint : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → Disjoint (ball s ε) (ball s' ε)) :
    ‖∑ s ∈ S, f s‖ ≤ ∑ s ∈ S, ‖f s‖ := ...
```

#### Step 5: Extract Cases as Lemmas
If a proof has `cases h with | inl => ... | inr => ...` or `by_cases`:
- Each case is often a standalone lemma
- Extract each case, then combine them in the main proof

```lean
-- Before: 80-line proof with two cases
theorem foo : P ∨ Q → R := by
  intro h
  cases h with
  | inl hp => ... 40 lines ...
  | inr hq => ... 40 lines ...

-- After: Two focused helpers + short main proof
private lemma foo_of_left (hp : P) : R := by ... 40 lines ...
private lemma foo_of_right (hq : Q) : R := by ... 40 lines ...

theorem foo : P ∨ Q → R := fun h => h.elim foo_of_left foo_of_right
```

#### Step 6: Check Definitions Too
Review ALL definitions in the file:
- Can they be simplified?
- Are they duplicating mathlib concepts?
- Should they use existing mathlib definitions instead?

### Decomposition Strategy
1. **Label sections by mathematical role**: setup, estimate, convergence, assembly
2. **Extract independent facts as helpers**: bounds, limits, constructions
3. **Name mathematically**: `norm_bound_of_continuous`, not `theorem_aux1`
4. **Minimize hypotheses**: weaker assumptions = more reusable lemmas
5. **Golf helpers aggressively**: isolated lemmas often become one-liners
6. **Consolidate shared logic**: same proof structure → parameterized helper
7. **Prefer mathlib**: if mathlib has it, use it; don't reinvent

### Helper Naming (Mathematical, not Structural)
```lean
-- Good: describes what it proves
private lemma norm_bound_of_continuous_on_compact : ...
private lemma limit_of_dominated_convergence : ...
lemma disjoint_balls_of_separated : ...  -- General, could be public

-- Bad: just references parent
private lemma big_theorem_aux1 : ...
private lemma step_2 : ...
```

### Helper Visibility
| Generality | Visibility |
|------------|------------|
| Very general, useful elsewhere | `lemma` (public) - consider if mathlib has it |
| Specific to this file's topic | `private lemma` |
| Only used once, can't generalize | `private lemma` with `_aux` suffix |

### Result
Main theorems should read as **clear outlines**:
```lean
private lemma continuity_bound : ‖f x‖ ≤ C := by ...
private lemma dominated_pointwise : ‖f_n x‖ ≤ g x := by ...

theorem main_result : ... :=
  limit_theorem (continuity_bound hf) (dominated_pointwise hg)
```

### Decomposition Checklist
For each proof >30 lines:
- [ ] Read and understand the complete proof
- [ ] List the independent mathematical steps
- [ ] Search mathlib for each step (`lean_loogle`, `lean_leansearch`)
- [ ] Identify cases/branches that could be separate lemmas
- [ ] For each potential helper: can it be generalized?
- [ ] Extract helpers with minimal, general hypotheses
- [ ] Name helpers mathematically (not `_aux1`, `_aux2`)
- [ ] Verify file compiles after each extraction
- [ ] Golf the extracted helpers
- [ ] Final main proof should be <15 lines

## Key Tactics for Golfing

**Goal: Minimize proof length.** One-liners are ideal. Brevity trumps readability.

### Deep Golfing Approach

For thorough optimization, use the **deep golfer** methodology:
1. Read PR feedback data (`data/pr_feedback/curated_examples.md`)
2. Go through **every 3-5 lines** of each proof
3. Check each pattern against the 12+ specific PR patterns
4. Try `lean_multi_attempt` on chunks with: `grind`, `aesop`, `simp_all`, `fun_prop`, `omega`, `ring`
5. Document which PR pattern each change matches

See `agents/deep-golfer-prompt.md` for the full deep golfer methodology.

### Quick Reference: Pattern Savings

| Pattern | Savings | Priority |
|---------|---------|----------|
| `by rfl` → `rfl` | 1 line | ⭐⭐⭐⭐⭐ |
| `by exact h` → `h` | 1 line | ⭐⭐⭐⭐⭐ |
| `fun x => f x` → `f` | Tokens | ⭐⭐⭐⭐⭐ |
| `rw; exact` → `rwa` | 50% | ⭐⭐⭐⭐⭐ |
| Single-use `have` inline | 30-50% | ⭐⭐⭐⭐ |
| Multi-step → `grind` | 60-80% | ⭐⭐⭐⭐⭐ |
| `.trans` chains | 2-3 lines | ⭐⭐⭐⭐ |

### `fun_prop` for Analysis Properties
```lean
-- IMPORTANT: Unfold definitions first so fun_prop can see structure
example : Continuous F := by simp only [F]; fun_prop
example : Differentiable ℝ f := by simp only [f]; fun_prop
```

### `grind` for Case Analysis
```lean
-- Powerful automation for case analysis and Finset/card goals
example (hs : s.card = 1) : ∃ a, s = {a} := by grind
example : castSucc i ≠ 0 := by grind [castSucc_ne_zero_iff]
-- For distance/metric goals
example : dist a b < ε := by grind [Real.dist_eq]
-- For cardinality
example (h : n.primeFactors = ∅) : n ≤ 1 := by grind [Finset.card_eq_zero, primeFactors_eq_empty]
```

### `omega` for Arithmetic Goals (PREFERRED)
For impossible arithmetic/inequality goals (including `Fin` inequalities), **prefer `omega`** as the most direct tactic:
```lean
-- omega handles these directly
example (h : n < m) : n + 1 < m + 1 := by omega
example (i : Fin n) : i.val < n := by omega
example (h : a ≤ b) (h' : b < c) : a < c := by omega
```

### Other Power Tactics
- `ring` / `ring_nf` - Polynomial arithmetic
- `linarith` / `nlinarith` - Linear/nonlinear arithmetic
- `omega` - Integer/natural arithmetic (PREFERRED for arithmetic)
- `aesop` - Automated proof search
- `grind` - Powerful case analysis automation
- `exact?` / `apply?` - Find applicable lemmas

### Things Handled by Linters (Don't Comment On)
Mathlib's built-in linters catch these automatically - no need to fix manually:
- Long lines (>100 chars)
- Unused arguments/hypotheses
- Unused variables
These will be flagged at PR time; focus on semantic issues instead.

## File Splitting Guidelines

When a file exceeds ~1500 lines, use `/split-file` to split it.

### Splitting Strategy

**Step 1: Group by naming prefix**
Declarations about the same object share naming prefixes:
- `cauchyPrincipalValue*` → `CauchyPrincipalValue.lean`
- `residue*`, `Residue*` → `Residue.lean`
- `integral_*` → `Integration.lean`

**Step 2: Choose structure based on size**

For 1500-3000 lines:
```
Module/
├── Basic.lean      -- Definitions + core lemmas
└── Theorems.lean   -- Main results (imports Basic)
```

For >3000 lines:
```
Module/
├── Defs.lean       -- Pure definitions
├── GroupA.lean     -- Lemmas about object A
├── GroupB.lean     -- Lemmas about object B
└── Main.lean       -- Main theorems (imports all)
```

**Step 3: Respect dependencies**
- Lower files import higher files, never vice versa
- No circular imports
- Each file must compile independently

### Example Split

```
Before: ResidueTheory.lean (3000 lines)

After:
ResidueTheory/
├── CauchyPrincipalValue.lean  -- PV definitions & lemmas
├── Residue.lean               -- Residue definitions & lemmas
└── ResidueTheorem.lean        -- Main theorems (imports above)
```

## PR Feedback RAG System

We have a **RAG (Retrieval Augmented Generation) system** built from 4,600+ PR review comments.
Use it to find relevant examples for the specific code you're working on.

### Using the RAG System

**Option 1: MCP Server** (if configured in `.mcp.json`)
```
search_golf_examples(code="have h := foo; simp [h]")  # Find similar examples
search_by_pattern(pattern="use_grind")                # Find grind transformation examples
search_by_topic(topics=["continuity"])                # Find topic-specific examples
get_mathlib_quality_principles()                      # Get core quality rules
```

**Option 2: Query Script**
```bash
python3 scripts/query_rag.py --code "simp only [foo]; exact bar" --limit 5
python3 scripts/query_rag.py --pattern use_grind --limit 5
python3 scripts/query_rag.py --tactics simp have exact --limit 5
python3 scripts/query_rag.py --topic continuity --limit 5
```

### Available Patterns for RAG Queries
- `simp_to_simpa` - Converting simp to simpa
- `use_grind` - Using grind tactic (50 examples)
- `use_fun_prop` - Using fun_prop (22 examples)
- `use_aesop` - Using aesop (31 examples)
- `use_omega` - Using omega (3 examples)
- `term_mode` - Converting to term mode (16 examples)
- `remove_redundant` - Removing unnecessary code (24 examples)

### Static Reference Files

**Key document:**
- `references/mathlib-quality-principles.md` - **Comprehensive quality guide** from PR analysis

**Curated examples:**
- `data/pr_feedback/curated_examples.md` - Best before/after examples with principles
- `data/pr_feedback/rag_index_focused.json` - Focused index with 891 golf examples

**Raw data (4,600+ items):**
- `data/pr_feedback/rag_index.json` - Full searchable index (1,905 useful examples)
- `data/pr_feedback/proof_golf_feedback.json` - All proof golf suggestions (2,786 items)
