---
name: overview
description: Generate project declaration inventory for consolidation analysis
---

# /overview - Deep Project Review

A slow, methodical review of the entire project. Produces a comprehensive inventory of every
declaration, then performs deep analysis to find: moral duplications, generalization opportunities,
missing API, and junk. **This is not a quick scan. Take all the time needed. Do not skip steps.**

## Usage

```
/overview [directory_or_file]
```

Output: writes `PROJECT_OVERVIEW.md` in the project root.

---

## Philosophy

This command serves the same role as a senior mathematician reviewing a paper before submission:
- Are the definitions at the right level of generality?
- Are there lemmas that are morally the same and should be unified?
- Is there missing API that would make proofs cleaner?
- Are there definitions that shouldn't exist (duplicating mathlib or too specific)?
- Could results be stated more generally (rings instead of fields, etc.)?

**Take your time.** Read proofs carefully. Think about the mathematics, not just the syntax.

---

## Phase 1: Inventory (Per-File Workers)

### Step 1: Find Files

Find all `.lean` files (excluding `.lake/`, `build/`):

```bash
find . -name "*.lean" -not -path "./.lake/*" -not -path "./build/*" | sort
```

### Step 2: Dispatch Per-File Inventory Agents

For each file, dispatch a worker agent. **Each worker must read the entire file carefully.**

**Worker prompt:**

```
You are creating a detailed inventory of [file_path]. Read the ENTIRE file carefully.

For EVERY declaration (def, lemma, theorem, instance, structure, class, abbrev),
produce an entry in this format:

### `[kind] [name]`
- **Type**: [full type signature, abbreviated only if >3 lines]
- **What**: [1-2 sentences in plain mathematical language — what this defines/proves]
- **How**: [1-2 sentences — key proof technique or construction. Name the mathematical
  argument, not just tactics. E.g., "Uses dominated convergence with the bound from
  `norm_le_of_compact`" not just "by simp"]
- **Hypotheses**: [list the key mathematical assumptions — what does this need to work?
  E.g., "Requires f to be continuous on a compact set K"]
- **Uses from project**: [list EVERY other declaration from THIS project used in the
  proof/definition body. Be thorough — grep for each project declaration name]
- **Used by**: [which other declarations in this file USE this one? If none, say "unused in file"]
- **Visibility**: [public / private / scoped]
- **Lines**: [line range, proof length]
- **Notes**: [any of: set_option present, proof >30 lines, sorry present, TODO comments]

IMPORTANT:
- Read proofs carefully enough to describe the mathematical argument, not just list tactics
- "Uses from project" must be complete — search for every project declaration name in the proof
- "Hypotheses" should describe the mathematical conditions, not just list Lean types

At the end, add:

### File Summary
- Total declarations: N (X defs, Y lemmas/theorems, Z instances)
- Key API (used by 3+ others): [list]
- Unused declarations (not used by anything in this file): [list]
- Declarations with sorry: [list]
- Declarations with set_option: [list]
- Proofs >30 lines: [list with line counts]
```

Dispatch file workers in parallel.

### Step 3: Assemble Inventory

Collect all worker outputs. Write the inventory section of `PROJECT_OVERVIEW.md`.

Add a cross-file dependency section:
- For each file, list project-internal imports
- Grep for declaration names across files to find cross-file usage

---

## Phase 2: Deep Analysis (Sequential — Do Not Rush)

**This phase is the core value of /overview. Do it carefully.**

After the inventory is complete, perform each analysis step below. For each step, read through
the ENTIRE inventory and think about the mathematics. Do not skim.

### Step 4: Deep Duplication Detection

**Goal: Find lemmas that are morally the same and should be unified.**

Surface-level duplication (same name, same type) is easy. The hard part is finding lemmas that
PROVE THE SAME THING in slightly different ways or with slightly different hypotheses.

For EACH pair of lemmas in the project, ask:
1. **Do they prove the same mathematical fact?** (even if stated differently)
2. **Is one a special case of the other?** (e.g., one for ℝ, one for ℂ, but the proof works for any field)
3. **Do they have the same proof structure?** (same sequence of mathematical steps, different objects)
4. **Could they be unified into a single parametric lemma?**

**How to check:**
- Compare the type signatures — are they the same modulo variable names?
- Compare the hypotheses — does one have strictly weaker assumptions?
- Compare the proofs — is the mathematical argument the same?
- Check: if we generalized the types, would both follow from one lemma?

**Output format:**

```markdown
### Moral Duplications

1. **`norm_bound_f` ≈ `norm_bound_g`**
   - File: Foo.lean lines 45, 80
   - Both prove `‖_ x‖ ≤ C` with the same argument (compactness + continuity)
   - Differ only in the function (f vs g) — same proof structure
   - **Action**: Unify into `norm_bound_of_continuous_on_compact (φ : X → Y) ...`

2. **`foo_integrable` ≈ `bar_integrable`**
   - Files: Foo.lean line 100, Bar.lean line 50
   - Both establish integrability via dominated convergence with similar bounds
   - `bar_integrable` has strictly weaker hypotheses
   - **Action**: Keep `bar_integrable`, derive `foo_integrable` as a corollary

3. **`custom_triangle_ineq` ≈ mathlib's `norm_add_le`**
   - File: Helpers.lean line 30
   - Proves the triangle inequality for our specific norm — but mathlib already has this
   - **Action**: Delete, use `norm_add_le` directly
```

### Step 5: Generalization Analysis

**Goal: Find where results could be stated more generally.**

Mathlib wants the most general version of every result. For each definition and key theorem:

1. **What algebraic structure does it actually need?**
   - Is it stated for `ℝ` but works for any `OrderedField`?
   - Is it stated for `ℂ` but works for any `NontriviallyNormedField`?
   - Is it stated for `Field` but works for `CommRing` or even `Semiring`?
   - Is it stated for `TopologicalSpace` but works for `UniformSpace`?

2. **Search the mathematical literature** to check generality:
   - Use web search: "[theorem name] generalization" or "[concept] for rings"
   - Check: in what generality is this result known in mathematics?
   - Look at standard references (e.g., Bourbaki, Lang, Rudin) for the general statement
   - Check mathlib: does mathlib already have a more general version?

3. **Check the proof** — does it actually use field-specific properties?
   - If a proof only uses `add_comm` and `mul_assoc`, it works for `CommSemiring`
   - If a proof uses `inv_mul_cancel`, it needs a `DivisionRing`
   - If a proof uses `abs_le`, it needs a `LinearOrderedField`

**How to search literature:**
- WebSearch: "in what generality does [theorem/concept] hold"
- WebSearch: "[concept] for commutative rings" or "[concept] non-commutative"
- Check if the Wikipedia article mentions the general setting
- Check mathlib for existing generalizations: `lean_loogle`, `lean_leansearch`

**Output format:**

```markdown
### Generalization Opportunities

1. **`theorem main_result` — currently for `ℂ`, works for any `NontriviallyNormedField`**
   - Current: `(f : ℂ → ℂ)` with `Differentiable ℂ f`
   - The proof only uses normed field properties, never `ℂ`-specific facts
   - Literature: This result holds for any complete normed field (Bourbaki, FA III.4)
   - Mathlib: `Mathlib.Analysis.NormedField` has the necessary API
   - **Action**: Generalize to `{𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]`
   - **Difficulty**: Low — just change type parameters, proof should work

2. **`def fundamentalDomain` — could work for any Fuchsian group, not just SL₂(ℤ)**
   - Current: Hardcoded for SL₂(ℤ) acting on ℍ
   - Literature: Fundamental domains exist for any properly discontinuous group action
   - Mathlib: `Mathlib.Topology.Algebra.ProperAction` has the framework
   - **Action**: Parametrize over the group, specialize to SL₂(ℤ) as an instance
   - **Difficulty**: High — requires restructuring definitions

3. **`lemma sum_bound` — currently for `Finset`, works for `Finsupp`**
   - The proof never uses that the set is finite, only that the sum is well-defined
   - **Action**: Generalize to `Finsupp` or use `tsum` with summability hypothesis
   - **Difficulty**: Medium
```

### Step 6: API Design Review

**Goal: Find where creating good API would simplify multiple proofs.**

Read through all the proofs in the project. Look for:

1. **Repeated proof patterns**: The same 3-5 line argument appearing in multiple proofs
   - This is a missing lemma that should be extracted
   - Name it well, make it general, place it early in the file

2. **Awkward workarounds**: Places where proofs are longer than they should be because
   a convenient lemma doesn't exist
   - What lemma would make this proof a one-liner?
   - Does mathlib have it? (search with lean_loogle, lean_leansearch)
   - If not, should we create it?

3. **Missing `simp` lemmas**: Theorems that should be tagged `@[simp]` because they
   describe how a definition simplifies
   - Every definition should have basic `simp` lemmas (e.g., `foo_zero`, `foo_one`, `foo_add`)
   - Check: are there manual `simp only [foo_def]` calls that could be replaced by `@[simp]` lemmas?

4. **Missing coercions/instances**: Places where explicit coercions are needed that could
   be automatic
   - Should there be a `Coe` instance?
   - Should there be a `FunLike` instance?

5. **API completeness**: For each definition, does it have the expected companion lemmas?
   - `_zero`, `_one`, `_add`, `_mul` for algebraic structures
   - `_mono`, `_anti` for order-theoretic structures
   - `_continuous`, `_measurable` for analytic structures
   - `ext` lemma for structures

**Output format:**

```markdown
### API Improvements

#### Missing Lemmas (would simplify multiple proofs)

1. **Need: `foo_continuous_of_bar`**
   - Pattern: 4 proofs manually establish `Continuous foo` given `Bar` hypothesis
   - Locations: File1:45, File1:90, File2:30, File3:55
   - All use the same argument: unfold foo, apply Continuous.comp, use bar_continuous
   - **Action**: Add `lemma foo_continuous_of_bar [Bar X] : Continuous foo`
   - Would reduce each proof by 3-5 lines

2. **Need: `@[simp] lemma myDef_zero`**
   - `myDef 0 = 0` is proved inline 6 times across the project
   - **Action**: Add as `@[simp]` lemma near the definition

#### Missing Instances

1. **`FunLike` for `MyMorphism`**
   - Currently using explicit `.toFun` everywhere
   - Adding `FunLike` would allow function application syntax

#### API Completeness Gaps

1. **`def fooBar`** — missing companion lemmas:
   - No `fooBar_zero`, `fooBar_add` (used manually in 3 proofs)
   - No `@[ext]` lemma
```

### Step 7: Junk Identification

**Goal: Find declarations that should be removed.**

For each declaration, check:

1. **Is it used?** — If no other declaration in the project references it, flag it
2. **Is it a wrapper?** — Does it just combine 1-2 mathlib calls? If so, inline it
3. **Does mathlib have it?** — Use `lean_loogle` and `lean_leansearch` to check
4. **Is it too specific?** — Could it be generalized, or should it be inlined?
5. **Is the definition well-chosen?** — Is there a more natural/standard way to define this?

**Output format:**

```markdown
### Junk / Removable Declarations

1. **`def myHelper`** (File1.lean:30) — REMOVE
   - Used only by `main_theorem`, can be inlined as `let`
   - 5 lines, no other dependents

2. **`lemma bridge_result`** (File2.lean:50) — REMOVE (wrapper)
   - Body: `Continuous.comp hf hg` — just a single mathlib call
   - Used at 2 sites — inline the mathlib call directly

3. **`def customNorm`** (Helpers.lean:10) — REPLACE
   - Duplicates `NNNorm` from mathlib
   - Used in 8 places — replace with mathlib's version

4. **`lemma unused_helper`** (File3.lean:200) — REMOVE (dead code)
   - Not referenced anywhere in the project
```

---

## Phase 3: Write Report

Write the complete document to `PROJECT_OVERVIEW.md` with these sections:

```markdown
# Project Overview: [project_name]

Generated: [date]

## Executive Summary
[2-3 paragraphs: what the project does, key findings, top priorities]

## Statistics
- Files: N, Declarations: M (X defs, Y lemmas, Z instances)
- Moral duplications found: D
- Generalization opportunities: G
- Missing API items: A
- Junk declarations: J

---

## Part 1: Declaration Inventory
[Per-file inventory from Phase 1]

## Part 2: Cross-File Dependencies
[Import graph and cross-file usage]

## Part 3: Moral Duplications
[From Step 4 — deep duplication analysis]

## Part 4: Generalization Opportunities
[From Step 5 — with literature references]

## Part 5: API Improvements
[From Step 6 — missing lemmas, instances, completeness]

## Part 6: Junk / Removable
[From Step 7 — with clear action items]

---

## Recommended Action Plan

### Priority 1: Quick Wins (can do now)
[Junk removal, wrapper inlining, simple generalizations]

### Priority 2: API Improvements (significant impact)
[Missing lemmas that would simplify many proofs]

### Priority 3: Generalizations (requires mathematical thought)
[Type parameter generalizations, with difficulty estimates]

### Priority 4: Structural Changes (major refactoring)
[Moral duplication unification, definition redesign]
```

Print a summary to the conversation with the top 5 action items.

---

## Important: This Is a Slow Process

- **Do NOT skim proofs.** Read them. Understand the mathematics.
- **Do NOT skip the literature search.** Check what generality is standard.
- **Do NOT rush the duplication check.** Compare every pair of similar declarations.
- **Do NOT write "flag for later."** Every finding must have a concrete action.
- **Take multiple passes** if needed. It's better to be thorough than fast.

If the project has many files, process them in phases. Quality over speed.

---

## Reference

- `/check-mathlib` — detailed mathlib search for individual declarations
- `/cleanup` — per-file cleanup after implementing overview recommendations
- `/decompose-proof` — decompose long proofs identified in the overview
