---
name: golf-proof
description: Optimize and shorten proofs
---

# /golf-proof - Proof Optimization

Optimize and shorten Lean proofs. **Goal: One-liners. Brevity trumps readability.**

## Usage

```
/golf-proof [theorem_name]
/golf-proof [file_path:line_number]
/golf-proof --all [file_path]
```

## Agent Integration

This command uses **three complementary approaches**:

1. **Quick pass (mathlib-golfer)** - Apply general patterns: inline `have`, term mode, etc.
2. **Deep pass (deep-golfer)** - Line-by-line analysis using PR feedback patterns
3. **Compiler-guided (lean4-proof-golfer)** - Iterative optimization with LSP feedback

### When to Use Each

| Situation | Agent |
|-----------|-------|
| Quick cleanup | mathlib-golfer |
| Thorough optimization | deep-golfer (line-by-line) |
| Stubborn proofs | lean4-proof-golfer |
| Best results | All three sequentially |

### Deep Golfer Approach

For thorough golfing, use the **deep-golfer** which:
1. Reads PR feedback data (`data/pr_feedback/curated_examples.md`)
2. Goes through every 3-5 lines of each proof
3. Checks each line against 12+ specific PR patterns
4. Tries `lean_multi_attempt` on chunks
5. Documents which PR pattern each change matches

See `agents/deep-golfer-prompt.md` for the full methodology.

## Statistical Rules (from 6979 PR reviews)

Based on analysis of mathlib PR feedback, these are the most impactful changes:

| Pattern | Frequency | Action |
|---------|-----------|--------|
| Remove `simp` | 311 | Replace with `grind`, `simpa`, or term mode |
| Remove `exact` | 311 | Convert to term mode |
| Remove `rw` | 276 | Combine into `simp only` or eliminate |
| Remove `rfl` | 169 | Use `rfl` term, not `by rfl` |
| Inline `have` | 77 | Inline single-use values |
| Use `grind` | 1144 | Replace multi-step with automation |

## Workflow

### Step 0: Strip Inline Comments

**Mathlib proofs should be comment-free.** Before golfing:
1. Remove ALL inline comments from proofs
2. If mathematical explanation is important, add a ONE-SENTENCE docstring to the theorem
3. Do NOT add docstrings to helper lemmas - only key public theorems

```lean
-- BEFORE (bad)
theorem foo : P := by
  -- First we establish the bound using continuity
  have hbound := continuous_bound hf
  -- Now apply dominated convergence
  -- This works because g is integrable
  exact dominated_conv hbound hg

-- AFTER (good)
/-- Foo follows from dominated convergence with the continuity bound. -/
theorem foo : P := by
  have hbound := continuous_bound hf
  exact dominated_conv hbound hg
```

### Step 1: Inline Simple `have` Statements

**CRITICAL RULE**: Inline `have foo := bar` (simple invocations) unless used multiple times.

```lean
-- PATTERN: have foo := bar (just invoking another result)
-- RULE: Inline it unless used 2+ times

-- BEFORE (bad)
theorem foo : P := by
  have h1 := lemma1 x
  have h2 := lemma2 y
  have h3 := lemma3 z
  exact combine h1 h2 h3

-- AFTER (good) - inline the single-use haves
theorem foo : P := combine (lemma1 x) (lemma2 y) (lemma3 z)
```

**EXCEPTION**: Keep `have foo : T := by proof` when it requires an actual proof:
```lean
-- This is OK to keep - it has a proof block
have hbound : ‖f x‖ ≤ C := by
  apply norm_le_of_continuous
  exact hf.continuousOn
```

**Decision tree for `have`:**
1. `have foo := bar` (no type, no `by`) → **INLINE IT** (unless used 2+ times)
2. `have foo : T := bar` (typed, no `by`) → **INLINE IT** (unless used 2+ times)
3. `have foo := by ...` or `have foo : T := by ...` → **KEEP** (has proof content)
4. Any `have` used 2+ times → **KEEP** (avoid duplication)

### Step 2: Load Relevant Examples

Based on what you see in the proof, read the appropriate example file:

- **Proof has `have` blocks** → Read `examples/inline_have.md`
- **Proof has `by exact`** → Read `examples/term_mode.md`
- **Proof has `simp` chains** → Read `examples/simp_golf.md`
- **Proof is multi-step** → Read `examples/automation.md`

### Step 3: Apply Transformations (Priority Order)

**Instant wins (always do):**
1. `by exact h` → `h`
2. `by rfl` → `rfl`
3. `fun x => f x` → `f` (eta-reduce)
4. Remove trailing commas in simp lists
5. **Inline single-use `have foo := bar`**

**High-impact (try first):**
6. Try `grind` on the whole proof
7. Try `fun_prop` for continuity/differentiability
8. `have h := x; exact f h` → `exact f x` or just `f x`
9. `simp; exact h` → `simpa using h`

**Medium-impact:**
10. `rw [a]; rw [b]` → `rw [a, b]`
11. `constructor; exact a; exact b` → `⟨a, b⟩`
12. `intro h; exact f h` → `fun h => f h` or just `f`

**Use `lean_multi_attempt` to test:**
```lean
lean_multi_attempt with:
- "grind"
- "aesop"
- "simp"
- "ring"
- "omega"
- "fun_prop"
```

### Step 4: Verify

After each change:
1. `lean_diagnostic_messages` - check no errors
2. Continue golfing until no more reductions possible

### Step 5: Report Results

```markdown
## Golf Results: theorem_name

### Before (N lines, M tactics)
```lean
[original proof]
```

### After (1 line, term mode)
```lean
[golfed proof]
```

### Reduction
- Lines: N → 1 (X% reduction)
- Tactics: M → 0
```

## Quick Reference

### `have` Inlining Rules

| Pattern | Action | Reason |
|---------|--------|--------|
| `have h := foo x` | **INLINE** | Simple invocation |
| `have h : T := foo x` | **INLINE** | Typed but still simple |
| `have h := by ...` | **KEEP** | Has proof content |
| `have h : T := by ...` | **KEEP** | Has proof content |
| Any `have` used 2+ times | **KEEP** | Avoid duplication |

### Automation Tactics

| Tactic | Use Case |
|--------|----------|
| `grind` | Finset/card, case analysis, membership |
| `fun_prop` | Continuity, differentiability, measurability |
| `omega` | ℕ/ℤ arithmetic |
| `ring` | Polynomial equalities |
| `aesop` | Logical goals |
| `simp` | Rewriting (terminal only unsqueezed) |

### Term Mode Conversions

| Tactic Pattern | Term Mode |
|----------------|-----------|
| `by exact h` | `h` |
| `by rfl` | `rfl` |
| `by constructor; exact a; exact b` | `⟨a, b⟩` |
| `by intro h; exact f h` | `f` or `fun h => f h` |
| `by cases h; exact a; exact b` | `h.casesOn (fun _ => a) (fun _ => b)` |

### Common Replacements

| Before | After |
|--------|-------|
| `obtain ⟨a, rfl⟩ := h; exact ⟨a, rfl⟩` | `grind` |
| `simp only [...]; exact h` | `simpa [...] using h` |
| `rw [h]; rfl` | `h` or `h ▸ rfl` |
| `have h := f x; exact g h` | `g (f x)` |
| `have h := f x; have h2 := g h; exact h2` | `g (f x)` |
| `apply f; exact h` | `f h` |

## Guidelines

**Always golf:**
- Inline comments (remove entirely)
- Single-use `have foo := bar` statements
- Verbose tactic sequences
- Multi-line proofs
- Any proof longer than necessary

**When to decompose instead:**
If a proof is >50 lines and automation doesn't help, use `/decompose-proof`:
- Extract `have foo : T := by proof` blocks as private helpers
- Extract case splits as separate lemmas
- Consolidate shared logic across theorems

**Goal:** Minimize proof length. One-liners are ideal. Brevity trumps readability.

A golfed proof should be:
1. **Correct** - Still proves the theorem
2. **Short** - Minimum lines/tactics possible
3. **Fast** - Compiles in reasonable time
4. **Comment-free** - No inline comments in proofs

**Main theorems after decomposition should be <15 lines**, reading as clear outlines.
