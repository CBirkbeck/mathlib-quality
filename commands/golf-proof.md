# /golf-proof - Proof Optimization

Optimize and shorten Lean proofs while maintaining correctness and readability.

## Usage

```
/golf-proof [theorem_name]
/golf-proof [file_path:line_number]
/golf-proof --all [file_path]
```

## Workflow

### Step 1: Identify Target

Locate the proof to optimize:
- By theorem name: Search for declaration
- By location: Go to specific line
- All mode: Process each theorem in file

### Step 2: Analyze Current Proof

Use LSP tools to understand the proof:
```
lean_goal at each tactic step
lean_hover_info on key terms
```

Document:
- Current proof length (lines, tactics)
- Proof structure (linear, branching, nested)
- Key lemmas used

### Step 3: Try Automation

Test if automation tactics can replace manual steps:

```lean
-- Try these in order of power/speed tradeoff
lean_multi_attempt with:
- "rfl"
- "trivial"
- "simp only [...]"
- "ring"
- "linarith"
- "omega"
- "aesop"
- "decide" / "native_decide"
```

### Step 4: Apply Optimizations

Common golfing patterns:

**Term mode conversion:**
```lean
-- Before
theorem foo : P := by
  exact h

-- After
theorem foo : P := h
```

**Inline simple have:**
```lean
-- Before
theorem foo : Q := by
  have h := f x
  exact g h

-- After
theorem foo : Q := g (f x)
```

**Use library lemmas:**
```lean
-- Before
theorem foo : a + b = b + a := by
  ring

-- After
theorem foo : a + b = b + a := add_comm a b
```

**Combine tactics:**
```lean
-- Before
theorem foo : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- After
theorem foo : P ∧ Q := ⟨hp, hq⟩
```

### Step 5: Verify Correctness

After each change:
1. Check with `lean_diagnostic_messages`
2. Verify no new errors introduced
3. Check proof still type-checks

### Step 6: Compare Results

Show before/after:

```
## Golf Results: theorem_name

### Before (12 lines, 8 tactics)
```lean
theorem foo (h : P → Q) (hp : P) : Q ∧ Q := by
  have hq : Q := h hp
  constructor
  · exact hq
  · exact hq
```

### After (1 line, term mode)
```lean
theorem foo (h : P → Q) (hp : P) : Q ∧ Q := ⟨h hp, h hp⟩
```

### Reduction
- Lines: 12 → 1 (92% reduction)
- Tactics: 8 → 0 (term mode)
- Readability: Maintained ✓
```

## Automation Tactics Reference

| Tactic | Use Case | Speed |
|--------|----------|-------|
| `rfl` | Definitional equality | Instant |
| `trivial` | Simple goals | Fast |
| `simp only [...]` | Rewriting with lemmas | Medium |
| `ring` | Polynomial equalities | Fast |
| `linarith` | Linear arithmetic | Medium |
| `omega` | Integer arithmetic | Medium |
| `aesop` | General search | Slow |
| `decide` | Decidable props | Varies |

## Search for Better Proofs

Use search tools to find library lemmas:

```
lean_leansearch "sum of two even numbers is even"
lean_loogle "(?a → ?b) → List ?a → List ?b"
lean_exact? / lean_apply?
```

## Guidelines

### Do Golf
- Unnecessary `have` blocks
- Verbose tactic sequences replaceable by automation
- Multiple `exact` calls on simple terms
- Redundant type annotations

### Don't Golf
- Proofs that become unreadable
- Educational proofs (where steps are the point)
- Proofs where readability aids maintenance
- Working proofs just to save 1-2 lines

### Quality Check
A good golfed proof should be:
1. **Correct** - Still proves the theorem
2. **Readable** - Intent is clear
3. **Maintainable** - Won't break easily
4. **Efficient** - Compiles reasonably fast

## Examples

### Example 1: Automation
```lean
-- Before
theorem nat_add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => simp [Nat.succ_add, ih]

-- After
theorem nat_add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b
```

### Example 2: Term Mode
```lean
-- Before
theorem and_imp (h : P ∧ Q → R) : P → Q → R := by
  intro hp hq
  apply h
  constructor
  · exact hp
  · exact hq

-- After
theorem and_imp (h : P ∧ Q → R) : P → Q → R := fun hp hq => h ⟨hp, hq⟩
```

### Example 3: Simp Lemmas
```lean
-- Before
theorem set_mem_union (h : x ∈ s) : x ∈ s ∪ t := by
  left
  exact h

-- After
theorem set_mem_union (h : x ∈ s) : x ∈ s ∪ t := Or.inl h
-- Or using simp
theorem set_mem_union (h : x ∈ s) : x ∈ s ∪ t := by simp [h]
```
