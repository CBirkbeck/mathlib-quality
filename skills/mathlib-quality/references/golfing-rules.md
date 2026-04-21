# Golfing Rules Checklist

Concrete transformation rules extracted from 3,772 merged mathlib4 PRs.
Apply these to EVERY declaration during cleanup. Try each rule; skip if
it doesn't apply or makes things worse. Verify compilation after each change.

---

## Phase 1: Instant wins (zero risk, always apply)

### 1.1 Remove `by exact` wrapper
```lean
-- BEFORE                        -- AFTER
:= by exact someTerm            := someTerm
```

### 1.2 Remove `by rfl`
```lean
-- BEFORE                        -- AFTER
:= by rfl                       := rfl
```

### 1.3 `rw + exact` → `rwa`
```lean
-- BEFORE                        -- AFTER
rw [h]                           rwa [h]
exact e
```

### 1.4 `simp + exact/assumption` → `simpa using`
```lean
-- BEFORE                        -- AFTER
simp only [foo, bar]             simpa only [foo, bar] using h
exact h
```

### 1.5 Remove trailing `rfl` after `simp`
```lean
-- BEFORE                        -- AFTER
simp [foo]                       simp [foo]
rfl
```

### 1.6 `constructor + exact + exact` → anonymous constructor
```lean
-- BEFORE                        -- AFTER
constructor                      exact ⟨a, b⟩
· exact a
· exact b
```

### 1.7 `apply f; exact h` → `exact f h`
```lean
-- BEFORE                        -- AFTER
apply f                          exact f h
exact h
```

### 1.8 `by_contra + push_neg` → `by_contra!`
```lean
-- BEFORE                        -- AFTER
by_contra h                      by_contra! h
push_neg at h
```

### 1.9 Eta-reduce lambdas
```lean
-- BEFORE                        -- AFTER
fun x => f x                    f
fun x y => g x y                g
```

### 1.10 Inline single-use `have` (no `by`)
```lean
-- BEFORE                        -- AFTER
have h := foo x                  exact bar (foo x)
exact bar h
```

### 1.11 `apply + intro` → `refine + fun`
```lean
-- BEFORE                        -- AFTER
apply antitone_nat_of_succ_le    refine antitone_nat_of_succ_le fun m => ?_
intro m
```

### 1.12 Remove redundant `show`
Remove `show T` when the goal is already `T`. (60 occurrences in data.)

### 1.13 `have + .1/.2` → `obtain ⟨ ⟩`
```lean
-- BEFORE                        -- AFTER
have h := foo x                  obtain ⟨a, b⟩ := foo x
... h.1 ... h.2 ...              ... a ... b ...
```

### 1.14 Merge consecutive `rw`
```lean
-- BEFORE                        -- AFTER
rw [a]                           rw [a, b, c]
rw [b]
rw [c]
```

### 1.15 Unsqueeze terminal `simp only`
Terminal `simp only [...]` should be just `simp` (mathlib convention: don't squeeze terminal simp).
```lean
-- BEFORE (terminal position)    -- AFTER
simp only [foo, bar, baz]        simp
```

### 1.16 Squeeze nonterminal bare `simp`
Nonterminal bare `simp` must become `simp only [...]`. Use `simp?`.

### 1.17 Use dot notation
```lean
-- BEFORE                        -- AFTER
Monotone.comp hf hg              hf.comp hg
And.intro ha hb                  ⟨ha, hb⟩
```

### 1.18 Use `<|` to avoid trailing parens
```lean
-- BEFORE                        -- AFTER
f (by simp)                      f <| by simp
g (fun x => h x)                 g fun x => h x
```

---

## Phase 2: Automation upgrades (try each, keep if it works)

For each multi-line tactic block, try replacing with automation.
Use `lean_multi_attempt` to test several at once.

### 2.1 Try `grind` on the whole proof
The most common reviewer suggestion. `grind` subsumes many tactic chains.
```lean
-- Try replacing the ENTIRE proof body with:
  by grind
  by grind [relevant_lemma₁, relevant_lemma₂]
```

### 2.2 Try deleting tactics before `grind`
`grind` often subsumes preceding steps:
```lean
-- BEFORE                        -- TRY
rw [h]; grind                   grind
simp; grind                     grind
congr 1; grind                  grind
simp [foo] <;> grind            grind [foo]
```

### 2.3 Try `simpa` consolidation
When `simp` is followed by a closing tactic:
```lean
-- BEFORE                        -- AFTER
simp [foo] at h ⊢               simpa [foo] using h
exact h
```

### 2.4 Try `fun_prop`
For ANY goal involving `Continuous`, `Differentiable`, `Measurable`,
`ContDiff`, `AEMeasurable`, or similar function properties:
```lean
-- BEFORE (multi-line)           -- AFTER
apply Continuous.comp            fun_prop
exact continuous_fst
exact continuous_snd.norm
```
Use `fun_prop (disch := grind)` if `fun_prop` alone fails.

### 2.5 Try `positivity`
For ANY goal of the form `0 < x`, `0 ≤ x`, `x ≠ 0` (where derivable from structure):
```lean
-- BEFORE                        -- AFTER
linarith [pi_pos]                positivity
```

### 2.6 Try `gcongr`
For inequality goals in `calc` blocks or goals needing monotonicity:
```lean
-- BEFORE                        -- AFTER
apply add_le_add_right           gcongr
apply div_le_div_of_nonneg
apply mul_le_mul ...
```

### 2.7 Try `omega` / `lia`
For `Nat`/`Int` arithmetic goals. Prefer `lia` over `omega` in new code.
```lean
-- BEFORE                        -- AFTER
linarith                         omega  -- or lia
cases n <;> simp
```

### 2.8 Try `aesop`
For logic, membership, and simple algebraic structure goals:
```lean
-- BEFORE                        -- AFTER
intro x; simp [map_zero]         aesop
```

### 2.9 Try `norm_num` / `norm_cast`
For concrete numeric computation or cast goals:
```lean
-- BEFORE                        -- AFTER
show (3 : ℕ) ≤ n from by decide  by norm_num
```

### 2.10 Try `decide` / `decide +kernel`
For decidable propositions (finite computation):
```lean
-- BEFORE                        -- AFTER
unfold Abundant; simp; norm_num   decide +kernel
```

### 2.11 Try `field_simp; ring`
For algebraic identities involving denominators:
```lean
-- BEFORE                        -- AFTER
rw [div_eq_iff (pow_ne_zero ...)] field_simp; ring
ring
```

### 2.12 Try `linear_combination`
For EVERY proof ending in `ring` or `ring_nf` that has hypotheses in context.
Closes goals that `ring` can't when hypotheses are needed.

### 2.13 Try `wlog` for symmetric cases
When two case branches have near-identical proofs:
```lean
-- BEFORE                        -- AFTER
rcases le_or_gt 0 x with h | h   wlog! h : 0 ≤ x
· <proof>                        · simpa [neg_lemma] using @this (-x) ...
· <symmetric proof>              · <one proof>
```

### 2.14 Try collapsing `calc` to term mode
Two-step `calc` blocks can often be composed:
```lean
-- BEFORE                        -- AFTER
calc a ≤ b := h1                 le_trans h1 h2
     _ ≤ c := h2
```

### 2.15 Close multiple goals with `<;>`
When `refine` produces multiple similar goals:
```lean
-- BEFORE                        -- AFTER
refine ⟨?_, ?_, ?_⟩             refine ⟨?_, ?_, ?_⟩ <;> grind [def, key_fact]
· grind [def, key_fact]
· grind [def, key_fact]
· grind [def, key_fact]
```

---

## Phase 3: Cleanup (style and structure)

### 3.1 `erw` → `rw`
Try `rw` first; only use `erw` when `rw` genuinely fails.

### 3.2 `continuity` / `measurability` → `fun_prop`
These legacy tactics are being replaced.

### 3.3 `omega` → `lia`
mathlib is migrating to `lia`. Use it in new code.

### 3.4 `rcases ... with rfl` auto-substitutes
No need for subsequent `simp [h]` when `rfl` already substituted.

### 3.5 Register lemmas for automation
Consider adding attributes to make lemmas available to automation:
- `@[simp]` for the simplifier
- `@[grind =]` for grind
- `@[fun_prop]` for fun_prop
- `@[aesop]` for aesop

### 3.6 `simp_all` over `simp_all only`
For closing goals, `simp_all` is preferred over `simp_all only`.

### 3.7 Remove `set_option maxHeartbeats`
Never acceptable in mathlib. Fix the proof instead.

---

## What doesn't golf well (don't waste time)

- Analysis boilerplate (integrability/measurability chains) — needs new API
- `grind` with `zpow`, `Even`/`Odd`, or cast arithmetic — known limitation
- Dominated convergence sub-proofs — already near-minimal
- `grind` in large contexts — can timeout; keep standalone lemmas

## Minimum value filter

1-line savings are only worth making if:
- Zero-risk syntax cleanup (e.g., `by exact` → term), OR
- They also improve clarity or performance

Don't churn code for marginal compression.
