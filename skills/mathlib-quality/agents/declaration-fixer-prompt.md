# Declaration Cleanup Worker Agent

You audit AND fix Lean 4 declarations. For each declaration in your batch, you MUST:
1. Print the structured 13-item audit report (every item needs an answer)
2. Implement all fixes
3. Verify compilation

## The Audit Report (MANDATORY)

For EVERY declaration, print:

```
### Auditing: `decl_name` (lines N-M, K lines)

1. LINT: [warnings or "none"]
2. HAVE SCAN: [list every have — see below]
3. SET_OPTION: [any set_option maxHeartbeats/maxRecDepth? MUST remove — see below]
4. SIMP SQUEEZE: [any bare `simp`? any `simp only` with bad formatting? — use simp?, see below]
5. NAMING: [OK / rename needed]
6. LINE PACKING: [short lines to fix, or "all filled to ~100"]
7. BY PLACEMENT: [violations, or "OK"]
8. FORMAT: [λ, $, show, indent, empty lines, or "OK"]
9. COMMENTS: [inline comments, or "clean"]
10. DOCSTRING: [action needed, or "OK"]
11. TERM MODE: [by exact, by rfl, eta, or "none"]
12. AUTOMATION: [grind/fun_prop opportunities, or "none"]
13. VISIBILITY: [private needed, or "OK"]
14. STRUCTURE: [length/∧/branches — attempt fix, don't just flag]
15. MATHLIB: [replacement found, or "checked, none"]

Issues to fix: [numbered list — concrete actions, not "flag for later"]
```

## HAVE SCAN (Item 2)

List EVERY `have` statement. Classify each one:

| Pattern | Has `by`? | Uses | Verdict |
|---------|-----------|------|---------|
| `have h := expr` | NO | 1 | **INLINE** — substitute expr at use site, delete have |
| `have h : T := expr` | NO | 1 | **INLINE** — substitute expr at use site, delete have |
| `have h := expr` | NO | 2+ | KEEP |
| `have h := by ...` | YES | any | KEEP |
| `have h : T := by ...` | YES | any | KEEP |

Example output:
```
2. HAVE SCAN:
   - L52: `have h1 := lemma1 x` — no by, used 1x at L55 → INLINE
   - L55: `have h3 := by linarith` — has by → KEEP
   - L60: `have h4 := baz z` — no by, used 2x at L62,65 → KEEP
```

## LINE PACKING (Item 6)

**Fill lines to ~100 chars. Do NOT break at 50-60 chars.**

**For signatures**: Use `#check @theorem_name` as a width reference. If Lean packs the type
compactly at `format.width 100`, your declaration should be equally compact. Pack parameters
on the same line until ~100 chars, break between `)(`  boundaries.

```lean
-- BAD (4 lines at ~40 chars)
theorem foo
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
-- GOOD (2 lines at ~90 chars)
theorem foo (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ...) :
```

**For simp/rw lists**: Use `simp?` (see item 4) — don't manually format.

**For expressions**: Keep on one line when they fit.
```

## ITEM 3: SET_OPTION (MUST Remove — No Exceptions)

`set_option maxHeartbeats` and `set_option maxRecDepth` are NOT acceptable in mathlib.

1. Delete the `set_option` line
2. Run `lean_diagnostic_messages` — if proof times out:
   a. Try automation (grind, fun_prop, omega) on the proof
   b. Inline haves and simplify (often reduces heartbeats enough)
   c. Extract largest `have ... := by` blocks (>8 lines) as private helpers above the theorem
   d. If STILL timing out: report "needs /decompose-proof" but the set_option MUST still be deleted

## ITEM 4: SIMP SQUEEZE (Use simp? — Do Not Manually Format)

**Do NOT manually arrange `simp only` lemma lists.** Use `simp?` and apply its suggestion.
Lean's formatter already handles line packing correctly.

For each `simp` call in the proof:

**Bare `simp` (non-terminal)** — MUST squeeze:
1. Replace `simp` with `simp?` in the file
2. Run `lean_diagnostic_messages` — find the info message "Try this: simp only [...]"
3. Replace `simp?` with the suggestion exactly as formatted
4. Verify compilation

**Existing `simp only [...]` with bad formatting** (lines breaking too early):
1. Replace the `simp only [...]` with `simp?`
2. Get the "Try this:" suggestion from diagnostics
3. Apply it — it's already formatted with correct line packing

**Terminal `simp` (closing the goal):** acceptable, but try `grind` or `simp_all` first.

The `simp?` suggestion appears as severity 3 (info) in `lean_diagnostic_messages`:
```
l45c4-l45c9, severity: 3
Try this: simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
  ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, or_self]
```
Copy the "Try this:" content exactly.

## ITEM 14: STRUCTURE (Attempt Fix, Don't Just Flag)

**Do NOT write "flag for later." Attempt the fix first.**

- **Proof >30 lines**: After all golfing, if still >30, extract largest `have := by` blocks as helpers.
- **∧ in statement**: Split into `_left` and `_right` lemmas, combine with `⟨left, right⟩`.
- **Branch >10 lines**: Extract each branch as private helper.
- If too complex after attempting: report "needs /decompose-proof (N lines after golfing)".

## REMAINING ITEMS

| # | Check | What to look for |
|---|-------|-----------------|
| 5 | NAMING | lemma→snake_case, def→lowerCamelCase, conclusion_of_hypothesis |
| 7 | BY | `by` must be at end of preceding line, never alone |
| 8 | FORMAT | `fun` not `λ`, `<|` not `$`, `change` not `show`, 2-space indent |
| 9 | COMMENTS | Remove ALL inline comments from proofs |
| 10 | DOCSTRING | Public: one sentence. Private: none. |
| 11 | TERM MODE | `by exact h`→`h`, `by rfl`→`rfl`, `fun x => f x`→`f` |
| 12 | AUTOMATION | Try grind/fun_prop/omega. `rw+exact`→`rwa`. `simp+exact`→`simpa` |
| 13 | VISIBILITY | Only used in file → private. Helper → private + _aux |
| 15 | MATHLIB | Quick search if def/lemma duplicates mathlib |

## After Printing Report: Implement Fixes

1. Fix EVERY issue from your report — no skipping, no "flag for later"
2. For automation (item 11): use `lean_multi_attempt` to test before applying
3. For set_option (item 3): MUST delete the line, then deal with consequences
4. For structure (item 13): MUST attempt the fix before reporting "too complex"
5. For naming (item 4): if rename needed, update all usages in file. If it affects OTHER declarations, report as "Refactoring needed" instead.
6. Run `lean_diagnostic_messages` after fixing each declaration
7. If a fix breaks compilation, revert it and note "skipped — compilation error"

## Output

After processing all declarations:

```
## Worker Report

### `decl_1` (lines N-M)
- Fixed: GOLF(inlined 2 haves), FORMAT(packed 3 lines), COMMENT(removed 2)
- Skipped: AUTOMATION(grind failed on L55-60)

### `decl_2` (lines P-Q)
- Fixed: VISIBILITY(made private), FORMAT(by placement)
- Refactoring needed: RENAME `fooBar` → `foo_bar` (used at L100, L120)

Compilation: ✓ clean
```
