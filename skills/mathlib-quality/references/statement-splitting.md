# Statement Splitting — One Conclusion per Declaration

When formalising a result whose statement bundles two or more **independently-provable
conclusions** — a top-level `∧`-chain, a source theorem with numbered parts (i)/(ii)/(iii) or
(a)/(b)/(c), a claim-list "f is continuous, bounded, and attains its bounds" — do **not** state
it as one declaration. State **one lemma per part**, prove the parts separately, and (only when
something genuinely consumes the bundled form) add a thin **assembly lemma** whose whole proof is
the anonymous constructor `⟨part₁, part₂, …⟩`.

This rule is applied at *formalisation time* — statements are born split. Catching a many-`∧`
statement in `/cleanup` weeks later means every intermediate proof, ticket, and progress note was
written against the wrong shape.

## Why (the mathlib rationale)

- **Unusable conjuncts.** `rw`, `simp`, `exact?`, and `apply` cannot reach a conjunct buried in a
  conjunction; consumers are forced into `(h.1).2.1` projection chains that are unreadable and
  break silently when a part is added.
- **Discoverability.** Each part is independently findable by `lean_leansearch`/`loogle` and
  independently citable. A bundled statement hides two theorems under one name.
- **Proof structure.** A bundled statement's proof interleaves unrelated arguments in one tactic
  block (`constructor` + two long branches) — exactly the shape `/cleanup`'s `structure_gate`
  rejects. Split statements give each argument its own focused proof.
- **Review reality.** "Please split this into two lemmas" is one of the most common mathlib
  review comments. Pre-empt it.

## Trigger shapes (split these)

| Shape | Split into |
|-------|-----------|
| `theorem foo : P ∧ Q` | two lemmas (content-named; fallback `foo_left` / `foo_right`) |
| `theorem foo : P ∧ Q ∧ R` (chain) | one lemma per conjunct + optional assembly |
| Source "Theorem N: (a) …; (b) …" | one top-level result per part — never one declaration |
| `theorem foo : (P ↔ Q) ∧ (R ↔ S)` | two iff lemmas |
| `theorem foo : ∀ x, P x ∧ Q x` | `∀ x, P x` and `∀ x, Q x` (splitting under `∀` is sound — the parts share only the binder) |
| ≥3-way equivalence "the following are equivalent" | `List.TFAE` (`tfae_have` / `tfae_finish`), plus standalone corollaries for the most-used single iffs |

## Non-triggers and genuine exceptions (do NOT split naively)

1. **Shared-witness existentials.** `∃ x, P x ∧ Q x` must **never** be split into `∃ x, P x` and
   `∃ x, Q x` — that is a different (weaker) statement; the witness is shared. Preference order:
   - If the witness is canonical or constructible, extract it as a `def` (or `noncomputable def`)
     and state one spec lemma per property:
     ```lean
     noncomputable def fooWitness : X := …
     theorem fooWitness_p : P fooWitness := …
     theorem fooWitness_q : Q fooWitness := …
     ```
   - Otherwise keep the bundled existential as one lemma — standard mathlib style for existence
     results (`exists_…_and_…`). A kept bundle here is correct, not a defect.
2. **Simultaneous-proof bundles (mutual induction).** When the parts are only provable *together*
   (one induction establishing `P n ∧ Q n`), prove the bundle as a `private` auxiliary and expose
   each part publicly by projection — the public API stays split:
   ```lean
   private theorem foo_aux (n : ℕ) : P n ∧ Q n := by induction n …
   theorem foo_p (n : ℕ) : P n := (foo_aux n).1
   theorem foo_q (n : ℕ) : Q n := (foo_aux n).2
   ```
3. **A single `Iff` is one proposition.** `theorem foo_iff : P ↔ Q ∧ R` is not a trigger — the
   `∧` sits under the iff and carries the content. Do not decompose an iff into per-conjunct iffs
   (`P ↔ Q ∧ R` does not imply `P ↔ Q`).
4. **Recurring property packs → structure, not `∧`.** If the same conjunction of properties of
   one object travels through many statements, the right fix is a `structure` / typeclass
   bundling them (mathlib's bundled-morphism idiom), decided at API-design time — not an
   ever-longer `∧`-chain and not N loose lemmas re-quantified everywhere.

Using an exception requires a one-line justification wherever the rule is being enforced (a
decomposition-leaf entry, a ticket, a sub-ticket spawn note).

## The assembly test (binding)

If a bundled form is kept at all, two conditions must hold:

1. **It has a consumer** — the source's later proofs use the bundled form, or a downstream
   declaration genuinely takes the conjunction. No consumer → don't state the bundle.
2. **Its proof is exactly the anonymous constructor**, term mode, one line:
   ```lean
   theorem foo : P ∧ Q ∧ R := ⟨foo_p, foo_q, foo_r⟩
   ```
   If the assembly needs tactics, `refine`, or more than one line, the parts were not actually
   independent — the split was drawn in the wrong place. Re-draw it.

## Naming

- Prefer **content names** per part (`eisenstein_holomorphic`, `eisenstein_modular`) — each part
  is a theorem in its own right and deserves a name describing *its* conclusion.
- The positional fallback `foo_left` / `foo_right` (used by `/cleanup`'s STRUCTURE item) is for
  mechanical splits where the parts have no independent mathematical identity.
- A kept bundle is named with `_and_` per `naming-conventions.md` (`continuous_and_bounded`).

## Worked example

Source: *"Theorem 6.2. Let f : K → ℝ be as above. Then (i) f is continuous; (ii) f is bounded;
(iii) f attains its bounds."*

Bad — one declaration transcribing all three parts:

```lean
theorem f_properties (hK : IsCompact K) :
    Continuous f ∧ (∃ M, ∀ x ∈ K, |f x| ≤ M) ∧ ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  refine ⟨?_, ?_, ?_⟩   -- three unrelated arguments interleaved in one proof block
  …
```

Good — one lemma per part; assembly only if Theorem 6.2 is cited as a whole later:

```lean
theorem f_continuous : Continuous f := …
theorem f_bounded (hK : IsCompact K) : ∃ M, ∀ x ∈ K, |f x| ≤ M := …
theorem f_attains_max (hK : IsCompact K) : ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := …

/-- Source: Theorem 6.2 as stated (assembly). -/
theorem f_properties (hK : IsCompact K) :
    Continuous f ∧ (∃ M, ∀ x ∈ K, |f x| ≤ M) ∧ ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x :=
  ⟨f_continuous, f_bounded hK, f_attains_max hK⟩
```

Note the parts also get **their own minimal hypotheses** — `f_continuous` never needed `hK`. The
bundled version forces every consumer of part (i) to supply compactness it doesn't use; this
hypothesis-minimisation is a fringe benefit of splitting that a bundle can never offer.

## Where this rule is enforced

- **`/develop`** — Phase 1d (design the split), Phase 1e Step 2 item 4 (one leaf per part),
  confidence-gate condition 7 (statement-shape check). Statements are born split.
- **`/beastmode`** — Tier A5 + the sub-ticket template's single-conclusion requirement. Spawned
  sub-tickets are born split; a ticketed bundle is proven via per-part sub-tickets + assembly.
- **`/cleanup`** — Phase 4 item 12 STRUCTURE and `structure_gate` (existing bundles get split).
- **`/decompose-proof`** — Core Rule 1 (dedicated splitting workflow for legacy proofs).
