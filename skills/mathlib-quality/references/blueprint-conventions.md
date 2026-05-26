# Blueprint LaTeX Conventions

Read this in full before authoring blueprint entries. The conventions here come from
the published blueprints of Sphere-Packing, FLT-Regular, PFR, Carleson, and the
upstream `leanblueprint` examples. Following them keeps the dep-graph valid and the
prose readable.

---

## The `leanblueprint` block vocabulary

Every blueprint chunk is one of:

| Environment | When to use | Takes `\begin{proof}`? |
|---|---|---|
| `\begin{definition}` | An object is defined (a function, a set, a structure, an instance). | No |
| `\begin{theorem}` | A named main result. | Yes |
| `\begin{lemma}` | An intermediate result used by other entries. | Yes |
| `\begin{proposition}` | A result that's neither headline nor mere helper — a named statement worth quoting on its own. | Yes |
| `\begin{corollary}` | A trivial specialisation or direct consequence. | Optional |
| `\begin{remark}` | Discussion, motivation, alternative formulation. No `\lean{}` required. | No |
| `\begin{notation}` | Introduces shorthand used across multiple chunks. | No |

Match the kind to the **mathematical** role, not the Lean keyword. A Lean `theorem`
that's used only as a helper inside one file becomes a `\begin{lemma}`. A Lean `def`
that introduces a key conceptual object becomes a `\begin{definition}` even if its
Lean signature is opaque.

---

## The four annotations: `\label`, `\lean`, `\uses`, `\leanok`

Every blueprint entry takes up to four leanblueprint-specific commands inside the
environment opening:

### `\label{<label>}` — required

The dep-graph node ID. Convention:

- `def:` prefix for definitions
- `thm:` for theorems
- `lem:` for lemmas
- `prop:` for propositions
- `cor:` for corollaries

The body of the label uses **kebab-case** for multi-word identifiers, matching the
mathematical name rather than the Lean name:

```latex
\label{def:q-expansion}              % not def:qExpansion
\label{thm:modular-forms-finite-rank} % not thm:modularFormsFiniteRank
\label{lem:mertens-bound}             % not lem:mertensBound
```

Labels must be globally unique across the whole `blueprint/src/` tree. The Phase-5
cross-link pass enforces this; pick descriptive names from the start to avoid clashes.

### `\lean{<qualified.Lean.Name>}` — required for everything except `remark` / `notation`

The Lean declaration this entry corresponds to. **Qualified, exactly as Lean spells
it.** Examples:

```latex
\lean{ModularForm.qExpansion_mul}                    % a theorem in ModularForm namespace
\lean{ModularForm.qExpansion_mul_coe}                % …
\lean{Modular.Discriminant}                          % a definition
\lean{ModularForm.instAddCommGroup}                  % an instance (yes, instances get \lean{} too)
```

`leanblueprint checkdecls` verifies every `\lean{X}` resolves in the compiled Lean
project. A blueprint chunk with no `\lean{}` is silently dropped from the dep-graph;
don't ship one unless it's a `remark` or `notation`.

### `\uses{<label1, label2, …>}` — comma-separated, optional but heavily used

Lists the dep-graph edges *out* of this node. Two places it appears:

1. **In the statement environment**: dependencies the *statement* mentions (definitions,
   notation, supporting structures).
   ```latex
   \begin{theorem}
     \label{thm:qexpansion-mul}
     \lean{ModularForm.qExpansion_mul}
     \uses{def:q-expansion, def:modular-form, def:analytic-at-cusp}
     ...
   \end{theorem}
   ```
2. **In the proof environment**: dependencies the *sketch* invokes (lemmas applied,
   prior theorems cited).
   ```latex
   \begin{proof}
     \uses{lem:cusp-function-product, thm:weierstrass-factorisation}
     \leanok
     By \cref{lem:cusp-function-product} and ...
   \end{proof}
   ```

Both lists are dep-graph edges. The dep-graph viewer (Phase 6 web build) colors a node
green when (a) it has `\leanok` and (b) every `\uses{}` target also resolves green.
Missing `\uses{}` declarations break the graph silently — be liberal.

Whitespace and line breaks inside `\uses{...}` are fine:

```latex
\uses{
  def:q-expansion,
  def:modular-form,
  lem:cusp-function-product
}
```

### `\leanok` — optional, but load-bearing for the dep-graph

Asserts the Lean proof is complete (no `sorry`). Appears in two places:

1. **On the statement**: "the Lean declaration `\lean{X}` compiles" — almost always
   true if `lake build` is clean, so this can be auto-emitted from Phase 4 by reading
   the compile state.
2. **On the proof**: "the Lean tactic proof of `\lean{X}` is sorry-free". Check by
   grepping the proof body for `sorry`; emit `\leanok` iff none found.

A theorem with `\leanok` on the statement but missing on the proof renders in the
dep-graph as "stated but not proved" — exactly what the graph is for. **Never emit
`\leanok` on a proof body that contains `sorry`** — it's a lie that defeats the
purpose of the graph.

---

## The "high-quality unformalisation" bar

The reason the blueprint exists is that **the Lean type is unreadable as mathematics**.
The unformalisation is where you earn your keep. Three rules:

### Rule 1 — Drop Lean-only plumbing entirely

Typeclass arguments, universe annotations, implicit `{α : Type*}` parameters,
decidability instances, `[Fintype …]` whenever it's "obviously satisfied for what we
care about", `FunLike`/`SetLike` instances — none of these belong in a math statement.

❌ Bad (mechanical Lean→LaTeX):
```latex
\begin{theorem}
  Let $F, G$ be types with $[FunLike F \alpha \beta]$ and $[FunLike G \alpha \beta]$.
  Let $[ModularFormClass\ F\ \Gamma\ a]$ and $[ModularFormClass\ G\ \Gamma\ b]$. Let $h : \mathbb{Q}$ with $0 < h$, $h \in \Gamma.strictPeriods$, $f : F$, $g : G$. Then $qExpansion\ h\ (\uparrow f * \uparrow g) = qExpansion\ h\ f * qExpansion\ h\ g$.
\end{theorem}
```

✓ Good (mathematical statement):
```latex
\begin{theorem}
  \label{thm:qexpansion-mul-coe}
  \lean{ModularForm.qExpansion_mul_coe}
  \uses{def:q-expansion, def:modular-form-class}
  \leanok
  Let $f$ be a modular form of weight $a$ and $g$ a modular form of weight $b$ on
  $\Gamma$, with $h > 0$ a strict period of $\Gamma$. Then
  \[
    q_h(fg) \;=\; q_h(f) \cdot q_h(g).
  \]
\end{theorem}
```

### Rule 2 — Use the project's own notation

If the project's module docstring writes "$q_h(f)$" for the $h$-th $q$-expansion of
$f$, use `q_h(f)` in the blueprint — not `qExpansion h f` and not `q^{(h)}_f`. If you
invent new notation, *register it once* in a `\begin{notation}` block in the same
chapter and reuse:

```latex
\begin{notation}
  \label{not:q-expansion}
  For $f : \mathbb{H} \to \mathbb{C}$ with cusp function analytic at $0$ and $h > 0$, we write
  $q_h(f)$ for the $h$-th $q$-expansion of $f$, viewed as a formal power series.
\end{notation}
```

Subsequent entries can `\uses{not:q-expansion}` to pull the notation in.

### Rule 3 — The proof sketch is the *mathematics*, not the tactics

The proof block describes the **strategy a mathematician would use to convince
themself**. A reader who has never opened the `.lean` file should follow it.

❌ Bad (tactic transcript):
```latex
\begin{proof}
  \leanok
  By \texttt{rw} of \texttt{discriminant\_mul\_discriminantEquiv} and
  \texttt{CuspForm.coe\_discriminant}, then \texttt{exact} applied to
  \texttt{ModularForm.qExpansion\_mul\_coe} with positivity and period
  hypotheses.
\end{proof}
```

❌ Also bad (refusing to sketch):
```latex
\begin{proof}
  \leanok
  See the Lean source.
\end{proof}
```

✓ Good (mathematical sketch):
```latex
\begin{proof}
  \uses{thm:qexpansion-mul-coe, def:discriminant}
  \leanok
  The modular form $f$ factors, on the upper half-plane, as the product of the
  discriminant $\Delta$ and the cusp form $f / \Delta$. Both factors are analytic
  at the cusp, so the $q$-expansion of the product is the product of the
  $q$-expansions (\cref{thm:qexpansion-mul-coe}); the result follows.
\end{proof}
```

---

## Chapter / file organisation

The leanblueprint convention is one chapter per source-file directory (or per file, for
small projects). The file structure under `blueprint/src/` mirrors the Lean tree:

```
blueprint/src/
├── content.tex            ← \input{}s for every chapter, in narrative order
├── ModularForm/
│   ├── Basic.tex
│   ├── QExpansion.tex
│   └── Discriminant.tex
└── Hecke/
    └── Operator.tex
```

`blueprint/src/content.tex` controls the order chunks appear in the rendered PDF / HTML
— think of it as the table of contents. New chapters get appended in the position that
preserves the narrative: definitions first, then helper lemmas, then the main results
that depend on them.

Inside a chapter file:

1. Open with `\section{<Chapter title>}\label{sec:<chapter>}` (or `\chapter{...}` for
   single-file chapters — match `print.tex`'s class).
2. Group blocks in dependency order: every definition before its consumers; every
   helper lemma before the theorem that uses it.
3. Use blank lines between blocks for readability. plastex tolerates either.

---

## Anti-patterns (catalogue from the failures we've seen)

| Anti-pattern | Why it fails | Fix |
|---|---|---|
| `\lean{}` with a wrong namespace (e.g. `\lean{qExpansion_mul}` when the decl is `\lean{ModularForm.qExpansion_mul}`) | `leanblueprint checkdecls` reports it missing → dep-graph drops the node silently | Always copy the qualified name from the actual Lean source; never abbreviate |
| `\uses{}` listing the Lean tactic names (`simp`, `omega`, `linarith`) | Those aren't labels; orphan refs | `\uses{}` is for labels of OTHER blueprint chunks, not tactics |
| Re-stating typeclass hypotheses (`[CommRing R]`, `[Fintype α]`) in the prose | Reads like Lean cosplay | Drop them; mathematicians read "$R$ a commutative ring" once at chapter start, not on every lemma |
| Proof sketch begins with "First we apply the following lemmas:" then lists them with no narrative | Reader has no idea why | Lead with the STRATEGY ("we induct on $n$ and use the bound from \cref{lem:foo}"), then the steps |
| Multi-page proof transcribed verbatim from the source paper | Defeats the purpose; the blueprint is a guide, not a substitute | One or two paragraphs sketching the spine; refer to the source paper for the full proof |
| `\leanok` emitted on a sorry-containing proof | Dep-graph turns green falsely; reader trusts what's broken | Grep the proof body for `sorry` before emitting `\leanok`; if any `sorry`, omit it |
| One blueprint entry per `private` helper | Pollutes the graph; the helper isn't part of the project's mathematical content | Skip `private` decls in Phase 1 enumeration; their content is folded into the public consumer's proof sketch |
| Statement copies Lean's `Type*` universe annotations | Mathematical content has no universes | Drop them |
| Using `\to` in display math where Lean uses `→` | OK to do this in displays, but match the project's macros (`\implies`, `\Rightarrow`) | Read existing chapters; match what they use |
| Creating a new label per drift re-author, leaving the old one in place | Dep-graph still references the old label; cross-link pass surfaces the orphan | When replacing a chunk, KEEP its existing label unless renaming for clarity |

---

## Worked examples

### Example 1 — A definition

Lean:
```lean
/-- The Eisenstein series of weight $k$ as a function on the upper half plane. -/
def EisensteinSeries (k : ℕ) (z : ℍ) : ℂ := ∑' (mn : ℤ × ℤ), ...
```

Blueprint:
```latex
\begin{definition}[Eisenstein series]
  \label{def:eisenstein-series}
  \lean{EisensteinSeries}
  \uses{def:upper-half-plane}
  \leanok
  For an integer $k \ge 2$ and $z$ in the upper half-plane $\mathbb{H}$, the
  \emph{Eisenstein series of weight $k$} is
  \[
    E_k(z) \;\coloneqq\; \sum_{(m,n) \in \mathbb{Z}^2 \setminus \{(0,0)\}} \frac{1}{(mz + n)^k}.
  \]
\end{definition}
```

### Example 2 — A lemma with a one-line sketch

Lean:
```lean
/-- The Eisenstein series transforms with weight `k` under the modular group action. -/
lemma EisensteinSeries.modular_transform (k : ℕ) (γ : SL₂(ℤ)) (z : ℍ) :
    EisensteinSeries k (γ • z) = (γ.c * z + γ.d) ^ k * EisensteinSeries k z := by
  unfold EisensteinSeries
  ...
```

Blueprint:
```latex
\begin{lemma}[Modular transformation of $E_k$]
  \label{lem:eisenstein-modular-transform}
  \lean{EisensteinSeries.modular_transform}
  \uses{def:eisenstein-series, def:sl2z}
  \leanok
  For $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ and $z \in \mathbb{H}$,
  \[
    E_k(\gamma z) \;=\; (cz + d)^k \, E_k(z).
  \]
\end{lemma}
\begin{proof}
  \leanok
  Substitute the Möbius action $\gamma z = (az+b)/(cz+d)$ into the defining series
  and reindex the sum by $(m, n) \mapsto (m, n) \gamma$. The factor of $(cz+d)^{-k}$
  produced by the substitution cancels against $(cz+d)^k$ from the reindexing
  Jacobian, leaving the claimed identity.
\end{proof}
```

### Example 3 — A theorem with a multi-paragraph sketch and several `\uses{}`

Lean:
```lean
/-- The space of modular forms of weight `k` and level `Γ` is finite-dimensional. -/
theorem ModularForm.finiteDimensional (Γ : Subgroup SL₂(ℤ)) (k : ℕ) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  ...
```

Blueprint:
```latex
\begin{theorem}[Finite-dimensionality of modular forms]
  \label{thm:modular-forms-finite-dim}
  \lean{ModularForm.finiteDimensional}
  \uses{def:modular-form, def:level-subgroup}
  \leanok
  For any finite-index subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ and any
  non-negative integer $k$, the $\mathbb{C}$-vector space $M_k(\Gamma)$ of modular forms
  of weight $k$ and level $\Gamma$ is finite-dimensional.
\end{theorem}
\begin{proof}
  \uses{lem:q-expansion-injective, lem:bounded-order-vanishing, prop:valence-formula}
  \leanok
  The proof is via the valence formula. Any modular form is determined by its
  $q$-expansion (\cref{lem:q-expansion-injective}), so it suffices to bound the
  dimension of the space of admissible $q$-expansions.

  The valence formula (\cref{prop:valence-formula}) relates the total order of
  vanishing of a non-zero modular form at the cusps and at the elliptic points to
  its weight $k$ and the genus of the modular curve $X(\Gamma)$. In particular, the
  total order of vanishing is bounded by an explicit expression in $k$ and the
  ramification data of $\Gamma$.

  This bounds the lowest-order term of an admissible $q$-expansion. Combined with
  the fact that vanishing to high enough order forces the form to be identically
  zero (\cref{lem:bounded-order-vanishing}), the space of $q$-expansions is finite-
  dimensional, and the dimension bound transfers back to $M_k(\Gamma)$.
\end{proof}
```

### Example 4 — A result with no proof block (trivial corollary)

Lean:
```lean
/-- Specialization of the main theorem to weight 12. -/
theorem ModularForm.weight12_specialization (Γ : Subgroup SL₂(ℤ)) :
    M_12(Γ) ≠ ⊥ := ModularForm.nonempty_of_weight_ge_12 Γ
```

Blueprint:
```latex
\begin{corollary}
  \label{cor:weight-12-nonempty}
  \lean{ModularForm.weight12_specialization}
  \uses{thm:modular-forms-nonempty-weight-ge-12}
  \leanok
  $M_{12}(\Gamma)$ is non-trivial for any finite-index subgroup $\Gamma$.
\end{corollary}
```

(No `\begin{proof}` — the result is a direct specialisation. The `\leanok` on the
statement is enough to mark the node green in the dep-graph.)

---

## Notation file (per-chapter `\input` pattern)

If a chapter uses a lot of project-specific macros, gather them in a chapter-level
`notation.tex`:

```
blueprint/src/ModularForm/
├── notation.tex     ← \newcommand{\qExp}{q}\newcommand{\Eis}{E}\dots
├── Basic.tex        ← \input{ModularForm/notation} at top
└── QExpansion.tex
```

`blueprint/src/macros/common.tex` is the right place for **project-wide** macros (the
ones every chapter uses). Don't put chapter-specific macros there.

---

## When the Lean type is genuinely a definition without a "math statement"

Some Lean declarations are infrastructure — e.g. `instance : AddCommGroup (ModularForm
Γ k) := …`. These need a blueprint entry (for `checkdecls`) but the math content is
either "this is an instance of a standard algebraic structure" or "this packages a
named construction".

```latex
\begin{definition}[Modular forms form a $\mathbb{C}$-vector space]
  \label{def:modular-form-vector-space}
  \lean{ModularForm.instModule}
  \uses{def:modular-form}
  \leanok
  The space $M_k(\Gamma)$ of modular forms of weight $k$ on $\Gamma$, equipped with
  pointwise addition and scalar multiplication by $\mathbb{C}$, is a $\mathbb{C}$-vector
  space.
\end{definition}
```

That's the right amount of content for an instance — name the algebraic structure,
say what operations realise it, no more.

---

## Skipping declarations from the blueprint

By convention, the following are NOT blueprinted:

- `private` decls
- `local` decls
- declarations in `test/` directories
- declarations whose docstring starts with `internal` or `auxiliary` (a project
  convention — check the project's existing blueprint for whether they follow this)
- `example` blocks (they're not named; they can't be `\lean{}`'d)
- Auto-generated decls (mathlib's `@[simps]` projections, `instImpl` patterns, etc.)

Phase 1 enumeration in `/blueprint` skips these by default.
