# Blueprint Authoring Conventions (verso-blueprint)

Read this in full before authoring blueprint entries. The conventions here come from
[`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint) (the
canonical project template + manual) and from the published reference blueprints
(`verso-sphere-packing`, `verso-flt`, `verso-carleson`, `verso-noperthedron`,
`verso-algebraic-combinatorics`).

A Verso blueprint is **Lean source**, not LaTeX. Chapter files are `.lean` modules
under `<Project>/Chapters/` that import `Verso`, `VersoManual`, `VersoBlueprint`, and
declare a `#doc (Manual) "Title" =>` block holding the prose + directives.

---

## Project shape

```
<project_root>/
  lakefile.lean               -- declares the Verso library + the blueprint-gen exe
  lean-toolchain
  <Project>.lean              -- root re-export
  <Project>/
    Blueprint.lean            -- top-level: imports chapters, assembles document,
                              --            adds {blueprint_graph}, {blueprint_summary}
    Chapters/
      Foo.lean                -- one chapter per file
      Bar.lean
      ...
  <Project>Main.lean          -- generator entry point (calls
                              -- Informal.PreviewManifest.manualMainWithSharedPreviewManifest)
  scripts/
    ci-pages.sh               -- builds + renders to _out/site/html-multi/
  .github/workflows/
    pages.yml                 -- deploys _out/site/html-multi to GitHub Pages
    blueprint-pages.yml       -- the reusable workflow doing the actual build
```

To render locally:

```bash
lake update                 # once after copying the template
./scripts/ci-pages.sh       # equivalent to:
                            # lake build <Project>
                            # lake env lean --run <Project>Main.lean --output _out/site
```

Output is at `_out/site/html-multi/`. Serve with `python3 -m http.server -d
_out/site/html-multi/` to preview.

---

## The five Verso directives every blueprint uses

### `:::definition "label" (lean := "Foo.bar")`

```
:::definition "addition_spec" (lean := "Nat.add, Nat.succ")
We write $`a + b` for the result of adding $`b` to $`a`.
:::
```

- The `"label"` is the global identifier — referenced by `{uses "label"}[]` and
  `{bpref "label"}[]` from other directives.
- `(lean := "Foo, Bar")` lists existing Lean declarations this definition is realised
  by (comma-separated). Verso's progress tracker uses this to colour the dep-graph
  node by the linked declarations' state.
- The body is **prose with KaTeX math** — see "Math syntax" below.

### `:::theorem "label" (lean := "Foo.bar")`

```
:::theorem "addition_assoc" (lean := "Nat.add_assoc")
For all $`a, b, c`, addition is associative: $`(a + b) + c = a + (b + c)`.
This follows from {uses "addition_spec"}[].
:::
```

`:::lemma` and `:::proposition` are aliases for theorem-shaped blocks. Pick by the
mathematical role, not by Lean's keyword.

### `:::proof "label"`

```
:::proof "addition_right_identity"
Induct on $`n`. The base case is immediate; the inductive step unfolds one
successor on each side and applies {uses "successor_def"}[].
:::
```

Proof blocks **follow** their theorem/lemma by sharing the `"label"`. Each proof can
have its own `{uses}` edges — these become the proof's outgoing edges in the dep-graph
(distinct from the statement's edges).

### Local Lean code block — fenced with the same label

````
```lean "addition_right_identity"
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```
````

This is the third way to link a Verso node to Lean (after `(lean := "X")` and the
`@[blueprint "label"]` attribute on a compiled declaration). The local Lean block is
useful when:

- The Lean proof is short enough to inline alongside the prose
- The blueprint is a teaching artifact where the formal text matters

Local blocks are elaborated as part of the Verso build; if the local Lean block has
a `sorry`, that flows into the dep-graph automatically.

### `@[blueprint "label"]` attribute (in regular Lean modules)

```lean
@[blueprint "addition_right_identity"]
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```

This is the cleanest connection: the declaration lives in your normal Lean library
(not a chapter file), and the attribute attaches it to the named blueprint node.
Prefer this when the Lean code lives in `<Project>/Lemmas.lean` and the blueprint
just prose-narrates.

---

## The two reference forms — `{uses}` vs `{bpref}`

| | Adds graph edge? | Renders as link in prose? |
|---|---|---|
| `{uses "label"}[]` | **yes** | yes |
| `{bpref "label"}[]` | **no** | yes |

Use `{uses}` when *this node mathematically depends on the target* — the dep-graph
edge is informative. Use `{bpref}` for "see also" prose links that don't add
mathematical dependency.

The empty payload `[]` lets Verso pick the visible text automatically (e.g.,
"Theorem 3"). Use the payload for custom prose:

```
This follows from {uses "addition_assoc"}[associativity of addition].
```

---

## Math syntax (KaTeX)

| Form | Use |
|------|-----|
| `` $`a + b` `` | inline math |
| `` $$`\sum_{i=0}^{n} i = \frac{n(n+1)}{2}` `` | display math |

KaTeX-renderable LaTeX inside the backticks. Verso lints KaTeX during elaboration —
unknown commands surface as build errors at the `#doc` block, not at runtime.

If you have project-specific macros, declare them via `tex_prelude` at the top of
the chapter:

```
tex_prelude "
  \def\re{\operatorname{Re}}
  \def\NN{\mathbb{N}}
"
```

Subsequent math in the same chapter can use `\re` and `\NN`.

---

## Metadata on directives

The directive parens accept several optional metadata keys:

```
:::theorem "addition_right_identity"
    (parent := "addition_core")
    (owner  := "jane")
    (tags   := "starter, arithmetic")
    (effort := "small")
    (priority := "high")
    (lean   := "Foo.bar, Foo.baz")
For every natural number $`n`, $`n + 0 = n`.
:::
```

- `(parent := "label")` puts this node under a named group block (`:::group "label" ... :::`).
- `(owner := "name")` for tracking who's working on it (rendered in summary view).
- `(tags := "...")` comma-separated, used for filtering in the rendered site.
- `(effort := "...")` and `(priority := "...")` show up in the progress summary.
- `(lean := "...")` is the most load-bearing one — links Lean declarations.

Workers normally only emit `(lean := "...")`. Other metadata is project-policy and
should mirror what neighbouring chapters use.

---

## Auto-progress (the reason `\leanok` is gone)

In Verso blueprints, **completion status is auto-computed** from the elaborated Lean
state of the declarations the node references. A `:::theorem` whose `(lean := "X")`
points at a sorry-free `theorem X` renders green; if `X` is `:= sorry`, it renders
in-progress; if the local Lean block has `sorry`, same. There is no `\leanok` to emit
or forget.

Workers do not have to grep for `sorry`. They emit `(lean := "...")` correctly; Verso
does the rest. This eliminates the "manual `\leanok` drifts out of sync" failure mode
from the LaTeX stack.

---

## The "high-quality unformalisation" bar

These three rules are stack-agnostic — they applied in LaTeX, they apply in Verso.

### Rule 1 — Drop Lean-only plumbing entirely

Typeclass arguments, universe annotations, implicit `{α : Type*}`, decidability
instances, `[Fintype …]` for "obviously satisfied", `FunLike`/`SetLike` instances —
none of these belong in the prose statement.

Bad (mechanical Lean→prose):

```
:::theorem "qexpansion_mul_coe" (lean := "ModularForm.qExpansion_mul_coe")
Let $`F, G` be types with $`[\text{FunLike } F\ \alpha\ \beta]` and similar, and let
$`[\text{ModularFormClass } F\ \Gamma\ a]` and $`[\text{ModularFormClass } G\ \Gamma\ b]`.
Let $`h : \mathbb{Q}` with $`0 < h`, $`h \in \Gamma.\text{strictPeriods}`, $`f : F`,
$`g : G`. Then $`\text{qExpansion}\ h\ (\uparrow f \cdot \uparrow g) =
\text{qExpansion}\ h\ f \cdot \text{qExpansion}\ h\ g`.
:::
```

Good (mathematical statement):

```
:::theorem "qexpansion_mul_coe" (lean := "ModularForm.qExpansion_mul_coe")
Let $`f` be a modular form of weight $`a` and $`g` a modular form of weight $`b`
on $`\Gamma`, with $`h > 0` a strict period of $`\Gamma`. Then
$$`q_h(fg) = q_h(f) \cdot q_h(g).`
:::
```

### Rule 2 — Use the project's own notation

If the project writes $`q_h(f)` for the $`h`-th $`q`-expansion of $`f`, use that —
not `qExpansion h f` and not a freshly-invented $`q^{(h)}_f`. If you introduce new
notation, register it once in a `tex_prelude` or `:::definition` and reuse.

### Rule 3 — The proof sketch is the *mathematics*, not the tactics

A reader who has never opened the `.lean` file should follow the proof. Saying
"by `simp` and `omega`" is not acceptable. Saying "by linearity of the integral and
the elementary bound $`|e^{ix}| \le 1`" is.

Bad (tactic transcript):

```
:::proof "qexpansion_eq_disc_mul"
By `rw` of `discriminant_mul_discriminantEquiv` and `CuspForm.coe_discriminant`,
then `exact` on `ModularForm.qExpansion_mul_coe` with the positivity and period
hypotheses.
:::
```

Also bad (refusal to sketch):

```
:::proof "qexpansion_eq_disc_mul"
See the Lean source.
:::
```

Good:

```
:::proof "qexpansion_eq_disc_mul"
The modular form $`f` factors, on the upper half-plane, as the product of the
discriminant $`\Delta` and the cusp form $`f / \Delta`. Both factors are analytic
at the cusp, so the $`q`-expansion of the product is the product of the
$`q`-expansions ({uses "qexpansion_mul_coe"}[]); the result follows.
:::
```

---

## Anti-patterns

| Anti-pattern | Why it fails | Fix |
|---|---|---|
| `(lean := "...")` with a wrong namespace | Verso reports it during elaboration; the dep-graph link is broken | Always copy the qualified name from the actual Lean source |
| `{uses "tactic-name"}[]` (e.g. `{uses "simp"}[]`) | tactics aren't blueprint labels; the reference resolves to nothing or errors | `{uses}` is for OTHER blueprint labels; don't reference tactics |
| Repeating typeclass hypotheses in the prose | reads like Lean cosplay | "$`R` is a commutative ring" once at chapter top, not per lemma |
| Multi-page proof transcribed verbatim from the source paper | defeats the purpose — the blueprint is a guide, not a substitute | one or two paragraphs sketching the spine |
| Re-emitting `\leanok` after the rewrite | `\leanok` is not a Verso directive — it's silently ignored | drop it; Verso computes status from `(lean := "...")` |
| Math written with `$...$` (LaTeX) instead of ``$`...` `` (Verso/KaTeX) | dollar-only math is plain prose; Verso doesn't render it | use ``$`...` `` for inline, ``$$`...` `` for display |
| One blueprint entry per `private` helper | pollutes the graph | skip `private` decls in enumeration; their content folds into the public consumer's proof |
| `:::theorem` directives without a closing `:::` | Verso parse error; whole chapter doesn't elaborate | always pair `:::name "label" ... :::` |

---

## Chapter organisation

```
<Project>/Chapters/
├── Basic.lean          -- Definitions + foundational lemmas
├── QExpansion.lean
└── Discriminant.lean
```

The top-level `<Project>/Blueprint.lean` `{include}`s them in narrative order:

```lean
import <Project>.Chapters.Basic
import <Project>.Chapters.QExpansion
import <Project>.Chapters.Discriminant

#doc (Manual) "My Project Blueprint" =>

{include 0 <Project>.Chapters.Basic}
{include 0 <Project>.Chapters.QExpansion}
{include 0 <Project>.Chapters.Discriminant}

{blueprint_graph}
{blueprint_summary}
```

The `{blueprint_graph}` block renders the interactive dep-graph; the
`{blueprint_summary}` block renders the progress summary table.

Inside a chapter file, group blocks by dependency: every `:::definition` before its
consumers; every `:::lemma` before the `:::theorem` that uses it.

---

## Worked examples

### Example 1 — A definition

Lean:
```lean
/-- The Eisenstein series of weight $k$ as a function on the upper half plane. -/
def EisensteinSeries (k : ℕ) (z : ℍ) : ℂ := ∑' (mn : ℤ × ℤ), ...
```

Blueprint:
```
:::definition "eisenstein-series" (lean := "EisensteinSeries")
For an integer $`k \ge 2` and $`z` in the upper half-plane $`\mathbb{H}`, the
*Eisenstein series of weight $`k`* is
$$`E_k(z) \;\coloneqq\; \sum_{(m,n) \in \mathbb{Z}^2 \setminus \{(0,0)\}}
                       \frac{1}{(mz + n)^k}.`
:::
```

### Example 2 — A lemma with a one-line sketch

Lean:
```lean
lemma EisensteinSeries.modular_transform (k : ℕ) (γ : SL₂(ℤ)) (z : ℍ) :
    EisensteinSeries k (γ • z) = (γ.c * z + γ.d) ^ k * EisensteinSeries k z := ...
```

Blueprint:
```
:::lemma "eisenstein-modular-transform" (lean := "EisensteinSeries.modular_transform")
For $`\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})`
and $`z \in \mathbb{H}`,
$$`E_k(\gamma z) \;=\; (cz + d)^k \, E_k(z).`
:::

:::proof "eisenstein-modular-transform"
Substitute the Möbius action $`\gamma z = (az+b)/(cz+d)` into the defining series
and reindex the sum by $`(m, n) \mapsto (m, n) \gamma`. The factor of $`(cz+d)^{-k}`
produced by the substitution cancels against $`(cz+d)^k` from the reindexing
Jacobian, leaving the claimed identity.
:::
```

### Example 3 — A theorem with multiple `{uses}` and a multi-paragraph sketch

Lean:
```lean
theorem ModularForm.finiteDimensional (Γ : Subgroup SL₂(ℤ)) (k : ℕ) :
    FiniteDimensional ℂ (ModularForm Γ k) := ...
```

Blueprint:
```
:::theorem "modular-forms-finite-dim" (lean := "ModularForm.finiteDimensional")
For any finite-index subgroup $`\Gamma \le \mathrm{SL}_2(\mathbb{Z})` and any
non-negative integer $`k`, the $`\mathbb{C}`-vector space $`M_k(\Gamma)` of
modular forms of weight $`k` and level $`\Gamma` is finite-dimensional.
:::

:::proof "modular-forms-finite-dim"
The proof is via the valence formula. Any modular form is determined by its
$`q`-expansion ({uses "q-expansion-injective"}[]), so it suffices to bound the
dimension of the space of admissible $`q`-expansions.

The valence formula ({uses "valence-formula"}[]) relates the total order of
vanishing of a non-zero modular form at the cusps and at the elliptic points to
its weight $`k` and the genus of the modular curve $`X(\Gamma)`. The total order
of vanishing is bounded by an explicit expression in $`k` and the ramification
data of $`\Gamma`.

Combined with the fact that vanishing to high enough order forces the form to be
identically zero ({uses "bounded-order-vanishing"}[]), the space of $`q`-expansions
is finite-dimensional, and the dimension bound transfers back to $`M_k(\Gamma)`.
:::
```

### Example 4 — A trivial corollary (no proof block)

Lean:
```lean
theorem ModularForm.weight12_specialization (Γ : Subgroup SL₂(ℤ)) :
    M_12(Γ) ≠ ⊥ := ModularForm.nonempty_of_weight_ge_12 Γ
```

Blueprint:
```
:::corollary "weight-12-nonempty" (lean := "ModularForm.weight12_specialization")
$`M_{12}(\Gamma)` is non-trivial for any finite-index subgroup $`\Gamma`.
{bpref "modular-forms-nonempty-weight-ge-12"}[Specialisation of the main result.]
:::
```

(No `:::proof` block — Verso's auto-progress reads the underlying Lean
declaration's status.)

---

## Skipping declarations from the blueprint

By convention, the following are NOT blueprinted:

- `private` decls
- `local` decls
- declarations in `test/` directories
- declarations whose docstring starts with `internal` or `auxiliary` (project-specific
  convention; check the project's existing blueprint for whether they follow this)
- `example` blocks (they're not named; can't be `(lean := ...)`'d)
- auto-generated decls (mathlib's `@[simps]` projections, `instImpl` patterns)

Phase 1 enumeration in `/blueprint` skips these by default.

---

## Deployment & CI gotchas (Verso-specific)

Verso eliminates the LaTeX-stack failure modes from the previous skill version
(latexmk pass count, undefined `\re`-style macros, `.aux` cascades, stale
`blueprint/lean_decls`). The Verso failure modes are different but worth flagging:

### Missing chapter import in `Blueprint.lean`

A new chapter file `Chapters/Foo.lean` won't appear in the rendered site unless
`Blueprint.lean` also has:

```lean
import <Project>.Chapters.Foo
...
{include 0 <Project>.Chapters.Foo}
```

Both lines are required (import + include). The Phase-5 cross-link pass checks for
"chapter file exists in `Chapters/` but no `{include}` in `Blueprint.lean`".

### KaTeX errors at elaboration

Unknown `\foo` macros in math inside `:::` directives surface as Lean elaboration
errors at the `#doc` block — not as runtime errors in the HTML. The fix is either
(a) declare the macro in a chapter-level `tex_prelude`, or (b) replace it with a
standard KaTeX command.

### `(lean := "X")` with a stale name

Verso checks `(lean := "X")` resolves during elaboration. If `X` was renamed in the
Lean source, the build fails. The Phase-5 cross-link pass catches this before the
build runs by greping current Lean decls.

### `_out/` should be `.gitignore`d

```
_out/
.lake/
```

The template ships these; verify they're present.

### CI workflow

The template's `.github/workflows/pages.yml` + `blueprint-pages.yml` handle the
full build/deploy. No `api-docs: true` toggle to remember (Verso's auto-link works
differently); no `latexmk` configuration. The Phase-0 doctor in `/blueprint`
verifies the workflows exist; if missing, prints the copy-template instructions.

### Pre-push checklist

```bash
./scripts/ci-pages.sh                              # full build + render
ls _out/site/html-multi/index.html                 # must exist
python3 -m http.server -d _out/site/html-multi/    # eyeball locally before pushing
```

If `ci-pages.sh` exits non-zero, fix the elaboration error it surfaces (the line
number is usually exact — Verso integrates with Lean's diagnostic surface) before
pushing.
