# Voyager — operator handover

Written 2026-08-04, after the sixth update. The authority on procedure is `SKILL.md` in this
directory: read it in full before your first run, and treat it as the contract — the logic
deliberately lives there, not in shell scripts or anyone's memory. This document is the
briefing on top of it: the current state, the editorial taste the skill can't fully encode,
and the production lessons with the scars still attached.

## What you are operating

Voyager is a Zulip bot (`voyager`, user id 1178994) that announces **real mathematics newly
merged into the Tau Ceti library** — on leanprover.zulipchat.com, channel **Tau Ceti**, topic
**new results**. The `PRs` topic in the same channel belongs to a different bot; never post
there and never touch its messages.

The prime directive is in SKILL.md and bears repeating: the failure mode is not missing
something, it is **crying wolf**. A quiet check-in is a normal, frequent, successful outcome.
One genuine named theorem is worth more than twenty declarations that merely have names, and
a reader who once catches Voyager dressing up API glue as news will never trust the topic
again. When in doubt, skip; the result will still be true tomorrow.

## State at handover

| thing | value |
|---|---|
| credentials | `~/.zuliprc` (bot email `Voyager-bot@leanprover.zulipchat.com` — capital V; never echo the key) |
| watermark | newest self-DM: `commit=54d9297295d9… pr=1770` (DM id 614796848) — always re-read the DM; this row is a snapshot |
| messages posted | 613614529 (first-run backlog, 2026-07-30, edited in place per channel feedback; now 9,473 codepoints — **do not let it grow**), 613886812, 614078696, 614179130, 614350642, 614590153 (edited 2026-08-05 to note the `ModularForm.L` overlap Thomas Browning raised), 614796841 (seventh, 13 bullets — too many; see the curation rule below) |
| cadence | daily, 16:03 UK; the window always ends at TauCeti's `docgen` branch |
| scheduling | a self-renewing session cron job in Chris's Claude session (the id changes at every run's upkeep step — `8bc06385` as of the seventh update; `CronList` is the source of truth). Session-only, and **its firing time is approximate by construction**: the job queues a prompt into the session's own loop, so it only fires when that loop is idle, and the scheduler adds up to 15 minutes of deliberate jitter on top. It therefore fires late whenever the machine is asleep or the session is mid-turn — 18:42 once, 16:33 another day — which is harmless, since the watermark defines the window and not the clock. Do not promise anyone a wall-clock minute; if punctuality ever matters, that is the argument for moving to Actions, not for tuning the cron. The sturdier long-term home is a GitHub Actions workflow in the TauCeti repo; Chris knows |
| first-run.md | dead weight — the backlog was posted once (2026-07-30) and must never be reposted; ignore that file entirely |

Owner decisions already made, not yours to revisit: no `sorry` counts in the stats block
(the no-`sorry` rule stays as an announcement gate); daily cadence at 16:03 UK; quiet windows
with merged PRs still get a short check-in; only a genuinely empty window posts nothing; the
bullet list is curated rather than exhaustive, and short is fine (2026-08-05 — see the
curation rule under House style); the loop keeps running until Chris says otherwise.

## The shape of a run

SKILL.md has the details; the skeleton, in order, with no step optional:

1. **Freshness abort** — newest Voyager channel message or state DM under 2 hours old → stop.
2. **Watermark** — parse `commit=`/`pr=` from the newest self-DM.
3. **Window** — full-history clone, fetch and check out `origin/docgen`, diff from the
   watermark commit. Equal → exit silently. All stats are computed at the docgen commit.
4. **Candidates** — PR-by-PR over the squash-merge subjects (`feat:` is where news lives),
   cross-checked with the module-title sweep of added `.lean` files.
5. **Novelty gate** — against *current Mathlib master*, never a pinned checkout alone:
   local-pin grep is cheap triage (a hit kills, a miss decides nothing), then
   `gh search code` on master **with a positive control** (e.g. `IsFredholm`) before trusting
   any empty result, then `lean_leansearch` for statement-level checks on high-risk items,
   then *read the hit* — a name hit is not a statement hit, in either direction.
6. **Significance gate** — one batched chatgpt-math call, `reasoning_effort: "high"` (never
   `"max"`, which times out). Verdicts are advice, not authority; sanity-check every sentence
   you adopt against the actual Lean statement.
7. **Compose** (see the style section — this is the part Chris singled out as good).
8. **Verify every link**, count codepoints (< 9,500), post, **re-fetch rendered** and check
   the stats lines are present and `[message truncated]` is absent.
9. **State DM** — post first, DM second; retry the DM if it fails.
10. **Cron upkeep** — delete and recreate the daily job so the 7-day session-cron expiry
    never lapses.

The three **never-double-post** checks (freshness; permanent `TauCeti#NNN` dedupe over the
entire topic history, `num_before=1000`; name-level repeat rule) are mandatory before every
post. PR numbers never recur, so the dedupe is permanent and absolute. A repeated *name*
posts only as a genuine strengthening from a different PR **with the delta stated in the
sentence** — the model case is the sixth update's E₄/E₆ bullet, which upgraded the fifth
update's generation statement to the full isomorphism and said so explicitly with a
back-reference to the earlier PR.

## House style — read this twice

The messages have earned trust by sounding like a mathematician telling colleagues what is
now proved, not like release notes. Every rule below came from feedback or a near-miss.

**Curate, don't enumerate — the list is meant to be short.** Chris, 2026-08-05, after the
seventh update ran to thirteen bullets: *"don't feel obliged to make the list long, it's more
important to keep it interesting and mention significant results."* Every bullet in that
message had passed all three gates, which is exactly the trap — the gates decide what is
*allowed*, and you still have to decide what is *worth reading*. A reader who skims one
long list learns less than one who reads three good bullets, and the topic's credibility
rests on the second experience. So: pick the results that matter, lead with the best one,
and stop; do not pad, and do not treat an eligible result as owed a mention. Nothing is
lost by leaving one out — the dedupe keys on *cited* PR numbers, so an omitted result can
still be announced the day it becomes the interesting one. Message 614796841 is the
calibration point in the wrong direction; the first six updates (three to eight bullets)
are the right shape.

**The bullet is the unit.** Its anatomy, fixed:

> - **[Standard name](verified docs anchor)** — one sentence, for a mathematician who does
>   not know the result, saying what it *asserts*; then any honest scope note; then a real
>   reference. (TauCeti#NNN)

A dissected specimen from the sixth update:

> - **[Strong approximation for SL₂](…#Matrix.SpecialLinearGroup.map_intCast_zmod_surjective)**
>   — the reduction map SL₂(ℤ) → SL₂(ℤ/dℤ) is surjective for every d (Shimura §1.6), the
>   input that realizes every unit of ℤ/N as a lower-right entry in Γ₀(N). (TauCeti#1882)

- the bold text is the **standard mathematical name**, never the Lean identifier;
- the sentence states the assertion in symbols a working mathematician reads, present tense,
  no hype;
- the optional trailing clause says what it is *for* in the library, when that helps;
- the reference is a real book or paper (Serre, Shimura, Milne, Kallenberg, Humphreys,
  Fulton–Harris…), **never a Lean file**;
- the PR citation is the bare realm linkifier, in parentheses, last.

**Two sections, one judgment call.** `*Named results*` and `*Notable definitions*`. A
definition with a real theorem attached (the Hecke ring with its commutativity criterion)
goes under results; a construction whose content is that it now exists in usable form (the
modular-form L-function, the central character) goes under definitions, with its best
theorem folded into the sentence.

**No eponym? Name the content.** "The pairing of two permutation characters counts double
cosets" and "The closed dominant chamber is a strict fundamental domain" are titles a reader
recognises instantly; both were used in preference to Lean names or vague labels.

**State exactly what is formalized, in the sentence itself.** The L-function bullet says
convergence bounds are proved *and* that analytic continuation is a separate later milestone.
The Sturm bullet says Mathlib master has the level-one case and this is the finite-index
case. This in-sentence honesty is the single most load-bearing style rule: it is what lets a
reader act on a bullet without opening the file.

**Overlap notes are neutral and specific — never competitive.** Banned outright: "Mathlib
doesn't have this", "Mathlib has none of these", "first ever". The house forms:
"also being formalised in mathlib4#NNNNN", "landed independently in Mathlib master on
<date>", "Mathlib master has the level-one case", "ports Chris Birkbeck's open upstream
draft mathlib4#39258 onto the current pin". Attribution to upstream drafts is part of
honesty, not modesty.

**No marketing register, ever.** No "exciting", "major milestone", "we are pleased",
no exclamation marks, no emoji. State what the theorem says, not how impressive it is.
Adjectives survive only when they carry mathematical content ("strict" fundamental domain,
"division-free" doubled forms).

**Mathematical notation** is plain Unicode in running text — χ, ⟨·,·⟩, Σ, ℂ[E₄, E₆],
`H\Δ/H` — matching how the previous six messages read. Inline code backticks are for actual
identifiers and formulas that read better monospaced.

**Zulip mechanics** (each learned the hard way):
- one physical line per paragraph and per bullet — Zulip keeps single newlines, so
  hard-wrapped prose renders ragged;
- bold goes **outside** links: `**[Name](url)**`, never `[**Name**](url)`;
- bare `TauCeti#NNN` / `mathlib4#NNN` — the realm linkifies them; no explicit PR URLs;
- no HTML comments anywhere — Zulip renders them as visible text;
- under ~9,500 codepoints (`len()` in Python on the exact string). The hard cap is 10,000
  and an over-long **edit returns success while silently truncating** the rendered message;
- after every post *and* every edit, GET the message with `apply_markdown=true` and check
  the stats lines are present and `[message truncated]` absent;
- the send API returns `result: "success"`, not `"ok"` — a wrong success-check throws
  *after* the message has landed.

**The stats block**, verbatim shape, commas in the numbers:

> *Stats*
> - 234,507 lines of Lean across 1,236 files (Tau Ceti only, excluding Mathlib)
> - 11,669 declarations
> - 64 PRs merged since the last update (1,692 total)

P is the exact count of squash-merge commits in the window; T is the GitHub search total.
They deliberately do not reconcile against the previous `pr=` (docgen lags post time, so a
few PRs counted at the last post reappear in this window's commits) — that is expected, not
a bug. No sorry counts.

**The quiet check-in**, when PRs merged but nothing survived the gates:

> **Voyager · Tau Ceti check-in**
>
> No notable named results landed in this window (as judged by the voyager AI bot).
>
> - <P> PRs merged since the last update (<T> total)
> - <N> lines of Lean across <M> files (Tau Ceti only, excluding Mathlib)

It advances the watermark like any post. Keep the "(as judged by the voyager AI bot)"
disclaimer — it is Chris's wording and it defuses complaints about judgment calls.

## Links: verify, then verify the right thing

Every bold name links to the declaration's anchor in the API docs,
`https://taucetiproject.github.io/TauCeti/docs/TauCeti/<Module/Path>.html#<FQN>`. Two rules:

1. **Verify by extraction, not construction.** Curl the page (expect 200) and pull the real
   `id="…"` out of the HTML. Never guess the fully qualified name: some files have no
   `TauCeti` namespace at all (`lieExp`, `pointDerivationEquivTangentSpace`,
   `ModularForm.lSeries`, `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective` are all
   bare or foreign-namespaced).
2. **Link the theorem the headline claims**, not the containing definition. The
   narrow-class-group finiteness bullet once linked the group's definition instead of
   `instFinite`; Chris caught it. If the bold text says "…is finite", the anchor is the
   finiteness statement.

Fallback when the docs page or anchor is missing: the source file at
`https://github.com/TauCetiProject/TauCeti/blob/main/<path>`. If the file has since been
*deleted* (it happens — `Parametrix.lean` went when TauCeti adopted Mathlib's Fredholm
predicate), use a pinned-commit permalink (`blob/<sha>/…`), which cannot rot.

**Link rot is real.** The docs site serves only the newest build, so links verified at post
time die when files move or declarations rename (Montel.lean → Montel/, JordanCurve.lean →
JordanCurve/Basic.lean, the Fredholm upstreaming). A full 70-link audit on 2026-08-03 fixed
four. Worth re-running such an audit occasionally, and always after a big refactor lands.

**Editing posted messages:** only for maintainer-requested fixes (links, formatting, tone) —
that is the standing rule, and both in-place edit rounds so far were Chris-requested. If a
posted claim turns out to be wrong or already in Mathlib, the remedy is a new correction
message, not a silent rewrite of history.

## Judgment calibration — the traps that almost happened

- **A file titled "the X theorem" may contain only scaffolding.** TauCeti#1942, "the Weyl
  dimension formula for GL n", builds the formula as a natural number — integrality,
  positivity, Vandermonde identities — and attaches it to no representation. Announcing it
  would have been false. Read the module docstring's *Main results* before believing any
  title; SKILL.md's calibration table (Gårding, Bochner, Gabriel rows) is the same lesson.
- **"In the directory" ≠ "proved".** A tree full of Bochner-adjacent machinery does not
  contain Bochner's theorem. Find the statement or drop the candidate.
- **Same eponym, different theorem.** Montel spaces vs Montel's selection theorem; the
  C*-algebra double centralizer vs the semisimple-module one; the Fredholm alternative vs
  Fredholm operators. Open the hit and read what it states.
- **Steps toward a named target stay silent.** Krull–Schmidt *existence* half, Cesàro/Koopman
  lemmas on the way to de Finetti, cusp-width infrastructure under the Sturm bound: all
  skipped, correctly. Announce the summit when it exists; the approach ridge is not news.
- **Restatements and packagings of already-announced results stay silent**, even when the
  new form is the textbook one (Montel-as-compactness after the selection theorem was
  announced; the hyperbolic-length Schwarz–Pick after Schwarz–Pick-with-rigidity).
- **ChatGPT's gate verdicts are advice.** It has misnumbered a theorem and misattributed a
  file before. Its ANNOUNCE/SKIP calls have been good; its supporting claims still get
  checked against the primary source before any of them reach a sentence you post.

## Ops gotchas, complete list

- `gh search code` rate-limits silently: run the positive control before trusting empties,
  sleep ~7s between searches.
- The scratch TauCeti clone must be **full history** — a shallow clone silently breaks
  `--diff-filter=A` PR attribution (every file appears added by the newest commit).
- Dirty scratch tree blocks checkout: `git checkout -- <file>`, then re-detach; stats must
  be computed at the docgen commit.
- Python f-strings eat literal braces — double them, or build messages with concatenation.
- The chatgpt-math MCP call can take minutes and may be backgrounded by the harness; keep
  working (stats, anchors, sorry gate) while it runs.
- The sorry gate greps *mentions*: read the hits; a docstring saying "the `sorry`-goal in
  Suggested.lean" is not a proof hole.
- Python's TLS can break independently of `curl`. On this machine the python.org 3.12 build
  lost its CA file (`ssl.get_default_verify_paths().cafile` is `None`), so `zulip.py check`
  died with `CERTIFICATE_VERIFY_FAILED` while `curl` kept working. The run path is curl-only
  and was unaffected — but do not read a failing probe as a dead bot. Fix with
  `export SSL_CERT_FILE=$(python3 -c 'import certifi;print(certifi.where())')`, or run the
  installer's "Install Certificates.command".
- The state DM's SHA must be copied, never retyped or padded — see the watermark protocol in
  SKILL.md, rule 5.
- A freshness abort is a *success*. If a human asked for the post early and the cron then
  fires, the gate stops the double-post; report the abort and move on.
- Never post from a fallback channel or invent output when credentials fail — report loudly
  and exit.

## Where things live

- Canonical skill: `~/Documents/GitHub/mathlib-quality/skills/voyager/SKILL.md` (this repo
  is the single source; a copy that once lived in TauCetiRoadmap was deleted to stop drift).
- The five Claude accounts on this machine all see it via the `mathlib-quality` plugin.
- Session-to-session operational memory (watermark history, lessons, current cron id) has
  been kept in Chris's Claude memory as `voyager-bot-state`; if you are not that Claude,
  everything you actually need is the newest state DM plus this file.
- The eventual home for the whole pipeline is the Tau Ceti CLI / a GitHub Actions workflow;
  keep decision logic in SKILL.md so it lifts across intact.
