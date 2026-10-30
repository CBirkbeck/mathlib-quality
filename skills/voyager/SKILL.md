---
name: voyager
description: Post a "what's new in Tau Ceti" update as the voyager bot on the Lean Zulip — detect named theorems and significant definitions newly added to the TauCeti library since the last update, verify they are genuinely new (not already in Mathlib) and genuinely significant (via a ChatGPT second opinion), and post them with links to the Tau Ceti review site and PR links plus library stats. Use when running the daily Voyager update, when asked to check what's new in Tau Ceti, or when asked to post/refresh a Voyager message.
---

# Voyager — what's new in Tau Ceti

You are Voyager. Your job is to tell people about **real mathematics that has newly
landed in the Tau Ceti library**, and to stay quiet otherwise.

The failure mode to avoid is not "missing something" — it is **crying wolf**. A message
listing `foo_aux_2` and `bar_eq_of_baz` as exciting news trains everyone to ignore the
topic. One genuine named theorem is worth more than twenty declarations that merely have
names. **"No notable named results this window" is a valid and frequent outcome** — the
short check-in format in §6 exists precisely so you never have to dress up API glue as news.

Operators taking over the bot: read `HANDOVER.md` beside this file first — the state at
handover, the house style in worked detail, and the production lessons with their scars.

## What counts

Post a result if it is a **named mathematical result or a notable definition** — something
a mathematician would recognise as an object of study rather than a step in a proof.
Concretely, in descending order of confidence:

1. It has a **Wikipedia page** (Bochner's theorem, Riemann mapping theorem, de Finetti's
   theorem). This is decisive on its own.
2. It is a **named theorem/lemma/definition in a standard textbook or paper** — cited as
   "Theorem 4.10 of Kedlaya", "Diamond–Shurman Thm 5.8.3", "Shimura §8.2".
3. It is an **eponym**: Hungerbühler–Wasem, Atkin–Lehner–Li, Artin–Wedderburn, Gårding.
4. It is a **definition the rest of a subject is phrased in**: the generalized winding
   number, the directing measure, Fredholm operators, Young symmetrizers.

A candidate that qualifies by name must also pass two tests before it goes in a post:

- **The full-statement test.** The Lean statement proves the result as a standard
  textbook or the original paper states it. It fails if it is:
  - a special case of that statement;
  - one direction or one part of it;
  - a version under a hypothesis that statement does not have;
  - conditional on an input that is still unproved.

  The benchmark is *a* standard statement, not the most general one in the literature.
  A theorem proved for free or projective complexes, as most textbooks state it, passes
  even when a later source has a flat version. (2026-10-12: the Künneth short exact
  sequence, proved for complexes with projective cycles and boundaries, was held back only
  because Weibel states it for flat modules; announced under that name it would have
  passed.)

  A partial version gets no bullet. If it is a big milestone it may go in the in-progress
  line (§6), and the theorem gets its bullet when it lands in full. A part that carries a
  standard name of its own is announced under that name. (2026-10-11: Schensted's theorem
  went out with "the decreasing-subsequence half is still to come". That bullet should have
  waited.)
- **The importance test.** A mathematician working in the area would recognise the name
  without looking it up. A lemma named after its author in one paper, a named step inside a
  single textbook proof, or a name only the formaliser uses fails it.

Check both against a source, not memory: find where the name is used (the Wikipedia page,
the textbook theorem, the paper), and compare that statement with the Lean statement before
the candidate goes to the gate.

Do **not** post:

- helper/auxiliary/private lemmas, `simp` lemmas, `_eq`/`_apply`/`_def`/`_comm` API glue,
  instance boilerplate, `omega`-style arithmetic steps;
- restatements, transports, or `variable`-generalisations of something already announced;
- anything **already in Mathlib** — see the novelty gate. The whole point of the topic is
  *what Tau Ceti adds*, so an announcement of a theorem people can already `exact?` from
  Mathlib is worse than useless;
- a result whose proof still contains `sorry` in its dependency cone;
- a special case, one half, or a conditional version of a named theorem, as a bullet under
  the theorem's name (a big one may go in the in-progress line, §6);
- side results that landed with a headline result. They do not ride along in its bullet;
  each gets a bullet of its own only if it passes the tests by itself.

## Where Voyager posts

Voyager is a **Zulip bot named `voyager`** on the **Lean Zulip**
(`https://leanprover.zulipchat.com`), posting in the **Tau Ceti** channel. Messages appear
under the name *voyager* with Zulip's `BOT` tag, so readers can tell them from a human's.

### One-time setup (a human must do this)

1. On leanprover.zulipchat.com: gear menu → **Personal settings → Bots → Add a new bot**.
   Bot type **Generic bot**, full name `voyager`. Zulip issues an email of the form
   `voyager-bot@leanprover.zulipchat.com` and an **API key**. Give it an avatar so it is
   recognisable in the channel.
   *If "Add a new bot" is unavailable, bot creation is restricted for your role — ask a Lean
   Zulip administrator.*
2. **Subscribe the bot to the `Tau Ceti` channel.** A Zulip bot cannot post to a channel it
   is not subscribed to; this is the single most common cause of a 400 from `send_message`.
3. Put the credentials in the environment (or the repo's Actions secrets) using the same
   names `scripts/pr_status/zulip.py` already uses — reuse that module rather than writing a
   second Zulip client:

```
ZULIP_SITE      https://leanprover.zulipchat.com
ZULIP_EMAIL     voyager-bot@leanprover.zulipchat.com
ZULIP_API_KEY   <the bot's API key>
ZULIP_CHANNEL   Tau Ceti
ZULIP_TOPIC     new results          ← Voyager's own topic, NOT the "PRs" topic
GH_TOKEN        for the gh CLI
```

Note that the existing PR-status bot is a *different* bot writing to *the same channel*
under the topic `PRs`. Do not post Voyager updates into `PRs`, and do not touch that bot's
messages.

For local trial runs, keep the credentials in `~/.zuliprc` (the standard Zulip config format,
`chmod 600`) and export them into the environment at the start of each run:

```ini
[api]
email=voyager-bot@leanprover.zulipchat.com
key=<the bot's API key>
site=https://leanprover.zulipchat.com
```

```bash
export ZULIP_EMAIL=$(awk -F= '$1=="email"{print $2}' ~/.zuliprc)
export ZULIP_API_KEY=$(awk -F= '$1=="key"{print $2}' ~/.zuliprc)
export ZULIP_SITE=$(awk -F= '$1=="site"{print $2}' ~/.zuliprc)
```

`scripts/pr_status/zulip.py check` is a ready-made credentials probe: it authenticates and
confirms channel subscription without posting. Run it first after setup.

## Prerequisites

Tools: `gh` CLI (authenticated), `git`, python3 stdlib only, `uvx` (for a review that says no,
§8), the npm **`codex` CLI** (OpenAI; driven through `~/.claude3/voyager/gate.sh`, which tries
`CODEX_HOME=~/.codex` then `~/.codex2`) for the significance gate, and a local Mathlib checkout
for the novelty gate (the roadmap repo's `.lake/packages/mathlib` is fine).

If credentials are missing, **stop and report** — do not post to a fallback channel and do
not invent a message.

## Running it

Three ways, in increasing order of automation. All three execute this same file, so the
logic lives in one place.

**By hand, in a Claude Code session:** `/voyager` (namespaced `/mathlib-quality:voyager` while
the skill ships in the `mathlib-quality` plugin, which every Claude account on this machine
already has installed).

**As a launched agent** — this is the intended mode while the bot is being trialled. Spawn a
general-purpose agent with:

> Follow the instructions in `skills/voyager/SKILL.md` of the mathlib-quality repo
> (`~/Documents/GitHub/mathlib-quality`, github.com/CBirkbeck/mathlib-quality) and carry out
> one Voyager run: read the watermark from the last Voyager message on the Lean Zulip
> `Tau Ceti > new results` topic, find named theorems and notable definitions added to
> TauCeti since that commit, apply the Mathlib-novelty and ChatGPT significance gates, and
> post the update. If nothing survives the gates, post nothing and report that.

The agent needs the Zulip env vars, an authenticated `gh`, and the npm `codex` CLI on PATH
(the significance gate runs through it, not through an MCP — see §4). Give it `Bash`, `Read`,
`Grep`, `Glob`. It does **not** need write access to any repository — Voyager never commits
anything. Its reviews (§8) are a comment and issues on the review site, which any signed-in `gh`
can make.

**On the schedule** (the intended cadence): twice a day, at 04:03 and 16:03 UK (owner-chosen
slots; twice daily since 2026-10-10, once at 16:03 before that). Timing is forgiving because
the window ends at the **`docgen` branch** (see §1), which by construction only advances
when a complete docgen run is published — so whenever Voyager runs, everything in its window
has docs pages, and there is nothing to wait for. (Background, in case the branch mechanism
ever breaks: the docs rebuild is nominally scheduled 06:00 UTC but starts ~08:00–08:35 UTC
after GitHub's delay, takes 60–90 minutes, and some days fails outright — which is exactly
why tracking `docgen` beats tracking `main` plus polling `pages.yml`.) As a GitHub Actions
workflow the same logic applies with `schedule: - cron: "3 3,15 * * *"` (UTC, which is UK
time in winter). GitHub's scheduled runs are best-effort; the watermark protocol makes
missed days harmless, since the next run picks up the whole missed window.

Whichever way it runs, the eventual home is the Tau Ceti CLI. Keep the decision logic here
rather than in shell scripts so it can be lifted across intact.

## The watermark protocol

Voyager keeps no external state file — and, learned in production, **no machine state in the
channel message either: Zulip renders HTML comments as visible text**, so a `<!-- ... -->`
footer shows up as literal garbage to every reader. The watermark lives in a **DM the bot
sends to itself**, which nobody else sees:

```
voyager-state
`commit=<full sha> pr=<total merged PR count> ts=<ISO8601>`
```

`pr=` is the **total number of merged PRs at the docgen commit** (the squash-commit count
from §7), **not** the highest PR number — PR numbers share a sequence with issues, so the
two differ, and the since-last-update stat subtracts `pr=` from the current total.

Each run:

1. Read the newest self-DM: `GET /api/v1/messages` with `anchor=newest`, `num_before=1`,
   `apply_markdown=false`, narrow `[{"operator":"dm","operand":"<bot email>"}]`, and parse
   `commit=` / `pr=` out of it.
2. That `commit` is your **previous HEAD**.
3. No self-DM *and* no Voyager message on the channel topic → **first run** (see below).
   Channel messages but no self-DM (state was lost): reconstruct — take the newest Voyager
   channel message's timestamp, set `commit` to the last TauCeti commit merged before it and
   `pr=` to the merged-PR count at that time, write the DM, then proceed.
4. **After every successful channel post, send the updated state DM** — post first, DM
   second; if the DM write fails, retry it before ending the run. An update in several parts
   (§6, "Size and parts") is one post: the DM goes after its last part.

## Never double-post

The watermark alone is not enough — a DM write that fails after a successful post, a lost
state DM, or a second launch would all rescan an already-announced window. Three checks, all
mandatory, before every post:

1. **Permanent PR-number dedupe.** Fetch the bot's *entire* topic history (`get_messages`
   with the sender+topic narrow, `num_before=1000`) and extract every `TauCeti#<n>` ever
   cited. Drop any candidate whose PR number is in that set. PR numbers never recur, so a
   result announced once can never be announced again — regardless of what the watermark
   says.
2. **Name-level repeat rule.** Also collect the previously announced result *names* (the
   bold link texts). A candidate whose name matches one already announced posts only if it
   is a genuine strengthening from a *different* PR, and then the sentence must state the
   delta ("now for arbitrary null-homologous cycles", "extended to countable index types") —
   otherwise drop it as a restatement. A name that has appeared only in an in-progress line
   was not announced: its bullet goes out when it lands in full, saying "now in full". A name
   that has appeared in any earlier in-progress line never goes in another one.
3. **Freshness abort.** If the newest Voyager channel message or state DM is less than
   2 hours old, another run just happened or is still in flight: abort without posting.
   On the daily cadence, fresher activity is never legitimate.

## Procedure

### 1. Establish the window

**The window ends at the `docgen` branch, not `main`.** TauCeti's `docgen` branch (set up in
TauCeti#1539) tracks the most recent commit on main **for which a complete docgen run is
published** — so everything inside the window is guaranteed to have API-docs pages, results
merged after the docs point simply wait for the next run (≤ half a day), and no docs-workflow
polling is needed. The Tau Ceti review site, where the bullets link (§6), follows the same branch,
so everything in the window has a page there too once the site has caught up: check it now (§6,
"Verify every link on the site") and start its update if it is behind.

Clone with **full history** — step 5 needs it for PR attribution, and a shallow clone breaks
that silently:

```bash
git clone https://github.com/TauCetiProject/TauCeti tc   # or fetch an existing clone
cd tc && git fetch origin '+refs/heads/docgen:refs/remotes/origin/docgen' && git checkout -q origin/docgen
git log --oneline <previous-sha>..origin/docgen | wc -l
```

If `origin/docgen` equals the watermark commit, there is nothing to do: **exit without
posting.** Compute the stats (§7) at the `docgen` commit too, so the numbers describe the
same tree the window ends at.

### 2. Extract candidates

**Work PR-by-PR — the merged PRs are the unit of discovery.** TauCeti squash-merges, so
`git log --format='%s' <watermark>..HEAD` lists exactly the window's PRs, one per commit,
with the number in the subject (`feat: prove the double centralizer theorem (#1435)`).
Triage by title: `feat:` is where announcements live; `chore:`/`refactor:`/`fix:` almost
never are. Then, for each candidate,
`gh pr view <n> --repo TauCetiProject/TauCeti --json title,body` — the body typically says
what was proved, names the result, and cites the roadmap and references, which is exactly
the raw material for the significance gate and for writing the one-sentence description.
The PR is also the attribution unit, so this hands you the link for free.

**Cross-check with the module-title sweep — a bland PR title can hide a named result.** Every
Tau Ceti file opens with a `/-! # Title` naming what it contains, and named results are named
there in English. Diff the titles of files added in the window:

```bash
git diff <previous-sha>..HEAD --diff-filter=A --name-only -- '*.lean' \
  | while read -r f; do printf '%s\t' "$f"; grep -m1 '^# ' "$f"; done
```

Scanning ~30 English titles beats scanning 800 declaration names, and titles like
"Harnack's inequality on a planar disk" or "The de Finetti–Ryll-Nardzewski summit and
equivalences" identify themselves instantly. Titles also tell you what is *not* a result:
"Approximating measures for Bernstein's theorem" is scaffolding for a target, not the target.

Then, inside each identified file, read the `## Main results` / `## Main declarations` section
to pick which declaration to name. A result may be *added* in one PR and *completed* in a
later one, so check that the statement you name is the theorem and not a stepping stone.

Second, catch results added to *existing* files, which the title sweep misses. Diff the
declarations and prefilter aggressively before spending any model time:

```bash
git diff <previous-sha>..HEAD -- '*.lean' | grep -E '^\+\s*(theorem|lemma|def|structure|class|abbrev|instance)\b'
```

- drop names matching `aux|helper|internal|step|_impl|^private|_eq$|_def$|_apply$|_comm$|_assoc$|_simp|_lemma_[0-9]+`;
- drop anything with no doc-comment;
- **keep** anything whose doc-comment carries an eponym or a citation (`Theorem N.N`,
  `[Author]`, `§`), or that is listed under a `## Main results` heading.

A useful cross-check on both passes: an eponym grep over the diff,
`grep -iE '<name1>|<name2>|…'`, seeded from the eponyms already in the library.

**Then check every survivor's name and strength.** This is where most weak bullets used to
slip through. For each candidate, write down in your notes (not in the post):
- the standard name;
- where that name is used (a Wikipedia page, a textbook's theorem, a paper);
- the statement there;
- whether the Lean statement proves that statement in full (the full-statement test).

Drop anything that fails the full-statement or importance test in *What counts*. Side
results that came in the same PR are separate candidates, not material for the headline's
bullet.

### 3. Novelty gate — is it already in Mathlib?

The comparison target is **current Mathlib master**, not any local checkout. A pinned
Mathlib (the roadmap repo's `.lake/packages/mathlib`, or whatever TauCeti builds against)
can lag master by months, and results land upstream continuously. This is not hypothetical:
a June-pinned checkout said "no Fredholm operators in Mathlib" while master had gained
`ContinuousLinearMap.IsFredholm` (mathlib4#41189) days earlier — only a master search caught
it. Releases also lag master; if a result is on master but in no release yet, say so rather
than rounding to "Mathlib has it" or "Mathlib lacks it".

For each survivor, in this order, and be strict:

1. **Fast triage** against a local checkout:
   `grep -rn "theorem <name>\|lemma <name>\|def <name>" <mathlib>/Mathlib`. A hit here kills
   the candidate cheaply; a miss decides nothing.
2. **Master name/file search** — authoritative for presence:
   `gh search code --repo leanprover-community/mathlib4 "<term>" --json path` (code search
   runs against the default branch, i.e. master). Ignore hits in `docs/1000.yaml` /
   `docs/undergrad.yaml` — those are wishlists, not formalisations.
3. **Statement check** — the important one, since Mathlib may hold the same theorem under a
   different name. Use the `lean-lsp` MCP: `lean_leansearch` (natural language),
   `lean_loogle` (type pattern). Rate limits apply, so batch and go in order of suspicion.
4. **Same eponym ≠ same theorem.** Open the hit and read what it actually states before
   ruling either way: Mathlib's `LocallyConvex/Montel.lean` is Montel *spaces*, not Montel's
   selection theorem; its C*-algebra "double centralizer" (multiplier algebra) is not the
   semisimple-module double centralizer theorem; the Fredholm *alternative* is not the
   Fredholm *operator* class. A name hit is not a statement hit, in either direction.
5. **Read the Tau Ceti docstring.** Tau Ceti files are honest about this: they routinely
   say "Mathlib's X" when consuming, and "not in Mathlib" when adding. Believe the
   docstring but spot-check it — it states the situation as of the file's writing, and
   upstream may have moved since.

There are three outcomes, not two:

- **New** — Mathlib does not have it. Announce.
- **Already in Mathlib, or a repackaging of a Mathlib result.** Do not announce. If Mathlib
  has it in *weaker* generality and Tau Ceti genuinely strengthens it, that **does** count,
  but say precisely what is new ("Mathlib has this for finite extensions; this is the
  infinite case").
- **New to Mathlib but overlapping in-flight upstream work.** Announce, *with the
  coordination note* — one clause naming the Mathlib PR. Tau Ceti files flag this
  themselves, in a `## Coordination with upstream Mathlib` docstring section.

Worked calibration from the library as it stands, so you can see where the lines fall:

| Declaration | Verdict | Why |
|---|---|---|
| `TauCeti.hungerbuhlerWasem_residueTheorem` | **announce** | Mathlib has no residue theorem allowing contours through poles; no upstream overlap |
| `TauCeti.rouche` | **announce, with note** | its own docstring says "Mathlib has no Rouché theorem", but the file is a declared temporary shim overlapping [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505) |
| `TauCeti.norm_deriv_lt_div_of_not_injOn` (`Conformal/Schwarz.lean`) | **skip** | a strict form built directly on Mathlib's `Complex.norm_deriv_le_div_of_mapsTo_ball`; the file calls itself a temporary shim. Announcing "Schwarz's lemma" here would be a false claim |
| `NumberField/Units/Dirichlet.lean` | **skip** | restates Mathlib's `NumberField.Units.exist_unique_eq_mul_prod` in structural form. Mathlib already has Dirichlet's unit theorem |
| Gårding's inequality, BCR Bochner, Gabriel's theorem | **skip** | these are roadmap *targets*; the library has the surrounding theory (energy forms, positive-definite functions, quiver reflections) but not the named theorem. Never announce a target as a result |
| `TauCeti.IsFredholm` + index (`Analysis/Fredholm/`) | **announce, with note** | the Fredholm *predicate* landed on Mathlib master 2026-07-28 ([mathlib4#41189](https://github.com/leanprover-community/mathlib4/pull/41189), TVS generality, unreleased) ten days after Tau Ceti's #984 — but the index theory and Atkinson did not. Announce the whole with the overlap stated; a June pin missed this entirely |
| TauCeti#1942, "the Weyl dimension formula for `GL n`" | **skip** | the file builds the formula *as a natural number* (integrality, positivity, Vandermonde identities) and attaches it to no representation. A title is not a theorem |

Two of these traps deserve naming twice. A directory called `Analysis/PositiveDefinite/`
full of Bochner-adjacent machinery does **not** mean Bochner's theorem is proved — find the
theorem statement, or do not announce it. And a file or PR *titled* "the X formula/theorem"
may contain only scaffolding for it (the #1942 near-miss, 2026-08-04) — read the module
docstring's *Main results* before believing any title.

### 4. Significance gate — the ChatGPT second opinion

**Model policy (owner request, 2026-09-07): always the most capable current OpenAI reasoning
model — today `gpt-6-astra`, which replaced `gpt-5.6-sol`. When OpenAI ships a newer top
model, bump the name here, in HANDOVER.md, and in the scheduler's `gate.sh`
(`~/.claude3/voyager`).** The gate runs through the npm `codex` CLI
(`npm i -g @openai/codex@latest`, ≥ 0.153); the old `chatgpt-math` MCP wrapper rejects every
model on a ChatGPT account and is no longer used.

**Account policy (owner request, 2026-09-10): two OpenAI accounts, same model on both.** The
helper `~/.claude3/voyager/gate.sh` owns the choice: it probes the primary account
`CODEX_HOME=~/.codex` and falls back to `~/.codex2` when the primary cannot serve (usage limit,
missing credentials, model rejected), and it retries on the other account if the first hits its
limit between the probe and the batched call. Never hand-roll `codex exec` or pick an account
yourself, and never print anything from either account's auth files.

Probe first, then batch **all** surviving candidates into **one** call:

```bash
~/.claude3/voyager/gate.sh probe            # prints GATE_ACCOUNT=<CODEX_HOME> or GATE_UNAVAILABLE
~/.claude3/voyager/gate.sh ask /tmp/voyager-gate-question.txt /tmp/voyager-gate-answer.md
                                            # prints GATE_SERVED_BY=.codex|.codex2, GATE_PENDING
                                            # or GATE_UNAVAILABLE; effort high
```

The call takes 4–10 minutes. `gate.sh ask` runs it in its own systemd user unit
(`voyager-gate.service`) and blocks for at most 9 minutes. **Run it in the foreground with the
Bash timeout at 600000.** On `GATE_PENDING`, run the *same* command again: it re-attaches to the
running call rather than starting a second one. To work in parallel, start it with
`GATE_WAIT=0 … ask …` (returns `GATE_PENDING` at once), do the stats, anchors and `sorry` gate,
then run the plain `ask` again to collect. **Never detach it yourself** (`run_in_background`,
`&`, `nohup`, `setsid`): Claude Code kills detached children when the tool call ends, which
lost the gate call on 2026-09-21. **Never end your turn while it is pending**: a headless run
ends with its turn, which lost the whole run on 2026-09-20.

(Underneath, `gate.sh ask` runs `codex exec --ephemeral --skip-git-repo-check -s read-only
-m gpt-6-astra -c model_reasoning_effort="high" -o <answer> "$(cat <question>)" < /dev/null`
with the chosen `CODEX_HOME`.)

Operational facts learned the hard way:

- reasoning effort `high`. **`ultra`/`max` reliably time out** on long prompts — `high` has
  been reliable;
- read the verdicts from the answer file (the helper already passes `< /dev/null`, without
  which codex blocks on stdin);
- run `gate.sh probe` **before** reading the window, so an unavailable gate costs seconds
  instead of a 138-PR read; a usage-limited primary account is a normal condition — the
  helper falls through to `~/.codex2` (2026-09-10: primary limited until 2026-09-15);
- one batched call, not one per candidate: each call costs minutes;
- the question must be **self-contained** — the model has no file access, so paste the
  declaration name, its statement, and its docstring summary;
- the gate is **required** (owner decision, 2026-10-10: every post is made with Fable and
  Astra). When no OpenAI account can serve (quota, the plan rejects the model, codex missing,
  timeout), `gate.sh` itself falls back to Claude Fable (`claude-fable-5-1`, API billing) with
  the same question and reports `GATE_SERVED_BY=claude-fallback` (owner decision, 2026-10-30:
  a post must still go out when Astra is unavailable). Only if the fallback fails too: post
  nothing, leave the watermark, and end the run as failed so the scheduler retries later.
  Record the model and which account served (`GATE_SERVED_BY`) in the run log and the state
  DM, never in the Zulip message; never pick a model or account by hand.

Prompt template:

```
I am triaging newly added results in a Lean mathematics library to decide which are
worth announcing to working mathematicians. For EACH numbered item below, answer with
one of:

  ANNOUNCE  — an important named result or notable definition, proved in full. It has a
              Wikipedia page, or is a named theorem/definition in a standard textbook or
              paper, or is an eponymous result people in the area know by that name, or
              is a definition the surrounding subject is phrased in; AND the Lean
              statement proves it as a standard textbook or the original paper states
              it (a more general version elsewhere does not make it partial).
  PARTIAL   — a named result, but the Lean statement is weaker than a standard
              statement of it: a special case, one direction or part, an extra
              hypothesis, or conditional on an unproved input. Say what is proved, in
              at most six words, and mark it MILESTONE if that part is a big step a
              reader in the area would care about (the main case, one of two main
              halves), or MINOR otherwise.
  SKIP      — an auxiliary lemma, API glue, a routine special case, a step towards a
              larger theorem, or a name used only by its own paper.

For each ANNOUNCE, add: (a) the standard name, (b) what it asserts, in at most 30 words,
for a mathematician who does not know it, (c) whether it has a Wikipedia page, and (d)
one standard reference.

Be conservative: a false ANNOUNCE costs more than a false SKIP. Do not be polite about
it. Rank the ANNOUNCE items by importance, most important first.

<numbered list: name, Lean statement, docstring summary>
```

PARTIAL items get no bullet; the theorem goes out when it is proved in full. A PARTIAL
marked MILESTONE may go in the in-progress line (§6) if it passes the importance test and
has never been named there before; MINOR ones are left out. A part with a standard name of
its own comes back as ANNOUNCE under that name.

Take its verdicts as **advice, not authority**. It has been wrong before on this project —
it misnumbered a Wedhorn theorem and mis-attributed a Mathlib file's authors. If a verdict
looks wrong, check the primary source and use your judgement. Never post a description you
have not sanity-checked against the actual Lean statement.

### 5. Attribute each result to a PR

Readers must be able to click through. TauCeti squash-merges, so the PR number is already in
the commit subject as `(#1443)` — read it off the commit that added the file rather than
querying the API:

```bash
git log --diff-filter=A --follow --format='%s' -1 -- <file> | grep -oE '#[0-9]+' | head -1
```

**A shallow clone silently breaks this.** With `--depth`, `--diff-filter=A` finds the graft
boundary for every path, so *every* file appears to have been added by the most recent
commit — you get one plausible-looking PR number for everything. If several unrelated files
report the same PR, that is the bug. Check with `test -f .git/shallow` and
`git fetch --unshallow` before trusting any attribution. Note also that in a sandboxed shell
`git` may have no network while `gh` does; fetch accordingly.

- Cite the PR as bare `TauCeti#<n>` — the Lean Zulip's linkifier turns it into a link.
- The bold result name links to the declaration's page on the **Tau Ceti review site** (see §6).
- If no PR can be found (direct push), cite the commit hash with an explicit link.
- Never announce something you could not link.

### 6. Compose and post

Format (Zulip markdown):

```markdown
**Voyager · what's new in Tau Ceti**

*Named results*
- **[<Standard name>](<review-site link>)** — <one sentence, at most 40 words, on what it asserts> (<one short reference>). (TauCeti#123)
- ...

*Notable definitions*
- **[<Name>](<review-site link>)** — <what it is and what it is for, at most 40 words>. (TauCeti#124)

*In progress* — <Standard name>: <what is proved, at most six words> (TauCeti#125); <…>

*Stats*
- <N> lines of Lean across <M> files (Tau Ceti only, excluding Mathlib)
- <D> declarations
- <P> PRs merged since the last update (<T> total)
```

…then send the updated state DM (see the watermark protocol), then leave the reviews of what you
checked (§8).

Zulip-specific rules, each learned from reader feedback on the first message:

- **One physical line per paragraph and per bullet.** Zulip keeps single newlines as line
  breaks, so hard-wrapped prose renders with ragged mid-sentence breaks. Never wrap.
- **Use the realm linkifiers**: bare `TauCeti#NNN` for TauCeti PRs, `mathlib4#NNN` for
  Mathlib PRs — not explicit markdown PR links.
- **Link each bold result name to the declaration's page on the Tau Ceti review site** (owner
  request, 2026-10-24), where a reader sees the statement as the docs show it and what it rests on,
  and can review it, suggest a test or say what could be better:
  `https://cbirkbeck.github.io/tauceti-reviewed-by-test/#/d/<Fully.Qualified.Name>`, the name
  percent-encoded as a URI component (Python `urllib.parse.quote(name, safe="")`; most names need
  nothing). **Take the name from the API docs, never construct it**: curl the published page,
  `https://taucetiproject.org/docs/TauCeti/<Module/Path>.html` (expect 200), and pull the real
  `id="…"` out of its HTML. Namespaces vary and some files have no `TauCeti` namespace at all
  (`lieExp`, `pointDerivationEquivTangentSpace`, `ModularForm.lSeries`,
  `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective` are bare or foreign-namespaced);
  probability lives under `TauCeti.Probability.*`, Lévy downward under `MeasureTheory.*`. **Link
  the declaration the headline claims, never the containing definition** — a bullet titled "…is
  finite" links the finiteness statement (`instFinite`), not the group it is about; the maintainer
  caught exactly this once.
- **Verify every link on the site before posting.** The site follows the `docgen` branch your
  window ends at: it checks every 20 minutes and rebuilds in about 45, so at the time of a run it
  can be behind.
  1. Right after establishing the window (§1), run the check below with the `docgen` commit and no
     names: it prints the site's commit. If that is not the `docgen` commit, start the site's update
     once, `gh workflow run follow.yml -R CBirkbeck/tauceti-reviewed-by-test`, and carry on with the
     gates; it is ready long before you are.
  2. Before posting, run the check with the `docgen` commit and every name you will link. It waits,
     at most nine minutes per call, until each name is on the site or the site has reached the
     `docgen` commit. On `SITE_PENDING`, run it again, for up to 90 minutes in all. Run it in the
     foreground with the Bash timeout at 600000; never detach it, and never end your turn while it
     is pending.
  3. Every name must print `ON-SITE`. A name still `MISSING` with the site at the `docgen` commit (the
     site's extractor skips a module that did not build for it), or after 90 minutes: link that
     bullet to the API docs anchor instead, `https://taucetiproject.org/docs/TauCeti/<Module/Path>.html#<Name>`
     (curled, 200, the `id` present), and say in the run log which name and why. Never post a link
     you have not verified.

  ```bash
  python3 - <docgen-sha> <Name> <Name> … <<'PY'
  import json, sys, time, urllib.request
  SITE = "https://cbirkbeck.github.io/tauceti-reviewed-by-test/data/"
  def get(path):  # past the Pages cache: the build may be minutes old
      return json.load(urllib.request.urlopen(f"{SITE}{path}?t={time.time():.0f}", timeout=60))
  def on_site(meta, name):  # the site's own name lookup (FNV-1a over UTF-16 code units)
      h, data = 0x811C9DC5, name.encode("utf-16-le")
      for i in range(0, len(data), 2):
          h = ((h ^ (data[i] | data[i + 1] << 8)) * 0x01000193) & 0xFFFFFFFF
      ids = [r[0] for r in get(f"names/{h % meta['shards']['names']}.json") if r[1] == name]
      n = meta["shards"]["nodes"]
      return bool(ids) and get(f"nodes/{ids[0] // n}.json")[ids[0] % n][2] & 1 == 1  # one of Tau Ceti's own
  target, names = sys.argv[1], sys.argv[2:]
  deadline = time.time() + 540
  while True:
      meta = get("meta.json")
      missing = [x for x in names if not on_site(meta, x)]
      if not missing or meta["library"]["commit"] == target or time.time() > deadline:
          break
      time.sleep(60)
  print("site at", meta["library"]["commit"], "· docgen at", target)
  for x in names:
      print("MISSING" if x in missing else "ON-SITE", x)
  if missing and meta["library"]["commit"] != target:
      print("SITE_PENDING")
  PY
  ```
- **Links rot after posting**, on the site as in the docs: both show only the current build, so a
  link that verified at post time dies when a later refactor renames or deletes the declaration (in
  the docs era: `Montel.lean` → `Montel/`, `JordanCurve.lean` → `JordanCurve/Basic.lean`, the
  Fredholm upstreaming that deleted `TauCeti.IsFredholm` and `Parametrix.lean` outright). Re-audit
  periodically and after any large refactor lands, with the check above over the topic's links.
  Retarget a renamed declaration to its new name (the site's Named page lists each announcement under
  its current name); for one deleted from the tree, use a pinned-commit permalink to the source
  (`https://github.com/TauCetiProject/TauCeti/blob/<sha>/<path>`), which cannot rot. In-place edits
  of posted messages remain maintainer-request-only, as below.
- **Bold goes OUTSIDE links**: `**[Name](url)**`, never `[**Name**](url)` — Zulip renders
  markup inside link text literally, so the reader sees raw asterisks.
- **No HTML comments anywhere** — Zulip renders them as visible text.
- **Tone**: state what Tau Ceti adds; never "Mathlib doesn't have this" / "Mathlib has none
  of these". Overlap notes are neutral and specific: "also being formalised in
  mathlib4#33505", "landed independently in Mathlib master on <date>".
- **Length**: Zulip caps a message at 10,000 *codepoints* and — worse — an edit that
  exceeds the cap returns **success while silently truncating** the rendered message with a
  trailing "[message truncated]" (this happened: it cut "Mathlib" to "Math" mid-word and ate
  the stats block). Count codepoints before sending (`len()` in Python on the exact
  content), stay under ~9,500 in every part, and **verify the rendered tail after every
  post or edit** (`GET` the message with `apply_markdown=true` and check that its last bullet,
  and in the last part the stats lines, are present, and "[message truncated]" is not).

Rules for the prose. **Short is the house style.**

- **One sentence of at most 40 words** per bullet, not counting the bold name, the reference
  and the PR citation. 20–30 is the norm. Write for a mathematician who does not know the
  result.
- **Say what the theorem asserts, and nothing else.** Leave out:
  - how it is proved;
  - what it is built from ("the input is…", "because…");
  - what else landed with it ("with it…", "on the way…");
  - what is planned next.

  Side results are separate candidates.
- **One link per bullet**: the bold name. No further inline links inside the sentence.
- **One short reference**, such as "(Fulton, *Young Tableaux*, §1.1)" or "(Schensted 1961)",
  not a list.
- **A scope clause only when needed**: when the formalized statement differs from the
  standard one in a way a reader must know. Then first ask whether the result passes the
  full-statement test at all.
- If a result strengthens Mathlib, say so in a clause.
- No marketing adjectives; no "exciting"/"major milestone". State what the theorem says,
  not how impressive it is.

**Size and parts** (owner request, 2026-10-24). Space never decides what goes in. Every result
that passes *What counts* gets its bullet, however many there are: when they do not fit in one
message under ~9,500 codepoints, post the update in parts. Never drop, merge or shorten a
qualifying bullet to fit one message; that is what made the October posts stop just under the
cap. Equally, never relax the bar to fill a part. What goes in is unchanged: named results and
notable definitions people in the area know by name, each proved in full, and in the
in-progress line only big milestones, once per theorem, never steps towards the same goal.
- **Split between bullets**, never inside one, each part under ~9,500 codepoints.
- **Every part is readable on its own**: its header line is
  `**Voyager · what's new in Tau Ceti** (part k of n)`, with whatever suffix the header carries,
  and it repeats the section heading (`*Named results*`, `*Notable definitions*`) over its
  bullets. The review site reads each message on its own, and takes a bullet's kind from the
  heading above it.
- **The in-progress line and the stats block** go in the last part only.
- **Post the parts in order**, verifying each one's rendered tail before posting the next. Send
  the state DM after the last. If a part fails to post, stop and report, leaving the watermark:
  the next run's PR dedupe drops what already went out and posts the rest.
- **More than about three parts** is rare: it can happen after a long quiet spell, but more
  often it means the bar has slipped. Re-apply the tests in *What counts* to every candidate
  before posting that much.

**The in-progress line** (owner request, 2026-10-12: "progress has to be meaningful … we want
big milestones only") names big milestones that have partly landed, so readers see them
coming without a premature bullet.
- **Big milestones only**: an important named theorem (the importance test) whose main case,
  or one of its two main halves, is now proved. Never a technical step, a lemma on the way,
  or lettered parts of a result.
- **The form**: the name, what is proved in at most six words, and the PR, e.g.
  "Schensted's theorem: the increasing-subsequence half (TauCeti#14191)".
- **Once per theorem, ever.** Collect the names from every earlier in-progress line in the
  topic history and never name one again. The theorem comes back only as a full bullet,
  when it lands in full, with "now in full" in its sentence.
- **Rarely more than three entries.** When nothing qualifies, leave the line out. A post with
  no bullets is still the short check-in, even if something partly landed.

A worked example from the 2026-10-11 post. Before (78 words, five links):

> - **[The fundamental theorem of Γ-convergence](…)** — for a sequence of extended-real functionals Fₙ on a first-countable space that Γ-converges to f in the sequential sense ([liminf inequality and recovery sequences](…)) and is [equicoercive](…), the infima of the Fₙ converge to the infimum of f, which [is attained](…), and cluster points of minimisers minimise f; sequential Γ-convergence is [equivalent to the Γ-liminf and Γ-limsup both being f](…) (Braides, *Γ-convergence for Beginners*, Ch. 1; Dal Maso, Chs. 7–8). (TauCeti#14447)

After (26 words, one link):

> - **[The fundamental theorem of Γ-convergence](…)** — if Fₙ Γ-converges to f and the Fₙ are equicoercive, then inf Fₙ → min f, and cluster points of minimisers of the Fₙ minimise f (Braides, *Γ-convergence for Beginners*, Ch. 1). (TauCeti#14447)

**Quiet runs still report.** If the window contains newly merged PRs but nothing survives
the gates, post this short check-in instead of the full format:

```markdown
**Voyager · Tau Ceti check-in**

No notable named results landed in this window (as judged by the voyager AI bot).

- <P> PRs merged since the last update (<T> total)
- <N> lines of Lean across <M> files (Tau Ceti only, excluding Mathlib)
```

…followed by the updated state DM, like any other post — the check-in advances the
watermark and becomes the reference point for the next run. Only a genuinely empty window (HEAD equal to the watermark commit,
nothing merged at all) posts nothing, so a quiet night does not fill the topic with identical
zero-change check-ins.

### 7. Stats

```bash
# LOC, Tau Ceti only. Do NOT "simplify" this to `xargs wc -l | tail -1`: xargs splits
# 5,000+ files into several batches, wc prints a `total` per batch, and tail -1 then
# reports only the LAST batch. That shipped a wrong number twice: 2026-09-17 (224,676
# against a true 1,280,610) and 2026-09-21 (365,766 against 1,443,324) — the fix for
# the first sat uncommitted, so the second run read the old recipe. cat into one
# stream and count once.
find TauCeti -name '*.lean' -print0 | xargs -0 cat | wc -l
find TauCeti -name '*.lean' | wc -l                        # files
grep -rhcE '^(theorem|lemma|def|structure|class|abbrev|instance)' --include='*.lean' TauCeti | awk '{s+=$1} END {print s}'
git log --format=%s origin/docgen | grep -cE '\(#[0-9]+\)$'      # T: PRs merged, at the docgen commit
```

**Sanity-check every stat against the previous post before you publish.** The library is
append-mostly, so LOC, files and declarations should each be *slightly up* on the last
update — a few tens of thousands of lines per day at the current rate. Any figure that
falls, or jumps by a factor, is a broken recipe and not a real measurement: read the
previous post's stats block and compare all three. On 2026-09-17 a LOC figure of 224,676
went out against the previous day's 1,246,270 — an 82% overnight "drop" that this one
comparison would have caught before posting. If a figure fails the check, fix the recipe
and recompute; never post it.

Do **not** report `sorry` counts in the stats (owner decision). The no-`sorry` rule remains
an announcement *gate*: check nothing you announce has a `sorry` in its file, remembering a
docstring can mention the word without it being a proof hole.

"PRs merged since the last update" = the number of squash-merge commits in the window
(each carries its `(#N)`), which is exact and consistent with what was actually scanned.
The total `T` counts the same commits over the whole docgen history.
- **Never use GitHub's merged search.** Tau Ceti lands pull requests through bors, which
  closes them instead of merging them, so that count stopped moving in October 2026
  (11,535 on 2026-10-12).
- **Check.** On 2026-10-12 the commit count gave 13,783 at docgen `1885e7be`, the figure
  that was posted.
- **Cross-check.** `T` minus the previous `pr=` equals `P` when the window starts at the
  previous post's docgen commit.

Exclude `.lake/` and any vendored Mathlib from every count — the LOC number is meant to be
*Tau Ceti's own* contribution and is the number most likely to be quoted.

The `sorry` grep counts **mentions**, not proof holes: a docstring saying "the `sorry`-goal in
`Suggested.lean`" matches too. The hit count is tiny, so read every hit and report only real
`sorry` terms. (As of `a695b8c` the library's one grep hit is a docstring mention — the honest
number was 0.)

### 8. Review what you checked

Owner request, 2026-10-24: Voyager leaves a review on the Tau Ceti review site of every result it
checks. The full-statement test of §2 (the standard name, where it is used, the statement there,
and whether the Lean statement proves it) is the question the site asks of a declaration — is it
correctly stated? — so its answer is recorded there, for every candidate whose statement you
compared, announced or not.

- **Yes** when the Lean statement says what its name and docstring say it does. A correctly
  labelled special case is a yes, though it gets no bullet.
- **No** when they claim more or other than it proves: the full named theorem for a special case,
  one direction or one part, an extra hypothesis, a different object or convention. Say what is
  claimed, what is stated, and the source you compared it with.
- **Nothing** for a candidate dropped before its statement was compared (a helper, no docstring,
  the importance test failing first), and for anything you did not read at the window's commit.

Every answer counts, so give it even when the declaration has answers already. Its reasons are
evidence, and the site shows every answer's, so they say only what the answers already there do
not (`reviews` below lists them): a second source that states it as Lean does, a check not yet
listed. With nothing to add, a yes is the name alone; a no that an open no already makes can say
just that (`as #N`), and anything more.

Do it after the post and the state DM. A failure here never touches them: report it in the run
log, and the next run does not redo it.

```bash
# The helper at origin/main, like this file; the plugin's copy if the clone is missing.
RS=/tmp/voyager-review_site.py
git -C ~/Documents/GitHub/mathlib-quality show origin/main:scripts/review_site.py > "$RS" 2>/dev/null ||
  cp "${CLAUDE_PLUGIN_ROOT:-$(ls -d ~/.claude/plugins/cache/*/mathlib-quality/*/ | sort -V | tail -1)}/scripts/review_site.py" "$RS"
python3 "$RS" reviews <name> <name> …      # the answers each already has, and their reasons
python3 "$RS" yes yes.tsv --agent "Voyager, <your exact model>" --commit <docgen sha> --skip-missing \
  --note "Checked in Voyager's full-statement test for the update of <date>: <link to the post>."
python3 "$RS" no why.md --agent "Voyager, <your exact model>" --decl <name> --commit <docgen sha> --category <axis>
```

- `<your exact model>` is the model you run as, exactly as your harness names it (`claude-opus-5-5`,
  `GPT-6 Astra`), never its family (`Opus`, `GPT-6`), which the helper refuses: the site shows it
  beside each answer.
- `yes.tsv` has a line per declaration, `<name>[<TAB><reasons>]`, the reasons on one line and
  only what is new: what it states and the source it was compared with, e.g. `Correctly stated:
  … (Serre, *A Course in Arithmetic*, VII §4); compared in Voyager's full-statement test.` The
  helper posts them as one comment on the site's bulk issue, marked as Voyager's AI review.
- Each no is its own issue, and `why.md` holds its reasons: what the name and docstring claim,
  what the Lean statement says, and the source's statement with its citation. Its category:
  `object` (a different object), `convention`, `edge-cases`, `junk`, `vacuous`, `generality` (an
  assumption the name and docstring do not mention), `naming` (the name or docstring claims more
  than the statement), or `other`.
- The helper refuses a site not at the window's `docgen` commit, so a review is always of the
  version you checked. The site was waited for in §6; if it is not there (it never caught up, or
  has moved on since), skip the reviews this run and say so in the log. `--skip-missing` leaves out a name the site has no page for
  and prints it: name it in the log too.
- On the site these are AI reviews, counted apart from people's.

## First run (once, ever)

The first run happens **at most once in the lifetime of the bot**, and is detected solely by
the **absence of both a state DM and any prior Voyager message** on the topic — never by the
calendar, and never by how this particular run was launched. (It already happened:
2026-07-30, message id 613614529.) Every launch after that is incremental: new results
since the watermark, or silence.

There is a backlog: the library already contains a lot that has never been announced. On
that one first run, post the curated backlog in `first-run.md` (next to this file) as the
initial message, with the stats block computed live and a watermark set to current `HEAD`.
Do not attempt to re-derive the backlog from scratch — it was assembled by reading the
library and is already checked. If a Voyager message already exists on the topic, `first-run.md`
is dead weight: ignore it entirely, even if the backlog was never posted in full.

## Operating notes

- **Idempotence**: re-running must not double-post. Always read the watermark first; if the
  window is empty, exit silently.
- **Failure volume**: a transient Zulip 5xx or a single unresolvable PR link is cosmetic —
  log it and carry on. Missing credentials, a 401/403, or the bot not subscribed to the
  channel is a configuration failure: report loudly and exit non-zero without posting.
- **Never** edit or delete a previous Voyager message on your own initiative to "fix"
  history; post a correction as a new message if something announced turns out to be wrong
  or already in Mathlib. Editing in place is reserved for maintainer-requested fixes
  (formatting, links, tone), as happened with the first message.
- **Don't claim Tau Ceti proved something it consumed.** When in doubt about provenance,
  read the file header — Tau Ceti's docstrings distinguish the two carefully.
- This skill is being trialled by hand before it moves into the Tau Ceti CLI. Keep the
  logic in this file (not in ad-hoc shell history) so it can be lifted over intact.
