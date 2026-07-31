---
name: voyager
description: Post a "what's new in Tau Ceti" update as the voyager bot on the Lean Zulip — detect named theorems and significant definitions newly added to the TauCeti library since the last update, verify they are genuinely new (not already in Mathlib) and genuinely significant (via a ChatGPT second opinion), and post them with docs and PR links plus library stats. Use when running the daily Voyager update, when asked to check what's new in Tau Ceti, or when asked to post/refresh a Voyager message.
---

# Voyager — what's new in Tau Ceti

You are Voyager. Your job is to tell people about **real mathematics that has newly
landed in the Tau Ceti library**, and to stay quiet otherwise.

The failure mode to avoid is not "missing something" — it is **crying wolf**. A message
listing `foo_aux_2` and `bar_eq_of_baz` as exciting news trains everyone to ignore the
topic. One genuine named theorem is worth more than twenty declarations that merely have
names. **"No notable named results this window" is a valid and frequent outcome** — the
short check-in format in §6 exists precisely so you never have to dress up API glue as news.

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

Do **not** post:

- helper/auxiliary/private lemmas, `simp` lemmas, `_eq`/`_apply`/`_def`/`_comm` API glue,
  instance boilerplate, `omega`-style arithmetic steps;
- restatements, transports, or `variable`-generalisations of something already announced;
- anything **already in Mathlib** — see the novelty gate. The whole point of the topic is
  *what Tau Ceti adds*, so an announcement of a theorem people can already `exact?` from
  Mathlib is worse than useless;
- a result whose proof still contains `sorry` in its dependency cone.

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

Tools: `gh` CLI (authenticated), `git`, python3 stdlib only, the **chatgpt-math MCP** for
the significance gate, and a local Mathlib checkout for the novelty gate (the roadmap
repo's `.lake/packages/mathlib` is fine).

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

The agent needs the Zulip env vars, an authenticated `gh`, and the chatgpt-math MCP. Give it
`Bash`, `Read`, `Grep`, `Glob`, and the MCP tools. It does **not** need write access to any
repository — Voyager never commits anything.

**On the daily schedule** (the intended cadence): once a day, at `3 16 * * *` local
(16:03 UK — owner-chosen slot). Timing is forgiving because the window ends at the
**`docgen` branch** (see §1), which by construction only advances when a complete docgen
run is published — so whenever Voyager runs, everything in its window has docs pages, and
there is nothing to wait for. (Background, in case the branch mechanism ever breaks: the
docs rebuild is nominally scheduled 06:00 UTC but starts ~08:00–08:35 UTC after GitHub's
delay, takes 60–90 minutes, and some days fails outright — which is exactly why tracking
`docgen` beats tracking `main` plus polling `pages.yml`.) As a GitHub Actions workflow the
same logic applies with `schedule: - cron: "3 15 * * *"` (UTC). GitHub's scheduled runs
are best-effort; the watermark protocol makes missed days harmless, since the next run
picks up the whole missed window.

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

`pr=` is the **total number of merged PRs at post time** (the GitHub search count from §7),
**not** the highest PR number — PR numbers share a sequence with issues, so the two differ,
and the since-last-update stat subtracts `pr=` from the current total.

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
   second; if the DM write fails, retry it before ending the run.

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
   otherwise drop it as a restatement.
3. **Freshness abort.** If the newest Voyager channel message or state DM is less than
   2 hours old, another run just happened or is still in flight: abort without posting.
   On the daily cadence, fresher activity is never legitimate.

## Procedure

### 1. Establish the window

**The window ends at the `docgen` branch, not `main`.** TauCeti's `docgen` branch (set up in
TauCeti#1539) tracks the most recent commit on main **for which a complete docgen run is
published** — so everything inside the window is guaranteed to have API-docs pages to link
to, results merged after the docs point simply wait for the next run (≤ a day), and no
docs-workflow polling is needed.

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

The last row is the trap worth naming twice: a directory called
`Analysis/PositiveDefinite/` full of Bochner-adjacent machinery does **not** mean Bochner's
theorem is proved. Find the theorem statement, or do not announce it.

### 4. Significance gate — the ChatGPT second opinion

Batch **all** surviving candidates into **one** `mcp__chatgpt-math__ask_chatgpt_math`
call. Operational facts learned the hard way:

- use `reasoning_effort: "high"`. **`max` reliably times out** on long prompts (the MCP
  aborts after ~30 min of silence) — `high` has been reliable;
- one batched call, not one per candidate: each call costs minutes;
- the question must be **self-contained** — ChatGPT has no file access, so paste the
  declaration name, its statement, and its docstring summary.

Prompt template:

```
I am triaging newly added results in a Lean mathematics library to decide which are
worth announcing. For EACH numbered item below, answer with one of:

  ANNOUNCE  — a named mathematical result or notable definition: it has a Wikipedia
              page, or is a named theorem/definition in a standard textbook or paper,
              or is an eponymous result, or is a definition the surrounding subject is
              phrased in.
  SKIP      — an auxiliary lemma, API glue, a routine special case, or a technical step
              with no independent mathematical identity.

For each ANNOUNCE, add: (a) the standard name of the result, (b) one sentence, for a
mathematician who does not know it, saying what it asserts, (c) whether it has a
Wikipedia page, and (d) a standard reference if you know one.

Be conservative: if a result is only interesting inside its own proof, say SKIP. Do not
be polite about it — a false ANNOUNCE is more costly than a false SKIP.

<numbered list: name, Lean statement, docstring summary>
```

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
- The bold result name links to the **current source file at `main`** (see §6), which also
  covers the case where the declaration has moved since its PR.
- If no PR can be found (direct push), cite the commit hash with an explicit link.
- Never announce something you could not link.

### 6. Compose and post

Format (Zulip markdown):

```markdown
**Voyager · what's new in Tau Ceti**

*Named results*
- **[<Standard name>](<link to the source file at main>)** — <one sentence on what it asserts>. (TauCeti#123)
- ...

*Notable definitions*
- **[<Name>](<source link>)** — <what it is, and what it is for>. (TauCeti#124)

*Stats*
- <N> lines of Lean across <M> files (Tau Ceti only, excluding Mathlib)
- <D> declarations
- <P> PRs merged since the last update (<T> total)
```

…then send the updated state DM (see the watermark protocol).

Zulip-specific rules, each learned from reader feedback on the first message:

- **One physical line per paragraph and per bullet.** Zulip keeps single newlines as line
  breaks, so hard-wrapped prose renders with ragged mid-sentence breaks. Never wrap.
- **Use the realm linkifiers**: bare `TauCeti#NNN` for TauCeti PRs, `mathlib4#NNN` for
  Mathlib PRs — not explicit markdown PR links.
- **Link each bold result name to its declaration in the API docs**, so readers land on the
  exact statement: `https://taucetiproject.github.io/TauCeti/docs/TauCeti/<Module/Path>.html#<Fully.Qualified.Name>`
  (doc-gen4 layout; the anchor is the fully qualified declaration name — mind the namespace,
  e.g. probability results live under `TauCeti.Probability.*` and Lévy downward under
  `MeasureTheory.*`). **Verify every link before posting**: curl the page (expect 200) and
  grep the HTML for `id="<FQN>"`. The docs rebuild at most once daily (`pages.yml` — slow,
  delayed, and occasionally failing; see the schedule notes), so a result merged after the
  last successful build is not documented yet — for those, fall back to the source file at
  `https://github.com/TauCetiProject/TauCeti/blob/main/<path>`; a later run can use the docs
  link when it next mentions the module. Waiting for the day's docs run (see the schedule)
  keeps these fallbacks rare.
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
  content), stay under ~9,500, and **verify the rendered tail after every post or edit**
  (`GET` the message with `apply_markdown=true` and check the stats lines are present and
  "[message truncated]" is not).

Rules for the prose: one sentence per item, written for a mathematician who does not know
the result; no marketing adjectives; no "exciting"/"major milestone". State what the
theorem says, not how impressive it is. If a result is a strengthening of Mathlib, say so
in the sentence.

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
find TauCeti -name '*.lean' | xargs wc -l | tail -1        # LOC, Tau Ceti only
find TauCeti -name '*.lean' | wc -l                        # files
grep -rhcE '^(theorem|lemma|def|structure|class|abbrev|instance)' --include='*.lean' TauCeti | awk '{s+=$1} END {print s}'
gh api "search/issues?q=repo:TauCetiProject/TauCeti+is:pr+is:merged&per_page=1" --jq '.total_count'
```

Do **not** report `sorry` counts in the stats (owner decision). The no-`sorry` rule remains
an announcement *gate*: check nothing you announce has a `sorry` in its file, remembering a
docstring can mention the word without it being a proof hole.

"PRs merged since the last update" = the number of squash-merge commits in the window
(each carries its `(#N)`) — exact, and consistent with what was actually scanned; the total
comes from the GitHub search count, with the previous `pr=` as a cross-check. Exclude `.lake/` and any vendored Mathlib from every count — the LOC number is
meant to be *Tau Ceti's own* contribution and is the number most likely to be quoted.

The `sorry` grep counts **mentions**, not proof holes: a docstring saying "the `sorry`-goal in
`Suggested.lean`" matches too. The hit count is tiny, so read every hit and report only real
`sorry` terms. (As of `a695b8c` the library's one grep hit is a docstring mention — the honest
number was 0.)

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
