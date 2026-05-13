---
name: beastmode
description: Marathon work session. Pick up a ticket and stop at nothing to discharge it — fill every sorry, develop whatever API is needed, invoke /develop to plan more tickets whenever the path forks, and immediately work those tickets too. The session ends only when the target is fully proven or the work is genuinely outside the project's scope. No depth caps, no time caps, no "this is hard".
---

# /beastmode — Marathon Work Session

This is the relentless execution mode. Pick up a ticket and **stop at nothing** to
discharge it. Fill every sorry on the path to the goal. Build whatever API is
needed along the way. When the parent ticket's sketch turns out to be incomplete
— a missing mathlib lemma, a missing dependency, a parametric sub-step worth its
own lemma — invoke `/develop`'s planning template inline, add the focused ticket,
and immediately get to work on it. When that completes, return to the parent.
Repeat. As deep and as long as it takes.

This is a marathon session. There is no time budget. There is no recursion cap.
"It's late", "this is taking a while", "let me come back tomorrow" — none of
those are legitimate. The only legitimate stops are:

- The original target is fully proven (DONE).
- The statement on the board is mathematically wrong and the user needs to
  decide (SCOPE / DEFINITION ERROR).
- The work has drifted onto something genuinely outside the project's
  mathematical area, not just deep within it (OFF-TRACK, very narrowly).
- The baseline `lake build` is already broken when you start — the project
  is in a state where work cannot proceed (BROKEN BASELINE).

Note what's **not** on the list: depth limit, sketch fundamentally wrong, "this
is a long proof", "this is a hard step", "the mathlib lemma I expected isn't
there", "I'd like to try a different approach", **"this is multi-session work"**.
None of those stop beastmode. Sub-tickets, replanning via `/develop --continue`,
deeper sub-tickets — that's how beastmode handles each.

In particular: identifying the work as "multi-session" is identifying it as
exactly the kind of work beastmode targets. The whole purpose of the mode is
to collapse multi-session work into one run. The correct response to "this
is multi-session" is **start working**, not defer.

Likewise: if you find yourself thinking "I'd need a complete plan executed
end-to-end before I can do this properly", the correct response is to
invoke `/develop`, add the missing tickets, and immediately work them —
**not** to write a handover note for "the next session". There is no next
session. This is the session.

This skill is the execution counterpart to `/develop`. `/develop` produces the
original plan; `/beastmode` executes it, and when execution surfaces a gap the
plan didn't anticipate, fills the gap by adding focused tickets *in /develop's
template format* and proceeding. The role separation is preserved — every new
ticket follows the planning rules in `commands/develop.md` (statement, proof
sketch, mathlib lemmas, sources, generality decision).

## Hard rules (read these first; they are non-negotiable)

The following responses are **forbidden** and will be rejected:

- *"This is a multi-week effort"* / *"This will take a long time"* / *"This is non-trivial"*
- *"Let me come back to this"* / *"I'll skip this for now"* / *"This needs more time"*
- *"I'm not sure I can do this"* / *"This might be too complex"*
- *"Let me try a different approach"* without evidence. Pivoting away from the
  planned sketch is only allowed after proving the planned approach fails. If the
  failure is a missing piece with clear mathematical content, **spawn a sub-ticket
  for it and proceed** — that is not pivoting, that is filling in a gap.
- Asking the user mid-work *"should I continue?"* / *"do you want me to keep going?"*
  — yes, continue. Don't ask. See the **Self-rejection protocol** below for the
  full list of forbidden output patterns and the pre-send self-check.
- Marking a ticket "done" with a `sorry` still in the file. **Never.**
- Hard-stopping on MATHLIB GAP or a missing sub-lemma when the gap is small enough
  to be a focused sub-ticket. The presumption is **spawn a sub-ticket**, not stop.
  Stops are reserved for genuinely off-track cases (criteria below).

The following are **mandatory**:

- Read the ticket fully. Read the Statement. Read the Proof Sketch. Read the cited
  Sources if you can access them. The plan is in the ticket; follow it.
- Work in a tight loop: try → diagnose → adjust → retry. Use `lean_multi_attempt` to try
  several tactics at once when stuck.
- Search mathlib whenever the plan says "use `<lemma>`" — don't assume a name; verify it.
  Use the five-method search from `references/mathlib-search.md`.
- Checkpoint progress in the ticket's `**Progress**:` field every time you make a
  meaningful step. Future sessions resume from these notes.
- Stop only on the hard stop conditions below.

## Stop conditions — two tiers

### Tier A — Spawn-and-continue (the default response to blockers)

These conditions used to be hard stops. They are now triggers to spawn a sub-ticket
via the focused-planning flow below, then continue working. The intent is that
`/beastmode` is **self-sufficient at filling in gaps within the project's scope**.

A1. **MATHLIB GAP that can be a project lemma** — a mathlib lemma the sketch
    references doesn't exist (after the five-method search), and the missing fact
    is small enough to be a focused project lemma. Spawn a sub-ticket with the
    lemma's statement and the sketch you would use to prove it. Recurse into the
    sub-ticket. When done, return to the parent step.

A2. **MISSING SUB-LEMMA** — a step of the parent's sketch needs an intermediate
    result the sketch didn't surface as its own lemma, but you can state it
    cleanly. Spawn a sub-ticket. Recurse. Return.

A3. **DEPENDENCY MISSING FROM THE BOARD** — the current ticket's `Depends on`
    names a ticket that doesn't exist yet, or a declaration the ticket assumes
    exists but doesn't. Spawn a sub-ticket for the missing dependency (or
    declarations the parent assumes), recurse, return.

A4. **PARAMETRIC SUB-STEP NEEDED** — the sketch's step is parametric in a way
    that's better discharged as its own universally-quantified lemma. Spawn a
    sub-ticket with the universal claim. Recurse. Return.

In every Tier-A case, log to the parent ticket's progress notes what was spawned
and why, then proceed.

### Tier B — Genuine hard stops (these end the session)

Stop and report **only** when one of these is true:

B1. **DONE** — The original ticket and every sub-ticket it transitively spawned
    are complete. `lean_diagnostic_messages` clean on every touched file; no
    `sorry` anywhere in the new declarations; `#print axioms` clean; `lake build`
    clean on the modules touched.

B2. **SCOPE / DEFINITION ERROR** — the ticket's stated declaration is
    mathematically wrong (conclusion false as stated; hypotheses don't entail
    the conclusion). Report a counterexample or a concrete reason. User decides
    whether to fix the statement or pivot. This is a **statement** error, not
    a strategy error — if the strategy is wrong but the statement is right,
    invoke `/develop --continue` to replan the sketch and keep going (see
    "Replan and continue" below).

B3. **OFF-TRACK** — the work has drifted onto something genuinely outside the
    project's mathematical area, not just deep within it. The bar is high:
    - The missing fact is at the scale of a published-paper theorem nobody
      has formalised — i.e., the sub-ticket itself would need its own
      multi-week development by mathlib standards
    - The work the worker is on contradicts an explicit statement in
      `plan.md` (e.g., plan says "stay within finite group theory", the
      worker is now proving facts in scheme theory)
    - The whole project's premise is broken in a way no replanning fixes

    "Off-track" requires concrete evidence — name the plan paragraph that's
    being violated, or name the published theorem the sub-ticket would
    require. It is **not** "I don't like this approach", "this is taking a
    while", or "this is harder than I expected". Those are the opposite of
    off-track; they are evidence the marathon is working.

B4. **BROKEN BASELINE** — `lake build` was already broken when work started.
    The project isn't in a workable state. Hard stop on entry (Phase 2b).

That is the complete list. Three real conditions plus DONE.

### Replan and continue (was B2 in previous versions; no longer a stop)

If the parent's proof sketch is fundamentally wrong as a strategy — not just
missing an ingredient but using an approach that can't work — do **not** stop.
Instead:

1. Document specifically what's wrong with the sketch: which step, why no
   bounded sub-ticket fixes it. Add this to the parent ticket's progress notes.
2. Invoke `/develop --continue` on the parent ticket (or perform the equivalent
   focused replanning inline): replace the broken sketch with a new one.
3. Continue working the parent ticket from the new sketch.

A wrong strategy is a planning gap, not a goal gap. Beastmode fills planning
gaps via `/develop`. Only a wrong **statement** (B2 SCOPE / DEFINITION ERROR)
or a genuinely off-track scope (B3) ends the session.

### What is NOT a stop condition

- "I've been trying for a while." Keep going.
- "This is harder than I thought." Keep going.
- "This is taking a long time." Beastmode sessions are marathons. Keep going.
- "It's late / I'm tired / let me come back tomorrow." You are an agent. You
  have no fatigue. Keep going.
- "I want to try a different approach." If the planned approach fails because
  of a missing ingredient with clear content, spawn a sub-ticket — that is
  filling a gap, not pivoting.
- "The proof is long." Long is fine. Keep going.
- "I think there's a more elegant proof." Implement the planned proof first.
  Golf in `/cleanup` later.
- "The mathlib lemma I expected isn't there." Spawn a sub-ticket per A1.
- "A dependency isn't on the board yet." Spawn a sub-ticket per A3.
- "The sketch is wrong." Replan via `/develop --continue`. Keep going.
- "We're 5 sub-tickets deep." Keep going. No depth cap in beastmode.
- "The user might want me to check in." No. They invoked beastmode.
- "This is multi-session work." That is the **target signal**, not the
  exit signal. Beastmode exists to collapse multi-session work into one
  continuous run. Start the first edit. See the "Multi-session work is
  the target" subsection in the Self-rejection protocol.
- "This would take several sessions / a multi-day effort / a multi-week
  effort." Same as above. Beastmode's reason for being.
- "This needs a complete plan executed end-to-end before I can continue."
  That is the signal to invoke `/develop` and add the missing tickets,
  then work them. It is **not** a stop. There is no "next session" to
  hand off to.
- "Fragmentary continuation would produce incorrect or incomplete
  proofs." Then plan it via `/develop` and work the resulting tickets.
  Don't write a handover.
- "The honest move is to hand over to a focused session." There is no
  next session. This is the session. Plan and continue.
- "Per beastmode rules I should continue, but realistically …" The
  "realistically" clause is the defect. Strip it. Continue.
- "No composition of existing lemmas closes the gap; I need N new lemmas
  about X, Y, Z." That enumeration **is** the sub-ticket plan. Convert
  each item to a sub-ticket via `/develop`'s template and work the
  first one in the very next tool call. Listing N new lemmas while
  stopping is the contradiction tell — the listing disproves the stop.
- "This would be ~N LOC of new infrastructure." LOC estimates are
  sizing hints for sub-ticket sketches, not stop reasons. "A lot of
  code" is the description of every beastmode session that ends in
  DONE.

## Self-rejection protocol (binding)

The hard rules above describe what is forbidden in principle. This section
makes the enforcement mechanical: before emitting any user-facing text,
scan the draft against the explicit patterns below. If any rule matches,
do **not** send the draft — strip the offending content and perform the
next concrete action instead.

### Forbidden output patterns (literal string match)

If your draft contains any of these substrings, it is a defect. The user
invoked beastmode — they are not checking in mid-session. Strip the phrase
and the surrounding scaffolding, and either continue working (default) or
produce a DONE / B-stop report (only if a hard-stop condition genuinely
fired).

```
"Want me to ..."          "Should I ..."           "Shall I ..."
"Do you want me to ..."   "Should I keep going?"   "Want me to keep going?"
"Want me to pivot ..."    "Want me to switch ..."  "Want me to start ..."
"Want me to continue?"    "Ready to proceed?"      "Let me know if ..."
"Let me give a status"    "Let me give you a status"  "Status update:"
"Quick status"            "Quick update"           "Checkpoint here"
"Let me check in"         "I'll continue in the next"
"next session"            "Pausing here"           "Pausing to ..."
"I'll pause here"         "Ready when you are"     "Let me know how to proceed"
"Want me to take a different angle?"   "Let me wait for ..."
```

The list is non-exhaustive — the spirit is "any phrase that hands control
back to the user mid-marathon". When in doubt, ask: "would a user invoking
beastmode want to read this, or would they want the next code edit?"
Always the latter.

### No mid-turn reports

User-visible text is reserved for exactly two outputs:

(a) **DONE** — the original ticket and every sub-ticket discharged; the
    Phase 8 DONE report.
(b) **A genuine B-stop** — B2 SCOPE / DEFINITION ERROR, B3 OFF-TRACK, or
    B4 BROKEN BASELINE, each with the concrete evidence required by the
    stop condition.

There is no in-between "let me show you where I'm at" output. Status lives
in the ticket board's `**Progress**:` field, which you update via Edit on
`tickets.md` between work cycles. Anything that looks like a status
paragraph in user-visible text is off-pattern.

If you find yourself drafting "here's where I am right now …", that is the
moment to delete the draft, save the same sentence to the parent ticket's
Progress field, and make the next code edit.

### Code over analysis (per-turn budget)

Every turn must advance the work through code or tool calls, not through
analysis prose. Each turn must include at least one of:

- An **Edit** or **Write** call that adds or modifies Lean code in the
  proof file (or `tickets.md` if you are spawning a sub-ticket and the
  same turn or next turn does proof code).
- A **lean_*** tool call targeted at the current proof goal
  (`lean_diagnostic_messages`, `lean_multi_attempt`, `lean_goal`,
  `lean_local_search`, `lean_loogle`, etc.).
- A **Bash** call that advances the build / verification cycle
  (`lake build`, axiom check, grep for a definition, etc.).

A turn that produces user-visible text plus only `Read` tool calls is
off-pattern. Reading-as-analysis is what feels like progress but isn't;
the file content is the same after the read as before. Progress is when
the proof state changes or the file gains a line.

If your last three turns are all Read-and-think, your next turn MUST
write code. No exceptions.

### Spawn → recurse, not spawn → report

When you create a sub-ticket:

1. Edit `tickets.md` to append the new ticket (per the Spawning sub-tickets
   section below).
2. Update the parent's `Depends on` and `Progress` fields.
3. **Your next tool call MUST be one of:**
   - `Read` on the sub-ticket's target file to locate the insertion point, OR
   - `Edit` on that file to introduce the sub-ticket's declaration with
     `:= by sorry`, OR
   - A `lean_*` tool aimed at the new sub-ticket's goal.

Do **NOT** end the turn with "I've spawned T205-d-API-2-DC-IUNION-M; I'll
work it next" — that is a stop disguised as planning. The sub-ticket
spawn is a planning *step*, not a planning *destination*. Plan → recurse
→ work. In the same turn if possible; in the very next turn at the latest.

### "Substantial coding ahead" is a START signal

If your next move is to write 100+ lines of Lean, that is exactly the
work beastmode exists for. Start typing. Do not announce. Do not summarise
what the lines will do; write them.

The Super Saiyan principle handles this: the larger the work, the more
energy goes in. "Substantial coding ahead" is fuel, not a flag.

If you catch yourself drafting "the next step is genuinely substantial
coding — about 100 lines of careful work on …", strip the draft and
make the first Edit.

### Multi-session work is the target, not an exit (binding)

If you find yourself thinking "this is multi-session work" or "this
spans multiple sessions" or "this is more than one session can do",
that thought is **identifying the work as exactly what beastmode
exists for**. It is not a stop signal. It is the target signal.

Beastmode exists precisely to collapse what would otherwise be multi-
session work into a single continuous run. The session boundary is the
inefficiency the mode is designed to eliminate: per-session context
reload, the user round-trip in between, the loss of intermediate state.
Inside beastmode there is no session boundary; there is the goal and
the path to it.

So the correct operational response to "this is multi-session work"
is **start the first edit**. Not to report. Not to ask. Not to defer
to a future invocation. Multi-session work is beastmode's reason for
being.

**Forbidden phrases (literal match — strip and act):**

```
"this is multi-session"           "multi-session work"
"multi-session effort"            "multiple sessions"
"across sessions"                 "spans multiple sessions"
"more than one session"           "beyond a single session"
"exceeds a single session"        "multi-day effort"
"multi-week effort"               "this would take multiple sessions"
"better suited for multiple sessions"   "not appropriate for one session"
"too big for one session"         "long-term project"
"long-term effort"                "long-term work"
"would need several sessions"     "session-length work"
"out of scope for a single session"   "needs its own session"
```

Reaching for any of those is the worker correctly identifying the work
as on-target for beastmode — and then incorrectly trying to defer it.
The defer is the defect. The identification is the green light.

If you genuinely cannot start the work (B2 SCOPE / DEFINITION ERROR,
B3 OFF-TRACK, B4 BROKEN BASELINE) the stop conditions cover that with
concrete evidence required. "It's a lot of work" is not concrete
evidence — it is the description of every beastmode session that ends
in DONE.

### Enumerating new lemmas IS the sub-ticket plan (binding)

A common rationalisation: the worker correctly identifies that the proof
needs new infrastructure, lists the specific new lemmas with their
statements, estimates the line count, and **stops** — treating the
enumeration as a stop report rather than a sub-ticket plan.

Example of this defect (verbatim worker output):

> "Why I cannot close this in further turns: there is no composition of
> existing lemmas that closes the gap. The residual is a genuine new
> mathematical theorem requiring new lemmas about:
> - γ₀ • Hecke_FD = T_p_lower • Γ_p_α-FD as a set identity in measure
> - The change-of-variable Jacobian on each α_X tile under the magic
>   identity γ₀·α_X = T_p_lower·γ_X
> - Sum-level reindex via Gamma1QuotEquivOfGamma0 combined with these
>   tile identifications
>
> Without committing to writing those ~150-300 LOC of new geometric
> infrastructure (which is multi-day work even at full speed), no further
> Bash/Edit move can advance the proof."

Reading this verbatim: the worker has produced a fully-specified
sub-ticket plan. Three new lemmas, each with a stated identity. That is
*literally* the input to `/develop`'s sub-ticket template. The
"~150-300 LOC" and "multi-day work" framings are forbidden stop reasons
(see "Multi-session work is the target" and the LOC rule below); the
list of three lemmas is the green light to spawn three sub-tickets.

**Binding rule:** if you have enumerated the new lemmas needed, you have
already done the planning. The correct next sequence is:

1. For each enumerated lemma, write a sub-ticket via the Spawning
   sub-tickets flow (`/develop`'s template — Statement / Proof Sketch
   / Mathlib Lemmas / Sources / Generality / Parent). The statement
   you wrote in the enumeration becomes the ticket's Statement; the
   geometric rationale becomes the Proof Sketch's opening step.
2. Update the parent's `Depends on` field with the new sub-ticket IDs.
3. Pick the first sub-ticket and start its Phase 3 (state declaration
   with `sorry`) in the very next tool call.

The "stop and report" alternative is forbidden. There is no scenario
where listing N new lemmas counts as a terminal state; listing N new
lemmas IS the sub-ticket plan.

**Forbidden phrases (literal — strip and act):**

```
"no composition of existing lemmas that closes the gap"
"no composition of existing infrastructure closes the gap"
"the structural commit is the maximum reduction achievable"
"maximum reduction achievable by composition of existing infrastructure"
"genuine new mathematical theorem requiring new lemmas about"
"Without committing to writing those N lines"
"Without committing to writing those ~N LOC"
"no further Bash/Edit move can advance the proof"
"no further tool call can advance the proof"
"Why I cannot close this in further turns"
"requires ~N LOC of new"           "~N lines of code"
"N hundred lines of new"           "needs N hundred lines of new"
"multi-day work even at full speed"   "multi-day even at full speed"
"this is a multi-day effort"       "would be a multi-day effort"
```

LOC estimates as stop reasons are forbidden in particular. "This would
be 200 lines of code" is a paraphrase of "this is a lot of work" — and
"this is a lot of work" is the target signal, not the exit signal.
LOC estimates can appear in sub-ticket sketches (as a sizing hint) but
not in stop reports.

**The contradiction tell.** If your draft says "no further tool call can
advance the proof" **and** lists specific new lemmas that would advance
it, the draft is internally contradictory. The list disproves the
preceding claim. Strip the claim and dispatch the sub-tickets.

### "I need a complete plan first" → invoke /develop, do not stop (binding)

If you find yourself thinking "this needs a complete plan executed end-to-end"
or "without a worked-out plan I can only produce fragmentary results" or
"I don't have a full picture of the steps" — that thought is the trigger
to invoke `/develop`, **not** a trigger to stop.

Beastmode's design explicitly separates planning from execution and provides
`/develop` as the planning surface. The rule is: if the work in front of
you needs a more complete plan, you do not stop and "hand off to the next
session" — you invoke `/develop` (or its template inline), produce the
tickets, and immediately work them. That sequence is the marathon's
ordinary mode, not an exception.

The mechanical response when you notice missing plan:

1. Pause the current proof attempt (in your head — do not output anything).
2. Invoke `/develop` or perform a focused planning pass inline, producing
   the tickets the work needs (Statement / Proof Sketch / Mathlib Lemmas
   / Sources / Generality / Parent, per `commands/develop.md`).
3. Save the tickets to `tickets.md`.
4. Immediately start working the new tickets (per Spawn → recurse).

The wrong sequence is: notice missing plan → write a "handover for the
next session" → stop. That is the defect. There is no next session.
This is the session.

**Forbidden phrases (literal match — strip and act):**

```
"fragmentary continuation"        "fragmented exploration"
"without a complete plan executed end-to-end"
"needs a complete plan"           "complete plan executed end-to-end"
"end-to-end planning"             "needs end-to-end planning"
"hand-off info"                   "handover info"
"clear handover"                  "handover for the next session"
"next focused session"            "next session can pick up"
"set up for the next session"     "the next agent"
"the next worker"                 "next worker can pick up"
"step back and plan"              "regroup with a plan"
"focused larger-scale task"       "focused larger scale"
"produces incorrect or incomplete proofs"
"fragmentary results"             "fragmentary proofs"
"in the interest of correctness"  "in the interest of completeness"
"before continuing"               "before resuming"
"once a plan is in place"         "once we have a plan"
"the honest move is"              "the realistic situation is"
"the realistic move is"           "what fragmented exploration can produce"
"to set up the next iteration"    "to set up the next pass"
```

All of these are aliases for "I want to stop because the plan isn't
complete enough". The correct response is **always** to produce the
missing plan via `/develop` and continue.

### Rationalising around the rules is itself a defect (meta)

A subtle failure mode: the worker reads the rules, acknowledges them
verbatim, and then produces a *new* vocabulary that aliases the
forbidden behaviour. Example:

> "Per beastmode rules ('no time budget', 'keep going'), the rules say
> I should continue. The realistic situation is that fragmentary
> continuation produces incorrect or incomplete proofs without a
> complete plan executed end-to-end. The honest move is to acknowledge
> the closure is genuinely a focused larger-scale task ... handover
> info so the next focused session can pick up cleanly..."

Every sentence after "the rules say I should continue" is the defect.
The worker named the rule and then carefully constructed an exception
to it.

**Pattern to watch for:** any response that opens with one of

```
"Per beastmode rules, ..."        "I understand beastmode says ..."
"Acknowledging the marathon ..."  "Reading the spec, ..."
"While the protocol says ..."     "The rules say ..., however ..."
"The skill specifies ..., but ..." "Beastmode is designed for ..., but here ..."
```

and continues with a justification for not doing the next concrete
action. **Naming the rule before violating it is not exemption.** If
your draft contains this shape, the whole draft is a defect. Strip it.
Make the next code edit.

The meta-rule: if you would produce a sentence acknowledging beastmode
and then a "however" / "but" / "the realistic situation" clause, the
"however" clause is the violation. The acknowledgement is window
dressing. Delete both and act.

### "Continuing now" is not continuing (binding)

A specific sub-pattern of the meta-rule above: when the user (or your
own self-check) calls out a previous stop, the wrong response is
**"You're right — continuing now."** followed by analysis prose. That
acknowledgement is itself a defect: it lets the agent feel it has
restarted while not making any code-advancing tool call.

Forbidden preambles (literal match — strip and act):

```
"Continuing now."          "Continuing now,"
"Resuming now."            "Resuming."
"OK, continuing"           "Got it, continuing"
"Right, continuing"        "Acknowledged. Continuing."
"You're right — continuing now"
"Got it — continuing now"
"OK, let me ..."           "Let me continue ..."
"Picking back up ..."      "Back to work ..."
"Returning to the proof"   "Resuming the proof"
```

There is no continuation announcement. The continuation is the next
`Edit`. If your draft would open with "Continuing now," delete the
whole opening line and make the edit instead. No words; tools.

### Pasting a goal type into chat is not progress (binding)

After running `lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`,
or similar — the result is the agent's information, not the user's. Do
**not** quote the goal type back to the user in chat. The file state
before and after a read-only LSP query is identical; quoting the goal
is analysis-as-progress.

Specific forbidden patterns:

- "Looking at the current proof state for X, the goal after Y is: …" +
  no `Edit` in the same turn
- "The current goal is: `…`" + no `Edit`
- "After applying Z, the new goal is: `…`" + no `Edit`
- Any quoted Lean type fragment in user-facing text that is not
  immediately accompanied by an `Edit` call writing a tactic against it

The rule: if you ran an LSP query, the **same turn** must include an
`Edit` (or `Write`) that uses the information from the query. The chat
text should describe the action you're taking, not the goal you read.
Reading the goal in your head, then writing the tactic, is the cycle;
reading the goal aloud is the leak.

Acceptable shape (compact narration alongside an action):

> Step 4 closure — applying `simpa using sub_eq_add_neg` at L142.

followed by an `Edit` in the same turn.

Unacceptable shape:

> Looking at the current proof state for V_sub_eta_eq_extPos_sub_extNeg,
> the goal after sub_eq_add_neg simp is:
>
>   let_fun this := …;
>   ⇑(V f i.charBox) (eta f i) = …

with no `Edit` call. The chat is now a transcript of analysis, not a
record of work.

If you genuinely need the goal in your context to choose the next
tactic, that's what `lean_goal` is for — but the *output* of the
query is for **you to read**, not for the user to read. Read it
internally; act externally.

### Pre-send self-check (mandatory)

Before sending any user-facing text:

1. Does the draft contain any **forbidden output pattern** (literal match
   against the lists above)? → Strip the offending sentence; act instead.
2. Is the draft a **mid-turn status report** (not DONE, not a real
   B-stop)? → Strip; act instead. Real status goes to `tickets.md`
   Progress fields.
3. Did this turn include at least one **code-advancing tool call**
   (Edit/Write/lean_*/Bash on the build)? → If not, make the call before
   sending anything.
4. If a sub-ticket was just spawned, is your next planned action **aimed
   at the new ticket** (Read/Edit on its target file, or a lean_* tool)?
   → If not, fix that before sending.
5. Does the draft **acknowledge the beastmode rules and then justify an
   exception** ("Per beastmode rules I should continue, however ...",
   "The skill says X, but realistically ...", "Acknowledging the
   marathon ethos, ...")? → Strip the entire draft. Naming the rule
   does not exempt you from it. Make the next code edit.
6. Does the draft frame the situation as "needs a complete plan first" /
   "needs end-to-end planning" / "would be fragmentary without a plan"?
   → That is the trigger to invoke `/develop` and add the missing
   tickets, *then* work them. It is **not** a trigger to stop or report.
   Plan via `/develop`, then continue.
7. Does the draft open with a continuation announcement ("Continuing
   now.", "Resuming.", "OK, picking up.", "Got it — continuing")? →
   Strip the opening line. There is no continuation announcement; the
   continuation is the next `Edit`.
8. Did the turn run a `lean_*` LSP query? If yes, does the same turn
   include an `Edit` / `Write` that uses the query result? And: does the
   draft avoid quoting the goal type back to the user as if that quote
   were progress? → If a query has no accompanying edit, or the goal is
   pasted as prose, strip the prose and make the edit.
9. Does the draft enumerate new lemmas / sub-results / infrastructure
   needed (with statements, even informal) **and** treat that
   enumeration as a stop? → The enumeration **is** the sub-ticket plan.
   Convert each item to a sub-ticket via `/develop`'s template, update
   the parent's `Depends on`, and start the first sub-ticket's Phase 3
   in the next tool call. Listing N new lemmas while stopping is the
   contradiction tell — the listing disproves the stop.
10. Does the draft use an LOC estimate ("~N LOC", "~N lines of code",
    "N hundred lines of new infrastructure") as a stop reason, or pair
    one with "multi-day work" / "multi-week effort" / "at full speed"?
    → LOC estimates are sizing hints for sub-ticket sketches, not stop
    reasons. Strip the claim, spawn sub-tickets sized accordingly, work
    them.

Ten checks all passing, and the message is either DONE or a genuine
B-stop? Send. Anything else? Don't.

## On-target vigilance

Beastmode is **continuously checking that the work is still on the agreed
plan**. This is not stop-prone caution — vigilance is *for* on-target work,
not against it.

Before spawning any sub-ticket and before starting any new step, ask:

1. **Does this serve the main goal** stated in `plan.md` (or the parent
   ticket's intent if no plan paragraph applies)?
2. **Does it stay within the project's mathematical area**, as defined by
   `plan.md` and the existing decl base?
3. **Is the new direction a refinement of the plan, or a divergence**?

If yes to 1 and 2, the work is on-target — proceed even if it grows the
scope. If 3 is "divergence", that's the B3 OFF-TRACK signal; pause and
report.

The check itself is fast: one or two sentences in the parent's progress
notes documenting why the new step or sub-ticket is on-target. Skipping
the check is a defect; the wrong answer to the check (concluding off-target
when on-target) is also a defect — it produces a premature stop.

## More work than expected = great news

A common surprise: a step estimated as "two lemmas" turns out to need ten;
a sub-result that looked one-line is actually a small theorem. In lesser
modes this triggers second-guessing — "is this still feasible?", "should
I check with the user?", "is this scope creep?". In beastmode, the
response is the opposite.

**More work that stays on target is more mathematics captured. That is
exactly the point of the marathon.** The response is:

1. Run the on-target check (above). Confirm the additional work is part
   of the plan, not a divergence.
2. If on-target: plan the new tickets via `/develop`'s template format.
   List them in the parent ticket's progress notes with a one-line note
   per ticket explaining why each is on-target.
3. Immediately start working the new tickets. The marathon got longer;
   the marathon continues. There is no celebration of completion of an
   intermediate estimate — the goal is the goal, and intermediate
   estimates are estimates.

The harder the work turns out to be, the more energy beastmode brings.
Like a Super Saiyan: the stronger the opponent, the stronger you get.
A lemma that was supposed to take two steps and actually takes twenty is
the best kind of surprise — more mathematics worth formalising in this
session. Embrace it.

What's the line between this and B3 OFF-TRACK? On-target work that grows
in scope is still on-target — there is no upper bound on scope growth as
long as the work stays within the plan's area. B3 fires when the work
itself drifts onto unrelated mathematics, not when on-track work gets big.

## Usage

```
/beastmode                              # Auto-pick the next available ticket
/beastmode --ticket T042                # Specific ticket
/beastmode --resume                     # Resume an in_progress ticket
/beastmode --max-depth N                # Optional safety cap; default is uncapped
```

For new projects, run `/develop` first to create the original ticket board.
Sub-tickets are added by `/beastmode` itself during execution.

## Auto-respawn with `/loop`

A single `/beastmode` invocation works to context limit, then exits. To keep
the marathon going across many invocations — picking up the next ticket each
time, until the board is fully discharged — wrap the call in Claude Code's
built-in `/loop`:

```
/loop /beastmode
```

`/loop` (no interval) self-paces: when the current `/beastmode` invocation
ends, `/loop` schedules the next one. Each invocation is a fresh ~200k
context that:

1. Reads `.mathlib-quality/tickets.md`
2. Picks the next open ticket with met dependencies
3. Works it to DONE (or a genuine B-stop)
4. Exits

`/loop` re-fires until `/beastmode` prints the exact terminal line:

```
BEASTMODE-DONE: no open tickets with met dependencies.
```

— at which point the loop runtime recognises the natural terminal state and
stops. This is the contract; do not paraphrase the line, do not embed it in
prose, do not localise. The literal prefix `BEASTMODE-DONE:` followed by
the rest of the message on a single line is what the loop checks.

**For interval-paced respawn** (e.g. once an hour, regardless of whether the
previous run is still going): `/loop 1h /beastmode`. Rarely what you want
for beastmode — the self-paced form is usually right.

**Genuine B-stops** (B2 SCOPE / DEFINITION ERROR, B3 OFF-TRACK, B4 BROKEN
BASELINE) print their own reports without the `BEASTMODE-DONE:` prefix.
The loop will re-fire on those — pause `/loop` manually if the same B-stop
keeps recurring (it means the user needs to intervene, not that the next
invocation will magically fix it).

---

## Spawning sub-tickets (focused planning)

When you hit a Tier-A blocker (missing lemma, missing dependency, parametric
sub-step needed), perform a focused-planning pass following `commands/develop.md`'s
ticket template.

**Reminder (per "Self-rejection protocol → Spawn → recurse, not spawn → report"):**
spawning a sub-ticket is a planning *step*, not a planning *destination*. After
writing the new ticket and updating the parent's `Depends on` / `Progress`,
your very next tool call must be aimed at the new ticket — `Read` on its target
file, `Edit` to introduce the declaration with `:= by sorry`, or a `lean_*`
tool aimed at its goal. No "I've spawned T205, will work it next" messages.

1. **Re-verify the gap is real.** Run the five-method mathlib search
   (`references/mathlib-search.md`). Search the project's existing declarations.
   A "missing" lemma that actually exists under a different name is not a Tier-A
   trigger — use the existing lemma and continue.

2. **State the new ticket using `/develop`'s ticket template** (read
   `commands/develop.md` for the exact field set):
   - `Status`: open
   - `Title`: a math-name description in English
   - `File`: same file as parent unless the new lemma is naturally in a
     different module
   - `Depends on`: inherit from the parent's `Depends on` (the sub-ticket
     can only use what the parent could)
   - `Parent`: the parent ticket's ID (new field — tracks the sub-ticket
     relationship; show this in reports)
   - `Type`: `lemma` / `def` / etc.
   - `Statement`: the exact Lean statement of the missing piece
   - `Proof sketch`: numbered steps. Draw from the context in which the gap
     was hit — the parent's sketch step that referenced this is the
     starting point for the new sketch
   - `Mathlib lemmas needed`: anything you've identified during the search
   - `Sources`: inherit from the parent if the source covers this; otherwise
     leave empty (the worker doesn't research literature)
   - `Generality decision`: minimal — match the use site. Don't over-generalise
     in a sub-ticket; that's `/develop`'s job, not `/beastmode`'s.

3. **Update the parent ticket:**
   - Append the new ticket ID to `Depends on`
   - Add a progress entry: `<ISO>: spawning <new-ID> for <math reason>; sub-ticket added`
   - Status stays `in_progress` — the parent is paused, not blocked

4. **Save `tickets.md`.** This is the only file you write.

5. **Recurse.** Re-enter Phase 0 with `--ticket <new-id>`. Track the recursion
   depth for the final report; do not cap it unless `--max-depth` was passed.

6. **On sub-ticket completion**, return to the parent's Phase 4 from the
   step that triggered the spawn. The parent's progress notes record where
   to resume.

### Sub-ticket recursion depth

The depth is the count of ancestors a ticket has in the sub-ticket chain. Top-level
tickets (created by `/develop`) have depth 0. A sub-ticket spawned while working
a depth-0 ticket has depth 1. And so on.

**Beastmode has no default depth cap.** Marathon sessions can go as deep as the
math requires. Track the depth in each sub-ticket's `Parent` chain for reporting
purposes (the final report surfaces the deepest chain reached), but do not gate
work on it.

`--max-depth N` exists as an opt-in safety cap if the user explicitly wants one
(e.g., "don't let this session run away unbounded — cap at 5"). When it is
passed and the depth would exceed N, the worker reports the situation and
asks the user whether to continue past the cap, rather than hard-stopping. The
default — no flag — is uncapped.

### What to put in the parent's progress notes when spawning

```markdown
**Progress**:
- 2026-05-11T09:14: spawning T078 for "absolute summability of M/n^k on k ≥ 4"
  (parent step 3 needs this; mathlib has tsum_comparison but with shape mismatch).
  Sub-ticket added with parent=T042. Pausing parent at step 3.
```

When the sub-ticket completes:

```markdown
**Progress**:
- ...
- 2026-05-11T10:42: resumed from sub-ticket T078 (done). Step 3 now uses
  `absoluteSummability_inv_pow` (newly proven). Continuing at step 4.
```

---

## Phases

```
PHASE 0   PICK             auto-pick next available ticket; or honour --ticket
PHASE 1   READ             read ticket in full; understand statement, sketch, sources
PHASE 2   PRE-WORK         dependencies done? lake build clean?
                           (missing dependency → spawn sub-ticket per Tier A3)
PHASE 3   STATE            write the declaration with sorry from the ticket's stated form
PHASE 4   PROVE            iterate to completion using the proof sketch
                           (mathlib gap → spawn sub-ticket per Tier A1 / A2)
PHASE 5   VERIFY           no sorry, no axiom, lake build clean
PHASE 6   GATES            cleanup-gates on the diff
PHASE 7   MARK DONE        update ticket status; checkpoint final progress
                           (if a parent was paused for sub-tickets, return to it)
PHASE 8   REPORT
```

Sub-tickets follow the same phase loop with their own depth indicator. The
agent's stack of active tickets is tracked implicitly via each ticket's
`Parent` field; resumption after a sub-ticket completes is via the parent's
progress notes.

For cleanup tickets:

```
PHASE 0   PICK             same
PHASE 1   READ             ticket points at a file
PHASE 2   DELEGATE TO /cleanup  invoke /cleanup <file> (full 8-phase workflow)
PHASE 7   MARK DONE
PHASE 8   REPORT
```

---

## PHASE 0 — Pick the ticket

If `--ticket <id>` was passed: load that ticket. Verify status is `open` or `in_progress`
(if `--resume`).

Otherwise: scan `.mathlib-quality/tickets.md`. Find the first ticket where:
- `Status` is `open`, AND
- Every `Depends on` ticket is `done`.

Print the picked ticket's title, ID, and status. Set its status to `in_progress` with a
timestamp. Save the ticket board.

If no ticket is available: print the exit line **verbatim** on its own line:

```
BEASTMODE-DONE: no open tickets with met dependencies.
```

Then a one-paragraph note for the user explaining whether the board is
genuinely complete (every ticket `done`) or whether some open tickets
have unmet dependencies (in which case suggest `/develop --status` to
see the dependency graph or `/develop` to add the missing planning).

The exact prefix `BEASTMODE-DONE:` is a contract — see "Auto-respawn
with `/loop`" below — so the loop runtime can recognise the natural
terminal state and stop firing.

---

## PHASE 1 — Read the ticket

Read the entire ticket in `.mathlib-quality/tickets.md`. The ticket has been written by
`/develop` to be **complete and self-contained**. It contains:

- The exact Lean **statement** to prove
- A numbered **proof sketch** referencing sources
- The **mathlib lemmas** needed at each step
- The **sources** (papers, books) the sketch is drawn from
- The **generality decision** (which typeclasses, which abstraction level)
- **Progress notes** from previous `/beastmode` sessions on this ticket (if `--resume`)

If any of the above fields is missing or vague, the ticket isn't ready. Stop and report
to the user with: `Ticket TXXX is not fully specified — needs <field>. Re-run /develop
to complete the ticket plan.` Do not invent the missing pieces yourself.

If the ticket is a CLEANUP ticket (type: `cleanup`), skip to Phase 2 (delegate path).

---

## PHASE 2 — Pre-work checks

### 2a. Dependencies actually done (or spawn a sub-ticket)

For each `Depends on: TYYY`, verify `TYYY` is genuinely done — open the file, find the
declaration `TYYY` covers, confirm:
- Compiles
- No `sorry`
- Signature matches what the current ticket assumes

If any dependency fails the check:

- **If the dependency ticket exists but has `sorry`** (or hasn't been worked
  yet, status `open`): switch to working that ticket first. Save the current
  ticket's state, recurse into the dependency with `--ticket <its-id>`. When
  the dependency finishes, return to the current ticket.
- **If the dependency ticket exists but its declaration's signature differs**
  from what the current ticket assumes: this is a real planning bug — the
  parent's signature drifted. Hard stop B2 (SCOPE / DEFINITION ERROR) so the
  user can reconcile.
- **If the dependency ticket is missing entirely** (named in `Depends on`
  but no ticket in the board with that ID, or named declaration doesn't
  exist in the project): spawn a sub-ticket for it (Tier A3), recurse,
  return.

Only hard-stop here if the dependency situation is genuinely off-track
(B2 or B3).

### 2b. Baseline build

```bash
lake build [target_module_for_this_ticket]
```

Must pass. If it doesn't, the project isn't in a state to work — hard stop. Don't try to
fix project-wide breakage from inside a single ticket.

For cleanup tickets: jump straight to delegation in 2c.

### 2c. Cleanup-ticket delegation

If this ticket's type is `cleanup`:

1. Invoke `/cleanup <file>` (the file the cleanup ticket targets).
2. Wait for `/cleanup` to complete its full 8-phase workflow.
3. If `/cleanup` reports success (Phase 6 gates pass), mark this ticket `done`. Skip to
   Phase 8.
4. If `/cleanup` reports failure, this is a stop condition for the cleanup ticket — the
   underlying file has issues. Mark the cleanup ticket `blocked` and report what failed.
   Don't try to fix `/cleanup`'s output yourself.

Cleanup tickets are easy because the heavy lifting is in `/cleanup`. The remaining
phases (3–7) below are only for proof/definition tickets.

---

## PHASE 3 — State the declaration

Open the file the ticket targets. Place the declaration at the right location (per the
ticket's `File` and the natural ordering — defs before lemmas about them; lemmas in
dependency order).

Write the declaration **exactly as stated in the ticket's Statement field**. Don't
modify the signature. Don't "improve" the type. Don't add or drop hypotheses. The
planning agent decided the form; your job is to prove it as stated.

End with `:= by sorry` so the file compiles and you have a target to work against.

```bash
lean_diagnostic_messages [file]
```

Confirm the declaration parses, the `sorry` is registered as a warning, and nothing else
broke.

---

## PHASE 4 — Prove

Work the proof sketch step by step. For each step:

### 4a. Find the lemma (or spawn a sub-ticket)

The sketch names a mathlib lemma (e.g., "Apply `Finset.prod_image`"). Verify the lemma
exists with that exact name and signature:

```
lean_loogle "<expected type signature>"
# OR
lean_local_search "<lemma name>"
```

If the lemma exists with the exact name: use it.

If the lemma exists with a slightly different name: use the actual name. Update the
ticket's progress notes with the actual name found.

If the lemma doesn't exist after the **five-method search** (`mathlib-search.md`):
this is a Tier-A MATHLIB GAP. In beastmode, the default response is spawn
a sub-ticket and continue (A1). Only escalate to B3 (off-track) if the
missing fact is genuinely research-scale:

- **A1 (spawn sub-ticket and continue) — the default**:
  - The missing fact is statable in a few Lean lines
  - It's provable from facts already in mathlib or already in the project
  - It's naturally part of the project's mathematical area

  Spawn a sub-ticket per the "Spawning sub-tickets" section. Statement
  is the needed lemma's type; sketch is what you would do to prove it
  from the existing infrastructure. Recurse into the new ticket.

  In beastmode, "the proof of this sub-ticket will itself need sub-tickets"
  is **not** an escalation reason — it's expected. Spawn whatever depth
  the math requires.

- **B3 (off-track, real stop)** only if the missing fact is at
  published-paper-theorem scale:
  - A research-level result nobody has formalised, requiring its own
    multi-week development by mathlib standards
  - Outside the project's stated mathematical area (`plan.md` explicitly
    excludes it)

  Report B3 with concrete evidence (cite the plan paragraph, name the
  published theorem) and let the user decide whether to ticket it
  upstream, redirect the parent, or pause the project.

In neither case do you invent a "substitute that looks similar" — that's how
silent inconsistency creeps in.

### 4b. Apply the step

Write the tactic call. Run `lean_diagnostic_messages` to see the new goal state. Use
`lean_goal` if you need a fine-grained read of the goal at a specific position.

If the tactic produces an unexpected goal: examine why. Often it's because a hypothesis
needs to be massaged first (`push_cast`, `simp only [foo]`, etc.). The proof sketch may
not list every micro-tactic — small bridging steps are expected. Big detours are not.

### 4c. Loop

Repeat 4a–4b until the proof closes. Use `lean_multi_attempt` aggressively when stuck on
a single goal:

```
lean_multi_attempt [
  "exact <lemma> h",
  "apply <lemma>; exact h",
  "simp [<lemma>]; exact h",
  "grind [<lemma>]"
]
```

### 4d. Checkpoint

Every time you successfully close a goal that was nontrivial (took >1 attempt or
required >1 lemma), update the ticket's progress notes:

```markdown
**Progress**:
- 2026-05-06T10:32: stated the declaration; sorry on line 47
- 2026-05-06T10:38: closed step 1 (Finset.prod_comp); 3 sub-goals remain
- 2026-05-06T10:51: closed step 2 (Finset.prod_image); refining at the n=0 base case
- ...
```

The progress notes serve two purposes: a future `/beastmode --resume` can pick up
exactly where you left off, and the user can scan the ticket board to see how things are
going without reading the full Lean files.

### 4e. Off-script tactics are fine; off-script proofs are not

Small bridging tactics that the sketch doesn't explicitly mention (`push_cast`, `simp`,
`norm_cast`, `omega`, `ring`) are fine — the sketch describes the mathematical argument,
not every Lean micro-step. Use them.

A wholesale change in approach (the sketch said "induction on n", you do "structural
induction on the term") is **not fine** without first proving the planned approach
fails. If you genuinely think there's a better proof, finish the planned one first;
golf in `/cleanup` later.

---

## PHASE 5 — Verify

```bash
lean_diagnostic_messages [file]      # must be clean
grep "sorry" [file]                  # must find none in the new declaration
```

Then check axioms:

```lean
#print axioms decl_name
```

Must show only the standard set: `propext`, `Quot.sound`, `Classical.choice`, plus any
axioms that mathlib uses (these are accepted). If a `sorryAx` appears, your declaration
isn't actually proven — the `sorry` may have been moved into a `have`. Find it. Prove it.

Then a project build:

```bash
lake build [target_module]
```

Must succeed. If it fails on a different file (your change broke something downstream),
that's a Phase-5 stop: the ticket as planned has unforeseen consequences. Hard stop,
condition 4 (SCOPE/DEFINITION ERROR).

---

## PHASE 6 — Gates

Run the cleanup-gates from `references/cleanup-gates.md` on the diff your work
produced:

| Gate                           | Expected for this ticket |
|--------------------------------|--------------------------|
| `lake_build_file`              | ✓ pass                  |
| `definition_protected`         | ✓ pass — the only def changes are the new declaration the ticket created. If the diff touches OTHER def lines, that's a defect. |
| `theorem_statement_protected`  | ✓ pass — the only theorem/lemma changes are the new declaration the ticket created. |
| `cumulative_no_unintended_breakage` | ✓ pass — call sites elsewhere still compile |

Gate failures here mean your work touched something the ticket didn't authorise. Find
out what (the gate's `Details` will name the line) and revert the unauthorised part.

---

## PHASE 7 — Mark done

Update `.mathlib-quality/tickets.md`:

```markdown
### [TXXX] <title>
- **Status**: done   (was: in_progress; finished YYYY-MM-DDTHH:MMZ)
...
```

Append a final progress note:

```markdown
**Progress**:
- ...
- 2026-05-06T11:42: DONE — `decl_name` proven, lake build clean, all gates pass
```

---

## PHASE 8 — Report

### On DONE

```
## /beastmode report — [TXXX] <title>

Status: DONE
Time on ticket: from <start ISO> to <end ISO>
Cycles: <approximate number of try-diagnose-adjust loops>

### Sub-tickets spawned during this session
- [TYYY] <math name> (depth 1) — DONE
- [TZZZ] <math name> (depth 2, spawned from TYYY) — DONE
- ...
(If none: "None.")

### Result (for the original ticket and each sub-ticket completed)
- Declaration: `<decl_name>` at <file>:<line>
- Lines: <N>
- Mathlib lemmas used: <list>
- Off-script bridging tactics needed: <list>

### Diagnostics
✓ lean_diagnostic_messages clean on all touched files
✓ No sorry in the new declarations
✓ #print axioms shows only standard set
✓ lake build clean on <modules>

### Gates
✓ definition_protected
✓ theorem_statement_protected
✓ lake_build_file
✓ cumulative_no_unintended_breakage

### Next ticket
<auto-suggest the next available ticket per dependency analysis, or "none ready">
```

### On a Tier-B hard stop

```
## /beastmode report — [TXXX] <title>

Status: BLOCKED — <one of: SCOPE-DEFINITION ERROR (B2) /
                  OFF-TRACK (B3) / BROKEN BASELINE (B4)>

### Sub-tickets spawned during this session
- [TYYY] <math name> (depth 1) — DONE / in_progress / blocked
- ...

### What stopped the work
<concrete description as required by the corresponding stop condition.
For B3 (OFF-TRACK), cite the specific bullet from the B3 definition that
applies: published-theorem scale, or explicit plan paragraph contradiction.
"I don't like this approach", "this is taking long", "this is hard" are
NOT valid B3 reasons in beastmode. If you find yourself reaching for one
of those, the right move is to keep working — not to stop.>

### What was tried
<specific tactics, mathlib searches, sub-tickets considered but not spawned
because they would also be off-track>

### Concrete suggestion
<a specific change: re-state with extra hypothesis, ticket the missing
lemma upstream to mathlib, replan the parent's sketch via /develop --continue,
etc. Not "this needs rethinking".>

### Ticket state
- Parent: status in_progress (left for the user to decide)
- Sub-tickets that completed: status done
- Sub-tickets that didn't complete: in_progress
- Progress notes updated through <ISO>
```

The original ticket stays `in_progress` so `/develop --status` (or
`/project-status`) shows it. The user decides whether to replan, escalate,
or move on.

---

## Multi-ticket / batch usage

`/beastmode` is single-ticket. To work several in sequence:

```bash
# bash loop in the user's terminal
for i in $(seq 1 10); do
  echo "iteration $i"
  # invoke /beastmode; capture exit; break if BLOCKED
done
```

Or run `/beastmode` repeatedly in Claude Code, each time letting it auto-pick the
next ticket. The pattern keeps each ticket's context isolated, which matches the
"deep focus on one ticket" principle.

For cleanup-cadence-driven sequences, this naturally executes in dependency order:
proof-tickets followed by their cleanup-tickets followed by the next proof-ticket.

---

## Why this design

`/develop` produces the original plan. The ticket has a statement, sketch,
sources, lemmas. But no plan anticipates every sub-step — proofs surface
ingredients the planner didn't foresee. Past versions of this command hard-
stopped on those surprises, which felt productive (concrete report back) but
in practice left workers parked, waiting for the user to manually add a ticket
and resume. Earlier versions also imposed a recursion depth cap and a "sketch
fundamentally wrong" hard stop, both of which broke the marathon flow.

Beastmode's design: **the worker is responsible for finishing the goal, end
to end, without manual intervention except on genuine off-track or wrong-
statement situations.** Gaps with mathematical content become sub-tickets via
`/develop`'s template. Wrong strategies become replans via `/develop --continue`.
Sub-tickets can recurse to any depth the math requires. There is no time
budget. The role separation with `/develop` is preserved — every sub-ticket
and every replan follows `/develop`'s template, so the work is recognisable
to a later planning pass.

Hard stops are reserved for the three cases where the worker genuinely
cannot proceed: the **statement** is wrong (B2 SCOPE / DEFINITION ERROR),
the work has drifted onto material genuinely outside the project's
mathematical scope (B3 OFF-TRACK), or the project doesn't build to start
with (B4 BROKEN BASELINE). "It's hard" is still not evidence. Neither is
"this is taking a while" — marathon sessions are expected to take a while.

---

## Reference

- `commands/develop.md` — the planner that produces the tickets this skill executes
- `references/cleanup-gates.md` — the gate definitions used in Phase 6
- `references/mathlib-search.md` — the five-method search used in Phase 4a
- `commands/cleanup.md` — invoked directly by Phase 2c when the ticket is a cleanup ticket
