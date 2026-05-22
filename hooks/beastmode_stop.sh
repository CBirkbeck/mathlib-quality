#!/usr/bin/env bash
# mathlib-quality :: beastmode Stop-hook driver
#
# WHAT THIS DOES
#   While a /beastmode marathon is active, this hook refuses the agent's turn-end and
#   re-prompts it to continue — so one session sustains across many turns instead of
#   stopping after ~2-3 minutes. This is the mechanism that makes beastmode actually
#   unstoppable: a turn-end becomes a re-prompt, not a session-end.
#
# HOW IT IS GATED (fail-safe)
#   Activation hinges on a sentinel file that the /beastmode skill writes on start and
#   removes on a genuine terminal state (DONE / B2 / B3 / B4). No sentinel  ->  this hook
#   is inert and the stop proceeds normally. On ANY doubt the hook allows the stop
#   (exit 0). It never blocks a non-beastmode session.
#
# ESCAPES (all immediate)
#   * press Esc                                 -> cancels the pending continuation
#   * rm .mathlib-quality/beastmode_active      -> disables blocking on the next stop
#   * progress budget (below)                   -> auto-releases if no .lean / ticket
#                                                  change for BEASTMODE_MAX_BLOCKS stops
#
# TUNABLES (env)
#   BEASTMODE_MAX_BLOCKS   consecutive no-progress stops before auto-release.
#                          default 30; set 0 for unlimited (power users only).
#
# I/O CONTRACT
#   stdin : Stop-hook JSON (consumed, not parsed; project root comes from
#           CLAUDE_PROJECT_DIR per the hook contract).
#   stdout: nothing (allow stop) | {"decision":"block","reason":"..."} (block stop).
#   exit  : always 0. A block is signalled by the JSON, not the exit code.

# Consume stdin so the producing pipe never blocks. We do not need to parse it.
cat >/dev/null 2>&1 || true

root="${CLAUDE_PROJECT_DIR:-$PWD}"
sentinel="$root/.mathlib-quality/beastmode_active"
tickets="$root/.mathlib-quality/tickets.md"
state="$root/.mathlib-quality/.beastmode_stop_state"

# 1) Inert unless a beastmode session is active.
[ -f "$sentinel" ] || exit 0

# 2) Progress budget (runaway guard). Count consecutive stops with no file progress;
#    reset to 0 whenever a .lean file or tickets.md changed since our last stamp.
max="${BEASTMODE_MAX_BLOCKS:-30}"
count=0
[ -f "$state" ] && count=$(cat "$state" 2>/dev/null || echo 0)
case "$count" in ''|*[!0-9]*) count=0 ;; esac

progressed=0
if [ -f "$state" ]; then
  if [ -n "$(find "$root" -name '*.lean' -not -path '*/.lake/*' -not -path '*/.git/*' \
              -newer "$state" -print -quit 2>/dev/null)" ]; then
    progressed=1
  fi
  if [ -f "$tickets" ] && [ "$tickets" -nt "$state" ]; then
    progressed=1
  fi
else
  progressed=1   # first stop of the session: assume progress
fi

if [ "$progressed" -eq 1 ]; then
  count=0
else
  count=$((count + 1))
fi
printf '%s' "$count" > "$state" 2>/dev/null || true
touch "$state" 2>/dev/null || true   # stamp = now, for the next -newer comparison

# 3) Stuck guard: release the stop if no progress for `max` consecutive turns.
if [ "$max" -gt 0 ] 2>/dev/null && [ "$count" -ge "$max" ]; then
  rm -f "$sentinel" "$state" 2>/dev/null || true
  exit 0   # allow stop; sentinel cleared so the user can intervene / re-run /beastmode
fi

# 4) Work remains -> block the turn-end and inject the next concrete action.
#    Keep the reason single-line and free of " and % so it embeds in JSON verbatim.
reason='beastmode is active (.mathlib-quality/beastmode_active present). Do NOT stop, summarise, or ask to continue. Read .mathlib-quality/beastmode_active for your CURRENT FOCUS and resume that exact step; if it records no focus, Read .mathlib-quality/tickets.md and pick the next open ticket with met dependencies. Your next message MUST begin with a tool call toward that goal (a lean_* call, an Edit, or a mathlib search) — not prose. End the session ONLY by: (a) board empty -> print the BEASTMODE-DONE line, then rm .mathlib-quality/beastmode_active; (b) a genuine B2/B3/B4 stop -> emit the report, then rm .mathlib-quality/beastmode_active. Nothing else is a valid stop.'
printf '{"decision":"block","reason":"%s"}\n' "$reason"
exit 0
