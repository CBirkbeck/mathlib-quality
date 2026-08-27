#!/bin/zsh
# Daily Voyager run — launched by launchd (com.tauceti.voyager) at 16:03 local.
# Runs a fresh headless Claude Code session, preferring the Fable model (owner
# request, 2026-08-19): the chain is models × accounts, so every account is probed
# for claude-fable-5 before any attempt falls back to claude-opus-5.
# Optional $1: alternative prompt file (used for smoke tests).
#
# Why the fallback cannot key off the exit status: `claude -p` exits 0 even when it
# never ran a turn — an exhausted weekly limit and an org-disabled subscription both
# print a one-line notice and exit 0. The authoritative signals are therefore
#   (a) a cheap entitlement probe before each attempt: a one-line completion on the
#       exact model, which is the only true test of "this account can run this model
#       right now" (there is no headless credits query),
#   (b) the VOYAGER_RESULT sentinel the prompt requires on every terminal outcome, and
#   (c) freshness.py, a read-only check for a Voyager post/DM inside the 2h window.
# Re-running after a partial failure is safe: the skill's own freshness abort makes a
# second attempt exit quietly rather than double-post.

set -u

export PATH="/Users/mcu22seu/.local/bin:/Users/mcu22seu/.nvm/versions/node/v22.9.0/bin:/opt/homebrew/bin:/Users/mcu22seu/miniforge3/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
export HOME="/Users/mcu22seu"

VOYAGER_DIR="$HOME/.claude3/voyager"
PROMPT_FILE="${1:-$VOYAGER_DIR/prompt.txt}"

# Model preference, outermost loop: try Fable on EVERY account before Opus on any,
# so a Fable-entitled account always beats an Opus-only one.
MODELS=("claude-fable-5" "claude-opus-5")
# Tests may override: VOYAGER_MODELS="claude-opus-5" run.sh smoke.txt
if [[ -n "${VOYAGER_MODELS:-}" ]]; then
  MODELS=(${=VOYAGER_MODELS})
  echo "── model chain overridden: ${MODELS[*]}"
fi

# Ordered fallback chain. "DEFAULT" means: run with CLAUDE_CONFIG_DIR unset (~/.claude.json).
# .claude5 is deliberately absent — its org has Claude Code subscription access disabled,
# so it can never serve; re-add it if that changes.
ACCOUNTS=("$HOME/.claude3" "$HOME/.claude2" "$HOME/.claude4" "DEFAULT")
# Tests may override the chain: VOYAGER_ACCOUNTS="/path/a /path/b" run.sh smoke.txt
if [[ -n "${VOYAGER_ACCOUNTS:-}" ]]; then
  ACCOUNTS=(${=VOYAGER_ACCOUNTS})
  echo "── account chain overridden: ${ACCOUNTS[*]}"
fi

echo ""
echo "══════════════════════════════════════════════════════════"
echo "voyager run: $(date '+%Y-%m-%d %H:%M:%S %Z') prompt=$PROMPT_FILE"
echo "══════════════════════════════════════════════════════════"

PROMPT="$(cat "$PROMPT_FILE")"
overall=1

# probe <config-dir|DEFAULT> <model>: succeeds iff the account completes a one-line
# turn on that exact model. A missing entitlement, an exhausted limit, and a broken
# login all fail the same way — no VOYAGER_PROBE_OK in the output. Costs one trivial
# completion; on a normal day the whole run spends exactly one probe.
probe() {
  local po
  if [[ "$1" == "DEFAULT" ]]; then
    po="$(env -u CLAUDE_CONFIG_DIR claude -p 'Reply with exactly: VOYAGER_PROBE_OK' --model "$2" 2>&1)"
  else
    po="$(CLAUDE_CONFIG_DIR="$1" claude -p 'Reply with exactly: VOYAGER_PROBE_OK' --model "$2" 2>&1)"
  fi
  [[ "$po" == *VOYAGER_PROBE_OK* ]]
}

for model in "${MODELS[@]}"; do
  for acct in "${ACCOUNTS[@]}"; do
    label="${acct##*/}"; [[ "$acct" == "DEFAULT" ]] && label="default"

    # Never start an attempt if the day's work already landed — covers the case where
    # a previous attempt posted but died before printing its sentinel.
    if python3 "$VOYAGER_DIR/freshness.py"; then
      echo "── stopping before $label: today's update is already out"
      overall=0
      break 2
    fi

    if ! probe "$acct" "$model"; then
      echo "── $label cannot run $model right now (probe failed) — next"
      continue
    fi

    echo "── attempt: $label model=$model ($(date '+%H:%M:%S'))"
    out="$(mktemp)"
    if [[ "$acct" == "DEFAULT" ]]; then
      env -u CLAUDE_CONFIG_DIR claude -p "$PROMPT" --model "$model" --dangerously-skip-permissions 2>&1 | tee "$out"
    else
      CLAUDE_CONFIG_DIR="$acct" claude -p "$PROMPT" --model "$model" --dangerously-skip-permissions 2>&1 | tee "$out"
    fi

    result="$(grep -o 'VOYAGER_RESULT:[^\"]*' "$out" | tail -1)"

    # Account health is decided by the SENTINEL FIRST, never by scanning the whole
    # transcript. A run that completed always prints VOYAGER_RESULT; a Claude account
    # that is rate-limited or unauthenticated never gets far enough to print one. The
    # limit-phrase grep therefore only applies when no sentinel came back — otherwise
    # it matches the agent's own prose about *other* services' limits and mislabels a
    # perfectly healthy account. That is exactly what happened on 2026-08-15: .claude2
    # and .claude4 both ran the full window and reported the codex quota in their
    # summaries, and the chain marked them rate-limited and burned two more accounts.
    if [[ -z "$result" ]]; then
      if grep -qiE 'weekly limit|usage limit|rate limit|disabled Claude subscription|Invalid API key|please run /login' "$out"; then
        echo "── $label unavailable (limit or auth) — falling through"
      else
        echo "── $label produced no VOYAGER_RESULT sentinel — treating as a failed run, falling through"
      fi
      rm -f "$out"; continue
    fi
    rm -f "$out"

    case "$result" in
      *posted*|*quiet-checkin*|*empty-window*|*freshness-abort*|*smoke-ok*)
        echo "── $label succeeded — $result"
        echo "── served by $label on $model"
        overall=0; break 2 ;;
      *failed-chatgpt*)
        # Machine-level blocker (codex quota / model entitlement), not an account one.
        # Every remaining account would fail identically, so stop rather than churn.
        echo "── $label reported $result — machine-level blocker, not account-level; stopping instead of retrying elsewhere"
        break 2 ;;
      *failed*)
        echo "── $label reported failure — $result — falling through" ;;
    esac
  done

  if (( overall != 0 )); then
    echo "── no account could serve model=$model — trying the next model tier (if any)"
  fi
done

if (( overall != 0 )); then
  echo "── ALL ACCOUNTS FAILED. No Voyager update today; the watermark is untouched, so tomorrow's run covers this window too."
fi

echo "── voyager run finished: $(date '+%Y-%m-%d %H:%M:%S %Z') status=$overall"
exit $overall
