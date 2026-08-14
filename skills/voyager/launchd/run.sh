#!/bin/zsh
# Daily Voyager run — launched by launchd (com.tauceti.voyager) at 16:03 local.
# Runs a fresh headless Claude Code session, falling back across accounts if the
# first one cannot run (usage limit, org restriction, auth failure).
# Optional $1: alternative prompt file (used for smoke tests).
#
# Why the fallback cannot key off the exit status: `claude -p` exits 0 even when it
# never ran a turn — an exhausted weekly limit and an org-disabled subscription both
# print a one-line notice and exit 0. The authoritative signals are therefore
#   (a) the VOYAGER_RESULT sentinel the prompt requires on every terminal outcome, and
#   (b) freshness.py, a read-only check for a Voyager post/DM inside the 2h window.
# Re-running after a partial failure is safe: the skill's own freshness abort makes a
# second attempt exit quietly rather than double-post.

set -u

export PATH="/Users/mcu22seu/.local/bin:/Users/mcu22seu/.nvm/versions/node/v22.9.0/bin:/opt/homebrew/bin:/Users/mcu22seu/miniforge3/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
export HOME="/Users/mcu22seu"

VOYAGER_DIR="$HOME/.claude3/voyager"
PROMPT_FILE="${1:-$VOYAGER_DIR/prompt.txt}"

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

for acct in "${ACCOUNTS[@]}"; do
  label="${acct##*/}"; [[ "$acct" == "DEFAULT" ]] && label="default"

  # Never start an attempt if the day's work already landed — covers the case where a
  # previous attempt posted but died before printing its sentinel.
  if python3 "$VOYAGER_DIR/freshness.py"; then
    echo "── stopping before $label: today's update is already out"
    overall=0
    break
  fi

  echo "── attempt: $label ($(date '+%H:%M:%S'))"
  out="$(mktemp)"
  if [[ "$acct" == "DEFAULT" ]]; then
    env -u CLAUDE_CONFIG_DIR claude -p "$PROMPT" --dangerously-skip-permissions 2>&1 | tee "$out"
  else
    CLAUDE_CONFIG_DIR="$acct" claude -p "$PROMPT" --dangerously-skip-permissions 2>&1 | tee "$out"
  fi

  if grep -qiE 'weekly limit|usage limit|rate limit|disabled Claude subscription|Invalid API key|please run /login' "$out"; then
    echo "── $label unavailable (limit or auth) — falling through"
    rm -f "$out"; continue
  fi

  result="$(grep -o 'VOYAGER_RESULT:[^\"]*' "$out" | tail -1)"
  rm -f "$out"

  case "$result" in
    *posted*|*quiet-checkin*|*empty-window*|*freshness-abort*|*smoke-ok*)
      echo "── $label succeeded — $result"
      overall=0; break ;;
    *failed*)
      echo "── $label reported failure — $result — falling through" ;;
    *)
      echo "── $label produced no VOYAGER_RESULT sentinel — treating as a failed run, falling through" ;;
  esac
done

if (( overall != 0 )); then
  echo "── ALL ACCOUNTS FAILED. No Voyager update today; the watermark is untouched, so tomorrow's run covers this window too."
fi

echo "── voyager run finished: $(date '+%Y-%m-%d %H:%M:%S %Z') status=$overall"
exit $overall
