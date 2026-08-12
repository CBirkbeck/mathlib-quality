#!/bin/zsh
# Daily Voyager run — launched by launchd (com.tauceti.voyager) at 16:03 local.
# Runs a fresh headless Claude Code session on the claude3 account.
# Optional $1: alternative prompt file (used for smoke tests).

set -u

# launchd starts with a minimal environment: build the PATH by hand.
export PATH="/Users/mcu22seu/.local/bin:/Users/mcu22seu/.nvm/versions/node/v22.9.0/bin:/opt/homebrew/bin:/Users/mcu22seu/miniforge3/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
export HOME="/Users/mcu22seu"
export CLAUDE_CONFIG_DIR="$HOME/.claude3"

PROMPT_FILE="${1:-$HOME/.claude3/voyager/prompt.txt}"

echo ""
echo "══════════════════════════════════════════════════════════"
echo "voyager run: $(date '+%Y-%m-%d %H:%M:%S %Z') prompt=$PROMPT_FILE"
echo "══════════════════════════════════════════════════════════"

claude -p "$(cat "$PROMPT_FILE")" --dangerously-skip-permissions
rc=$?

echo "── voyager run finished: $(date '+%Y-%m-%d %H:%M:%S %Z') exit=$rc"
exit $rc
