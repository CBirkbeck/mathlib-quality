# launchd scheduling for the daily Voyager run

Since 2026-08-12 the daily 16:03 run is fired by macOS `launchd`, not by a session cron.
The session-cron era's two failure modes — the scheduler dying with its session (2026-08-11
credits incident) and 20–40 minute App-Nap drift on an idle terminal — do not apply to
launchd: it fires on the wall clock while the machine is awake, and coalesces a missed
firing into one run on wake.

Installed on the operator machine as:

| file | installed at |
|---|---|
| `com.tauceti.voyager.plist` | `~/Library/LaunchAgents/com.tauceti.voyager.plist` |
| `run.sh` | `~/.claude3/voyager/run.sh` |
| `prompt.txt` | `~/.claude3/voyager/prompt.txt` |
| `smoke.txt` | `~/.claude3/voyager/smoke.txt` (read-only environment test: `run.sh smoke.txt`) |

Each firing runs a **fresh headless Claude Code session** (`claude -p`, claude3 account via
`CLAUDE_CONFIG_DIR`, `--dangerously-skip-permissions`) with `prompt.txt` — the same daily
prompt the session cron carried, minus the cron-upkeep step (launchd has no 7-day expiry)
and with ask-Chris rerouted to the run log. All bot state stays in the Zulip self-DM, so
fresh sessions are the designed mode. Logs: `~/Library/Logs/voyager.log`.

Operate it with:

```bash
launchctl print gui/$(id -u)/com.tauceti.voyager      # inspect, incl. last exit status
launchctl kickstart gui/$(id -u)/com.tauceti.voyager  # fire a run now (freshness abort keeps it safe)
launchctl bootout gui/$(id -u)/com.tauceti.voyager    # disable
tail -f ~/Library/Logs/voyager.log                    # watch a run
```

The wrapper pins PATH by hand (launchd's environment is minimal): `claude` and `uvx` from
`~/.local/bin`, node from the nvm install the chatgpt-math MCP needs, `gh` from Homebrew.
If node is upgraded via nvm, update the path in `run.sh`. The 2h freshness abort makes a
double-fire against any leftover session cron harmless — whichever runs second exits quietly.
