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
| `freshness.py` | `~/.claude3/voyager/freshness.py` (read-only "has today's post landed?" check) |

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

## Account fallback

`run.sh` walks an ordered chain of Claude accounts and stops at the first that completes the
run: **`.claude3` → `.claude2` → `.claude4` → default** (`CLAUDE_CONFIG_DIR` unset,
`~/.claude.json`). `.claude5` is deliberately excluded — its organisation has Claude Code
subscription access disabled, so it can never serve; re-add it if that changes.

**Exit status cannot drive the fallback.** `claude -p` exits **0** even when it never ran a
turn: an exhausted weekly limit and an org-disabled subscription each print one line and exit
cleanly (both observed on this machine, 2026-08-14). The chain therefore keys off two positive
signals instead:

1. **The `VOYAGER_RESULT:` sentinel**, required by `prompt.txt` as the last line of every
   terminal outcome — `posted-<id>`, `quiet-checkin-<id>`, `empty-window`, `freshness-abort`, or
   `failed-<reason>`. A *missing* sentinel means the model never got to run, so the chain moves
   to the next account. Known limit/auth strings are matched first, purely so the log says why.
2. **`freshness.py`**, run before every attempt: a read-only check for a Voyager post or state
   DM inside the 2-hour window. If one exists the chain stops immediately, which covers the case
   where an attempt posted successfully but died before printing its sentinel.

Retrying is safe by construction: the skill's own freshness abort makes a second attempt exit
quietly rather than double-post, and the permanent `TauCeti#NNN` dedupe backs that up. If every
account fails, the log says so loudly and nothing is posted — the watermark is untouched, so the
next day's run covers the missed window too.

Test the chain without spending a real run by overriding it and using the read-only smoke prompt:

```bash
VOYAGER_ACCOUNTS="$HOME/.claude5 $HOME/.claude2" ~/.claude3/voyager/run.sh \
  ~/.claude3/voyager/smoke.txt      # .claude5 fails fast, .claude2 answers: proves the fallback
```

Every account in the chain needs the chatgpt-math MCP for the significance gate; all four have
it. Zulip credentials (`~/.zuliprc`) and the `gh` keychain login are shared, so they are
account-independent.
