# Voyager scheduler

The daily run is owned by **launchd** (`com.tauceti.voyager`), not by a session cron. These
are the files it executes. They were untracked until 2026-08-15 — living only in
`~/.claude3/voyager/` on one machine, with no review trail and no backup.

**`~/.claude3/voyager/` remains the deployed copy.** These are the reviewable source of
truth; edits here do nothing until they are copied across:

```sh
cp skills/voyager/scheduler/{prompt.txt,run.sh,freshness.py,status.py,smoke.txt} \
   ~/.claude3/voyager/
```

| file | role |
|---|---|
| `prompt.txt` | what launchd hands to `claude -p`. Carries the standing rules, which **override `SKILL.md`** where they conflict. |
| `run.sh` | the account-fallback wrapper: tries each Claude account in turn until one returns a terminal `VOYAGER_RESULT` sentinel. |
| `freshness.py` | asks Zulip directly whether today's update is already out. Exit 0 = already posted, stop. Run before every attempt, so a partial run cannot double-post. |
| `status.py` | backs the `voyager-status` alias: schedule loaded, last run, whether today posted, account chain. |
| `smoke.txt` | a read-only prompt that verifies the headless environment (git, gh, Zulip read) without posting. |

## Two lessons the code now encodes

**Account health is decided by the sentinel, never by scanning the transcript.** `run.sh`
used to grep the whole output for `usage limit|weekly limit|…` to decide whether an account
was rate-limited. On 2026-08-15 two healthy accounts described *codex's* quota in their own
reports, matched that grep, and were logged as rate-limited Claude accounts — so the chain
burned every remaining account on a blocker no account switch could fix, and `voyager-status`
reported four dead accounts when two were fine. A completed run always prints
`VOYAGER_RESULT`; a rate-limited account never gets far enough to. So the sentinel is checked
first, and the limit-phrase grep applies only when no sentinel came back.

**A machine-level blocker stops the chain.** `failed-chatgpt-*` means the significance gate
could not run, which is a property of the machine's codex credentials, not of the Claude
account. Retrying elsewhere fails identically, so the chain stops rather than churning.

## The significance gate is best-effort

`prompt.txt` clause (3) and `SKILL.md` §4 both say so, and they must stay in agreement. A run
that cannot reach the chatgpt-math MCP posts anyway, on its own judgement, and notes the
reason in the log — never in the Zulip message. Holding the post was the failure mode on
2026-08-15: two runs read all 138 PRs in the window, assembled a slate, and published nothing.
