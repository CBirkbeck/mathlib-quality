#!/usr/bin/env python3
"""One-screen answer to "is Voyager working?".

Reports: whether the launchd agent is loaded and when it next fires, what the last
run did (which account served it, what it decided, how long it took), whether a run
is in flight, and whether today's update is actually out on Zulip.

Read-only. Never posts, never prints the API key.  Run:  voyager-status
"""
import datetime
import os
import re
import subprocess
import sys

LOG = os.path.expanduser("~/Library/Logs/voyager.log")
VOYAGER_DIR = os.path.expanduser("~/.claude3/voyager")
LABEL = "com.tauceti.voyager"
GREEN, RED, YELL, DIM, OFF = "\033[32m", "\033[31m", "\033[33m", "\033[2m", "\033[0m"


def agent_state():
    uid = os.getuid()
    out = subprocess.run(["launchctl", "print", f"gui/{uid}/{LABEL}"],
                         capture_output=True, text=True)
    if out.returncode != 0:
        return None, None
    state = re.search(r"^\s*state = (.+?)\s*$", out.stdout, re.M)
    last = re.search(r"last exit code = (\S+)", out.stdout)
    return (state.group(1) if state else "?"), (last.group(1) if last else None)


def next_fire(hour=16, minute=3):
    now = datetime.datetime.now()
    fire = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if fire <= now:
        fire += datetime.timedelta(days=1)
    delta = fire - now
    hrs, rem = divmod(int(delta.total_seconds()), 3600)
    return fire, f"{hrs}h {rem // 60}m"


def last_run():
    if not os.path.exists(LOG):
        return None
    text = open(LOG, errors="replace").read()
    blocks = re.split(r"^voyager run: ", text, flags=re.M)[1:]
    if not blocks:
        return None
    b = blocks[-1]
    started = b.split("\n")[0].split(" prompt=")[0].strip()
    attempts = re.findall(r"── attempt: (\S+)", b)
    served = re.search(r"── (\S+) succeeded — VOYAGER_RESULT: (\S+)", b)
    sentinel = re.search(r"VOYAGER_RESULT: (\S+)", b)
    finished = re.search(r"── voyager run finished: (.+?) (?:status|exit)=(\d+)", b)
    allfail = "ALL ACCOUNTS FAILED" in b
    skipped = re.findall(r"── (\S+) unavailable \(limit or auth\)", b)
    return dict(started=started, attempts=attempts, served=served, sentinel=sentinel,
                finished=finished, allfail=allfail, skipped=skipped, n_blocks=len(blocks))


def main():
    print(f"\n{DIM}Voyager status — {datetime.datetime.now():%Y-%m-%d %H:%M:%S %Z}{OFF}")

    state, last_exit = agent_state()
    fire, until = next_fire()
    if state is None:
        print(f"  schedule   {RED}NOT LOADED{OFF} — launchd agent {LABEL} is not registered")
    else:
        print(f"  schedule   {GREEN}loaded{OFF} ({state}), next fire {fire:%a %H:%M} (in {until})")

    r = last_run()
    if not r:
        print(f"  last run   {YELL}none logged yet{OFF}")
    else:
        if r["finished"]:
            when, status = r["finished"].group(1), r["finished"].group(2)
            if r["allfail"]:
                verdict = f"{RED}ALL ACCOUNTS FAILED{OFF}"
            elif r["served"]:
                verdict = (f"{GREEN}{r['served'].group(1)}{OFF} → "
                           f"{r['served'].group(2)}")
            elif r["sentinel"]:
                verdict = f"{GREEN}{r['sentinel'].group(1)}{OFF}"
            else:
                verdict = f"{YELL}no sentinel (predates the fallback system){OFF}"
            print(f"  last run   started {r['started']}")
            print(f"             finished {when} (status {status}) — {verdict}")
        else:
            print(f"  last run   {YELL}IN FLIGHT{OFF} — started {r['started']}, "
                  f"on {r['attempts'][-1] if r['attempts'] else '?'}")
        if r["skipped"]:
            print(f"             fell through: {', '.join(r['skipped'])}")

    fr = subprocess.run([sys.executable, f"{VOYAGER_DIR}/freshness.py"],
                        capture_output=True, text=True)
    msg = (fr.stdout or "").strip().replace("freshness: ", "")
    print(f"  today      {(GREEN + 'posted' + OFF) if fr.returncode == 0 else (YELL + 'not yet' + OFF)} — {msg}")
    print(f"  chain      .claude3 → .claude2 → .claude4 → default{DIM}  (.claude5 org-disabled){OFF}")
    print(f"{DIM}  log: {LOG}{OFF}\n")


if __name__ == "__main__":
    main()
