#!/usr/bin/env python3
"""Exit 0 if a Voyager post/state-DM landed within the freshness window, else 1.

Used by run.sh as the authoritative "did the work already get done" test, because
`claude -p` exits 0 even when it never ran (rate limit, org restriction). Read-only;
never posts. Never prints the API key.
"""
import datetime
import json
import os
import subprocess
import sys

WINDOW_HOURS = 2.0


def zuliprc():
    cfg = {}
    with open(os.path.expanduser("~/.zuliprc")) as fh:
        for line in fh:
            if "=" in line:
                k, _, v = line.partition("=")
                cfg[k.strip()] = v.strip()
    return cfg["site"], cfg["email"], cfg["key"]


def newest_age_hours(site, email, key, narrow):
    out = subprocess.run(
        ["curl", "-sS", "--max-time", "30", "-u", f"{email}:{key}", "-G",
         f"{site}/api/v1/messages",
         "--data-urlencode", "anchor=newest",
         "--data-urlencode", "num_before=1",
         "--data-urlencode", "num_after=0",
         "--data-urlencode", "apply_markdown=false",
         "--data-urlencode", f"narrow={json.dumps(narrow)}"],
        capture_output=True, text=True)
    msgs = json.loads(out.stdout).get("messages") or []
    if not msgs:
        return None
    ts = datetime.datetime.fromtimestamp(msgs[0]["timestamp"], datetime.timezone.utc)
    return (datetime.datetime.now(datetime.timezone.utc) - ts).total_seconds() / 3600.0


def main():
    try:
        site, email, key = zuliprc()
    except Exception as exc:                       # noqa: BLE001
        print(f"freshness: cannot read ~/.zuliprc ({exc.__class__.__name__})")
        return 1                                   # unknown -> let the run proceed
    ages = []
    for narrow in (
        [{"operator": "channel", "operand": "Tau Ceti"},
         {"operator": "topic", "operand": "new results"},
         {"operator": "sender", "operand": email}],
        [{"operator": "dm", "operand": email}],
    ):
        try:
            age = newest_age_hours(site, email, key, narrow)
        except Exception:                          # noqa: BLE001
            age = None
        if age is not None:
            ages.append(age)
    if not ages:
        print("freshness: no Zulip history readable")
        return 1
    youngest = min(ages)
    if youngest < WINDOW_HOURS:
        print(f"freshness: newest Voyager activity {youngest:.2f}h old — today is done")
        return 0
    print(f"freshness: newest Voyager activity {youngest:.1f}h old — a run is needed")
    return 1


if __name__ == "__main__":
    sys.exit(main())
