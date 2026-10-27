#!/usr/bin/env python3
"""Screenshots of the scenario and every card, for a visual pass: desktop and phone width, light and dark.

    shots.py OUT_DIR [BASE_URL]   # BASE_URL defaults to http://127.0.0.1:8767/index.html (a server over this dir)

Uses the page's ?shot=<card>:<step> mode and Playwright's cached headless Chromium (CHROME overrides it).
"""
import glob
import json
import os
import pathlib
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

here = pathlib.Path(__file__).resolve().parent
out = pathlib.Path(sys.argv[1]).resolve()
base = sys.argv[2] if len(sys.argv) > 2 else "http://127.0.0.1:8767/index.html"
chrome = os.environ.get("CHROME") or sorted(glob.glob(os.path.expanduser(
    "~/Library/Caches/ms-playwright/chromium_headless_shell-*/chrome-headless-shell-*/chrome-headless-shell")))[-1]
data = json.loads((here / "frames.json").read_text(encoding="utf-8"))

# the scenario at a few telling steps; each card at its first failure and at its end, with its code open
targets = [("l1", i, False) for i in (2, 4, 9, 11)]
for cid, c in data["cards"].items():
    n = len(c["frames"])
    targets += [(cid, 1, False), (cid, n - 1, True)]
configs = [("desktop", 1440, 1100), ("phone", 390, 1900)]
themes = ["light", "dark"]
out.mkdir(parents=True, exist_ok=True)


def shot(job):
    (cid, step, code), (cname, w, h), theme = job
    name = f"{cname}-{theme}-{cid}-{step}{'-code' if code else ''}.png"
    url = f"{base}?shot={cid}:{step}&theme={theme}" + ("&code=1" if code else "")
    subprocess.run([chrome, "--headless", "--hide-scrollbars", f"--window-size={w},{h}", "--virtual-time-budget=4000",
                    f"--screenshot={out / name}", url], check=True, capture_output=True, timeout=60)
    return name


jobs = [(t, c, th) for t in targets for c in configs for th in themes]
with ThreadPoolExecutor(6) as ex:
    for name in ex.map(shot, jobs):
        print(name)
