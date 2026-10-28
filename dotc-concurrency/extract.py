#!/usr/bin/env python3
"""Extract the cards' code excerpts (excerpts.json) from the compiler at a pinned commit into excerpts.gen.json.

Each excerpt runs from the first line matching `start` to the next matching `end` (plus `after` lines), with
comments, bookkeeping annotations and `skip` lines dropped; a run of dropped code lines shows as one `⋯`. `hl` patterns (and `sig`, where a cancellation arrives) are resolved to the
excerpt's lines here, so a pattern that matches nothing is an error, not a quiet loss of a highlight.

    extract.py [--check]   # SCALA3=<a checkout of the compiler's repository>, default ~/code/scala/scala3

--check extracts again and fails if the result differs from excerpts.gen.json: the code at the pinned commit
no longer reads as the cards say, or the spec changed without a new extraction.
"""
import json
import os
import pathlib
import re
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
spec = json.loads((here / "excerpts.json").read_text(encoding="utf-8"))
repo = os.path.expanduser(os.environ.get("SCALA3", "~/code/scala/scala3"))
out_path = here / "excerpts.gen.json"


def show(path):
    return subprocess.run(["git", "-C", repo, "show", f"{spec['sha']}:{path}"], check=True, capture_output=True,
                          text=True).stdout.split("\n")


# The state map's bookkeeping annotations (`@cache`, `@publishedBy(...)`, `@treeState`, ...) are left off; `@volatile`,
# which changes what the code means, stays.
ANNOT = re.compile(r'@(\w+)(\((?:[^()"]|"[^"]*")*\))?\s*')


def strip_annotations(line):
    ind = line[:len(line) - len(line.lstrip())]
    rest = line.lstrip()
    out = ""
    while rest.startswith("@"):
        m = ANNOT.match(rest)
        if not m:
            break
        if m.group(1) == "volatile":
            out += "@volatile "
        rest = rest[m.end():]
    return ind + out + rest


def strip_comment(line):
    # a trailing `// …` outside a string literal
    i = line.find(" //")
    if i >= 0 and line[:i].count('"') % 2 == 0:
        return line[:i].rstrip()
    return line


def excerpt(card, ex, cache):
    lines = cache.setdefault(ex["file"], show(ex["file"]))
    s = next((i for i, l in enumerate(lines) if re.search(ex["start"], l)), None)
    if s is None:
        sys.exit(f"{card}: no line matches start {ex['start']!r} in {ex['file']}")
    e = next((i for i in range(s, len(lines)) if re.search(ex["end"], lines[i])), None)
    if e is None:
        sys.exit(f"{card}: no line matches end {ex['end']!r} after line {s + 1} in {ex['file']}")
    e += ex.get("after", 0)
    out, in_doc, dropped = [], False, False
    for i in range(s, e + 1):
        raw = lines[i]
        t = raw.strip()
        if in_doc:
            in_doc = "*/" not in t
            continue
        if t.startswith("/*"):
            in_doc = "*/" not in t
            continue
        if t.startswith("//") or not t:
            continue
        if any(re.search(p, raw) for p in ex.get("skip", [])):
            dropped = True
            continue
        text = strip_annotations(strip_comment(raw))
        if not text.strip():
            continue
        if dropped:
            out.append({"n": None, "text": "⋯"})
            dropped = False
        out.append({"n": i + 1, "text": text})
    # the common indent, so that the excerpt starts at column 0
    ind = min(len(x["text"]) - len(x["text"].lstrip()) for x in out if x["n"] is not None)
    for x in out:
        if x["n"] is not None:
            x["text"] = x["text"][ind:]
        else:
            x["text"] = " " * 0 + "⋯"
    hl = {}
    for beat, pats in ex.get("hl", {}).items():
        idx = []
        for p in pats:
            hits = [j for j, x in enumerate(out) if x["n"] is not None and re.search(p, x["text"])]
            if not hits:
                sys.exit(f"{card}: highlight {p!r} (step {beat}) matches no line of the excerpt from {ex['file']}")
            idx += hits
        hl[beat] = sorted(set(idx))
    # `sig`: where a cancellation arrives from outside, per step; an entry is a pattern, or [pattern, label]
    sig = {}
    for beat, entries in ex.get("sig", {}).items():
        marks = []
        for e in entries:
            p, label = (e, "cancel") if isinstance(e, str) else e
            hits = [j for j, x in enumerate(out) if x["n"] is not None and re.search(p, x["text"])]
            if not hits:
                sys.exit(f"{card}: signal {p!r} (step {beat}) matches no line of the excerpt from {ex['file']}")
            marks.append([hits[0], label])
        sig[beat] = marks
    r = {"file": ex["file"].split("/")[-1], "path": ex["file"], "url": f"{spec['github']}/blob/{full_sha}/{ex['file']}",
         "lines": out, "hl": hl}
    if sig:
        r["sig"] = sig
    return r


full_sha = subprocess.run(["git", "-C", repo, "rev-parse", spec["sha"]], check=True, capture_output=True, text=True).stdout.strip()


def extract():
    cache = {}
    return {"sha": spec["sha"], "cards": {c: [excerpt(c, ex, cache) for ex in exs] for c, exs in spec["cards"].items()}}


result = json.dumps(extract(), indent=1, ensure_ascii=False) + "\n"
if "--check" in sys.argv:
    if not out_path.exists() or out_path.read_text(encoding="utf-8") != result:
        sys.exit("excerpts.gen.json is out of date with excerpts.json at " + spec["sha"] + ": run extract.py")
    print("excerpts: up to date at", spec["sha"])
else:
    out_path.write_text(result, encoding="utf-8")
    print("wrote", out_path)
