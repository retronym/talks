#!/usr/bin/env python3
"""Inline talk.md, the scenario's frames.json, the code excerpts (excerpts.gen.json, see extract.py) and the hand-written before code (before.json) into template.html, producing index.html.

Rendering (markdown, the scenario player, chunking into cards) happens in the browser, so this step only embeds
the sources. The result is one self-contained page that also works from file://.
"""
import json
import pathlib
import sys

here = pathlib.Path(__file__).resolve().parent
src = (here / "talk.md").read_text(encoding="utf-8")
frames = (here / "frames.json").read_text(encoding="utf-8")
excerpts = (here / "excerpts.gen.json").read_text(encoding="utf-8")
before = (here / "before.json").read_text(encoding="utf-8")
throughput = (here / "throughput.json").read_text(encoding="utf-8")
template = (here / "template.html").read_text(encoding="utf-8")

for slot in ("%%TALK%%", "%%FRAMES%%", "%%EXCERPTS%%", "%%BEFORE%%", "%%THROUGHPUT%%"):
    if slot not in template:
        sys.exit(f"template.html has no {slot} placeholder")
json.loads(frames)
json.loads(excerpts)
json.loads(before)
json.loads(throughput)

# A '---' straight after a line of text makes that line a heading (a setext underline), not a divider.
lines = src.split("\n")
for i, line in enumerate(lines[1:], 1):
    if line.strip() == "---" and lines[i - 1].strip() and not lines[i - 1].startswith("---"):
        sys.exit(f"talk.md:{i + 1}: '---' right after text; leave a blank line before it")

out = template.replace("%%TALK%%", src.replace("</script", "<\\/script"))
out = out.replace("%%FRAMES%%", frames.replace("</script", "<\\/script"))
out = out.replace("%%EXCERPTS%%", excerpts.replace("</script", "<\\/script"))
out = out.replace("%%BEFORE%%", before.replace("</script", "<\\/script"))
out = out.replace("%%THROUGHPUT%%", throughput.replace("</script", "<\\/script"))
(here / "index.html").write_text(out, encoding="utf-8")
print("wrote", here / "index.html")
