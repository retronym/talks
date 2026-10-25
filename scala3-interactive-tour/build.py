#!/usr/bin/env python3
"""Inline talk.md into template.html, producing index.html.

Rendering (markdown, KaTeX math, Mermaid diagrams, chunking into cards) happens
in the browser, so this step only embeds the source. The result is one
self-contained page that also works from file://.
"""
import pathlib
import sys

here = pathlib.Path(__file__).resolve().parent
src = (here / "talk.md").read_text(encoding="utf-8")
template = (here / "template.html").read_text(encoding="utf-8")

if "%%TALK%%" not in template:
    sys.exit("template.html has no %%TALK%% placeholder")

embedded = src.replace("</script", "<\\/script")
(here / "index.html").write_text(template.replace("%%TALK%%", embedded), encoding="utf-8")
print("wrote", here / "index.html")
