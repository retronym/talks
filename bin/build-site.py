#!/usr/bin/env python3
"""Assemble the GitHub Pages site for this repo into _site/.

Each top-level directory is a talk. A talk with a Makefile is rebuilt first, and
the build must leave its committed files unchanged (pass --check to enforce that).
The talk's page is index.html, or else slides.html. Its title is the first
`# ` heading of its README.md, or else the page's <title>, or else the directory
name. The landing page lists every talk.
"""
import html
import pathlib
import re
import shutil
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parent.parent
site = root / "_site"
check = "--check" in sys.argv[1:]

ENTRY_PAGES = ("index.html", "slides.html")
SKIP_DIRS = {".git", ".github", "bin", "_site"}
SKIP_IN_TALK = shutil.ignore_patterns(".lake", ".DS_Store", ".sass-cache")


def title_of(talk: pathlib.Path, entry: pathlib.Path) -> str:
    readme = talk / "README.md"
    if readme.exists():
        for line in readme.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    m = re.search(r"<title>(.*?)</title>", entry.read_text(encoding="utf-8", errors="replace"), re.S | re.I)
    return m.group(1).strip() if m else talk.name


talks = []
for talk in sorted(p for p in root.iterdir() if p.is_dir() and p.name not in SKIP_DIRS and not p.name.startswith(".")):
    if (talk / "Makefile").exists():
        subprocess.run(["make", "-s", "-C", str(talk)], check=True)
        if check:
            diff = subprocess.run(["git", "status", "--porcelain", "--", str(talk)], cwd=root, capture_output=True, text=True, check=True)
            if diff.stdout.strip():
                sys.exit(f"{talk.name}: the committed build output is stale; run make and commit.\n{diff.stdout}")
    entry = next((talk / e for e in ENTRY_PAGES if (talk / e).exists()), None)
    if entry is None:
        continue
    talks.append((talk.name, entry.name, title_of(talk, entry)))

if site.exists():
    shutil.rmtree(site)
site.mkdir()
for name, _, _ in talks:
    shutil.copytree(root / name, site / name, ignore=SKIP_IN_TALK)

items = "\n".join(
    f'    <li><a href="{html.escape(name)}/{html.escape(entry)}">{html.escape(title)}</a></li>'
    for name, entry, title in talks
)
(site / "index.html").write_text(f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Talks</title>
<style>
  :root {{ --bg: #f6f5f1; --ink: #1d1d1f; --muted: #6b6b70; --link: #1f5fa8; }}
  @media (prefers-color-scheme: dark) {{ :root {{ --bg: #141416; --ink: #ececee; --muted: #9a9aa2; --link: #7fb2ff; }} }}
  body {{ background: var(--bg); color: var(--ink); font: 17px/1.5 system-ui, sans-serif; margin: 0; padding: 48px 16px; }}
  main {{ max-width: 720px; margin: 0 auto; }}
  h1 {{ font-size: 28px; margin: 0 0 24px; }}
  li {{ margin: 8px 0; }}
  a {{ color: var(--link); text-decoration: none; }}
  a:hover {{ text-decoration: underline; }}
  footer {{ color: var(--muted); font-size: 14px; margin-top: 32px; }}
</style>
</head>
<body>
<main>
  <h1>Talks</h1>
  <ul>
{items}
  </ul>
  <footer>Source: <a href="https://github.com/retronym/talks">retronym/talks</a></footer>
</main>
</body>
</html>
""", encoding="utf-8")
print(f"wrote {site} with {len(talks)} talks: {', '.join(n for n, _, _ in talks)}")
