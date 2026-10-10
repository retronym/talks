"""Runs `scripts/Axioms.lean` and fails unless every core theorem depends only on the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`)."""
import re, subprocess, sys

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
out = subprocess.run(['lake', 'env', 'lean', 'scripts/Axioms.lean'], capture_output=True, text=True)
text = out.stdout + out.stderr
if out.returncode != 0:
    print(text)
    sys.exit(1)
expected = len(re.findall(r'^#print axioms', open('scripts/Axioms.lean').read(), re.M))
seen = 0
bad = []
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
    seen += 1
    axioms = {a.strip() for a in (m.group(2) or '').split(',') if a.strip()}
    if not axioms <= ALLOWED:
        bad.append((m.group(1), sorted(axioms - ALLOWED)))
print(f'{seen} theorems checked')
if seen != expected or bad:
    print(text)
    for name, extra in bad:
        print(f'{name}: {extra}')
    sys.exit(1)
