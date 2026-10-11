"""Fails if a `theorem` is proved by `native_decide`: those are checks (`example`, `check_`), not
theorems (DESIGN-spec.md)."""
import glob, re, sys

bad = []
for f in sorted(glob.glob('Zinc/*.lean') + glob.glob('ZincNames/*.lean') + glob.glob('*.lean')):
    s = open(f).read()
    for m in re.finditer(r'^theorem (\S+)(.*?)(?=^\S)', s, re.S | re.M):
        if 'native_decide' in m.group(2):
            bad.append(f'{f}: {m.group(1)}')
print('\n'.join(bad) if bad else 'no theorem uses native_decide')
sys.exit(1 if bad else 0)
