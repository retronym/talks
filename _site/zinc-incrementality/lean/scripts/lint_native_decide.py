"""Fails if a `theorem` or `lemma` is proved by `native_decide`: those are checks (`example`,
`check_`), not theorems (DESIGN-spec.md)."""
import glob, re, sys

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma) (\S+)(.*?)(?=^\S)',
    re.S | re.M)

bad = []
for f in sorted(glob.glob('**/*.lean', recursive=True)):
    if f.startswith('.lake/'):
        continue
    s = open(f).read()
    for m in DECL.finditer(s):
        if 'native_decide' in m.group(2):
            bad.append(f'{f}: {m.group(1)}')
print('\n'.join(bad) if bad else 'no theorem uses native_decide')
sys.exit(1 if bad else 0)
