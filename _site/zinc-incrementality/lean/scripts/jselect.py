"""Selects bases from a `jconformance names` dump, greedily, until every signature (the edit, the
model's resolution before and after, the client's package, name and `implements`) has an edit; keeps
every edit of a chosen base."""
import json, sys

src, dst = sys.argv[1], sys.argv[2]
bases = [json.loads(line) for line in open(src)]

def sig(b, e):
    f = b['factors']
    return (e['cfg'], f['pkg'], f['opt'], f['inh'])

sigs = [{sig(b, e) for e in b['edits']} for b in bases]
uncovered = set().union(*sigs)
total = len(uncovered)
chosen = []
while uncovered:
    i = max(range(len(bases)), key=lambda i: len(sigs[i] & uncovered))
    chosen.append(i)
    uncovered -= sigs[i]
with open(dst, 'w') as out:
    for i in sorted(chosen):
        out.write(json.dumps(bases[i]) + '\n')
print(f"{total} signatures, {len(chosen)} bases, {sum(len(bases[i]['edits']) for i in chosen)} edits", file=sys.stderr)
