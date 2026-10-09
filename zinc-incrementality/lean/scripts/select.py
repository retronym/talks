"""Selects bases from a `conformance names` dump, greedily, until every signature (the edit, the
model's resolution before and after, the client's package clause, name, `extends`, block import,
and `first` where a wildcard import makes it matter) has an edit; keeps every edit of a chosen
base, since a base build costs more than an edit."""
import json, sys

src, dst = sys.argv[1], sys.argv[2]
# `narrow`: leave the name, `extends` and the block import out of the signature (the model's
# resolution before and after, in the edit's cfg, already shows when they bind)
narrow = len(sys.argv) > 3 and sys.argv[3] == 'narrow'
bases = [json.loads(line) for line in open(src)]

def sig(b, e):
    f = b['factors']
    first = f['first'] if f['wild'] == 'true' else '-'
    if narrow:
        return (e['cfg'], first, f['pkg'], f.get('exp'))
    return (e['cfg'], first, f['pkg'], f['opt'], f['inh'], f['blk'], f.get('exp'))

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
