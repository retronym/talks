"""Reads a conformance run of the inline or opaque space (`--out` of the harness; optionally a fresh
dump, `lake exe conformance inline|opaque [mode]`, to take the model's verdicts from) and reports:
* where the model's verdict (clean or not) disagrees with the harness's;
* where the model's recompiled classes differ from the harness's;
* the divergences, grouped by the factors that tell the families apart."""
import collections, json, sys

rs = [json.loads(l, strict=False) for l in open(sys.argv[1]) if l.strip()]
if len(sys.argv) > 2:
    fresh = {}
    for line in open(sys.argv[2]):
        b = json.loads(line)
        for e in b['edits']:
            fresh[e['cfg']] = e
    for r in rs:
        if r['verdict'] != 'base-error':
            e = fresh[r['edited']]
            r['modelClean'], r['modelRecompiled'] = e['modelClean'], e['modelRecompiled']

ok = lambda r: r['verdict'] in ('same', 'same-fail')

def pickling(r):
    """Only mirror classes (`Client.class`, not `Client$.class`) of recompiled objects differ: dotc
    pickles a prefix differently when the class is compiled apart from what it references (shared
    `ThisType` of the package vs its `TermRef`), so the TASTy UUID in the mirror's attribute
    differs. Not Zinc's: the incremental build compiled the class, separately."""
    names = [d.split()[0].split('/')[-1] for d in r['diff']]
    return bool(names) and all(not n.endswith('$.class') and n[:-6] in r['recompiled'] for n in names)
cases = [r for r in rs if r['verdict'] != 'base-error']
print(f"{len(cases)} cases, {len(rs) - len(cases)} base errors, "
      f"{sum(not ok(r) for r in cases)} divergent, {sum(r['revert'] not in ('same', 'same-fail') for r in cases)} revert divergent")
for r in rs:
    if r['verdict'] == 'base-error':
        print('  base error', r['layout'], r['cfg'], r['errors'][:1])

art = [r for r in cases if not ok(r) and pickling(r)]
print(f"{len(art)} divergent only in the mirror's TASTy UUID (pickling, joint vs separate)")
verdict = [r for r in cases if r['modelClean'] != (ok(r) or pickling(r))]
print(f"model vs harness verdict (pickling counted as same): {len(verdict)} disagree")
for r in verdict[:20]:
    print('  ', r['layout'], r['edited'], r['verdict'], 'model clean' if r['modelClean'] else 'model unclean', r['diff'][:2])

rec = [r for r in cases if sorted(r['modelRecompiled']) != sorted(r['recompiled'])]
print(f"model vs harness recompiled: {len(rec)} differ")
by = collections.Counter((r['layout'], tuple(sorted(r['modelRecompiled'])), tuple(r['recompiled'])) for r in rec)
for k, n in by.most_common(20):
    print('  ', n, k)
for r in rec[:10]:
    print('  e.g.', r['layout'], r['edited'], 'model', sorted(r['modelRecompiled']), 'harness', r['recompiled'])

fam = collections.Counter()
for r in cases:
    if not ok(r) and not pickling(r):
        cfg = r['edited'].split(': ', 1)[1].split()
        key = (r['layout'], r['space'], cfg[-1] if r['space'] == 'inline' else cfg[-2], tuple(sorted({d.split()[0].split('/')[-1] for d in r['diff']})))
        fam[key] += 1
print('divergences by layout, space, ref/use, stale classfiles:')
for k, n in sorted(fam.items()):
    print('  ', n, k)
