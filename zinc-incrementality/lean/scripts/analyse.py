"""Reads a conformance run of the names space (`--out` of the harness; optionally a fresh dump to
take the model's verdicts from) and reports:
* where the model's resolution disagrees with the compiler's (read off the client's classfile);
* where the model's verdict disagrees with the harness's;
* the divergences (incremental differs from clean), grouped by edit and resolution change."""
import collections, json, re, sys

def slot_of(probe, name):
    toks = set(re.findall(r'[A-Za-z0-9_/$]+', ' '.join(probe)))
    toks |= {t[1:] for t in toks if t.startswith('L')}
    m = {f'a/V${name}$': 'blk', f'a/P${name}$': 'inh', f'a/X${name}$': 'expl', f'a/W${name}$': 'wild',
         f'a/q/{name}$': 'wpkg', f'a/b/{name}$': 'inner', f'a/b/package${name}$': 'pobj',
         f'a/{name}$': 'outer', 'scala/Option$': 'lib', f'a/U${name}$': 'wild', f'a/U2${name}$': 'pobj'}
    hits = [s for k, s in m.items() if k in toks]
    return '+'.join(hits) if hits else '?'

def model_res(cfg):
    b, a = cfg.split(': ', 1)[1].split(' -> ')
    return b, a

rs = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
# A fresh dump (optional) supplies the current model's verdicts, matched by base cfg and edit.
if len(sys.argv) > 2:
    fresh = {}
    for line in open(sys.argv[2]):
        b = json.loads(line)
        for e in b['edits']:
            fresh[(b['cfg'], e['cls'])] = e
    def norm(cfg):
        t = cfg.split()
        return ' '.join(t[:8] + t[9:]) if len(t) == 17 and t[8] == 'false' else cfg
    fresh = {(norm(c), e): v for (c, e), v in fresh.items()}
    for r in rs:
        e = fresh.get((norm(r['cfg']), r.get('edit')))
        if e:
            r['modelClean'] = e['modelClean']
            r['edited'] = e['cfg']
res_mis = collections.Counter()
verd_mis = collections.Counter()
div = collections.defaultdict(list)
rev = collections.Counter()
for r in rs:
    if r['verdict'] == 'base-error':
        res_mis[('base-error', r['cfg'], tuple(r['errors'][:1]))] += 1
        continue
    name = 'Option' if r['cfg'].split()[7] == 'true' else 'Foo'
    # with `exp`, the factor list has one more field before the slots
    mb, ma = model_res(r['edited'])
    rb = slot_of(r.get('baseProbe', []), name)
    ra = slot_of(r.get('cleanProbe', []), name) if r['cleanOk'] else 'error'
    mb_ = mb if not mb.startswith('error') else 'error'
    ma_ = 'error' if ma.startswith('error') or ma == 'clash' else ma
    if mb_ != rb:
        res_mis[('before', r['edit'], mb, rb)] += 1
    if ma_ != ra:
        res_mis[('after', r['edit'], ma, ra)] += 1
    ok = r['verdict'] in ('same', 'same-fail')
    if r['revert'] not in ('same', 'same-fail'):
        rev[(r['edit'], r['revert'])] += 1
    if ok != r.get('modelClean'):
        verd_mis[(r['edited'], r['verdict'], r['revert'], r['cfg'])] += 1
    if not ok:
        div[(r['edit'].split()[0] + ' ' + r['edit'].split()[-1], f'{rb} -> {ra}', r['verdict'], r['revert'])].append(r)
print(f'{len(rs)} cases')
print('\n== resolution: model vs compiler')
for k, n in sorted(res_mis.items(), key=lambda x: -x[1])[:60]:
    print(n, k)
print('\n== verdict: model vs harness', sum(verd_mis.values()))
for k, n in sorted(verd_mis.items(), key=lambda x: -x[1])[:60]:
    print(n, k)
print('\n== revert divergences (the inverse edit)', sum(rev.values()))
for k, n in sorted(rev.items(), key=lambda x: -x[1])[:20]:
    print(n, k)
print('\n== divergences', sum(len(v) for v in div.values()))
for k, v in sorted(div.items(), key=lambda x: -len(x[1])):
    fs = collections.Counter()
    for r in v:
        f = r['cfg'].split()
        fs[f'first={f[6]}'] += 1
    print(len(v), k, dict(fs), v[0]['base'], v[0]['cfg'])
