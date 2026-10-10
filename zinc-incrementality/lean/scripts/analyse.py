"""Reads a conformance run of the names space (`--out` of the harness; optionally a fresh dump to
take the model's verdicts from) and reports:
* where the model's resolution disagrees with the compiler's (read off the client's classfile);
* where the model's verdict disagrees with the harness's;
* where the classes the model recompiles beyond the edited files (the client, the bystanders
  `User`, `Near`, `Mid`) differ from Zinc's, and the cost: the client recompiled though not
  necessary, and the bystanders recompiled;
* the divergences (incremental differs from clean), grouped by edit and resolution change."""
import collections, json, re, sys

from families import family, givens_family

GIVENS = {'gBlk': 'blk', 'gInh': 'inh', 'gWild': 'wild', 'gInner': 'inner', 'gPobj': 'pobj',
          'gOuter': 'outer', 'gComp': 'comp'}

def slot_of(probe, name):
    toks = set(re.findall(r'[A-Za-z0-9_/$]+', ' '.join(probe)))
    toks |= {t[1:] for t in toks if t.startswith('L')}
    if name is None:
        hits = [s for k, s in GIVENS.items() if k in toks]
        # a client that extends P holds P's given as a member, whatever it resolved to
        if len(hits) > 1 and 'inh' in hits:
            hits.remove('inh')
        return '+'.join(hits) if hits else '?'
    m = {f'a/V${name}$': 'blk', f'a/P${name}$': 'inh', f'a/X${name}$': 'expl', f'a/W${name}$': 'wild',
         f'a/q/{name}$': 'wpkg', f'a/b/{name}$': 'inner', f'a/b/package${name}$': 'pobj',
         f'a/{name}$': 'outer', 'scala/Option$': 'lib', f'a/U${name}$': 'wild', f'a/U2${name}$': 'pobj',
         f'a/PT${name}$': 'pobj', f'a/WT${name}$': 'wild'}
    hits = [s for k, s in m.items() if k in toks]
    return '+'.join(hits) if hits else '?'

def model_res(cfg):
    b, a = cfg.split(': ', 1)[1].split(' -> ')
    return b, a

rs = [json.loads(l, strict=False) for l in open(sys.argv[1]) if l.strip()]
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
            for k in ('modelRecompiled', 'modelNecessary', 'modelFamily'):
                if k in e:
                    r[k] = e[k]
BYSTANDERS = {'c.User': 'User', 'a.b.Near': 'Near', 'a.Mid': 'Mid'}

def harness_recompiled(r):
    """The classes the harness saw recompiled, among those the model predicts: the client's file
    (`Client`, with `First` or `Last`) and the bystanders."""
    out = set()
    for c in r['recompiled']:
        if c.split('.')[-1] in ('Client', 'First', 'Last'):
            out.add('Client')
        elif c in BYSTANDERS:
            out.add(BYSTANDERS[c])
    return out

rec_mis = collections.Counter()
cost = collections.Counter()
res_mis = collections.Counter()
verd_mis = collections.Counter()
div = collections.defaultdict(list)
rev = collections.Counter()
for r in rs:
    if r['verdict'] == 'base-error':
        res_mis[('base-error', r['cfg'], tuple(r['errors'][:1]))] += 1
        continue
    name = None if r['space'] == 'givens' else 'Option' if r['cfg'].split()[7] == 'true' else 'Foo'
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
    # a failed incremental build reports nothing recompiled
    if 'modelRecompiled' in r and not r['incErrors']:
        model = set(r['modelRecompiled'])
        zinc = harness_recompiled(r)
        if model != zinc:
            rec_mis[(r['edited'], tuple(sorted(model)), tuple(sorted(zinc)))] += 1
        cost['edits'] += 1
        if 'Client' in zinc and not r.get('modelNecessary', True):
            cost['client, not necessary'] += 1
        for b in zinc - {'Client'}:
            cost[b] += 1
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
print('\n== recompiled (client, bystanders): model vs harness', sum(rec_mis.values()))
for k, n in sorted(rec_mis.items(), key=lambda x: -x[1])[:40]:
    print(n, k)
print('\n== cost (harness)', dict(cost))
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

fam = collections.Counter()
for (e, res, v, rv), xs in div.items():
    b, a = res.split(' -> ')
    for r in xs:
        mb, ma = model_res(r['edited'])
        fam[r.get('modelFamily') or (givens_family if r['space'] == 'givens' else family)(r['edit'], mb, ma)] += 1
print('\n== divergences by family')
for k, n in sorted(fam.items()):
    print(n, k)
