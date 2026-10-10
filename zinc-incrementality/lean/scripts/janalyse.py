"""Reads a conformance run of a Java space (`jnames` or `jsealed`; the harness's `--out`), with an
optional fresh `jconformance` dump to take the model's verdicts from, and reports where the model's
resolution disagrees with the compiler's (read off the client's classfile), where the model's
verdict or recompilation disagrees with the harness's, and the divergences by edit."""
import collections, json, re, sys

def slot_of(probe, name):
    toks = set(re.findall(r'[A-Za-z0-9_/$]+', ' '.join(probe)))
    m = {f'a/P${name}': 'inh', f'a/X${name}': 'expl', f'a/W${name}': 'wild', f'a/q/{name}': 'wpkg',
         f'a/b/{name}': 'inner', f'a/{name}': 'outer', 'java/lang/Process': 'lib'}
    hits = [s for k, s in m.items() if k in toks]
    return '+'.join(hits) if hits else '?'

def agrees(v):
    return v in ('same', 'same-fail')

runs = [json.loads(l, strict=False) for l in open(sys.argv[1])]
model = {}
if len(sys.argv) > 2:
    for line in open(sys.argv[2]):
        b = json.loads(line)
        for e in b['edits']:
            model[(b['id'], e['cfg'])] = e
res_dis, verd_dis, rc_dis, div = [], [], [], collections.Counter()
n = 0
for r in runs:
    if r['verdict'] == 'base-error':
        res_dis.append(('base-error', r['base'], r['cfg'], r['errors']))
        continue
    n += 1
    e = model.get((r['base'], r['edited']), r)
    if r['space'] == 'jnames':
        name = 'Process' if 'true' == dict(zip(['pkg', 'inh', 'expl', 'wild', 'wpkg', 'opt'], r['cfg'].split()))['opt'] else 'Foo'
        before, after = r['edited'].split(': ', 1)[1].split(' -> ')
        if slot_of(r['baseProbe'], name) != before:
            res_dis.append(('before', r['base'], r['edited'], slot_of(r['baseProbe'], name)))
        got = slot_of(r['cleanProbe'], name) if r['cleanOk'] else 'error'
        if (after.startswith('error') and got != 'error') or (not after.startswith('error') and got != after):
            res_dis.append(('after', r['base'], r['edited'], got, r['cleanErrors'][:1]))
    elif r['cleanOk']:
        res_dis.append(('clean build compiles', r['base'], r['edited']))
    if agrees(r['verdict']) != e['modelClean']:
        verd_dis.append((r['base'], r['cfg'], r['edited'], r['verdict'], e['modelClean'], r['recompiled']))
    client = any(c.endswith('Client') for c in r['recompiled'])
    if client != bool(e['modelRecompiled']) and not (r['cleanOk'] is False and not r['incErrors'] == []):
        rc_dis.append((r['base'], r['cfg'], r['edited'], r['recompiled'], e['modelRecompiled']))
    if not agrees(r['verdict']):
        div[(r['edited'], r['verdict'])] += 1
print(f"{n} cases; resolution disagreements {len(res_dis)}; verdict disagreements {len(verd_dis)}; recompilation disagreements {len(rc_dis)}; divergences {sum(div.values())}")
for x in res_dis[:15]: print('  res', x)
for x in verd_dis[:15]: print('  verdict', x)
for x in rc_dis[:15]: print('  rc', x)
for k, v in sorted(div.items(), key=lambda kv: -kv[1]): print(f"  {v:5d} {k[1]:13s} {k[0]}")
