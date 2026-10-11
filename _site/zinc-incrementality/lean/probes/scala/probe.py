#!/usr/bin/env python3
"""Calibrate Scala/Lower.lean against scalac.

    probe.py OUT [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

Runs `lake exe scalaprobe OUT` (sources and the model's classfiles), compiles OUT/src with scalac
2.12, 2.13 and 3 via scala-cli, reads the classfiles, and diffs them against the model. Writes
OUT/report-<dialect>.txt with every divergence grouped by shape, and prints the agreement counts.

The comparison: class header (interface/abstract/final, superclass, interfaces), fields and
methods by name and descriptor with access (public/private), static, final, abstract and
ACC_BRIDGE, and, for methods whose body the model synthesizes, the invoke/getstatic instructions
on classes outside java/ and scala/ (for a constructor or static initialiser, only `$init$` calls). Package prefixes
are stripped.
"""
import os, re, struct, subprocess, sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..'))

# --- classfile reading ----------------------------------------------------------------------

def opcode_len(code, pc):
    op = code[pc]
    if op == 0xaa:  # tableswitch
        p = (pc + 4) & ~3
        lo, hi = struct.unpack('>ii', code[p + 4:p + 12])
        return p + 12 + 4 * (hi - lo + 1) - pc
    if op == 0xab:  # lookupswitch
        p = (pc + 4) & ~3
        n, = struct.unpack('>i', code[p + 4:p + 8])
        return p + 8 + 8 * n - pc
    if op == 0xc4:  # wide
        return 6 if code[pc + 1] == 0x84 else 4
    if op in (0x10, 0x12, 0x15, 0x16, 0x17, 0x18, 0x19, 0x36, 0x37, 0x38, 0x39, 0x3a, 0xa9, 0xbc):
        return 2
    if op in (0x11, 0x13, 0x14, 0x84, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xbb, 0xbd, 0xc0, 0xc1,
              0xc6, 0xc7) or 0x99 <= op <= 0xa8:
        return 3
    if op in (0xb9, 0xba, 0xc8, 0xc9):
        return 5
    if op == 0xc5:
        return 4
    return 1

OPS = {0xb2: 'getstatic', 0xb6: 'invokevirtual', 0xb7: 'invokespecial', 0xb8: 'invokestatic',
       0xb9: 'invokeinterface'}

def read_class(path):
    b = open(path, 'rb').read()
    pos = 10
    n, = struct.unpack('>H', b[8:10])
    cp = [None] * n
    i = 1
    while i < n:
        tag = b[pos]
        if tag == 1:
            ln, = struct.unpack('>H', b[pos + 1:pos + 3])
            cp[i] = ('utf8', b[pos + 3:pos + 3 + ln].decode('utf-8', 'replace'))
            pos += 3 + ln
        elif tag in (3, 4):
            pos += 5
        elif tag in (5, 6):
            pos += 9; i += 1
        elif tag in (7, 8, 16, 19, 20):
            cp[i] = (tag, struct.unpack('>H', b[pos + 1:pos + 3])[0]); pos += 3
        elif tag in (9, 10, 11, 12, 17, 18):
            cp[i] = (tag,) + struct.unpack('>HH', b[pos + 1:pos + 5]); pos += 5
        elif tag == 15:
            pos += 4
        else:
            raise ValueError(f'{path}: tag {tag}')
        i += 1
    utf = lambda k: cp[k][1]
    cls = lambda k: utf(cp[k][1])
    def ref(k):
        _, c, nt = cp[k]
        _, nn, dd = cp[nt]
        return cls(c), utf(nn), utf(dd)
    acc, this, sup, ni = struct.unpack('>HHHH', b[pos:pos + 8]); pos += 8
    ifaces = [cls(struct.unpack('>H', b[pos + 2 * j:pos + 2 * j + 2])[0]) for j in range(ni)]
    pos += 2 * ni
    def members():
        nonlocal pos
        cnt, = struct.unpack('>H', b[pos:pos + 2]); pos += 2
        out = []
        for _ in range(cnt):
            a, nn, dd, na = struct.unpack('>HHHH', b[pos:pos + 8]); pos += 8
            code = None
            for _ in range(na):
                an, al = struct.unpack('>HI', b[pos:pos + 6])
                if utf(an) == 'Code':
                    cl, = struct.unpack('>I', b[pos + 10:pos + 14])
                    code = b[pos + 14:pos + 14 + cl]
                pos += 6 + al
            calls = []
            if code is not None:
                pc = 0
                while pc < len(code):
                    op = code[pc]
                    if op in OPS:
                        k, = struct.unpack('>H', code[pc + 1:pc + 3])
                        calls.append((OPS[op],) + ref(k))
                    pc += opcode_len(code, pc)
            out.append((a, utf(nn), utf(dd), calls))
        return out
    fields = members()
    methods = members()
    inner = []
    na, = struct.unpack('>H', b[pos:pos + 2]); pos += 2
    for _ in range(na):
        an, al = struct.unpack('>HI', b[pos:pos + 6])
        if utf(an) == 'InnerClasses':
            n, = struct.unpack('>H', b[pos + 6:pos + 8])
            for j in range(n):
                ii, oi, ni, fl = struct.unpack('>HHHH', b[pos + 8 + 8 * j:pos + 16 + 8 * j])
                inner.append((cls(ii), cls(oi) if oi else None, utf(ni) if ni else None, fl))
        pos += 6 + al
    return dict(acc=acc, name=cls(this), sup=cls(sup) if sup else None, ifaces=ifaces,
                fields=fields, methods=methods, inner=inner)

# --- canonical lines --------------------------------------------------------------------------

PKG = re.compile(r'p\d+[/$]')
strip = lambda s: PKG.sub('', s)

def flags(ws):
    return ' '.join(w for w, on in ws if on)

def dump(pid, c):
    name = strip(c['name'])
    out = {}
    a = c['acc']
    out[(pid, name, 'class')] = (flags([('interface', a & 0x200), ('abstract', a & 0x400), ('final', a & 0x10)]),
                                 f"super={strip(c['sup'])};ifaces={','.join(strip(i) for i in c['ifaces'])}")
    for i, o, n, fl in c['inner']:
        if i.startswith('java/') or i.startswith('scala/'):
            continue
        out[(pid, name, f'inner {strip(i)}')] = (flags([('public', fl & 1), ('private', fl & 2), ('protected', fl & 4),
            ('static', fl & 8), ('final', fl & 0x10), ('interface', fl & 0x200), ('abstract', fl & 0x400)]),
            f"outer={strip(o or '')};name={n or ''}")
    for a, n, d, _ in c['fields']:
        out[(pid, name, f'field {n} {strip(d)}')] = (flags([('private' if a & 2 else 'public', True),
            ('static', a & 8), ('final', a & 0x10)]), None)
    for a, n, d, calls in c['methods']:
        cs = [(op, strip(o), nn, strip(dd)) for op, o, nn, dd in calls
              if not (o.startswith('java/') or o.startswith('scala/') or o.startswith('['))]
        if n in ('<init>', '<clinit>'):
            cs = [x for x in cs if x[2] == '$init$']
        out[(pid, name, f'method {strip(n)} {strip(d)}')] = (flags([('private' if a & 2 else 'public', True),
            ('static', a & 8), ('final', a & 0x10), ('abstract', a & 0x400), ('bridge', a & 0x40)]),
            '; '.join(f'{op} {o}.{strip(nn)}:{dd}' for op, o, nn, dd in cs))
    return out

def read_expected(path):
    """The model's lines, and the classes it models only partly."""
    out, partly = {}, set()
    for line in open(path):
        parts = line.rstrip('\n').split('\t')
        if len(parts) == 3 and parts[2] == 'partly':
            partly.add((parts[0], parts[1]))
        if len(parts) < 4:
            continue
        pid, cls, key, fl = parts[:4]
        if key == 'class' or key.startswith('inner'):
            out[(pid, cls, key)] = (fl, parts[4])
        elif key.startswith('field'):
            out[(pid, cls, key)] = (fl, None)
        else:
            out[(pid, cls, key)] = (fl, None if parts[4] == '*' else parts[4])
    return out, partly

# --- driver -----------------------------------------------------------------------------------

def scalac(version, inputs, dest, cp=None):
    if os.path.isdir(dest) and os.listdir(dest):
        return
    os.makedirs(dest, exist_ok=True)
    cmd = ['scala-cli', 'compile', '--server=false', '-S', version] + inputs + ['-d', dest]
    if cp:
        cmd += ['--extra-jars', cp]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout + r.stderr)
        raise SystemExit(f'scalac {version} failed')

def compile_all(out, version, tag):
    """One run over src (and src3 for Scala 3); for sep, a run over the libraries, then one over
    the clients against them."""
    three = tag == '3'
    srcs = [os.path.join(out, 'src')] + ([os.path.join(out, 'src3')] if three else [])
    main = os.path.join(out, f'classes-{tag}')
    scalac(version, srcs, main)
    dests = [main]
    for sep in ['sep'] + (['sep3'] if three else []):
        lib, client = os.path.join(out, f'classes-{tag}-{sep}-lib'), os.path.join(out, f'classes-{tag}-{sep}-client')
        scalac(version, [os.path.join(out, sep, 'lib')], lib)
        scalac(version, [os.path.join(out, sep, 'client')], client, cp=lib)
        dests += [lib, client]
    return dests

def actual(dests):
    out = {}
    for dest in dests:
        out.update(actual1(dest))
    return out

def actual1(dest):
    out = {}
    for pdir in sorted(os.listdir(dest)):
        full = os.path.join(dest, pdir)
        if not (os.path.isdir(full) and re.fullmatch(r'p\d+', pdir)):
            continue
        for f in os.listdir(full):
            if f.endswith('.class'):
                out.update(dump(pdir, read_class(os.path.join(full, f))))
    return out

def shape(key, what):
    """A divergence with the program id dropped, for grouping."""
    return f'{key[1]}\t{key[2]}\t{what}'

def diff(exp, partly, act):
    by_prog = defaultdict(list)
    pids = {k[0] for k in exp}
    for k in sorted(set(exp) | {k for k in act if k[0] in pids}):
        e, a = exp.get(k), act.get(k)
        if e is None and (k[0], k[1]) in partly:
            continue
        if e is None:
            by_prog[k[0]].append(shape(k, f'only scalac: {a[0]}'))
        elif a is None:
            by_prog[k[0]].append(shape(k, f'only model: {e[0]}'))
        else:
            if e[0] != a[0]:
                by_prog[k[0]].append(shape(k, f'flags model [{e[0]}] scalac [{a[0]}]'))
            if e[1] is not None and e[1] != a[1]:
                by_prog[k[0]].append(shape(k, f'body model [{e[1]}] scalac [{a[1]}]'))
    return by_prog

def main():
    args = sys.argv[1:]
    out = os.path.abspath(args[0] if args else 'out')
    # run tag -> (scalac version, the model's dialect)
    versions = {'2.12': ('2.12.21', '2.12'), '2.13': ('2.13.18', '2.13'), '3': ('3.9.0', '3')}
    for i, a in enumerate(args):
        if a == '--scala212': versions['2.12'] = (args[i + 1], '2.12')
        if a == '--scala2': versions['2.13'] = (args[i + 1], '2.13')
        if a == '--scala3': versions['3'] = (args[i + 1], '3')
    subprocess.run(['lake', 'exe', 'scalaprobe', out], cwd=LEAN, check=True)
    fam = dict(l.split('\t') for l in open(os.path.join(out, 'index.txt')).read().split('\n') if l)
    for tag, (version, dialect) in versions.items():
        dest = compile_all(out, version, tag)
        exp, partly = read_expected(os.path.join(out, f'expected-{dialect}.txt'))
        act = actual(dest)
        by_prog = diff(exp, partly, act)
        pids = {k[0] for k in exp}
        groups = defaultdict(list)
        for pid, ds in by_prog.items():
            for d in ds:
                groups[(fam[pid], d)].append(pid)
        famcount = defaultdict(int)
        for pid in pids:
            famcount[fam[pid]] += 1
        badfam = defaultdict(int)
        for pid in by_prog:
            badfam[fam[pid]] += 1
        summary = ', '.join(f'{f} {famcount[f] - badfam[f]}/{famcount[f]}' for f in sorted(famcount))
        print(f'scalac {version}: {len(pids) - len(by_prog)}/{len(pids)} programs agree ({summary}); '
              f'{len(groups)} divergence shapes')
        with open(os.path.join(out, f'report-{tag}.txt'), 'w') as rep:
            rep.write(f'scalac {version}: {len(pids) - len(by_prog)}/{len(pids)} programs agree ({summary})\n\n')
            for (f, d), pids in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                rep.write(f'{len(pids):5d}  {f}\t{d}\te.g. {" ".join(pids[:4])}\n')

if __name__ == '__main__':
    main()
