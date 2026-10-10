#!/usr/bin/env python3
"""Calibrate Java/Lower.lean against javac.

    probe.py OUT [--jdk 17=/path/to/jdk17 ...]

Runs `lake exe javaprobe OUT` (sources and the model's classfiles), compiles OUT/src with javac at
each release (`--release N`, with that release's own javac), reads the classfiles, and diffs them
against the model. Writes OUT/report-<release>.txt with every divergence grouped by shape, and
prints the agreement counts. JDKs default to $JAVA<N>_HOME, then ~/.sdkman/candidates/java/<N>*.

The comparison: class header (public/interface/abstract/final/enum, superclass, interfaces,
PermittedSubclasses, the Record attribute's components), fields (access, static, final, synthetic,
enum, ConstantValue) and methods (access, static, final, abstract, bridge, synthetic) by name and
descriptor, every method's getstatic and invoke instructions on classes outside java/ and
arrays, and the int and String constants it pushes (where folded constants show up). Package prefixes are stripped.
"""
import glob, os, re, struct, subprocess, sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..'))

def opcode_len(code, pc):
    op = code[pc]
    if op == 0xaa:
        p = (pc + 4) & ~3
        lo, hi = struct.unpack('>ii', code[p + 4:p + 12])
        return p + 12 + 4 * (hi - lo + 1) - pc
    if op == 0xab:
        p = (pc + 4) & ~3
        n, = struct.unpack('>i', code[p + 4:p + 8])
        return p + 8 + 8 * n - pc
    if op == 0xc4:
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
        elif tag == 3:
            cp[i] = ('int', struct.unpack('>i', b[pos + 1:pos + 5])[0]); pos += 5
        elif tag == 4:
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
    def const(k):
        e = cp[k]
        if e[0] == 'int':
            return f'int {e[1]}'
        if e[0] == 8:
            return f'String {utf(e[1])}'
        return '?'
    acc, this, sup, ni = struct.unpack('>HHHH', b[pos:pos + 8]); pos += 8
    ifaces = [cls(struct.unpack('>H', b[pos + 2 * j:pos + 2 * j + 2])[0]) for j in range(ni)]
    pos += 2 * ni
    def members():
        nonlocal pos
        cnt, = struct.unpack('>H', b[pos:pos + 2]); pos += 2
        out = []
        for _ in range(cnt):
            a, nn, dd, na = struct.unpack('>HHHH', b[pos:pos + 8]); pos += 8
            code, cv = None, None
            for _ in range(na):
                an, al = struct.unpack('>HI', b[pos:pos + 6])
                if utf(an) == 'Code':
                    cl, = struct.unpack('>I', b[pos + 10:pos + 14])
                    code = b[pos + 14:pos + 14 + cl]
                elif utf(an) == 'ConstantValue':
                    cv = const(struct.unpack('>H', b[pos + 6:pos + 8])[0])
                pos += 6 + al
            calls, pushes = [], []
            if code is not None:
                pc = 0
                while pc < len(code):
                    op = code[pc]
                    if op in OPS:
                        k, = struct.unpack('>H', code[pc + 1:pc + 3])
                        calls.append((OPS[op],) + ref(k))
                    elif 0x02 <= op <= 0x08:
                        pushes.append(f'int {op - 3}')
                    elif op == 0x10:
                        pushes.append(f'int {struct.unpack(">b", code[pc + 1:pc + 2])[0]}')
                    elif op == 0x11:
                        pushes.append(f'int {struct.unpack(">h", code[pc + 1:pc + 3])[0]}')
                    elif op in (0x12, 0x13):
                        k = code[pc + 1] if op == 0x12 else struct.unpack('>H', code[pc + 1:pc + 3])[0]
                        if cp[k][0] in ('int', 8):
                            pushes.append(const(k))
                    pc += opcode_len(code, pc)
            out.append((a, utf(nn), utf(dd), (calls, pushes), cv))
        return out
    fields = members()
    methods = members()
    permits, record = [], None
    na, = struct.unpack('>H', b[pos:pos + 2]); pos += 2
    for _ in range(na):
        an, al = struct.unpack('>HI', b[pos:pos + 6])
        body = b[pos + 6:pos + 6 + al]
        if utf(an) == 'PermittedSubclasses':
            k, = struct.unpack('>H', body[:2])
            permits = [cls(struct.unpack('>H', body[2 + 2 * j:4 + 2 * j])[0]) for j in range(k)]
        elif utf(an) == 'Record':
            k, = struct.unpack('>H', body[:2])
            p, record = 2, []
            for _ in range(k):
                nn, dd, nat = struct.unpack('>HHH', body[p:p + 6]); p += 6
                for _ in range(nat):
                    _, l2 = struct.unpack('>HI', body[p:p + 6]); p += 6 + l2
                record.append(f'{utf(nn)}:{utf(dd)}')
        pos += 6 + al
    return dict(acc=acc, name=cls(this), sup=cls(sup) if sup else None, ifaces=ifaces,
                fields=fields, methods=methods, permits=permits, record=record)

PKG = re.compile(r'p\d+/')
strip = lambda s: PKG.sub('', s)

def flags(ws):
    return ' '.join(w for w, on in ws if on)

def access(a):
    return 'public' if a & 1 else 'private' if a & 2 else 'protected' if a & 4 else 'package'

def dump(pid, c):
    name = strip(c['name'])
    out = {}
    a = c['acc']
    head = f"super={strip(c['sup'])};ifaces={','.join(strip(i) for i in c['ifaces'])};permits={','.join(strip(p) for p in c['permits'])}"
    if c['record'] is not None:
        head += ';record=' + ','.join(strip(r) for r in c['record'])
    out[(pid, name, 'class')] = (flags([('public', a & 1), ('interface', a & 0x200), ('abstract', a & 0x400),
                                       ('final', a & 0x10), ('enum', a & 0x4000)]), head)
    for a, n, d, _, cv in c['fields']:
        out[(pid, name, f'field {n} {strip(d)}')] = (flags([(access(a), True), ('static', a & 8), ('final', a & 0x10),
            ('synthetic', a & 0x1000), ('enum', a & 0x4000)]), cv or '-')
    for a, n, d, (calls, pushes), _ in c['methods']:
        cs = [(op, strip(o), nn, strip(dd)) for op, o, nn, dd in calls
              if not (o.startswith('java/') or o.startswith('['))]
        out[(pid, name, f'method {n} {strip(d)}')] = (flags([(access(a), True), ('static', a & 8), ('final', a & 0x10),
            ('abstract', a & 0x400), ('bridge', a & 0x40), ('synthetic', a & 0x1000)]),
            '; '.join(f'{op} {o}.{nn}:{dd}' for op, o, nn, dd in cs) +
            (' | ' + ', '.join(pushes) if pushes else ''))
    return out

def read_expected(path):
    out = {}
    for line in open(path):
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 4:
            continue
        pid, cls, key, fl = parts[:4]
        out[(pid, cls, key)] = (fl, parts[4] if len(parts) > 4 else '')
    return out

def jdk_home(rel, overrides):
    if rel in overrides:
        return overrides[rel]
    env = os.environ.get(f'JAVA{rel}_HOME')
    if env:
        return env
    hits = sorted(glob.glob(os.path.expanduser(f'~/.sdkman/candidates/java/{rel}.*')))
    return hits[0] if hits else None

def compile_all(out, rel, home):
    dest = os.path.join(out, f'classes-{rel}')
    if os.path.isdir(dest) and os.listdir(dest):
        return dest
    os.makedirs(dest, exist_ok=True)
    srcs = sorted(glob.glob(os.path.join(out, 'src', 'p*', '*.java')))
    argfile = os.path.join(out, f'sources-{rel}.txt')
    with open(argfile, 'w') as f:
        f.write('\n'.join(srcs))
    r = subprocess.run([os.path.join(home, 'bin', 'javac'), '--release', rel, '-d', dest, '@' + argfile],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout + r.stderr)
        raise SystemExit(f'javac {rel} failed')
    return dest

def actual(dest):
    out = {}
    for pdir in sorted(os.listdir(dest)):
        full = os.path.join(dest, pdir)
        if not (os.path.isdir(full) and re.fullmatch(r'p\d+', pdir)):
            continue
        for f in os.listdir(full):
            if f.endswith('.class'):
                out.update(dump(pdir, read_class(os.path.join(full, f))))
    return out

def main():
    args = sys.argv[1:]
    out = os.path.abspath(args[0] if args else 'out')
    overrides = {}
    for i, a in enumerate(args):
        if a == '--jdk':
            k, v = args[i + 1].split('=', 1)
            overrides[k] = v
    subprocess.run(['lake', 'exe', 'javaprobe', out], cwd=LEAN, check=True)
    fam = dict(l.split('\t') for l in open(os.path.join(out, 'index.txt')).read().split('\n') if l)
    exp = read_expected(os.path.join(out, 'expected.txt'))
    pids = {k[0] for k in exp}
    for rel in ['17', '21', '25']:
        home = jdk_home(rel, overrides)
        if not home:
            print(f'javac {rel}: no JDK found, skipped')
            continue
        act = actual(compile_all(out, rel, home))
        by_prog = defaultdict(list)
        for k in sorted(set(exp) | {k for k in act if k[0] in pids}):
            e, a = exp.get(k), act.get(k)
            shape = f'{k[1]}\t{k[2]}'
            if e is None:
                by_prog[k[0]].append(f'{shape}\tonly javac: {a[0]} {a[1]}')
            elif a is None:
                by_prog[k[0]].append(f'{shape}\tonly model: {e[0]} {e[1]}')
            else:
                if e[0] != a[0]:
                    by_prog[k[0]].append(f'{shape}\tflags model [{e[0]}] javac [{a[0]}]')
                if e[1] != a[1]:
                    by_prog[k[0]].append(f'{shape}\tdetail model [{e[1]}] javac [{a[1]}]')
        groups = defaultdict(list)
        for pid, ds in by_prog.items():
            for d in ds:
                groups[(fam[pid], d)].append(pid)
        famcount, badfam = defaultdict(int), defaultdict(int)
        for pid in pids:
            famcount[fam[pid]] += 1
        for pid in by_prog:
            badfam[fam[pid]] += 1
        summary = ', '.join(f'{f} {famcount[f] - badfam[f]}/{famcount[f]}' for f in sorted(famcount))
        line = f'javac {rel}: {len(pids) - len(by_prog)}/{len(pids)} programs agree ({summary}); {len(groups)} divergence shapes'
        print(line)
        with open(os.path.join(out, f'report-{rel}.txt'), 'w') as rep:
            rep.write(line + '\n\n')
            for (f, d), ps in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                rep.write(f'{len(ps):5d}  {f}\t{d}\te.g. {" ".join(ps[:4])}\n')

if __name__ == '__main__':
    main()
