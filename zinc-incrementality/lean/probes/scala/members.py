#!/usr/bin/env python3
"""Calibrate Scala/Members.lean (membership and overriding) against scalac and dotc.

    members.py OUT [--scala212 2.12.21] [--scala2 2.13.18] [--scala3 3.9.0]

Runs `lake exe scalaprobe OUT` (which writes OUT/srcm/qN.scala and the model's verdicts
OUT/members-<dialect>.txt), then for each compiler:

1. compiles every program in one run, in rounds: a compiler stops before refchecks when an earlier
   phase reported an error, so the programs that reported errors are recorded and dropped, and the
   rest recompiled, until a run is clean;
2. maps each error to its program (the file), its class (the definition enclosing the error's line)
   and its kind (by message);
3. for the programs that compiled, runs a `Main` that prints, for each concrete class, which
   owner's `m` ran.

Writes OUT/members-report-<dialect>.txt with every divergence grouped by shape, and prints counts.
"""
import os, re, shutil, subprocess, sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..'))

KINDS = [  # (kind, substrings of scalac's or dotc's message)
    ('illegalModifiers', ['illegal combination of modifiers']),
    ('needsOverride', ['`override` modifier required', 'needs `override` modifier', "needs `override' modifier"]),
    ('conflicting', ['inherits conflicting members']),
    ('overridesNothing', ['overrides nothing']),
    ('finalOverride', ['cannot override final member']),
    ('accidental', ["third member that's overridden by both", 'third member that is overridden by both']),
    ('needsAbstract', ['needs to be abstract']),
    ('stable', ['stable, immutable value']),
    ('weakerAccess', ['weaker access']),
    ('lazyMismatch', ['must be lazy', 'must not be lazy', 'declared lazy', 'non-lazy value']),
    ('resultType', ['incompatible type']),
]

ANSI = re.compile(r'\x1b\[[0-9;]*m')
HDR2 = re.compile(r'^(?:\[error\] )?(\S+\.scala):(\d+)(?::\d+)?: error: (.*)$')
HDR3 = re.compile(r'^-- (?:\[E\d+\] )?.*Error: (\S+\.scala):(\d+):\d+\s*$')
DEF = re.compile(r'^(?:(?:abstract|final|sealed) )*(class|trait|object) (\w+)')


def classify(msg):
    if re.search(r'private \w+ \w+ cannot override', msg):  # dotc's form of weaker access
        return 'weakerAccess'
    for kind, subs in KINDS:
        if any(s in msg for s in subs):
            return kind
    return 'other:' + msg.strip().splitlines()[0][:80] if msg.strip() else 'other'


def parse_errors(text):
    """[(file, line, message)] from scalac 2 or dotc output."""
    out, cur = [], None
    for raw in ANSI.sub('', text).splitlines():
        m2, m3 = HDR2.match(raw), HDR3.match(raw)
        if m2 or m3:
            if cur:
                out.append(cur)
            m = m2 or m3
            cur = [m.group(1), int(m.group(2)), m2.group(3) if m2 else '']
        elif cur is not None:
            line = raw.split('|', 1)[1] if raw.lstrip().startswith('|') else raw
            cur[2] += '\n' + line
    if cur:
        out.append(cur)
    return out


def enclosing_class(path, line):
    name = '?'
    with open(path) as f:
        for i, l in enumerate(f, 1):
            if i > line:
                break
            m = DEF.match(l)
            if m:
                name = m.group(2)
    return name


def scalac(version, files, dest, extra=()):
    os.makedirs(dest, exist_ok=True)
    opts = ['-O', '-Xmaxerrs', '-O', '1000000'] if not version.startswith('3') else []
    cmd = ['scala-cli', 'compile', '--server=false', '-S', version] + opts + list(extra) + files + ['-d', dest]
    r = subprocess.run(cmd, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def verdicts(out, tag, version):
    """Compile in rounds; return ({pid: set((cls, kind))}, accepted pids)."""
    src = os.path.join(out, 'srcm')
    files = sorted(os.path.join(src, f) for f in os.listdir(src) if f.endswith('.scala'))
    errs = defaultdict(set)
    rnd = 0
    while files:
        rnd += 1
        dest = os.path.join(out, f'mclasses-{tag}-{rnd}')
        rc, text = scalac(version, files, dest)
        found = parse_errors(text)
        if rc == 0:
            break
        if not found:
            sys.stderr.write(text)
            raise SystemExit(f'{version}: compilation failed without parsable errors')
        bad = set()
        for path, line, msg in found:
            pid = os.path.basename(path)[:-len('.scala')]
            errs[pid].add((enclosing_class(path, line), classify(msg)))
            bad.add(path)
        files = [f for f in files if f not in bad]
        print(f'  {version} round {rnd}: {len(bad)} programs with errors', flush=True)
    accepted = [os.path.basename(f)[:-len('.scala')] for f in files]
    return errs, accepted


def run_main(out, tag, version, accepted, news):
    """Compile the accepted programs with a Main and run it; {pid: {cls: owner}}."""
    d = os.path.join(out, f'mrun-{tag}')
    os.makedirs(d, exist_ok=True)
    calls = [f'    try println("{pid} {c} " + new {pid}.{c}().m) catch {{ case e: Throwable => println("{pid} {c} !" + e.getClass.getSimpleName) }}'
             for pid in accepted for c in news.get(pid, [])]
    # split into chunks to keep methods small
    chunks = [calls[i:i + 200] for i in range(0, len(calls), 200)]
    body = '\n'.join(f'  def run{i}(): Unit = {{\n' + '\n'.join(ch) + '\n  }' for i, ch in enumerate(chunks))
    main = 'object Main {\n' + body + '\n  def main(args: Array[String]): Unit = {\n' + \
        '\n'.join(f'    run{i}()' for i in range(len(chunks))) + '\n  }\n}\n'
    with open(os.path.join(d, 'Main.scala'), 'w') as f:
        f.write(main)
    files = [os.path.join(out, 'srcm', p + '.scala') for p in accepted] + [os.path.join(d, 'Main.scala')]
    opts = ['-O', '-Xmaxerrs', '-O', '1000000'] if not version.startswith('3') else []
    cmd = ['scala-cli', 'run', '--server=false', '-S', version] + opts + files + ['--main-class', 'Main']
    r = subprocess.run(cmd, capture_output=True, text=True)
    with open(os.path.join(d, 'log.txt'), 'w') as f:
        f.write(r.stdout + r.stderr)
    if r.returncode != 0:
        raise SystemExit(f'{version}: Main failed, see {d}/log.txt')
    ran = defaultdict(dict)
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0].startswith('q'):
            ran[parts[0]][parts[1]] = parts[2]
    return ran


def read_model(path):
    errs, runs = defaultdict(set), defaultdict(dict)
    for line in open(path):
        parts = line.rstrip('\n').split('\t')
        if len(parts) != 4:
            continue
        pid, what, cls, x = parts
        if what == 'err':
            errs[pid].add((cls, x))
        else:
            runs[pid][cls] = x
    return errs, runs


def show(errs):
    return ' '.join(sorted(f'{c}:{k}' for c, k in errs)) or 'ok'


def main():
    args = sys.argv[1:]
    out = os.path.abspath(args[0] if args else 'out')
    versions = {'2.12': '2.12.21', '2.13': '2.13.18', '3': '3.9.0'}
    for i, a in enumerate(args):
        if a == '--scala212': versions['2.12'] = args[i + 1]
        if a == '--scala2': versions['2.13'] = args[i + 1]
        if a == '--scala3': versions['3'] = args[i + 1]
    if not os.path.isdir(os.path.join(out, 'srcm')):
        subprocess.run(['lake', 'exe', 'scalaprobe', out], cwd=LEAN, check=True)
    desc = dict(l.rstrip('\n').split('\t') for l in open(os.path.join(out, 'members-index.txt')) if l.strip())
    for tag, version in versions.items():
        merrs, mruns = read_model(os.path.join(out, f'members-{tag}.txt'))
        aerrs, accepted = verdicts(out, tag, version)
        news = {pid: list(mruns.get(pid, {}).keys()) for pid in accepted if not merrs.get(pid)}
        ran = run_main(out, tag, version, [p for p in accepted if p in news], news)
        groups = defaultdict(list)
        agree = 0
        for pid in desc:
            e, a = merrs.get(pid, set()), aerrs.get(pid, set())
            if e != a:
                groups[f'errors model [{show(e)}] scalac [{show(a)}]'].append(pid)
            elif not e and ran.get(pid, {}) != mruns.get(pid, {}):
                groups[f'runs model {sorted(mruns.get(pid, {}).items())} scalac {sorted(ran.get(pid, {}).items())}'].append(pid)
            else:
                agree += 1
        print(f'scalac {version}: {agree}/{len(desc)} programs agree; {len(accepted)} accepted; {len(groups)} divergence shapes')
        with open(os.path.join(out, f'members-report-{tag}.txt'), 'w') as rep:
            rep.write(f'scalac {version}: {agree}/{len(desc)} programs agree\n\n')
            for d, pids in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                rep.write(f'{len(pids):5d}  {d}\n       e.g. ' + '; '.join(f'{p}: {desc[p]}' for p in pids[:3]) + '\n')


if __name__ == '__main__':
    main()
