#!/usr/bin/env python3
"""References from the talks to the Lean models in retronym/jvm-lang-models.

Each talk that cites the models names the commit it was written against, in its front matter:

    **Lean model:** [retronym/jvm-lang-models](https://github.com/retronym/jvm-lang-models) at `<sha>`.

Against that commit this script checks the talk's `talk.md` and `README.md` (and any `README.md`
under the talk, which takes the talk's pin) and fails on:

* a Lean file or document of the models mentioned without a link (`Zinc/Erasure.lean`,
  `PLAN-names.md`, `BUG-MAP.md`, as the talks wrote them before the models moved, or their
  current paths);
* a Lean declaration of the models mentioned without a link (`zinc_diverges`,
  `XCompiler.round_preserves`): a name that matches exactly one declaration, or one `example`
  named by its doc comment, by a suffix of its full name, and contains `_` or `.` or is CamelCase
  with two capitals;
* a name that looks like a Lean theorem (`snake_case`, or `Name.snake_case`) and is not a
  declaration at the pinned commit: a deleted or renamed declaration, as `early_agreement` was.
  Declarations of the talk's own `lean/` (the primer, frozen copies) count as existing. Names that
  are not Lean (a tactic, Python) can be listed in `bin/lean_refs_allow.txt`;
* a link into the models at a commit other than the talk's pin.

With `--fix` it writes the links, to `https://github.com/retronym/jvm-lang-models/blob/<pin>/…`,
keeping the text as written. The models are read from a local clone: `$JVM_LANG_MODELS`, or else
`.cache/jvm-lang-models`, cloned on first use.

Usage: python3 bin/lean_refs.py [--fix]
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = 'retronym/jvm-lang-models'
URL = f'https://github.com/{REPO}'
TALKS = ['zinc-incrementality', 'zinc-lean', 'zinc-merkle', 'zinc-testing']
PIN = re.compile(r'\*\*Lean model:\*\*.*? at `([0-9a-f]{40})`')

# Documents of the Zinc model as the talks named them before the move, to their current paths.
DOCS = {
    'PLAN.md': 'docs/history/phases.md',
    'PLAN-repo.md': 'docs/history/repository-split.md',
    'PLAN-framework.md': 'packages/inc-comp/docs/framework-merge.md',
    'PLAN-track-j.md': 'packages/jvm/docs/track-j.md',
    'PLAN-track-java.md': 'packages/java/docs/track-java.md',
    'PLAN-track-s.md': 'packages/scala/docs/track-s.md',
    'PLAN-track-b.md': 'packages/mima/docs/track-b.md',
    'BUG-MAP.md': 'docs/evidence/bug-map.md',
    'BUGS-catalogue.md': 'docs/evidence/bugs.md',
    'TESTS-catalogue.md': 'docs/evidence/tests.md',
    'ROADMAP.md': 'docs/roadmap.md',
    'DESIGN-spec.md': 'docs/specification.md',
    'REVIEW-2026-10-11.md': 'docs/history/reviews/2026-10-11-morning.md',
    'REVIEW-2026-10-11-central.md': 'docs/history/reviews/2026-10-11-central.md',
}
PHASES = {'names': 10, 'inline': 11, 'java': 12, 'split': 13, 'order': 14, 'cycles': 15,
          'naming': 16, 'hash': 17, 'annotations': 18, 'pipelining': 19, 'synthetic': 20,
          'derived': 21, 'macros': 22, 'extrahash': 23, 'extensions': 24, 'companions': 25,
          'files': 26, 'imports': 27, 'sam': 28}
for t, n in PHASES.items():
    DOCS[f'PLAN-{t}.md'] = f'packages/zinc/docs/{n:02d}-{t}.md'


def models_clone():
    path = os.environ.get('JVM_LANG_MODELS') or os.path.join(ROOT, '.cache', 'jvm-lang-models')
    if not os.path.isdir(os.path.join(path, '.git')):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        subprocess.run(['git', 'clone', '-q', f'{URL}.git', path], check=True)
    return path


def git(clone, *args):
    return subprocess.run(['git', '-C', clone, *args], capture_output=True, text=True,
                          check=True).stdout


DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|nonrec|unsafe)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s:({\[]+)')
NAMED_EXAMPLE = re.compile(r'^\s*/--\s*`([A-Za-z_][A-Za-z0-9_\'.]*)`:')
NS_OPEN = re.compile(r'^\s*namespace\s+(\S+)')
NS_END = re.compile(r'^\s*end\s+(\S+)\s*$')


class Models:
    """The files and declarations of the models at one commit."""

    def __init__(self, clone, sha):
        self.sha = sha
        try:
            git(clone, 'cat-file', '-e', sha + '^{commit}')
        except subprocess.CalledProcessError:
            git(clone, 'fetch', '-q', 'origin')
        self.files = [f for f in git(clone, 'ls-tree', '-r', '--name-only', sha).split('\n') if f]
        self.fileset = set(self.files)
        self.by_base = {}
        for f in self.files:
            self.by_base.setdefault(os.path.basename(f), []).append(f)
        self.decls = {}
        for f in self.files:
            if not f.endswith('.lean'):
                continue
            ns = []
            for n, line in enumerate(git(clone, 'show', f'{sha}:{f}').split('\n'), 1):
                m = NS_OPEN.match(line)
                if m:
                    ns += m.group(1).split('.')
                    continue
                m = NS_END.match(line)
                if m:
                    k = len(m.group(1).split('.'))
                    if ns[-k:] == m.group(1).split('.'):
                        del ns[-k:]
                    continue
                m = DECL.match(line) or NAMED_EXAMPLE.match(line)
                if m:
                    # a declaration, or an `example` named by its doc comment
                    parts = ns + m.group(m.lastindex).split('.')
                    for i in range(len(parts)):
                        self.decls.setdefault('.'.join(parts[i:]), set()).add((f, n))

    def url(self, path, line=None):
        return f'{URL}/blob/{self.sha}/{path}' + (f'#L{line}' if line else '')

    def path(self, written):
        """The models' path for a file as a talk wrote it, or None."""
        w = re.sub(r'^(\.\./)*(zinc-incrementality/)?lean/', '', written)
        if w in self.fileset:
            return w
        if w in DOCS and DOCS[w] in self.fileset:
            return DOCS[w]
        base = os.path.basename(w)
        if base in DOCS:
            return DOCS[base]
        if w.endswith('.lean'):
            hits = self.by_base.get(base, [])
            if len(hits) == 1:
                return hits[0]
            # `Zinc/X.lean`, `BinCompat/X.lean`: the directory narrows a name used twice
            d = os.path.dirname(w)
            hits = [h for h in hits if d and f'/{d}/' in f'/{h}']
            if len(hits) == 1:
                return hits[0]
        return None

    def decl(self, name):
        if not ('_' in name or '.' in name or re.fullmatch(r'[A-Z][a-z0-9]*[A-Z][A-Za-z0-9]*', name)):
            return None
        hits = self.decls.get(name)
        return next(iter(hits)) if hits and len(hits) == 1 else None


LEANISH = re.compile(r"[a-z][A-Za-z0-9']*(?:_[A-Za-z0-9']+)+|[A-Z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9']*)*\.[a-z][A-Za-z0-9']*(?:_[A-Za-z0-9']+)+")
CODE = re.compile(r"`([A-Za-z0-9_./'-]+?)(?::(\d+))?`")
LINK = re.compile(r'\[[^\]]*\]\([^)]*\)')
LOCAL = re.compile(r'^(lean/(V1|V2|Primer)|\.\./)')


def local_names(talk):
    """Declarations in a talk's own `lean/` (frozen copies, the primer): they exist, unlinked."""
    names = set()
    for d, _, fs in os.walk(os.path.join(ROOT, talk, 'lean')):
        if '.lake' in d:
            continue
        for f in fs:
            if f.endswith('.lean'):
                for line in open(os.path.join(d, f), encoding='utf-8'):
                    m = DECL.match(line) or NAMED_EXAMPLE.match(line)
                    if m:
                        parts = m.group(m.lastindex).split('.')
                        names.update('.'.join(parts[i:]) for i in range(len(parts)))
    return names


def process(md, text, models, allow, fix):
    problems = []
    out = []
    fence = False
    for n, line in enumerate(text.split('\n'), 1):
        if line.lstrip().startswith('```'):
            fence = not fence
        if fence or line.lstrip().startswith('```'):
            out.append(line)
            continue
        # links into the models at another commit, or into the models' old home in this repo
        def relink(m):
            href = m.group(0)
            old = re.match(r'https://github\.com/retronym/talks/blob/[^/]+/zinc-incrementality/lean/([^)#\s]+)(#\S*)?', href)
            if old:
                p = models.path(old.group(1))
                if p:
                    problems.append(f'{md}:{n}: link into the old zinc-incrementality/lean/')
                    return models.url(p) + (old.group(2) or '')
            new = re.match(rf'{re.escape(URL)}/blob/([0-9a-f]+)/(.*)', href)
            if new and new.group(1) != models.sha:
                problems.append(f'{md}:{n}: link at {new.group(1)[:7]}, not the pin {models.sha[:7]}')
                return f'{URL}/blob/{models.sha}/{new.group(2)}'
            return href

        line2 = re.sub(r'https://github\.com/[^\s)]+', relink, line)
        spans = [m.span() for m in LINK.finditer(line2)]

        def code(m):
            if any(a <= m.start() < b for a, b in spans) or (m.start() and line2[m.start() - 1] == '['):
                return m.group(0)
            word, lineno = m.group(1), m.group(2)
            if LOCAL.match(word):
                return m.group(0)
            if re.search(r'\.(lean|md)$', word) or '/' in word:
                p = models.path(word)
                if p:
                    problems.append(f'{md}:{n}: unlinked {m.group(0)}')
                    return f'[{m.group(0)}]({models.url(p, lineno)})'
                return m.group(0)
            t = models.decl(word)
            if t:
                problems.append(f'{md}:{n}: unlinked {m.group(0)}')
                return f'[{m.group(0)}]({models.url(t[0], t[1])})'
            if LEANISH.fullmatch(word) and word not in models.decls and word not in allow:
                problems.append(f'{md}:{n}: {m.group(0)} is not a declaration at {models.sha[:7]}')
            return m.group(0)

        line2 = CODE.sub(code, line2)
        out.append(line2 if fix else line)
    return '\n'.join(out), problems


def main():
    fix = '--fix' in sys.argv
    clone = models_clone()
    allow_file = os.path.join(ROOT, 'bin', 'lean_refs_allow.txt')
    allow = set()
    if os.path.exists(allow_file):
        allow = {l.split('#')[0].strip() for l in open(allow_file) if l.split('#')[0].strip()}
    problems = []
    cache = {}
    for talk in TALKS:
        talk_md = os.path.join(ROOT, talk, 'talk.md')
        m = PIN.search(open(talk_md, encoding='utf-8').read())
        if not m:
            problems.append(f'{talk}/talk.md: no "**Lean model:** … at `<sha>`" pin')
            continue
        sha = m.group(1)
        models = cache.get(sha) or cache.setdefault(sha, Models(clone, sha))
        docs = [talk_md] + [os.path.join(d, 'README.md') for d, _, fs in os.walk(os.path.join(ROOT, talk))
                            if 'README.md' in fs and '.lake' not in d]
        talk_allow = allow | local_names(talk)
        for path in docs:
            rel = os.path.relpath(path, ROOT)
            text = open(path, encoding='utf-8').read()
            new, ps = process(rel, text, models, talk_allow, fix)
            if fix and new != text:
                open(path, 'w', encoding='utf-8').write(new)
                _, ps = process(rel, new, models, talk_allow, False)
            problems += ps
    print('\n'.join(problems) if problems else 'Lean references ok')
    sys.exit(1 if problems else 0)


if __name__ == '__main__':
    main()
