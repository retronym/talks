"""Counts the edits of a `conformance names` dump that the model calls unclean, by family."""
import collections, json, sys

from families import family

fam = collections.Counter()
n = 0
for line in open(sys.argv[1]):
    b = json.loads(line)
    for e in b['edits']:
        n += 1
        if not e['modelClean']:
            before, after = e['cfg'].split(': ', 1)[1].split(' -> ')
            fam[family(e['cls'], before, after)] += 1
print(n, 'edits,', sum(fam.values()), 'unclean')
for k, c in sorted(fam.items()):
    print(c, k)
