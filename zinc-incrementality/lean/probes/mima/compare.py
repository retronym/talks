import json,sys,collections
model={}
for l in open(sys.argv[1]):
    d=json.loads(l); model[d['name']]=sorted(d['problems'])
bad=collections.Counter(); n=0
for f in sys.argv[2:]:
    for l in open(f):
        d=json.loads(l); n+=1
        real=sorted(p['problem'] for p in d['problems'])
        if real!=model[d['name']]:
            bad[(tuple(model[d['name']]),tuple(real))]+=1
            print(d['name'],'model',model[d['name']],'mima',real, [p['description'] for p in d['problems']][:3])
print(n,'compared,',sum(bad.values()),'differ')
