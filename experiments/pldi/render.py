#!/usr/bin/env python3
"""Render process medians, 95% percentile bootstrap CIs, CSV, EDN and TeX.
Only Python's standard library is needed. Independent unit: whole JVM.
"""
import collections, csv, hashlib, json, math, pathlib, random, statistics, sys
out=pathlib.Path(sys.argv[1])
manifest=json.loads((out/'manifest.json').read_text())
expected=manifest['protocol']['runs']
if expected<10 or manifest.get('incomplete'):
    raise SystemExit('refusing to render incomplete confirmatory evidence')
groups=collections.defaultdict(list)
for file in sorted(out.glob('run-*.csv')):
    block=int(file.name.split('-')[1])
    for row in csv.DictReader(file.open()):
        key=(row['rq'],row['workload'],row['mode'],int(row['size']))
        groups[key].append((block,float(row['ns']),float(row['bytes'])))
rng=random.Random(162028)
def interval(xs, statistic=statistics.median):
    n=len(xs)
    samples=sorted(statistic(rng.choices(xs,k=n)) for _ in range(10000))
    return statistic(xs), samples[249],samples[9749]
def edn(x):
    if isinstance(x,dict): return '{'+' '.join(':'+k+' '+edn(v) for k,v in x.items())+'}'
    if isinstance(x,(list,tuple)): return '['+' '.join(map(edn,x))+']'
    if isinstance(x,str): return json.dumps(x)
    if x is None:return 'nil'
    if isinstance(x,bool):return str(x).lower()
    return str(x)
summary=[]
for key,values in sorted(groups.items()):
    if len(values)!=expected or len(set(x[0] for x in values))!=expected:
        raise SystemExit(f'incomplete or duplicate process units: {key}: {len(values)}')
    times=interval([x[1] for x in values])
    measured_allocation = not (key[1].endswith('-compile') or key[1] in ['first-correct','recovery'])
    allocs=interval([x[2] for x in values]) if measured_allocation else (None,None,None)
    summary.append(dict(zip(['rq','workload','mode','size'],key),processes=len(values),
                        ns=times[0],ns_low=times[1],ns_high=times[2],
                        bytes=allocs[0],bytes_low=allocs[1],bytes_high=allocs[2]))
fields=list(summary[0])
with (out/'summary.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(summary)
(out/'summary.edn').write_text(edn(summary)+'\n')
per_unit=[]
for r in summary:
    if r['rq']=='rq2' and r['size']:
        unit=dict(r)
        for field in ['ns','ns_low','ns_high','bytes','bytes_low','bytes_high']:
            unit[field]=r[field]/r['size']
        unit['unit']='particle-observation' if r['workload']=='smc' else 'update'
        per_unit.append(unit)
with (out/'authority-per-unit.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(per_unit[0]));w.writeheader();w.writerows(per_unit)
(out/'authority-per-unit.edn').write_text(edn(per_unit)+'\n')
# Ratios resample paired repetition blocks and recompute the ratio of medians.
ratios=[]
for key,values in sorted(groups.items()):
    rq,workload,mode,size=key
    if mode!='compiled' or rq!='rq1' or workload.endswith('-compile'):continue
    for other in ['t0','clojure','java']:
        other_values=groups[(rq,workload,other,size)]
        pairs=[(x[1],y[1]) for x,y in zip(sorted(values),sorted(other_values))]
        def ratio(ps):return statistics.median([p[0] for p in ps])/statistics.median([p[1] for p in ps])
        mid,lo,hi=interval(pairs,ratio)
        ratios.append({'workload':workload,'size':size,'ratio':'compiled/'+other,'estimate':mid,'low':lo,'high':hi})
with (out/'ratios.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(ratios[0]));w.writeheader();w.writerows(ratios)
(out/'ratios.edn').write_text(edn(ratios)+'\n')
def cell(mid,lo,hi,scale=1):
    if mid is None:return 'n/a'
    return f'{mid/scale:.3g} [{lo/scale:.3g}, {hi/scale:.3g}]'
# Every paper RQ gets its own importable table fragment. The correctness table
# is emitted by summarize.clj, which understands the raw EDN records.
for rq in ['rq1','rq2','rq3','rq4']:
    records=[r for r in summary if r['rq']==rq]
    lines=['\\begin{tabular}{llrrr}','\\toprule Workload & Mode & Size & $\\mu$s/call [95\\% CI] & B/call [95\\% CI] \\\\','\\midrule']
    for r in records:
        lines.append(f"{r['workload']} & {r['mode']} & {r['size']} & "+
                     cell(r['ns'],r['ns_low'],r['ns_high'],1000)+' & '+
                     cell(r['bytes'],r['bytes_low'],r['bytes_high'])+' \\\\')
    lines+=['\\bottomrule','\\end{tabular}']
    (out/f'{rq}.tex').write_text('\n'.join(lines)+'\n')
# Compact comparison matrix for the paper; complete long-form rows remain
# available separately for allocation/compilation and both measured sizes.
(out/'rq1-all-estimates.tex').write_text((out/'rq1.tex').read_text())
by_key={(r['rq'],r['workload'],r['mode'],r['size']):r for r in summary}
matrix=[r'\begin{tabular}{lrllll}',
        r'\toprule Workload & Size & T0 & Compiled & Clojure & Java \\', r'\midrule']
for label in ['numeric','collections','closures','tail-effects','calls','hof-pipeline','hof-mapv','smc']:
    size=384 if label=='smc' else 2000
    cells=[]
    for mode in ['t0','compiled','clojure','java']:
        r=by_key['rq1',label,mode,size]
        cells.append(cell(r['ns'],r['ns_low'],r['ns_high'],1000))
    matrix.append(label+' & '+str(size)+' & '+' & '.join(cells)+r' \\')
matrix+=[r'\bottomrule',r'\end{tabular}']
(out/'rq1.tex').write_text('\n'.join(matrix)+'\n')
# Process-cluster event quantiles: resample complete process event series.
events=collections.defaultdict(lambda:collections.defaultdict(list))
for r in csv.DictReader((out/'events.csv').open()):
    events[(r['kind'],int(r['size']))][r['process']].append(float(r['ns']))
def quantile(xs,p):
    xs=sorted(xs);return xs[min(len(xs)-1,math.ceil(p*len(xs))-1)]
event_summary=[]
for (kind,size),processes in sorted(events.items()):
    blocks=list(processes.values())
    if len(blocks)!=expected:raise SystemExit('missing event processes')
    for p in [0.5,0.95,0.99]:
        def q(bs):return quantile([x for b in bs for x in b],p)
        mid,lo,hi=interval(blocks,q)
        event_summary.append({'kind':kind,'size':size,'quantile':p,'ns':mid,'low':lo,'high':hi})
with (out/'events-summary.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(event_summary[0]));w.writeheader();w.writerows(event_summary)
(out/'events-summary.edn').write_text(edn(event_summary)+'\n')
md=['| RQ | Workload | Mode | Size | µs/call [95% CI] | B/call [95% CI] |',
    '|---|---|---|---:|---:|---:|']
for r in summary:
    md.append(f"| {r['rq']} | {r['workload']} | {r['mode']} | {r['size']} | "+
              cell(r['ns'],r['ns_low'],r['ns_high'],1000)+' | '+cell(r['bytes'],r['bytes_low'],r['bytes_high'])+' |')
(out/'tables.md').write_text('\n'.join(md)+'\n')
counts=list(csv.DictReader((out/'correctness.csv').open()))
rq5=['\\begin{tabular}{lr}', '\\toprule Case & Count \\\\', '\\midrule']
rq5 += [r['metric']+' & '+r['count']+' \\\\' for r in counts]
rq5 += ['\\bottomrule','\\end{tabular}']
(out/'rq5.tex').write_text('\n'.join(rq5)+'\n')
root=pathlib.Path(__file__).resolve().parents[2]
(out/'analysis-manifest.json').write_text(json.dumps({
    'note':'Measurement worker hashes and frozen collector revision are in manifest.json; these hashes record post-collection table and supplementary-validation scripts.',
    'sha256': {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted((root/'experiments/pldi').glob('*'))
               if p.suffix in ['.py','.clj']}},indent=2))
print(f'{len(summary)} estimates from {expected} independent JVMs/configuration; tables in {out}')
