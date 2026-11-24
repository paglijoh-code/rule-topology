#!/usr/bin/env python3
"""Row dumps of the 26 distinct walls (one per law) for the defect model. Writes prediction/out/<id>.bin (uint8 N*D) + meta json."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
WS = os.path.join(ROOT, 'census_10/out/wallscan')
walls = [json.loads(l) for l in open(os.path.join(ROOT, 'census_10/walls_exact.jsonl'))]
def wid(w): return 's' + '-'.join(map(str, w['S1'])) + '_g' + ''.join(map(str, w['g']['pattern'])) + '_p%d' % w['g']['pre']
jobs = []
for w in walls:
    c = w['classes'][0]
    t0, w0 = w['classes'][0]['t0'], w['classes'][0]['w0']
    # enough rows for ~8 super-rounds past onset
    lam = eval(w['lam']); D_ = w['Delta']
    a, ww, k = max(cc['t0'] for cc in w['classes']), max(cc['w0'] for cc in w['classes']), 0
    while k < 5:
        a += lam * ww * w['q'] + 200; ww += D_; k += 1
    N = int(a) + 500; D = int(ww) + 2500
    jobs.append((w, N, D))
out = os.path.join(HERE, 'out'); meta = {}
procs = []
for w, N, D in jobs:
    i = wid(w); f = os.path.join(out, i + '.bin')
    meta[i] = dict(tag=w['tag'], S1=w['S1'], g=w['g'], N=N, D=D, Delta=w['Delta'], q=w['q'], lam=w['lam'], s=w['s'])
    if os.path.exists(f) and os.path.getsize(f) == N * D: continue
    g = w['g']
    cmd = [WS, str(N), str(D), '400', ','.join(map(str, w['S1'])), str(g['pre']), str(g['per']), ','.join(map(str, g['pattern'])), f + '.pre']
    procs.append(subprocess.Popen(cmd, env=dict(os.environ, WS_DUMP=f), stdout=open(f + '.json', 'w')))
    if len(procs) >= 14:
        procs.pop(0).wait()
for p in procs: p.wait()
json.dump(meta, open(os.path.join(out, 'meta.json'), 'w'), indent=1)
tot = sum(m['N'] * m['D'] for m in meta.values()); print(len(meta), 'walls', tot / 1e6, 'MB')
