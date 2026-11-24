#!/usr/bin/env python3
"""For walls whose left lattice admits the decomposition lambda = P_L / r with u = (i, r) in L_L, report the rank of the
two leg vectors u and (P_L - i, -r) among the defect-correlation peaks of legs.py (rank 0 = strongest; i = 0 is an in-row return)."""
import json, os, subprocess, sys
from fractions import Fraction as F
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
L = json.load(open(os.path.join(HERE, 'out', 'lattice.json'))); out = {}
seen = set()
for wid, r in sorted(L.items()):
    key = (tuple(r['S1']), r['Delta'], r['s'])
    if key in seen: continue
    seen.add(key); l = r['L']; lam = F(r['lam'])
    if not l or not l.get('P'): out[wid] = 'no left lattice'; continue
    T, P, sg = l['T'], l['P'], l['sigma']; PL = P * (T // gcd(sg, T)); ru = F(PL) / lam
    us = [k * P for k in range(0, PL // P) if ru.denominator == 1 and (k * sg - int(ru)) % T == 0]
    if not us: out[wid] = dict(P_L=PL, r=str(ru), legs=None); continue
    i = us[0]; rr = int(ru)
    p = subprocess.run([sys.executable, os.path.join(HERE, 'legs.py'), wid, str(PL), str(min(PL, 40))], capture_output=True, text=True,
                       env=dict(os.environ, TOP='60')).stdout.split('\n')[1].split()
    vecs = [x.split(':')[0] for x in p]
    def rank(v): s = '(%d,%d)' % v; return vecs.index(s) if s in vecs else None
    out[wid] = dict(P_L=PL, u=(i, rr), back=(PL - i, -rr), inv_vR=str(F(i, rr)), inv_vL=str(F(PL - i, rr)),
                    rank_u=rank((i, rr)) if i else 'in-row', rank_back=rank((PL - i, -rr)), top3=vecs[:3])
    print(wid[:40].ljust(40), out[wid], flush=True)
json.dump(out, open(os.path.join(HERE, 'out', 'legs.json'), 'w'), indent=1)
