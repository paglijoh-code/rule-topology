#!/usr/bin/env python3
"""why_chain.py : for A->B->C chains, does the wall survive exactly when the push to C leaves B's table unchanged?
Reads census4000.jsonl (chain rows), recomputes B's table with and without C at N.
Run: nice -n 10 python3 rule_graphs/why_chain.py 4000 > rule_graphs/why_chain4000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs
from collections import Counter
N = int(sys.argv[1])
rows = [json.loads(l) for l in open(os.path.join(H, 'census4000.jsonl'))]
rows = [r for r in rows if r['type'] == 'chain']
plainB = {}
cnt = Counter(); ex = []
for r in rows:
    S = {k: tuple(v) for k, v in r['sets'].items()}
    if S['B'] not in plainB:
        plainB[S['B']] = graphs.solve_graph({'B': S['B']}, {}, N)[('B', None)]
    Bc = graphs.solve_graph({'B': S['B'], 'C': S['C']}, {'B': ['C']}, N)[('B', None)]
    d = Bc != plainB[S['B']]
    same = not d.any()
    # first row where B's table changes (the C push only matters from there on)
    first = int(np.nonzero(d.any(1))[0][0]) if not same else -1
    surv = r['kind'] in ('growing', 'linear')
    cnt[(surv, same)] += 1
    if surv and not same and len(ex) < 15: ex.append((r['id'], r['kind'], r['alpha'], first, int(d.sum())))
print('N', N, 'chains', len(rows))
for (s, m), c in sorted(cnt.items()): print(f"wall survives={s}  B table unchanged={m}: {c}")
print('survivors where B changed (id, kind, alpha, first changed row of B, cells changed):')
for e in ex: print(' ', e)
