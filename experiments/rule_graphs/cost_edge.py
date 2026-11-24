#!/usr/bin/env python3
"""cost_edge.py : one switch A->B that also removes exactly c from one pile (c = 0 is the plain edge).
Separates the cost from unlimited switching (switching.py cost). Run:
  nice -n 10 python3 rule_graphs/cost_edge.py 4000 rule_graphs/cost_edge4000.jsonl"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent
N, OUT = int(sys.argv[1]), sys.argv[2]
W = [json.loads(l) for l in open(os.path.join(H, '..', 'census_10', 'walls_exact.jsonl'))]
with open(OUT, 'w') as f:
    for w in [w for w in W if w['S2_example']]:
        A, B = tuple(w['S1']), tuple(w['S2_example'])
        TB = graphs.solve_graph({'B': B}, {}, N)[('B', None)] == 1
        for c in (0, 1, 2, 3, 5):
            P = np.zeros_like(TB)
            if c == 0: P = TB.copy()
            else:
                P[c:, :] |= TB[:-c, :]; P[:, c:] |= TB[:, :-c]
            T = graphs._node_c(A, P, N)
            r, _ = exponent.analyse(T, pmax=400, tail=min(1200, N // 4))
            f.write(json.dumps(dict(wall=w['tag'], c=c, kind=r['kind'], alpha=r['alpha'], n_rounds=r.get('n_rounds'))) + '\n')
