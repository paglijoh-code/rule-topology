#!/usr/bin/env python3
"""why_s1e.py N : row 5 of the partner table, split into far-field residue and near-diagonal cells.
Base offset-2 table; row/col 5 replaced by: far field b >= 12 at b = 4 (mod 5) (the shift-2/7 residue), plus chosen
near cells. Run: nice -n 10 python3 rule_graphs/why_s1e.py 4000 > rule_graphs/why_s1e_4000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent
N = int(sys.argv[1]); assert graphs._load() is not None
S1 = (1, 2, 5, 6, 9)
a = np.arange(N + 1); D = a[None, :] - a[:, None]
def offset(c): A = np.abs(D); return (A % 5 == c) & (A >= c)
def tag(P):
    r, _ = exponent.analyse(graphs._node_c(S1, np.ascontiguousarray(P), N), pmax=400, tail=min(1200, N // 4))
    return f"{r['kind']} {r['alpha']:.2f}/{r.get('n_rounds')}"
def with_row5(near, far_res=4, far_from=12, base=2):
    P = offset(base).copy(); P[5, :] = False; P[:, 5] = False
    cols = [b for b in range(far_from, N + 1) if b % 5 == far_res] + list(near)
    for b in cols: P[5, b] = P[b, 5] = True
    return P
cases = {"far only": [], "far + 2,3,7 (shift 2)": [2, 3, 7], "far + 2": [2], "far + 3": [3], "far + 7": [7],
         "far + 2,3": [2, 3], "far + 2,7": [2, 7], "far + 3,7": [3, 7]}
for name, near in cases.items(): print(f"offset2, row 5 = {name}: {tag(with_row5(near))}", flush=True)
print(f"offset2, row 5 = its own offset-2 cells but far residue 4 from 9: {tag(with_row5([3, 7], far_from=9))}")
for base in (0, 1, 3, 4):
    res = (base + 2 + 5) % 5   # row 5 two residues off, as in the shifted tables
    print(f"offset{base}, row 5 far residue {res}: {tag(with_row5([], far_res=res, base=base))}", flush=True)
