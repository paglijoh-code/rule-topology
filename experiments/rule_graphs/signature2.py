#!/usr/bin/env python3
"""signature2.py N : shape of B's rewritten table T' in A->B->C, and wall survival by shape.
g-form: P(a,b) iff g(a)=g(b) (what a plain subtraction game gives; census_10's signature map covers only these).
matching-form: rows' P-supports pairwise equal or disjoint, i.e. P(a,b) iff class(b) = sigma(class(a)).
Run: nice -n 10 python3 rule_graphs/signature2.py 1000 > rule_graphs/signature2_1000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs
from collections import Counter
N = int(sys.argv[1])

def shape(T):
    P = T == 1; P = P | P.T
    keys = {}
    for a in range(len(P)):
        keys.setdefault(P[a].tobytes(), []).append(a)
    M = np.array([np.frombuffer(k, dtype=bool) for k in keys], dtype=np.int32)
    G = M @ M.T
    if (G - np.diag(np.diag(G))).any():
        return "other", 0
    gform = P.diagonal().all()
    fixed = sum(P[v[0], v[0]] for v in keys.values())
    return ("g-form" if gform else "matching"), len(keys)

rows = [json.loads(l) for l in open(os.path.join(H, "census4000.jsonl"))]
rows = [r for r in rows if r["type"] == "chain"]
cache = {}; cnt = Counter(); diag = Counter()
for r in rows:
    B, C = tuple(r["sets"]["B"]), tuple(r["sets"]["C"])
    if (B, C) not in cache:
        T = graphs.solve_graph({"B": B, "C": C}, {"B": ["C"]}, N)[("B", None)]
        cache[(B, C)] = shape(T)
        diag[bool((T.diagonal() == 1).any())] += 1
    cnt[(cache[(B, C)][0], r["kind"] in ("growing", "linear"))] += 1
print("N", N, "chains", len(rows), "distinct (B,C)", len(cache))
print("distinct tables with any P cell on the diagonal:", dict(diag))
print("distinct tables by shape:", dict(Counter(v[0] for v in cache.values())))
for sh in ("g-form", "matching", "other"):
    s, d = cnt[(sh, True)], cnt[(sh, False)]
    if s + d:
        print(f"  {sh:9s} chains {s + d:5d}  wall survives {s:4d} ({100 * s / (s + d):.1f}%)")
