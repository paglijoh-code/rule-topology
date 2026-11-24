#!/usr/bin/env python3
"""why_s3_big.py N : wall s3-4-9-10 (p0, B={1,2,3,4}) in the chain with C={3,7} at large N; and where T' has P cells.
Run: nice -n 10 python3 rule_graphs/why_s3_big.py 8000 > rule_graphs/why_s3_8000.txt"""
import os, sys
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent
N = int(sys.argv[1]); A, B, C = (3, 4, 9, 10), (1, 2, 3, 4), (3, 7)
T = graphs.solve_graph({"B": B, "C": C}, {"B": ["C"]}, N)[("B", None)]
P = T == 1
a, b = np.nonzero(np.triu(P))
d = b - a
print("T' P cells by offset b-a mod 5:", np.bincount(d % 5, minlength=5).tolist())
for k in range(0, 30):
    rows = a[d == k]
    if len(rows):
        print(f"  offset {k}: {len(rows)} P cells, rows mod 5 {np.bincount(rows % 5, minlength=5).tolist()}, first rows {rows[:6].tolist()}")
TA = graphs._node_c(A, np.ascontiguousarray(P), N)
del T, P
r, M = exponent.analyse(TA, pmax=400, tail=min(1200, N // 4))
Tr, Lr = exponent.rounds(M)
print("A->B->C(3,7):", r["kind"], "alpha", r["alpha"], "range", r.get("lo"), r.get("hi"), "bfit", r.get("alpha_bfit"),
      "rounds", len(Tr), "M_end", int(M[-1]))
print("  T_j", Tr.tolist()); print("  L_j", Lr.tolist())
