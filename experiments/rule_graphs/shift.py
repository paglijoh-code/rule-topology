#!/usr/bin/env python3
"""shift.py N : does translating the wall partner's P set by a constant keep the wall?
For each of the 28 walls (A, B = S2_example, g = mex sequence of B), target P_delta(a,b) iff g(a) = g(b - delta) for
b >= a + delta (and symmetrically), delta = 0..9; delta 0 is the plain edge. Start-mode table of A, census settings.
Run: nice -n 10 python3 rule_graphs/shift.py 4000 > rule_graphs/shift4000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
sys.path.insert(0, os.path.join(H, "..", "census_8"))
import numpy as np, graphs, exponent
from gpatterns import mex_g
from collections import Counter
N = int(sys.argv[1]); assert graphs._load() is not None, "C backend needed"
walls = [w for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl"))) if w["S2_example"]]
cnt = Counter(); out = []
for w in walls:
    g = np.array(mex_g(w["S2_example"], N + 10)[:N + 1])
    row = []
    for dl in range(10):
        P = np.zeros((N + 1, N + 1), bool)
        if dl == 0:
            P = g[:, None] == g[None, :]
        else:
            U = np.zeros((N + 1, N + 1), bool)
            U[:, dl:] = g[:, None] == g[None, :N + 1 - dl]       # g(a) = g(b - delta)
            U = np.triu(U, dl)
            P = U | U.T
        r, M = exponent.analyse(graphs._node_c(tuple(w["S1"]), np.ascontiguousarray(P), N), pmax=400, tail=min(1200, N // 4))
        k = r["kind"]; a = r["alpha"]; nr = r.get("n_rounds", 0)
        tag = "sqrt" if k == "growing" and 0.4 <= a <= 0.6 and nr >= 6 else k
        cnt[(dl, tag)] += 1
        row.append(f"{tag}:{a:.2f}/{nr}")
    out.append((w["tag"], row))
    print(w["tag"], " ".join(row), flush=True)
print("by delta (sqrt = growing, alpha 0.4-0.6, >= 6 rounds):")
for dl in range(10):
    print(f"  delta {dl}: " + ", ".join(f"{t} {c}" for (d, t), c in sorted(cnt.items()) if d == dl))
