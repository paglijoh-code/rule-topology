#!/usr/bin/env python3
"""why_s1c.py N : which small-pile cells of the partner table carry wall s1-2-5-6-9 p12?
Base = pure offset-2 table (bounded). Copy cells with min(a,b) < K (or a single row r) from the shift-delta
table and analyse. Also: does adding the shift-delta small-pile corner to EVERY offset base restore the wall?
Run: nice -n 10 python3 rule_graphs/why_s1c.py 4000 > rule_graphs/why_s1c_4000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
sys.path.insert(0, os.path.join(H, "..", "census_8"))
import numpy as np, graphs, exponent
from gpatterns import mex_g
N = int(sys.argv[1]); assert graphs._load() is not None
w = [w for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl")))
     if w["tag"] == "r10:s1-2-5-6-9_g00112233041520314_p12"][0]
S1 = tuple(w["S1"]); g = np.array(mex_g(w["S2_example"], N + 10)[:N + 1])
a = np.arange(N + 1); D = a[None, :] - a[:, None]; MN = np.minimum(a[:, None], a[None, :])
def shifted(dl):
    if dl == 0: return g[:, None] == g[None, :]
    U = np.zeros((N + 1, N + 1), bool); U[:, dl:] = g[:, None] == g[None, :N + 1 - dl]
    U = np.triu(U, dl); return U | U.T
def offset(c): A = np.abs(D); return (A % 5 == c) & (A >= c)
def tag(P):
    r, _ = exponent.analyse(graphs._node_c(S1, np.ascontiguousarray(P), N), pmax=400, tail=min(1200, N // 4))
    return f"{r['kind']} {r['alpha']:.2f}/{r.get('n_rounds')}"
S2 = shifted(2)
for K in (1, 2, 3, 4, 6, 8, 10, 12):
    P = offset(2).copy(); m = MN < K; P[m] = S2[m]; print(f"offset2 + shift2 cells min(a,b)<{K}: {tag(P)}", flush=True)
for r0 in range(12):
    P = offset(2).copy(); m = MN == r0; P[m] = S2[m]; print(f"offset2 + shift2 row/col {r0} only: {tag(P)}", flush=True)
print("row 0 of shift tables (P columns b < 40):")
for dl in range(10): print(f"  delta {dl}:", [int(b) for b in np.nonzero(shifted(dl)[0, :40])[0]])
print("row 0 of offset2:", [int(b) for b in np.nonzero(offset(2)[0, :40])[0]])
# minimal extra cells: N-row / P-cells at small piles in the no-push (all-N) table
for K in (2, 12):
    P = np.zeros((N + 1, N + 1), bool); m = MN < K; P[m] = S2[m]; print(f"all-N + shift2 cells min(a,b)<{K}: {tag(P)}", flush=True)
