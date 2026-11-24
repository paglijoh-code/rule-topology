#!/usr/bin/env python3
"""why_s1d.py N : row 5 of the partner table for wall s1-2-5-6-9 p12. Prints row 5's P columns for each shift
and for offset 2, then tests single extra P cells (5, b) added to the offset-2 base (and its mirror).
Run: nice -n 10 python3 rule_graphs/why_s1d.py 4000 > rule_graphs/why_s1d_4000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
sys.path.insert(0, os.path.join(H, "..", "census_8"))
import numpy as np, graphs, exponent
from gpatterns import mex_g
N = int(sys.argv[1]); assert graphs._load() is not None
w = [w for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl")))
     if w["tag"] == "r10:s1-2-5-6-9_g00112233041520314_p12"][0]
S1 = tuple(w["S1"]); g = np.array(mex_g(w["S2_example"], N + 10)[:N + 1])
a = np.arange(N + 1); D = a[None, :] - a[:, None]
def shifted(dl):
    if dl == 0: return g[:, None] == g[None, :]
    U = np.zeros((N + 1, N + 1), bool); U[:, dl:] = g[:, None] == g[None, :N + 1 - dl]
    U = np.triu(U, dl); return U | U.T
def offset(c): A = np.abs(D); return (A % 5 == c) & (A >= c)
def tag(P):
    r, _ = exponent.analyse(graphs._node_c(S1, np.ascontiguousarray(P), N), pmax=400, tail=min(1200, N // 4))
    return f"{r['kind']} {r['alpha']:.2f}/{r.get('n_rounds')}"
print("g[:20]", "".join(map(str, g[:20])))
for dl in range(10): print(f"row 5, delta {dl}:", [int(b) for b in np.nonzero(shifted(dl)[5, :45])[0]])
O = offset(2); print("row 5, offset2:", [int(b) for b in np.nonzero(O[5, :45])[0]])
extra = sorted(set(np.nonzero(shifted(2)[5])[0]) ^ set(np.nonzero(O[5])[0])); print("row 5 shift2 xor offset2:", [int(x) for x in extra[:20]])
for b in [x for x in extra if x < 60]:
    P = O.copy(); P[5, b] = P[b, 5] = not P[5, b]; print(f"offset2 with cell (5,{b}) flipped: {tag(P)}", flush=True)
for b in range(0, 12):
    P = np.zeros_like(O); P[5, b] = P[b, 5] = True; P |= O
    print(f"offset2 + P at (5,{b}): {tag(P)}", flush=True)
