#!/usr/bin/env python3
"""why_s1b.py N : wall s1-2-5-6-9 p12 against (i) shifted partner tables, (ii) pure offset tables
P iff b - a = +-c (mod 5), c = 0..4, (iii) delta 2 vs 7. Prints round times T_j and levels.
Run: nice -n 10 python3 rule_graphs/why_s1b.py 4000 > rule_graphs/why_s1b_4000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
sys.path.insert(0, os.path.join(H, "..", "census_8"))
import numpy as np, graphs, exponent
from gpatterns import mex_g
N = int(sys.argv[1]); assert graphs._load() is not None
w = [w for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl")))
     if w["tag"] == "r10:s1-2-5-6-9_g00112233041520314_p12"][0]
S1 = tuple(w["S1"]); g = np.array(mex_g(w["S2_example"], N + 10)[:N + 1])
def shifted(dl):
    if dl == 0: return g[:, None] == g[None, :]
    U = np.zeros((N + 1, N + 1), bool); U[:, dl:] = g[:, None] == g[None, :N + 1 - dl]
    U = np.triu(U, dl); return U | U.T
a = np.arange(N + 1); D = a[None, :] - a[:, None]
def offset(c):                      # P iff |b - a| = c (mod 5) and |b - a| >= c
    A = np.abs(D); return (A % 5 == c) & (A >= c)
def show(name, P):
    r, M = exponent.analyse(graphs._node_c(S1, np.ascontiguousarray(P), N), pmax=400, tail=min(1200, N // 4))
    print(f"{name}: {r['kind']} a={r['alpha']:.2f} rounds={r.get('n_rounds')} bfit={r.get('alpha_bfit')}")
    for k in ("T_j", "L_j", "round_times", "levels"):
        if k in r: print(f"   {k} {list(r[k])[:14]}")
    return r
for dl in (0, 1, 2, 7): show(f"shift {dl}", shifted(dl))
for c in range(5): show(f"offset {c} mod 5", offset(c))
def strip(c, K):                    # offset table, but cells with |b - a| < K copied from the shift-c table
    P = offset(c % 5).copy(); m = np.abs(D) < K; P[m] = shifted(c)[m]; return P
for c in (1, 2): 
    for K in (0, 3, 6, 11, 21): show(f"offset {c}, strip |b-a|<{K} from shift {c}", strip(c, K))
def small(c, K):                    # offset table, but cells with min(a,b) < K copied from the shift-c table
    P = offset(c % 5).copy(); m = np.minimum(a[:, None], a[None, :]) < K; P[m] = shifted(c)[m]; return P
for K in (12, 30): show(f"offset 2, min(a,b)<{K} from shift 2", small(2, K))
P2, P7 = shifted(2), shifted(7); d = np.argwhere(P2 != P7)
print("shift 2 vs 7 target cells differing:", len(d), "max offset |b-a|:", int(np.abs(d[:, 1] - d[:, 0]).max()) if len(d) else 0)
