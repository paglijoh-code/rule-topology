#!/usr/bin/env python3
"""why_s1.py N : why does wall r10:s1-2-5-6-9_g00112233041520314_p12 ignore shifts of its partner's P set?
Compares A's start-mode table across delta = 0..9, and the plain, budget-1 and budget-2 tables.
Run: nice -n 10 python3 rule_graphs/why_s1.py 2000 > rule_graphs/why_s1_2000.txt"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
sys.path.insert(0, os.path.join(H, "..", "census_8"))
import numpy as np, graphs, exponent
from gpatterns import mex_g
N = int(sys.argv[1]); assert graphs._load() is not None
w = [w for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl")))
     if w["tag"] == "r10:s1-2-5-6-9_g00112233041520314_p12"][0]
S1 = tuple(w["S1"]); B = w["S2_example"]; print("S1", S1, "B", B)
g = np.array(mex_g(B, N + 10)[:N + 1]); print("g[:40]", "".join(map(str, g[:40])))
def target(dl):
    if dl == 0: return g[:, None] == g[None, :]
    U = np.zeros((N + 1, N + 1), bool); U[:, dl:] = g[:, None] == g[None, :N + 1 - dl]
    U = np.triu(U, dl); return U | U.T
def tab(P): return graphs._node_c(S1, np.ascontiguousarray(P), N)
none = tab(np.zeros((N + 1, N + 1), bool))          # push target all N: push never wins
T = {dl: tab(target(dl)) for dl in range(10)}
for dl in range(10):
    r, _ = exponent.analyse(T[dl], pmax=400, tail=min(1200, N // 4))
    print(f"delta {dl}: {r['kind']} a={r['alpha']:.2f} rounds={r.get('n_rounds')}  "
          f"cells != delta0: {int((T[dl] != T[0]).sum())}  != no-push: {int((T[dl] != none).sum())}  "
          f"push used (P-target cells A lands on as P): {int(((T[dl]==1) & target(dl)).sum()) if False else '-'}")
r, _ = exponent.analyse(none, pmax=400, tail=min(1200, N // 4))
print("no-push-wins (target all N):", r["kind"], r["alpha"], r.get("n_rounds"))
# where do the tables differ?
for dl in (1, 3, 7):
    d = np.argwhere(T[dl] != T[0]); 
    if len(d): off = d[:, 1] - d[:, 0]; print(f"delta {dl} vs 0: {len(d)} diff cells, offset range {off.min()}..{off.max()}, first {d[:5].tolist()}")
