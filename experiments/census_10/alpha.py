#!/usr/bin/env python3
"""alpha.py CENSUS.jsonl : for every growing nofit pair, growth exponent alpha from M(a) at a_stop/4, /2, 1
(log2 ratios); sqrt gives 0.5, linear 1. Print class counts and the pairs with alpha in [0.35, 0.65]."""
import sys, json, os, collections, numpy as np
H = os.path.dirname(os.path.abspath(__file__)); c = collections.Counter(); mid = []
for l in open(sys.argv[1]):
    r = json.loads(l); L = r["law"]; k = L.get("kind")
    if k == "nofit" and r["status"] in ("ok", "overflow"):
        pre = np.fromfile(os.path.join(H, r["dir"], r["name"] + ".pre"), dtype=np.int32)
        M = np.maximum.accumulate(pre); n = len(M)
        if n < 400: c["too-short"] += 1; continue
        if M[n//2] == M[-1]: c["bounded"] += 1; continue
        a1 = np.log2(max(M[n//2]-M[n//8], 1) / max(M[n//4]-M[n//16], 1)); a2 = np.log2(max(M[-1]-M[n//4], 1) / max(M[n//2]-M[n//8], 1))
        cl = "linear-ish" if min(a1, a2) > 0.85 else ("sqrt-ish" if 0.35 <= a2 <= 0.65 else "other")
        c[cl] += 1
        if cl != "linear-ish": mid.append((r["dir"].split("/")[-1], r["name"], r["status"], n, round(float(a1), 2), round(float(a2), 2)))
    else: c[(r["status"], k)] += 1
print(dict(c))
for m in mid: print(*m)
