#!/usr/bin/env python3
"""classify2c.py CENSUS.jsonl : refine fit3 'nofit' rows using the wall M(a): bounded (M(N/2)==M(end)), growing (other)."""
import sys, json, os, collections, numpy as np
H = os.path.dirname(os.path.abspath(__file__)); c = collections.Counter(); grow = []
for l in open(sys.argv[1]):
    r = json.loads(l); L = r["law"]; k = L.get("kind")
    if k == "nofit" and r["status"] in ("ok", "overflow"):
        p = os.path.join(H, r["dir"], r["name"] + ".pre"); pre = np.fromfile(p, dtype=np.int32)
        if len(pre) < 100: k = "too-short"
        else:
            M = np.maximum.accumulate(pre); n = len(M)
            k = "bounded" if M[n // 2] == M[-1] else "growing-irregular"
            if k == "growing-irregular": grow.append((r["dir"].split("/")[-1], r["name"], r["status"], n, int(M[n//2]), int(M[-1])))
    c[(r["dir"].split("/")[-1].rsplit("_", 1)[0][4:] if False else r["dir"].split("/")[-1][:6], r["status"], k)] += 1
for k, v in sorted(c.items()): print(k, v)
for g in grow: print("GROW", *g)
