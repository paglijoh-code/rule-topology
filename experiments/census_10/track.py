#!/usr/bin/env python3
"""track.py DUMP PRE D P A0 A1 [WIN] : defect cells E_a(d) = [r_a(d) != r_{a-P}(d)], d < M(a)-10. Per row, group defects into
clusters (gap > 3); link each cluster to the nearest cluster centre in the next row within WIN cells; keep tracks >= 15 rows.
Print a histogram of track speeds (cells/row, rounded to 1/30; < 0 = toward the diagonal), weighted by track length."""
import sys, numpy as np, collections
from fractions import Fraction as F
f, pf, D, P, A0, A1 = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:7]); WIN = int(sys.argv[7]) if len(sys.argv) > 7 else 8
R = np.fromfile(f, dtype=np.uint8); N = len(R) // D; R = R[:N*D].reshape(N, D)
M = np.maximum.accumulate(np.fromfile(pf, dtype=np.int32)[:N]); A1 = min(A1, N)
def clusters(a):
    m = max(M[a] - 10, 0); d = np.nonzero(R[a, :m] != R[a - P, :m])[0]
    if not len(d): return []
    cut = np.nonzero(np.diff(d) > 3)[0] + 1
    return [float(g.mean()) for g in np.split(d, cut)]
tracks, live = [], []   # live: list of [start_a, [centres]]
for a in range(max(A0, P), A1):
    cs = clusters(a); used = set(); nl = []
    for t in live:
        last = t[1][-1]; best = None
        for i, c in enumerate(cs):
            if i in used: continue
            if abs(c - last) <= WIN and (best is None or abs(c - last) < abs(cs[best] - last)): best = i
        if best is None: tracks.append(t)
        else: used.add(best); t[1].append(cs[best]); nl.append(t)
    for i, c in enumerate(cs):
        if i not in used: nl.append([a, [c]])
    live = nl
tracks += live
h = collections.Counter()
for t in tracks:
    n = len(t[1])
    if n < 15: continue
    v = (t[1][-1] - t[1][0]) / (n - 1)
    h[F(round(v * 30), 30)] += n
tot = sum(h.values())
print([(str(v), round(float(v), 3), w) for v, w in sorted(h.items(), key=lambda x: -x[1])[:8]], "total", tot)
