"""three_heaps/tube2.py — radial profile of irregularity around the main diagonal.  Slab s = a+b+c in [s0, s0+20), s <= N;
for radius bins of width 4 (distance from a=b=c), rare-block density among chamber corners (a<=b<=c).
r* = outer edge of the last bin, scanning out from r = 0, whose density is > 0.3 (the tube edge)."""
import sys, json, numpy as np
from sector import rare_map
S1 = tuple(json.loads(sys.argv[1])); S2 = tuple(json.loads(sys.argv[2])); N = int(sys.argv[3])
rare, ch = rare_map(S1, S2, N)
idx = np.argwhere(ch).astype(np.int64); s = idx.sum(1)
keep = s <= N; idx = idx[keep]; s = s[keep]; rv = rare[tuple(idx.T)]
r = np.sqrt(np.maximum((idx ** 2).sum(1) - s ** 2 / 3, 0)); rb = (r // 4).astype(int)
out = []
for s0 in range(40, N - 19, 20):
    m = (s >= s0) & (s < s0 + 20)
    tot = np.bincount(rb[m]); hit = np.bincount(rb[m], weights=rv[m], minlength=len(tot))
    dens = np.where(tot > 0, hit / np.maximum(tot, 1), 0)
    rstar = 0
    for i, d in enumerate(dens):
        if d > 0.3: rstar = 4 * (i + 1)
        elif i * 4 > rstar + 12: break
    out.append((s0, rstar, [round(float(x), 2) for x in dens[:16]]))
print(json.dumps(dict(S1=S1, S2=S2, N=N, prof=out)))
