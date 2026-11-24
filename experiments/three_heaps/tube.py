"""three_heaps/tube.py — radius of the irregular region around the main diagonal.  For slabs s = a+b+c in [s0, s0+30) with s <= N
(whole slab inside the cube), r = distance of a rare-block corner from the line a=b=c; reports the 90th/99th percentile of r
and the rare fraction inside radius 10.  Growth of r with s: bounded = tube, ~s = cone, ~s^q (0<q<1) = curved wall."""
import sys, json, numpy as np
from sector import rare_map
S1 = tuple(json.loads(sys.argv[1])); S2 = tuple(json.loads(sys.argv[2])); N = int(sys.argv[3])
rare, ch = rare_map(S1, S2, N)
idx = np.argwhere(rare).astype(np.int64); s = idx.sum(1); r = np.sqrt(np.maximum((idx ** 2).sum(1) - s ** 2 / 3, 0))
res = []
for s0 in range(60, N - 29, 30):
    m = (s >= s0) & (s < s0 + 30)
    if m.sum() < 50: res.append((s0, None)); continue
    res.append((s0, round(float(np.percentile(r[m], 90)), 1), round(float(np.percentile(r[m], 99)), 1), int(m.sum())))
print(json.dumps(dict(S1=S1, S2=S2, N=N, slabs=res)))
