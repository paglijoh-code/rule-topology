"""three_heaps/cone.py — boundary of the irregular region of a pair: for slices c, smallest a whose row (in chamber a<=b<=c)
has rare-block density > 0.2 over a window of 8 rows; reports a_min/c to test a cone (planes through 0) vs a curved wall."""
import sys, json, numpy as np
from sector import rare_map
S1 = tuple(json.loads(sys.argv[1])); S2 = tuple(json.loads(sys.argv[2])); N = int(sys.argv[3])
rare, ch = rare_map(S1, S2, N); M = rare.shape[0]; out = []
for c in range(60, M, 20):
    dens = np.array([rare[a:a + 8, :, c][ch[a:a + 8, :, c]].mean() if ch[a:a + 8, :, c].any() else 0 for a in range(c + 1)])
    hit = np.nonzero(dens > 0.2)[0]
    out.append((c, int(hit[0]) if len(hit) else None))
print(S1, S2, N, [(c, a, round(a / c, 3) if a is not None else None) for c, a in out])
