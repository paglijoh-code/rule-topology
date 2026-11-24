import sys, time, numpy as np
from lib3 import chain, far_period, mismatch, plane_cover
N = int(sys.argv[1]); pairs = [tuple(tuple(map(int, s.split(","))) for s in a.split(">")) for a in sys.argv[2:]]
for sets in pairs:
    t = time.time(); T = chain(N, list(sets)); p, fr = far_period(T)
    print(sets, "N", N, "far period", p, "far mismatch %.4f" % fr, "P-density %.4f" % T.mean())
    if p is None: continue
    D = mismatch(T, p); print("  |D| =", int(D.sum()))
    planes, res, R = plane_cover(D, p)
    for f, k, c in planes: print("   plane %s.(u,v,w) in [%d,%d)  cells %d" % (f, k, k + p, c))
    print("  residue", res, "max coord of residue:", R.max(axis=0) if res else None, "%.1fs" % (time.time() - t))
