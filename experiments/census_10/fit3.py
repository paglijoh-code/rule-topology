#!/usr/bin/env python3
"""fit3.py PREFILE [GAP=40] : exact jump law with super-rounds.
Records of the running max M of pre cluster into rounds (records < GAP rows apart): round j starts at T_j
and lifts M to L_j. Find the least q <= 12 and the earliest j0 such that, for every j >= j0,
L_{j+q} - L_j = Delta and T_{j+2q} - 2 T_{j+q} + T_j = s (same Delta, s for all residues j mod q) to the end
of the data. Then for each residue class the super-round index k gives t_k = t0 + g0 k + s k(k-1)/2 and
w_k = w0 + Delta k exactly; w ~ c sqrt(a), c = Delta sqrt(2/s) (s > 0); s = 0 means a linear wall."""
import sys, json, numpy as np
def rounds(p, GAP):
    M = np.maximum.accumulate(p); idx = np.nonzero(np.diff(M))[0] + 1
    cl = [[idx[0]]]
    for i, g in zip(idx[1:], np.diff(idx)):
        (cl.append([i]) if g > GAP else cl[-1].append(i))
    return np.array([c[0] for c in cl]), np.array([M[c[-1]] for c in cl])
def fit(T, L):
    n = len(T)
    for q in range(1, 13):
        if n < 4 * q + 4: break
        r = L[q:] - L[:-q]; d2 = T[2*q:] - 2 * T[q:-q] + T[:-2*q]
        D, s = int(r[-1]), int(d2[-1])
        j0 = len(d2)
        while j0 > 0 and r[j0 - 1] == D and d2[j0 - 1] == s: j0 -= 1
        if r[j0:].min() != D: continue  # r has q more tail entries
        if n - j0 >= 3 * q + 3 and len(d2) - j0 >= q + 2:  # at least 3 super-rounds per class checked
            return q, j0, D, s
    return None
p = np.fromfile(sys.argv[1], dtype=np.int32); GAP = int(sys.argv[2]) if len(sys.argv) > 2 else 40
T, L = rounds(p, GAP); f = fit(T, L)
out = {"file": sys.argv[1], "rounds": len(T), "N": len(p), "last_T": int(T[-1]), "max_M": int(L[-1])}
if f:
    q, j0, D, s = f; cls = []; ok = True
    for i in range(q):
        Ti, Li = T[j0 + i::q], L[j0 + i::q]; k = np.arange(len(Ti))
        t0, g0, w0 = int(Ti[0]), int(Ti[1] - Ti[0]), int(Li[0])
        ok &= bool((2 * Ti == 2 * t0 + 2 * g0 * k + s * k * (k - 1)).all() and (Li == w0 + D * k).all())
        cls.append({"t0": t0, "gap0": g0, "w0": w0, "k_checked": int(len(k)), "t_k": f"{s/2:g}k^2 + {g0 - s/2:g}k + {t0}", "w_k": f"{w0} + {D}k"})
    out.update(q=q, j0=int(j0), Delta=D, s=s, exact=ok, kind="sqrt" if s > 0 else ("linear" if s == 0 else "neg"),
               lam=(f"{s}/{D}" if D else None), c=(round(D * (2 / s) ** 0.5, 4) if s > 0 else None), classes=cls)
else: out.update(q=None, exact=False, kind="nofit")
print(json.dumps(out))
