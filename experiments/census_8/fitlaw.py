#!/usr/bin/env python3
"""fitlaw.py PREFILE [GAP=40] : exact jump law of a sqrt-type wall.
Running max M of pre(a); records cluster into rounds (records < GAP rows apart). Round j starts at T_j
and lifts M to L_j. From the first round j0 after which rise L_j - L_{j-1} (=Delta) and the second
difference of T are constant to the end of the data, report t_k = T_{j0+k} = t0 + g0 k + (s/2) k(k-1),
w_k = L_{j0+k} = w0 + Delta k, checked exactly on every round; and c = Delta*sqrt(2/s) (w ~ c sqrt a)."""
import sys, json, numpy as np
p = np.fromfile(sys.argv[1], dtype=np.int32); GAP = int(sys.argv[2]) if len(sys.argv) > 2 else 40
M = np.maximum.accumulate(p); idx = np.nonzero(np.diff(M))[0] + 1
cl = [[idx[0]]]
for i, g in zip(idx[1:], np.diff(idx)):
    (cl.append([i]) if g > GAP else cl[-1].append(i))
T = np.array([c[0] for c in cl]); L = np.array([M[c[-1]] for c in cl])
rise = np.diff(L); dT = np.diff(T); d2 = np.diff(dT)
Delta, s = int(rise[-1]), int(d2[-1])
j0 = len(T) - 1
while j0 > 0 and rise[j0 - 1] == Delta and (j0 - 2 < 0 or d2[j0 - 2] == s): j0 -= 1
j0 += 1  # first round from which everything is constant
k = np.arange(len(T) - j0); t0, g0, w0 = int(T[j0]), int(T[j0 + 1] - T[j0]), int(L[j0])
ok = bool((T[j0:] == t0 + g0 * k + s * k * (k - 1) // 2).all() and (L[j0:] == w0 + Delta * k).all())
out = {"rounds": len(T), "j0": int(j0), "k_checked": int(len(k)), "t0": t0, "gap0": g0, "s": s, "Delta": Delta, "w0": w0,
       "t_k": f"{s/2:g}k^2 + {g0 - s/2:g}k + {t0}", "w_k": f"{w0} + {Delta}k", "exact": ok,
       "c": round(Delta * (2 / s) ** 0.5, 4), "gap_vs_w": f"gap_k = {s/Delta:g}*w_k + {g0 - s/Delta*w0:g}", "last_T": int(T[-1])}
print(json.dumps(out))
