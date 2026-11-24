#!/usr/bin/env python3
"""fit2.py PREFILE [GAP=40] : rounds of the running max M of pre; prints T_j, L_j, rise, dT, d2 tail."""
import sys, numpy as np
p = np.fromfile(sys.argv[1], dtype=np.int32); GAP = int(sys.argv[2]) if len(sys.argv) > 2 else 40
M = np.maximum.accumulate(p); idx = np.nonzero(np.diff(M))[0] + 1
cl = [[idx[0]]]
for i, g in zip(idx[1:], np.diff(idx)):
    (cl.append([i]) if g > GAP else cl[-1].append(i))
T = np.array([c[0] for c in cl]); L = np.array([M[c[-1]] for c in cl])
print("n", len(T), "N", len(p)); print("T", T[-14:].tolist()); print("L", L[-14:].tolist())
print("rise", np.diff(L)[-13:].tolist()); dT = np.diff(T); print("dT", dT[-13:].tolist()); print("d2", np.diff(dT)[-12:].tolist())
