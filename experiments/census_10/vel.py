#!/usr/bin/env python3
"""vel.py DUMP PRE D P TAU A0 A1 : defect mask E_a(d) = [r_a(d) != r_{a-P}(d)] for d < M(a)-20 (drop the wall edge).
Score(s) = sum_a sum_d E_a(d) E_{a+TAU}(d+s), normalised by the static... prints top shifts s -> velocity s/TAU (cells/row; <0 = toward diagonal)."""
import sys, numpy as np
f, pre_f, D, P, TAU, A0, A1 = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:8])
R = np.fromfile(f, dtype=np.uint8); N = len(R) // D; R = R[:N*D].reshape(N, D).astype(np.int8)
M = np.maximum.accumulate(np.fromfile(pre_f, dtype=np.int32)[:N])
A1 = min(A1, N - TAU)
E = np.zeros((N, D), np.int8)
for a in range(max(P, A0), A1 + TAU):
    m = max(M[a] - 20, 0); E[a, :m] = R[a, :m] != R[a - P, :m]
S = 4 * TAU + 50; sc = {}
for s in range(-S, S + 1):
    lo, hi = max(0, -s), min(D, D - s)
    sc[s] = int((E[A0:A1, lo:hi] & E[A0 + TAU:A1 + TAU, lo + s:hi + s]).sum())
base = np.median(list(sc.values()))
top = sorted(sc, key=lambda s: -sc[s])[:12]
print("median", base, [(s, round(s / TAU, 3), sc[s]) for s in sorted(top)])
