#!/usr/bin/env python3
"""legs.py DUMP.bin PRE D P : defects = cells d < M(a) with r_a(d) != r_{a-P}(d). Print per row: a, M(a), #defects, min d, max d."""
import sys, numpy as np
f, D, P = sys.argv[1], int(sys.argv[3]), int(sys.argv[4])
R = np.fromfile(f, dtype=np.uint8); N = len(R) // D; R = R[:N*D].reshape(N, D)
pre = np.fromfile(sys.argv[2], dtype=np.int32)[:N]; M = np.maximum.accumulate(pre)
lo, hi = int(sys.argv[5]), int(sys.argv[6])
for a in range(max(P, lo), min(N, hi)):
    m = M[a]; df = np.nonzero(R[a, :m] != R[a-P, :m])[0]
    print(a, m, len(df), df.min() if len(df) else -1, df.max() if len(df) else -1, (df[:8].tolist() if len(df) else ''))
