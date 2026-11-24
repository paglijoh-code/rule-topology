#!/usr/bin/env python3
"""probe.py ID SIDE : for P = 0..PM, best shifts sigma (by agreement) of R_a(d) vs R_{a-P}(d-sigma) in region SIDE (L or R)."""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bulk import load
i, side = sys.argv[1], sys.argv[2]; PM = int(sys.argv[3]) if len(sys.argv) > 3 else 40
m, R, pre = load(i); N = len(pre); Dl = m['Delta']
rows = range(int(N * 0.6), N - 1, 3)
def reg(a):
    return (8, int(pre[a]) - 2 * Dl) if side == 'L' else (int(pre[a]) + 2, m['D'] - 1700)
for P in range(0, PM + 1):
    sc = []
    for sg in range(-130, 131):
        if P == 0 and sg <= 0: continue
        ag = tot = 0
        for a in rows:
            l1, h1 = reg(a); l2, h2 = reg(a - P)
            l, h = max(l1, l2 + sg), min(h1, h2 + sg)
            if h - l < 20: continue
            ag += int((R[a, l:h] == R[a - P, l - sg:h - sg]).sum()); tot += h - l
        if tot: sc.append((ag / tot, sg))
    sc.sort(reverse=True)
    print(P, ' '.join('%d:%.3f' % (s, f) for f, s in sc[:5]))
