#!/usr/bin/env python3
"""legs.py ID PL : defect mask E_a(d) = [R_a(d) != R_{a-PL}(d)] on the left region (8 <= d < pre(a) - 2*Delta);
correlation C(i, r) = sum E_a(d) E_{a+i}(d+r) / sum E for 1 <= i <= IMAX, |r| <= 60 (excluding (i,0)), top velocity vectors."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bulk import load
i_, PL = sys.argv[1], int(sys.argv[2]); IMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 12
m, R, pre = load(i_); N = len(pre); Dl = m['Delta']; D = m['D']
a0 = int(N * 0.6); A = np.arange(a0, N)
E = np.zeros((N, D), bool)
for a in A:
    h = int(pre[a]) - 2 * Dl
    if h > 8: E[a, 8:h] = R[a, 8:h] != R[a - PL, 8:h]
tot = E.sum(); res = []
for i in range(1, IMAX + 1):
    X = E[a0:N - i]; Y = E[a0 + i:N]
    for r in range(-60, 61):
        if r >= 0: c = (X[:, :D - r] & Y[:, r:]).sum()
        else: c = (X[:, -r:] & Y[:, :D + r]).sum()
        res.append((c / tot, i, r))
res.sort(reverse=True)
print(i_[:40], 'defect density', round(tot / sum(max(int(pre[a]) - 2 * Dl - 8, 0) for a in A), 4))
print(' '.join('(%d,%d):%.2f' % (i, r, c) for c, i, r in res[:int(os.environ.get('TOP', '12'))]))
