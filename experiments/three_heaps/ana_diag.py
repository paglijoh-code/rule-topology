"""three_heaps/ana_diag.py N PAIR [QMAX] [RC] — translation along the main diagonal, from big/N/PAIR.diag (X[a][i][j] = T(a, a+i-R, a+j-R)).
For each q <= QMAX: mismatch m(q) = P(T(x) != T(x + q(1,1,1))) over cells at distance r <= RC from the diagonal with a >= N/4.
For the best q: mismatch per a-bin (a = s/3 on the axis) and per radius bin, i.e. where the remaining defects sit."""
import sys, numpy as np
N, pair = int(sys.argv[1]), sys.argv[2]; QMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 240; RC = int(sys.argv[4]) if len(sys.argv) > 4 else 120
X = np.fromfile(f"big/{N}/{pair}.diag", np.uint8); D = round((len(X) / (N + 1)) ** 0.5); R = D // 2; X = X.reshape(N + 1, D, D)
i, j = np.meshgrid(np.arange(D) - R, np.arange(D) - R, indexing="ij"); r = np.sqrt(np.maximum(i * i + j * j - (i + j) ** 2 / 3, 0))
core = r <= RC; Xc = X[:, core]; rc = r[core]          # (N+1, ncore)
a0 = N // 4
def mis(q, lo=a0):
    A, B = Xc[lo:N + 1 - q], Xc[lo + q:]; v = (A != 2) & (B != 2); return ((A != B) & v), v
res = []
for q in range(1, QMAX + 1):
    m, v = mis(q); res.append((m.sum() / v.sum(), q))
res.sort(); best = res[0][1]
p = ((Xc == 1) & (Xc != 2)).sum() / (Xc != 2).sum()
print(pair, "N", N, "core r <=", RC, "density", round(float(p), 4), "iid", round(float(2 * p * (1 - p)), 4))
print(" best q (shift q(1,1,1)) over a >= N/4:", [(q, round(float(x), 5)) for x, q in res[:6]])
m, v = mis(best, 0); A = np.arange(N + 1 - best)
print(" mismatch at best q per a-bin of 100 (s = 3a):", [(int(lo), round(float(m[lo:lo + 100].sum() / max(1, v[lo:lo + 100].sum())), 5)) for lo in range(0, N + 1 - best, 100)])
rb = (rc // 10).astype(int)
for lo in range(0, N + 1 - best, 250):
    mm, vv = m[lo:lo + 250], v[lo:lo + 250]
    prof = [round(float(mm[:, rb == k].sum() / max(1, vv[:, rb == k].sum())), 4) for k in range(int(RC // 10) + 1)]
    print(f"  a in [{lo},{lo+250}) mismatch by r-bin of 10:", prof)
