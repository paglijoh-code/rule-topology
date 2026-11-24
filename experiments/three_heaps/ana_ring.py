"""three_heaps/ana_ring.py N PAIR RLO RHI ALO [QMAX] — best diagonal period q(1,1,1) restricted to the ring RLO <= r < RHI, a >= ALO;
also counts the defect cells (mismatch at the best q) by parity class of (a,b,c) and lists a few of them."""
import sys, numpy as np
N, pair = int(sys.argv[1]), sys.argv[2]; RLO, RHI, ALO = map(int, sys.argv[3:6]); QMAX = int(sys.argv[6]) if len(sys.argv) > 6 else 600
X = np.fromfile(f"big/{N}/{pair}.diag", np.uint8); D = round((len(X) / (N + 1)) ** 0.5); R = D // 2; X = X.reshape(N + 1, D, D)
i, j = np.meshgrid(np.arange(D) - R, np.arange(D) - R, indexing="ij"); r = np.sqrt(np.maximum(i * i + j * j - (i + j) ** 2 / 3, 0))
ring = (r >= RLO) & (r < RHI); Xc = X[:, ring]; I, J = i[ring], j[ring]
res = []
for q in range(1, min(QMAX, N - ALO - 50) + 1):
    A, B = Xc[ALO:N + 1 - q], Xc[ALO + q:]; v = (A != 2) & (B != 2); res.append(((A != B)[v].mean(), q))
res.sort(); print(pair, f"ring {RLO}<=r<{RHI}, a>={ALO}: best q", [(q, round(float(x), 5)) for x, q in res[:8]])
q = res[0][1]; A, B = Xc[ALO:N + 1 - q], Xc[ALO + q:]; m = (A != B) & (A != 2) & (B != 2)
aa, kk = np.nonzero(m); aa = aa + ALO; b = aa + I[kk]; c = aa + J[kk]
par = (aa % 2) * 4 + (b % 2) * 2 + (c % 2); print(" defects", len(aa), "by parity class (a%2,b%2,c%2):", np.bincount(par, minlength=8).tolist())
off = sorted(set(zip(I[kk].tolist(), J[kk].tolist()))); print(" distinct (b-a, c-a) offsets with defects:", len(off), off[:30])
