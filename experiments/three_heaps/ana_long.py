"""three_heaps/ana_long.py N PAIR [RC] [DMAX] — long translations near the diagonal: for t = (q, q+d1, q+d2), 1 <= q <= N/2, |d1|,|d2| <= DMAX,
mismatch(t) = P(T(x) != T(x+t)) over cells at distance <= RC from the diagonal with a >= N/4 (exact, FFT along a of each line).
Prints the 10 smallest mismatches and the iid baseline."""
import sys, numpy as np
N, pair = int(sys.argv[1]), sys.argv[2]; RC = int(sys.argv[3]) if len(sys.argv) > 3 else 40; DM = int(sys.argv[4]) if len(sys.argv) > 4 else 4
X = np.fromfile(f"big/{N}/{pair}.diag", np.uint8); D = round((len(X) / (N + 1)) ** 0.5); R = D // 2; X = X.reshape(N + 1, D, D)[N // 4:]
A = X.shape[0]; i, j = np.meshgrid(np.arange(D) - R, np.arange(D) - R, indexing="ij"); r = np.sqrt(np.maximum(i * i + j * j - (i + j) ** 2 / 3, 0))
I, J = np.nonzero(r <= RC); need = np.zeros((D, D), bool)
for d1 in range(-DM, DM + 1):
    for d2 in range(-DM, DM + 1): need[np.clip(I + d1, 0, D - 1), np.clip(J + d2, 0, D - 1)] = True
li, lj = np.nonzero(need); pos = -np.ones((D, D), int); pos[li, lj] = np.arange(len(li))
Xl = X[:, li, lj]; m = (Xl != 2).astype(np.float32); f = np.where(Xl == 1, 1.0, -1.0).astype(np.float32) * m
S = 2 * A; Ff = np.fft.rfft(f, S, axis=0).astype(np.complex64); Fm = np.fft.rfft(m, S, axis=0).astype(np.complex64); del f, m
p = (Xl == 1).sum() / (Xl != 2).sum(); best = []
for d1 in range(-DM, DM + 1):
    for d2 in range(-DM, DM + 1):
        I2, J2 = I + d1, J + d2; ok = (I2 >= 0) & (I2 < D) & (J2 >= 0) & (J2 < D); a, b, a2, b2 = I[ok], J[ok], I2[ok], J2[ok]
        C = np.fft.irfft((np.conj(Ff[:, pos[a, b]]) * Ff[:, pos[a2, b2]]).sum(1), S)[:A // 2 + 1]
        Cn = np.fft.irfft((np.conj(Fm[:, pos[a, b]]) * Fm[:, pos[a2, b2]]).sum(1), S)[:A // 2 + 1]
        mis = (Cn - C) / (2 * np.maximum(Cn, 1))
        for q in range(1, A // 2 + 1):
            if (q, d1, d2) != (0, 0, 0) and Cn[q] > 1000: best.append((float(mis[q]), (q, q + d1, q + d2)))
best.sort(); print(pair, "N", N, f"r<={RC}", "shifts tested", len(best), "iid", round(float(2 * p * (1 - p)), 4))
print(" smallest:", [(t, round(x, 4)) for x, t in best[:10]])
