"""three_heaps/ana_win.py N PAIR k [H] — translation scan of window big/N/PAIR.win<k> (L^3, L=256): for every shift t in [-H,H]^3,
mismatch(t) = P(T(x) != T(x+t)) over the overlap, computed exactly by FFT correlation. Prints the smallest mismatches,
the iid baseline 2p(1-p), and the structure-factor summary (share of variance in the top Fourier modes)."""
import sys, numpy as np, numpy.fft as F
N, pair, k = sys.argv[1], sys.argv[2], int(sys.argv[3]); H = int(sys.argv[4]) if len(sys.argv) > 4 else 64
W = np.fromfile(f"big/{N}/{pair}.win{k}", np.uint8); L = round(len(W) ** (1 / 3)); W = W.reshape(L, L, L)
def scan(W, H):
    m = (W != 2).astype(np.float32); f = np.where(W == 1, 1.0, -1.0).astype(np.float32) * m
    S = L + H
    def corr(x, y): return F.irfftn(np.conj(F.rfftn(x, (S,) * 3, axes=(0, 1, 2))) * F.rfftn(y, (S,) * 3, axes=(0, 1, 2)), (S,) * 3, axes=(0, 1, 2))
    C = corr(f, f); Cn = corr(m, m)
    idx = np.r_[0:H + 1, S - H:S]; C = C[np.ix_(idx, idx, idx)]; Cn = Cn[np.ix_(idx, idx, idx)]
    mis = (Cn - C) / (2 * np.maximum(Cn, 1)); sh = np.r_[0:H + 1, -H:0]
    return mis, sh
if __name__ == "__main__":
    p = (W == 1).sum() / (W != 2).sum(); mis, sh = scan(W, H); mis[0, 0, 0] = 9
    o = np.argsort(mis, axis=None)[:12]
    print(pair, "win", k, "density", round(float(p), 4), "iid baseline", round(float(2 * p * (1 - p)), 4))
    print(" smallest mismatch shifts:", [(tuple(int(sh[i]) for i in np.unravel_index(j, mis.shape)), round(float(mis.flat[j]), 4)) for j in o])
    g = np.where(W == 2, 0, W.astype(np.float32) - p); P = np.abs(F.rfftn(g)) ** 2; P[0, 0, 0] = 0; tot = P.sum()
    q = np.sort(P, axis=None)[::-1]
    print(" variance share in top 10 / 100 / 1000 Fourier modes:", [round(float(q[:n].sum() / tot), 3) for n in (10, 100, 1000)],
          "(iid: ~", round(10 / P.size * np.log(P.size), 5), "for top 10)")
    top = np.argsort(P, axis=None)[::-1][:8]
    print(" top modes (freq*L):", [tuple(int(x) for x in np.unravel_index(j, P.shape)) for j in top])
