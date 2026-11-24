"""three_heaps/ana_ent.py N PAIR k [seed] — entropy of window big/N/PAIR.win<k>: Shannon entropy H(n) of length-n words along each axis
(n <= 24) and of n x n patches in planes a = const (n <= 5); entropy rate estimates h(n) = H(n+1) - H(n) (bits per cell).
Controls: an iid table with the same density, and the window shuffled within each of the 105^3 residue classes
of (a,b,c) mod 105 (keeps every periodic component of the forcing, destroys everything else)."""
import sys, numpy as np
N, pair, k = sys.argv[1], sys.argv[2], int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
W = np.fromfile(f"big/{N}/{pair}.win{k}", np.uint8); L = round(len(W) ** (1 / 3)); W = W.reshape(L, L, L)
assert (W != 2).all()
def H(codes):
    _, c = np.unique(codes, return_counts=True); p = c / c.sum(); return float(-(p * np.log2(p)).sum())
def words(T, n, ax):
    T = np.moveaxis(T, ax, 2).astype(np.uint64); code = np.zeros(T[:, :, :L - n + 1].shape, np.uint64)
    for t in range(n): code |= T[:, :, t:L - n + 1 + t] << np.uint64(t)
    return code.ravel()
def patches(T, n):
    T = T.astype(np.uint64); code = np.zeros(T[:, :L - n + 1, :L - n + 1].shape, np.uint64); sh = 0
    for x in range(n):
        for y in range(n): code |= T[:, x:L - n + 1 + x, y:L - n + 1 + y] << np.uint64(sh); sh += 1
    return code.ravel()
def report(T, name):
    hw = [H(words(T, n, 2)) for n in range(1, 25)]; hd = [round(hw[n] - hw[n - 1], 4) for n in (4, 8, 12, 16, 20, 23)]
    hp = [H(patches(T, n)) for n in range(1, 6)]
    print(f" {name:9s} H(1)={hw[0]:.4f}  word rate h(n) n=5,9,13,17,21,24: {hd}   patch H(n)/n^2 n=1..5: {[round(hp[n - 1] / n / n, 4) for n in range(1, 6)]}")
print(pair, "win", k, "L", L)
report(W, "table")
report((rng.random(W.shape) < W.mean()).astype(np.uint8), "iid")
S = W.copy(); P = 105; idx = np.indices(W.shape).reshape(3, -1); cls = ((idx[0] % P) * P + idx[1] % P) * P + idx[2] % P
flat = S.ravel(); o = np.argsort(cls, kind="stable"); cs = cls[o]; vals = flat[o].copy()
b = np.r_[0, np.nonzero(np.diff(cs))[0] + 1, len(cs)]
for s0, s1 in zip(b[:-1], b[1:]): rng.shuffle(vals[s0:s1])
flat[o] = vals; report(S, "shuf105")
