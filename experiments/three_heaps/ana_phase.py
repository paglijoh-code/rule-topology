"""three_heaps/ana_phase.py N PAIR P REF k... — domain (phase) analysis. The background B is the most frequent aligned P^3 block of window
big/N/PAIR.win<REF>. In window k every aligned P^3 block is matched against the translates of B and of its 5 axis permutations:
'exact' if some translate matches, else 'defect'. Prints the share of exact blocks, how many phases occur (with shares),
and the share of neighbouring exact blocks that carry different phases (domain walls)."""
import sys, numpy as np
N, pair, P, REF = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
def win(k):
    W = np.fromfile(f"big/{N}/{pair}.win{k}", np.uint8); L = round(len(W) ** (1 / 3)); return W.reshape(L, L, L)
R = win(REF); n0 = R.shape[0] // P                       # background = most frequent aligned P^3 block of window REF
blk, c = np.unique(R[:n0 * P, :n0 * P, :n0 * P].reshape(n0, P, n0, P, n0, P).transpose(0, 2, 4, 1, 3, 5).reshape(-1, P ** 3), axis=0, return_counts=True)
B = blk[c.argmax()].reshape(P, P, P); print(" background block share in reference window", round(c.max() / c.sum(), 4)); T = {}
import itertools
for perm in itertools.permutations(range(3)):                # the six chambers carry axis-permuted copies of the background
    Bp = B.transpose(perm)
    for i in range(P):
        for j in range(P):
            for l in range(P): T.setdefault(np.roll(Bp, (-i, -j, -l), (0, 1, 2)).tobytes(), (perm, i, j, l))
print(pair, "N", N, "background period", P, "translates", len(T), "(distinct", len(set(T)), ")")
for k in map(int, sys.argv[5:]):
    W = win(k); n = W.shape[0] // P
    ph = -np.ones((n, n, n), int); keys = {}
    for x in range(n):
        for y in range(n):
            for z in range(n):
                t = T.get(W[x * P:(x + 1) * P, y * P:(y + 1) * P, z * P:(z + 1) * P].tobytes())
                if t is not None: ph[x, y, z] = keys.setdefault(t, len(keys))
    ex = ph >= 0; cnt = np.bincount(ph[ex]); walls = tot = 0
    for ax in range(3):
        a = np.moveaxis(ph, ax, 0); m = (a[1:] >= 0) & (a[:-1] >= 0); tot += m.sum(); walls += (m & (a[1:] != a[:-1])).sum()
    print(f" win{k}: exact blocks {ex.mean():.4f}; phases {len(cnt)}; top shares {np.round(np.sort(cnt)[::-1][:6] / ex.sum(), 3).tolist()}; "
          f"neighbouring exact blocks with different phase {walls / max(tot, 1):.4f}")
