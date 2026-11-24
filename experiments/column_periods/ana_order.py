"""column_periods/ana_order.py PREFIX S [k] : 3D local order on slab S from slab files PREFIX.s{S}, .s{S+21}, .s{S+42}.
For each cell x of slab S and each axis i, e_i^p(x) = [T(x) != T(x + p e_i)], p in (21, 42).
Writes PREFIX.order{S}.npy: coarse (k x k cell blocks) mean of min_i e_i^42 and per-axis maps, and prints
a profile of mismatch against distance to the nearest mirror plane, and the chamber-bulk value."""
import numpy as np, sys
pre, S = sys.argv[1], int(sys.argv[2]); k = int(sys.argv[3]) if len(sys.argv) > 3 else 40
def ld(s): return np.fromfile(f"{pre}.s{s}", dtype=np.uint8).reshape(s + 1, s + 1)
X = ld(S); Y = {p: ld(S + p) for p in (21, 42)}
n = S + 1; a = np.arange(n)[:, None]; b = np.arange(n)[None, :]; inside = (a + b) <= S
E = {}
for p in (21, 42):
    Z = Y[p]
    E[('c', p)] = X != Z[:n, :n]                 # x + p e_c : same (a,b) on slab S+p
    E[('a', p)] = X != Z[p:p + n, :n]            # (a+p, b)
    E[('b', p)] = X != Z[:n, p:p + n]            # (a, b+p)
m42 = np.minimum(np.minimum(E[('a', 42)], E[('b', 42)]), E[('c', 42)])
c = S - a - b
dm = np.minimum(np.minimum(abs(a - b), abs(b - c)), abs(a - c))
# per-cell "best axis" is too noisy; use block-level min over axes of block-mean mismatch
nb = n // k
def blk(M):
    M = np.where(inside, M.astype(float), np.nan)[:nb * k, :nb * k]
    return np.nanmean(M.reshape(nb, k, nb, k), axis=(1, 3))
import warnings; warnings.simplefilter('ignore')
B = {key: blk(v) for key, v in E.items()}
best = np.fmin(np.fmin(B[('a', 42)], B[('b', 42)]), B[('c', 42)])
best21 = np.fmin(np.fmin(B[('a', 21)], B[('b', 21)]), B[('c', 21)])
dmb = blk(dm); dens = blk(X == 1)
np.save(f"{pre}.order{S}.npy", np.stack([best, best21, dmb, dens, B[('a', 42)], B[('b', 42)], B[('c', 42)]]))
print(f"S={S} block={k}: profile of min-axis 42-mismatch vs distance to mirror plane (block means)")
edges = [0, 0.01, 0.02, 0.04, 0.06, 0.08, 0.1, 0.15, 0.2, 0.3, 0.5, 1.0]
for lo, hi in zip(edges, edges[1:]):
    m = (dmb >= lo * S) & (dmb < hi * S) & np.isfinite(best)
    if m.sum(): print(f"  dmirror/S in [{lo},{hi}): blocks {m.sum():5d}  min-axis-42 {np.nanmean(best[m]):.4f}  min-axis-21 {np.nanmean(best21[m]):.4f}  frac blocks exact(=0) {np.mean(best[m]==0):.3f}  density {np.nanmean(dens[m]):.4f}")
