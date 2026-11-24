"""three_heaps/lib3.py — solver wrappers, game-semantic brute force, phase-boundary detector (three heaps)."""
import os, subprocess, tempfile, functools, itertools, math
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
TMP = os.environ.get("M5C_TMP", tempfile.gettempdir())

def _run(args):
    subprocess.check_call([os.path.join(HERE, args[0])] + [str(x) for x in args[1:]])

def chain(N, sets):
    """P-set (bool array (N+1)^3) of start node of chain sets[0] -> sets[1] -> ... (each a tuple)."""
    out = tempfile.mktemp(dir=TMP)
    _run(["chain3", N, out] + [",".join(map(str, s)) for s in sets])
    T = np.fromfile(out, dtype=np.uint8).reshape(N + 1, N + 1, N + 1).astype(bool); os.unlink(out); return T

def phi(N, S, T=None):
    """Phi_S(T) on three heaps; T bool array or None (empty)."""
    out = tempfile.mktemp(dir=TMP); tin = "-"
    if T is not None:
        tin = tempfile.mktemp(dir=TMP); T.astype(np.uint8).tofile(tin)
    _run(["phi3", N, ",".join(map(str, S)), tin, out])
    if tin != "-": os.unlink(tin)
    R = np.fromfile(out, dtype=np.uint8).reshape(N + 1, N + 1, N + 1).astype(bool); os.unlink(out); return R

def brute_chain(N, sets):
    """Independent game-semantic brute force: state (node, a, b, c); moves Sub(S_node) on one heap,
    or push (costs the turn) to node+1 if it exists. Normal play. Returns bool array of P for node 0."""
    k = len(sets)
    @functools.lru_cache(maxsize=None)
    def win(i, x):
        for j in range(3):
            for s in sets[i]:
                if x[j] >= s:
                    y = list(x); y[j] -= s
                    if not win(i, tuple(y)): return True
        if i + 1 < k and not win(i + 1, x): return True
        return False
    T = np.zeros((N + 1,) * 3, bool)
    for x in itertools.product(range(N + 1), repeat=3):
        T[x] = not win(0, x)
    return T

# ---------------- phase-boundary detector ----------------
def far_period(T, pmax=60):
    """Period of the far region: the p <= pmax minimising the fraction of far cells (all coords >= N/2)
    with T(x) != T(x + p e_c); the smallest p within 1% (absolute 1e-4) of that minimum.
    Returns (p, mismatch fraction at p)."""
    N = T.shape[0] - 1; lo = N // 2; B = T[lo:, lo:, lo:]
    fr = [float((B[:, :, :-p] != B[:, :, p:]).mean()) for p in range(1, pmax + 1)]
    m = min(fr)
    for p in range(1, pmax + 1):
        if fr[p - 1] <= m * 1.01 + 1e-4: return p, fr[p - 1]

def mismatch(T, p):
    """D: cells x (with x + p e_i inside) where T(x) != T(x + p e_i) for some axis i."""
    D = np.zeros_like(T)
    D[:-p, :, :] |= T[:-p] != T[p:]
    D[:, :-p, :] |= T[:, :-p] != T[:, p:]
    D[:, :, :-p] |= T[:, :, :-p] != T[:, :, p:]
    return D

def forms(r=2):
    out = []
    for v in itertools.product(range(-r, r + 1), repeat=3):
        if v == (0, 0, 0) or math.gcd(*map(abs, v)) != 1: continue
        if tuple(-t for t in v) in out: continue
        out.append(v)
    return out

def plane_cover(D, p, maxplanes=40, r=2, slab=None):
    """Greedy cover of D (sorted coordinates u <= v <= w) by slabs  k <= alpha.(u,v,w) < k + width.
    width = slab or p (a slip plane shows as p parallel mismatch planes). Returns (planes, residue count, residue coords)."""
    idx = np.argwhere(D)
    U = np.sort(idx, axis=1)
    U = np.unique(U, axis=0)
    alive = np.ones(len(U), bool); planes = []
    F = forms(r); width = slab or p
    vals = {f: U @ np.array(f) for f in F}
    while alive.sum() and len(planes) < maxplanes:
        best = None
        for f in F:
            v = vals[f][alive]
            if not len(v): continue
            lo = v.min(); h = np.bincount(v - lo)
            c = np.convolve(h, np.ones(width, int), "valid") if len(h) >= width else np.array([h.sum()])
            k = int(c.argmax())
            if best is None or c[k] > best[0]: best = (int(c[k]), f, int(k + lo))
        cnt, f, k = best
        if cnt < max(8, 0.002 * len(U)): break
        sel = alive & (vals[f] >= k) & (vals[f] < k + width)
        alive &= ~sel; planes.append((f, k, cnt))
    return planes, int(alive.sum()), U[alive]

def line_clusters(T, p):
    """Lines along c with a <= b (the table is symmetric). Mismatch m(c) = T(a,b,c) != T(a,b,c+p).
    Clusters: runs of mismatches merged across gaps < p. Returns list of (a, b, start, end) (end exclusive)."""
    N = T.shape[0] - 1
    Mm = T[:, :, :-p] != T[:, :, p:]
    out = []
    aa, bb = np.nonzero(np.triu(Mm.any(axis=2)))
    for a, b in zip(aa, bb):
        cs = np.flatnonzero(Mm[a, b])
        br = np.flatnonzero(np.diff(cs) >= p)
        starts = np.r_[cs[0], cs[br + 1]]; ends = np.r_[cs[br], cs[-1]] + 1
        for s, e in zip(starts, ends): out.append((int(a), int(b), int(s), int(e)))
    return np.array(out, dtype=int).reshape(-1, 4)

def analyse(T, pmax=60, verbose=False):
    """Phase-boundary summary of a three-heap table."""
    N = T.shape[0] - 1; p, fr = far_period(T, pmax)
    C = line_clusters(T, p)
    w = C[:, 3] - C[:, 2] if len(C) else np.zeros(0, int)
    thin = C[w <= p]; thick = C[w > p]
    r = dict(N=N, p=p, far_mismatch=fr, n_clusters=len(C), n_thin=len(thin), n_thick=len(thick),
             max_thick_width=int(w.max()) if len(thick) else 0)
    # thin clusters: slip points (a, b, end) -> sorted coords -> plane cover
    if len(thin):
        X = np.zeros((N + 1,) * 3, bool)
        X[thin[:, 0], thin[:, 1], thin[:, 2]] = True
        planes, res, R = plane_cover(X, p, slab=p)
        r["slip_planes"] = [(f, k, c) for f, k, c in planes]; r["slip_residue"] = res
        r["slip_residue_maxu"] = int(R[:, 0].max()) if res else None
    if len(thick):
        u = np.minimum(thick[:, 0], np.minimum(thick[:, 1], thick[:, 2]))   # smallest coordinate at cluster start
        r["thick_max_u"] = int(u.max())
        # thick lines far from every face (all coordinates >= N/4 at the start)
        far = thick[(thick[:, 0] >= N // 4) & (thick[:, 2] >= N // 4)]
        r["thick_far"] = len(far); r["thick_far_maxwidth"] = int((far[:, 3] - far[:, 2]).max()) if len(far) else 0
    return r, C

def complexity(T, k=4, Ns=None):
    """Number of distinct k x k x k blocks (k <= 4) whose corner lies in [0, n - k]^3, for each n in Ns."""
    N = T.shape[0] - 1; Ns = Ns or [N]
    code = np.zeros(tuple(s - k + 1 for s in T.shape), np.uint64); sh = 0
    for i in range(k):
        for j in range(k):
            for l in range(k):
                code |= T[i:i + code.shape[0], j:j + code.shape[1], l:l + code.shape[2]].astype(np.uint64) << np.uint64(sh); sh += 1
    return [len(np.unique(code[:n - k + 1, :n - k + 1, :n - k + 1])) for n in Ns]

def cycle(N, sets, kmax=4000):
    """(onset, period) of budgeted directed cycle sets[0] -> sets[1] -> ... -> sets[0] (C solver cyc3)."""
    out = subprocess.check_output([os.path.join(HERE, "cyc3"), str(N), str(kmax)] + [",".join(map(str, s)) for s in sets]).split()
    return (None, None) if out[0] == b"none" else (int(out[0]), int(out[1]))

def cycle_py(N, sets, kmax=400):
    """Same via phi3 and Python state hashing (slow; for checks)."""
    n = len(sets); X = [phi(N, s) for s in sets]; seen = {}
    for k in range(kmax):
        key = b"".join(x.tobytes() for x in X)
        if key in seen: return seen[key], k - seen[key]
        seen[key] = k
        X = [phi(N, sets[v], X[(v + 1) % n]) for v in range(n)]
    return None, None
