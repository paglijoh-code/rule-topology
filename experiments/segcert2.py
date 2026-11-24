#!/usr/bin/env python3
"""Piecewise-shift segmentation check for two-heap push-subtraction Sub(S1) -> Sub(S2).

Relation PS(r, u): row r+u (as a 0/1 string over d) is a concatenation of pieces, piece k being
row r shifted right by s_k (R1[j] = R0[j - s_k]), with at most JUNK unmatched cells in all.
This is a sector picture: sector k has translation vector (u, s_k) and its walls move by a fixed
amount per u rows. Straight periodicity: one piece, s = 0. Block insertion: pieces 0, v.
COMPUTED check for a pair: some u (multiple of per g) such that for every r in [A, A+3u+M)
the shift list (s_1..s_m) is the same and every wall moves by the same amount from r to r+u
(walls tracked over r, r+u, r+2u). This is evidence of a segmentation, not a proof.
Usage: segcert2.py PAIRS_JSONL NR UMAX WORKERS"""
import sys, json
import numpy as np
from multiprocessing import Pool
from lead_a3 import Pair

MINSEG, JUNK, PAD = 40, 60, 400

def arr(R, n):
    return np.array([R(d) for d in range(n)], dtype=np.int8)

def pieces(a, b, smin, smax):
    """Greedy cover of b by shifted copies of a. Returns [(start_in_b, shift)] or None."""
    n = len(b)
    shifts = list(range(smin, smax + 1))
    # run[s][j] = length of agreement b[j..] == a[j-s..], for j - s >= 0
    runs = {}
    for s in shifts:
        eq = np.zeros(n + 1, dtype=np.int32)
        lo = max(0, s); hi = min(n, len(a) + s)
        if hi <= lo: continue
        e = (b[lo:hi] == a[lo - s:hi - s]).astype(np.int32)
        # reverse run lengths
        r = np.zeros(hi - lo + 1, dtype=np.int32)
        for i in range(hi - lo - 1, -1, -1):
            pass
        # vectorized reverse run length: positions of zeros
        idx = np.arange(hi - lo)
        z = np.where(e == 0)[0]
        nxt = np.full(hi - lo, hi - lo, dtype=np.int64)
        if len(z):
            pos = np.searchsorted(z, idx)
            ok = pos < len(z)
            nxt[ok] = z[pos[ok]]
        eq[lo:hi] = (nxt - idx)
        runs[s] = eq
    out, j, junk = [], 0, 0
    while j < n - PAD // 2:
        best_s, best_l = None, 0
        for s, eq in runs.items():
            l = eq[j]
            if l > best_l or (l == best_l and l > 0 and out and s == out[-1][1]):
                best_s, best_l = s, l
        if best_l < MINSEG:
            junk += 1
            if junk > JUNK: return None
            j += 1; continue
        if not out or out[-1][1] != best_s:
            out.append((j, best_s))
        j += best_l
    return out

def local_period(b, x0, x1, pmax=600):
    # period of the interior of [x0, x1): trim a margin at each end (walls are fuzzy)
    m = min(60, (x1 - x0) // 6)
    seg = b[x0 + m:x1 - m]
    for p in range(1, min(pmax, len(seg) // 2) + 1):
        if np.array_equal(seg[p:], seg[:-p]): return p
    return None

def canon(b, pcs, end):
    """Merge neighbouring pieces whose shifts agree modulo the period of b on their union;
    drop thin pieces (shorter than THIN). Returns [(start, period, shift mod period)]."""
    pcs = [(int(x), int(s)) for x, s in pcs]
    bounds = lambda i: (pcs[i][0], pcs[i + 1][0] if i + 1 < len(pcs) else end)
    changed = True
    while changed:
        changed = False
        # drop thin interior pieces
        for i in range(1, len(pcs) - 1):
            x0, x1 = bounds(i)
            if x1 - x0 < THIN:
                del pcs[i]; changed = True; break
        if changed: continue
        for i in range(len(pcs) - 1):
            x0 = pcs[i][0]; x1 = bounds(i + 1)[1]
            p = local_period(b, x0, x1)
            if p and (pcs[i + 1][1] - pcs[i][1]) % p == 0:
                del pcs[i + 1]; changed = True; break
    out = []
    for i, (x, sh) in enumerate(pcs):
        x0, x1 = bounds(i)
        p = local_period(b, x0, x1) or 0
        out.append((x, p, sh % p if p else sh))
    return out

THIN = 120

def job(args):
    S1, S2, NR, UMAX = args
    P = Pair(tuple(S1), tuple(S2)); M = P.M
    for _ in range(NR): P.next_row()
    g = P.gper; A = NR // 3
    for u in range(g, UMAX + 1, g):
        if A + 4 * u + M >= NR: break
        sigs, walls_ok, ok = set(), True, True
        cache = {}
        def pc(r):
            if r not in cache:
                R0, R1 = P.rows[r], P.rows[r + u]
                n = max(len(R0.pre), len(R1.pre)) + PAD
                dv = len(R1.pre) - len(R0.pre)
                b = arr(R1, n)
                pcs = pieces(arr(R0, n), b, min(0, dv) - 200, max(0, dv) + 200)
                cache[r] = None if pcs is None else canon(b, pcs, n - PAD // 2)
            return cache[r]
        for r in range(A, A + 3 * u + M):
            p1 = pc(r)
            if p1 is None: ok = False; break
            sigs.add(tuple((q, s) for _, q, s in p1))
            p2 = pc(r + u)
            if p2 is None or tuple((q, s) for _, q, s in p2) != tuple((q, s) for _, q, s in p1): ok = False; break
            # walls move by the same amount per u rows: start(r+u) - start(r) == start(r+2u) - start(r+u)
            p0 = pc(r - u) if r - u >= A - u else None
            if p0 is not None and tuple((q, s) for _, q, s in p0) == tuple((q, s) for _, q, s in p1):
                if any((x2 - x1) != (x1 - x0) for (x0, _, _), (x1, _, _), (x2, _, _) in zip(p0, p1, p2)):
                    ok = False; break
        if ok:
            sig = max(sigs, key=len)
            def sub(l):
                it = iter(sig); return all(x in it for x in l)
            if not all(sub(l) for l in sigs): continue
            return dict(S1=S1, S2=S2, u=u, sectors=[list(t) for t in sig], A=A, gper=g,
                        walls=[int(x) for x, _, _ in pc(A)], rows_checked=3 * u + M)
    return dict(S1=S1, S2=S2, u=None)

if __name__ == "__main__":
    src, NR, UMAX, W = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    R = [json.loads(l) for l in open(src)]
    jobs = [(r['S1'], r['S2'], NR, UMAX) for r in R if r.get('u', 1) is None or r.get('cert', 1) is None]
    with Pool(W) as p:
        for r in p.imap_unordered(job, jobs):
            print(json.dumps(r), flush=True)
