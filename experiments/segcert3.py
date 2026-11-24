#!/usr/bin/env python3
"""Run-decomposition segmentation check for two-heap push-subtraction Sub(S1) -> Sub(S2).

Each exact row (lead_a3.Pair) is cut greedily, from the diagonal outward, into maximal periodic
runs: at position j take the period p <= PMAX whose run from j is longest (ties: smallest p).
A run shorter than MINSEG counts as junk (at most JUNK junk cells per row). The run signature
is the list of (p, cycle word up to rotation); walls are the run start positions.
COMPUTED check: a u (multiple of per g) such that over rows r in [A, A+3u+M) every signature is a
sublist of one master signature, and for every r whose row and row r+u both have the master
signature, wall_k(r+u) - wall_k(r) = delta_k is the same for all such r. Then the rows look like
k sectors with walls of slope delta_k/u. This is evidence of an outcome segmentation (sectors
between rational-slope walls, each periodic), not a proof.
Usage: segcert3.py PAIRS_JSONL NR UMAX WORKERS"""
import sys, json
import numpy as np
from multiprocessing import Pool
from lead_a3 import Pair

MINSEG, JUNK, PAD, PMAX = 40, 80, 300, 600

def arr(R, n):
    return np.fromiter((R(d) for d in range(n)), dtype=np.int8, count=n)

def minrot(w):
    return min(w[i:] + w[:i] for i in range(len(w)))

def runs(b, tail_from):
    """Greedy periodic-run cover of b[0:tail_from+PAD]. Returns list of (start, p, word) or None."""
    n = len(b); out = []; j = 0; junk = 0
    while j < tail_from:
        best = (0, None)
        for p in range(1, PMAX + 1):
            if j + p >= n: break
            e = b[j + p:] != b[j:n - p]
            z = np.flatnonzero(e)
            L = (z[0] if len(z) else n - j - p) + p
            if L >= 3 * p and L > best[0]: best = (L, p)
            if L >= n - j: break
        L, p = best
        if L < max(MINSEG, 3 * (p or 1)):
            junk += 1
            if junk > JUNK: return None
            j += 1; continue
        w = ''.join(map(str, b[j:j + p]))
        out.append((j, p, minrot(w)))
        j += L
    return out

def job(args):
    S1, S2, NR, UMAX = args
    P = Pair(tuple(S1), tuple(S2)); M = P.M
    for _ in range(NR): P.next_row()
    g = P.gper; A = NR // 3
    cache = {}
    def rr(r):
        if r not in cache:
            R = P.rows[r]; T = len(R.pre)
            n = T + PAD + 2 * PMAX + 2 * len(R.cyc)
            cache[r] = runs(arr(R, n), T + PAD // 2)
        return cache[r]
    for u in range(g, UMAX + 1, g):
        if A + 4 * u + M >= NR: break
        sigs = {}; ok = True
        for r in range(A, A + 3 * u + M + u):
            x = rr(r)
            if x is None: ok = False; break
            sigs[r] = tuple((p, w) for _, p, w in x)
        if not ok: continue
        master = max(sigs.values(), key=len)
        def sub(l):
            it = iter(master); return all(x in it for x in l)
        if not all(sub(l) for l in sigs.values()): continue
        deltas = None
        for r in range(A, A + 3 * u + M):
            if sigs[r] == master and sigs[r + u] == master:
                d = tuple(int(b[0] - a[0]) for a, b in zip(rr(r), rr(r + u)))
                if deltas is None: deltas = d
                elif d != deltas: ok = False; break
        if ok and deltas is not None:
            return dict(S1=S1, S2=S2, u=u, sectors=[[p, w] for p, w in master], wall_moves=list(deltas),
                        A=A, gper=g, rows_checked=3 * u + M)
    return dict(S1=S1, S2=S2, u=None)

if __name__ == "__main__":
    src, NR, UMAX, W = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    R = [json.loads(l) for l in open(src)]
    jobs = [(r['S1'], r['S2'], NR, UMAX) for r in R if r.get('cert', 1) is None]
    with Pool(W) as p:
        for r in p.imap_unordered(job, jobs):
            print(json.dumps(r), flush=True)
