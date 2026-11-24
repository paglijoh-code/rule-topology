#!/usr/bin/env python3
"""Segmentation certificate (sloped defects) for two-heap push-subtraction Sub(S1) -> Sub(S2).

Rows are exact (lead_a3.Pair). Relation INS(r, u): row r+u equals row r with blocks inserted:
at each defect j, v_j cells are inserted at a point x_j inside a run of row r that is periodic with
period dividing v_j for at least RUN cells before x_j; the inserted cells continue that run.
Everything else (head near the diagonal, between defects, the infinite tail) is copied unshifted
(relative to the cumulative offset). Straight double periodicity is the case of no defects.

COMPUTED check: INS holds for every row r in [A, A + K*u + M) with the same defect list (v_1..v_m)
up to rows where some defects are invisible (row purely periodic there), gper | u, gper | v_j.
Soundness lemma (paper argument): if INS holds on M consecutive rows with runs longer
than the transducer transient, it holds for all later rows, because row a is produced from rows
a-M..a-1 by a finite-state transducer in d whose state over a long run is periodic with period | v_j.
Usage: segcert.py PAIRS_JSONL NR UMAX WORKERS"""
import sys, json
from multiprocessing import Pool
from lead_a3 import Pair

def L(row):
    return len(row.pre) + 4 * len(row.cyc)

PMAX = 600

def align(R0, R1, M, vmax, RUN):
    """Return list of (x, v) insertions turning R0 into R1, or None."""
    n = L(R0) + 2 * vmax + 50
    ins, off, d = [], 0, 0
    while d < n:
        if R1(d + off) == R0(d):
            d += 1; continue
        # mismatch at d: R0's run ended before R1's did. Try an insertion of v cells at x = d.
        done = False
        # (a) tandem duplication: copy R0[d-v, d) to d, where R0 already repeats with lag v on [d-RUN, d)
        for v in range(1, vmax + 1):
            if d - RUN - v < 0: break
            if any(R0(t) != R0(t - v) for t in range(d - RUN, d)): continue
            if any(R1(d + off + i) != R0(d - v + i) for i in range(v)): continue
            if all(R1(d + off + v + i) == R0(d + i) for i in range(min(2 * RUN, n - d))):
                ins.append((d, v)); off += v; done = True; break
        # (b) continue a run of period p0 by v cells
        for p0 in ([] if done else range(1, PMAX + 1)):
            W = RUN + 2 * p0
            if d - W < 0: break
            if any(R0(t) != R0(t - p0) for t in range(d - W + p0, d)): continue
            for v in range(1, vmax + 1):
                # inserted cells continue the period-p0 run; afterwards R1 matches R0 again
                if any(R1(d + off + i) != R0(d - p0 + (i % p0)) for i in range(v)): continue
                if all(R1(d + off + v + i) == R0(d + i) for i in range(min(2 * RUN + 2 * p0, n - d))):
                    ins.append((d, v)); off += v; done = True; break
            if done: break
        if not done:
            return None
    # tail beyond n is periodic in both rows with equal cycles (checked by cycles equal)
    if R0.cyc != R1.cyc: return None
    return ins

def job(args):
    S1, S2, NR, UMAX = args
    P = Pair(tuple(S1), tuple(S2)); M = P.M
    for _ in range(NR): P.next_row()
    g = P.gper; A = NR // 3
    vmax = 400; RUN = 4 * M + 8
    for u in range(g, UMAX + 1, g):
        lists = []
        ok = True
        for r in range(A, min(NR - u, A + 3 * u + M)):
            ins = align(P.rows[r], P.rows[r + u], M, vmax, RUN)
            if ins is None or any(v % g for _, v in ins): ok = False; break
            lists.append(tuple(v for _, v in ins))
        if not ok: continue
        master = max(lists, key=len)
        def sub(l):
            it = iter(master); return all(x in it for x in l)
        if all(sub(l) for l in lists):
            return dict(S1=S1, S2=S2, u=u, v=list(master), A=A, rows_checked=len(lists),
                        straight=(len(master) == 0), gper=g)
    return dict(S1=S1, S2=S2, u=None)

if __name__ == "__main__":
    src, NR, UMAX, W = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    R = [json.loads(l) for l in open(src)]
    jobs = [(r['S1'], r['S2'], NR, UMAX) for r in R if r.get('cert', 'x') is None or 'cert' not in r]
    with Pool(W) as p:
        for r in p.imap_unordered(job, jobs):
            print(json.dumps(r), flush=True)
