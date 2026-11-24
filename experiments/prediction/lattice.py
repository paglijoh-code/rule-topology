#!/usr/bin/env python3
"""Symmetry lattices of the bulk left (8 <= d < pre(a) - 2*Delta) and right (d > pre(a)) of the wall, in (a, d) coordinates.
Basis (HNF): (0, T) and (P, sigma), 0 <= sigma < T. A vector (P, s) is a symmetry if agreement of R_a(d) with R_{a-P}(d-s) >= THR."""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bulk import load, meta, OUT
def agree(R, pre, rows, side, P, sg, Dl, D):
    ag = tot = 0
    for a in rows:
        def reg(b): return (8, int(pre[b]) - 2 * Dl) if side == 'L' else (int(pre[b]) + 2, D - 1700)
        l1, h1 = reg(a); l2, h2 = reg(a - P); l, h = max(l1, l2 + sg), min(h1, h2 + sg)
        if h - l < 20: continue
        ag += int((R[a, l:h] == R[a - P, l - sg:h - sg]).sum()); tot += h - l
    return ag / tot if tot > 500 else 0.0
def lattice(R, pre, rows, side, Dl, D, thr, TMAX=400, PMAX=80):
    T = next((t for t in range(1, TMAX) if agree(R, pre, rows, side, 0, t, Dl, D) >= thr), None)
    if T is None: return None
    for P in range(1, PMAX):
        sc = [(agree(R, pre, rows, side, P, s, Dl, D), s) for s in range(T)]
        f, s = max(sc)
        if f >= thr: return dict(T=T, P=P, sigma=s, f=round(f, 4))
    return dict(T=T, P=None, sigma=None)
if __name__ == '__main__':
    res = {}
    for i in (sys.argv[1:] or sorted(meta)):
        m, R, pre = load(i); N = len(pre); Dl = m['Delta']
        rows = list(range(max(int(N * 0.6), 200), N - 1, 5))
        L = lattice(R, pre, rows, 'L', Dl, m['D'], 0.97); Rt = lattice(R, pre, rows, 'R', Dl, m['D'], 0.999)
        res[i] = dict(L=L, R=Rt, Delta=Dl, q=m['q'], lam=m['lam'], s=m['s'], gper=m['g']['per'], gpre=m['g']['pre'], S1=m['S1'])
        print(i[:42].ljust(42), 'Δ', Dl, 'q', m['q'], 's', m['s'], '| L', L, '| R', Rt, flush=True)
    json.dump(res, open(os.path.join(OUT, 'lattice.json'), 'w'), indent=1)
