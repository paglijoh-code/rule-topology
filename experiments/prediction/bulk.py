#!/usr/bin/env python3
"""Bulk lattices left and right of the wall. For each dump: T_L = least d-period of the left region (agreement >= THR),
(P_L, sig_L) = least row period with shift in the left region; same for the right region (d > pre(a))."""
import json, os, sys, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(HERE, 'out')
meta = json.load(open(os.path.join(OUT, 'meta.json')))
THR = float(os.environ.get('THR', '0.98'))
def load(i):
    m = meta[i]; R = np.fromfile(os.path.join(OUT, i + '.bin'), dtype=np.uint8).reshape(m['N'], m['D'])
    pre = np.fromfile(os.path.join(OUT, i + '.bin.pre'), dtype=np.int32); return m, R, pre
def dper(R, rows, lo, hi):
    for T in range(1, 400):
        agree = tot = 0
        for a in rows:
            l, h = lo[a], hi[a] - T
            if h - l < 20: continue
            x = R[a, l:h]; y = R[a, l + T:h + T]; agree += int((x == y).sum()); tot += h - l
        if tot and agree / tot >= THR: return T, agree / tot
    return None, None
def aper(R, rows, lo, hi, Pmax=200, smax=120):
    best = None
    for P in range(1, Pmax):
        for sg in range(-smax, smax + 1):
            agree = tot = 0
            for a in rows[::4]:
                l, h = max(lo[a], lo[a - P] + sg, 0), min(hi[a], hi[a - P] + sg)
                if h - l < 20: continue
                x = R[a, l:h]; y = R[a - P, l - sg:h - sg]; agree += int((x == y).sum()); tot += h - l
            if tot > 2000 and agree / tot >= THR: return P, sg, agree / tot
    return None
if __name__ == '__main__':
    res = {}
    ids = sys.argv[1:] or sorted(meta)
    for i in ids:
        m, R, pre = load(i); N = len(pre); M = np.maximum.accumulate(pre)
        rows = list(range(int(N * 0.6), N - 1))
        Dl = m['Delta']
        loL = {a: 8 for a in rows}; hiL = {a: int(pre[a]) - 2 * Dl for a in rows}
        for a in rows: hiL[a] = max(hiL[a], 8)
        loR = {a: int(pre[a]) + 2 for a in rows}; hiR = {a: m['D'] - 1700 for a in rows}
        for a in list(rows):
            if a - 200 < 0: rows.remove(a)
        for d in (loL, hiL, loR, hiR):
            for a in range(int(N * 0.6) - 200, int(N * 0.6)):
                d.setdefault(a, 8 if d is loL else (int(pre[a]) - 2 * Dl if d is hiL else (int(pre[a]) + 2 if d is loR else m['D'] - 1700)))
        TL = dper(R, rows, loL, hiL); TR = dper(R, rows, loR, hiR)
        AL = aper(R, rows, loL, hiL); AR = aper(R, rows, loR, hiR)
        res[i] = dict(TL=TL, TR=TR, AL=AL, AR=AR, Delta=Dl, q=m['q'], lam=m['lam'], gper=m['g']['per'])
        print(i[:44].ljust(44), 'Δ', Dl, 'q', m['q'], 'λ', m['lam'], '| TL', TL[0], 'AL', AL and AL[:2], '| TR', TR[0], 'AR', AR and AR[:2], flush=True)
    json.dump(res, open(os.path.join(OUT, 'bulk.json'), 'w'), indent=1)
