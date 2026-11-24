#!/usr/bin/env python3
"""Rule R1 (pre-registered form): from the FAR TAIL of a short run only (no use of pre(a) records, M, or any fit),
  T_R = least d-period of rows a in [A0, A1) on d in [DL, DH)   (exact on every cell)
  P_R = least P >= 1 with R_a(d) = R_{a-P}(d) on that window      (exact)
predict, for a pair that has an exact sqrt(a) wall:  Delta = T_R,  s = T_R * P_R / per(g)  (lambda = P_R / per(g)).
Usage: predict.py JOBS.jsonl OUT.jsonl  (job: {"id", "S1", "gpre", "gper", "gpat"}); runs wallscan N=A1 rows, D=DH+200 cols."""
import json, os, subprocess, sys, tempfile, numpy as np
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
WS = os.path.join(ROOT, 'census_10/out/wallscan')
A0, A1, DL, DH = 700, 1300, 2000, 3800
def bulk(job):
    with tempfile.TemporaryDirectory(dir=os.path.join(HERE, 'out')) as td:
        f = os.path.join(td, 'r.bin'); D = DH + 200
        cmd = [WS, str(A1), str(D), '400', ','.join(map(str, job['S1'])), str(job['gpre']), str(job['gper']), ','.join(map(str, job['gpat']))]
        p = subprocess.run(cmd, env=dict(os.environ, WS_DUMP=f), capture_output=True, text=True)
        try: st = json.loads(p.stdout)['status']
        except Exception: st = 'error'
        if not os.path.exists(f) or os.path.getsize(f) < A1 * D: return dict(id=job['id'], status='short:' + st)
        R = np.fromfile(f, dtype=np.uint8).reshape(A1, D)[:, DL:DH]
    W = R[A0:A1]
    T = next((t for t in range(1, 600) if np.array_equal(W[:, t:], W[:, :-t])), None)
    P = next((q for q in range(1, A0) if np.array_equal(R[A0:A1], R[A0 - q:A1 - q])), None)
    out = dict(id=job['id'], status=st, T_R=T, P_R=P)
    if T and P:
        s = Fraction(T * P, job['gper'])
        out.update(Delta_pred=T, s_pred=str(s), lam_pred=str(Fraction(P, job['gper'])))
    return out
if __name__ == '__main__':
    jobs = [json.loads(l) for l in open(sys.argv[1])]
    with ProcessPoolExecutor(14) as ex, open(sys.argv[2], 'w') as fo:
        for r in ex.map(bulk, jobs, chunksize=4):
            fo.write(json.dumps(r) + '\n')
