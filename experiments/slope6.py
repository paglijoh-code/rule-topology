"""Pairs with no straight certificate (raw/out_hunt6.jsonl cert None).
1. From exact rows, find (u, v): row cycles repeat with period u in a, and the defect position
   pre(a) satisfies pre(a+u) == pre(a) + v (pre = 0 rows map to pre = 0 rows), for a in [NR/3, NR).
2. Two-region test, COMPUTED: for a in a window, cells d < cut(a) satisfy row[a+u](d) == row[a](d)
   and cells d >= cut(a) satisfy row[a+u](d+v) == row[a](d); cut(a) = pre(a) - K (variant 'L')
   or a fixed K (variant 'K'). Reports which variant holds, if any."""
import sys, json
from multiprocessing import Pool
from lead_a3 import Pair

def find_uv(P, lo, hi):
    pre = [len(r.pre) for r in P.rows]
    for u in range(1, 400):
        if any(P.rows[a].cyc != P.rows[a + u].cyc for a in range(lo, hi - u)):
            continue
        vs = {pre[a + u] - pre[a] for a in range(lo, hi - u) if pre[a] > 0 or pre[a + u] > 0}
        z = all((pre[a] == 0) == (pre[a + u] == 0) for a in range(lo, hi - u))
        if len(vs) == 1 and z:
            return u, vs.pop()
        if not vs and z:
            return u, 0
    return None

def two_region(P, u, v, lo, hi, cutf):
    for a in range(lo, hi - u):
        c = cutf(a)
        L = len(P.rows[a].pre) + 3 * len(P.rows[a].cyc) + v + 50
        for d in range(L):
            if d < c:
                if P.rows[a + u](d) != P.rows[a](d): return False
            elif P.rows[a + u](d + v) != P.rows[a](d): return False
    return True

def job(pr):
    S1, S2 = tuple(pr['S1']), tuple(pr['S2'])
    P = Pair(S1, S2); NR = 2400
    for _ in range(NR): P.next_row()
    uv = find_uv(P, NR // 3, NR)
    res = dict(S1=S1, S2=S2, uv=uv)
    if uv:
        u, v = uv
        pre = lambda a: len(P.rows[a].pre)
        for name, K in [('L', 40), ('L', 120), ('K', 0), ('K', 20), ('K', 60)]:
            f = (lambda a, K=K: pre(a) - K) if name == 'L' else (lambda a, K=K: K)
            if two_region(P, u, v, NR // 3, NR // 3 + 3 * u + 10, f):
                res['variant'] = f"{name}{K}"; break
        else:
            res['variant'] = None
    return res

if __name__ == "__main__":
    R = [json.loads(l) for l in open('raw/out_hunt6.jsonl')]
    bad = [r for r in R if r['cert'] is None]
    with Pool(12) as p:
        for r in p.imap_unordered(job, bad):
            print(json.dumps(r), flush=True)
