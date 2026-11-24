"""three_heaps/big.py — non-saturated pairs at N = 450: complexity at 150, 300, 450, plus where new blocks appear
(distance class of new-block corners: d = max - (sum of others), and min coordinate)."""
import json, sys, numpy as np
from multiprocessing import Pool
from lib3 import chain
N = 450; k = 4
def codes(T):
    code = np.zeros(tuple(s - k + 1 for s in T.shape), np.uint64); sh = 0
    for i in range(k):
        for j in range(k):
            for l in range(k):
                code |= T[i:i + code.shape[0], j:j + code.shape[1], l:l + code.shape[2]].astype(np.uint64) << np.uint64(sh); sh += 1
    return code
def job(pair):
    T = chain(N, [tuple(pair[0]), tuple(pair[1])]); C = codes(T); del T
    out = dict(S1=pair[0], S2=pair[1])
    out["cx"] = [len(np.unique(C[:n - k + 1, :n - k + 1, :n - k + 1])) for n in (150, 300, 450)]
    old = np.unique(C[:297, :297, :297])
    shell = np.ones(C.shape, bool); shell[:297, :297, :297] = False
    newmask = shell & ~np.isin(C, old)
    idx = np.argwhere(newmask); s = np.sort(idx, axis=1); u, v, w = s.T; d = w - u - v
    out["new_cells"] = int(len(idx)); out["shell_cells"] = int(shell.sum())
    out["new_d_hist"] = {str(b): int(((d >= lo) & (d < hi)).sum()) for b, (lo, hi) in
                         {"d<-100": (-10**9, -100), "-100..-10": (-100, -10), "-10..10": (-10, 10), "10..100": (10, 100), ">=100": (100, 10**9)}.items()}
    out["new_u_hist"] = {b: int(((u >= lo) & (u < hi)).sum()) for b, (lo, hi) in {"u<10": (0, 10), "10..50": (10, 50), "50..150": (50, 150), ">=150": (150, 10**9)}.items()}
    out["new_vu_hist"] = {b: int((((v - u) >= lo) & ((v - u) < hi)).sum()) for b, (lo, hi) in {"v-u<10": (0, 10), "10..50": (10, 50), ">=50": (50, 10**9)}.items()}
    return json.dumps(out)
if __name__ == "__main__":
    R = [json.loads(l) for l in open("raw/cx_300.jsonl")]
    pairs = [(r["S1"], r["S2"]) for r in R if r["cx"][2] != r["cx"][1]]
    with Pool(3) as P, open("raw/big_450.jsonl", "w") as f:
        for line in P.imap(job, pairs): f.write(line + "\n"); f.flush()
    print("done", len(pairs))
