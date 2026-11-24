#!/usr/bin/env python3
"""Counterexample hunt for two-heap double periodicity: all ordered pairs S1 != S2 of
non-empty subsets of {1..N}. Per pair: lead_a3 certificate (or none within AMAX rows),
plus row statistics (max preperiod, max period, and their values in the last rows) so
growth would show. Usage: hunt6.py N AMAX WORKERS > raw/out_hunt<N>.jsonl"""
import sys, json, itertools, time
from multiprocessing import Pool
from lead_a3 import Pair

def job(args):
    S1, S2, amax = args
    t = time.time()
    P = Pair(S1, S2)
    c = P.certify(amax)
    rows = P.rows
    pres = [len(r.pre) for r in rows]; pers = [len(r.cyc) for r in rows]
    k = max(1, len(rows) // 4)
    return dict(S1=S1, S2=S2, cert=c, nrows=len(rows), maxpre=max(pres), maxper=max(pers),
                lastq_maxpre=max(pres[-k:]), lastq_maxper=max(pers[-k:]),
                firstq_maxpre=max(pres[:k]), firstq_maxper=max(pers[:k]), sec=round(time.time() - t, 2))

if __name__ == "__main__":
    N, amax, w = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    subs = [c for r in range(1, N + 1) for c in itertools.combinations(range(1, N + 1), r)]
    jobs = [(a, b, amax) for a in subs for b in subs if a != b]
    # skip pairs already done if resuming
    with Pool(w) as p:
        for r in p.imap_unordered(job, jobs, chunksize=4):
            print(json.dumps(r), flush=True)
