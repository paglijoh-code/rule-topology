#!/usr/bin/env python3
"""mscan.py N OUT.jsonl [DEADLINE_S] : stage-1 wall scan of S1 against rewritten target tables.

Targets: the 91 distinct matching-form tables T' (B's table with a push to C) found in the A->B->C chains
of census4000.jsonl (signature.py / signature2.py). One representative (B, C) per signature, from
rule_graphs/msig.json. Each target table is recomputed at N.
S1: every nonempty subset of {1..8} (255) plus the 28 wall sets of census_10/walls_exact.jsonl.
For each (S1, target): start-mode table of A in the edge A->T', analysed by exponent.analyse
(pmax 200, tail 400). Resumable; one process; run under nice.
  nice -n 10 env OMP_NUM_THREADS=1 python3 rule_graphs/mscan.py 1500 rule_graphs/mscan1500.jsonl 3000
"""
import os, sys, json, time, itertools, resource
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent

N = int(sys.argv[1]); OUT = sys.argv[2]
deadline = time.time() + (float(sys.argv[3]) if len(sys.argv) > 3 else 3000)

reps = {}
for B, C, sg in json.load(open(os.path.join(H, "msig.json"))):
    if sg is not None:
        reps.setdefault(json.dumps(sg), (tuple(B), tuple(C), sg))
S1s = [s for r in range(1, 9) for s in itertools.combinations(range(1, 9), r)]
walls = [tuple(w["S1"]) for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl")))
         if w["S2_example"]]
S1s += [w for w in dict.fromkeys(walls) if w not in S1s]

done = set()
if os.path.exists(OUT):
    done = {(json.loads(l)["sig_id"], tuple(json.loads(l)["S1"])) for l in open(OUT)}
print(len(reps), "targets x", len(S1s), "S1 =", len(reps) * len(S1s), "jobs;", len(done), "done", flush=True)
n = 0
for sid, (key, (B, C, sg)) in enumerate(sorted(reps.items())):
    todo = [s for s in S1s if (sid, s) not in done]
    if not todo:
        continue
    T = graphs.solve_graph({"B": B, "C": C}, {"B": ["C"]}, N)[("B", None)]
    push = np.ascontiguousarray(T == 1)
    for S1 in todo:
        if time.time() > deadline:
            print(f"deadline; wrote {n}", flush=True); sys.exit(0)
        t0 = time.time()
        TA = graphs._node_c(S1, push, N)
        r, M = exponent.analyse(TA, pmax=200, tail=400)
        out = {k: r[k] for k in ("kind", "alpha", "n_rounds", "M_end", "alpha_bfit", "bad_rows") if k in r}
        out.update(sig_id=sid, S1=list(S1), B=list(B), C=list(C), pre=sg[0], per=sg[1], classes=sg[2],
                   s=round(time.time() - t0, 3))
        with open(OUT, "a") as f:
            f.write(json.dumps(out) + "\n")
        n += 1
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20
    if rss > 2500:
        print("RSS too high, stopping", rss); break
print(f"wrote {n}", flush=True)
