#!/usr/bin/env python3
"""mscan2.py N IN.jsonl OUT.jsonl : stage 2 of mscan. Rechecks every growing/linear/slow pair of IN at N with
the census settings (exponent.analyse pmax 400, tail min(1200, N/4)). Resumable, one process, run under nice:
  nice -n 10 env OMP_NUM_THREADS=1 python3 rule_graphs/mscan2.py 4000 rule_graphs/mscan1500.jsonl rule_graphs/mscan4000.jsonl"""
import os, sys, json
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent
N, IN, OUT = int(sys.argv[1]), sys.argv[2], sys.argv[3]
rows = [json.loads(l) for l in open(IN)]
rows = [r for r in rows if r["kind"] in ("growing", "linear", "slow")]
done = {(json.loads(l)["sig_id"], tuple(json.loads(l)["S1"])) for l in open(OUT)} if os.path.exists(OUT) else set()
rows.sort(key=lambda r: r["sig_id"]); cur = None
for r in rows:
    if (r["sig_id"], tuple(r["S1"])) in done: continue
    if cur != r["sig_id"]:
        T = graphs.solve_graph({"B": tuple(r["B"]), "C": tuple(r["C"])}, {"B": ["C"]}, N)[("B", None)]
        push = np.ascontiguousarray(T == 1); cur = r["sig_id"]
    a, M = exponent.analyse(graphs._node_c(tuple(r["S1"]), push, N), pmax=400, tail=min(1200, N // 4))
    out = {k: a[k] for k in ("kind", "alpha", "lo", "hi", "n_rounds", "M_end", "alpha_bfit", "bad_rows", "rounds_T") if k in a}
    out.update({k: r[k] for k in ("sig_id", "S1", "B", "C", "pre", "per", "classes")}, kind1500=r["kind"])
    with open(OUT, "a") as f: f.write(json.dumps(out) + "\n")
print("done", flush=True)
