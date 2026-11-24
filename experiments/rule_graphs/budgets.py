#!/usr/bin/env python3
"""budgets.py : push budgets 1..10 on the 2-cycle A<->B for the 28 walls with an example B.

For each wall and budget k, the start-mode table T_k = table (A, k pushes left) is compared exactly
with the plain A game (no pushes), the one-push edge A->B, and T_{k-2}, then analysed for a boundary.
Run: nice -n 10 python3 rule_graphs/budgets.py 4000 rule_graphs/budgets4000.jsonl
"""
import os, sys, json, gc
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
import numpy as np
import graphs, exponent

N, OUT = int(sys.argv[1]), sys.argv[2]
KMAX = 10
walls = [json.loads(l) for l in open(os.path.join(H, "..", "census_10", "walls_exact.jsonl"))]
walls = [w for w in walls if w["S2_example"]]
with open(OUT, "w") as f:
    for w in walls:
        A, B, tag = tuple(w["S1"]), tuple(w["S2_example"]), w["tag"]
        plain = graphs.solve_graph({"A": A}, {}, N)[("A", None)]
        edge = graphs.solve_graph({"A": A, "B": B}, {"A": ["B"]}, N)[("A", None)]
        res = graphs.solve_graph({"A": A, "B": B}, {"A": ["B"], "B": ["A"]}, N, KMAX)
        T = {k: res[("A", k)] for k in range(KMAX + 1)}
        for k in range(1, KMAX + 1):
            r, _ = exponent.analyse(T[k], pmax=400, tail=min(1200, N // 4))
            rec = dict(wall=tag, k=k, kind=r["kind"], alpha=r["alpha"], n_rounds=r.get("n_rounds"),
                       eq_plain=bool((T[k] == plain).all()), eq_edge=bool((T[k] == edge).all()),
                       eq_k_minus_2=bool(k >= 2 and (T[k] == T[k - 2]).all()),
                       diff_edge=int((T[k] != edge).sum()), diff_plain=int((T[k] != plain).sum()))
            f.write(json.dumps(rec) + "\n")
        f.flush()
        print(tag, " ".join(f"{k}:{'E' if (T[k]==edge).all() else 'P' if (T[k]==plain).all() else '?'}" for k in range(1, KMAX + 1)), flush=True)
        del res, T; gc.collect()
