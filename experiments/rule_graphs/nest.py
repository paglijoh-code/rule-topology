#!/usr/bin/env python3
"""nest.py : does nesting nest the glider?  For the two N=16000 sub-sqrt survivors of the census
(pre|s1-2-5-9|1467 and |12356) prepend one more node D (D->C->A->B) and compare the round times of the
root table with the depth-2 table.  nice -n 10 env OMP_NUM_THREADS=1 python3 rule_graphs/nest.py [N] > rule_graphs/nest.jsonl"""
import os, sys, json, gc
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
import numpy as np, graphs, exponent
N = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
A, B = (1, 2, 5, 9), tuple(range(1, 9))
for Cn in ((1, 4, 6, 7), (1, 2, 3, 5, 6)):
    for D in (None, (1,), (2,), (3,), (7,), Cn, (1, 2, 3, 4, 5, 6, 7)):
        S = {"C": Cn, "A": A, "B": B}
        G = {"C": ["A"], "A": ["B"]}
        root = "C"
        if D is not None:
            S["D"] = D; G["D"] = ["C"]; root = "D"
        T = graphs.solve_graph(S, G, N)[(root, None)]
        r, M = exponent.analyse(T, pmax=400, tail=min(1200, N // 4))
        Tt, Ll = exponent.rounds(M)
        print(json.dumps(dict(C=Cn, D=D, N=N, kind=r["kind"], alpha=r["alpha"], n_rounds=r["n_rounds"], M_end=r["M_end"],
                              T=[int(t) for t in Tt[:30]], L=[int(l) for l in Ll[:30]])), flush=True)
        del T; gc.collect()
