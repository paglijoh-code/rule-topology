#!/usr/bin/env python3
"""why_s3.py N : why wall s3-4-9-10 (p0, B={1,2,3,4}) survives A->B->C exactly for C with 3,7 in C, 1,2 not.
Compares B's rewritten table T'_C over all C <= {1..7} containing 3, and A's start-mode boundary.
Run: nice -n 10 python3 rule_graphs/why_s3.py 4000 > rule_graphs/why_s3_4000.txt"""
import os, sys, itertools
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import numpy as np, graphs, exponent
N = int(sys.argv[1]); A, B = (3, 4, 9, 10), (1, 2, 3, 4)
Cs = [C for r in range(1, 8) for C in itertools.combinations(range(1, 8), r) if 3 in C]
T0 = graphs.solve_graph({"B": B}, {}, N)[("B", None)]
tabs = {}
for C in Cs:
    tabs[C] = graphs.solve_graph({"B": B, "C": C}, {"B": ["C"]}, N)[("B", None)]
surv = [C for C in Cs if 7 in C and 1 not in C and 2 not in C]
ref = tabs[surv[0]]
print("survivor C:", surv)
print("T' identical across survivor C:", [bool((tabs[C] == ref).all()) for C in surv])
same = [C for C in Cs if (tabs[C] == ref).all()]
print("all C (with 3) giving exactly that T':", same)
iu = np.triu_indices(N + 1)
D = (ref != T0)
print("cells where T' differs from plain B:", int(D[iu].sum()), "of", len(iu[0]))
d = (np.nonzero(D)[1] - np.nonzero(D)[0])
print("their offsets b-a: min", d.min(), "max", d.max(), "count by offset (first 12):",
      np.bincount(np.abs(d))[:12].tolist())
# A against T' and against plain B: round times and levels
for name, T in (("edge A->B", T0), ("A->B->C(37)", ref)):
    TA = graphs._node_c(A, np.ascontiguousarray(T == 1), N)
    r, M = exponent.analyse(TA, pmax=400, tail=min(1200, N // 4))
    Tr, Lr = exponent.rounds(M)
    print(name, r["kind"], "alpha", r["alpha"], "bfit", r.get("alpha_bfit"), "rounds", len(Tr))
    print("  T_j", Tr.tolist()[:30]); print("  L_j", Lr.tolist()[:30])
