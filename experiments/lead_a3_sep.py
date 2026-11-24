"""What separates the 41 H1 failures: minimal tail laws from the exact certificates."""
import json, sys
from math import lcm
from lead_a3 import Pair, SUBSETS

def analyse(S1, S2, Tcap=30):
    P = Pair(S1, S2); c = P.certify()
    A0c, qc = c["A0"], c["q"]
    def row(a):
        if a >= A0c + qc: a = A0c + (a - A0c) % qc
        return P.rows[a]
    L = lcm(*[len(P.rows[i].cyc) for i in range(len(P.rows))])
    span = max(len(r.pre) for r in P.rows) + L
    def agree(a, b, T):
        ra, rb = row(a), row(b)
        return all(ra(d) == rb(d) for d in range(T, T + span + 1))
    def law(A0, q, T):
        return all(agree(a, a + q, T) for a in range(A0, max(A0, A0c) + lcm(q, qc) + qc))
    def minq(A0, T, qmax=200):
        return next((q for q in range(1, qmax + 1) if law(A0, q, T)), None)
    q0 = minq(0, Tcap)                       # old H1: law from a = 0, tail d >= 30
    qT0 = minq(0, 0)                         # law from a = 0, whole rows
    qfree = minq(60, 0)                      # smallest eventual period in a (exact rows)
    A0free = next(A for A in range(0, 61) if law(A, qfree, 0))
    p = lcm(*[len(row(a).cyc) for a in range(A0free, A0free + qfree)])
    return dict(q_from0_T30=q0, q_from0_T0=qT0, q_eventual=qfree, A0=A0free, p=p, gper=P.gper,
                maxpre=max(len(r.pre) for r in P.rows))

fails = set(json.load(open("raw/h1_fails.json")))
for S1 in SUBSETS:
    for S2 in SUBSETS:
        if S1 == S2: continue
        r = analyse(S1, S2)
        r.update(S1=S1, S2=S2, tag="FAIL41" if repr((S1, S2)) in fails else "fit169")
        print(json.dumps(r), flush=True)
