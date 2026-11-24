#!/usr/bin/env python3
"""Lead A, wider window: rows of two-heap one-push subtraction games (COMPUTED, NOT PROVED).

Game Sub(S1) -push-> Sub(S2), shared mode, push costs the turn. Two heaps a <= b, d = b - a.
Row a = the sequence d -> outcome(a, a+d). For each pair we find, per row, the eventual
period p_a and preperiod T_a, then ask whether rows are eventually periodic in a.
Usage: lead_a2.py --selftest | --rows N AMAX | --one S1 S2 N
"""
import sys, itertools, json
from leads import sg_seq, solve_k, SUBSETS

def solve2(S1, S2, N):
    """P[a][b] (1 = P) for 0 <= a,b <= N; plain loops, symmetric."""
    g = sg_seq(S2, N)
    S1 = sorted(S1)
    P = [[0] * (N + 1) for _ in range(N + 1)]
    for a in range(N + 1):
        Pa = P[a]
        for b in range(a, N + 1):
            if g[a] ^ g[b] == 0:
                v = 0
            else:
                v = 1
                for s in S1:
                    if (s <= a and P[a - s][b]) or (s <= b and P[a][b - s]):
                        v = 0; break  # rows < a are complete and P is filled symmetrically
            Pa[b] = v
            P[b][a] = v
    return P

def per_pre(seq, pmax):
    """Smallest period p <= pmax (then smallest preperiod T) with seq[i] = seq[i+p] for all
    i >= T, requiring the periodic tail to cover at least 4 periods and 60 terms."""
    n = len(seq)
    for p in range(1, pmax + 1):
        # largest i with seq[i] != seq[i+p]
        last = -1
        for i in range(n - p - 1, -1, -1):
            if seq[i] != seq[i + p]:
                last = i; break
        T = last + 1
        if n - T >= max(4 * p, 60):
            return p, T
    return None

def rows_report(S1, S2, N, AMAX, pmax=60):
    P = solve2(S1, S2, N)
    rows = []
    for a in range(AMAX + 1):
        seq = [P[a][a + d] for d in range(N - a + 1)]
        rows.append(per_pre(seq, pmax))
    return P, rows

def a_periodicity(P, N, AMAX, Tcap):
    """Smallest (q, A0) with q <= 60: rows a and a+q agree for d in [Tcap, N-a-q] whenever a >= A0."""
    best = None
    for q in range(1, 61):
        bad = -1
        for a in range(AMAX - q, -1, -1):
            if any(P[a][a + d] != P[a + q][a + q + d] for d in range(Tcap, N - a - q + 1)):
                bad = a; break
        A0 = bad + 1
        if A0 <= AMAX - 2 * q - 10:
            if best is None or (A0, q) < (best[1], best[0]):
                best = (q, A0)
            if A0 == 0:
                break
    return best

def selftest():
    for S1, S2 in [((1, 2), (1, 2, 3)), ((1,), (1, 2)), ((1, 3), (1, 4)), ((3,), (2,))]:
        P = solve2(set(S1), set(S2), 40)
        Q = solve_k(set(S1), set(S2), 2, 40)
        for a in range(41):
            for b in range(41):
                if P[a][b] != Q[a, b]:
                    print("FAIL", S1, S2, a, b); sys.exit(1)
    print("PASS (solve2 == leads.solve_k on 4 pairs, heaps <= 40)")

if __name__ == "__main__":
    if sys.argv[1] == "--selftest":
        selftest()
    elif sys.argv[1] == "--rows":
        N, AMAX = int(sys.argv[2]), int(sys.argv[3])
        fails = set(json.load(open("raw/h1_fails.json")))
        for S1 in SUBSETS:
            for S2 in SUBSETS:
                if S1 == S2: continue
                P, rows = rows_report(set(S1), set(S2), N, AMAX)
                ps = [r[0] if r else None for r in rows]
                Ts = [r[1] if r else None for r in rows]
                Tok = [t for t in Ts if t is not None]
                Tcap = max(Tok) if Tok else 0
                ap = a_periodicity(P, N, AMAX, min(Tcap, 200))
                tag = "FAIL41" if repr((S1, S2)) in fails else "fit169"
                print(json.dumps({"S1": S1, "S2": S2, "tag": tag, "p": ps, "T": Ts, "aper": ap}), flush=True)
    elif sys.argv[1] == "--one":
        S1 = tuple(int(x) for x in sys.argv[2].split(",")); S2 = tuple(int(x) for x in sys.argv[3].split(","))
        N = int(sys.argv[4])
        P, rows = rows_report(set(S1), set(S2), N, min(N // 2, 120))
        for a, r in enumerate(rows):
            print(a, r)
