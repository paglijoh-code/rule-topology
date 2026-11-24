#!/usr/bin/env python3
"""Two leads on push-the-button subtraction games (computed, not proved).

Lead A: multi-heap outcomes of Sub(S1) -push-> Sub(S2); hypotheses H1-H3.
Lead B: does the zero-test of thesis Lemma 89 nest for a chain of two pushes?

Usage: leads.py --selftest | --A | --B
Everything is impartial normal play; a push costs the turn and changes the
ruleset of all heaps at once.
"""
import sys
import itertools
from functools import lru_cache
from math import lcm
import numpy as np

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- Lead A
def sg_seq(S, n):
    g = []
    for h in range(n + 1):
        opts = {g[h - s] for s in S if s <= h}
        m = 0
        while m in opts:
            m += 1
        g.append(m)
    return g


def sg_period(S, n=400):
    g = sg_seq(S, n)
    for p in range(1, 100):
        if all(g[i] == g[i + p] for i in range(100, n - p)):
            return p
    return None


def solve_k(S1, S2, k, N):
    """Outcome array (1 = P, 0 = N) for k heaps, each size 0..N, mode 0 = Sub(S1)
    with one push to Sub(S2). Heap slots are ordered; zero heaps allowed."""
    g2 = sg_seq(S2, N)
    shape = (N + 1,) * k
    out = np.zeros(shape, dtype=np.int8)
    for pos in itertools.product(range(N + 1), repeat=k):  # lexicographic: options come earlier
        x = 0
        for h in pos:
            x ^= g2[h]
        win = (x == 0)
        if not win:
            for i, h in enumerate(pos):
                for s in S1:
                    if s <= h:
                        q = pos[:i] + (h - s,) + pos[i + 1:]
                        if out[q] == 1:
                            win = True
                            break
                if win:
                    break
        out[pos] = 0 if win else 1
    return out


def thm98_pred(heaps):
    """Theorem 98 as stated; heaps = tuple of sizes (zero-size heaps are dropped)."""
    h = [x for x in heaps if x]  # zero heaps are absent heaps
    if h and len(h) % 2 == 0:
        m = min(h)
        h.remove(m)
        h = [x - m for x in h]
    n1 = sum(1 for x in h if x % 3 == 1)
    n2 = sum(1 for x in h if x % 3 == 2)
    return (n1 % 2 == 1) and (n2 % 2 == 0)


def selftest_thm98():
    for k, N in ((1, 80), (2, 80), (3, 40)):
        out = solve_k({1}, {1, 2}, k, N)
        for pos in itertools.product(range(N + 1), repeat=k):
            if (out[pos] == 1) != thm98_pred(pos):
                return False, (k, pos)
    return True, None


SUBSETS = [tuple(c) for r in range(1, 5) for c in itertools.combinations([1, 2, 3, 4], r)]


def fit_h1(P2, N, qmax=12, pmax=24, tmax=30):
    """Smallest (q,p,T) ordered by (q*p, T, q): outcome for a<=b, d=b-a>=T depends only on
    (a mod q, d mod p). P2[a][b] array of outcomes."""
    A, B = np.meshgrid(np.arange(N + 1), np.arange(N + 1), indexing="ij")
    m = A <= B
    a = A[m]
    d = (B - A)[m]
    o = P2[m].astype(np.int64)
    cands = sorted(((q * p, q, p) for q in range(1, qmax + 1) for p in range(1, pmax + 1)))
    best = None
    for qp, q, p in cands:
        if best and qp > best[0]:
            break
        key = (a % q) * p + (d % p)
        for T in range(0, tmax + 1):
            sel = d >= T
            tot = np.bincount(key[sel], minlength=q * p)
            ones = np.bincount(key[sel], weights=o[sel], minlength=q * p)
            if not np.any((ones > 0) & (ones < tot)):
                if best is None or (qp, T, q) < (best[0], best[3], best[1]):
                    best = (qp, q, p, T)
                break
    return None if best is None else (best[1], best[2], best[3])


def fit_h2(P2, N, a0max=20):
    """Smallest a0 such that for a>=a0 the outcome depends only on d (a<=b<=N)."""
    for a0 in range(a0max + 1):
        f = {}
        ok = True
        for a in range(a0, N + 1):
            for b in range(a, N + 1):
                d = b - a
                v = int(P2[a, b])
                if f.setdefault(d, v) != v:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return a0
    return None


def fit_h3(P3, N, qmax=6, pmax=12, tmax=10, a0max=3, min_obs=3.0):
    """a<=b<=c. outcome depends only on (a mod q, (b-a) mod p, (c-a) mod p) for b-a>=T and a>=A0
    (the a>=A0 clause is needed because zero heaps are absent heaps; reported as a 4th number).
    Non-vacuity: mean observations per occupied key >= min_obs. Returns (q, p, T, A0)."""
    idx = np.array([(a, b, c) for a in range(N + 1) for b in range(a, N + 1) for c in range(b, N + 1)])
    a, b, c = idx[:, 0], idx[:, 1], idx[:, 2]
    o = P3[a, b, c].astype(np.int64)
    e, f = b - a, c - a
    cands = sorted(((q * p * p, q, p) for q in range(1, qmax + 1) for p in range(1, pmax + 1)))
    best = None
    for cost, q, p in cands:
        if best and cost > best[0]:
            break
        key = ((a % q) * p + (e % p)) * p + (f % p)
        for T in range(0, tmax + 1):
            for A0 in range(0, a0max + 1):
                sel = (e >= T) & (a >= A0)
                tot = np.bincount(key[sel], minlength=q * p * p)
                ones = np.bincount(key[sel], weights=o[sel], minlength=q * p * p)
                if np.any((ones > 0) & (ones < tot)):
                    continue
                occ = (tot > 0).sum()
                if occ == 0 or sel.sum() / occ < min_obs:
                    continue
                cand = (cost, T + A0, q, p, T, A0)
                if best is None or cand[:3] < best[:3]:
                    best = cand
                break
    return None if best is None else best[2:]


def run_A():
    N2, N3 = 80, 40
    rows = []
    for S1 in SUBSETS:
        for S2 in SUBSETS:
            if S1 == S2:
                continue
            P2 = solve_k(set(S1), set(S2), 2, N2)
            P3 = solve_k(set(S1), set(S2), 3, N3)
            h1 = fit_h1(P2, N2)
            h2 = fit_h2(P2, N2)
            h3 = fit_h3(P3, N3)
            per = (sg_period(S1), sg_period(S2))
            rows.append((S1, S2, h1, h2, h3, per))
            print(f"{S1} -> {S2}  H1={h1}  H2a0={h2}  H3={h3}  sgperiods={per}", flush=True)
    # spot check the stated formula S1={1,2},S2={1,2,3}
    P2 = solve_k({1, 2}, {1, 2, 3}, 2, N2)
    okf = all((P2[a, b] == 1) == (b - a == 2 or (b - a >= 5 and (b - a) % 4 == 1))
              for a in range(1, N2 + 1) for b in range(a, N2 + 1))
    print("formula check ({1,2}->{1,2,3}, a>=1, 2 heaps, a<=b<=80):", okf)
    n = len(rows)
    n1 = sum(r[2] is not None for r in rows)
    n2 = sum(r[3] is not None for r in rows)
    n3 = sum(r[4] is not None for r in rows)
    print(f"\npairs={n}  H1 holds={n1}  H2 holds={n2}  H3 holds={n3}")
    print("H1 FAIL:", [(r[0], r[1]) for r in rows if r[2] is None])
    print("H2 no:", [(r[0], r[1]) for r in rows if r[3] is None])
    print("H3 FAIL:", [(r[0], r[1]) for r in rows if r[4] is None])
    # generality: does p divide lcm of single-ruleset SG periods, q?
    pdiv = [(r[0], r[1], r[2], r[5]) for r in rows if r[2] and r[5][0] and r[5][1]
            and lcm(r[5][0], r[5][1]) % r[2][1] != 0]
    print("H1 fits whose p does not divide lcm(sg period S1, sg period S2):", pdiv)
    return rows


# ---------------------------------------------------------------- Lead B
def make_opts(S):
    @lru_cache(maxsize=None)
    def opts(ms):
        out = set()
        for h in set(ms):
            for s in S:
                if s <= h:
                    l = list(ms)
                    l.remove(h)
                    if h - s:
                        l.append(h - s)
                    out.add(tuple(sorted(l)))
        return tuple(out)
    return opts


class Triple:
    def __init__(self, S0, S1, S2):
        self.S = (S0, S1, S2)
        self.opts = [make_opts(S) for S in self.S]
        self.g2 = sg_seq(S2, 40)
        self.o = {}
        self.L = {}
        self.Nn = {}

    def outcome(self, m, ms):
        """1 = P, 0 = N, memoised on sorted nonzero heap tuples."""
        k = (m, ms)
        r = self.o.get(k)
        if r is not None:
            return r
        win = False
        if m < 2 and self.outcome(m + 1, ms) == 1:
            win = True
        if not win:
            for q in self.opts[m](ms):
                if self.outcome(m, q) == 1:
                    win = True
                    break
        r = 0 if win else 1
        self.o[k] = r
        return r

    def sg_xor(self, ms):
        x = 0
        for h in ms:
            x ^= self.g2[h]
        return x

    def Lz(self, ms):
        """Lemma 89 test for the one-push game (mode 1 -> 2) on multiset ms."""
        r = self.L.get(ms)
        if r is not None:
            return r
        r = (self.sg_xor(ms) == 0) and all(
            any(self.Lz(q2) for q2 in self.opts[1](q1)) for q1 in self.opts[1](ms))
        self.L[ms] = r
        return r

    def N(self, ms):
        r = self.Nn.get(ms)
        if r is not None:
            return r
        r = self.Lz(ms) and all(
            any(self.N(q2) for q2 in self.opts[0](q1)) for q1 in self.opts[0](ms))
        self.Nn[ms] = r
        return r


def multisets(maxn, maxh):
    out = []
    for n in range(maxn + 1):
        out += list(itertools.combinations_with_replacement(range(1, maxh + 1), n))
    return out


def plain_outcome(S, m, pos):
    """Independent plain recursive solver (ordered tuples, zeros kept, no memo)."""
    if m < 2 and plain_outcome(S, m + 1, pos) == 1:
        return 0
    for i, h in enumerate(pos):
        for s in S[m]:
            if s <= h and plain_outcome(S, m, pos[:i] + (h - s,) + pos[i + 1:]) == 1:
                return 0
    return 1


def selftest_solver():
    S = ({1, 2}, {1}, {1, 2, 3})
    T = Triple(*S)
    for k in range(1, 4):
        for pos in itertools.product(range(7), repeat=k):
            ms = tuple(sorted(x for x in pos if x))
            for m in range(3):
                if plain_outcome(S, m, pos) != T.outcome(m, ms):
                    return False, (m, pos)
    return True, None


TRIPLES = [({1, 2}, {1}, {1, 2, 3}), ({1}, {1, 2}, {1, 2, 3}), ({1, 2, 3}, {1, 2}, {1}),
           ({1, 2}, {1, 2, 3}, {1}), ({1, 3}, {1, 2}, {1}), ({2, 3}, {1}, {1, 2})]


def run_B():
    Gs = multisets(4, 10)
    Cs = multisets(3, 12)
    for S in TRIPLES:
        T = Triple(*S)
        nN = 0
        emp = 0
        bad = []
        n_false_unref = 0
        sym_fail = 0
        for G in Gs:
            n = T.N(G)
            nN += n
            refut = None
            for C in Cs:
                U = tuple(sorted(G + C))
                if T.outcome(0, U) != T.outcome(0, C):
                    refut = C
                    break
            if refut is None:
                emp += 1
            if n and refut is not None:
                bad.append((G, refut))
            if (not n) and refut is None:
                n_false_unref += 1
            if not T.N(tuple(sorted(G + G))):
                sym_fail += 1
        # empirical zero-equivalent that fail N
        print(f"triple {[sorted(s) for s in S]}: #G={len(Gs)} N-true={nN} emp-zero={emp} "
              f"N-true-but-refuted={len(bad)} N-false-not-refuted={n_false_unref} GG-fails-N={sym_fail}")
        if bad:
            bad.sort(key=lambda x: (sum(x[0]), len(x[0]), x[0]))
            G, C = bad[0]
            U = tuple(sorted(G + C))
            ordered = tuple(G + C)
            Sd = tuple(S)
            p1 = plain_outcome(Sd, 0, ordered) if sum(ordered) <= 22 else None
            p2 = plain_outcome(Sd, 0, C) if sum(C) <= 22 else None
            print(f"  smallest counterexample G={G} context C={C}: memo o(G+C)={T.outcome(0, U)}, o(C)={T.outcome(0, C)}"
                  f"; plain solver o(G+C)={p1}, o(C)={p2}  (1=P,0=N)")
            print("  next 5:", bad[1:6])
        # an example of the other direction for context
        sys.stdout.flush()


def selftest():
    ok1, w1 = selftest_thm98()
    ok2, w2 = selftest_solver()
    if ok1 and ok2:
        print("PASS (Theorem 98 on 1,2,3 heaps; memoised solver == plain recursive solver)")
    else:
        print("FAIL", w1, w2)
        sys.exit(1)


if __name__ == "__main__":
    a = sys.argv[1:]
    if "--selftest" in a:
        selftest()
    elif "--A" in a:
        run_A()
    elif "--B" in a:
        run_B()
    else:
        print(__doc__)
