#!/usr/bin/env python3
"""rule_graph_laws enumeration: algebra of rule graphs via phi(R, T).

  rgenum.py --selftest     run selftests
  rgenum.py all            run E1..E5 (+ N=150 reruns), write rule_graph_laws/raw/*.txt and rule_graph_laws/ENUM_RESULTS.md

Sets of cells are Python ints used as bitsets (bit a*(N+1)+b).  phi(R, T) is
the P-set of ruleset R where every cell of T is forced to be N.
"""
import sys
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
# this file is called rgenum.py: keep its directory off sys.path so stdlib `enum` wins
sys.path = [p for p in sys.path if os.path.abspath(p or ".") != HERE]
import itertools
import random
import time
import zlib
import multiprocessing as mp
from collections import Counter
import numpy as np
sys.path.insert(0, ROOT)
import rulegraph as rg

SEED = 20261122
_TBL = bytes.maketrans(b"\x00\x01", b"01")
_PHI = {}


# ------------------------------------------------------------------ blocks
class Block:
    def __init__(self, name, kind, N, param=None):
        self.name, self.kind, self.N, self.param = name, kind, N, param
        self.key = (N, name)
        self._o = None

    def opts(self):
        if self._o is None:
            N = self.N
            n1 = N + 1
            k = self.kind
            o = []
            for a in range(n1):
                for b in range(n1):
                    L = []
                    if k in ("nim", "wyth"):
                        L += [a2 * n1 + b for a2 in range(a)]
                        L += [a * n1 + b2 for b2 in range(b)]
                        if k == "wyth":
                            L += [(a - t) * n1 + b - t for t in range(1, min(a, b) + 1)]
                    elif k == "euclid":
                        for x, y in rg.options("euclid", a, b):
                            L.append(x * n1 + y)
                    elif k == "sub":
                        for s in self.param:
                            if a >= s:
                                L.append((a - s) * n1 + b)
                            if b >= s:
                                L.append(a * n1 + b - s)
                    elif k == "vec":
                        for x, y in self.param:
                            if a >= x and b >= y:
                                L.append((a - x) * n1 + b - y)
                    o.append(L)
            self._o = o
        return self._o

    def grundy(self):
        o = self.opts()
        g = [0] * len(o)
        for i, L in enumerate(o):
            s = {g[j] for j in L}
            m = 0
            while m in s:
                m += 1
            g[i] = m
        return g


NAMED_SUBS = [tuple(c) for r in range(1, 5) for c in itertools.combinations([1, 2, 3, 4], r)]


def make_named(N):
    B = [Block("nim", "nim", N), Block("wythoff", "wyth", N), Block("euclid", "euclid", N)]
    for S in NAMED_SUBS:
        B.append(Block("Sub{" + ",".join(map(str, S)) + "}", "sub", N, S))
    B.append(Block("Sub{1,2,5,6}", "sub", N, (1, 2, 5, 6)))
    B.append(Block("Sub{1,2,3,4,6}", "sub", N, (1, 2, 3, 4, 6)))
    B.append(Block("empty", "sub", N, ()))
    return B


def make_random(N, n_each=200, seed=SEED):
    """n_each random Sub(S) (S in 1..8, |S| 1..4) and n_each random 2D vector sets.
    Duplicates are possible (only 162 distinct Sub sets exist)."""
    rng = random.Random(seed)
    B = []
    for _ in range(n_each):
        S = tuple(sorted(rng.sample(range(1, 9), rng.randint(1, 4))))
        B.append(Block("rSub{" + ",".join(map(str, S)) + "}", "sub", N, S))
    cells = [(x, y) for x in range(4) for y in range(4) if (x, y) != (0, 0)]
    for _ in range(n_each):
        V = tuple(sorted(rng.sample(cells, rng.randint(1, 4))))
        B.append(Block("rVec" + "".join("(%d,%d)" % v for v in V), "vec", N, V))
    return B


# ---------------------------------------------------------------- core phi
def phi(blk, T=0):
    key = (blk.key, T)
    r = _PHI.get(key)
    if r is not None:
        return r
    N = blk.N
    n1 = N + 1
    M = n1 * n1
    P = bytearray(M)
    Ts = bin(T)[2:].zfill(M)[::-1] if T else None
    k = blk.kind
    if k in ("nim", "wyth"):
        w = k == "wyth"
        rowP = [0] * n1
        colP = [0] * n1
        dg = [0] * (2 * n1)
        i = 0
        for a in range(n1):
            for b in range(n1):
                if ((Ts is None or Ts[i] != "1") and not rowP[a] and not colP[b]
                        and not (w and dg[a - b + N])):
                    P[i] = 1
                    rowP[a] = colP[b] = 1
                    dg[a - b + N] = 1
                i += 1
    else:
        opts = blk.opts()
        for i in range(M):
            if Ts is not None and Ts[i] == "1":
                continue
            for o in opts[i]:
                if P[o]:
                    break
            else:
                P[i] = 1
    res = int(bytes(P[::-1]).translate(_TBL), 2)
    if len(_PHI) > int(1e8 / (M / 8)):
        _PHI.clear()
    _PHI[key] = res
    return res


def low(diff):
    return (diff & -diff).bit_length() - 1


def cell(i, N):
    return "(%d,%d)" % divmod(i, N + 1)


def pc(x):
    return bin(x).count("1")


def eval_acyclic(blocks, adj):
    memo = {}

    def X(v):
        if v not in memo:
            T = 0
            for w in adj.get(v, []):
                T |= X(w)
            memo[v] = phi(blocks[v], T)
        return memo[v]
    return {v: X(v) for v in range(len(blocks))}


def budget_seq(blocks, adj, K):
    """X_0..X_K as lists (per node) of P-set ints."""
    cur = [phi(b, 0) for b in blocks]
    out = [cur]
    for _ in range(K):
        nxt = []
        for v, b in enumerate(blocks):
            T = 0
            for w in adj.get(v, []):
                T |= cur[w]
            nxt.append(phi(b, T))
        cur = nxt
        out.append(cur)
    return out


def loopy(blocks, adj, N):
    """Unlimited pushes: retrograde fixed point; returns per node list of -1/0/1."""
    M = (N + 1) ** 2
    st = [[-1] * M for _ in blocks]
    ops = [b.opts() for b in blocks]
    changed = True
    while changed:
        changed = False
        for v in range(len(blocks)):
            sv, ov, tg = st[v], ops[v], adj.get(v, [])
            for i in range(M):
                if sv[i] != -1:
                    continue
                x = ov[i]
                if any(sv[o] == 1 for o in x) or any(st[w][i] == 1 for w in tg):
                    sv[i] = 0
                    changed = True
                elif all(sv[o] == 0 for o in x) and all(st[w][i] == 0 for w in tg):
                    sv[i] = 1
                    changed = True
    return st


def bits_to_arr(x, N):
    n1 = N + 1
    s = bin(x)[2:].zfill(n1 * n1)[::-1]
    return np.array([c == "1" for c in s]).reshape(n1, n1)


def rg_spec(blk):
    if blk.kind == "nim":
        return "nim"
    if blk.kind == "wyth":
        return "wythoff"
    if blk.kind == "euclid":
        return "euclid"
    n1 = blk.N + 1
    o = blk.opts()
    return lambda a, b: [divmod(j, n1) for j in o[a * n1 + b]]


# ------------------------------------------------------------------- stats
class Stat:
    def __init__(self):
        self.n = self.ok = self.ct = self.sv = self.nv = 0
        self.fail = self.sfail = self.nfail = None

    def add(self, ok, cond=None, diff=0, desc="", N=60):
        self.n += 1
        self.ok += bool(ok)
        c = (low(diff), desc) if diff else (-1, desc)
        if not ok and (self.fail is None or c < self.fail[0]):
            self.fail = (c, "%s %s" % (cell(c[0], N), desc))
        if cond is not None:
            self.ct += bool(cond)
            if cond and not ok:
                self.sv += 1
                if self.sfail is None or c < self.sfail[0]:
                    self.sfail = (c, "%s %s" % (cell(c[0], N), desc))
            if ok and not cond:
                self.nv += 1
                if self.nfail is None or desc < self.nfail[0][1]:
                    self.nfail = (c, desc)


def stat_dict(S):
    return {k: dict(n=s.n, ok=s.ok, ct=s.ct, sv=s.sv, nv=s.nv,
                    fail=s.fail and s.fail[1], sfail=s.sfail and s.sfail[1],
                    nfail=s.nfail and s.nfail[1]) for k, s in S.items()}


def rng_for(tag):
    return random.Random(SEED ^ zlib.crc32(tag.encode()))


def triples(B, limit, rng):
    if len(B) ** 3 <= limit:
        return list(itertools.product(B, repeat=3))
    return [tuple(rng.choice(B) for _ in range(3)) for _ in range(limit)]


# --------------------------------------------------------------------- E1
GRAPHS = {
    "selfloop": (1, {0: [0]}),
    "cycle2": (2, {0: [1], 1: [0]}),
    "triangle": (3, {0: [1], 1: [2], 2: [0]}),
    "complete3": (3, {0: [1, 2], 1: [0, 2], 2: [0, 1]}),
    "cycle2+exit": (3, {0: [1], 1: [0, 2], 2: []}),
}
E1_LIMIT = {"selfloop": 10 ** 6, "cycle2": 441, "triangle": 3000, "complete3": 1500,
            "cycle2+exit": 1500}


def periodic(states, t, pj, nodes):
    L = len(states)
    res = []
    for v in range(nodes):
        xs = [s[v] for s in states]

        def f(k):
            return xs[k] if k < L else xs[t + (k - t) % pj]
        for p in range(1, pj + 1):
            if pj % p == 0 and all(f(k) == f(k + p) for k in range(t, t + pj)):
                break
        k = t - 1
        while k >= 0 and f(k) == f(k + p):
            k -= 1
        res.append((p, k + 1))
    return res


def e1(graph, kind, N=60):
    m, adj = GRAPHS[graph]
    B = make_named(N) if kind == "named" else make_random(N)
    rng = rng_for("e1" + graph + kind)
    if kind == "named":
        tuples = (list(itertools.product(B, repeat=m)) if len(B) ** m <= E1_LIMIT[graph]
                  else [tuple(rng.choice(B) for _ in range(m)) for _ in range(E1_LIMIT[graph])])
    else:
        tuples = ([(b,) for b in B] if m == 1 else
                  [tuple(rng.choice(B) for _ in range(m)) for _ in range(400)])
    per, ons, jp = Counter(), Counter(), Counter()
    ex_p3 = ex_on = None
    lines = []
    for tu in tuples:
        cur = tuple(phi(b, 0) for b in tu)
        seen, states = {}, []
        while cur not in seen:
            seen[cur] = len(states)
            states.append(cur)
            nxt = []
            for v, b in enumerate(tu):
                T = 0
                for w in adj[v]:
                    T |= cur[w]
                nxt.append(phi(b, T))
            cur = tuple(nxt)
        t = seen[cur]
        pj = len(states) - t
        jp[pj] += 1
        res = periodic(states, t, pj, m)
        names = ",".join(b.name for b in tu)
        for v, (p, o) in enumerate(res):
            per[p] += 1
            ons[o] += 1
            lines.append("%s\t%s\tstart=%d\tperiod=%d\tonset=%d" % (graph, names, v, p, o))
            if p > 2 and ex_p3 is None:
                ex_p3 = "%s start=%d period=%d onset=%d" % (names, v, p, o)
            if ex_on is None or o > ex_on[0]:
                ex_on = (o, "%s start=%d period=%d onset=%d" % (names, v, p, o))
    return dict(kind="E1", graph=graph, set=kind, ntuples=len(tuples), per=dict(per),
                ons=dict(ons), jp=dict(jp), ex_p3=ex_p3, ex_on=ex_on and ex_on[1],
                raw=("E1_%s_%s.txt" % (graph.replace("+", "_"), kind), "\n".join(lines) + "\n"))


# --------------------------------------------------------------------- E2
def e2(kind, N=60, nt=None, nrand=200):
    B = make_named(N) if kind == "named" else make_random(N, nrand)
    rng = rng_for("e2" + kind)
    T3 = triples(B, nt or (10 ** 6 if kind == "named" else 3000), rng)
    S = {k: Stat() for k in ("C", "D3", "D2")}
    for r1, r2, r3 in T3:
        P2, P3 = phi(r2, 0), phi(r3, 0)
        A, Bm = phi(r2, P3), phi(r3, P2)
        c123, c132 = phi(r1, A), phi(r1, Bm)
        d = "%s>%s>%s" % (r1.name, r2.name, r3.name)
        S["C"].add(c123 == c132, A == Bm, c123 ^ c132, d, N)
        c12 = phi(r1, P2)
        S["D3"].add(c123 == c12, (P2 & P3) == 0, c123 ^ c12, d, N)
        c13 = phi(r1, P3)
        S["D2"].add(c123 == c13, A == P3, c123 ^ c13, d, N)
    return dict(kind="E2", set=kind, N=N, ntuples=len(T3), stats=stat_dict(S))


# --------------------------------------------------------------------- E3
def e3(kind, N=60, nt=None, nrand=200):
    B = make_named(N) if kind == "named" else make_random(N, nrand)
    rng = rng_for("e3" + kind)
    T3 = triples(B, nt or (10 ** 6 if kind == "named" else 3000), rng)
    S = {k: Stat() for k in ("F1 fork==phi(R1,P2|P3)", "F2 fork<=P(ch12)&P(ch13)",
                              "F3 fork==a chain", "F2b fork<=P(ch12)|P(ch13)",
                              "F2c fork>=P(ch12)&P(ch13)", "J1 join start1==chain(1,3)",
                              "J2 join start2==chain(2,3)")}
    ks = list(S)
    rel = Counter()
    for r1, r2, r3 in T3:
        d = "%s>{%s,%s}" % (r1.name, r2.name, r3.name)
        P2, P3 = phi(r2, 0), phi(r3, 0)
        fork = phi(r1, P2 | P3)
        gf = eval_acyclic([r1, r2, r3], {0: [1, 2]})[0]
        c12, c13 = phi(r1, P2), phi(r1, P3)
        S[ks[0]].add(fork == gf, None, fork ^ gf, d, N)
        S[ks[1]].add(fork & ~(c12 & c13) == 0, None, fork & ~(c12 & c13), d, N)
        S[ks[2]].add(fork == c12 or fork == c13, None, fork ^ c12, d, N)
        S[ks[3]].add(fork & ~(c12 | c13) == 0, None, fork & ~(c12 | c13), d, N)
        S[ks[4]].add((c12 & c13) & ~fork == 0, None, (c12 & c13) & ~fork, d, N)
        rel[(fork == c12, fork == c13, c12 == c13)] += 1
        j = eval_acyclic([r1, r2, r3], {0: [2], 1: [2]})
        dj = "%s>%s<%s" % (r1.name, r3.name, r2.name)
        S[ks[5]].add(j[0] == c13, None, j[0] ^ c13, dj, N)
        c23 = phi(r2, P3)
        S[ks[6]].add(j[1] == c23, None, j[1] ^ c23, dj, N)
    rl = {"fork==ch12:%d,fork==ch13:%d,ch12==ch13:%d" % k: v for k, v in rel.items()}
    return dict(kind="E3", set=kind, N=N, ntuples=len(T3), stats=stat_dict(S), rel=rl)


# --------------------------------------------------------------------- E4
def e4(kind, N=60, nrand=200):
    B = make_named(N) if kind == "named" else make_random(N, nrand)
    K = 8
    S = {k: Stat() for k in ("R->R == R", "R->R->R == R->R", "R->R->R == R",
                              "loop even k == P(R) (k=2..8)", "loop odd k == {G=1} (k=1..7)")}
    ks = list(S)
    for b in B:
        P = phi(b, 0)
        X = [P]
        for _ in range(K):
            X.append(phi(b, X[-1]))
        G1 = 0
        for i, g in enumerate(b.grundy()):
            if g == 1:
                G1 |= 1 << i
        d = b.name
        S[ks[0]].add(X[1] == P, None, X[1] ^ P, d, N)
        S[ks[1]].add(X[2] == X[1], None, X[2] ^ X[1], d, N)
        S[ks[2]].add(X[2] == P, None, X[2] ^ P, d, N)
        ev = [k for k in range(2, K + 1, 2) if X[k] != P]
        S[ks[3]].add(not ev, None, X[ev[0]] ^ P if ev else 0, d + (" k=%d" % ev[0] if ev else ""), N)
        od = [k for k in range(1, K, 2) if X[k] != G1]
        S[ks[4]].add(not od, None, X[od[0]] ^ G1 if od else 0, d + (" k=%d" % od[0] if od else ""), N)
    return dict(kind="E4", set=kind, N=N, ntuples=len(B), stats=stat_dict(S))


# --------------------------------------------------------------------- E5
def e5mono(kind, N=60, nrand=200):
    B = make_named(N) if kind == "named" else make_random(N, nrand)
    rng = rng_for("e5" + kind)
    named = make_named(N)
    if kind == "named":
        cases = [(R, b1, b2) for R in named for b1 in named for b2 in named]
    else:
        cases = [(rng.choice(B), rng.choice(B), rng.choice(B)) for _ in range(3000)]
    cnt = Counter()
    best = None
    for R, b1, b2 in cases:
        T = phi(b1, 0)
        T2 = T | phi(b2, 0)
        if T2 == T:
            cnt["T==T' (skipped)"] += 1
            continue
        U, V = phi(R, T2), phi(R, T)
        if U & ~V == 0:
            cnt["holds: phi(R,T') <= phi(R,T)" + (" (equal)" if U == V else " (strict)")] += 1
        else:
            cnt["FAILS"] += 1
            cnt["  of which phi(R,T) <= phi(R,T')" if V & ~U == 0 else "  of which incomparable"] += 1
            key = (pc(T2), low(U & ~V), R.name, b1.name, b2.name)
            if best is None or key < best:
                best = key
    # tiny exhaustive search: T subset T', |T'| <= 2, cells in {0,1,2}^2, R named
    tiny = None
    cl = [a * (N + 1) + b for a in range(3) for b in range(3)]
    for sz in (1, 2):
        for Tp in itertools.combinations(cl, sz):
            for r in range(sz + 1):
                for T in itertools.combinations(Tp, r):
                    Tm = sum(1 << c for c in T)
                    Tpm = sum(1 << c for c in Tp)
                    for R in named:
                        U, V = phi(R, Tpm), phi(R, Tm)
                        if U & ~V:
                            tiny = (R.name, [divmod(c, N + 1) for c in T],
                                    [divmod(c, N + 1) for c in Tp], cell(low(U & ~V), N))
                            break
                    if tiny:
                        break
                if tiny:
                    break
            if tiny:
                break
        if tiny:
            break
    return dict(kind="E5m", set=kind, N=N, ncases=len(cases), cnt=dict(cnt),
                best=best and "R=%s T=P(%s) T'=T+P(%s) |T'|=%d cell %s" % (
                    best[2], best[3], best[4], best[0], cell(best[1], N)),
                tiny=tiny)


def e5cycle(N=16, nt=2500):
    B = make_named(N)
    rng = rng_for("e5cycle")
    adj = {0: [1], 1: [0, 2], 2: []}
    cnt = [Counter() for _ in range(3)]
    anydraw = [0, 0, 0]
    ex = None
    lines = []
    for _ in range(nt):
        tu = [rng.choice(B) for _ in range(3)]
        st = loopy(tu, adj, N)
        for v in range(3):
            c = Counter(st[v])
            cnt[v].update(c)
            if c[-1]:
                anydraw[v] += 1
        if ex is None and Counter(st[0])[-1] == 0 and Counter(st[1])[-1] == 0 and False:
            ex = tu
        lines.append("%s\tP/N/D start0=%s start1=%s" % (
            ",".join(b.name for b in tu),
            "%d/%d/%d" % tuple(Counter(st[0])[x] for x in (1, 0, -1)),
            "%d/%d/%d" % tuple(Counter(st[1])[x] for x in (1, 0, -1))))
    return dict(kind="E5c", N=N, nt=nt, cnt=[{("P" if k == 1 else "N" if k == 0 else "draw"): v
                                              for k, v in c.items()} for c in cnt],
                anydraw=anydraw, raw=("E5_cycle_exit.txt", "\n".join(lines) + "\n"))


# --------------------------------------------------------------- selftests
def selftest():
    ok = True

    def check(name, cond):
        nonlocal ok
        print(("ok   " if cond else "FAIL ") + name)
        ok &= bool(cond)
    N = 60
    B = {b.name: b for b in make_named(N)}
    n1 = N + 1
    diag = sum(1 << (a * n1 + a) for a in range(n1))
    check("phi(nim, empty) is the diagonal", phi(B["nim"], 0) == diag)
    r = rg.solve({"w": "wythoff"}, {}, N)[("w", None)]
    check("phi(wythoff, empty) matches rulegraph", (bits_to_arr(phi(B["wythoff"], 0), N) == (r == 1)).all())
    for nm in ("euclid", "Sub{1,2}", "Sub{2,3}"):
        r = rg.solve({"x": rg_spec(B[nm])}, {}, 20)[("x", None)]
        b20 = {b.name: b for b in make_named(20)}[nm]
        check("phi(%s, empty) matches rulegraph (N=20)" % nm,
              (bits_to_arr(phi(b20, 0), 20) == (r == 1)).all())
    exp = {(0, 1), (1, 0)} | {(a, a) for a in range(2, N + 1)}
    got = phi(B["nim"], phi(B["wythoff"], 0))
    check("chain nim->wythoff = misere Nim", got == sum(1 << (a * n1 + b) for a, b in exp))
    N30 = 30
    B30 = {b.name: b for b in make_named(N30)}
    bl = [B30["nim"], B30["wythoff"]]
    ref = rg.solve({"n": "nim", "w": "wythoff"}, {"n": ["w"], "w": ["n"]}, N30, budget=4)
    seq = budget_seq(bl, {0: [1], 1: [0]}, 4)
    good = all((bits_to_arr(seq[k][v], N30) == (ref[(m, k)] == 1)).all()
               for k in range(5) for v, m in enumerate(("n", "w")))
    check("budgeted 2-cycle Nim<->Wythoff matches rulegraph.solve, k<=4, N=30", good)
    B14 = make_named(14)
    nw = [B14[0], B14[1]]
    st = loopy(nw, {0: [1], 1: [0]}, 14)
    check("unlimited 2-cycle Nim<->Wythoff: all draws", all(x == -1 for s in st for x in s))
    # loopy vs reference, with exit
    tri = [B14[0], B14[1], B14[2]]
    ad = {0: [1], 1: [0, 2], 2: []}
    st = loopy(tri, ad, 14)
    ref = rg.solve_reference({"a": "nim", "b": "wythoff", "c": "euclid"},
                             {"a": ["b"], "b": ["a", "c"], "c": []}, 14)
    check("loopy fixed point == rulegraph.solve_reference (N=14, cycle+exit)",
          all((np.array(st[v]).reshape(15, 15) == ref[(m, None)]).all() for v, m in enumerate("abc")))
    # fork and chain vs rulegraph.solve (N=14)
    nm14 = {b.name: b for b in B14}
    trio = [nm14["Sub{1,2}"], nm14["wythoff"], nm14["Sub{3}"]]
    ref = rg.solve({"a": rg_spec(trio[0]), "b": "wythoff", "c": rg_spec(trio[2])},
                   {"a": ["b", "c"]}, 14)
    fk = eval_acyclic(trio, {0: [1, 2]})[0]
    check("fork == rulegraph.solve (N=14)", (bits_to_arr(fk, 14) == (ref[("a", None)] == 1)).all())
    ref = rg.solve({"a": "nim", "b": "wythoff", "c": "euclid"}, {"a": ["b"], "b": ["c"]}, 14)
    ch = eval_acyclic(B14[:3], {0: [1], 1: [2]})[0]
    check("chain nim>wythoff>euclid == rulegraph.solve (N=14)", (bits_to_arr(ch, 14) == (ref[("a", None)] == 1)).all())
    print("PASS" if ok else "FAIL")
    return ok


# -------------------------------------------------------------------- main
def fmt_counter(c):
    return ", ".join("%s:%d" % (k, c[k]) for k in sorted(c))


def table(head, rows):
    out = ["| " + " | ".join(head) + " |", "|" + "---|" * len(head)]
    for r in rows:
        out.append("| " + " | ".join(str(x) for x in r) + " |")
    return "\n".join(out) + "\n"


def run_task(t):
    t0 = time.time()
    fn, args = t
    r = fn(*args)
    r["secs"] = round(time.time() - t0, 1)
    return r


def stat_rows(results, laws=None):
    rows = []
    for r in results:
        for k, s in r["stats"].items():
            rows.append([k, r["set"], r["N"], r["ntuples"], s["ok"], s["ct"], s["sv"], s["nv"],
                         s["fail"] or "-", s["sfail"] or "-"])
    return rows


STAT_HEAD = ["law", "blocks", "N", "cases", "law holds", "cond holds", "cond true & law false (suff viol)",
             "law true & cond false (nec viol)", "smallest failure (cell, case)", "smallest suff-viol"]


def main_all():
    t0 = time.time()
    os.makedirs(os.path.join(HERE, "raw"), exist_ok=True)
    tasks = []
    for g in GRAPHS:
        for kd in ("named", "random"):
            tasks.append((e1, (g, kd)))
    for f in (e2, e3):
        tasks.append((f, ("named",)))
        tasks.append((f, ("random",)))
    tasks += [(e4, ("named",)), (e4, ("random",)), (e5mono, ("named",)), (e5mono, ("random",)),
              (e5cycle, ())]
    tasks += [(e2, ("named", 150, 500)), (e2, ("random", 150, 300, 25)),
              (e3, ("named", 150, 500)), (e3, ("random", 150, 300, 25)),
              (e4, ("named", 150)), (e4, ("random", 150, 25))]
    ctx = mp.get_context("fork")
    with ctx.Pool(16) as pool:
        res = pool.map(run_task, tasks, chunksize=1)
    md = ["# rule_graph_laws enumeration results (generated by rule_graph_laws/rgenum.py all)\n",
          "N=60 unless stated. Sets are P-sets over cells (a,b), 0<=a,b<=N. 'named' = nim, wythoff, euclid, "
          "Sub(S) for the 15 nonempty S in {1..4}, Sub{1,2,5,6}, Sub{1,2,3,4,6}, empty (21 blocks). "
          "'random' = 200 random Sub(S) (S in 1..8, |S| 1..4) + 200 random 2D vector sets (1..4 vectors, "
          "coords 0..3), seed %d; duplicates possible.\n" % SEED]
    # E1
    md.append("## E1 budget period\n")
    md.append("Period/onset are exact for the infinite sequence X_k (detected by repeat of the joint state "
              "(X_k(v))_v on the window), not truncated at k=24. Counts are over (tuple, start node) pairs.\n")
    rows = []
    for r in res:
        if r["kind"] != "E1":
            continue
        rows.append([r["graph"], r["set"], r["ntuples"], fmt_counter(r["per"]), fmt_counter(r["ons"]),
                     fmt_counter(r["jp"]), r["ex_p3"] or "none"])
        open(os.path.join(HERE, "raw", r["raw"][0]), "w").write(r["raw"][1])
    md.append(table(["graph", "blocks", "tuples", "period:count", "onset:count", "joint period:count",
                     "first example with period>2"], rows))
    # E2, E3, E4
    for kd, title in (("E2", "E2 commuting / drop-out on chains R1>R2>R3 (C: 123==132, D3: 123==12, D2: 123==13)"),
                      ("E3", "E3 fork R1>{R2,R3} vs chains, and join R1>R3<R2"),
                      ("E4", "E4 idempotence")):
        md.append("\n## %s\n" % title)
        main = [r for r in res if r["kind"] == kd and r["N"] == 60]
        big = [r for r in res if r["kind"] == kd and r["N"] == 150]
        md.append(table(STAT_HEAD, stat_rows(main)))
        if kd == "E3":
            for r in main:
                md.append("fork/chain equality patterns (%s): %s\n" % (r["set"], fmt_counter(r["rel"])))
        if kd == "E4":
            md.append("(E4 has no condition columns; 'law holds' counts blocks.)\n")
        zero = []
        for law in main[0]["stats"]:
            if all((r["stats"][law]["sv"] == 0 if r["stats"][law]["ct"] or kd == "E2" else
                    r["stats"][law]["ok"] == r["stats"][law]["n"]) for r in main):
                zero.append(law)
        md.append("\nZero-violation laws at N=60 (named and random; for E2 means the sufficient condition): "
                  "%s\n" % (zero or "none"))
        md.append("\nRerun at N=150 (named sample / 25 random blocks; smaller samples):\n")
        md.append(table(STAT_HEAD, stat_rows(big)))
        with open(os.path.join(HERE, "raw", "%s.txt" % kd), "w") as f:
            for r in main + big:
                for k, s in r["stats"].items():
                    f.write("%s N=%d %s: %s\n" % (r["set"], r["N"], k, s))
    # E5
    md.append("\n## E5 monotonicity of phi (T = P(B1), T' = T u P(B2))\n")
    rows = []
    raw5 = []
    for r in res:
        if r["kind"] == "E5m":
            rows.append([r["set"], r["ncases"], fmt_counter(r["cnt"]), r["best"] or "none"])
            raw5.append("%s: %s\n  smallest: %s\n  tiny search (T<=T', |T'|<=2, cells in 0..2): %s\n" % (
                r["set"], r["cnt"], r["best"], r["tiny"]))
    md.append(table(["R,B1,B2 from", "cases (R,T,T')", "outcome counts", "smallest failing (by |T'|)"], rows))
    for r in res:
        if r["kind"] == "E5m":
            md.append("Smallest hand-size counterexample (%s run; T<=T', |T'|<=2, cells in 0..2): %s\n" % (
                r["set"], r["tiny"]))
    open(os.path.join(HERE, "raw", "E5_monotone.txt"), "w").write("".join(raw5))
    for r in res:
        if r["kind"] == "E5c":
            md.append("\n### E5 cycle R1<->R2, R2->R3 (unlimited pushes), named blocks, N=%d, %d random "
                      "ordered triples\n" % (r["N"], r["nt"]))
            md.append(table(["start node", "cells P", "cells N", "cells draw", "triples with >=1 draw"],
                            [["R%d" % (v + 1), r["cnt"][v].get("P", 0), r["cnt"][v].get("N", 0),
                              r["cnt"][v].get("draw", 0), r["anydraw"][v]] for v in range(3)]))
            open(os.path.join(HERE, "raw", r["raw"][0]), "w").write(r["raw"][1])
    md.append("\nTotal wall time %.0fs (parallel); per task secs: %s\n" % (
        time.time() - t0, ", ".join("%s/%s/%s:%s" % (r["kind"], r.get("set", r.get("graph", "")),
                                                      r.get("N", ""), r["secs"]) for r in res)))
    open(os.path.join(HERE, "ENUM_RESULTS.md"), "w").write("\n".join(md))
    print("done in %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(0 if selftest() else 1)
    if "all" in sys.argv:
        main_all()
    else:
        print(__doc__)
