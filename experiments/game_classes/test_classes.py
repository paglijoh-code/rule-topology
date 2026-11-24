#!/usr/bin/env python3
"""game_classes validation: `nice -n 10 python3 game_classes/test_classes.py` (about 15 s, one process)."""
import functools
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import classify as C  # noqa: E402
import fast as F  # noqa: E402
import games as G  # noqa: E402

PHI = (1 + 5 ** 0.5) / 2
ok_all = True


def check(name, cond, extra=""):
    global ok_all
    print(("ok   " if cond else "FAIL ") + name + (" | " + str(extra) if extra else ""))
    ok_all &= bool(cond)


def pset(T, lo=0):
    return {(a, b) for a in range(lo, T.shape[0]) for b in range(lo, T.shape[1]) if T[a, b] == 1}


def brute_misere(game, N):
    """Independent memoised recursion: mover with no move wins; else wins iff some option loses."""
    @functools.lru_cache(None)
    def win(a, b):
        o = game(a, b)
        return True if not o else any(not win(x, y) for x, y in o)
    T = np.zeros((N + 1, N + 1), dtype=np.int8)
    for a in range(N + 1):
        for b in range(N + 1):
            T[a, b] = 0 if win(a, b) else 1
    return T


# 1. subtraction {1..k}: P iff a = b mod k+1 -> stripes with period k+1
for k in (2, 5, 9):
    N = 200
    T = G.normal_table(G.subtraction(range(1, k + 1)), N)
    exact = all((T[a, b] == 1) == ((a - b) % (k + 1) == 0) for a in range(N + 1) for b in range(N + 1))
    r = C.classify(T)
    check(f"subtraction {{1..{k}}}: P iff a=b mod {k + 1}", exact)
    check(f"subtraction {{1..{k}}} -> stripes, period {k + 1}",
          r["cls"] == "stripes" and r["detail"]["stripes"]["shifts"].get("a") == k + 1, (r["cls"], r["conf"], C.summary(r)))

# 2. Nim -> line of slope 1
r = C.classify(G.normal_table(G.nim(), 300), G.grundy_table(G.nim(), 300))
check("Nim -> lines, slope 1", r["cls"] == "lines" and r["detail"]["lines"]["slopes"] == [1.0],
      (r["cls"], r["conf"], C.summary(r), "grundy scaling %.2f" % r["detail"]["grundy_scaling"]))

# 3. Wythoff -> two lines, slopes phi and 1/phi
r = C.classify(G.normal_table(G.wythoff(), 600))
sl = r["detail"]["lines"].get("slopes", [])
check("Wythoff -> lines, slopes 1/phi and phi",
      r["cls"] == "lines" and len(sl) == 2 and abs(sl[0] - 1 / PHI) < 0.01 and abs(sl[1] - PHI) < 0.01,
      (r["cls"], r["conf"], sl))

# 4. Euclid -> cone with slopes phi, 1/phi; P = {a<b<phi a} and mirror (a, b >= 1)
N = 300
T = G.normal_table(G.euclid(), N)
exp = {(a, b) for a in range(1, N + 1) for b in range(1, N + 1)
       if (a < b and b < PHI * a) or (b < a and a < PHI * b)}
check("Euclid P (a,b>=1) = {a<b<phi a} u mirror (N=300)", pset(T, 1) == exp)
check("Euclid: pile-0 positions are terminal, hence P", all(T[0, b] == 1 and T[b, 0] == 1 for b in range(N + 1)))
r = C.classify(G.normal_table(G.euclid(), 600))
sl = r["detail"]["cone"].get("slopes", [])
check("Euclid -> cone, slopes 1/phi and phi",
      r["cls"] == "cone" and len(sl) == 2 and abs(sl[0] - 1 / PHI) < 0.03 and abs(sl[1] - PHI) < 0.03,
      (r["cls"], r["conf"], sl))

# 5. Nim (+) Wythoff by push: P = {(0,1),(1,0),(k,k): k>=2}
N = 60
T = G.push_table(G.nim(), G.wythoff(), N)
exp = {(0, 1), (1, 0)} | {(k, k) for k in range(2, N + 1)}
check("Nim push Wythoff: P = {(0,1),(1,0),(k,k),k>=2} (N=60)", pset(T) == exp)
r = C.classify(G.push_table(G.nim(), G.wythoff(), 300))
check("Nim push Wythoff -> lines, slope 1", r["cls"] == "lines" and r["detail"]["lines"]["slopes"] == [1.0], (r["cls"], C.summary(r)))

# 6. sqrt wall A: push {1,2,5,6} -> {1,2,3,4}
N = 1000
T = G.push_table(G.subtraction([1, 2, 5, 6]), G.subtraction([1, 2, 3, 4]), N)
P = (T == 1).astype(np.int8)


def settle(row, p=10):
    eq = row[:-p] == row[p:]
    bad = np.nonzero(~eq)[0]
    return int(bad[-1]) + 1 if len(bad) else 0


tk = lambda k: 7 * k * k + 35 * k + 13  # noqa: E731
got = [(k, settle(P[tk(k)]) - tk(k)) for k in range(0, 8)]
check("wall A: row 7k^2+35k+13 settles at column offset 35+10k (k=0..7, N=1000)",
      all(d == 35 + 10 * k for k, d in got), got)
r = C.classify(T)
w = r["detail"]["wall"]
check("wall A -> curved, exponent ~ 0.5", r["cls"] == "curved" and abs(w["alpha"] - 0.5) <= 0.1,
      (r["cls"], r["conf"], C.summary(r), "risers", w.get("risers")))
check("wall A: straight wall (alpha=1) rejected", w["sse_linear"] > 100 * max(w["sse_min"], 1), (w["sse_min"], w["sse_linear"]))

# 7. misere hand cases and independent cross-check
T = G.misere_table(G.subtraction([1]), 8)
check("misere sub{1}: P iff a+b odd", all((T[a, b] == 1) == ((a + b) % 2 == 1) for a in range(9) for b in range(9)))
T = G.misere_table(G.subtraction([1, 2]), 12)
check("misere sub{1,2}, one pile: P at n=1,4,7,10 (hand-computed)",
      [n for n in range(13) if T[n, 0] == 1] == [1, 4, 7, 10])
T = G.misere_table(G.nim(), 40)
check("misere Nim: P = {(0,1),(1,0),(k,k) k>=2}", pset(T) == {(0, 1), (1, 0)} | {(k, k) for k in range(2, 41)})
T = G.misere_table(G.wythoff(), 12)
check("misere Wythoff hand cases: (0,0)N (0,1)P (1,1)N (1,2)N (2,2)P",
      (T[0, 0], T[0, 1], T[1, 1], T[1, 2], T[2, 2]) == (0, 1, 0, 0, 1))
for nm, gm in (("nim", G.nim()), ("wythoff", G.wythoff()), ("euclid", G.euclid()), ("sub{1,3}", G.subtraction([1, 3])),
               ("wsub{1,2}", G.wythoff_sub([1, 2])), ("trunc_euclid2", G.trunc_euclid(2)), ("larger_cap2", G.larger_cap(2))):
    check(f"misere {nm}: solver == memoised recursion (N=14)", (G.misere_table(gm, 14) == brute_misere(gm, 14)).all())
# normal-play solver cross-check on the callables too
for nm, gm in (("trunc_euclid3", G.trunc_euclid(3)), ("wsub{1,2}", G.wythoff_sub([1, 2]))):
    A = G.normal_table(gm, 20)
    B = (lambda f: f)(None)
    # normal play: recursion with terminal = loss
    @functools.lru_cache(None)
    def win(a, b, gm=gm):
        return any(not win(x, y) for x, y in gm(a, b))
    R = np.array([[0 if win(a, b) else 1 for b in range(21)] for a in range(21)], dtype=np.int8)
    check(f"normal {nm}: rulegraph == recursion (N=20)", (A == R).all())
    win.cache_clear()
for nm, gm in (("larger_only", G.larger_only()), ("larger_cap1", G.larger_cap(1)), ("larger_cap2", G.larger_cap(2)),
               ("larger_cap8", G.larger_cap(8))):
    @functools.lru_cache(None)
    def winL(a, b, gm=gm):
        return any(not winL(x, y) for x, y in gm(a, b))
    R = np.array([[0 if winL(a, b) else 1 for b in range(31)] for a in range(31)], dtype=np.int8)
    check(f"normal {nm}: fast flag sweep == recursion (N=30)", (G.normal_table(gm, 30) == R).all())
    check(f"misere {nm}: fast flag sweep == recursion (N=30)", (G.misere_table(gm, 30) == brute_misere(gm, 30)).all())
check("trunc_euclid(k) -> Euclid: tables agree for k >= N", (G.normal_table(G.trunc_euclid(60), 60) == G.normal_table(G.euclid(), 60)).all())

# 8. classifier on synthetic tables (no game here yields them; checks the other branches)
n = 255
i = np.arange(n + 1)
sier = ((i[:, None] & i[None, :]) == 0).astype(np.int8)
r = C.classify(sier)
check("synthetic Sierpinski (a&b==0) -> fractal", r["cls"] == "fractal", (r["cls"], r["conf"], C.summary(r)))
rng = np.random.default_rng(0)
r = C.classify((rng.random((400, 400)) < 0.5).astype(np.int8))
check("synthetic random table -> chaos", r["cls"] == "chaos", (r["cls"], r["conf"]))
syn = np.zeros((801, 801), dtype=np.int8)
for a in range(801):
    b = int(a ** 1.2)
    if b <= 800:
        syn[a, b] = 1
        syn[b, a] = 1
r = C.classify(syn)
check("synthetic curved line b = a^1.2 -> curved, alpha ~ 1.2 (mirror branch gives 0.83)",
      r["cls"] == "curved" and any(abs(l.get("alpha", 9) - 1.2) < 0.15 for l in r["detail"]["lines"]["lines"]),
      (r["cls"], [(l.get("alpha"), l.get("alpha_range")) for l in r["detail"]["lines"]["lines"]]))

# 9. order independence: Euclid is never stripes, whichever test runs first or what N is
import itertools  # noqa: E402
import tracemalloc  # noqa: E402
for N in (1000, 2000):
    T = G.normal_table(G.euclid(), N)
    P = (T == 1).astype(np.int8)
    M = C._margin(N)
    st_first = C.test_stripes(P, N, M)[0]
    C.test_cone(P, N, M)
    st_after = C.test_stripes(P, N, M)[0]
    r = C.classify(T)
    check(f"Euclid N={N}: stripes test rejects it before and after the cone test; class cone, no tie",
          (not st_first) and (not st_after) and r["cls"] == "cone" and "also_passes" not in r["detail"],
          (st_first, st_after, r["cls"], r["detail"].get("also_passes")))
# every named table is claimed by exactly one test (no order dependence), N=1000
for nm, mk in (("nim", lambda: G.normal_table(G.nim(), 1000)), ("wythoff", lambda: G.normal_table(G.wythoff(), 1000)),
               ("sub{1,2,5,7}", lambda: F.solve_fast("sub", [1, 2, 5, 7], 1000)),
               ("wsub{1,2,3}", lambda: F.solve_fast("wsub", [1, 2, 3], 1000)),
               ("wall A", lambda: G.push_table(G.subtraction([1, 2, 5, 6]), G.subtraction([1, 2, 3, 4]), 1000)),
               ("trunc_euclid8", lambda: G.normal_table(G.trunc_euclid(8), 1000))):
    r = C.classify(mk())
    check(f"{nm} N=1000: exactly one test claims it", "also_passes" not in r["detail"], (r["cls"], r["detail"].get("also_passes")))

# 10. cone test memory at N=4000 (synthetic wedge table; the old mgrid version took ~650 MB extra)
N = 4000
i = np.arange(N + 1)
wedge = ((i[None, :] > i[:, None]) & (i[None, :] < PHI * i[:, None])).astype(np.int8)
wedge = wedge | wedge.T
tracemalloc.start()
okc, confc, detc = C.test_cone(wedge, N, C._margin(N))
peak = tracemalloc.get_traced_memory()[1] / 2 ** 20
tracemalloc.stop()
check("test_cone N=4000 peak extra memory < 500 MB, finds the wedge", peak < 500 and okc and len(detc["slopes"]) == 2,
      ("%.0f MB" % peak, detc.get("slopes")))
del wedge

# 11. sparse vs chaos labels
r = C.classify(G.normal_table(G.larger_cap(1), 800))
check("larger_cap1 N=800 -> sparse (not chaos)", r["cls"] == "sparse", (r["cls"], r["detail"]["density"]))
r = C.classify((np.random.default_rng(1).random((600, 600)) < 0.005).astype(np.int8))
check("random table, density 0.005 -> sparse", r["cls"] == "sparse", r["cls"])
r = C.classify(G.normal_table(G.trunc_euclid(2), 800))
check("trunc_euclid2 (dense, density 0.45) -> chaos", r["cls"] == "chaos", (r["cls"], r["detail"]["density"]))

# 12. wall A at N=2000: windowed exponent range contains 1/2 and excludes 1
T = G.push_table(G.subtraction([1, 2, 5, 6]), G.subtraction([1, 2, 3, 4]), 2000)
r = C.classify(T)
w = r["detail"]["wall"]
lo, hi = w["alpha_range"]
check("wall A N=2000: curved, windowed alpha range contains 0.5 and is below 1",
      r["cls"] == "curved" and lo <= 0.5 <= hi + 1e-9 and hi < 1, (r["cls"], round(w["alpha"], 3), (round(lo, 3), round(hi, 3)),
                                                              w["alpha_windows"], "risers", w["risers"]))

# 13. fast solvers == reference solvers (random sets, N=60)
rnd = np.random.default_rng(5)
okf = True
for _ in range(12):
    S = sorted(rnd.choice(np.arange(1, 8), size=rnd.integers(1, 5), replace=False).tolist())
    Tt = sorted(rnd.choice(np.arange(1, 8), size=rnd.integers(1, 5), replace=False).tolist())
    for kind, mk in (("sub", G.subtraction), ("wsub", G.wythoff_sub)):
        okf &= bool((F.solve_fast(kind, S, 60) == G.normal_table(mk(S), 60)).all())
        okf &= bool((F.solve_fast(kind, S, 60, misere=True) == G.misere_table(mk(S), 60)).all())
        okf &= bool((F.solve_fast(kind, S, 60, pre=G.normal_table(G.wythoff_sub(Tt), 60)) == G.push_table(mk(S), G.wythoff_sub(Tt), 60)).all())
        okf &= bool((F.solve_fast(kind, S, 60, pre=G.normal_table(G.nim(), 60)) == G.push_table(mk(S), G.nim(), 60)).all())
        okf &= bool((F.solve_nim_push("wythoff", 60, G.normal_table(mk(S), 60)) == G.push_table(G.wythoff(), mk(S), 60)).all())
check("fast.py solvers == rulegraph/games solvers (normal, misere, push; 12 random sets, N=60)", okf)

print("PASS" if ok_all else "FAIL")
sys.exit(0 if ok_all else 1)
