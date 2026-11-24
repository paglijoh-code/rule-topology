#!/usr/bin/env python3
"""Rule-graph combinatorial games on pairs (a, b), a, b <= N.

Impartial, normal play. A position is (a, b) plus a mode m (and optionally a
remaining push budget). On a turn a player either moves in the current mode's
ruleset or PUSHES along an edge m -> m' of the mode graph; a push costs the
turn (push-the-button convention) and leaves (a, b) unchanged.

Rulesets: "nim", "wythoff", "euclid", or a callable options(a, b) -> iterable
of (a', b').

Euclid convention used here: from (a, b) with both piles > 0, subtract a
positive multiple of the smaller pile from the larger, result >= 0 (so a move
to a position with a 0 pile is allowed, e.g. (3,6)->(3,0)); a position with a
0 pile has no Euclid move (terminal). The prior-art report does not state the
push paper's convention, so this is my choice and is NOT checked against that
paper.  For a == b both piles are "the larger", giving (0,a) and (a,0).

Outcomes (arrays of int8): 1 = P (previous player wins), 0 = N (next player
wins), -1 = draw (loopy only).

solve(rulesets, graph, N, budget=None) -> dict key -> numpy array [a][b]
  budget None, acyclic graph : keys (mode, None)   (layered, exact)
  budget None, cyclic graph  : keys (mode, None)   (loopy fixed point)
  budget k                   : keys (mode, j), j = 0..k, j = pushes left
"""
import sys
import numpy as np


def _is_acyclic(graph):
    color = {}

    def dfs(u):
        color[u] = 1
        for v in graph.get(u, []):
            if color.get(v, 0) == 1:
                return False
            if color.get(v, 0) == 0 and not dfs(v):
                return False
        color[u] = 2
        return True
    return all(color.get(u, 0) != 0 or dfs(u) for u in graph)


def options(rs, a, b):
    """Explicit options (used by the slow reference solver and callables)."""
    out = []
    if callable(rs):
        return list(rs(a, b))
    if rs in ("nim", "wythoff"):
        out += [(a - t, b) for t in range(1, a + 1)]
        out += [(a, b - t) for t in range(1, b + 1)]
        if rs == "wythoff":
            out += [(a - t, b - t) for t in range(1, min(a, b) + 1)]
    elif rs == "euclid":
        if a > 0 and b > 0:
            if a >= b:
                out += [(a - q * b, b) for q in range(1, a // b + 1)]
            if b >= a:
                out += [(a, b - q * a) for q in range(1, b // a + 1)]
    else:
        raise ValueError(rs)
    return out


def _sweep(rs, st, pushP, pushAllN, N):
    """One lexicographic sweep. st[a][b] in {-1,0,1}; updates in place.
    pushP[a][b]: some push target is P. pushAllN[a][b]: all push targets N.
    Every ruleset option of (a,b) is lexicographically earlier, so one sweep
    is exact when push info is final. Returns True if anything changed."""
    changed = False
    n1 = N + 1
    rowP = [False] * n1
    colP = [False] * n1
    diagP = [False] * (2 * n1)
    rowN = [0] * n1
    colN = [0] * n1
    diagN = [0] * (2 * n1)
    simple = rs in ("nim", "wythoff")
    wyth = rs == "wythoff"
    for a in range(n1):
        sa = st[a]
        for b in range(n1):
            v = sa[b]
            if v == -1:
                if pushP[a][b]:
                    v = 0
                elif simple:
                    anyP = rowP[a] or colP[b] or (wyth and diagP[a - b + N])
                    if anyP:
                        v = 0
                    elif (pushAllN[a][b] and rowN[a] == b and colN[b] == a and
                          (not wyth or diagN[a - b + N] == min(a, b))):
                        v = 1
                else:
                    opts = options(rs, a, b)
                    if any(st[x][y] == 1 for x, y in opts):
                        v = 0
                    elif pushAllN[a][b] and all(st[x][y] == 0 for x, y in opts):
                        v = 1
                if v != -1:
                    sa[b] = v
                    changed = True
            if simple:
                if v == 1:
                    rowP[a] = colP[b] = True
                    diagP[a - b + N] = True
                elif v == 0:
                    rowN[a] += 1
                    colN[b] += 1
                    diagN[a - b + N] += 1
    return changed


def _push_arrays(targets, st_of, N):
    n1 = N + 1
    if not targets:
        return (np.zeros((n1, n1), bool).tolist(), np.ones((n1, n1), bool).tolist())
    arrs = [np.array(st_of(t)) for t in targets]
    anyP = np.zeros((n1, n1), bool)
    allN = np.ones((n1, n1), bool)
    for x in arrs:
        anyP |= (x == 1)
        allN &= (x == 0)
    return anyP.tolist(), allN.tolist()


def solve(rulesets, graph, N, budget=None):
    modes = list(rulesets)
    graph = {m: list(graph.get(m, [])) for m in modes}
    n1 = N + 1
    res = {}

    def fresh():
        return [[-1] * n1 for _ in range(n1)]

    if budget is not None:
        for j in range(budget + 1):
            for m in modes:
                st = fresh()
                tg = graph[m] if j >= 1 else []
                pP, pN = _push_arrays([(t, j - 1) for t in tg],
                                      lambda k: res[k], N)
                _sweep(rulesets[m], st, pP, pN, N)
                res[(m, j)] = np.array(st, dtype=np.int8)
        return res

    if _is_acyclic(graph):
        done = set()

        def visit(m):
            if m in done:
                return
            for t in graph[m]:
                visit(t)
            st = fresh()
            pP, pN = _push_arrays([(t, None) for t in graph[m]],
                                  lambda k: res[k], N)
            _sweep(rulesets[m], st, pP, pN, N)
            res[(m, None)] = np.array(st, dtype=np.int8)
            done.add(m)
        for m in modes:
            visit(m)
        return res

    # loopy: monotone fixed point of the win/lose labelling; leftover = draw
    sts = {m: fresh() for m in modes}
    while True:
        changed = False
        for m in modes:
            pP, pN = _push_arrays(graph[m], lambda t: sts[t], N)
            changed |= _sweep(rulesets[m], sts[m], pP, pN, N)
        if not changed:
            break
    return {(m, None): np.array(sts[m], dtype=np.int8) for m in modes}


def solve_reference(rulesets, graph, N, budget=None):
    """Slow explicit-graph retrograde analysis (independent implementation),
    for cross-checking solve() on small N."""
    modes = list(rulesets)
    ks = [None] if budget is None else list(range(budget + 1))
    n1 = N + 1
    succ, pred = {}, {}
    for k in ks:
        for m in modes:
            for a in range(n1):
                for b in range(n1):
                    s = (m, k, a, b)
                    out = [(m, k, x, y) for x, y in options(rulesets[m], a, b)]
                    if k is None:
                        out += [(t, None, a, b) for t in graph.get(m, [])]
                    elif k >= 1:
                        out += [(t, k - 1, a, b) for t in graph.get(m, [])]
                    succ[s] = out
                    for o in out:
                        pred.setdefault(o, []).append(s)
    cnt = {s: len(o) for s, o in succ.items()}
    lab = {}
    queue = []
    for s, o in succ.items():
        if not o:
            lab[s] = 1
            queue.append(s)
    while queue:
        s = queue.pop()
        for p in pred.get(s, []):
            if p in lab:
                continue
            if lab[s] == 1:
                lab[p] = 0
                queue.append(p)
            else:
                cnt[p] -= 1
                if cnt[p] == 0:
                    lab[p] = 1
                    queue.append(p)
    out = {}
    for k in ks:
        for m in modes:
            arr = np.full((n1, n1), -1, dtype=np.int8)
            for a in range(n1):
                for b in range(n1):
                    arr[a, b] = lab.get((m, k, a, b), -1)
            out[(m, k)] = arr
    return out


def p_positions(arr, upper=None):
    """P-positions with a <= b (and b <= upper), sorted by (a, b)."""
    n = arr.shape[0] if upper is None else upper + 1
    return [(a, b) for a in range(n) for b in range(a, n) if arr[a, b] == 1]


def mex(s):
    g = 0
    while g in s:
        g += 1
    return g


# ----------------------------------------------------------------- selftest
def selftest():
    ok = True

    def check(name, cond, extra=""):
        nonlocal ok
        print(("ok   " if cond else "FAIL ") + name + (" " + extra if extra else ""))
        ok &= bool(cond)

    N = 60
    # (1) single-mode Nim
    r = solve({"n": "nim"}, {}, N)[("n", None)]
    check("Nim P-positions are a==b (N=60)",
          all((r[a, b] == 1) == (a == b) for a in range(N + 1) for b in range(N + 1)))
    # (2) single-mode Wythoff, golden-ratio Beatty pairs
    r = solve({"w": "wythoff"}, {}, N)[("w", None)]
    phi = (1 + 5 ** 0.5) / 2
    exp = {(0, 0)}
    n = 1
    while int(n * phi) <= N and int(n * phi * phi) <= N:
        x, y = int(n * phi), int(n * phi * phi)
        exp |= {(x, y), (y, x)}
        n += 1
    got = {(a, b) for a in range(N + 1) for b in range(N + 1) if r[a, b] == 1}
    check("Wythoff P-positions = Beatty pairs (floor(n*phi), floor(n*phi^2)) (N=60)",
          got == exp, f"({len(got)} positions)")
    # (3) Nim => Wythoff equals misere Nim (push paper; report says so)
    r = solve({"n": "nim", "w": "wythoff"}, {"n": ["w"]}, N)[("n", None)]
    exp = {(0, 1), (1, 0)} | {(a, a) for a in range(2, N + 1)}
    got = {(a, b) for a in range(N + 1) for b in range(N + 1) if r[a, b] == 1}
    check("Nim=>Wythoff P = misere Nim P: {(0,1),(1,0)} u {(a,a): a>=2}", got == exp)
    # Wythoff => Nim and Euclid => Nim are only computed (report gives no formula)
    for nm, rs in (("Wythoff=>Nim", "wythoff"), ("Euclid=>Nim", "euclid")):
        r = solve({"s": rs, "n": "nim"}, {"s": ["n"]}, N)[("s", None)]
        print("info " + nm + " first P (a<=b):", p_positions(r, 25)[:12], "...")
    # cross-check fast solver against the explicit retrograde solver
    rs3 = {"n": "nim", "w": "wythoff", "e": "euclid"}
    cases = [
        ({"n": ["w"], "w": ["e"]}, None),
        ({"e": ["n"], "n": ["w"], "w": []}, None),
        ({"n": ["w"], "w": ["n"]}, None),           # loopy
        ({"n": ["w"], "w": ["n"]}, 3),              # budget
        ({"n": ["w", "e"], "w": ["e"], "e": ["n"]}, 2),
        ({"n": ["n"], "w": ["e"], "e": ["w"]}, None),  # loopy, self-loop
    ]
    for g, bud in cases:
        A = solve(rs3, g, 14, bud)
        B = solve_reference(rs3, g, 14, bud)
        same = all((A[k] == B[k]).all() for k in A)
        check(f"fast == reference retrograde, graph={g}, budget={bud}", same)
    print("PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(0 if selftest() else 1)
    print(__doc__)
