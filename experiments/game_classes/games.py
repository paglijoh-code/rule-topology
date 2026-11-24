#!/usr/bin/env python3
"""game_classes/games.py: two-pile impartial games as options(a, b) callables, one constructor per axiom.

Every constructor returns a callable options(a, b) -> list of (a', b').  Callables for
the three named rulegraph games carry an attribute `rg` ("nim" / "wythoff" / "euclid"),
which `normal_table` passes to rulegraph (its fast flag-based sweep) instead of the
callable.

Axiom switches
  subtraction(S)          finite moves, one pile
  wythoff_sub(S)          finite moves, one pile OR the same k from both piles
  nim(), wythoff(), euclid()          unbounded moves
  trunc_euclid(k)         subtract q*min from max, q <= k (-> Euclid as k -> inf)
  larger_only(), larger_cap(K)        rule atoms for the Nim -> Euclid path
  nim_to_euclid_path()    the rule-atom path (list of (label, game))
  subtraction_path(kmax)  subtraction {1..k}, k = 1..kmax (-> Nim as k -> inf)
Normal play  : normal_table(game, N) (rulegraph), push_table(A, B, N) (graph {A:[B], B:[]})
Misere play  : misere_table(game, N)  (own solver below; terminal = win for the mover)
Grundy table : grundy_table(game, N)  (normal play; None when not computed)
All tables are int8 arrays [a][b], 1 = P (previous player wins), 0 = N.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import rulegraph as rg  # noqa: E402


def _tag(fn, name, rgname=None):
    fn.name = name
    if rgname:
        fn.rg = rgname
    return fn


# ------------------------------------------------------------ finite move sets
def subtraction(S):
    S = tuple(sorted(S))

    def opts(a, b):
        return [(a - s, b) for s in S if s <= a] + [(a, b - s) for s in S if s <= b]
    return _tag(opts, "sub" + "".join(map(str, S)) if max(S) < 10 else "sub" + ",".join(map(str, S)))


def wythoff_sub(S):
    S = tuple(sorted(S))

    def opts(a, b):
        return ([(a - s, b) for s in S if s <= a] + [(a, b - s) for s in S if s <= b] +
                [(a - s, b - s) for s in S if s <= a and s <= b])
    return _tag(opts, "wsub" + ",".join(map(str, S)))


# ---------------------------------------------------------------- unbounded
def nim():
    return _tag(lambda a, b: rg.options("nim", a, b), "nim", "nim")


def wythoff():
    return _tag(lambda a, b: rg.options("wythoff", a, b), "wythoff", "wythoff")


def euclid():
    return _tag(lambda a, b: rg.options("euclid", a, b), "euclid", "euclid")


def trunc_euclid(k):
    """Subtract q*min from max, 1 <= q <= k, result >= 0; terminal if a pile is 0
    (same convention as rulegraph's Euclid, to which it converges as k -> inf)."""
    def opts(a, b):
        out = []
        if a > 0 and b > 0:
            if a >= b:
                out += [(a - q * b, b) for q in range(1, min(k, a // b) + 1)]
            if b >= a:
                out += [(a, b - q * a) for q in range(1, min(k, b // a) + 1)]
        return out
    return _tag(opts, f"trunc_euclid{k}")


# ------------------------------------------------- rule atoms (Nim -> Euclid)
def larger_only():
    """Rule atom 1: only the larger pile may move (either, if equal), by any amount."""
    def opts(a, b):
        out = []
        if a >= b:
            out += [(a - t, b) for t in range(1, a + 1)]
        if b >= a:
            out += [(a, b - t) for t in range(1, b + 1)]
        return out
    f = _tag(opts, "larger_only")
    f.larger_K = float("inf")
    return f


def larger_cap(K):
    """Rule atom 2: larger-only, and the amount is capped: t <= K*min (no cap if min = 0)."""
    def opts(a, b):
        m = min(a, b)
        out = []
        if a >= b:
            out += [(a - t, b) for t in range(1, (a if m == 0 else min(a, K * m)) + 1)]
        if b >= a:
            out += [(a, b - t) for t in range(1, (b if m == 0 else min(b, K * m)) + 1)]
        return out
    f = _tag(opts, f"larger_cap{K}")
    f.larger_K = K
    return f


def nim_to_euclid_path():
    """Each step adds or tightens exactly one rule.
    nim -> only larger pile moves -> amount capped at K*min (K=8,2,1) ->
    amount must be a multiple of min, q <= k (k=1,2,4,8) -> q unbounded (Euclid).
    Caveat: a pile-0 position is terminal from the 'multiple of min' step on (0 divides
    nothing), but not before; that is part of the multiple-of-min rule."""
    steps = [("nim", nim()), ("larger_only", larger_only()),
             ("cap8", larger_cap(8)), ("cap2", larger_cap(2)), ("cap1", larger_cap(1))]
    steps += [(f"tEuclid{k}", trunc_euclid(k)) for k in (1, 2, 4, 8)]
    steps.append(("euclid", euclid()))
    return steps


def subtraction_path(kmax):
    return [(f"sub{{1..{k}}}", subtraction(range(1, k + 1))) for k in range(1, kmax + 1)]


# ------------------------------------------------------------------ solvers
def _rgspec(game):
    return getattr(game, "rg", game)


def _larger_table(K, N, misere):
    """Flag sweep for larger-only games with cap t <= K*min (K = inf: none).  Options of (a, b),
    a > b, are (a', b) with a - K*b <= a' < a (all a' < a if b = 0): only the latest P in
    column b matters.  Same for rows when a < b; a = b uses both."""
    n1 = N + 1
    st = np.zeros((n1, n1), dtype=np.int8)
    lastc = [-1] * n1  # latest P row index in each column
    lastr = [-1] * n1  # latest P column index in each row
    for a in range(n1):
        for b in range(n1):
            if a == 0 and b == 0:
                isP = not misere
            else:
                m = min(a, b)
                lim = float("inf") if m == 0 else K * m
                win = False
                if a >= b and lastc[b] >= 0 and a - lastc[b] <= lim:
                    win = True
                if b >= a and lastr[a] >= 0 and b - lastr[a] <= lim:
                    win = True
                isP = not win
            if isP:
                st[a, b] = 1
                lastc[b] = a
                lastr[a] = b
    return st


def normal_table(game, N):
    if hasattr(game, "larger_K"):
        return _larger_table(game.larger_K, N, False)
    return rg.solve({"g": _rgspec(game)}, {}, N)[("g", None)]


def push_table(A, B, N):
    """One-push combination A (-) B: either player may press the button once (costing
    the turn), switching from A's rules to B's."""
    res = rg.solve({"A": _rgspec(A), "B": _rgspec(B)}, {"A": ["B"], "B": []}, N)
    return res[("A", None)]


def misere_table(game, N):
    """Misere play: the player who cannot move WINS.  Terminal (no options) is N;
    otherwise P iff no option is P and every option is N (so: P iff no option is P),
    except the terminal rule.  All options of (a, b) are lexicographically earlier."""
    if hasattr(game, "larger_K"):
        return _larger_table(game.larger_K, N, True)
    n1 = N + 1
    st = np.zeros((n1, n1), dtype=np.int8)
    name = getattr(game, "rg", None)
    if name in ("nim", "wythoff"):  # flag sweep, same as rulegraph's fast path
        rowP = [False] * n1
        colP = [False] * n1
        diagP = [False] * (2 * n1)
        for a in range(n1):
            for b in range(n1):
                if a == 0 and b == 0:
                    continue  # terminal -> N (mover wins)
                anyP = rowP[a] or colP[b] or (name == "wythoff" and diagP[a - b + N])
                if not anyP:
                    st[a, b] = 1
                    rowP[a] = colP[b] = True
                    diagP[a - b + N] = True
        return st
    for a in range(n1):
        for b in range(n1):
            o = game(a, b)
            if o and not any(st[x, y] == 1 for x, y in o):
                st[a, b] = 1
    return st


def grundy_table(game, N):
    """Normal-play Grundy values; Nim by XOR, Wythoff and anything slow -> None."""
    name = getattr(game, "rg", None)
    if name == "nim":
        i = np.arange(N + 1)
        return (i[:, None] ^ i[None, :]).astype(np.int32)
    if name == "wythoff":
        return None
    n1 = N + 1
    g = np.zeros((n1, n1), dtype=np.int32)
    for a in range(n1):
        for b in range(n1):
            seen = {g[x, y] for x, y in game(a, b)}
            m = 0
            while m in seen:
                m += 1
            g[a, b] = m
    return g
