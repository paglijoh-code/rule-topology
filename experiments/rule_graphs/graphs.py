#!/usr/bin/env python3
"""graphs.py : two-pile subtraction games over a rule graph (chain, budgeted 2-cycle, branch).

Each mode m has a subtraction set S_m (a move removes s in S_m from ONE pile).
A turn is either such a move or a push along an edge m -> m' (costs the turn,
piles unchanged). Same conventions and result keys as rulegraph.solve:
  budget None, acyclic graph : keys (mode, None)
  budget k                   : keys (mode, j), j = pushes left, push (m,j)->(t,j-1)
Arrays are int8 [a][b]: 1 = P, 0 = N.  Backend: C (sub.c via cc -O2, ctypes) or
a numpy/python fallback (env M7B_NO_C=1 or use_c=False forces the fallback).
"""
import os, ctypes, subprocess
import numpy as np

H = os.path.dirname(os.path.abspath(__file__))
_lib = None
_tried = False


def _load():
    global _lib, _tried
    if _tried:
        return _lib
    _tried = True
    so = os.path.join(H, "_sub.so")
    src = os.path.join(H, "sub.c")
    try:
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            subprocess.run(["cc", "-O2", "-shared", "-fPIC", "-o", so, src], check=True,
                           capture_output=True)
        lib = ctypes.CDLL(so)
        lib.solve_node.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p,
                                   ctypes.c_void_p, ctypes.c_void_p]
        lib.solve_node.restype = None
        _lib = lib
    except Exception:
        _lib = None
    return _lib


def have_c():
    return _load() is not None and not os.environ.get("M7B_NO_C")


def _node_c(S, pushP, N):
    n1 = N + 1
    out = np.empty((n1, n1), dtype=np.int8)
    Sa = np.array(sorted(S), dtype=np.int32)
    pp = None if pushP is None else np.ascontiguousarray(pushP, dtype=np.uint8)
    _lib.solve_node(n1, len(Sa), Sa.ctypes.data,
                    None if pp is None else pp.ctypes.data, out.ctypes.data)
    return out


def _node_py(S, pushP, N):
    n1 = N + 1
    S = sorted(S)
    out = np.zeros((n1, n1), dtype=np.int8)
    for a in range(n1):
        base = np.zeros(n1, bool) if pushP is None else pushP[a].astype(bool).copy()
        for s in S:
            if s <= a:
                base |= out[a - s] == 1
        row = out[a]
        bl = base.tolist()
        rl = [0] * n1
        for b in range(n1):
            if bl[b]:
                continue
            for s in S:
                if s <= b and rl[b - s] == 1:
                    break
            else:
                rl[b] = 1
        out[a] = rl
    return out


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


def solve_graph(sets, graph, N, budget=None, use_c=None):
    """sets: mode -> iterable of ints; graph: mode -> list of modes. Returns dict like rulegraph.solve."""
    if use_c is None:
        use_c = have_c()
    node = _node_c if use_c else _node_py
    if use_c and _load() is None:
        raise RuntimeError("C backend unavailable")
    modes = list(sets)
    graph = {m: list(graph.get(m, [])) for m in modes}
    res = {}

    def pushP(targets):
        if not targets:
            return None
        acc = np.zeros_like(res[targets[0]], dtype=bool)
        for t in targets:
            acc |= res[t] == 1
        return acc

    if budget is not None:
        for j in range(budget + 1):
            for m in modes:
                tg = [(t, j - 1) for t in graph[m]] if j >= 1 else []
                res[(m, j)] = node(sets[m], pushP(tg), N)
        return res
    if not _is_acyclic(graph):
        raise ValueError("cyclic graph needs a budget")
    done = set()

    def visit(m):
        if m in done:
            return
        for t in graph[m]:
            visit(t)
        res[(m, None)] = node(sets[m], pushP([(t, None) for t in graph[m]]), N)
        done.add(m)
    for m in modes:
        visit(m)
    return res


def sub_callable(S):
    S = tuple(S)
    return lambda a, b: [(a - s, b) for s in S if s <= a] + [(a, b - s) for s in S if s <= b]


def rulegraph_reference(sets, graph, N, budget=None):
    """Same game through rulegraph.solve (slow, callable rulesets) for cross-checks."""
    import sys
    sys.path.insert(0, os.path.dirname(H))
    import rulegraph
    return rulegraph.solve({m: sub_callable(s) for m, s in sets.items()}, graph, N, budget)


# convenience constructors
def chain(A, B, C):
    return {"A": A, "B": B, "C": C}, {"A": ["B"], "B": ["C"]}, None

def cycle(A, B):
    return {"A": A, "B": B}, {"A": ["B"], "B": ["A"]}

def branch(A, B, C):
    return {"A": A, "B": B, "C": C}, {"A": ["B", "C"]}
