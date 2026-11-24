#!/usr/bin/env python3
"""game_classes/fast.py: fast exact solvers for the finite-move games of the census (subtraction S, Wythoff-type S).

All tables are int8 [a][b], 1 = P.  Method: scan cells in lexicographic order; a cell not yet "attacked" is
P and attacks the cells it can be reached from.  `pre` (bool [N+1][N+1], optional) pre-attacks cells: that is
the one-push rule (A (+) B: a cell of A is N if B's cell is P, since pressing the button reaches it).
misere=True: a cell with no options is N (mover wins), so it is never P.
Cross-checked against games.normal_table / misere_table / push_table in test_classes.py.
"""
import numpy as np


def solve_fast(kind, S, N, misere=False, pre=None):
    n1 = N + 1
    S = tuple(sorted(S))
    wyth = kind == "wsub"
    m = S[0]
    if pre is None:
        att = [bytearray(n1) for _ in range(n1)]
    else:
        att = [bytearray(r.astype(np.uint8).tobytes()) for r in (pre == 1)]
    out = np.zeros((n1, n1), dtype=np.int8)
    for a in range(n1):
        ra = att[a]
        row = bytearray(n1)
        b = ra.find(0)
        while b != -1:
            if misere and a < m and b < m:  # terminal: mover wins, so N (and attacks nothing)
                b = ra.find(0, b + 1)
                continue
            row[b] = 1
            for s in S:
                if b + s <= N:
                    ra[b + s] = 1
                if a + s <= N:
                    att[a + s][b] = 1
                    if wyth and b + s <= N:
                        att[a + s][b + s] = 1
            b = ra.find(0, b + 1)
        out[a] = np.frombuffer(bytes(row), dtype=np.uint8)
    return out


def solve_nim_push(kind, N, pre):
    """nim or wythoff as the pushing game A: A (+) B with B's P cells in `pre`."""
    n1 = N + 1
    st = np.zeros((n1, n1), dtype=np.int8)
    rowP = [False] * n1
    colP = [False] * n1
    diag = [False] * (2 * n1)
    w = kind == "wythoff"
    for a in range(n1):
        pa = pre[a]
        for b in range(n1):
            if pa[b] == 1 or rowP[a] or colP[b] or (w and diag[a - b + N]):
                continue
            st[a, b] = 1
            rowP[a] = colP[b] = True
            diag[a - b + N] = True
    return st
