#!/usr/bin/env python3
"""Conjecture checks. Prints evidence sizes."""
import math, itertools
import numpy as np
from rulegraph import solve, p_positions
PHI = (1 + 5 ** 0.5) / 2
N = 300
R = {"n": "nim", "w": "wythoff", "e": "euclid"}
def S(arr):  # all ordered P-cells
    return {(a, b) for a in range(arr.shape[0]) for b in range(arr.shape[1]) if arr[a, b] == 1}
def chain(*ms):
    g = {ms[i]: [ms[i + 1]] for i in range(len(ms) - 1)}
    g[ms[-1]] = []
    return S(solve({m: R[m] for m in ms}, g, N)[(ms[0], None)])
def sym(pairs): return pairs | {(b, a) for a, b in pairs}
cells = (N + 1) ** 2
wyP = sym({(int(n * PHI), int(n * PHI * PHI)) for n in range(0, N) if int(n * PHI * PHI) <= N})
diag = {(a, a) for a in range(N + 1)}
print(f"N={N}, ordered cells per layer={cells}")
c = chain("w", "n")
cand = sym({(int(n * PHI) - 1, int(n * PHI) - 1 + n) for n in range(1, N) if int(n * PHI) - 1 + n <= N})
print("W=>N P == {(floor(n phi)-1, floor(n phi)-1+n)} sym:", c == cand, "size", len(c))
print("W=>N == Wythoff-P with (n phi) shift: differs from Wythoff P:", c != wyP)
print("W=>N: P == {(a,b): (a+1,b+1)...}? checks b-a = n and a=floor(n*phi)-1 -> above")
print("N=>W == misere Nim:", chain("n", "w") == ({(0, 1), (1, 0)} | {(a, a) for a in range(2, N + 1)}))
print("N=>E P == {(a,a): a>=1}:", chain("n", "e") == diag - {(0, 0)})
print("N=>E=>W P == diagonal:", chain("n", "e", "w") == diag)
print("N=>W=>E P == diag minus (2,2) plus (1,2),(2,1) minus (1,1)?:",
      chain("n", "w", "e") == (diag - {(1, 1), (2, 2)}) | {(1, 2), (2, 1)}, "size", len(chain("n", "w", "e")))
print("N=>W=>E has (1,2)?", (1, 2) in chain("n", "w", "e"), " (1,1)?", (1, 1) in chain("n", "w", "e"), " (2,2)?", (2, 2) in chain("n", "w", "e"))
print("W=>N=>E == Wythoff P:", chain("w", "n", "e") == wyP, "| W=>E=>N == Wythoff P:", chain("w", "e", "n") == wyP)
print("W=>E == W=>N with (0,1)->(1,1):", chain("w", "e") == (chain("w", "n") - {(0, 1), (1, 0)}) | {(1, 1)})
e_n, e_w = chain("e", "n"), chain("e", "w")
print("E=>N == E=>W:", e_n == e_w)
e_nw, e_wn = chain("e", "n", "w"), chain("e", "w", "n")
print("E=>N=>W == E=>W=>N:", e_nw == e_wn)
print("E=>N=>W == E=>N + (0,0),(1,1) - (0,1):", e_nw == (e_n | {(0, 0), (1, 1)}) - {(0, 1), (1, 0)})
# Euclid=>Nim row structure: P iff (a=0,b>=1) or 2<=a<b<=floor(phi a) or sym
cand = {(0, b) for b in range(1, N + 1)} | {(a, b) for a in range(2, N + 1) for b in range(a + 1, N + 1) if b <= math.floor(PHI * a)}
cand = sym(cand)
print("E=>N P == {(0,b)} u {a<b<=floor(phi*a), a>=2} (sym), exact float floor:", e_n == cand, "size", len(e_n))
bad = [(a, b) for (a, b) in sorted(e_n ^ cand)][:10]
print("   first mismatches:", bad, "| #mismatch:", len(e_n ^ cand))
# integer-exact floor(phi*a) = (a + isqrt(5 a^2)) // 2
cand2 = sym({(0, b) for b in range(1, N + 1)} | {(a, b) for a in range(2, N + 1) for b in range(a + 1, N + 1) if b <= (a + math.isqrt(5 * a * a)) // 2})
print("   same with integer floor((a+sqrt(5a^2))/2):", e_n == cand2)
# B: period 2 in k
g = {"n": ["w"], "w": ["n"]}
K = 8
res = solve({"n": "nim", "w": "wythoff"}, g, N, K)
for m in "nw":
    print(f"cycle start {m}: P_k == P_(k+2) for k=0..{K-2}:", all((res[(m, k)] == res[(m, k + 2)]).all() for k in range(K - 1)))
print("cycle Nim start: even k == Nim P (a==b):", all(S(res[("n", k)]) == diag for k in (0, 2, 4, 6, 8)),
      "; odd k == misere Nim:", all(S(res[("n", k)]) == ({(0, 1), (1, 0)} | {(a, a) for a in range(2, N + 1)}) for k in (1, 3, 5, 7)))
print("cycle Wythoff start: even k == Wythoff P:", all(S(res[("w", k)]) == wyP for k in (0, 2, 4, 6, 8)),
      "; odd k == W=>N:", all(S(res[("w", k)]) == chain("w", "n") for k in (1, 3, 5, 7)))
# C: unlimited
res = solve({"n": "nim", "w": "wythoff"}, g, 150)
print("C unlimited cycle N=150: cells P/N/draw per mode:", {m: (int((res[(m, None)] == 1).sum()), int((res[(m, None)] == 0).sum()), int((res[(m, None)] == -1).sum())) for m in "nw"})
# C extras: cycle plus escape to Euclid sink / Euclid-> cycle
for name, gg, rs in [
    ("n<->w, w->e (e sink)", {"n": ["w"], "w": ["n", "e"], "e": []}, "new"),
    ("n<->w, n->e (e sink)", {"n": ["w", "e"], "w": ["n"], "e": []}, "new"),
    ("n->n self loop only", {"n": ["n"]}, "n"),
    ("e<->n", {"e": ["n"], "n": ["e"]}, "en"),
]:
    r = solve({m: R[m] for m in rs}, gg, 150)
    print("C extra", name, {m: tuple(int(((r[(m, None)] == v)).sum()) for v in (1, 0, -1)) for m in rs}, "(P,N,D) over ordered cells N=150")
