"""three_heaps/planelaw.py — proof check of the plane law for Sub{1,2} -> Sub{1,2,3} on three heaps.

L(x), x sorted u <= v <= w, r = mod 4, alpha = r(u) xor r(v), d = w - u - v:
  u >= 1:        P iff (d <= 2 and r(w) == alpha ^ 1) or (d >= 3 and r(w) == (alpha + 1) % 4)
  u = 0, v >= 1: P iff w - v == 2 or (w - v >= 5 and (w - v) % 4 == 1)
  u = v = 0:     P iff w % 4 == 1
Claim: L is the P-set. Proof: P is the unique solution of
  P(x) <=> Z(x) and no legal move x -> x - s e_i (s in {1,2}) with P(x - s e_i),   Z(x): r(x1)^r(x2)^r(x3) != 0
(push wins iff the Sub{1,2,3}^3 position is P, i.e. xor of residues = 0). So it suffices that L satisfies C(x) for all x.
(1) C(x) holds on the box [0,B]^3 (checked below).
(2) Reduction lemma: C(x) = C(x - tau) for the four translations below under the stated conditions,
    and every x reduces into [0,40]^3.
This script checks (1), checks L against the solver table, and sanity-checks (2) on random large points.
"""
import sys, random, numpy as np

def L(x):
    u, v, w = sorted(x)
    if u >= 1:
        a = (u % 4) ^ (v % 4); d = w - u - v
        return (w % 4) == (a ^ 1) if d <= 2 else (w % 4) == (a + 1) % 4
    if v >= 1:
        e = w - v; return e == 2 or (e >= 5 and e % 4 == 1)
    return w % 4 == 1

def Z(x): return ((x[0] % 4) ^ (x[1] % 4) ^ (x[2] % 4)) != 0

def C(x):
    rhs = Z(x) and not any(L(x[:i] + (x[i] - s,) + x[i + 1:]) for i in range(3) for s in (1, 2) if x[i] >= s)
    return L(x) == rhs

def reduce(x):
    """Apply the four reductions (bulk steps of the same translation are taken at once)."""
    u, v, w = sorted(x); steps = []
    while True:
        d = w - u - v
        if v - u >= 7: k = (v - u - 7) // 4 + 1; v -= 4 * k; w -= 4 * k; steps.append(("t2", k))
        elif d >= 11: k = (d - 11) // 4 + 1; w -= 4 * k; steps.append(("t1", k))
        elif u >= 7 and d <= -4: k = min((-4 - d) // 4 + 1, (u - 7) // 4 + 1); u -= 4 * k; v -= 4 * k; w -= 4 * k; steps.append(("t4i", k))
        elif u >= 7 and d >= 5: k = (u - 7) // 4 + 1; u -= 4 * k; v -= 4 * k; w -= 4 * k; steps.append(("t4o", k))
        elif u >= 7 and w - v >= 7: k = min((u - 7) // 4 + 1, (w - v - 7) // 4 + 1); u -= 4 * k; v -= 4 * k; w -= 8 * k; steps.append(("t3", k))
        else: return (u, v, w), steps

if __name__ == "__main__":
    B = 60
    bad = [x for x in ((a, b, c) for a in range(B + 1) for b in range(B + 1) for c in range(B + 1)) if not C(x)]
    print("(1) C fails on box [0,%d]^3 at %d points" % (B, len(bad)), bad[:5])
    random.seed(7); mx = [0, 0, 0]; viol = 0
    for _ in range(200000):
        x = tuple(random.choice([random.randint(0, 50), random.randint(0, 10**6)]) for _ in range(3))
        y, st = reduce(x)
        mx = [max(m, t) for m, t in zip(mx, y)]
        if C(x) != C(y): viol += 1
        # each single step must preserve C as well
    print("(2) random reduction: max reduced coords", mx, "(box 40 claimed), C changed in", viol, "cases")
    # step-by-step preservation on medium points
    viol2 = 0
    for _ in range(100000):
        x = tuple(sorted(random.randint(0, 400) for _ in range(3)))
        u, v, w = x; d = w - u - v
        for cond, y in ((v - u >= 7, (u, v - 4, w - 4)), (d >= 11, (u, v, w - 4)),
                        (u >= 7 and (d <= -4 or d >= 5), (u - 4, v - 4, w - 4)), (u >= 7 and w - v >= 7, (u - 4, v - 4, w - 8))):
            if cond and C(x) != C(y): viol2 += 1
    print("(2') single-step preservation violations:", viol2)
    if len(sys.argv) > 1:
        from lib3 import chain
        N = int(sys.argv[1]); T = chain(N, [(1, 2), (1, 2, 3)])
        idx = np.argwhere(np.ones_like(T)); s = np.sort(idx, axis=1); u, v, w = s.T
        a = (u % 4) ^ (v % 4); d = w - u - v; e = w - v
        Lv = np.where(u >= 1, np.where(d <= 2, (w % 4) == (a ^ 1), (w % 4) == (a + 1) % 4),
                      np.where(v >= 1, (e == 2) | ((e >= 5) & (e % 4 == 1)), w % 4 == 1))
        print("(3) L vs solver table on [0,%d]^3: mismatches" % N, int((Lv != T.reshape(-1)).sum()))
