#!/usr/bin/env python3
"""Lead A certificate: exact two-heap outcomes of Sub(S1) -push-> Sub(S2) (one push, shared).

Rows are exact symbolic objects (prefix, cycle): row a is d -> outcome(a, a+d), 1 = P.
Row a is computed from rows a-1..a-M (M = max S1), row a itself and the SG sequence g of
Sub(S2), by running the recursion in d until its finite state repeats after every input has
entered its cycle. That makes each row's eventual periodicity exact, not fitted.
Once a >= A* = M + pre(g), the map (rows a-M..a-1, a mod per(g)) -> row a does not depend on
a, so if the window at a0 equals the window at a0+q (and q is a multiple of per(g)), every
row a >= a0 equals row a+q. The certificate is that repeated window.

Usage: lead_a3.py --selftest | --all [AMAX] | --one 1,3 1,4
"""
import sys, json
from math import lcm
from leads import sg_seq, SUBSETS


class Row:
    """Eventually periodic 0/1 sequence, canonical (shortest cycle, then shortest prefix)."""
    __slots__ = ("pre", "cyc", "key")

    def __init__(self, pre, cyc):
        pre, cyc = list(pre), list(cyc)
        # shortest cycle
        n = len(cyc)
        for p in range(1, n + 1):
            if n % p == 0 and cyc == cyc[:p] * (n // p):
                cyc = cyc[:p]
                break
        # shortest prefix: roll back while last prefix element equals last cycle element
        while pre and pre[-1] == cyc[-1]:
            cyc = [pre.pop()] + cyc[:-1]
        self.pre, self.cyc = tuple(pre), tuple(cyc)
        self.key = (self.pre, self.cyc)

    def __call__(self, d):
        if d < len(self.pre):
            return self.pre[d]
        return self.cyc[(d - len(self.pre)) % len(self.cyc)]


def sg_cert(S, n=2000):
    """SG sequence of Sub(S) with exact preperiod/period (state = last max(S) values)."""
    g = sg_seq(S, n)
    M = max(S)
    seen = {}
    for i in range(M, n + 1):
        st = tuple(g[i - M:i])
        if st in seen:
            j = seen[st]
            return g, j - M, i - j          # g[x] = g[x + per] for x >= pre
        seen[st] = i
    raise RuntimeError("SG period not found")


class Pair:
    def __init__(self, S1, S2):
        self.S1, self.S2 = sorted(S1), sorted(S2)
        self.M = max(S1)
        self.g, self.gpre, self.gper = sg_cert(S2)
        self.rows = []

    def gval(self, x):
        if x < self.gpre + self.gper:
            return self.g[x]
        return self.g[self.gpre + (x - self.gpre) % self.gper]

    def val(self, a, b):
        """outcome(a, b) for rows already computed (a <= b) or below the diagonal."""
        if a > b:
            a, b = b, a
        return self.rows[a](b - a)

    def next_row(self):
        a = len(self.rows)
        S1 = self.S1
        r = []

        def cell(d):
            b = a + d
            if self.gval(a) ^ self.gval(b) == 0:
                return 0
            for s in S1:
                if s <= a and self.val(a - s, b) == 1:      # row a-s (a-s may be 0: lone heap)
                    return 0
                if s <= b:
                    if b - s >= a:
                        if r[d - s] == 1:
                            return 0
                    elif self.val(b - s, a) == 1:          # crosses the diagonal: row b-s < a
                        return 0
            return 1

        # inputs: rows a-s (s in S1, s <= a) read at d+s; g read at a+d; row a itself.
        ins = [self.rows[a - s] for s in S1 if s <= a]
        D0 = max([len(x.pre) for x in ins] + [self.gpre, self.M]) + self.M
        L = lcm(*([len(x.cyc) for x in ins] + [self.gper]))
        seen = {}
        d = 0
        while True:
            if d >= D0:
                st = (tuple(r[d - self.M:d]), d % L)
                if st in seen:
                    j = seen[st]
                    row = Row(r[:j], r[j:d])
                    break
                seen[st] = d
            r.append(cell(d))
            d += 1
        self.rows.append(row)
        return row

    def certify(self, amax=3000):
        """Find the first (a0, q) with q a multiple of per(g) and window(a0) == window(a0+q),
        a0 >= A* . Returns dict or None."""
        Astar = self.M + self.gpre
        win = {}
        for a in range(amax):
            self.next_row()
            if a + 1 >= self.M and a + 1 - self.M >= Astar:
                start = a + 1 - self.M          # window = rows start..a, predicts row a+1
                key = (tuple(self.rows[i].key for i in range(start, a + 1)), start % self.gper)
                if key in win:
                    a0 = win[key]
                    q = start - a0
                    # rows a >= a0 repeat with period q; trim a0 down as far as rows agree
                    A0 = a0
                    while A0 > 0 and self.rows[A0 - 1].key == self.rows[A0 - 1 + q].key:
                        A0 -= 1
                    per = lcm(*[len(self.rows[i].cyc) for i in range(A0, A0 + q)])
                    T = max(len(self.rows[i].pre) for i in range(A0, A0 + q))
                    Tall = max(len(r.pre) for r in self.rows)
                    return dict(q=q, A0=A0, a0_window=a0, p=per, T=T, T_all_rows=Tall,
                                rows_computed=len(self.rows), gpre=self.gpre, gper=self.gper)
                win[key] = start
        return None


def predict(P, cert, a, b):
    if a > b:
        a, b = b, a
    A0, q = cert["A0"], cert["q"]
    d = b - a
    if a >= A0 + q:
        a = A0 + (a - A0) % q
    return P.rows[a](d)


def selftest():
    from lead_a2 import solve2
    for S1, S2 in [((1, 2), (1, 2, 3)), ((1,), (1, 2)), ((1, 3), (1, 4)), ((3,), (2,)), ((2, 3, 4), (2, 3)),
                   ((1, 2, 3), (1, 3, 4))]:
        P = Pair(S1, S2)
        c = P.certify()
        N = 900
        B = solve2(set(S1), set(S2), N)
        bad = sum(1 for a in range(N + 1) for b in range(N + 1) if B[a][b] != predict(P, c, a, b))
        if bad:
            print("FAIL", S1, S2, c, bad); sys.exit(1)
    print("PASS (certified row law == brute force on all a, b <= 900 for 6 pairs)")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "--selftest":
        selftest()
    elif a[0] == "--one":
        S1 = tuple(int(x) for x in a[1].split(",")); S2 = tuple(int(x) for x in a[2].split(","))
        P = Pair(S1, S2); c = P.certify(); print(c)
        for i in range(min(len(P.rows), c["A0"] + c["q"] + 2)):
            print(i, "pre", "".join(map(str, P.rows[i].pre)), "cyc", "".join(map(str, P.rows[i].cyc)))
    elif a[0] == "--all":
        amax = int(a[1]) if len(a) > 1 else 3000
        fails = set(json.load(open("raw/h1_fails.json")))
        for S1 in SUBSETS:
            for S2 in SUBSETS:
                if S1 == S2:
                    continue
                c = Pair(S1, S2).certify(amax)
                tag = "FAIL41" if repr((S1, S2)) in fails else "fit169"
                print(json.dumps({"S1": S1, "S2": S2, "tag": tag, "cert": c}), flush=True)
