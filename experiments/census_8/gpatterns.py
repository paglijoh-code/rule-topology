#!/usr/bin/env python3
"""g patterns: `realised` (S2 subsets of {1..8}) and `periodic P` (all minimal-period-p equality patterns)."""
import json, os, sys
from itertools import combinations
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")

def mex_g(S2, H=600):
    g = []
    for h in range(H + 1):
        seen = {g[h - s] for s in S2 if s <= h}
        m = 0
        while m in seen: m += 1
        g.append(m)
    return g

def canon(pat):
    m = {}
    return [m.setdefault(x, len(m)) for x in pat]

def eventual(g):
    """(pre, per) with per minimal, then pre minimal; None if not found within the range."""
    H = len(g)
    for per in range(1, H // 3):
        # pre minimal for this per
        y = H - per - 1
        while y >= 0 and g[y] == g[y + per]: y -= 1
        pre = y + 1
        if pre + 3 * per <= H and pre <= H // 2: return pre, per
    return None

def realised():
    groups = {}
    for k in range(1, 9):
        for S2 in combinations(range(1, 9), k):
            g = mex_g(S2)
            pre, per = eventual(g)
            pat = canon(g[:pre + per])
            groups.setdefault((pre, per, tuple(pat)), []).append(list(S2))
    res = [{"pre": a, "per": b, "pattern": list(c), "S2s": v} for (a, b, c), v in sorted(groups.items())]
    json.dump(res, open(os.path.join(OUT, "g_realised.json"), "w"))
    print(len(res), "groups")
    return res

def rgs(p):
    def rec(pref, mx):
        if len(pref) == p: yield list(pref); return
        for v in range(mx + 2):
            yield from rec(pref + [v], max(mx, v))
    yield from rec([0], 0)

def minimal_period(pat):
    p = len(pat)
    return min(q for q in range(1, p + 1) if p % q == 0 and all(pat[i] == pat[i % q] for i in range(p)))

def periodic(P):
    real = {(r["pre"], r["per"], tuple(r["pattern"])) for r in json.load(open(os.path.join(OUT, "g_realised.json")))} \
        if os.path.exists(os.path.join(OUT, "g_realised.json")) else set()
    res, counts = [], []
    for p in range(1, P + 1):
        c = 0
        for pat in rgs(p):
            if minimal_period(pat) == p:
                c += 1
                res.append({"pre": 0, "per": p, "pattern": pat, "realised": (0, p, tuple(pat)) in real})
        counts.append(c)
    json.dump(res, open(os.path.join(OUT, "g_periodic%d.json" % P), "w"))
    print("counts", counts, "total", len(res))

if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    if sys.argv[1] == "realised": realised()
    elif sys.argv[1] == "periodic": periodic(int(sys.argv[2]))
