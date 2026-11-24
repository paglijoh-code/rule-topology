#!/usr/bin/env python3
"""summ.py DIR [--all] : stage-2 summary. Local exponents e_i = log2(R(2x)/R(x)) of the running max R
of pre at x = N/16, N/8, N/4, N/2. Labels: bounded (last record < N/2), linear (last e > 0.85),
sqrt (0.4..0.6 for the last two), other.  Prints non-linear rows (all with --all)."""
import json, sys, glob, math, os
from collections import Counter
c = Counter()
for f in sorted(glob.glob(os.path.join(sys.argv[1], "*.json"))):
    try: r = json.load(open(f))
    except Exception: c["unreadable"] += 1; continue
    rec = r["records"]; N = r["a_stop"]
    def R(a):
        v = 1
        for t, p in rec:
            if t <= a: v = p
        return max(v, 1)
    xs = [N // 16, N // 8, N // 4, N // 2]
    e = [round(math.log2(R(2 * x) / R(x)), 3) for x in xs]
    if r["status"] == "noperiod": lab = "noperiod"
    elif rec[-1][0] < N // 2 and r["status"] == "ok": lab = "bounded"
    elif e[-1] > 0.85 or r["status"] == "overflow" and e[-1] > 0.75: lab = "linear"
    elif all(0.4 <= x <= 0.6 for x in e[-2:]): lab = "sqrt"
    else: lab = "other"
    c[lab] += 1
    if "--all" in sys.argv or lab not in ("bounded", "linear"):
        print(lab, os.path.basename(f)[:-5], r["status"], N, r["max_pre"], r["tail_periods"][:3], e)
print(dict(c))
