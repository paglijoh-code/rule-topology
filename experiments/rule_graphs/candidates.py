#!/usr/bin/env python3
"""candidates.py RECHECK.jsonl [--list] : sort the N=8000 recheck rows into classes using the stored round times.
  late fit  = exponent.bounce_fit on the last two thirds of the rounds (needs n_rounds >= 12): early irregular
              rounds (before the glider regime settles) pull the plain bfit down on pre|A|367-like rows.
  d2 trend  = median 2nd difference of T in the last third / middle third (about 1 for a sqrt wall, about 2 for T ~ j^3)
Classes: sqrt (late fit in [0.44,0.58]), sub-sqrt (late fit < 0.42), super (late fit 0.62..0.85), linear-ish (>= 0.85), linear (kind linear),
         few (<12 rounds, unresolved), other kinds (bounded, slow, noperiod, none) kept as is."""
import sys, json, collections
import numpy as np
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import exponent


def classify(r):
    if r["kind"] != "growing":
        return r["kind"]
    T = r.get("rounds_T") or []
    if r["n_rounds"] < 12 or len(T) < 12:
        return "few"
    late = exponent.bounce_fit(np.array(T[len(T) // 3:]), skip=0)
    r["late_fit"] = late
    d2 = np.diff(np.array(T, float), 2)
    k = len(d2) // 3
    m, l = np.median(d2[k:2 * k]), np.median(d2[2 * k:])
    r["d2_trend"] = round(float(l / m), 2) if m > 0 else None
    if late is None:
        return "few"
    if late >= 0.85:
        return "linear-ish"       # sawtooth linear growth (M ~ c a with periodic bursts of bounces)
    return "sqrt" if 0.44 <= late <= 0.58 else ("sub-sqrt" if late < 0.42 else ("super" if late > 0.62 else "between"))


if __name__ == "__main__":
    rows = [json.loads(l) for l in open(sys.argv[1])]
    cls = collections.defaultdict(list)
    for r in rows:
        cls[classify(r)].append(r)
    types = ["chain", "pre", "cycle", "branch", "rand"]
    print("class       " + " ".join(f"{t:>7s}" for t in types))
    for c in sorted(cls):
        print(f"{c:11s} " + " ".join(f"{sum(1 for r in cls[c] if r['type']==t):7d}" for t in types))
    if "--list" in sys.argv:
        for r in cls["sub-sqrt"]:
            print(r["id"], "late", r["late_fit"], "bfit", r.get("alpha_bfit"), "d2trend", r["d2_trend"], "alpha", r["alpha"],
                  "rounds", r["n_rounds"], "M_end", r["M_end"])
    json.dump({c: [r["id"] for r in v] for c, v in cls.items()}, open(sys.argv[1].replace(".jsonl", "_classes.json"), "w"))
