#!/usr/bin/env python3
"""Stage-1 classifier.  classify.py IN.jsonl [OUT_growing.json]
Categories (from wallscan fields; records = [a, pre] each time pre exceeds all earlier pre):
  noperiod  - some row had no tail period <= PMAX
  overflow  - wall reached the window: fast wall, slope est = max_pre / a_stop
  bounded   - no new record in the second half of the run (wall settled)
  growing   - records continue into the second half; local exponents
              e1 = log2(R(N/2)/R(N/4)), e2 = log2(R(N)/R(N/2)) of the running max R.
              sub-labels: linear (e2 > 0.85), sqrt-like (0.3 <= e2 <= 0.75), slow (< 0.3), mid (else)
Every growing pair, whatever its sub-label, is listed for stage 2 (no threshold hides a class)."""
import sys, json, math
from collections import Counter

def runmax(recs, a):
    v = 0
    for t, p in recs:
        if t <= a: v = p
        else: break
    return v

def classify(r):
    if r["status"] == "noperiod": return "noperiod", {}
    if r["status"] == "overflow":
        return "overflow", {"slope": round(r["max_pre"] / max(r["a_stop"], 1), 3)}
    N = r["N"]; recs = r["records"]
    if recs[-1][0] < N // 2: return "bounded", {"w": r["max_pre"], "last": recs[-1][0]}
    R1, R2, R3 = (max(runmax(recs, x), 1) for x in (N // 4, N // 2, N))
    e1, e2 = math.log2(R2 / R1), math.log2(R3 / R2)
    sub = "linear" if e2 > 0.85 else "sqrt-like" if 0.3 <= e2 <= 0.75 else "slow" if e2 < 0.3 else "mid"
    return "growing:" + sub, {"e1": round(e1, 3), "e2": round(e2, 3), "R": [R1, R2, R3], "nrec2": sum(1 for t, _ in recs if t >= N // 2)}

if __name__ == "__main__":
    rows = [json.loads(l) for l in open(sys.argv[1])]
    cnt = Counter(); grow = []
    for r in rows:
        c, info = classify(r); cnt[c] += 1
        if c.startswith("growing") or c == "noperiod":
            grow.append({"S1": r["S1"], "g": r["g"], "cls": c, **info, "periods": r["tail_periods"]})
    print(len(rows), "pairs"); [print(f"  {k}: {v}") for k, v in sorted(cnt.items())]
    if len(sys.argv) > 2: json.dump(grow, open(sys.argv[2], "w"), indent=0)
