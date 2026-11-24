#!/usr/bin/env python3
"""select2.py S1RESULT.jsonl JOBFILE : stage-2 routing (classifier census_8/classify.py).
Routes: every growing pair (any sub-label), every noperiod pair, every overflow with a_stop > N/3
(a wall that reached d=600 only late could be a fast sqrt wall). Writes st2.sh-style job lines:
NAME N D PMAX S1 gpre gper gpat (N, D, PMAX chosen by the caller of run_s2.sh)."""
import sys, json, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "census_8"))
from classify import classify
from collections import Counter
cnt = Counter(); out = []
for l in open(sys.argv[1]):
    r = json.loads(l); c, info = classify(r); cnt[c] += 1
    take = c.startswith("growing") or c == "noperiod" or (c == "overflow" and r["a_stop"] > r["N"] // 3)
    if take:
        g = r["g"]; S = ",".join(map(str, r["S1"])); pat = ",".join(map(str, g["pattern"]))
        name = "s" + S.replace(",", "-") + "_g" + "".join(map(str, g["pattern"])) + "_p%d" % g["pre"]
        out.append((c, name, S, g["pre"], g["per"], pat))
print(sys.argv[1], dict(cnt), "-> stage 2:", len(out), Counter(o[0].split(":")[0] if o[0] != "overflow" else "late-overflow" for o in out))
with open(sys.argv[2], "w") as f:
    for c, name, S, pre, per, pat in out: f.write(f"{name} {S} {pre} {per} {pat} {c}\n")
