#!/usr/bin/env python3
"""jobs5.py KIND OUT.jsonl [--sample K --seed S]
KIND: realised10 (g of every S2 <= {1..10}, 244 patterns) x S1 <= {1..10}, skipping pairs census_8 scanned
(S1 <= {1..8} and g among census_8's 89); periodic7 / periodic8 (minimal-period patterns) x S1 <= {1..10}.
--s1 filter: 'all' or '12' (S1 contains 1 and 2). --sample K: uniform random K pairs."""
import argparse, json, os, random, sys
from itertools import combinations
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(H, "..", "census_8"))
from gpatterns import mex_g, eventual, canon, rgs, minimal_period

def realised10():
    groups = {}
    for k in range(1, 11):
        for S2 in combinations(range(1, 11), k):
            pre, per = eventual(mex_g(S2, 1500))
            groups.setdefault((pre, per, tuple(canon(mex_g(S2, 1500)[:pre + per]))), []).append(list(S2))
    return [{"pre": a, "per": b, "pattern": list(c), "S2s": v} for (a, b, c), v in sorted(groups.items())]

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("kind"); ap.add_argument("out")
    ap.add_argument("--s1", default="all"); ap.add_argument("--sample", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1); a = ap.parse_args()
    old = {(r["pre"], r["per"], tuple(r["pattern"])) for r in json.load(open(os.path.join(H, "..", "census_8", "out", "g_realised.json")))}
    if a.kind == "realised10":
        gs = realised10(); json.dump(gs, open(os.path.join(H, "out", "g_realised10.json"), "w"))
    else:
        p = int(a.kind[-1]); gs = [{"pre": 0, "per": p, "pattern": pat} for pat in rgs(p) if minimal_period(pat) == p]
    real10 = {(g["pre"], g["per"], tuple(g["pattern"])) for g in realised10()} if a.kind != "realised10" else None
    S1s = [list(c) for k in range(1, 11) for c in combinations(range(1, 11), k)]
    if a.s1 == "12": S1s = [s for s in S1s if 1 in s and 2 in s]
    jobs = []
    for g in gs:
        kg = (g["pre"], g["per"], tuple(g["pattern"]))
        for S1 in S1s:
            if a.kind == "realised10" and kg in old and max(S1) <= 8: continue
            tag = a.kind if real10 is None else (a.kind + ("+realised" if kg in real10 else ""))
            jobs.append({"S1": S1, "g": {"pre": g["pre"], "per": g["per"], "pattern": g["pattern"]}, "tag": tag})
    if a.sample: random.seed(a.seed); jobs = random.sample(jobs, min(a.sample, len(jobs)))
    with open(a.out, "w") as f:
        for j in jobs: f.write(json.dumps(j) + "\n")
    print(len(jobs), "jobs")

if __name__ == "__main__": main()
