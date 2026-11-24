#!/usr/bin/env python3
"""summarize.py CENSUS.jsonl [--list] : counts by graph type and kind, exponent histogram, candidates.
Candidate = kind growing and (alpha outside [0.4,0.6] and outside [0.9,1.1], or alpha_bfit < 0.42),
or growing with <8 rounds (unresolved), or kind slow / noperiod (non-bounded) in a non-control graph (type != edge)."""
import sys, json, collections
rows = [json.loads(l) for l in open(sys.argv[1])]
BINS = [(0, 0.1), (0.1, 0.2), (0.2, 0.3), (0.3, 0.4), (0.4, 0.45), (0.45, 0.55), (0.55, 0.6), (0.6, 0.7), (0.7, 0.9), (0.9, 1.1), (1.1, 9)]


def is_cand(r):
    if r["type"] == "edge":
        return False
    if r["kind"] in ("slow", "noperiod"):
        return True
    if r["kind"] != "growing":
        return False   # includes linear, bounded, none
    a, b = r["alpha"], r.get("alpha_bfit")
    if b is None:                       # fewer than 8 rounds: exponent unresolved (sparse records)
        return True
    ok = (0.4 <= a <= 0.6) or (0.9 <= a <= 1.1)
    return (not ok) or (b is not None and b < 0.42)


types = ["edge", "chain", "pre", "cycle", "branch", "rand"]
print("N =", rows[0]["N"], " total", len(rows))
print("\nkind by type (survival = kind growing or linear; sqrt-like = growing with alpha in [0.4,0.6])")
print("type    n  none bounded slow noperiod linear growing  sqrt-like  growing%")
for t in types:
    R = [r for r in rows if r["type"] == t]
    if not R:
        continue
    c = collections.Counter(r["kind"] for r in R)
    sq = sum(1 for r in R if r["kind"] == "growing" and 0.4 <= r["alpha"] <= 0.6)
    print(f"{t:7s}{len(R):5d} {c['none']:5d} {c['bounded']:7d} {c['slow']:5d} {c['noperiod']:8d} {c['linear']:6d} {c['growing']:7d} {sq:10d} {100*(c['growing']+c['linear'])/len(R):8.1f}")
print("\nexponent histogram (growing only; headline alpha)")
print("bin        " + " ".join(f"{t:>7s}" for t in types))
for lo, hi in BINS:
    cells = []
    for t in types:
        cells.append(sum(1 for r in rows if r["type"] == t and r["kind"] == "growing" and lo <= r["alpha"] < hi))
    print(f"[{lo:.2f},{hi:.2f}) " + " ".join(f"{x:7d}" for x in cells))
print("\nbfit (alpha_bfit, growing, >=8 rounds) histogram")
for lo, hi in ((0, 0.3), (0.3, 0.4), (0.4, 0.45), (0.45, 0.55), (0.55, 0.65), (0.65, 1.1), (1.1, 9)):
    print(f"[{lo:.2f},{hi:.2f}) " + " ".join(f"{sum(1 for r in rows if r['type']==t and r['kind']=='growing' and r.get('alpha_bfit') is not None and lo<=r['alpha_bfit']<hi):7d}" for t in types))
print("growing with <8 rounds (no bfit):", " ".join(f"{t}:{sum(1 for r in rows if r['type']==t and r['kind']=='growing' and r.get('alpha_bfit') is None)}" for t in types))
cands = [r for r in rows if is_cand(r)]
print(f"\ncandidates: {len(cands)}  by type:", dict(collections.Counter(r['type'] for r in cands)),
      " by kind:", dict(collections.Counter(r['kind'] for r in cands)))
if "--ids" in sys.argv:       # --ids FILE : write candidate ids
    open(sys.argv[sys.argv.index("--ids") + 1], "w").write("\n".join(r["id"] for r in cands) + "\n")
if "--list" in sys.argv:
    for r in cands:
        print(r["id"], r["kind"], r["alpha"], r["lo"], r["hi"], r.get("alpha_bfit"), r.get("n_rounds"), r.get("M_end"), r.get("sat_row"))
