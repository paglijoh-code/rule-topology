#!/usr/bin/env python3
"""game_classes/analyze.py: tables from census_N2000.jsonl (and recheck_N4000.jsonl).
  python3 game_classes/analyze.py            prints markdown tables to stdout
"""
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name):
    p = os.path.join(HERE, name)
    return [json.loads(l) for l in open(p)] if os.path.exists(p) else []


R = {r["id"]: r for r in load("census_N2000.jsonl")}
R4 = {r["id"]: r for r in load("recheck_N4000.jsonl")}
CLASSES = ["stripes", "lines", "cone", "curved", "fractal", "sparse", "other", "chaos"]


def row(label, recs):
    c = collections.Counter(r["cls"] for r in recs)
    return "| %s | %d | " % (label, len(recs)) + " | ".join(str(c.get(k, 0)) for k in CLASSES) + " |"


def hdr(first):
    return "| %s | n | " % first + " | ".join(CLASSES) + " |\n|---|---|" + "---|" * len(CLASSES)


def fam(r):
    j = r["id"]
    if j.startswith("push:"):
        a, b = j[5:].split(">")
        return "push " + a.split(":")[0] + " > " + b.split(":")[0]
    return j.split(":")[0]


def ablation():
    print(hdr("axiom switch (N=2000, 127 sets each)"))
    names = {"sub": "one-pile subtraction S (normal)", "wsub": "Wythoff-type S: one pile or both (normal)",
             "msub": "one-pile subtraction S (misere)", "mwsub": "Wythoff-type S (misere)",
             "u": "unbounded games from games.py (normal; 12 games, no S)", "mu": "unbounded games (misere)"}
    for k in ("sub", "wsub", "msub", "mwsub", "u", "mu"):
        print(row(names[k], [r for r in R.values() if fam(r) == k]))
    print()
    print("Unbounded games, one by one:\n")
    print("| game | normal | misere |\n|---|---|---|")
    for g in [r["id"][2:] for r in R.values() if r["id"].startswith("u:")]:
        a, b = R.get("u:" + g), R.get("mu:" + g)
        print("| %s | %s %s | %s %s |" % (g, a["cls"], a["summary"][:40], b["cls"] if b else "-", (b["summary"][:40] if b else "")))
    print()
    # normal vs misere: same S, same class?
    for k, m in (("sub", "msub"), ("wsub", "mwsub")):
        same = diff = 0
        per = collections.Counter()
        ex = []
        for j, r in R.items():
            if fam(r) == k:
                r2 = R.get(m + ":" + j.split(":")[1])
                if r2:
                    if r["cls"] == r2["cls"] and r.get("period") == r2.get("period"):
                        same += 1
                    else:
                        diff += 1
                        ex.append((j, r["cls"], r.get("period"), r2["cls"], r2.get("period")))
        print(f"normal vs misere, {k}: same class and period {same}, different {diff}", ex[:8])
    same = diff = 0
    ex = []
    for j, r in R.items():
        if fam(r) == "sub":
            r2 = R.get("wsub:" + j.split(":")[1])
            if r["cls"] == r2["cls"] and r.get("period") == r2.get("period"):
                same += 1
            else:
                diff += 1
                ex.append((j, r["cls"], r.get("period"), r2["cls"], r2.get("period")))
    print(f"one pile vs Wythoff-type, same S: same class and period {same}, different {diff}", ex[:8])
    pc = collections.Counter(tuple(r["period"]) for r in R.values() if r["cls"] == "stripes" and fam(r) == "sub")
    print("sub period distribution:", sorted(pc.items()))
    pc = collections.Counter(tuple(r["period"]) for r in R.values() if r["cls"] == "stripes" and fam(r) == "wsub")
    print("wsub period distribution:", sorted(pc.items()))


def side(txt):
    if txt in ("nim", "wythoff"):
        return R.get("u:" + txt)
    return R.get(txt)


def cross():
    print(hdr("push type A > B (N=2000)"))
    types = sorted({fam(r) for r in R.values() if r["id"].startswith("push")})
    for t in types:
        print(row(t, [r for r in R.values() if fam(r) == t]))
    print()
    print("| push type | n | class = A's | class = B's | equals both | neither (new class) | stripes with period different from A and B |\n|---|---|---|---|---|---|---|")
    for t in types:
        n = ea = eb = eboth = neither = newper = 0
        for r in R.values():
            if fam(r) != t:
                continue
            A, B = r["id"][5:].split(">")
            ra, rb = side(A), side(B)
            if not ra or not rb:
                continue
            n += 1
            a_ = r["cls"] == ra["cls"]
            b_ = r["cls"] == rb["cls"]
            ea += a_
            eb += b_
            eboth += a_ and b_
            neither += (not a_) and (not b_)
            if r["cls"] == "stripes" and ra["cls"] == "stripes" and rb["cls"] == "stripes" and \
                    tuple(r["period"]) not in (tuple(ra["period"]), tuple(rb["period"])):
                newper += 1
        print(f"| {t} | {n} | {ea} | {eb} | {eboth} | {neither} | {newper} |")


def boundaries():
    print("| id | class | N=2000 | density | N=4000 |\n|---|---|---|---|---|")
    for r in R.values():
        if r["cls"] in ("stripes",) or (r["cls"] == "lines" and r.get("nlines", 1) <= 5):
            continue
        s4 = R4.get(r["id"])
        d4 = f"{s4['cls']} {s4['summary']}" if s4 else "-"
        print(f"| {r['id']} | {r['cls']} | {r['summary']} | {r['density']} | {d4} |")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("all", "ablation"):
        ablation()
    if what in ("all", "cross"):
        print()
        cross()
    if what in ("all", "boundaries"):
        print()
        boundaries()
