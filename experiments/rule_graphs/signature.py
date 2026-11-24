#!/usr/bin/env python3
"""signature.py N : does the signature of B's rewritten table predict whether the wall survives in A->B->C?

A's table reads B only through B's table, so A->B->C is the edge A->T', T' = B's table with its push to C.
For each chain in census4000.jsonl:
  1. Is T' a g-table, i.e. P(a,b) iff g'(a) = g'(b) for some g' (an equivalence relation on heap sizes)?
  2. If so, take g's eventual signature (pre, per, canonical pattern), the same key census_10 scanned.
  3. Look up (A, signature) in the census_10 stage-1 scan (census_10/out/s1_*.jsonl, classified by census_8/classify.py)
     and in the confirmed walls (census_10/walls_exact.jsonl). Predicted survival = census_10 class 'growing*'.
  4. Compare with the census verdict (kind growing or linear).
Run: nice -n 10 env OMP_NUM_THREADS=1 python3 rule_graphs/signature.py 4000 > rule_graphs/signature4000.txt
"""
import os, sys, json, glob
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
sys.path.insert(0, os.path.join(H, "..", "census_8"))
import numpy as np, graphs
from gpatterns import eventual, canon
from classify import classify
from collections import Counter

N = int(sys.argv[1])


def gform(T):
    """g' labels if T's P-set (T == 1) is {g'(a) = g'(b)}, else None. T is upper-triangular (b >= a)."""
    P = T == 1
    P = P | P.T
    if not P.diagonal().all():
        return None
    rep = P.argmax(1)                      # smallest b equivalent to a
    if not (P == (rep[:, None] == rep[None, :])).all():
        return None
    return rep


def sig(rep):
    g = [int(x) for x in rep]
    e = eventual(g)
    if e is None:
        return None
    pre, per = e
    return (pre, per, tuple(canon(g[:pre + per])))


census_10 = {}
for f in glob.glob(os.path.join(H, "..", "census_10", "out", "s1_*.jsonl")):
    for l in open(f):
        r = json.loads(l); g = r["g"]
        census_10[(tuple(r["S1"]), g["pre"], g["per"], tuple(g["pattern"]))] = classify(r)[0]
walls = {(tuple(w["S1"]), w["g"]["pre"], w["g"]["per"], tuple(w["g"]["pattern"]))
         for w in map(json.loads, open(os.path.join(H, "..", "census_10", "walls_exact.jsonl")))}

# sanity: the plain game's table is the g-table of its mex sequence
for S in ((1, 2, 3, 4), (1, 3, 4), (2, 5, 7)):
    T = graphs.solve_graph({"B": S}, {}, 600)[("B", None)]
    assert gform(T) is not None, ("plain table not g-form", S)

rows = [json.loads(l) for l in open(os.path.join(H, "census4000.jsonl"))]
rows = [r for r in rows if r["type"] == "chain"]
cnt = Counter(); conf = Counter(); ex = []
cache = {}
for r in rows:
    S = {k: tuple(v) for k, v in r["sets"].items()}
    key = (S["B"], S["C"])
    if key not in cache:
        T = graphs.solve_graph({"B": S["B"], "C": S["C"]}, {"B": ["C"]}, N)[("B", None)]
        rep = gform(T)
        cache[key] = None if rep is None else sig(rep)
    sg = cache[key]
    surv = r["kind"] in ("growing", "linear")
    if sg is None:
        cnt[("not g-form", surv)] += 1
        continue
    k = (S["A"],) + sg
    c = census_10.get(k)
    if c is None:
        cnt[("g-form, not in census_10 scan", surv)] += 1
        continue
    pred = c.startswith("growing")
    cnt[("g-form, in scan", surv)] += 1
    conf[(pred, surv, k in walls)] += 1
    if pred != surv and len(ex) < 20:
        ex.append((r["id"], r["kind"], c, sg[0], sg[1], "".join(map(str, sg[2]))[:30]))

print("N", N, "chains", len(rows), "distinct (B,C)", len(cache),
      "g-form", sum(v is not None for v in cache.values()))
for (a, s), c in sorted(cnt.items()):
    print(f"  {a:28s} survives={s}: {c}")
print("prediction from the census_10 stage-1 class (growing*) vs census, for g-form chains in the scan:")
for (p, s, w), c in sorted(conf.items()):
    print(f"  predicted grow={p}  census survives={s}  (A,sig) a confirmed wall={w}: {c}")
print("mismatches (id, census kind, census_10 class, pre, per, pattern head):")
for e in ex:
    print(" ", e)
