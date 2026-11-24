#!/usr/bin/env python3
"""game_classes/census.py: the ablation census (Step 2) and the cross-class one-push census; resumable, jsonl output.

  nice -n 10 python3 game_classes/census.py run [--N 2000] [--budget 540] [--out game_classes/census_N2000.jsonl]
        runs jobs not yet in the jsonl until `budget` seconds are used, then exits (rerun to continue)
  census.py count              number of jobs by family
  census.py recheck --N 4000 [--budget S]   rerun every non-straight N=2000 result (+150 'other') at N=4000 -> game_classes/recheck_N4000.jsonl

Job ids (S, T = comma lists of subtraction amounts):
  sub:S wsub:S msub:S mwsub:S           finite subtraction / Wythoff-type (one pile, or k from both), normal / misere
  u:nim u:wythoff u:euclid u:trunc<k> u:larger_only u:cap<K>   unbounded games from games.py, mu:... = misere
  push:A>B   one-push A (+) B; A in sub:S wsub:S nim wythoff; B in sub:T wsub:T msub:T mwsub:T nim wythoff
Sampling is seeded (SEED = 20261123), so the job list is reproducible.
"""
import itertools
import json
import os
import random
import resource
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import numpy as np  # noqa: E402
import classify as C  # noqa: E402
import fast as F  # noqa: E402
import games as G  # noqa: E402

SEED = 20261123
SETS = [tuple(i + 1 for i in range(7) if m >> i & 1) for m in range(1, 128)]
SMALL = [s for s in SETS if len(s) <= 2]
UNBOUNDED = ["nim", "wythoff", "euclid", "trunc1", "trunc2", "trunc3", "trunc4", "trunc8", "larger_only", "cap1", "cap2", "cap8"]
N_RANDOM = int(os.environ.get("M7A_NRANDOM", 1000))  # random extra pairs per push type


def ss(S):
    return ",".join(map(str, S))


def jobs():
    rnd = random.Random(SEED)
    out = []
    for S in SETS:
        out += [f"sub:{ss(S)}", f"wsub:{ss(S)}", f"msub:{ss(S)}", f"mwsub:{ss(S)}"]
    for u in UNBOUNDED:
        out += [f"u:{u}", f"mu:{u}"]
    seen = set(out)

    def add(j):
        if j not in seen:
            seen.add(j)
            out.append(j)

    def pairs(a, b, extra_pool_a=SETS, extra_pool_b=SETS, same=False):
        for S in SMALL:
            for T in SMALL:
                if S != T:
                    add(f"push:{a}:{ss(S)}>{b}:{ss(T)}")
        pool = [(S, T) for S in extra_pool_a for T in extra_pool_b if S != T]
        for S, T in rnd.sample(pool, min(N_RANDOM, len(pool))):
            add(f"push:{a}:{ss(S)}>{b}:{ss(T)}")
    pairs("sub", "sub")
    pairs("sub", "wsub")
    pairs("wsub", "sub")
    for S in SETS:
        for a in ("sub", "wsub"):
            for b in ("nim", "wythoff"):
                add(f"push:{a}:{ss(S)}>{b}")
        for b in ("nim", "wythoff"):
            add(f"push:{b}>sub:{ss(S)}")
    for S in SETS:
        add(f"push:sub:{ss(S)}>msub:{ss(S)}")
        add(f"push:wsub:{ss(S)}>mwsub:{ss(S)}")
    pool = [(S, T) for S in SETS for T in SETS if S != T]
    for S, T in rnd.sample(pool, min(N_RANDOM, len(pool))):
        add(f"push:sub:{ss(S)}>msub:{ss(T)}")
    return out


def _S(txt):
    return tuple(int(x) for x in txt.split(","))


def _game(tag):
    if tag.startswith("trunc"):
        return G.trunc_euclid(int(tag[5:]))
    if tag.startswith("cap"):
        return G.larger_cap(int(tag[3:]))
    return {"nim": G.nim, "wythoff": G.wythoff, "euclid": G.euclid, "larger_only": G.larger_only}[tag]()


def _finite(kind, S, N, misere=False, pre=None):
    return F.solve_fast("wsub" if kind.endswith("wsub") else "sub", S, N, misere=misere, pre=pre)


def _side(txt, N):
    """table of one side of a push (as B: possibly misere)."""
    if txt in ("nim", "wythoff"):
        return G.normal_table(_game(txt), N)
    k, S = txt.split(":")
    return _finite(k, _S(S), N, misere=k.startswith("m"))


def table(job, N):
    if job.startswith("push:"):
        A, B = job[5:].split(">")
        pre = _side(B, N)
        if A in ("nim", "wythoff"):
            return F.solve_nim_push(A, N, pre)
        k, S = A.split(":")
        return _finite(k, _S(S), N, pre=pre)
    k, rest = job.split(":", 1)
    if k in ("sub", "wsub", "msub", "mwsub"):
        return _finite(k, _S(rest), N, misere=k.startswith("m"))
    g = _game(rest)
    return G.misere_table(g, N) if k == "mu" else G.normal_table(g, N)


def record(job, N):
    t0 = time.time()
    T = table(job, N)
    t1 = time.time()
    r = C.classify(T)
    t2 = time.time()
    d = r["detail"]
    w = d.get("wall") or {}
    rec = dict(id=job, N=N, cls=r["cls"], conf=r["conf"], summary=C.summary(r), density=round(d["density"], 5),
               also=d.get("also_passes"), blockfrac=d.get("block_fraction"), t_solve=round(t1 - t0, 2), t_cls=round(t2 - t1, 2),
               rss_mb=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20))
    if r["cls"] == "stripes":
        rec["period"] = d["stripes"]["period"]
    if r["cls"] == "curved" and w.get("verdict") == "curved":
        rec["alpha"] = [round(w["alpha"], 3)] + [round(x, 3) for x in w["alpha_range"]]
        rec["risers"] = w["risers"]
        rec["wall_p"] = w["p"]
    if r["cls"] in ("lines", "curved") and "lines" in d["lines"]:
        rec["nlines"] = len(d["lines"]["lines"])
    if r["cls"] == "cone":
        rec["slopes"] = d["cone"]["slopes"]
    return rec


def done_ids(path):
    ids = set()
    if os.path.exists(path):
        for line in open(path):
            try:
                ids.add(json.loads(line)["id"])
            except Exception:
                pass
    return ids


def recheck_ids(path, n_other=150):
    """Every non-straight N=2000 result (curved, fractal, cone, sparse, chaos, lines with > 5 clusters),
    in that order, then a seeded sample of n_other of the 'other' results (too many to redo all at N=4000)."""
    rs = [json.loads(l) for l in open(path)]
    ids = []
    for c in ("curved", "fractal", "cone", "sparse", "chaos"):
        ids += [r["id"] for r in rs if r["cls"] == c]
    ids += [r["id"] for r in rs if r["cls"] == "lines" and r.get("nlines", 1) > 5]
    oth = [r["id"] for r in rs if r["cls"] == "other"]
    random.Random(SEED).shuffle(oth)
    return ids + oth[:n_other]


def main():
    a = sys.argv[1:]
    N = int(a[a.index("--N") + 1]) if "--N" in a else 2000
    out = a[a.index("--out") + 1] if "--out" in a else os.path.join(HERE, f"census_N{N}.jsonl")
    if a[0] == "count":
        js = jobs()
        fam = {}
        for j in js:
            key = j.split(":")[0] if not j.startswith("push") else "push " + j[5:].split(">")[0].split(":")[0] + ">" + j.split(">")[1].split(":")[0]
            fam[key] = fam.get(key, 0) + 1
        print(len(js), fam)
        return
    if a[0] == "recheck":
        js = recheck_ids(os.path.join(HERE, "census_N2000.jsonl"))
        out = a[a.index("--out") + 1] if "--out" in a else os.path.join(HERE, f"recheck_N{N}.jsonl")
    else:
        js = jobs()
    budget = float(a[a.index("--budget") + 1]) if "--budget" in a else 540.0
    if "--limit" in a:
        js = js[:int(a[a.index("--limit") + 1])]
    done = done_ids(out)
    t0 = time.time()
    n = 0
    for j in js:
        if j in done:
            continue
        if time.time() - t0 > budget:
            break
        rec = record(j, N)
        with open(out, "a") as f:
            f.write(json.dumps(rec) + "\n")
        n += 1
        if rec["rss_mb"] > 3000:
            print("RSS limit hit", rec["rss_mb"])
            break
    left = sum(1 for j in js if j not in done_ids(out))
    print(f"ran {n} jobs in {time.time() - t0:.0f}s; {left} left of {len(js)}; peak rss {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 2 ** 20} MB")


if __name__ == "__main__":
    main()
