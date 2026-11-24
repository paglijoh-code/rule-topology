#!/usr/bin/env python3
"""pilot.py [N] [OUT.jsonl] : rule_graphs pilot. One graph at a time. Writes one JSON line per graph."""
import os, sys, json, time, random, resource, tracemalloc
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
import graphs, exponent

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(H, "pilot.jsonl")
walls = [json.loads(l) for l in open(os.path.join(H, "..", "census_10", "walls_exact.jsonl"))]
walls = [w for w in walls if w["S2_example"]]
byname = {w["tag"]: w for w in walls}
pick = ["A", "r10:s1-2-4-7-9-10_g0123456_p0", "r10:s2-3-6-7-10_g0123456_p0",
        "r10:s3-4-9-10_g00112233041520314_p12", "r10:s6-7-8_g0120120123_p0"]
rng = random.Random(7)


def randC():
    k = rng.randint(1, 4)
    return tuple(sorted(rng.sample(range(1, 8), k)))


jobs = []
for t in pick:
    w = byname[t]
    A, B = tuple(w["S1"]), tuple(w["S2_example"])
    jobs.append((f"edge {t} (control)", {"A": A, "B": B}, {"A": ["B"]}, None))
    for C in list(dict.fromkeys(randC() for _ in range(8)))[:6]:
        jobs.append((f"chain {t} C={set(C)}", {"A": A, "B": B, "C": C}, {"A": ["B"], "B": ["C"]}, None))
for t, k in ((pick[0], 2), (pick[1], 3), (pick[2], 2)):
    w = byname[t]
    jobs.append((f"cycle k={k} {t}", {"A": tuple(w["S1"]), "B": tuple(w["S2_example"])},
                 {"A": ["B"], "B": ["A"]}, k))
for t in pick[:3]:
    w = byname[t]
    C = randC()
    jobs.append((f"branch {t} C={set(C)}", {"A": tuple(w["S1"]), "B": tuple(w["S2_example"]), "C": C},
                 {"A": ["B", "C"]}, None))

done = set()
if os.path.exists(OUT):
    done = {json.loads(l)["graph"] for l in open(OUT)}
for name, S, G, bud in jobs:
    if name in done:
        continue
    tracemalloc.start()
    t0 = time.time()
    res = graphs.solve_graph(S, G, N, bud)
    t1 = time.time()
    T = res[("A", bud)] if bud is not None else res[("A", None)]
    r, M = exponent.analyse(T, pmax=400, tail=min(1200, N // 4))
    t2 = time.time()
    peak = tracemalloc.get_traced_memory()[1]
    tracemalloc.stop()
    del res, T
    r.update(graph=name, N=N, solve_s=round(t1 - t0, 2), analyse_s=round(t2 - t1, 2),
             peak_mb=round(peak / 2**20), rss_mb=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20),
             sets={m: list(s) for m, s in S.items()}, budget=bud)
    with open(OUT, "a") as f:
        f.write(json.dumps(r) + "\n")
    print(name, r["kind"], r["alpha"], r["lo"], r["hi"], r.get("confidence"), "bad", r["bad_rows"],
          "per", r["max_period"], "t", r["solve_s"], r["analyse_s"], "mb", r["peak_mb"], flush=True)
