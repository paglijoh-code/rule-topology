#!/usr/bin/env python3
"""census.py N OUT.jsonl [DEADLINE_S] [JOBS_FILTER|@IDFILE] : rule_graphs census. Resumable (skips ids already in OUT).
  nice -n 10 env OMP_NUM_THREADS=1 python3 rule_graphs/census.py 4000 rule_graphs/census4000.jsonl 540
Job families (seeds fixed; the list is a pure function of the walls file):
  edge    A->B control for each wall that has an S2_example (28 of the 32)
  chain   A->B->C, every nonempty C of {1..7}              (28 x 127)
  pre     C->A->B (wall at the end), table of root C        (28 x 127)
  cycle   A<->B budget 2,3,4, table (A, budget)            (28 x 3)
  branch  A->{B,C}, C random nonempty subset of {1..7}, 300 samples (seed 1)
  rand    chains of 2..4 nodes, each S random nonempty subset of {1..8}, 500 samples (seed 2)
Start-mode table of the root, rows a < N/2, analysed by exponent.analyse (pmax 400, tail min(1200,N/4)).
"""
import os, sys, json, time, random, resource, itertools, gc
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
import graphs, exponent


def subsets(universe):
    for r in range(1, len(universe) + 1):
        yield from itertools.combinations(universe, r)


def job_list():
    walls = [json.loads(l) for l in open(os.path.join(H, "..", "census_10", "walls_exact.jsonl"))]
    walls = [w for w in walls if w["S2_example"]]
    jobs = []
    for w in walls:
        A, B, t = tuple(w["S1"]), tuple(w["S2_example"]), w["tag"]
        jobs.append((f"edge|{t}", "edge", t, {"A": A, "B": B}, {"A": ["B"]}, None))
    for w in walls:
        A, B, t = tuple(w["S1"]), tuple(w["S2_example"]), w["tag"]
        for C in subsets(range(1, 8)):
            jobs.append((f"chain|{t}|{''.join(map(str, C))}", "chain", t,
                         {"A": A, "B": B, "C": C}, {"A": ["B"], "B": ["C"]}, None))
    for w in walls:
        A, B, t = tuple(w["S1"]), tuple(w["S2_example"]), w["tag"]
        for C in subsets(range(1, 8)):
            jobs.append((f"pre|{t}|{''.join(map(str, C))}", "pre", t,
                         {"C": C, "A": A, "B": B}, {"C": ["A"], "A": ["B"]}, None, "C"))
    for w in walls:
        A, B, t = tuple(w["S1"]), tuple(w["S2_example"]), w["tag"]
        for k in (2, 3, 4):
            jobs.append((f"cycle|{t}|{k}", "cycle", t, {"A": A, "B": B}, {"A": ["B"], "B": ["A"]}, k))
    rng = random.Random(1)
    for i in range(300):
        w = rng.choice(walls)
        A, B, t = tuple(w["S1"]), tuple(w["S2_example"]), w["tag"]
        C = tuple(sorted(rng.sample(range(1, 8), rng.randint(1, 7))))
        jobs.append((f"branch|{i}|{t}|{''.join(map(str, C))}", "branch", t,
                     {"A": A, "B": B, "C": C}, {"A": ["B", "C"]}, None))
    rng = random.Random(2)
    for i in range(500):
        L = rng.randint(2, 4)
        names = "ABCD"[:L]
        S = {m: tuple(sorted(rng.sample(range(1, 9), rng.randint(1, 8)))) for m in names}
        G = {names[j]: [names[j + 1]] for j in range(L - 1)}
        jobs.append((f"rand|{i}|" + "|".join("".join(map(str, S[m])) for m in names), "rand", "", S, G, None))
    return jobs


def run(job, N):
    jid, typ, tag, S, G, bud = job[:6]
    root = job[6] if len(job) > 6 else "A"
    t0 = time.time()
    res = graphs.solve_graph(S, G, N, bud)
    t1 = time.time()
    T = res[(root, bud)] if bud is not None else res[(root, None)]
    r, M = exponent.analyse(T, pmax=400, tail=min(1200, N // 4))
    t2 = time.time()
    del res, T
    gc.collect()   # solve_graph's recursive closure forms a cycle that holds every table until gc runs
    keep = ("kind", "alpha", "lo", "hi", "n_rounds", "M_end", "sat_row", "alpha_bfit", "alpha_fit",
            "alpha_bounce", "rounds_T", "rounds_L", "slope", "confidence", "bad_rows", "max_period", "note", "T_rounds_head")
    out = {k: r[k] for k in keep if k in r}
    out.update(id=jid, type=typ, wall=tag, N=N, root=root, budget=bud, solve_s=round(t1 - t0, 2),
               analyse_s=round(t2 - t1, 2), rss_mb=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20),
               sets={m: list(s) for m, s in S.items()}, graph=G)
    return out


if __name__ == "__main__":
    N = int(sys.argv[1])
    OUT = sys.argv[2]
    deadline = time.time() + (float(sys.argv[3]) if len(sys.argv) > 3 else 540)
    only = sys.argv[4] if len(sys.argv) > 4 else None
    done = set()
    if os.path.exists(OUT):
        done = {json.loads(l)["id"] for l in open(OUT)}
    ids = set(l.strip() for l in open(only[1:])) if only and only.startswith("@") else None
    jobs = [j for j in job_list() if (only is None or ids is not None or j[1] == only)
            and (ids is None or j[0] in ids) and j[0] not in done]
    print(f"{len(jobs)} jobs left", flush=True)
    n = 0
    for j in jobs:
        if time.time() > deadline:
            break
        r = run(j, N)
        if r["rss_mb"] > 2800:
            print("RSS too high, stopping", r["rss_mb"]); break
        with open(OUT, "a") as f:
            f.write(json.dumps(r) + "\n")
        n += 1
    print(f"wrote {n}, left {len(jobs) - n}, rss {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20:.0f} MB", flush=True)
