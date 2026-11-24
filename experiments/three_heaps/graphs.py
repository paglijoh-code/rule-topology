"""three_heaps/graphs.py — S2 stage: rule graphs on three heaps over Sub(S), S ⊆ {1..4}.
  part 'cycles': budgeted triangles (all rotation classes) at N = 24 and 36; 4- and 5-cycles (random) at N = 24.
  part 'chains': all 3375 chains S1 -> S2 -> S3 at N = 150: pattern complexity at n = 75, 150.
  part 'forks':  all forks S1 -> {S2, S3} (S2 < S3) at N = 150 via the tail law Phi_1(P2 ∪ P3): complexity.
Output raw/<part>.jsonl"""
import sys, json, itertools, random, time
import numpy as np
from multiprocessing import Pool
from lib3 import chain, phi, cycle, complexity
subs = [s for r in range(1, 5) for s in itertools.combinations(range(1, 5), r)]
def P0(N, S):
    g = []
    for h in range(N + 1):
        seen = {g[h - s] for s in S if s <= h}; m = 0
        while m in seen: m += 1
        g.append(m)
    g = np.array(g); return (g[:, None, None] ^ g[None, :, None] ^ g[None, None, :]) == 0
def jcyc(sets):
    return json.dumps(dict(sets=sets, n24=cycle(24, sets), n36=cycle(36, sets) if len(sets) == 3 else None))
def jchain(sets):
    T = chain(150, list(sets)); return json.dumps(dict(sets=sets, cx=complexity(T, 4, [75, 150]), dens=float(T.mean())))
def jfork(t):
    s1, s2, s3 = t; T = phi(150, s1, P0(150, s2) | P0(150, s3))
    return json.dumps(dict(sets=t, cx=complexity(T, 4, [75, 150]), dens=float(T.mean())))
if __name__ == "__main__":
    part = sys.argv[1]; t0 = time.time(); random.seed(5)
    if part == "cycles":
        tri = sorted({min((t[i:] + t[:i]) for i in range(3)) for t in itertools.product(subs, repeat=3)})
        jobs = [list(t) for t in tri] + [[random.choice(subs) for _ in range(4)] for _ in range(300)] + [[random.choice(subs) for _ in range(5)] for _ in range(200)]
        fn = jcyc
    elif part == "chains":
        jobs = list(itertools.product(subs, repeat=3)); fn = jchain
    else:
        jobs = [(a, b, c) for a in subs for b, c in itertools.combinations(subs, 2)]; fn = jfork
    with Pool(8) as P, open("raw/%s.jsonl" % part, "w") as f:
        for line in P.imap(fn, jobs, chunksize=4): f.write(line + "\n"); f.flush()
    print("done", part, len(jobs), "%.0fs" % (time.time() - t0))
