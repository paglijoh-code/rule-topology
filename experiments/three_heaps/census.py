"""three_heaps/census.py — all pairs S1 -> S2, S ⊆ {1..4}, three heaps, phase-boundary summary. Output raw/census_N.jsonl"""
import sys, json, itertools, time
from multiprocessing import Pool
from lib3 import chain, analyse
N = int(sys.argv[1])
subs = [s for r in range(1, 5) for s in itertools.combinations(range(1, 5), r)]
def job(pair):
    T = chain(N, list(pair)); r, C = analyse(T)
    r["S1"], r["S2"] = pair; r["face_P"] = int(T[:, :, 0].sum())
    return json.dumps(r, default=str)
if __name__ == "__main__":
    t = time.time()
    pairs = [(a, b) for a in subs for b in subs]
    with Pool(8) as P, open("raw/census_%d.jsonl" % N, "w") as f:
        for line in P.imap(job, pairs): f.write(line + "\n"); f.flush()
    print("done", len(pairs), "pairs, %.0fs" % (time.time() - t))
