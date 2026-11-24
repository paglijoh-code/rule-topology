"""three_heaps/census_cx.py — pattern complexity (distinct 4x4x4 blocks) at n = 75, 150, 300 for all 225 pairs."""
import json, itertools, time
from multiprocessing import Pool
from lib3 import chain, complexity
subs = [s for r in range(1, 5) for s in itertools.combinations(range(1, 5), r)]
def job(pair):
    T = chain(300, list(pair)); c = complexity(T, 4, [75, 150, 300])
    return json.dumps(dict(S1=pair[0], S2=pair[1], cx=c))
if __name__ == "__main__":
    t = time.time(); pairs = [(a, b) for a in subs for b in subs]
    with Pool(8) as P, open("raw/cx_300.jsonl", "w") as f:
        for line in P.imap(job, pairs): f.write(line + "\n"); f.flush()
    print("done %.0fs" % (time.time() - t))
