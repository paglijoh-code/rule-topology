"""three_heaps/big600.py — pairs still growing at N=450: block complexity at 300, 450, 600 (N = 600). Resumable: skips pairs already
in raw/big_600.jsonl.  Records per-pair CPU seconds."""
import json, os, time, numpy as np
from multiprocessing import Pool
from lib3 import chain
from big import codes
N = 600; k = 4; OUT = "raw/big_600.jsonl"
def job(pair):
    t = time.process_time(); T = chain(N, [tuple(pair[0]), tuple(pair[1])]); C = codes(T); del T
    cx = [len(np.unique(C[:n - k + 1, :n - k + 1, :n - k + 1])) for n in (300, 450, 600)]
    return json.dumps(dict(S1=pair[0], S2=pair[1], cx=cx, cpu_s=round(time.process_time() - t, 1)))
if __name__ == "__main__":
    R = [json.loads(l) for l in open("raw/big_450.jsonl")]
    pairs = [(r["S1"], r["S2"]) for r in R if r["cx"][2] != r["cx"][1]]
    done = {(tuple(r["S1"]), tuple(r["S2"])) for r in map(json.loads, open(OUT))} if os.path.exists(OUT) else set()
    todo = [p for p in pairs if (tuple(p[0]), tuple(p[1])) not in done]
    with Pool(2) as P, open(OUT, "a") as f:
        for line in P.imap_unordered(job, todo): f.write(line + "\n"); f.flush()
    print("done", len(pairs))
