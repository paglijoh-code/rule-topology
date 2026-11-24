#!/usr/bin/env python3
"""scan.py GFILE OUT.jsonl N D PMAX [--jobs 16] [--limit K]
Every nonempty S1 subset of {1..8} x every g in GFILE -> wallscan; one JSON line per pair; resumable."""
import argparse, json, os, subprocess, sys, time
from itertools import combinations
from multiprocessing import Pool
H = os.path.dirname(os.path.abspath(__file__))
BIN = H + "/out/wallscan"

def key(S1, g): return json.dumps([S1, g["pre"], g["per"], g["pattern"]])

def work(a):
    S1, g, N, D, PMAX = a
    cmd = ["nice", "-n", "10", BIN, str(N), str(D), str(PMAX), ",".join(map(str, S1)),
           str(g["pre"]), str(g["per"]), ",".join(map(str, g["pattern"]))]
    t = time.time()
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode:
        return {"S1": S1, "g": {k: g[k] for k in ("pre", "per", "pattern")}, "status": "error", "err": out.stderr[:200]}
    r = json.loads(out.stdout)
    r.update({"S1": S1, "g": {k: g[k] for k in ("pre", "per", "pattern")}, "secs": round(time.time() - t, 3)})
    return r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("gfile"); ap.add_argument("out")
    ap.add_argument("N", type=int); ap.add_argument("D", type=int); ap.add_argument("PMAX", type=int)
    ap.add_argument("--jobs", type=int, default=16); ap.add_argument("--limit", type=int, default=0)
    a = ap.parse_args()
    subprocess.check_call(["cc", "-O2", "-o", BIN, H + "/wallscan.c"])
    gs = json.load(open(a.gfile))
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            try: r = json.loads(line); done.add(key(r["S1"], r["g"]))
            except Exception: pass
    todo = []
    for k in range(1, 9):
        for S1 in combinations(range(1, 9), k):
            for g in gs:
                if key(list(S1), g) not in done: todo.append((list(S1), g, a.N, a.D, a.PMAX))
    if a.limit: todo = todo[:a.limit]
    total = len(todo); t0 = time.time(); print("todo", total, "already", len(done), flush=True)
    with Pool(a.jobs) as pool, open(a.out, "a") as f:
        for i, r in enumerate(pool.imap_unordered(work, todo, chunksize=4), 1):
            f.write(json.dumps(r) + "\n"); f.flush()
            if i % 500 == 0 or i == total:
                el = time.time() - t0
                print("%d/%d elapsed %.0fs eta %.0fs" % (i, total, el, el / i * (total - i)), flush=True)

if __name__ == "__main__": main()
