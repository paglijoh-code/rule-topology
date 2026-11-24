#!/usr/bin/env python3
"""scan5.py JOBS.jsonl OUT.jsonl N D PMAX [--jobs 16]
JOBS: one {"S1":[..],"g":{"pre","per","pattern"},"tag":..} per line (from jobs5.py). Runs census_8 wallscan
on each; one JSON line per pair; resumable. Records CPU seconds per pair (child user+sys)."""
import argparse, json, os, resource, subprocess, time
from multiprocessing import Pool
H = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(H, "..", "census_8", "wallscan.c"); BIN = os.path.join(H, "out", "wallscan")

def key(S1, g): return json.dumps([S1, g["pre"], g["per"], g["pattern"]])

def work(a):
    j, N, D, PMAX = a
    S1, g = j["S1"], j["g"]
    cmd = ["nice", "-n", "10", BIN, str(N), str(D), str(PMAX), ",".join(map(str, S1)),
           str(g["pre"]), str(g["per"]), ",".join(map(str, g["pattern"]))]
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    out = subprocess.run(cmd, capture_output=True, text=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = round(r1.ru_utime - r0.ru_utime + r1.ru_stime - r0.ru_stime, 3)
    base = {"S1": S1, "g": {k: g[k] for k in ("pre", "per", "pattern")}, "tag": j.get("tag"), "cpu": cpu}
    if out.returncode: return {**base, "status": "error", "err": out.stderr[:200]}
    r = json.loads(out.stdout); r.update(base); return r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jobs"); ap.add_argument("out")
    ap.add_argument("N", type=int); ap.add_argument("D", type=int); ap.add_argument("PMAX", type=int)
    ap.add_argument("--jobs", dest="np", type=int, default=16)
    a = ap.parse_args()
    os.makedirs(os.path.dirname(BIN), exist_ok=True)
    subprocess.check_call(["cc", "-O2", "-o", BIN, SRC])
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            try: r = json.loads(line); done.add(key(r["S1"], r["g"]))
            except Exception: pass
    todo = [(j, a.N, a.D, a.PMAX) for j in map(json.loads, open(a.jobs)) if key(j["S1"], j["g"]) not in done]
    total = len(todo); t0 = time.time(); cpu = 0.0
    print("todo", total, "already", len(done), flush=True)
    with Pool(a.np) as pool, open(a.out, "a") as f:
        for i, r in enumerate(pool.imap_unordered(work, todo, chunksize=8), 1):
            cpu += r.get("cpu", 0); f.write(json.dumps(r) + "\n"); f.flush()
            if i % 2000 == 0 or i == total:
                el = time.time() - t0
                print("%d/%d wall %.0fs cpu %.0fs eta %.0fs" % (i, total, el, cpu, el / i * (total - i)), flush=True)

if __name__ == "__main__": main()
