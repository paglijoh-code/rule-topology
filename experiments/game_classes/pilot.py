#!/usr/bin/env python3
"""game_classes pilot: classify ~30 games and walk two atomic paths.  One child process per game, run
one after the other (peak RSS is per child).  Usage:
  nice -n 10 python3 game_classes/pilot.py [N]        # runs everything, writes game_classes/pilot_results.json
  python game_classes/pilot.py --one NAME N                      # one game, prints one JSON line
"""
import json
import os
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import classify as C  # noqa: E402
import games as G  # noqa: E402


def S(*xs):
    return G.subtraction(xs)


def build():
    """name -> (mode, thunk): mode in normal / misere / push(A, B)."""
    d = {}
    for k in (2, 5, 9):
        d[f"sub{{1..{k}}}"] = ("normal", lambda k=k: G.subtraction(range(1, k + 1)))
    d["sub{2,3}"] = ("normal", lambda: S(2, 3))
    d["sub{1,3,4}"] = ("normal", lambda: S(1, 3, 4))
    d["sub{1,2,5,6}"] = ("normal", lambda: S(1, 2, 5, 6))
    for ss in ((1,), (1, 2), (1, 2, 3), (1, 2, 3, 4, 5), (2, 3, 7)):
        d["wsub{" + ",".join(map(str, ss)) + "}"] = ("normal", lambda ss=ss: G.wythoff_sub(ss))
    d["nim"] = ("normal", G.nim)
    d["wythoff"] = ("normal", G.wythoff)
    d["euclid"] = ("normal", G.euclid)
    for k in (1, 2, 3, 8):
        d[f"trunc_euclid{k}"] = ("normal", lambda k=k: G.trunc_euclid(k))
    d["larger_only"] = ("normal", G.larger_only)
    for K in (8, 2, 1):
        d[f"larger_cap{K}"] = ("normal", lambda K=K: G.larger_cap(K))
    d["misere nim"] = ("misere", G.nim)
    d["misere wythoff"] = ("misere", G.wythoff)
    d["misere euclid"] = ("misere", G.euclid)
    d["misere sub{1..5}"] = ("misere", lambda: G.subtraction(range(1, 6)))
    d["misere sub{1,2,5,6}"] = ("misere", lambda: S(1, 2, 5, 6))
    d["misere wsub{1,2}"] = ("misere", lambda: G.wythoff_sub((1, 2)))
    d["misere trunc_euclid2"] = ("misere", lambda: G.trunc_euclid(2))
    for nm, (A, B) in {
        "nim (+) wythoff": (G.nim, G.wythoff),
        "wythoff (+) nim": (G.wythoff, G.nim),
        "nim (+) euclid": (G.nim, G.euclid),
        "euclid (+) nim": (G.euclid, G.nim),
        "sub{1,2,5,6} (+) sub{1,2,3,4}": (lambda: S(1, 2, 5, 6), lambda: S(1, 2, 3, 4)),
        "sub{1,2,3} (+) nim": (lambda: S(1, 2, 3), G.nim),
        "sub{1,2} (+) wythoff": (lambda: S(1, 2), G.wythoff),
        "wsub{1,2} (+) sub{1,2}": (lambda: G.wythoff_sub((1, 2)), lambda: S(1, 2)),
    }.items():
        d[nm] = ("push", (A, B))
    for k in range(1, 13):  # path 1: subtraction {1..k} toward Nim
        d[f"path1 sub{{1..{k}}}"] = ("normal", lambda k=k: G.subtraction(range(1, k + 1)))
    for lab, g in G.nim_to_euclid_path():  # path 2: Nim -> Euclid rule atoms
        d[f"path2 {lab}"] = ("normal", lambda g=g: g)
    return d


def run_one(name, N):
    mode, th = build()[name]
    t0 = time.time()
    if mode == "push":
        T = G.push_table(th[0](), th[1](), N)
        g = None
    else:
        game = th()
        T = G.misere_table(game, N) if mode == "misere" else G.normal_table(game, N)
        g = None
    t1 = time.time()
    r = C.classify(T, g)
    t2 = time.time()
    w = r["detail"].get("wall") or {}
    out = dict(name=name, N=N, cls=r["cls"], conf=r["conf"], summary=C.summary(r),
               t_solve=round(t1 - t0, 2), t_classify=round(t2 - t1, 2),
               rss_mb=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20, 0),
               density=round(float((T == 1)[N // 10:, N // 10:].mean()), 4),
               scores={k: round(float(v), 3) for k, v in r["scores"].items()},
               wall=dict(verdict=w.get("verdict"), alpha=w.get("alpha"), alpha_range=w.get("alpha_range"),
                         p=w.get("p"), risers=w.get("risers")) if w else None)
    return out


if __name__ == "__main__":
    if "--one" in sys.argv:
        i = sys.argv.index("--one")
        print(json.dumps(run_one(sys.argv[i + 1], int(sys.argv[i + 2]))))
        sys.exit(0)
    if "--scale" in sys.argv:  # runtime / memory scaling, N <= 1000
        out = []
        for name in ("nim", "sub{1,2,5,6}", "wsub{1,2,3}", "euclid", "trunc_euclid3", "misere sub{1..5}",
                     "sub{1,2,5,6} (+) sub{1,2,3,4}", "nim (+) euclid"):
            for N in (200, 400, 800, 1000):
                p = subprocess.run([sys.executable, __file__, "--one", name, str(N)], capture_output=True, text=True,
                                   timeout=300, env=dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1"))
                r = json.loads(p.stdout)
                out.append(r)
                print(name, N, r["cls"], r["t_solve"], r["t_classify"], r["rss_mb"], flush=True)
        json.dump(out, open(os.path.join(HERE, "scale_results.json"), "w"), indent=1)
        sys.exit(0)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 800
    res = []
    for name in build():
        p = subprocess.run([sys.executable, __file__, "--one", name, str(N)], capture_output=True, text=True,
                           timeout=300, env=dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1"))
        if p.returncode:
            res.append(dict(name=name, N=N, cls="ERROR", conf=0, summary=p.stderr.strip().splitlines()[-1][:80]))
        else:
            res.append(json.loads(p.stdout))
        r = res[-1]
        print(r["name"], r["cls"], r["conf"], r["summary"], r.get("t_solve"), r.get("t_classify"), r.get("rss_mb"), flush=True)
    json.dump(res, open(os.path.join(HERE, "pilot_results.json"), "w"), indent=1)
