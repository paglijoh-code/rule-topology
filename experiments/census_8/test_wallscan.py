#!/usr/bin/env python3
"""Compare wallscan rows against bf2.c cell by cell, plus the {1,2,5,6} t_k/w_k check."""
import json, os, subprocess, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gpatterns import mex_g, eventual
H = os.path.dirname(os.path.abspath(__file__)); OUT = H + "/out"
os.makedirs(OUT, exist_ok=True)
subprocess.check_call(["cc", "-O2", "-o", OUT + "/wallscan", H + "/wallscan.c"])
subprocess.check_call(["cc", "-O2", "-o", OUT + "/bf2", H + "/../bf2.c"])

def csv(x): return ",".join(map(str, x))
def run_ws(N, D, PMAX, S1, pre, per, pat, dump=None, rowfile=None):
    env = dict(os.environ)
    if dump: env["WS_DUMP"] = dump
    cmd = [OUT + "/wallscan", str(N), str(D), str(PMAX), csv(S1), str(pre), str(per), csv(pat)]
    if rowfile: cmd.append(rowfile)
    return json.loads(subprocess.check_output(cmd, env=env))

def gpat(S2):
    g = mex_g(S2); pre, per = eventual(g); return pre, per, g[:pre + per]

pairs = [([1, 2, 5, 6], [1, 2, 3, 4])]
for S1 in ([1], [2, 3], [1, 4], [3, 5, 8], [1, 2, 3, 4], [2, 5, 7], [1, 3, 5, 7, 8], [4, 6], [1, 2, 6, 7, 8]):
    pairs.append((S1, [1, 2, 3, 4]))
pre_S2 = []; long_S2 = []
import itertools
for k in range(1, 9):
    for S2 in itertools.combinations(range(1, 9), k):
        pre, per, _ = gpat(list(S2))
        if pre > 0: pre_S2.append(list(S2))
        if per >= 8: long_S2.append(list(S2))
rng = np.random.default_rng(1)
S1s = [[1, 2], [2, 5], [1, 3, 6], [4, 7, 8], [1, 2, 5, 6], [3, 4], [1, 5, 8], [2, 3, 4, 6, 7]]
for i in range(10):
    pairs.append((S1s[i % len(S1s)], pre_S2[int(rng.integers(len(pre_S2)))]))
for i in range(8):
    pairs.append((S1s[(i + 3) % len(S1s)], long_S2[int(rng.integers(len(long_S2)))]))
print(len(pairs), "pairs;", len(pre_S2), "preperiodic S2,", len(long_S2), "long-period S2")

NB, N, D = 3000, 3000, 800
bad = 0; npre = 0; nincomplete = 0
for S1, S2 in pairs:
    pre, per, pat = gpat(S2)
    npre += pre > 0
    dump = OUT + "/t_dump.bin"; bf = OUT + "/t_bf.bin"
    r = run_ws(N, D, 100, S1, pre, per, pat, dump=dump)
    if r["status"] != "ok": nincomplete += 1; print("  note", S1, S2, r["status"], r["a_stop"])
    done = r["a_stop"]
    rows = np.fromfile(dump, dtype=np.uint8)[:done * D].reshape(done, D)
    subprocess.check_call([OUT + "/bf2", str(NB), csv(S1), csv(S2), bf])
    P = np.fromfile(bf, dtype=np.uint8).reshape(NB + 1, NB + 1)
    cnt = 0
    for a in range(done):
        dmax = min(D, NB - 2 * a + 1)   # b=a+d <= NB
        dmax = min(D, NB - a + 1)
        if dmax <= 0: continue
        ref = P[a, a:a + dmax]
        if not np.array_equal(ref, rows[a, :dmax]):
            bad += 1; print("MISMATCH", S1, S2, "row", a, np.nonzero(ref != rows[a, :dmax])[0][:5]); break
        cnt += dmax
    print("ok", S1, S2, "(pre,per)=", (pre, per), "cells", cnt)

# t_k / w_k
r = run_ws(30000, 2000, 100, [1, 2, 5, 6], 0, 5, [0, 1, 2, 3, 4], rowfile=OUT + "/t_rows.bin")
pres = np.fromfile(OUT + "/t_rows.bin", dtype=np.int32)
print("1256 scan:", r["status"], r["a_stop"], "max_pre", r["max_pre"])
assert r["status"] == "ok"
k = 0; checked = 0
while 7 * k * k + 35 * k + 13 < 30000:
    t = 7 * k * k + 35 * k + 13
    if pres[t] != 35 + 10 * k:
        bad += 1; print("t_k FAIL", k, t, pres[t], 35 + 10 * k)
    checked += 1; k += 1
print("t_k checked", checked)
print("incomplete pairs:", nincomplete)
print("PASS" if bad == 0 and npre >= 1 and len(pairs) >= 20 else "FAIL")
sys.exit(bad != 0)
