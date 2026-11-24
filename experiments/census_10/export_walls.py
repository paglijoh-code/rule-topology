#!/usr/bin/env python3
"""export_walls.py : write census_10/walls.json and census_10/walls_exact.jsonl, the machine-readable table of every exact sqrt wall
(the 30 census walls + A + B). Reads out/census_s2b_*.jsonl, out/sel_*.txt, out/g_realised10.json, out/s2b/{A,B}."""
import json, os, subprocess
from fractions import Fraction as F
H = os.path.dirname(os.path.abspath(__file__)); O = os.path.join(H, "out"); PY = sys.executable
real = {(g["pre"], g["per"], tuple(g["pattern"])): g["S2s"] for g in json.load(open(os.path.join(O, "g_realised10.json")))}
DEF = ("Rows r_a(d) = P(a, a+d) in {0,1} (1 = P-position), d < D. p_a = least tail period <= PMAX of r_a on [D-4*PMAX, D); "
       "pre(a) = least y with r_a(x) = r_a(x+p_a) for all y <= x < D-p_a. Wall M(a) = max_{b<=a} pre(b). "
       "Records of M closer than 40 rows are merged into one round; round j starts at T_j (first record row) and lifts M to L_j. "
       "Super-round of q rounds: class i, index k: t_k = T_{j0+i+kq}, w_k = L_{j0+i+kq}; gap_k = t_{k+1} - t_k.")
def entry(tag, S1, pre, per, pat, law, scan, files):
    S2s = real.get((pre, per, tuple(pat)))
    cl = []
    for c in law["classes"]:
        t0, g0, w0, D, s = c["t0"], c["gap0"], c["w0"], law["Delta"], law["s"]
        # t_k = t0 + g0 k + (s/2) k(k-1);  gap_k = g0 + s k;  w_k = w0 + D k
        cl.append(dict(t0=t0, gap0=g0, w0=w0, k_range=[0, c["k_checked"]],
                       t_k=dict(a2=str(F(s, 2)), a1=str(F(g0) - F(s, 2)), a0=t0, text=c["t_k"]),
                       gap_k=dict(a1=s, a0=g0), w_k=dict(a1=D, a0=w0, text=c["w_k"]),
                       gap_over_w=dict(lam=str(F(s, D)), mu=str(F(g0) - F(s, D) * w0))))
    return dict(tag=tag, S1=[int(x) for x in S1], g=dict(pre=pre, per=per, pattern=list(pat)),
                g_realised=bool(S2s), S2_example=(min(S2s, key=lambda x: (len(x), x)) if S2s else None),
                q=law["q"], j0=law["j0"], Delta=law["Delta"], s=law["s"], lam=str(F(law["s"], law["Delta"])), c=law["c"],
                Delta_over_gper=str(F(law["Delta"], per)), classes=cl, scan=scan, files=files,
                legs=None, legs_note="leg speeds measured only for A (6/5 + 1/5) and B (1 + 0); others not measured")
out = []
for tag, S1, pre, per, pat in [("A", [1,2,5,6], 0, 5, [0,1,2,3,4]), ("B", [1,2,3,4,7,8], 0, 6, [0,1,2,3,2,4])]:
    p = os.path.join(O, "s2b", tag + ".pre")
    law = json.loads(subprocess.run([PY, os.path.join(H, "fit3.py"), p], capture_output=True, text=True).stdout)
    info = json.loads(open(p[:-4] + ".json").read().strip().splitlines()[-1])
    e = entry(tag, S1, pre, per, pat, law, {k: info[k] for k in ("N", "D", "PMAX", "status", "a_stop")},
              {"pre": f"census_10/out/s2b/{tag}.pre", "per": f"census_10/out/s2b/{tag}.pre.per", "summary": f"census_10/out/s2b/{tag}.json"})
    if tag == "B": e["legs"] = {"inv_vL": "1", "inv_vR": "0"}; e["files"]["rows_dump"] = "census_10/out/B_rows.bin (wallscan 5000 1800 250, N*D bytes)"
    if tag == "A": e["legs"] = {"inv_vL": "6/5", "inv_vR": "1/5"}
    out.append(e)
sel = {}
for s in ["r10", "p7_12", "p8_12s", "p78_rand"]:
    for l in open(os.path.join(O, f"sel_{s}.txt")):
        f = l.split(); sel[(s, f[0])] = f
for cf in ["census_s2b_r10.jsonl", "census_s2b_rest.jsonl"]:
    for l in open(os.path.join(O, cf)):
        r = json.loads(l); L = r["law"]
        if L["kind"] != "sqrt": continue
        s = r["dir"].split("s2b_")[1]; f = sel[(s, r["name"])]
        info = json.loads(open(os.path.join(H, r["dir"], r["name"] + ".json")).read().strip().splitlines()[-1]) if not r["dir"].startswith("/") else json.loads(open(os.path.join(r["dir"], r["name"] + ".json")).read().strip().splitlines()[-1])
        d = os.path.relpath(os.path.join(H, r["dir"]) if not r["dir"].startswith("/") else r["dir"], os.path.join(H, ".."))
        out.append(entry(f"{s}:{r['name']}", f[1].split(","), int(f[2]), int(f[3]), [int(x) for x in f[4].split(",")], L,
                         {k: info[k] for k in ("N", "D", "PMAX", "status", "a_stop")},
                         {"pre": f"{d}/{r['name']}.pre", "per": f"{d}/{r['name']}.pre.per", "summary": f"{d}/{r['name']}.json"}))
doc = dict(definition=DEF, generator="census_10/export_walls.py (fit3.py exact fits; checks 2*t_k == 2*t0 + 2*gap0*k + s*k*(k-1) and w_k == w0 + Delta*k on every k in k_range)",
           file_formats={"pre": "int32 little-endian, one per row a = 0..a_stop-1: pre(a)", "per": "int32 LE, p_a per row",
                         "rows_dump": "WS_DUMP: uint8 per cell, row-major, N rows x D bytes, r_a(d) in {0,1}"},
           walls=out)
json.dump(doc, open(os.path.join(H, "walls.json"), "w"), indent=1)
with open(os.path.join(H, "walls_exact.jsonl"), "w") as fh:
    for e in out: fh.write(json.dumps(e) + "\n")
print(len(out), sum(e["g_realised"] for e in out))
