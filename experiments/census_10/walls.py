#!/usr/bin/env python3
"""walls.py : collect every exact sqrt wall from the stage-2b census files into out/walls.jsonl and print a markdown table."""
import json, os
from fractions import Fraction as F
H = os.path.dirname(os.path.abspath(__file__)); O = os.path.join(H, "out")
real = {(g["pre"], g["per"], tuple(g["pattern"])): g["S2s"] for g in json.load(open(os.path.join(O, "g_realised10.json")))}
sel = {}
for s in ["r10", "p7_12", "p8_12s", "p78_rand"]:
    for l in open(os.path.join(O, f"sel_{s}.txt")):
        f = l.split(); sel[(s, f[0])] = f
rows = []
for cf in ["census_s2b_r10.jsonl", "census_s2b_rest.jsonl"]:
    for l in open(os.path.join(O, cf)):
        r = json.loads(l); L = r["law"]
        if L["kind"] != "sqrt": continue
        s = r["dir"].split("s2b_")[1]; f = sel[(s, r["name"])]
        S1 = f[1]; pre, per = int(f[2]), int(f[3]); pat = tuple(int(x) for x in f[4].split(","))
        S2s = real.get((pre, per, pat)); lam = F(L["s"], L["Delta"])
        c0 = L["classes"][0]
        rows.append(dict(set=s, S1=S1, g_pre=pre, g_per=per, g=f[4].replace(",", ""), S2=(min(S2s, key=lambda x: (len(x), x)) if S2s else None),
                         q=L["q"], Delta=L["Delta"], s=L["s"], lam=str(lam), c=L["c"], onset=c0["t0"], w_onset=c0["w0"],
                         k_checked=min(c["k_checked"] for c in L["classes"]), last_T=L["last_T"], row_period=r["tail_periods"][0],
                         Delta_over_gper=str(F(L["Delta"], per)), classes=L["classes"]))
json.dump(rows, open(os.path.join(O, "walls.json"), "w"), indent=0)
print("| set | S1 | g (pre+period) | e.g. S2 | q | Δ | s | λ=s/Δ | c | onset a | super-rounds checked/class | row period | Δ/per(g) |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for w in sorted(rows, key=lambda w: (w["g_per"], w["g"], w["S1"])):
    g = w["g"]; gs = (g[:w["g_pre"]] + "·" + g[w["g_pre"]:]) if w["g_pre"] else g
    print(f"| {w['set']} | {{{w['S1']}}} | {gs} ({w['g_pre']}+{w['g_per']}) | {w['S2'] and '{'+','.join(map(str,w['S2']))+'}' or '—'} | {w['q']} | {w['Delta']} | {w['s']} | {w['lam']} | {w['c']} | {w['onset']} | {w['k_checked']} | {w['row_period']} | {w['Delta_over_gper']} |")
print(len(rows))
