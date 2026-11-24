#!/usr/bin/env python3
"""select3.py : stage 2c job lists (CPU cap lifted 2026-11-22). From each out/s2o_SET/*.json take
noperiod pairs -> out/sel_SET_np.txt and pairs that overflowed before a = 3000 -> out/sel_SET_of.txt (lines copied from out/sel_SET_o.txt)."""
import json, os, sys
H = os.path.dirname(os.path.abspath(__file__)); O = os.path.join(H, "out")
for s in ["r10", "p7_12", "p8_12s", "p78_rand"]:
    sel = {l.split()[0]: l for l in open(os.path.join(O, f"sel_{s}_o.txt"))}
    np_, of = [], []
    for name, l in sel.items():
        try: info = json.loads(open(os.path.join(O, f"s2o_{s}", name + ".json")).read().strip().splitlines()[-1])
        except Exception: continue
        if info["status"] == "noperiod": np_.append(l)
        elif info["status"] == "overflow" and info["a_stop"] < 3000: of.append(l)
    open(os.path.join(O, f"sel_{s}_np.txt"), "w").writelines(np_); open(os.path.join(O, f"sel_{s}_of.txt"), "w").writelines(of)
    print(s, len(np_), len(of))
