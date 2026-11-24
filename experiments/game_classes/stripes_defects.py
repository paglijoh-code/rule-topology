#!/usr/bin/env python3
"""game_classes/stripes_defects.py: how clean are the census 'stripes'?  For a seeded sample of 100 push results
labelled stripes at N=2000, the exact far-field mismatch of the reported period shift (a-direction).
Output game_classes/stripes_defects.jsonl (id, period, mismatch fraction).   nice -n 10 python3 game_classes/stripes_defects.py"""
import json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, ".."))
import numpy as np
import census as CE
rs = [json.loads(l) for l in open(os.path.join(HERE, "census_N2000.jsonl"))]
st = [r for r in rs if r["cls"] == "stripes" and r["id"].startswith("push:")]
random.Random(11).shuffle(st)
N = 2000; M = 200
with open(os.path.join(HERE, "stripes_defects.jsonl"), "w") as f:
    for r in st[:100]:
        T = CE.table(r["id"], N); p = r["period"][0]
        X = T[M:N + 1 - p, M:]
        mis = float((X != T[M + p:, M:]).mean())
        f.write(json.dumps(dict(id=r["id"], period=r["period"], mismatch=mis)) + "\n")
