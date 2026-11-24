#!/usr/bin/env python3
"""census.py OUT.jsonl DIR [DIR...] : run fit3.py on every DIR/*.pre with its DIR/*.json and write one JSON line per
pair (name, set, status, a_stop, row tail periods, fit3 law). Then print the sqrt walls (exact laws) and counts."""
import sys, json, glob, os, subprocess, collections
HERE = os.path.dirname(os.path.abspath(__file__)); PY = sys.executable
out = open(sys.argv[1], "w"); cnt = collections.Counter()
for d in sys.argv[2:]:
    for pre in sorted(glob.glob(os.path.join(d, "*.pre"))):
        name = os.path.basename(pre)[:-4]
        try: info = json.loads(open(pre[:-4] + ".json").read().strip().splitlines()[-1])
        except Exception: info = {"status": "unreadable"}
        try: law = json.loads(subprocess.run([PY, os.path.join(HERE, "fit3.py"), pre], capture_output=True, text=True).stdout)
        except Exception: law = {"kind": "nofit", "exact": False}
        r = {"name": name, "dir": d, "status": info.get("status"), "a_stop": info.get("a_stop"),
             "tail_periods": info.get("tail_periods"), "max_pre": info.get("max_pre"), "law": law}
        out.write(json.dumps(r) + "\n"); cnt[(info.get("status"), law.get("kind"), law.get("exact"))] += 1
print(dict(cnt))
