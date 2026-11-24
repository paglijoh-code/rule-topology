#!/bin/sh
# Prediction-test scan (fixed before the scan; run only after PREREG.md and out/pred_all.jsonl's hash are committed).
# S1: every pair, N=2500 D=1600 PMAX=200 (= census_10 stage 1). Route (census_10/select2.py): growing / noperiod / late overflow.
# S2a: routed pairs at N=12000 D=6000 PMAX=600. Not bounded (M(N/2) < M(N)) or not ok -> S2b at N=100000 D=8000 PMAX=400,
# overflow there -> rerun D=20000 PMAX=600. fit3 on every S2b row file. Census -> out/census.jsonl (score.py).
set -e
cd "$(dirname "$0")"; M5A=../census_10
py() { python3 "$@"; }
py - <<'PY'
import json
with open('out/jobs_s1.jsonl', 'w') as f:
    for l in open('out/jobs.jsonl'):
        j = json.loads(l); f.write(json.dumps(dict(S1=j['S1'], g=dict(pre=j['gpre'], per=j['gper'], pattern=j['gpat']), tag=j['id'])) + '\n')
PY
[ -s out/s1.jsonl ] && [ "$(wc -l < out/s1.jsonl)" -ge "$(wc -l < out/jobs_s1.jsonl)" ] || py $M5A/scan5.py out/jobs_s1.jsonl out/s1.jsonl 2500 1600 200 --jobs 14 > out/s1.log 2>&1
py $M5A/select2.py out/s1.jsonl out/sel.txt
run() { # JOBFILE N D PMAX OUTDIR
  mkdir -p "$5"; cut -d' ' -f1-5 "$1" | xargs -P 14 -L 1 sh -c 'nice -n 10 ../census_10/out/wallscan '"$2 $3 $4"' $1 $2 $3 $4 '"$5"'/$0.pre > '"$5"'/$0.json'
}
run out/sel.txt 12000 6000 600 out/s2a
py - <<'PY'
import json, numpy as np, os
o = open('out/sel2b.txt', 'w')
for l in open('out/sel.txt'):
    n = l.split()[0]; r = json.load(open(f'out/s2a/{n}.json'))
    p = np.fromfile(f'out/s2a/{n}.pre', dtype=np.int32)
    bounded = r['status'] == 'ok' and len(p) and p[: len(p) // 2].max() == p.max()
    if not bounded: o.write(l)
PY
run out/sel2b.txt 100000 8000 400 out/s2b
py - <<'PY'
import json
o = open('out/sel2c.txt', 'w')
for l in open('out/sel2b.txt'):
    n = l.split()[0]; r = json.load(open(f'out/s2b/{n}.json'))
    if r['status'] == 'overflow': o.write(l)
PY
run out/sel2c.txt 100000 20000 600 out/s2c
py - <<'PY'
import json, subprocess, os
out = open('out/census.jsonl', 'w')
for l in open('out/sel2b.txt'):
    n = l.split()[0]; d = 'out/s2c' if os.path.exists(f'out/s2c/{n}.json') else 'out/s2b'
    r = json.load(open(f'{d}/{n}.json'))
    f = json.loads(subprocess.run(['python3', '../census_10/fit3.py', f'{d}/{n}.pre'], capture_output=True, text=True).stdout or '{}')
    out.write(json.dumps(dict(name=n, route=l.split()[5], status=r['status'], a_stop=r['a_stop'], max_pre=r['max_pre'], fit=f)) + '\n')
PY
echo scan done > out/scan.done
