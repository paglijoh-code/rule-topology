#!/bin/sh
# Stage 1 of census_10: N=2500, D=1600, PMAX=200 (overflow threshold pre > 600), 14 workers, niced.
cd "$(dirname "$0")"
for s in r10 p7_12 p8_12s p78_rand; do
  python3 scan5.py out/jobs_$s.jsonl out/s1_$s.jsonl 2500 1600 200 --jobs 14 > out/s1_$s.log 2>&1
done
echo done > out/s1.done
