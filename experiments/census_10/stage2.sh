#!/bin/sh
# Tiered stage 2 for one stage-1 result set S (r10, p7_12, p8_12s, p78_rand).
# 2a: growing pairs at N=12000, D=4000, PMAX=400.  2o: late-overflow + noperiod at N=6000, D=4200, PMAX=600.
cd "$(dirname "$0")"; S=$1
python3 select2.py out/s1_$S.jsonl out/sel_$S.txt
grep ' growing' out/sel_$S.txt > out/sel_${S}_g.txt; grep -v ' growing' out/sel_$S.txt > out/sel_${S}_o.txt
./run_s2.sh out/sel_${S}_g.txt 12000 4000 400 out/s2a_$S
./run_s2.sh out/sel_${S}_o.txt 6000 4200 600 out/s2o_$S
