#!/bin/sh
# Stage 2c (owner lifted the CPU cap, 2026-11-22): rerun the undecided pairs bigger.
# noperiod at 2o -> N=30000 D=20000 PMAX=2000; early overflow at 2o -> N=100000 D=16000 PMAX=600. Resumable via .done markers.
cd "$(dirname "$0")"
for S in r10 p7_12 p8_12s p78_rand; do
  [ -f out/s2c_np_$S.done ] || { ./run_s2.sh out/sel_${S}_np.txt 30000 20000 2000 out/s2c_np_$S && touch out/s2c_np_$S.done; }
  [ -f out/s2c_of_$S.done ] || { ./run_s2.sh out/sel_${S}_of.txt 100000 16000 600 out/s2c_of_$S && touch out/s2c_of_$S.done; }
done
echo stage2c-done
