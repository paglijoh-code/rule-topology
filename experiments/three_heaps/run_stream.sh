#!/bin/bash
# three_heaps/run_stream.sh N — streaming analyses (stream3) for the 9 growers at size N, 3 at a time; resumable (skips done pairs).
# Env PAIRS (S1:S2 list) and RD (diag half-width) override the defaults; [1,2,3,4]->* runs with NOHASH above N=1500.
# Outputs big/N/<S1>_<S2>.{cx,prof,diag,win0..3} (regenerable, gitignored).
N=$1; cd "$(dirname "$0")"; mkdir -p big/$N
L=256; W1=$((N/5-128)); W2=$((N/2-128)); W3=$((N-300)); 
PAIRS=${PAIRS:-"2,4:1,2,3,4 1,3,4:1,2,3,4 1,2,3,4:1,3,4 1,2,3:1,2 1,2,3:1,2,4 1,2,3:3,4 1,2,3:1,3,4 3,4:1,2,3,4 2,3,4:1,2,3,4"}
RD=${RD:-150}
run() { p=$1; a=${p%%:*}; b=${p##*:}; o=big/$N/${a}_${b}; [ -s $o.prof ] && return
  /usr/bin/time -l env $([ "$a" = "1,2,3,4" ] && [ $N -gt 1500 ] && echo NOHASH=1) ./stream3 $N $a $b $o $RD 60 $L $W1 $W1 $W1 $L $W2 $W2 $W2 $L $W3 $W3 $W3 $L $((N/10)) $((N*4/10)) $((N*7/10)) > $o.log 2>&1; }
export -f run; export N L W1 W2 W3 RD
echo $PAIRS | tr ' ' '\n' | xargs -P 3 -I{} bash -c 'run {}'
echo done
