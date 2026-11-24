#!/bin/sh
# stage 2: run_s2.sh JOBFILE N D PMAX OUTDIR -> OUTDIR/NAME.json (+ NAME.pre, NAME.pre.per as int32)
cd "$(dirname "$0")"; mkdir -p "$5"
cut -d' ' -f1-5 "$1" | xargs -P 14 -L 1 sh -c 'nice -n 10 out/wallscan '"$2 $3 $4"' $1 $2 $3 $4 '"$5"'/$0.pre > '"$5"'/$0.json'
