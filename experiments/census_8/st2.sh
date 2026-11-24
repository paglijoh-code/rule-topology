#!/bin/sh
# stage 2: st2.sh JOBFILE N  -> out/$OUTD/NAME.json (+ NAME.pre / NAME.pre.per)
cd "$(dirname "$0")"
N=$2; OUTD=${3:-st2}
cat "$1" | xargs -P 12 -L 1 sh -c 'nice -n 10 out/wallscan '"$N"' $1 $2 $3 $4 $5 $6 out/'"$OUTD"'/$0.pre > out/'"$OUTD"'/$0.json'
