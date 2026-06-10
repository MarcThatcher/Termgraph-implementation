#!/bin/bash

# Usage: ./flin.sh [flags] filename
# run chmod +x flin first

FLAGS=""
FILENAME=""
BAT=0

for arg in "$@"; do
    if [[ "$arg" == -* ]]; then
        FLAGS="$FLAGS $arg"
        if [[ "$arg" == "-bat" ]]; then
            BAT=1
        fi
    else
        FILENAME="$arg"
    fi
done

runghc Trans.hs $FLAGS $FILENAME

if [[ $BAT -eq 1 ]]; then
    OUTFILE="${FILENAME%.txt}.in"
    inpla -f "$OUTFILE"
fi