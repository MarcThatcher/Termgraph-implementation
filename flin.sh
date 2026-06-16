#!/bin/bash
# Usage: flin.sh [-imm] [-hof] [-mpp] [-npm] <filename.txt>

FILE="${@: -1}"         # last argument is the filename
FLAGS="${@:1:$#-1}"     # everything else is flags

./flin $FLAGS -bat "$FILE"

BASE="${FILE%.txt}"     # strip .txt extension

inpla -f "${BASE}.in"

# save and then 
# chmod +x flin.sh
# Run as:
#  ./flin.sh [flags] <filename>.txt