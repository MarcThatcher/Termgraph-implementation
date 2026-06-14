#!/bin/bash
# Usage: flin.sh [-imm] [-hof] [-mpp] [-npm] <filename.txt>

FILE="${@: -1}"         # last argument is the filename
FLAGS="${@:1:$#-1}"     # everything else is flags
BASE="${FILE%.txt}"     # strip .txt extension

./flin $FLAGS -bat "$FILE"
inpla -f "${BASE}.in"

# save and then 
# chmod +x flin.sh
# Run as:
#  ./flin.sh [flags] <filename>.txt