#!/bin/bash

workdir=tmp

base=`basename "$1"`
name=${base%.*}

echo "Translating $base"

mkdir -p "$workdir"

../scade2lama/dist/build/scade2lama/scade2lama -i $1 -f "$workdir/$name.lm" --inline=state-scope --invariant="$3" "$2"
