#!/bin/bash

proofNode="Proof::LCHAL_DCCA"
invariant="H1_out"
workdir=tmp

if [ -z "$2" ]; then
  strategy="kinduct";
else
  strategy="$2";
fi

base=`basename "$1"`
name=${base%.*}

echo "Running $base"

mkdir -p "$workdir"

../scade2lama/dist/build/scade2lama/scade2lama -i $1 -f "$workdir/$name.lm" --inline=state-scope "$proofNode" --invariant="$invariant"

./runBase.sh "$workdir/$name.lm" $proofNode $strategy "40"
