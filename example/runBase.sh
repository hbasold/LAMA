#!/bin/bash

workdir=tmp

base=`basename "$1"`
name=${base%.*}

if [ -z "$4" ]; then
  d="100";
else
  d="$4";
fi
strategy="-s $3 -o depth=$d -o progress"

echo "Running $base"

mkdir -p "$workdir"

time ../lamaSMT/dist/build/lamasmt/lamasmt -i $1 $strategy --scenario="$workdir/$name.sss" --node-name=$2 --enum-impl=bits
