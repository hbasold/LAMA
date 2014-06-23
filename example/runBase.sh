#!/bin/bash

workdir=tmp

base=`basename "$1"`
name=${base%.*}

if [ -z "$4" ]; then
  d="100";
else
  d="$4";
fi
strategy="-s $3 -o depth=$d -o progress -o hints"

timefmt="%U user\n%S system\n%E elapsed\n%P CPU\n%Xkb text + %Dkb data -> %Kkb total + %Mkb max\n%I inputs + %O outputs\n%F major + %R minor pagefaults\n%W swaps"

echo "Running $base"

mkdir -p "$workdir"

TIME="$timefmt" /usr/bin/time ../lamaSMT/dist/build/lamasmt/lamasmt -i $1 $strategy --scenario="$workdir/$name.sss" --node-name=$2 --enum-impl=bits
