#!/bin/bash

echo "Renaming parser modules"

# set -x
srcdirname="./Lang/LAMA"
tgtdirname="./Lang/LAMA/Parser"
files=`find "$srcdirname/" -regex ".*\.\(hs\|x\|y\)" -printf "%f\n"`

mkdir -p $tgtdirname

for f in $files ; do
    cat "${srcdirname}/$f" | sed 's/Lang\.LAMA\./Lang\.LAMA\.Parser\./' \
        > "${tgtdirname}/${f}"
    rm "${srcdirname}/$f"
done

