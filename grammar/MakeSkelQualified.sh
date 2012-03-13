#!/bin/bash

echo "Qualifying skeleton file"

#set -x
dirname="./Lang/LAMA"

cat "${dirname}/Skel.hs" \
    | perl -pe 's/((?<!(?:[".]))\b(?!(?:Show|Result|Bad|Err|String)\b)[A-Z][a-zA-Z0-9]*\b(?!\.))/Abs.\1/' \
    | sed 's/import Lang.LAMA.Abs/import qualified Lang.LAMA.Abs as Abs/' \
    > "${dirname}/Skel.hs.new"

mv "${dirname}/Skel.hs.new" "${dirname}/Skel.hs"
