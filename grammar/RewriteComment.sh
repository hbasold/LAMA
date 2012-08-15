#!/bin/bash

# Rewrite comments in the lexer file so that haddock
# is able to parse it and does not break while generating
# the documentation.

echo "Rewrite comment"

# set -x
dirname="./Lang/LAMA/Parser"

# Remove whitespaces in front of of haddock comments
cat "${dirname}/Lex.x" \
  | sed 's/\s\+-- |/-- |/' \
  > "${dirname}/Lex.x.new"
mv "${dirname}/Lex.x.new" "${dirname}/Lex.x"
