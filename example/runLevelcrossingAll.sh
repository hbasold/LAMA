#!/bin/bash

for f in `find Levelcrossing/ -name "Levelcrossing_*.scade" -not -name "*old*"`;
do
  ./runLevelcrossing.sh $f;
done
