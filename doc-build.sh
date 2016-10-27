#!/bin/bash

workdir=$(dirname "$1")
fname=$(basename "$1")

cd $workdir
coqdoc -html --no-index $fname
cd ..

