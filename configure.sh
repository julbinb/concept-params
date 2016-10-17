#!/bin/bash

echo "building coq makefile..."

coq_makefile -f _CoqProject -o Makefile

echo "done"

