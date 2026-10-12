#!/bin/sh
set -e
cd "$(dirname "$0")"
lake build
lake build minimal
m=./.lake/build/bin/minimal
($m examples/*.sl
 $m --unchecked examples/*_bad.sl | sed 's/^/unchecked /'
 $m --stripped $(ls examples/*.sl | grep -v _bad) | sed 's/^/stripped /') |
  diff examples/expected.txt -
lake env lean Axioms.lean
