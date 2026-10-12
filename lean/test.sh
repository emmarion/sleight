#!/bin/sh
set -e
cd "$(dirname "$0")"
lake build
lake build minimal
(./.lake/build/bin/minimal examples/*.sl; ./.lake/build/bin/minimal --unchecked examples/*_bad.sl | sed 's/^/unchecked /') |
  diff examples/expected.txt -
lake env lean Axioms.lean
