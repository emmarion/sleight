#!/bin/sh
cd "$(dirname "$0")"
m=./.lake/build/bin/minimal
($m examples/*.sl
 $m --unchecked examples/*_bad.sl | sed 's/^/unchecked /'
 $m --stripped $(ls examples/*.sl | grep -v _bad) | sed 's/^/stripped /') > examples/expected.txt
