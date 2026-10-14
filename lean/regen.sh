#!/bin/sh
cd "$(dirname "$0")"
m=./.lake/build/bin/minimal
($m examples/*.sl
 $m --unchecked examples/*_bad.sl | sed 's/^/unchecked /'
 $m --full $(ls examples/*.sl | grep -v '_bad\|_big') | sed 's/^/full /') > examples/expected.txt
