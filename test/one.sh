#!/bin/sh
set -u
cd "$(dirname "$0")/.."
[ $# -gt 0 ] || { echo "usage: test/one.sh tests/a.sl ..."; exit 2; }
for f in "$@"; do [ -f "$f" ] || { echo "no such test: $f"; exit 2; }; done
dune build test/runtest.exe @test/sources 2>&1 | head -5
(cd _build/default/test && ./runtest.exe "$@"); ref=$?
self/bootstrap.sh one "$@" && exit $ref
