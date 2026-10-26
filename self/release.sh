#!/bin/sh
# Builds a release slc: bootstrap.sh's steps 1 and 3 without its checks (no test suite, no fixpoint comparison).
# The reference extracts a stage-one slc, which compiles self/*.sl; that output is compiled without -g, with -O3
# when the compiler has flambda, and stripped. ocamlopt appears to record call-site locations for backtraces even
# without -g, so the last step compiles from inside the work directory to keep the build path out of them.
# Usage: self/release.sh [out-binary]   (default _build/release/slc)
set -eu
cd "$(dirname "$0")/.."
OUT=${1:-_build/release/slc}
mkdir -p "$(dirname "$OUT")"
OUT=$(cd "$(dirname "$OUT")" && pwd)/$(basename "$OUT")
B=$(dirname "$OUT")/release-work
mkdir -p "$B"
SL="std/macro.sl self/base.sl self/heap.sl self/reader.sl self/core.sl self/eval.sl self/elab.sl lib/embed.sl self/header.sl self/emit.sl self/interp.sl self/main.sl"
OC="ocamlfind ocamlopt -package zarith,unix -linkpkg"
REL=
ocamlfind ocamlopt -config | grep -q '^flambda: true' && REL=-O3
dune build bin/main.exe
rm -rf "$B/stage1.build"
_build/default/bin/main.exe $SL --build "$B/stage1"
"$B/stage1" $SL > "$B/slc.ml"
(cd "$B" && $OC $REL slc.ml -o "$OUT.tmp")
strip "$OUT.tmp"
mv -f "$OUT.tmp" "$OUT"
echo "built $OUT"
