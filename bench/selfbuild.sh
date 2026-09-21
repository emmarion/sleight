#!/bin/sh
# Builds slc from the current self/*.sl with an existing slc binary, for a quick edit-measure loop; the full
# check remains self/bootstrap.sh. Usage: bench/selfbuild.sh [in-slc] [out-binary]   (defaults: _build/self/slc, _build/self/slc_new)
set -eu
cd "$(dirname "$0")/.."
IN=${1:-_build/self/slc}
OUT=${2:-_build/self/slc_new}
SL="self/base.sl self/heap.sl self/reader.sl self/core.sl self/eval.sl self/elab.sl self/header.sl self/emit.sl self/interp.sl self/main.sl"
python3 self/gen_header.py
"$IN" -- lib/prelude.sl $SL > "$OUT.ml"
ocamlfind ocamlopt -package zarith,unix -linkpkg "$OUT.ml" -o "$OUT"
echo "built $OUT"
