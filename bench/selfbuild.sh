#!/bin/sh
# Builds slc from the current self/*.sl with an existing slc binary, for a quick edit-measure loop; the full
# check remains self/bootstrap.sh. Usage: bench/selfbuild.sh [in-slc] [out-binary]   (defaults: _build/self/slc, _build/self/slc_new)
set -eu
cd "$(dirname "$0")/.."
IN=${1:-_build/self/slc}
OUT=${2:-_build/self/slc_new}
SL="std/list.sl std/macro.sl self/base.sl self/escape.sl self/heap.sl self/reader.sl self/core.sl self/eval.sl self/elab.sl lib/embed.sl self/header.sl self/emit.sl self/elab-main.sl self/interp.sl self/main.sl"
"$IN" $SL --build "$OUT"
echo "built $OUT"
