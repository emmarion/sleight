#!/bin/sh
# usage: build_slc_cells.sh OUTDIR   (run from anywhere; needs _build/release/slc)
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
out=$1
mkdir -p "$out"
(cd "$root/tests" && ../_build/release/slc ../std/immediate.sl cell_imm.sl) > "$out/cell_imm.ml"
name() { grep -o "v[0-9]*_$1_a[0-9]*" "$out/cell_imm.ml" | head -1; }
sed '$d' "$out/cell_imm.ml" > "$out/cells.ml"
sed -e "s/SWAP_IN/$(name swap_in)/" -e "s/WRITE_IN/$(name write_in)/" -e "s/FRESH_IN/$(name fresh_in)/" "$here/slc_cells_driver.ml" >> "$out/cells.ml"
for v in n d; do
  flag=; [ $v = d ] && flag="-runtime-variant d"
  (cd "$out" && ocamlfind ocamlopt -package zarith,unix $flag -linkpkg cells.ml -o "cells_$v")
done
