#!/bin/sh
set -eu
cd "$(dirname "$0")"
B=$PWD/_build
T=agent/tasks/heapsort-fast
OC="ocamlfind ocamlopt -package zarith,unix -linkpkg"
mkdir -p "$B"
sh ../ats/build.sh
(cd ../.. && sh self/release.sh >/dev/null &&
  for d in opus mimo flat; do
    std="std/nat.sl std/list.sl"; [ $d = flat ] && std="$std std/macro.sl std/tactics.sl"
    _build/release/slc --no-shape-note $std $T/spec.sl $(cat heapsort/$d/files.txt) $T/accept.sl $T/perf.sl > "$B/sl_$d.ml"
  done)
{ sed -n '/^let sift/,/^  done$/p' ../heapsort.ml; cat ml_main.ml; } > "$B/ml.ml"
oc() { (cd "$B" && $OC "$@"); }
builds() {
  s=$1; shift
  for d in opus mimo flat; do oc "$@" sl_$d.ml -o sl_$d$s; done
  oc "$@" -inline 200 ml.ml -o ml_safe$s && oc "$@" -unsafe -inline 200 ml.ml -o ml_unsafe$s
}
builds ""
if [ -n "${FL_SWITCH:-}" ]; then OC="opam exec --switch=$FL_SWITCH -- $OC"; builds _fl -O3; fi
(cd lean && lake build)
idris2 Hs.idr --build-dir "$B/idris" -o hs
