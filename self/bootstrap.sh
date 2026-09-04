#!/bin/sh
# Bootstraps the self-hosted compiler (self/README.md) and checks it against the reference interpreter:
#   1. builds the reference and extracts slc (self/*.sl) to a native binary with the reference extractor;
#   2. compiles every tests/*.sl that runs (no "; error:" directive) with slc, builds the OCaml, runs it
#      with the test's stdin and arguments, and compares stdout, stderr and exit code with the reference
#      interpreter run on the same files;
#   3. compiles slc with slc, then again with the result, and requires the two outputs to be identical.
# Usage: self/bootstrap.sh [build-dir]   (default _build/self)
set -u
cd "$(dirname "$0")/.."
B=${1:-_build/self}
mkdir -p "$B"
SL="self/base.sl self/reader.sl self/core.sl self/eval.sl self/elab.sl self/header.sl self/emit.sl self/main.sl"
REF=_build/default/bin/main.exe
OC="ocamlfind ocamlopt -package zarith -linkpkg"

dune build 2>&1 | head -5
python3 self/gen_header.py
echo "== extracting slc with the reference extractor"
$REF $SL --extract "$B/slc.ml" || exit 1
$OC "$B/slc.ml" -o "$B/slc" > "$B/slc.log" 2>&1 || { cat "$B/slc.log"; exit 1; }

directive() { sed -n "s/^; $2: //p" "$1"; }

pass=0; fail=0; skipped=0
echo "== compiling the tests with slc"
for t in tests/*.sl; do
  name=$(basename "$t" .sl)
  if [ -n "$(directive "$t" error)" ]; then skipped=$((skipped+1)); continue; fi
  needs=""
  for n in $(directive "$t" needs); do needs="$needs tests/$n.sl"; done
  args=$(directive "$t" args)
  directive "$t" stdin > "$B/$name.in"
  # the reference run, files sharing one scope in order
  $REF $needs "$t" -- $args < "$B/$name.in" > "$B/$name.ref.out" 2> "$B/$name.ref.err"; refcode=$?
  if ! "$B/slc" -- lib/prelude.sl $needs "$t" > "$B/$name.ml" 2> "$B/$name.slc.err"; then
    echo "FAIL $name: slc: $(head -3 "$B/$name.slc.err")"; fail=$((fail+1)); continue
  fi
  if ! $OC "$B/$name.ml" -o "$B/$name.exe" > "$B/$name.log" 2>&1; then
    echo "FAIL $name: the emitted OCaml does not compile, see $B/$name.log"; fail=$((fail+1)); continue
  fi
  "$B/$name.exe" -- $args < "$B/$name.in" > "$B/$name.out" 2> "$B/$name.err"; code=$?
  if cmp -s "$B/$name.out" "$B/$name.ref.out" && cmp -s "$B/$name.err" "$B/$name.ref.err" && [ "$code" = "$refcode" ]; then
    pass=$((pass+1))
  else
    echo "FAIL $name: output differs (exit $code vs $refcode), see $B/$name.out and $B/$name.ref.out"; fail=$((fail+1))
  fi
done
echo "$pass passed, $fail failed, $skipped skipped (tests expecting an error)"

echo "== compiling slc with slc"
"$B/slc" -- lib/prelude.sl $SL > "$B/slc2.ml" 2> "$B/slc2.err" || { head -5 "$B/slc2.err"; exit 1; }
$OC "$B/slc2.ml" -o "$B/slc2" > "$B/slc2.log" 2>&1 || { cat "$B/slc2.log"; exit 1; }
echo "== compiling slc with the slc that slc compiled"
"$B/slc2" -- lib/prelude.sl $SL > "$B/slc3.ml" 2> "$B/slc3.err" || { head -5 "$B/slc3.err"; exit 1; }
if cmp -s "$B/slc2.ml" "$B/slc3.ml"; then echo "fixpoint reached: slc2.ml and slc3.ml are identical"; else echo "FAIL: slc2.ml and slc3.ml differ"; fail=$((fail+1)); fi
[ "$fail" = 0 ]
