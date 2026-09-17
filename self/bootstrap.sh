#!/bin/sh
# Bootstraps the self-hosted compiler (self/README.md) and checks it against the reference interpreter:
#   1. builds the reference and extracts slc (self/*.sl) to a native binary with the reference extractor;
#   2. compiles every tests/*.sl with slc, in parallel: a test with an "; error:" directive must be refused
#      with a message mentioning that text; any other is built (to bytecode, the faster compile) and run with
#      the test's stdin and arguments, and its stdout, stderr and exit code compared with the reference
#      interpreter's on the same files; the extern, thunk, main, char and nat tests are compiled again with
#      --no-templates (ASSUMPTIONS 133);
#   3. compiles slc with slc, then again with the result, and requires the two outputs to be identical.
# Usage: self/bootstrap.sh [build-dir]   (default _build/self)
set -u
cd "$(dirname "$0")/.."
ROOT=$(pwd)
if [ "${1:-}" = check ]; then B=$BOOTSTRAP_B; else B=${1:-_build/self}; mkdir -p "$B"; B=$(cd "$B" && pwd); fi
SL="self/base.sl self/heap.sl self/reader.sl self/core.sl self/eval.sl self/elab.sl self/header.sl self/emit.sl self/main.sl"
REF=_build/default/bin/main.exe
OC="ocamlfind ocamlopt -package zarith,unix -linkpkg"
OCB="ocamlfind ocamlc -package zarith,unix -linkpkg"

directive() { sed -n "s/^; $2: //p" "$1"; }

# check_test <file> <slc flags or -> <tag or ->: compiles one test with slc and compares it with the reference,
# printing one line: "ok name", "refused name" or "FAIL name: why".
check_test() {
  t=$1; flags=$2; tag=$3
  [ "$flags" = - ] && flags=""
  [ "$tag" = - ] && tag=""
  name=$(basename "$t" .sl)$tag
  needs=""
  for n in $(directive "$t" needs); do needs="$needs tests/$n.sl"; done
  if [ -n "$(directive "$t" error)" ]; then
    # a test expecting an error: slc must refuse the program with a message mentioning the text
    if "$B/slc" -- $flags lib/prelude.sl $needs "$t" > "$B/$name.ml" 2> "$B/$name.slc.err"; then
      echo "FAIL $name: slc accepted a program the checker refuses"; return
    fi
    directive "$t" error | while IFS= read -r want; do grep -qF -- "$want" "$B/$name.slc.err" || { echo "FAIL $name: expected an error mentioning: $want; got: $(head -c 300 "$B/$name.slc.err" | tr '\n' ' ')"; exit 1; }; done && echo "refused $name"
    return
  fi
  args=$(directive "$t" args)
  directive "$t" stdin > "$B/$name.in"
  # the reference run, files sharing one scope in order; both runs happen inside $B, where a test may write files
  (cd "$B" && "$ROOT/$REF" $(for f in $needs "$t"; do echo "$ROOT/$f"; done) -- $args < "$name.in" > "$name.ref.out" 2> "$name.ref.err"); refcode=$?
  if ! "$B/slc" -- $flags lib/prelude.sl $needs "$t" > "$B/$name.ml" 2> "$B/$name.slc.err"; then
    echo "FAIL $name: slc: $(head -3 "$B/$name.slc.err")"; return
  fi
  if ! $OCB "$B/$name.ml" -o "$B/$name.exe" > "$B/$name.log" 2>&1; then
    echo "FAIL $name: the emitted OCaml does not compile, see $B/$name.log"; return
  fi
  (cd "$B" && "./$name.exe" -- $args < "$name.in" > "$name.out" 2> "$name.err"); code=$?
  if cmp -s "$B/$name.out" "$B/$name.ref.out" && cmp -s "$B/$name.err" "$B/$name.ref.err" && [ "$code" = "$refcode" ]; then
    echo "ok $name"
  else
    echo "FAIL $name: output differs (exit $code vs $refcode), see $B/$name.out and $B/$name.ref.out"
  fi
}
if [ "${1:-}" = check ]; then check_test "$2" "$3" "$4"; exit 0; fi

dune build 2>&1 | head -5
python3 self/gen_header.py
echo "== extracting slc with the reference extractor"
$REF $SL --extract "$B/slc.ml" || exit 1
$OC "$B/slc.ml" -o "$B/slc" > "$B/slc.log" 2>&1 || { cat "$B/slc.log"; exit 1; }

echo "== compiling the tests with slc, and the extern, thunk, main, char and nat tests again with --no-templates"
{ for t in tests/*.sl; do echo "$t - -"; done
  for t in tests/extern_*.sl tests/thunk_*.sl tests/main_*.sl tests/char*.sl tests/nat_*.sl; do echo "$t --no-templates _view"; done
} | BOOTSTRAP_B=$B xargs -P "$(nproc)" -L 1 sh self/bootstrap.sh check > "$B/results.txt"
grep "^FAIL" "$B/results.txt"
fail=$(grep -c "^FAIL" "$B/results.txt")
echo "$(grep -c '^ok ' "$B/results.txt") programs matched the interpreter, $(grep -c '^refused ' "$B/results.txt") programs refused with the expected message, $fail failed"

echo "== compiling slc with slc"
"$B/slc" -- lib/prelude.sl $SL > "$B/slc2.ml" 2> "$B/slc2.err" || { head -5 "$B/slc2.err"; exit 1; }
$OC "$B/slc2.ml" -o "$B/slc2" > "$B/slc2.log" 2>&1 || { cat "$B/slc2.log"; exit 1; }
echo "== compiling slc with the slc that slc compiled"
"$B/slc2" -- lib/prelude.sl $SL > "$B/slc3.ml" 2> "$B/slc3.err" || { head -5 "$B/slc3.err"; exit 1; }
if cmp -s "$B/slc2.ml" "$B/slc3.ml"; then echo "fixpoint reached: slc2.ml and slc3.ml are identical"; else echo "FAIL: slc2.ml and slc3.ml differ"; fail=$((fail+1)); fi
[ "$fail" = 0 ]
