#!/bin/sh
# Bootstraps the self-hosted compiler (self/README.md) and checks it against the reference interpreter:
#   1. builds the reference and extracts slc (self/*.sl) to a native binary with the reference extractor;
#   2. compiles every tests/*.sl with slc, in parallel: a test with an "; error:" directive must be refused
#      with a message mentioning that text; any other is built (to bytecode, the faster compile) and run with
#      the test's stdin and arguments, and its stdout, stderr and exit code compared with the reference
#      interpreter's on the same files; the extern, thunk, main, char and nat tests are compiled again with
#      --no-templates (ASSUMPTIONS 133); and every test is run again under slc --interpret, which performs
#      the program in place of writing it out, and compared the same way; a refused test is also run through
#      the reference, and where each side puts its first message is compared and counted (ASSUMPTIONS 194);
#   3. compiles slc with slc, then again with the result, and requires the two outputs to be identical.
# Usage: self/bootstrap.sh [build-dir]   (default _build/self)
#        self/bootstrap.sh one tests/a.sl ...   step 2 for those tests alone, into _build/self, rebuilding slc only
#        when self/*.sl or the reference binary changed; test/one.sh also runs them through test/runtest.ml
set -u
cd "$(dirname "$0")/.."
ROOT=$(pwd)
if [ "${1:-}" = check ]; then B=$BOOTSTRAP_B; else B=${1:-_build/self}; [ "$B" = one ] && B=_build/self; mkdir -p "$B"; B=$(cd "$B" && pwd); fi
SL="self/base.sl self/heap.sl self/reader.sl self/core.sl self/eval.sl self/elab.sl self/header.sl self/emit.sl self/interp.sl self/main.sl"
REF=_build/default/bin/main.exe
OC="ocamlfind ocamlopt -package zarith,unix -linkpkg"
OCB="ocamlfind ocamlc -custom -package zarith,unix -linkpkg"

directive() { sed -n "s/^; $2: //p" "$1"; }
# has <file> <directive text>: the text is on a line of the file, "<**>" in it matching any run of characters.
has() { grep -q -- "$(printf '%s' "$2" | sed 's/[][\\.*^$]/\\&/g; s/<\\\*\\\*>/.*/g')" "$1"; }

# check_warns <file> <name>: every "; warns:" line must appear in slc's own stderr, where it writes a warning,
# the reference writing one as it elaborates or as it checks a file's indentation. A "; warns:" line names the
# test by its path from the repository root, which is a suffix of the path slc is handed here, so the match is
# on a substring; the filters above drop a warning, and the note that may follow it, from a stderr being
# compared.
check_warns() {
  directive "$1" warns | while IFS= read -r want; do
    has "$B/$2.slc.err" "$want" || { echo "FAIL $2: expected a warning mentioning: $want; got: $(head -c 300 "$B/$2.slc.err" | tr '\n' ' ')"; exit 1; }
  done
}

# check_test <file> <slc flags or -> <tag or ->: compiles one test with slc and compares it with the reference,
# printing one line: "ok name", "refused name" or "FAIL name: why".
check_test() {
  t=$1; flags=$2; tag=$3
  [ "$flags" = - ] && flags=""
  [ "$tag" = - ] && tag=""
  name=$(basename "$t" .sl)$tag
  needs=""
  for n in $(directive "$t" needs); do needs="$needs tests/$n.sl"; done
  # a "; prelude: none" test runs, on both sides, without the prelude
  noprelude=""
  [ "$(directive "$t" prelude)" = none ] && noprelude=--no-prelude
  if [ -n "$(directive "$t" error)" ]; then
    # a test expecting an error: slc must refuse the program with a message mentioning the text
    if "$B/slc" $noprelude $flags $needs "$t" > "$B/$name.ml" 2> "$B/$name.slc.err"; then
      echo "FAIL $name: slc accepted a program the checker refuses"; return
    fi
    directive "$t" error | while IFS= read -r want; do has "$B/$name.slc.err" "$want" || { echo "FAIL $name: expected an error mentioning: $want; got: $(head -c 300 "$B/$name.slc.err" | tr '\n' ' ')"; exit 1; }; done &&
      check_warns "$t" "$name" || return
    # Where each side puts its first message. The directives match on the text alone, so nothing else
    # compares the two positions; slc records one per form it descends into and the reference carries one
    # per form, so the file and line agree far more often than the column (ASSUMPTIONS 194).
    "$ROOT/$REF" $noprelude $(for f in $needs "$t"; do echo "$ROOT/$f"; done) > /dev/null 2> "$B/$name.ref.err"
    first() { grep -m1 ' error: ' "$1" | sed "s|^$ROOT/||"; }
    refpos=$(first "$B/$name.ref.err"); slcpos=$(first "$B/$name.slc.err")
    if [ "$(echo "$refpos" | cut -d: -f1-3)" = "$(echo "$slcpos" | cut -d: -f1-3)" ]; then echo "pos-same $name"
    elif [ "$(echo "$refpos" | cut -d: -f1-2)" = "$(echo "$slcpos" | cut -d: -f1-2)" ]; then echo "pos-col $name: $refpos vs $slcpos"
    else echo "pos-line $name: $refpos vs $slcpos"; fi
    echo "refused $name"
    return
  fi
  args=$(directive "$t" args)
  envs=$(directive "$t" env)
  confine=""
  for d in $(directive "$t" confine-dir); do confine="--confine-dir $d"; done
  for b in $(directive "$t" confine-output-bytes); do confine="$confine --confine-output-bytes $b"; done
  [ -n "$(directive "$t" no-env)" ] && confine="$confine --no-env"
  directive "$t" stdin > "$B/$name.in"
  # the reference run, files sharing one scope in order; both runs happen inside $B, where a test may write files,
  # and in an environment holding the "; env:" variables alone, as test/runtest.ml runs a program
  (cd "$B" && env -i $envs "$ROOT/$REF" $noprelude $confine $(for f in $needs "$t"; do echo "$ROOT/$f"; done) -- $args < "$name.in" > "$name.ref.out" 2> "$name.ref.err"); refcode=$?
  if [ "$flags" = --interpret ]; then
    # slc elaborates and performs the program in one process, as the reference does, so its warnings land in
    # the same stderr and are filtered from both below
    (cd "$B" && env -i $envs "$B/slc" $noprelude $confine --interpret $(for f in $needs "$t"; do echo "$ROOT/$f"; done) -- $args < "$name.in" > "$name.out" 2> "$name.slc.err"); code=$?
    check_warns "$t" "$name" || return
    grep -vE ': warning: |: note: ' "$B/$name.slc.err" > "$B/$name.err" || true
  else
  if ! "$B/slc" $noprelude $confine $flags $needs "$t" > "$B/$name.ml" 2> "$B/$name.slc.err"; then
    echo "FAIL $name: slc: $(head -3 "$B/$name.slc.err")"; return
  fi
  if ! $OCB "$B/$name.ml" -o "$B/$name.exe" > "$B/$name.log" 2>&1; then
    echo "FAIL $name: the emitted OCaml does not compile, see $B/$name.log"; return
  fi
  check_warns "$t" "$name" || return
  (cd "$B" && env -i $envs "./$name.exe" $args < "$name.in" > "$name.out" 2> "$name.err"); code=$?
  fi
  # The reference elaborates and runs in one process, so a warning of its own lands in the stderr the program
  # then writes to; slc wrote its warnings at compile time, checked above. What is left is the program's.
  grep -vE ': warning: |: note: ' "$B/$name.ref.err" > "$B/$name.ref.err.run" || true
  if cmp -s "$B/$name.out" "$B/$name.ref.out" && cmp -s "$B/$name.err" "$B/$name.ref.err.run" && [ "$code" = "$refcode" ]; then
    echo "ok $name"
  else
    echo "FAIL $name: output differs (exit $code vs $refcode), see $B/$name.out and $B/$name.ref.out"
  fi
}
if [ "${1:-}" = check ]; then check_test "$2" "$3" "$4"; exit 0; fi

build_slc() {
  dune build 2>&1 | head -5
  python3 self/gen_header.py
  key=$(cat $SL $REF | md5sum)
  if [ "${1:-}" = cached ] && [ -x "$B/slc" ] && [ "$key" = "$(cat "$B/slc.key" 2>/dev/null)" ]; then return; fi
  echo "== extracting slc with the reference extractor"
  $REF $SL --extract "$B/slc.ml" || exit 1
  $OC "$B/slc.ml" -o "$B/slc" > "$B/slc.log" 2>&1 || { cat "$B/slc.log"; exit 1; }
  echo "$key" > "$B/slc.key"
}
check_all() {
  { for t in "$@"; do echo "$t - -"; done
    for t in "$@"; do case $(basename "$t") in extern_*|thunk_*|main_*|char*|nat_*) echo "$t --no-templates _view" ;; esac; done
    for t in "$@"; do echo "$t --interpret _interp"; done
  } | BOOTSTRAP_B=$B xargs -P "$(getconf _NPROCESSORS_ONLN)" -L 1 sh self/bootstrap.sh check > "$B/results.txt"
}
if [ "${1:-}" = one ]; then
  shift
  build_slc cached
  check_all "$@"
  cat "$B/results.txt"
  ! grep -q "^FAIL" "$B/results.txt"; exit
fi

build_slc
echo "== compiling the tests with slc, the extern, thunk, main, char and nat tests again with --no-templates, and every test again under --interpret"
check_all tests/*.sl
grep "^FAIL" "$B/results.txt"
fail=$(grep -c "^FAIL" "$B/results.txt")
echo "$(grep -c '^ok ' "$B/results.txt") programs matched the interpreter, $(grep -c '^refused ' "$B/results.txt") programs refused with the expected message, $fail failed"
grep "^pos-line " "$B/results.txt"
echo "$(grep -c '^pos-same ' "$B/results.txt") refusals agree on file, line and column, $(grep -c '^pos-col ' "$B/results.txt") on file and line alone ($B/results.txt lists them), $(grep -c '^pos-line ' "$B/results.txt") on neither"

echo "== compiling slc with slc"
# timed, and the time reported, so a change that slows slc down is seen: this is a report, not a check
# (GNU time takes -f; BSD time, as on macOS, takes -l and reports its maximum resident set in bytes)
if /usr/bin/time -o /dev/null -f x true 2> /dev/null; then
  /usr/bin/time -o "$B/slc2.time" -f "slc compiled itself in %e s (wall), %M KB max rss" "$B/slc" $SL > "$B/slc2.ml" 2> "$B/slc2.err" || { head -5 "$B/slc2.err"; exit 1; }
else
  /usr/bin/time -l -o "$B/slc2.time.raw" "$B/slc" $SL > "$B/slc2.ml" 2> "$B/slc2.err" || { head -5 "$B/slc2.err"; exit 1; }
  awk '/ real /{t=$1} /maximum resident/{m=$1/1024} END{printf "slc compiled itself in %s s (wall), %d KB max rss\n", t, m}' "$B/slc2.time.raw" > "$B/slc2.time"
fi
cat "$B/slc2.time"
$OC "$B/slc2.ml" -o "$B/slc2" > "$B/slc2.log" 2>&1 || { cat "$B/slc2.log"; exit 1; }
echo "== compiling slc with the slc that slc compiled"
"$B/slc2" $SL > "$B/slc3.ml" 2> "$B/slc3.err" || { head -5 "$B/slc3.err"; exit 1; }
if cmp -s "$B/slc2.ml" "$B/slc3.ml"; then echo "fixpoint reached: slc2.ml and slc3.ml are identical"; else echo "FAIL: slc2.ml and slc3.ml differ"; fail=$((fail+1)); fi
[ "$fail" = 0 ]
