#!/bin/sh
# Times the self-hosted compiler (self/README.md) on a pinned copy of its own sources and on the sample
# programs under bench/*.sl. The pinned sources are the self/*.sl files of the commit named by PINNED,
# materialized under the build directory so that later edits to self/ change the compiler but not its input.
# Usage: bench/bench.sh [-n runs] [-b build-dir] [slc-binary]   (defaults: 5 runs, _build/self, _build/self/slc)
set -u
cd "$(dirname "$0")/.."
PINNED=4fda15f
RUNS=5
B=_build/self
while getopts n:b: opt; do case $opt in n) RUNS=$OPTARG;; b) B=$OPTARG;; esac; done
shift $((OPTIND - 1))
SLC=${1:-$B/slc}
P=_build/bench/pinned
mkdir -p "$P"
for f in base heap reader core eval elab header emit main; do
  [ -s "$P/$f.sl" ] || git show "$PINNED:self/$f.sl" > "$P/$f.sl"
done
PIN="$P/base.sl $P/heap.sl $P/reader.sl $P/core.sl $P/eval.sl $P/elab.sl $P/header.sl $P/emit.sl $P/main.sl"

# time_one <label> <files...>: RUNS runs, reporting the minimum and median wall time, the minimum user time
# and the maximum resident size, then the GC's own account of the run (minor words, major collections).
time_one() {
  label=$1; shift
  out=$(mktemp)
  i=0
  while [ $i -lt "$RUNS" ]; do
    /usr/bin/time -f "%e %U %M" -o "$out.t" "$SLC" -- lib/prelude.sl "$@" > /dev/null 2> "$out.err" || { echo "$label: slc failed: $(head -c 200 "$out.err")"; rm -f "$out" "$out.t" "$out.err"; return; }
    cat "$out.t" >> "$out"
    i=$((i + 1))
  done
  gc=$(OCAMLRUNPARAM=v=0x400 "$SLC" -- lib/prelude.sl "$@" 2>&1 >/dev/null | awk '/minor_words|major_collections|top_heap_words|promoted_words/ {printf "%s ", $0}')
  sort -n "$out" | awk -v l="$label" -v gc="$gc" '{ w[NR]=$1; if (NR==1 || $2<u) u=$2; if ($3>m) m=$3 } END { printf "%-28s wall min %6.2fs  median %6.2fs  user min %6.2fs  maxrss %6.0fMB   %s\n", l, w[1], w[int((NR+1)/2)], u, m/1024, gc }'
  rm -f "$out" "$out.t" "$out.err"
}

echo "== $SLC, $RUNS runs each"
time_one "slc on pinned slc ($PINNED)" $PIN
REF=_build/default/bin/main.exe
[ -x "$REF" ] && { /usr/bin/time -f "reference on pinned slc      wall  %es (one run)" "$REF" $PIN --extract /dev/null > /dev/null; } 2>&1 | grep "^reference"
for t in bench/*.sl; do
  [ -f "$t" ] || continue
  needs=""
  for n in $(sed -n "s/^; needs: //p" "$t"); do needs="$needs tests/$n.sl"; done
  time_one "$(basename "$t" .sl)" $needs "$t"
done
