#!/bin/sh
# Times the self-hosted compiler (self/README.md) on a copy of its own sources at a given commit and on the
# sample programs under bench/*.sl. The sources are the self/*.sl files of that commit, materialized under
# the build directory with the lib/ files its header is generated from, so that later edits change the
# compiler but not its input; the commit has to be reachable (not in a shallow clone) and its sources written
# in the syntax the measured slc accepts.
# Usage: bench/bench.sh [-n runs] [-b build-dir] <commit> [slc-binary]   (defaults: 5 runs, _build/self, _build/self/slc)
set -u
cd "$(dirname "$0")/.."
RUNS=5
B=_build/self
while getopts n:b: opt; do case $opt in n) RUNS=$OPTARG;; b) B=$OPTARG;; *) exit 2;; esac; done
shift $((OPTIND - 1))
[ $# -ge 1 ] || { echo "usage: bench/bench.sh [-n runs] [-b build-dir] <commit> [slc-binary]"; exit 2; }
PINNED=$(git rev-parse --short --verify "$1^{commit}") || { echo "commit $1 is not reachable here (a shallow clone? git fetch --unshallow)"; exit 2; }
SLC=${2:-$B/slc}
P=_build/bench/$PINNED
[ -d "$P/self" ] || { mkdir -p "$P" && git archive "$PINNED" self lib | tar -x -C "$P"; } || exit 1
[ ! -f "$P/self/gen_header.py" ] || python3 "$P/self/gen_header.py" || exit 1
PIN=""
for f in self/base self/heap self/reader self/core self/eval self/elab lib/embed self/header self/emit self/interp self/main; do [ -f "$P/$f.sl" ] && PIN="$PIN $P/$f.sl"; done

# timed <file> <command...>: runs the command, writing "wall-seconds user-seconds max-rss-KB" to the file (GNU time
# takes -f; BSD time, as on macOS, takes -l and reports its maximum resident set in bytes).
timed() {
  t=$1; shift
  if /usr/bin/time -o /dev/null -f x true 2> /dev/null; then /usr/bin/time -f "%e %U %M" -o "$t" "$@"; return; fi
  /usr/bin/time -l -o "$t.raw" "$@"; code=$?
  awk '/ real /{w=$1; u=$3} /maximum resident/{m=$1/1024} END{print w, u, m}' "$t.raw" > "$t"; rm -f "$t.raw"
  return $code
}

# time_one <label> <files...>: RUNS runs, reporting the minimum and median wall time, the minimum user time
# and the maximum resident size, then the GC's own account of the run (minor words, major collections).
time_one() {
  label=$1; shift
  out=$(mktemp)
  i=0
  while [ $i -lt "$RUNS" ]; do
    timed "$out.t" "$SLC" "$@" > /dev/null 2> "$out.err" || { echo "$label: slc failed: $(head -c 200 "$out.err")"; rm -f "$out" "$out.t" "$out.err"; return; }
    cat "$out.t" >> "$out"
    i=$((i + 1))
  done
  gc=$(OCAMLRUNPARAM=v=0x400 "$SLC" "$@" 2>&1 >/dev/null | awk '/minor_words|major_collections|top_heap_words|promoted_words/ {printf "%s ", $0}')
  sort -n "$out" | awk -v l="$label" -v gc="$gc" '{ w[NR]=$1; if (NR==1 || $2<u) u=$2; if ($3>m) m=$3 } END { printf "%-28s wall min %6.2fs  median %6.2fs  user min %6.2fs  maxrss %6.0fMB   %s\n", l, w[1], w[int((NR+1)/2)], u, m/1024, gc }'
  rm -f "$out" "$out.t" "$out.err"
}

echo "== $SLC, $RUNS runs each"
time_one "slc on slc at $PINNED" $PIN
REF=_build/default/bin/main.exe
[ -x "$REF" ] && { r=$(mktemp); timed "$r" "$REF" $PIN --extract /dev/null > /dev/null 2>&1; awk -v c="$PINNED" '{ printf "reference on slc at %s wall  %ss (one run)\n", c, $1 }' "$r"; rm -f "$r"; }
for t in bench/*.sl; do
  [ -f "$t" ] || continue
  needs=""
  for n in $(sed -n "s/^; needs: //p" "$t"); do needs="$needs tests/$n.sl"; done
  time_one "$(basename "$t" .sl)" $needs "$t"
done
