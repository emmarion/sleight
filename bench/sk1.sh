#!/bin/sh
# Times the Skelet #1 job (bb/sk1.sl's main-run) alone: elaborates just the files it needs plus a native-compute of
# main-run, captures the generated OCaml, and reruns the compiled job. Results go to _build/sk1/results.tsv.
# Usage: bench/sk1.sh [-n runs] [-m main.ml] [-p] [-f] [-s slc] [label]
#   -m  skip elaboration and time a given (perhaps hand-edited) main.ml   -p  also profile a prefix run under callgrind
#   -f  also run the full BB(5) check of bb/README.md
set -u
cd "$(dirname "$0")/.."
RUNS=2 ML= PROF= FULL= SLC=_build/release/slc PFUEL=${PFUEL:-10000000}
while getopts n:m:pfs: opt; do case $opt in n) RUNS=$OPTARG;; m) ML=$(realpath "$OPTARG");; p) PROF=1;; f) FULL=1;; s) SLC=$OPTARG;; *) exit 2;; esac; done
shift $((OPTIND - 1))
LABEL=${1:-}
B=$(pwd)/_build/sk1
mkdir -p "$B/wrap"
DEPS="std/list.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/search.sl bb/far.sl std/macro.sl bb/pat.sl bb/skelet.sl bb/sk1.sl"
REV=$(git rev-parse --short HEAD)$(git diff --quiet HEAD -- bb || echo "+$(git diff HEAD -- bb | sha1sum | cut -c1-7)")
ELAB=-
if [ -z "$ML" ]; then
  awk '/^\(def-fns _ \$ \(many main-run :/{p=1} p&&/^$/{exit} p' bb/sk1.sl | sed "s/main-run/main-run-prof/; s/200000000/$PFUEL/" > "$B/prof.sl"
  grep -q "$PFUEL" "$B/prof.sl" || { echo "could not derive a prefix run from main-run"; exit 1; }
  printf '(let ((many res) (many pres)) (native-compute main-run main-run-prof))\n(comptime-match many res (ROk _ _))\n' >> "$B/prof.sl"
  printf '#!/bin/sh\n/usr/bin/ocamlfind "$@"; rc=$?\n[ -f main.ml ] && cp main.ml "%s/main.ml"\nexit $rc\n' "$B" > "$B/wrap/ocamlfind"
  chmod +x "$B/wrap/ocamlfind"
  rm -f "$B/main.ml"
  T0=$(date +%s.%N)
  PATH="$B/wrap:$PATH" "$SLC" $DEPS "$B/prof.sl" --inline 25 > /dev/null 2> "$B/elab.err" || { tail -20 "$B/elab.err"; echo "FAIL: elaboration or job"; exit 1; }
  ELAB=$(echo "$(date +%s.%N) - $T0" | bc | xargs printf '%.1f')
  ML=$B/main.ml
fi
W=$B/ml; rm -rf "$W"; mkdir -p "$W"; cp "$ML" "$W/main.ml"
(cd "$W" && ocamlfind ocamlopt -inline 25 -package zarith,unix -linkpkg main.ml -o main 2> compile.err) || { tail "$W/compile.err"; exit 1; }
BEST=
for i in $(seq "$RUNS"); do
  OCAMLRUNPARAM=v=0x400 /usr/bin/time -f "%U %M" "$W/main" 0 > "$W/out" 2> "$W/stats" || { echo "FAIL: job crashed"; exit 1; }
  [ "$(cat "$W/out")" = 0 ] || { echo "FAIL: job returned RFail"; exit 1; }
  U=$(tail -1 "$W/stats" | cut -d' ' -f1); MEM=$(tail -1 "$W/stats" | cut -d' ' -f2)
  [ -z "$BEST" ] || [ "$(echo "$U < $BEST" | bc)" = 1 ] && BEST=$U
done
MW=$(awk '/minor_words/{printf "%.0fM", $2/1e6}' "$W/stats")
MAJ=$(awk '/major_words/{printf "%.0fM", $2/1e6}' "$W/stats")
TOP=-
if [ -n "$PROF" ]; then
  (cd "$W" && valgrind --tool=callgrind --callgrind-out-file=cg.out ./main 1 > /dev/null 2> cg.err)
  for k in incl self; do
    callgrind_annotate $([ $k = incl ] && echo --inclusive=yes) "$W/cg.out" 2> /dev/null | sed -n '/PROGRAM TOTALS/,$p' | grep -v '([0-9]\{4,\}\.\|(\(10[1-9]\|1[1-9][0-9]\|[2-9][0-9][0-9]\)\.\|below main\|caml_start\|caml_main\|caml_program\|Main__entry\|ld-linux\|libc_start\|???:main' | head -40 |
      sed "s/???:camlMain__v[0-9]*_\(.*\)_a[0-9]*_[0-9]*[^ ]* \[.*/\1/; s/ \[[^]]*main\]$//" > "$B/prof-$k.txt"
  done
  TOP=$(awk '/PROGRAM TOTALS/{gsub(",","",$1); printf "%.0fM", $1/1e6}' "$B/prof-self.txt")
fi
FULLT=-
if [ -n "$FULL" ]; then
  T0=$(date +%s.%N)
  "$SLC" std/nat.sl std/list.sl std/macro.sl std/tactics.sl agent/tasks/bb5/defs.sl agent/tasks/bb5/spec.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl bb/skelet.sl bb/sk17.sl bb/sk1.sl bb/holes.sl bb/par.sl bb/bb5.sl bb/spec.sl bb/spec5.sl --goal proved --inline 25 > "$B/full.out" 2> "$B/full.err"
  FULLT=$(echo "$(date +%s.%N) - $T0" | bc | xargs printf '%.1f')$(grep -q "proved: PASS" "$B/full.out" && echo "" || echo "FAIL")
fi
[ -f "$B/results.tsv" ] || printf 'date\trev\tlabel\telab+job_s\tjob_user_s\tminor_words\tmajor_words\tmaxrss_kb\tprefix_instr\tfull_s\n' > "$B/results.tsv"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date +%m-%d_%H:%M)" "$REV" "${LABEL:--}" "$ELAB" "$BEST" "$MW" "$MAJ" "$MEM" "$TOP" "$FULLT" >> "$B/results.tsv"
awk -F'\t' 'NR==FNR{for(i=1;i<=NF;i++)if(length($i)>w[i])w[i]=length($i);next}FNR==1||FNR>n-11{for(i=1;i<=NF;i++)printf "%-*s  ",w[i],$i;print ""}' n="$(wc -l < "$B/results.tsv")" "$B/results.tsv" "$B/results.tsv"
