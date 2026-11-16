#!/bin/sh
set -u
cd "$(dirname "$0")"
R=$(cd ../../.. && pwd)
REF=${REF:-$R/_build/default/bin/main.exe}
SLC=${SLC:-$R/_build/release/slc}
MINI="$R/mini/base.sl $R/mini/term.sl $R/mini/core.sl"
LIB="$R/std/list.sl $R/mini/base.sl"
HEAP="$LIB heap.sl code.sl big.sl small.sl"
failed=0

goal() {
  dir=$1
  shift
  for tool in "$REF" "$SLC"; do
    out=$(cd "$dir" && "$tool" "$@" --goal proved 2>&1 | tail -1)
    [ "$out" = "--goal proved: PASS" ] || failed=1
    echo "$dir ($(basename "$tool")): $out"
  done
}

accepted() {
  dir=$1
  shift
  if (cd "$dir" && "$REF" "$@" >/dev/null 2>&1); then
    echo "$dir: accepted: $*"
  else
    failed=1
    echo "$dir: REFUSED: $*"
  fi
}

last() {
  label=$1
  dir=$2
  shift 2
  echo "$label: $(cd "$dir" && "$@" 2>&1 | tail -1)"
}

whole() {
  label=$1
  dir=$2
  shift 2
  echo "$label: $(cd "$dir" && "$@" 2>&1 | sed 's/^.*runtime error: //' | tr '\n' '|')"
}

echo "== goals, each under the reference and under slc"
goal verdict spec.sl proof.sl qed.sl
goal verdict-machine spec.sl machine.sl qed.sl
goal three-iterations spec.sl machine.sl iterate.sl halting.sl goal.sl qed.sl
goal derivation-and-doubling $MINI "$R/mini/eval.sl" evalby_goal.sl evalby.sl evalby_qed.sl
goal derivation-and-doubling $MINI eval2.sl evaluniq.sl neg.sl eval3.sl fuelthm.sl sized.sl fuelgoal.sl fuelqed.sl
goal reader syntax.sl spec.sl read.sl proof.sl qed.sl
goal reader syntax.sl read.sl adequacy-spec.sl adequacy-proof.sl

echo "== step machine: files the reference accepts, and runs under both"
STEP="$MINI $R/mini/eval.sl"
accepted step-machine $STEP machine.sl graph.sl reach.sl traced.sl guided.sl evalby.sl runguided.sl depth.sl programs.sl drive.sl
accepted step-machine $STEP machine_tail.sl depth_tail.sl programs.sl drive.sl
accepted step-machine "$R/std/list.sl" heap/heap.sl heap/heapstep.sl
last "fuelled eval, double 1000, fuel 1000 (reference)" step-machine "$REF" $STEP machine.sl programs.sl drive.sl main.sl -- fuel double 1000 1000
for name in reference "slc --interpret"; do
  tool=$REF
  [ "$name" = reference ] || tool="$SLC --interpret"
  last "machine, double 1000 ($name)" step-machine $tool $STEP machine.sl programs.sl drive.sl main.sl -- step double 1000
  last "machine, the program of tests/mini_eval.sl ($name)" step-machine $tool $STEP machine.sl drive.sl test_a_program.sl
  last "store machine ($name)" step-machine $tool "$R/std/list.sl" heap/heap.sl heap/heapstep.sl heap/heapdrive.sl -- 5 1 1
done

echo "== heap machine: lemma files the reference accepts"
accepted heap-machine $HEAP det.sl
accepted heap-machine $HEAP keep.sl
accepted heap-machine $HEAP agree.sl
accepted heap-machine $HEAP keep.sl ren.sl ren-small.sl ren-grow.sl ren-online.sl
accepted heap-machine $HEAP det.sl ren.sl corollary.sl

echo "== suspendable elaborator: one result from every design"
for design in "r0.sl" "r-elab.sl r.sl" "r-elab.sl rc.sl" "ro.sl" "rq.sl" "m.sl" "mu.sl" "d.sl"; do
  last "$design (reference)" suspendable-elaborator "$REF" common.sl trees.sl $design
  last "$design (slc --interpret)" suspendable-elaborator "$SLC" --interpret common.sl trees.sl $design
done

echo "== order: programs whose output depends on the order of siblings"
for f in values-measure-first values-build-first cell-write-operand; do
  last "$f (reference)" order "$REF" $f.sl
  last "$f (slc --interpret)" order "$SLC" --interpret $f.sl
done

echo "== order: what is printed before a failure, with a small --eval-fuel"
for f in values-say-then-crash values-crash-then-say values-nested-argument cell-write-operand-crash; do
  whole "$f (reference)" order "$REF" --eval-fuel 50000 $f.sl
  whole "$f (slc --interpret)" order "$SLC" --interpret --eval-fuel 50000 $f.sl
done

echo "== gaps: acceptance that depends on more than the source"
for f in slot-eq-asserts-some slot-eq-asserts-none special-let-at-slot-0 special-match-at-slot-0 special-match-at-slot-26 gensym-expansion-order; do
  last "$f (reference)" gaps "$REF" $f.sl
  last "$f (reference --no-extern)" gaps "$REF" --no-extern $f.sl
  last "$f (slc --interpret)" gaps "$SLC" --interpret $f.sl
done

[ "$failed" = 0 ] && echo "all goals and lemma files passed" || echo "SOMETHING FAILED"
exit $failed
