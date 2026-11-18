#!/bin/sh
# usage: toolchain.sh OUTDIR OCAML_PREFIX ZARITH_BUILD_DIR MAJOR(4|5) [ocamlopt flags]   (needs _build/release/slc)
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
out=$1 tc=$2 z=$3 major=$4
shift 4
mkdir -p "$out" && sh "$here/build_slc_cells.sh" "$out/slc" > /dev/null || exit 1
cd "$out" || exit 1
cp "$root/lib/ffi_core.ml" "$out/slc/cells.ml" "$here"/neg_young.ml "$here"/neg_mark.ml "$here"/helpers_*.ml .
sed 's/^module F = Sleight.Ffi_core$/module F = Ffi_core/' "$here/stress.ml" > stress.ml
O="$tc/bin/ocamlopt" Z="-I $z zarith.cmxa"
if [ "$major" = 5 ]; then U="-I +unix unix.cmxa"; else U=unix.cmxa; fi
T="-I +threads $U threads.cmxa"
for v in n d; do
  rv=; [ $v = d ] && rv="-runtime-variant d"
  $O "$@" $rv $Z ffi_core.ml stress.ml -o stress_$v
  $O "$@" $rv $Z $U cells.ml -o cells_$v
  $O "$@" $rv neg_young.ml -o neg_young_$v
  [ "$major" = 4 ] && $O "$@" $rv neg_mark.ml -o neg_mark_$v
  $O "$@" $rv $Z $T ffi_core.ml helpers_thr.ml stress.ml -o stress_thr_$v
  $O "$@" $rv $Z $T helpers_thr.ml cells.ml -o cells_thr_$v
  [ "$major" = 5 ] && $O "$@" $rv $Z ffi_core.ml helpers_dom.ml stress.ml -o stress_dom_$v
  [ "$major" = 5 ] && $O "$@" $rv $Z $U helpers_dom.ml cells.ml -o cells_dom_$v
done 2> build.log
run() {
  bin=$1 rp=$2; shift 2
  [ -x "$bin" ] || return 0
  res=$(OCAMLRUNPARAM=$rp ./$bin "$@" 2> err.txt); code=$?
  echo "$bin $* [$rp] exit=$code heap-checks=$(grep -c 'heap check\|Heap verified' err.txt) :: $res $(grep -i 'assert\|fatal\|error' err.txt | head -n 1)"
}
V=; [ "$major" = 5 ] && V=,V=1,v=0x800
for rp in "" s=4k s=4k,o=1; do run stress_n "$rp"; run stress_d "$rp$V"; done
for rp in "" s=4k s=4k,o=20; do run cells_n "$rp"; run cells_d "$rp$V"; done
for b in stress_thr cells_thr stress_dom cells_dom; do run ${b}_n ""; run ${b}_n s=4k; run ${b}_d "s=4k$V"; done
for v in n d; do run neg_young_$v ""; run neg_young_$v "" barrier; for m in nobarrier barrier imm; do run neg_mark_$v "" $m; done; done
