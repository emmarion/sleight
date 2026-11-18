#!/bin/sh
# usage: arm64.sh OUTDIR CROSS_OCAML_PREFIX   (stress.ml with Ffi_core's three -imm operations inlined, no Zarith; runs under qemu-aarch64-static)
set -u
here=$(cd "$(dirname "$0")" && pwd)
out=$1 tc=$2
mkdir -p "$out" && cd "$out" || exit 1
cp "$here"/neg_young.ml "$here"/helpers_*.ml .
sed -e '/^module F = Sleight.Ffi_core$/{r '"$here"'/noz_ops.ml' -e 'd;}' -e 's/(Z\.of_int \([a-z_0-9]*\))/\1/g' "$here/stress.ml" > stress_noz.ml
O="$tc/bin/ocamlopt" T="-I +unix -I +threads unix.cmxa threads.cmxa"
for v in n d; do
  rv=; [ $v = d ] && rv="-runtime-variant d"
  $O $rv stress_noz.ml -o stress_noz_$v
  $O $rv $T helpers_thr.ml stress_noz.ml -o stress_noz_thr_$v
  $O $rv helpers_dom.ml stress_noz.ml -o stress_noz_dom_$v
  $O $rv neg_young.ml -o neg_young_$v
done 2> build.log
run() {
  bin=$1 rp=$2; shift 2
  res=$(OCAMLRUNPARAM=$rp qemu-aarch64-static -L /usr/aarch64-linux-gnu ./$bin "$@" 2> err.txt); code=$?
  echo "$bin $* [$rp] exit=$code heap-checks=$(grep -c 'Heap verified' err.txt) :: $res $(grep -i 'assert\|fatal\|error' err.txt | head -n 1)"
}
for rp in "" s=4k s=4k,o=1; do run stress_noz_n "$rp"; run stress_noz_d "$rp,V=1,v=0x800"; done
for b in stress_noz_thr stress_noz_dom; do run ${b}_n ""; run ${b}_n s=4k; run ${b}_d s=4k,V=1,v=0x800; done
for v in n d; do run neg_young_$v ""; run neg_young_$v "" barrier; done
