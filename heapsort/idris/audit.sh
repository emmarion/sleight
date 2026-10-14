#!/bin/sh
cd "$(dirname "$0")"
hatch='believe_me|assert_|idris_crash|unsafe|prim__|%[a-zA-Z]+|\?[A-Za-z_]|partial|covering|MkArr|MkDone'
echo "== escape hatches and directives in Arr.idr (the trusted base)"
grep -nE "$hatch" Arr.idr
echo "== escape hatches and directives in HeapSort.idr (expect only %default total and %inline)"
grep -nE "$hatch" HeapSort.idr | grep -vE '^[0-9]+:(%default total|%inline)$' || echo "(none)"
echo "== library modules imported"
mods=$(grep -h '^import' Arr.idr HeapSort.idr | awk '{print $NF}' | sort -u)
echo $mods
if [ -n "${IDRIS2_SRC:-}" ]; then
  echo "== escape hatches in those modules' sources under $IDRIS2_SRC"
  for m in $mods; do
    f=$(ls "$IDRIS2_SRC"/*/"$(echo "$m" | tr . /)".idr 2>/dev/null | head -1)
    [ -n "$f" ] && grep -nHE 'believe_me|assert_|idris_crash|unsafe' "$f" | grep -v '|||'
  done
fi
tmp=$(mktemp -d)
echo "== type-check"
idris2 --check HeapSort.idr --build-dir "$tmp" | grep -v '^[0-9]*/[0-9]*: Building' || echo ok
idris2 Main.idr --build-dir "$tmp" -o cert >/dev/null
ss=$tmp/exec/cert_app/cert.ss
echo "== HeapSort and Arr definitions in the compiled Scheme"
grep -oE '\(define (HeapSort|Arr)-[^ ]+' "$ss" | sed 's/(define //' | tr '\n' ' '; echo
echo "== erased (quantity 0) definitions present in the compiled Scheme (expect none)"
for f in $(grep -hoE '^0 [a-zA-Z]+' Arr.idr HeapSort.idr | awk '{print $2}'); do
  grep -qE "(HeapSort|Arr)-$f[ )]" "$ss" && echo "$f"
done
echo "== HeapSort definitions that build closures or pass erased placeholders (expect none)"
grep -E '^\(define HeapSort-' "$ss" | grep -E "'erased|lambda.*lambda" | grep -oE '^\(define [^ ]+' || echo "(none)"
rm -rf "$tmp"
