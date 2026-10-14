#!/bin/sh
# Runs the Lean runner over the OCaml suite's tests and tallies how its verdicts compare.
cd "$(dirname "$0")"
m=./.lake/build/bin/minimal
for f in ../tests/*.sl; do
  grep -q '^; \(stdin\|args\|env\|externs\|confine\)' "$f" && continue
  needs=$(grep -m1 '^; needs: ' "$f" | cut -d' ' -f3- | sed 's|\([^ ]*\)|../tests/\1.sl|g')
  if grep -q '^; error:' "$f"; then want=refuse; else want=accept; fi
  flag=; grep -q '^; prelude: none' "$f" && flag=--no-prelude
  out=$(timeout 10 $m --shared $flag $needs "$f")
  [ $? = 124 ] && out="x: stuck: timeout"
  out=$(printf '%s\n' "$out" | head -1 | cut -d' ' -f2-)
  case "$out" in
    *"not supported"*|*"malformed"*|*"unbound name"*|*"is not a type or constructor"*) got=unsupported ;;
    "error:"*) got=refuse ;;
    "refused:"*) got=refuse ;;
    "stuck"*) got=stuck ;;
    *) got=accept
       exp=$(grep -m1 '^; expect: ' "$f" | cut -d' ' -f3-)
       [ -n "$exp" ] && [ "$exp" != "$out" ] && got=mismatch ;;
  esac
  printf "%s %s %s %s\n" "$want" "$got" "$(basename "$f")" "$out"
done
