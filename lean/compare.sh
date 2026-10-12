#!/bin/sh
# Runs the Lean runner over the OCaml suite's tests and tallies how its verdicts compare.
cd "$(dirname "$0")"
m=./.lake/build/bin/minimal
for f in ../tests/*.sl; do
  grep -q '^; \(needs\|stdin\|args\|env\|externs\|confine\)' "$f" && continue
  if grep -q '^; error:' "$f"; then want=refuse; else want=accept; fi
  flag=; grep -q '^; prelude: none' "$f" && flag=--no-prelude
  out=$($m $flag "$f" | cut -d' ' -f2-)
  case "$out" in
    *"not supported"*|*"malformed"*|*"unbound name"*|*"is not a type or constructor"*) got=unsupported ;;
    "error:"*) got=refuse ;;
    "refused:"*) got=refuse ;;
    "stuck"*) got=stuck ;;
    *) got=accept ;;
  esac
  echo "$want $got $(basename "$f") $out"
done
