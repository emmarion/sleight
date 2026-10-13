# Heap sort with flat invariants

A heap sort certified against `agent/tasks/heapsort-fast/spec.sl`, with the
proof structure of `heapsort/ats/heapsort_cert.dats`. `files.txt` lists its
files in order. From the repository root:

```
T=agent/tasks/heapsort-fast
dune exec bin/main.exe -- --warnings-as-errors std/nat.sl std/list.sl std/macro.sl std/tactics.sl $T/spec.sl \
  $(cat heapsort/flat/files.txt) $T/accept.sl $T/perf.sl --extract flat_perf.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg flat_perf.ml -o flat_perf && ./flat_perf
```

- `arith.sl`: order (`lt-lemma` from `std/tactics.sl`, and `Ne` from `std/nat.sl`), `Child` (the children of p are 2p+1 and 2p+2), halving
  through `u62-shr`, and the decreasing measure of the sift loop.
- `lists.sl`: `Swap`, reading an element back through a swap, and a swap as
  a `Permutation`.
- `glue.sl`: the `Nat` contents tied to the `Copy (U62)` array the sort
  writes with `-imm` operations, the coercions at either end, and the runtime
  `get` and `swap`.
- `inv.sl`: the "for all positions" invariants `HeapExc`, `Grand`, `Suffix`,
  `Stays`, `CMax` and `Max`. Each is an erased function at the one level
  `Inv`, packed with a `Ver` value as its first, `subterm`, parameter; an
  invariant built from others has a version containing theirs, so it may call
  them, and the loops, whose levels come later, may call any of them.
  Lemmas these functions call precede `(def-lvl Inv)`.
- `loops.sl`: `sift` and `sift-to`, `heapify` and `sortdown`.
- `sort.sl`: `heapsort-fast`, which `accept.sl` calls.
