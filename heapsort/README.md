# Heap sort: OCaml vs. verified Lean

Both programs heap sort the same 2^20 pseudo-random 63-bit integers five
times and print the time with the min, median and max.

- `heapsort.ml`: OCaml on `int array`.
- `HeapSort.lean`: generic in-place heap sort, with `heapSort_correct`
  (the output is a permutation of the input and sorted) for any total,
  transitive `le`.
- `Int63.lean`: `Int63` (OCaml's `int` range) and `Int63.heapSort_correct`.
- `Main.lean`: the Lean benchmark; it prints the axioms
  `Int63.heapSort_correct` depends on when built.

```
ocamlopt -inline 200 -o heapsort_ml heapsort.ml && ./heapsort_ml
ocamlopt -unsafe -inline 200 -o heapsort_ml_unsafe heapsort.ml && ./heapsort_ml_unsafe
lake build && .lake/build/bin/bench
```

`mimo/` holds an SL heap sort certified against
`agent/tasks/heapsort-fast/spec.sl`, written by the mimo-v2.6-pro agent
on the heapsort-fast task. `mimo/files.txt` lists its files in order. It
sorts a different input, `perf.sl`'s 2^20 pseudo-random integers below
2^30, once, and prints the time and what the sort allocates. From the
repository root:

```
dune exec bin/main.exe -- std/nat.sl std/list.sl agent/tasks/heapsort-fast/spec.sl \
  $(cat heapsort/mimo/files.txt) agent/tasks/heapsort-fast/accept.sl \
  agent/tasks/heapsort-fast/perf.sl --extract heapsort/mimo_perf.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg heapsort/mimo_perf.ml -o heapsort/mimo_perf && heapsort/mimo_perf
```
