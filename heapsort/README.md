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
