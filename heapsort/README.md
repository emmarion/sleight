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

`opus/` holds another, written by the claude-opus-5-5 agent in the first
session of run `20261012-1220-claude-opus-5-5-heapsort-fast`; of the runs in
`agent-runs-e194350.csv`, it is the smallest solution by non-whitespace
characters outside comments. It runs as `mimo/` does, with `opus` for `mimo`.

`agent-runs-e194350.csv` lists the heapsort-fast agent runs made on commit
e194350, one row per run: the first session whose `work/` passed (it
compiles in the prescribed order with no warnings and no `;! suppress`, and
`perf.sl` reaches the expected checksum allocating nothing), and the
context used and dollars spent at that session's first such `perf.sl` run.
A Claude session derived it by re-checking each session with slc built at
that commit and reading the erased OCaml of each first pass to judge that it
is a heap sort; that judgment and the `notes` column are its reading and may
be wrong. Dollars are the provider's reported cost for Neuralwatt models and
`agent/pi.py`'s list-price estimate otherwise.

`ats/` holds an in-place heap sort in ATS2 (ATS/Postiats 0.4.2,
`apt-get install ats2-lang`) whose type states that the output is a
permutation of the input and sorted, as checked by `patsopt`:

- `heapsort_cert.dats`: the sort. The array is the dataview `arr_v(l, xs)`,
  indexed by the static list `xs` of its contents. `PERM` (a sequence of
  `SWAP`s of two positions, via `ilist_prf.sats`' `NTH` and `UPDATE`) and
  `SORTED` (adjacent pairs) are its own dataprops; every lemma it uses is a
  `prfun`/`prfn` with its body in the file.
- `cert_entry.dats`: the C-callable wrapper: copies the input into
  `arr_v` memory, times the sort, and copies the result out. Its `extern`
  declarations (allocation, raw reads and writes, the clock) are the FFI
  boundary of the benchmark, not of the sort.
- `heapsort_plain.dats`: an unverified ATS heap sort over `@[lint][n]`
  with statically checked bounds; `heapsort_c.c`: the same in C.
- `driver.c`: the benchmark input (2^20 values, reversed LCG order) and
  checksum, and a differential test against `qsort` for n = 1..2999 with
  value ranges 2, 3 and ~1e9.

```
heapsort/ats/build.sh && heapsort/ats/driver test
heapsort/ats/bench.sh     # 20 pinned runs of each sort, min and median
heapsort/ats/audit.sh     # greps for axioms, lists proof functions, and
                          # type-checks against a copy of only the ilist_prf
                          # definitions the sort uses
```
