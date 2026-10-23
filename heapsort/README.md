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

`mimo/` holds an Sleight heap sort certified against
`agent/tasks/heapsort-fast/spec.sl`, written by the mimo-v2.6-pro agent
on the heapsort-fast task. `mimo/files.txt` lists its files in order. It
sorts a different input, `perf.sl`'s 2^20 pseudo-random integers below
2^30, once, and prints the time and what the sort allocates. From the
repository root:

```
dune exec bin/main.exe -- std/nat.sl std/list.sl agent/tasks/heapsort-fast/spec.sl \
  $(cat heapsort/mimo/files.txt) agent/tasks/heapsort-fast/perf.sl \
  --extract heapsort/mimo_perf.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg heapsort/mimo_perf.ml -o heapsort/mimo_perf && heapsort/mimo_perf
```

`opus/` holds another, written by the claude-opus-5-5 agent in the first
session of run `20261012-1220-claude-opus-5-5-heapsort-fast`; of the runs in
`agent-runs-8860c75.csv`, it is the smallest solution by non-whitespace
characters outside comments. It runs as `mimo/` does, with `opus` for `mimo`.

`agent-runs-8860c75.csv` lists the heapsort-fast agent runs made on commit
8860c75, one row per run: the first session whose `work/` passed (it
compiles in the prescribed order with no warnings and no `;! suppress`, and
`perf.sl` reaches the expected checksum allocating nothing), and the
context used and dollars spent at that session's first such `perf.sl` run.
A Claude session derived it by re-checking each session with slc built at
that commit and reading the erased OCaml of each first pass to judge that it
is a heap sort; that judgment and the `notes` column are its reading and may
be wrong. Dollars are the provider's reported cost for Neuralwatt models and
`agent/pi.py`'s list-price estimate otherwise. The `sort_ms` columns are
`perf.sl`'s own `wall-ns` reading, which brackets only the sort:
the median and minimum of 9 rounds on an Apple M4 Pro (OCaml 5.4.1), each
round running every passing session's build once, in turn, with nothing
else running. `fastest_passing_session` is the run's passing session with
the lowest median. The `flambda_` columns are the same OCaml compiled with
flambda `-O3`, timed in the same rounds, and the `x86_` columns are both
measurements on `bench/`'s Xeon. Differences of a few milliseconds are
within the noise.
The `code_` columns measure the first passing session's own files, those
its `work/files.txt` lists: how many, their non-blank lines and
non-whitespace characters with `;` comments removed, and their bytes as
written.

`bench/` times all of these, and C, Lean and Idris 2 heap sorts, on
`perf.sl`'s input; its README has the results.

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

`idris/` holds an in-place heap sort in Idris 2 (0.8.0, Chez backend) whose
type states that the output is a permutation of the input and sorted, as
checked by `idris2` with `%default total`:

- `HeapSort.idr`: the sort,
  `heapSort : (n : Nat) -> {0 xs : Vect n Int} -> (1 _ : Arr xs) -> Ex (\ys => (Perm xs ys, Sorted ys))`.
  `Arr xs` is a linear handle to the array, indexed by the vector `xs` of
  its contents. `Perm` (a sequence of `Swap`s of two positions) and `Sorted`
  (adjacent pairs, by `Int`'s `<=`) are its own types, and its heap
  invariants follow `ats/heapsort_cert.dats`. Every lemma is declared with
  quantity 0 and has its body in the file, which contains no escape hatch. It finds
  `n/2` by `Integer` division, checking the bounds it needs at run time.
- `Arr.idr`: the trusted base, whose definitions `HeapSort.idr` uses only
  through their types:
  - `leTrans` and `leFlip`, assumed with `believe_me`: `Int`'s `<=` is
    transitive, and `not (x <= y)` implies `y <= x`. `<=` on `Int` is a
    primitive that Idris does not unfold, so these may not be provable.
  - `Arr`, whose index is a phantom: that `xs` is the array's contents is
    assumed, and kept by exporting `Arr` without its constructor.
  - `get`, whose `Nth i x xs` (the value read is the one at position `i` of
    `xs`) is assumed with `believe_me`, and `set`, whose new contents a
    proved lemma computes and which are assumed to match memory. Both call
    Scheme's `vector-ref` or `vector-set!` through `%foreign`, as `PrimIO`
    applied to `%MkWorld` (as `unsafePerformIO` does), with indices whose
    bounds the types prove.
  - `withArr`, which assumes the array it is given has length `n`; it gives
    its continuation `replicate n 0` as the ghost contents, which the
    continuation cannot rely on since it is polymorphic in them. `done`
    ends the handle.

  The trust may also extend to Idris 2's linearity checking, which keeps a
  handle from being used twice, and to its compiler keeping the order of
  the `PrimIO` calls, as it does for `IO`.
- `Main.idr`: the benchmark input and checksum, as `bench/Hs.idr`, and a
  differential test against `Data.List.sort` for n = 1..2999 with value
  ranges 2, 3 and ~1e9.

```
cd heapsort/idris && idris2 Main.idr -o hs_cert && build/exec/hs_cert test
heapsort/idris/audit.sh   # greps for escape hatches and directives,
                          # type-checks, and checks the compiled Scheme for
                          # erased definitions and for closures or erased
                          # placeholders in the sort's own functions
```

With `IDRIS2_SRC` naming the `libs/` directory of an Idris 2 0.8.0 source
checkout, `audit.sh` also greps the sources of the library modules the two
files import. There, the only `believe_me`s are in `Decidable.Equality`'s
named `FromEq` instance, which `decEq` at `Nat` does not use.
