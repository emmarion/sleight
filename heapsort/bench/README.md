# Heap sort benchmark

Times the heap sorts in `heapsort/` on one input: `perf.sl`'s 2^20 integers
(an LCG from 42, mod 2^30, filled from the end), each program sorting once
and printing the sort-only time and `perf.sl`'s checksum, which `run.py`
checks. From the repository root:

```
heapsort/bench/build.sh
python3 heapsort/bench/run.py [ROUNDS] [EXTRA-SL-BINARY...]
```

`build.sh` needs `patscc` (`brew install ats2-postiats`), `lake` and
`idris2`. It builds `ats/driver` (C, ATS plain and ATS certified, each timed
inside its entry point), the SL sorts in `opus/`, `mimo/` and `flat/` with
`self/release.sh`'s slc, `heapsort.ml`'s sort with `ml_main.ml` (with and
without `-unsafe`), `HeapSort.lean`'s sort through `lean/`, and `Hs.idr`, an
unverified Idris 2 port of the same sift-down sort. `run.py` runs every
program once per round, one at a time, for ROUNDS rounds (default 11), and
prints each one's median and minimum. Extra arguments are further `perf.sl`
binaries, such as an agent's solution extracted with slc.

With `FL_SWITCH` naming an opam switch whose compiler has flambda (here
`fl-5.4`, OCaml 5.4.1 with `ocaml-option-flambda`), `build.sh` also compiles
the same OCaml, the SL sorts' and `heapsort.ml`'s, there with `-O3`, and
`run.py` times those builds too.

On an Apple M4 Pro (OCaml 5.4.1, Apple clang 21, ATS/Postiats 0.4.2,
Lean 4.34.1, Idris 2 0.8.0 on Chez Scheme), 11 rounds, median and minimum:

| Sort | OCaml without flambda | flambda `-O3` |
|---|---|---|
| ATS certified | 49.7 ms (48.9) | |
| C (clang -O2) | 50.4 ms (49.8) | |
| ATS plain | 50.7 ms (49.5) | |
| SL `mimo/` | 106.7 ms (104.7) | 85.4 ms (83.8) |
| SL `opus/` | 105.0 ms (102.5) | 88.3 ms (86.3) |
| SL, glm-5.3-flash-flex's (run 2, session 10 of `agent-runs-e194350.csv`) | 102.0 ms (99.8) | 90.9 ms (89.1) |
| SL `flat/` | 113.2 ms (111.3) | 91.7 ms (89.8) |
| OCaml handwritten -unsafe | 92.1 ms (90.3) | 93.1 ms (91.6) |
| OCaml handwritten | 102.3 ms (100.5) | 105.3 ms (103.3) |
| Lean verified | 115.9 ms (113.1) | |
| Idris 2 (plain port) | 814.5 ms (806.3) | |

The SL sorts and the C and ATS sorts allocate nothing; `heapsort.ml`'s sort
allocates about 7.9M minor words without flambda and 6.3M with it, perhaps
the closure its `sift` builds on each call. The Idris 2 port is a direct
transcription, not tuned for the Chez backend, and its time may say more
about that backend's `Int` arithmetic than about Idris 2.
