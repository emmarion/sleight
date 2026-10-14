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

On an Apple M4 Pro (OCaml 5.4.1 without flambda, Apple clang 21, ATS/Postiats
0.4.2, Lean 4.34.1, Idris 2 0.8.0 on Chez Scheme), 11 rounds:

| Sort | Median | Min |
|---|---|---|
| ATS certified | 49.4 ms | 48.3 ms |
| ATS plain | 50.1 ms | 49.5 ms |
| C (clang -O2) | 50.3 ms | 49.1 ms |
| OCaml handwritten -unsafe | 91.2 ms | 89.9 ms |
| OCaml handwritten | 101.0 ms | 99.2 ms |
| SL, glm-5.3-flash-flex's (run 2, session 10 of `agent-runs-e194350.csv`) | 101.9 ms | 99.7 ms |
| SL `opus/` | 104.3 ms | 102.7 ms |
| SL `mimo/` | 106.0 ms | 104.5 ms |
| SL `flat/` | 112.8 ms | 110.9 ms |
| Lean verified | 115.7 ms | 113.8 ms |
| Idris 2 (plain port) | 813.8 ms | 801.9 ms |

The SL sorts and the C and ATS sorts allocate nothing; `heapsort.ml`'s sort
allocates about 7.9M minor words, perhaps the closure its `sift` builds on
each call. The Idris 2 port is a direct transcription, not tuned for the Chez
backend, and its time may say more about that backend's `Int` arithmetic
than about Idris 2.
