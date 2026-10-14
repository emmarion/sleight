# Heap sort benchmark

Times the heap sorts in `heapsort/` on one input: `perf.sl`'s 2^20 integers
(an LCG from 42, mod 2^30, filled from the end), each program sorting once
and printing the sort-only time and `perf.sl`'s checksum, which `run.py`
checks. From the repository root:

```
heapsort/bench/build.sh
python3 heapsort/bench/run.py [ROUNDS] [EXTRA-SLC-BINARY...]
```

`build.sh` needs `patscc` (`brew install ats2-postiats`, or `apt-get install
ats2-lang` with `PATSHOME` set), `lake` and `idris2`. For each C compiler in
`CCS` (default `cc`) it builds `_build/driver_CC` from `ats/` (C, ATS plain
and ATS certified, each timed inside its entry point). It also builds the Sleight
sorts in `opus/`, `mimo/` and `flat/` with `self/release.sh`'s slc,
`heapsort.ml`'s sort with `ml_main.ml` (with and without `-unsafe`),
`HeapSort.lean`'s sort through `lean/`, and `Hs.idr`, an unverified Idris 2
port of the same sift-down sort. `run.py` runs every program once per round,
one at a time, for ROUNDS rounds (default 11), and prints each one's median
and minimum. Extra arguments are further `perf.sl` binaries, such as an
agent's solution extracted with slc.

With `FL_SWITCH` naming an opam switch whose compiler has flambda (here
`fl-5.4`, OCaml 5.4.1 with `ocaml-option-flambda`), `build.sh` also compiles
the same OCaml, the Sleight sorts' and `heapsort.ml`'s, there with `-O3`, and
`run.py` times those builds too.

Medians of 11 rounds on two machines: an Apple M4 Pro (macOS, Apple clang 21)
and a DigitalOcean `c-4-intel` droplet, four dedicated vCPUs of an Intel Xeon
Gold 6548N at 2.0 GHz (Ubuntu 24.04, gcc 13.3, clang 18.1). Both have OCaml
5.4.1, ATS/Postiats 0.4.2, Lean 4.34.1 and Idris 2 0.8.0 on Chez Scheme.

| Sort | M4 Pro | M4 Pro, flambda `-O3` | Xeon | Xeon, flambda `-O3` |
|---|---|---|---|---|
| ATS certified, clang -O2 | 49.7 ms | | 98.7 ms | |
| ATS certified, gcc -O2 | | | 127.0 ms | |
| C, clang -O2 | 50.4 ms | | 122.2 ms | |
| C, gcc -O2 | | | 134.6 ms | |
| ATS plain, clang -O2 | 50.7 ms | | 121.2 ms | |
| ATS plain, gcc -O2 | | | 133.0 ms | |
| Sleight `mimo/` | 106.7 ms | 85.4 ms | 168.3 ms | 127.1 ms |
| Sleight `opus/` | 105.0 ms | 88.3 ms | 162.6 ms | 135.0 ms |
| Sleight, glm-5.3-flash-flex's (run 2, session 10 of `agent-runs-e194350.csv`) | 102.0 ms | 90.9 ms | 175.2 ms | 142.2 ms |
| Sleight `flat/` | 113.2 ms | 91.7 ms | 166.6 ms | 136.3 ms |
| OCaml handwritten -unsafe | 92.1 ms | 93.1 ms | 145.7 ms | 158.9 ms |
| OCaml handwritten | 102.3 ms | 105.3 ms | 162.1 ms | 178.1 ms |
| Lean verified | 115.9 ms | | 214.3 ms | |
| Idris 2 (plain port) | 814.5 ms | | 1617.1 ms | |

On the Xeon the Sleight sorts with flambda come within about 4-16% of C with
clang, and the fastest beats C with gcc, where on the M4 Pro they take about
1.7-1.8 times C's time; this may reflect OCaml's code generation being more
mature on x86-64 than on arm64. `agent-runs-e194350.csv` has the agent
solutions' Xeon times too.

The Sleight sorts and the C and ATS sorts allocate nothing; `heapsort.ml`'s sort
allocates about 7.9M minor words without flambda and 6.3M with it, perhaps
the closure its `sift` builds on each call. The Idris 2 port is a direct
transcription, not tuned for the Chez backend, and its time may say more
about that backend's `Int` arithmetic than about Idris 2.
