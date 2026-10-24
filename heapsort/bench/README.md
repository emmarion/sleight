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
sorts in `agent/solutions/heapsort-fast/opus/`, `agent/solutions/heapsort-fast/mimo/`
and `flat/` with `self/release.sh`'s slc,
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

Medians of 11 rounds on two machines: an Apple M4 Pro (macOS 26.6, Apple
clang 21, Chez Scheme 10.4.1) and a DigitalOcean `c-4-intel` droplet in
nyc3, four dedicated vCPUs of an Intel Xeon Platinum 8358 at 2.6 GHz (Ubuntu
24.04, gcc 13.3, clang 18.1, Chez Scheme 9.5.8). Both have OCaml 5.4.1,
ATS/Postiats 0.4.2, Lean 4.34.1 and Idris 2 0.8.0.

| Sort | M4 Pro | M4 Pro, flambda `-O3` | Xeon | Xeon, flambda `-O3` | Lines |
|---|---|---|---|---|---|
| ATS certified, clang -O2 | 49.9 ms | | 105.4 ms | | 281 |
| ATS certified, gcc -O2 | | | 139.8 ms | | 281 |
| C, clang -O2 | 50.0 ms | | 128.2 ms | | 17 |
| C, gcc -O2 | | | 139.5 ms | | 17 |
| ATS plain, clang -O2 | 51.1 ms | | 128.2 ms | | 26 |
| ATS plain, gcc -O2 | | | 137.8 ms | | 26 |
| Sleight `mimo/` | 106.2 ms | 88.0 ms | 187.4 ms | 135.9 ms | 2047 |
| Sleight `opus/` | 106.4 ms | 87.6 ms | 179.4 ms | 136.1 ms | 834 |
| Sleight, glm-5.3-flash-flex's (run 2, session 10 of `agent-runs-8860c75.csv`) | 101.5 ms | 90.7 ms | 185.7 ms | 157.2 ms | 2099 |
| Sleight `flat/` | 114.1 ms | 90.6 ms | 187.3 ms | 145.1 ms | 611 |
| OCaml handwritten -unsafe | 93.0 ms | 91.9 ms | 163.6 ms | 173.5 ms | 23 |
| OCaml handwritten | 101.3 ms | 104.2 ms | 178.4 ms | 194.9 ms | 23 |
| Lean verified | 117.6 ms | | 228.2 ms | | 263 |
| Idris 2 certified | 210.0 ms | | 424.9 ms | | 338 |
| Idris 2 (plain port) | 820.4 ms | | 1852.7 ms | | 28 |

`sizes.py` writes `sizes.csv`, the size of each sort: its non-blank lines
(the `Lines` column above) and non-whitespace characters, both with comments
removed, and its bytes. It counts the sort and any proofs, but not the
benchmark harness around it. For ATS certified, Lean and Idris 2 certified
that includes their own statements of sortedness and permutation; for
Sleight it does not, since the task gives `spec.sl`, which `sizes.csv` lists
on its own row. Arguments
of the form `NAME=SANDBOX` add an agent session's `work/files.txt`, as for
the glm-5.3-flash-flex row here. Line counts may compare poorly across
languages with different line lengths and proof styles.

On the Xeon the Sleight sorts with flambda take about 1.06-1.23 times the
time of C with clang, and the fastest two beat C with gcc, where on the M4
Pro they take about 1.75-1.81 times C's time; this may reflect OCaml's code
generation being more mature on x86-64 than on arm64. `agent-runs-8860c75.csv`
has the agent solutions' Xeon times too.

The Sleight sorts and the C and ATS sorts allocate nothing; `heapsort.ml`'s sort
allocates about 7.9M minor words without flambda and 6.3M with it, perhaps
the closure its `sift` builds on each call. The Idris 2 port is a direct
transcription, not tuned for the Chez backend, and its time may say more
about that backend's `Int` arithmetic than about Idris 2.
