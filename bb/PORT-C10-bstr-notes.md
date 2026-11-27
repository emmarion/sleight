# Notes on the 10^110012 goal in 25 pieces (`bb/l3c10bound-110012-bstr.sl`)

These notes are a session's account of an experiment and its
measurements; they may be wrong in places.

## Files

- `bb/l3c10-bstr.sl`:
  - A checkpoint is one `String`: the `PQ` of `bb/l3c10-par37.sl`
    written as bytes in prefix form. A number is its base-255 digits,
    least significant first, each as the byte one above it, then a 0
    byte (`BNum`); a `Bool` is a byte 0 or 1 (`BBit`); a `PGen` or
    `NGen` node is its constructor's position as a byte, then its
    fields (`BP`, `BN`, with `BNs` for a fixed count of numbers);
    `BQ` reads a whole `PQ`. Each relation's constructors are told
    apart by the first byte's `Zero`/`Succ` shape, as
    `fourcolor/red/configs.sl` does.
  - `bnum-fn`, `bns-fn`, `bbit-fn`, `bp-fn`, `bn-fn` and `bq-fn` show
    the decoding functional; `dec-q` computes it.
  - `GenB s e` (the bytes `s` decode to a `PQ` whose `GenP` is `e`),
    `genb-fn`, `gen-b`, `RchB`, `ReachB`, `SpanB` and `rchb-cat` are the
    `PQ` layer of `bb/l3c10-par110.sl` over strings. `rb-first`,
    `rb-run` and `rb-span` run `run-from6` (`c10-run6`, then
    `s15-run` over a script).
  - `chk-b s e` checks that the bytes `s` decode to a `PQ` that
    generates `e` (`GenB s e`) without building the configuration
    that `s` stands for: `unalt` reads the counts off each side of
    `e` (`AltEv`), and `pchk`, `gchk`, `rep-chk`, `trn-chk` and
    `dig-chk` strip each generator's expansion from the front of
    those counts, comparing each number of `e` with one computed from
    the generator, so that a train's numbers are computed one at a
    time and none is kept. `gen-at` is `chk-b`, falling back to
    `gen-b` and `rq-eq`; `rb-first` and `rb-run` check their target
    checkpoint with it against the configuration the run reached.
  - All have the types above and use no axiom.
- `bb/l3c10-bstr-gen.py`: writes the goal (`--goal E SCRIPT
  [--order=...] m:s=src ... m:s`, as `bb/l3c10-par110-gen.py`), with
  each checkpoint as a string literal; `--order` is the order of the
  pieces in the `native-compute`. `--fit DUMP C TEMPLATE.v` fits a
  configuration that `bb/l3c10-bstr-h.sl` dumped (its `C` lines) by
  keeping the far-end items of a Rocq certificate that still match,
  shortening a `repL` or `trnD` that matches in part, and fitting
  what is left near the head.
- `bb/l3c10-bstr-h.sl`: a harness that decodes a checkpoint string,
  runs moves in chunks of 1,000 and then script steps, and prints the
  user time after each, with the configuration at chosen points.
- `bb/l3c10bound-110012-bstr.sl`: the goal, generated with the
  checkpoints below; `bb/l3c10bound-110012-bstr.sh` runs it. With `V`
  the `verify` directory of the busycoq-L3 checkout that holds the
  Rocq certificates, the command that writes it is:

  ```sh
  D=bb/l3c10-bstr-data
  python3 bb/l3c10-bstr-gen.py --goal 110012 $D/script.txt \
    --order=21,6,4,5,20,19,24,3,22,2,23,1,7,9,15,16,14,17,13,18,8,12,11,0,10 \
    46007:0=$V/lin3c1_m1/m1_c2.v 49133:0=$V/lin3c1_m1/m1_c3.v \
    52189:0=$V/lin3c1_m1/m1_c4.v 55117:0=$V/lin3c1_m1/m1_c5.v \
    58111:0=$V/lin3c1_m1/m1_c6.v 60874:0=$V/lin3c1_m1/m1_c7.v \
    64231:0=$V/lin3c1_m1/m1_c9.v 66862:0=$V/lin3c1_m2/m2_c4.v \
    68992:0=$V/lin3c1_m2/m2_c7.v 71317:0=$V/lin3c1_m2/m2_c10.v \
    72978:0=$V/lin3c1_m2/m2_c12.v 74657:0=$V/lin3c1_m2/m2_c14.v \
    76391:0=$V/lin3c1_m3/m3_c1.v 78252:0=$V/lin3c1_m3/m3_c3.v \
    80201:0=$V/lin3c1_m3/m3_c5.v 82198:0=$V/lin3c1_m3/m3_c7.v \
    84158:0=$V/lin3c1_m3/m3_c9.v 86078:0=$V/lin3c1_m3/m3_c11.v \
    87938:0=$V/lin3c1_m3/m3_c13.v 125501:0=$V/lin3c3_s0/s0_c9.v \
    215907:0=$V/lin3c3_s0/s0_c32.v \
    345355:0=$V/lin3c3_s0/s0_c66.v 345355:1199=$V/lin3c4_s2/s2_c1.v \
    345355:1618=$D/q1618.sl 345355:1621 \
    > bb/l3c10bound-110012-bstr.sl
  ```

## Pieces

| piece | from | to | checkpoint source |
|---|---|---|---|
| 0 | blank | move 46,007 | `lin3c1_m1/m1_c2.v` |
| 1 | 46,007 | 49,133 | `m1_c3.v` |
| 2 | 49,133 | 52,189 | `m1_c4.v` |
| 3 | 52,189 | 55,117 | `m1_c5.v` |
| 4 | 55,117 | 58,111 | `m1_c6.v` |
| 5 | 58,111 | 60,874 | `m1_c7.v` |
| 6 | 60,874 | 64,231 | `m1_c9.v` |
| 7 | 64,231 | 66,862 | `lin3c1_m2/m2_c4.v` |
| 8 | 66,862 | 68,992 | `m2_c7.v` |
| 9 | 68,992 | 71,317 | `m2_c10.v` |
| 10 | 71,317 | 72,978 | `m2_c12.v` |
| 11 | 72,978 | 74,657 | `m2_c14.v` |
| 12 | 74,657 | 76,391 | `lin3c1_m3/m3_c1.v` |
| 13 | 76,391 | 78,252 | `m3_c3.v` |
| 14 | 78,252 | 80,201 | `m3_c5.v` |
| 15 | 80,201 | 82,198 | `m3_c7.v` |
| 16 | 82,198 | 84,158 | `m3_c9.v` |
| 17 | 84,158 | 86,078 | `m3_c11.v` |
| 18 | 86,078 | 87,938 | `m3_c13.v` |
| 19 | 87,938 | 125,501 | `lin3c3_s0/s0_c9.v` |
| 20 | 125,501 | 215,907 | `s0_c32.v` |
| 21 | 215,907 | 345,355 | `s0_c66.v` |
| 22 | 345,355 | script step 1,199 | `lin3c4_s2/s2_c1.v` |
| 23 | step 1,199 | step 1,618 (CHILD9 at 1,605, ABSORB8 at 1,612) | dump, fitted against `s2_c1.v` |
| 24 | step 1,618 | step 1,621 (CHAIN8V at 1,619) and the span bound |  |

- Rocq's move counts for `lin3c1_*` appear to equal `c10-run6`'s, and
  those for `lin3c3_s0` less 1,220,145,608 (so that `s0_c0.v` is at
  89,501, where `m3_c16.v` is): the pieces' end checks pass with them.
- The script is the 1,621 indices `bb/l3c10bound-110012-par.sl` runs
  (pieces 2 and 3 there), one per word in
  `bb/l3c10-bstr-data/script.txt`. The fitted checkpoints are
  `bb/l3c10-bstr-data/q1604.sl`, `q1611.sl`, and `q1618.sl`; the goal
  uses only `q1618.sl`.
- The three fitted checkpoints keep 2,970 of the 3,041 left items of
  `s2_c1.v` with 96 new runs at the head, and 6, 4 and 2 of its 21
  right items with 33,084, 125,688 and 195,654 new runs.
- The `native-compute` runs the pieces longest first, by their CPU
  times with the code of `bb/PORT-C10-bigj-notes.md` (those of pieces
  19 and 20 from the harness profile below).
- Pieces 19 to 24 are cut where the large-memory part of the run
  seems to start (about move 87,938), at the script steps above, and
  at `s0_c9.v` (move 125,501), where a profile of the moves from move
  87,938 (`bb/l3c10-bstr-h.sl`, with that code) puts about 97 s
  before the cut and 101 s after it. The `lin3c3_s0` certificates are
  4,000 moves apart; `bb/l3c10-bstr-gen.py` refuses `s0_c10.v` to
  `s0_c12.v`, whose run lists seem to hold two adjacent runs of one
  symbol.
  Pieces 0 to 18 are cut at Rocq certificates only, chosen from a
  profile of the CPU time per 1,000 moves (`bb/l3c10-bstr-h.sl`, from
  the blank tape and six checkpoints up to move 84,158) so as to keep
  each piece under about 205 s with the times as even as the
  certificates allow: they are about 1,000 moves apart past move
  64,231, where 1,000 moves take about 100 s, so finer cuts would need
  fitted dumps. Nearly all of the time below move 87,938 seems to be
  past move 40,000 (about 20 s before it).

## Timings

Both on a shared 4-core, 15 GB container with no other job, one
after the other, and both before the code of
`bb/PORT-C10-fast-notes.md` and `bb/PORT-C10-bigj-notes.md`. The 24
pieces are those of the table above without the cut at move 125,501:
their piece 19 is pieces 19 and 20 here, and their pieces 20 to 23
are pieces 21 to 24. The 24-piece column is from a run with `chk-b`
and `rnorm-q` (`bb/l3c10-child.sl`), the 4-piece column from one
without them.

| | 24 pieces, bytes | 4 pieces, tokens (`-par.sl`) |
|---|---|---|
| result | PASS, exit 0 | PASS, exit 0 |
| wall | 1,193 s | 1,785 s |
| user | 4,467 s | 4,854 s |
| peak RSS (one process) | 3.46 GB | 4.99 GB |
| pieces start after | about 45 s | about 45 s |
| largest piece (CPU) | 331 s (piece 19) | 1,721 s (piece 1) |
| sum of pieces (CPU, `ps` every 5 s) | 4,368 s | 4,800 s |

Per piece in the 24-piece run, CPU seconds and peak RSS:

| piece | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s | 74 | 110 | 123 | 131 | 141 | 147 | 193 | 198 | 166 | 204 | 146 | 155 |
| GB | 0.36 | 0.27 | 0.28 | 0.24 | 0.24 | 0.22 | 0.22 | 0.21 | 0.18 | 0.16 | 0.14 | 0.13 |

| piece | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s | 163 | 172 | 188 | 196 | 209 | 216 | 212 | 331 | 181 | 151 | 271 | 290 |
| GB | 0.12 | 0.11 | 0.10 | 0.09 | 0.08 | 0.07 | 0.07 | 1.68 | 1.39 | 2.80 | 3.46 | 2.89 |

- On 12 processors, starting that run's pieces in its
  `native-compute`'s order (22, 23, 19, 20, 21, then pieces 0 to 18)
  as processors come free, the wall time would seem to be about
  45 s before the pieces start plus about 405 s, about 450 s. The
  pieces running at once would then seem to hold at most about 13.1 GB
  (the sum of their peaks, the first twelve pieces in that order), with
  about 0.7 GB more for `slc` itself.
- The four pieces' CPU was 1,270, 1,721, 1,204 and 605 s, at most
  0.48, 0.19, 4.99 and 3.59 GB.
- Encoding alone (the same four checkpoints, and twelve of an earlier
  split,
  with every piece's moves and script cut to nothing): elaboration
  and ocamlopt came within a few seconds of each other either way,
  and ocamlopt on the saved programs took 14.9 and 15.6 s with
  tokens and 17.6 and 17.7 s with bytes. The goal's program without
  any checkpoint compiled in 0.4 s, so most of the 15 s seems to be
  the simulator code the pieces reach rather than the data.
- Decoding a checkpoint and expanding it to an `Rq` (`gen-e` against
  `gen-b`, measured in one program) took 0.03 to 0.18 s for the
  checkpoints before move 345,355 and 4.2 to 5.3 s after, with no
  consistent difference between the two encodings; nearly all of it
  seems to be the expansion of the trains.

## Memory

- The configurations of the late checkpoints, counted by a harness
  that decodes each with `gen-b` (runs on each side, and the sum of
  the bit lengths of the right side's numbers):

  | checkpoint | left runs | right runs | right bits |
  |---|---|---|---|
  | move 215,907 | 137 | 1,116,731 | 3.98e9 |
  | move 345,355 | 3,831,422 | 130,094 | 3.98e9 |
  | step 1,199 | 3,439,144 | 326,256 | 7.22e9 |
  | step 1,618 | 3,360,732 | 321,822 | 3.98e9 |

- Nearly all of the right side's bits seem to be in explicit trains:
  one of 63,054 markers (63,053 at step 1,618), whose gaps' bit
  lengths fall by 2 from 126,170 to 65, at the far end of the right
  side in all four, about 0.5 GB of digits; and at step 1,199 one more
  of 56,848 markers (about 0.4 GB), which the piece from step 1,199
  absorbs (ABSORB8 at step 1,612). The left sides' numbers are small;
  their cells seem to take about 0.17 GB.
- The simulator works on the explicit `Rq`, so those trains seem to
  be live throughout pieces 19 to 24. A harness run of piece 23's
  script from the step-1,199 checkpoint (no target check) peaked at
  3.45 GB, at the end of ABSORB8, with a heap of about 487M words at
  exit; under `OCAMLRUNPARAM=o=60` it peaked at 2.66 GB and took about
  15% more user time (360 s against 313 s). Much of the peak thus
  seems to be the collector's headroom over a live set of perhaps
  1.2 to 1.5 GB.
- Decoding the step-1,199 checkpoint alone peaked at 1.97 GB; checking
  it with `chk-b` against the configuration decoded from it, at
  2.29 GB in all, so the check's transient numbers seem to cost less
  than a second configuration. In a run of the goal that decoded each
  target with `gen-b` in place of `chk-b`, the peak of the piece that
  ends at step 1,199 went from
  about 2.9 GB to 3.43 GB at that decode.
- `rnorm` builds a copy of each side, the 3.4 to 3.8 million runs of
  the left included; `rnorm-q` skips it where the side is already
  normal, as the proposals certified in pieces 21 to 24 seem to be.

## Other `native-compute`s in the load list

- `bb/l3c10-desc.sl` (`le-run`) and `bb/l3c10-local-tbl.sl` (six
  frame-table checks) each run a `native-compute`, so seven programs
  are compiled before the goal's. Their ocamlopt runs took 0.7 to
  1.8 s each, about 7.4 s in all, and the whole load list elaborated
  in about 24 s. Their results are used later in the load list
  (`le-ar` in `bb/l3c10-desc.sl`, the tables in `bb/l3c10-run.sl`),
  so they were not folded into the goal's `native-compute` here.
- `mirm` is called only in `bb/l3bound*.sl`, which are not in the
  list. The scripts' `rd-nats` calls are inside the piece bodies.

## Run settings

- 1,500 moves from move 64,231 in the harness: 110.5 s by default,
  110.9 s with `--inline 200`, 98.5 s with `OCAMLRUNPARAM=o=200`,
  91.4 s with `o=400` and 93.1 s with both; the peak RSS went from
  0.21 GB to 0.27 GB with `o=200` and 0.42 GB with `o=400`.
- So `--inline 200` seemed to change nothing, and `o=400` to save
  about a sixth of the CPU time at about twice the memory. The goal
  was not run under `o=400` here: its large pieces at about twice
  3.5 GB would not seem to fit two at a time in this container.
  `bb/l3c10bound-110012-bstr.sh` sets neither.
