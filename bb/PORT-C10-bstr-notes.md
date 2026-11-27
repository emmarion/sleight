# Notes on the 10^110012 goal in twelve pieces (`bb/l3c10bound-110012-bstr.sl`)

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
    `s15-run` over a script); a piece decodes its target checkpoint
    only after its run, so that the two configurations are not live
    at once.
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
    --order=10,0,1,2,11,3,4,5,9,6,7,8 \
    55117:0=$V/lin3c1_m1/m1_c5.v 64231:0=$V/lin3c1_m1/m1_c9.v \
    69746:0=$V/lin3c1_m2/m2_c8.v 74657:0=$V/lin3c1_m2/m2_c14.v \
    79212:0=$V/lin3c1_m3/m3_c4.v 84158:0=$V/lin3c1_m3/m3_c9.v \
    87938:0=$V/lin3c1_m3/m3_c13.v 215907:0=$V/lin3c3_s0/s0_c32.v \
    345355:0=$V/lin3c3_s0/s0_c66.v 345355:1199=$V/lin3c4_s2/s2_c1.v \
    345355:1618=$D/q1618.sl 345355:1621 \
    > bb/l3c10bound-110012-bstr.sl
  ```

## Pieces

| piece | from | to | checkpoint source |
|---|---|---|---|
| 0 | blank | move 55,117 | `lin3c1_m1/m1_c5.v` |
| 1 | 55,117 | 64,231 | `m1_c9.v` |
| 2 | 64,231 | 69,746 | `lin3c1_m2/m2_c8.v` |
| 3 | 69,746 | 74,657 | `m2_c14.v` |
| 4 | 74,657 | 79,212 | `lin3c1_m3/m3_c4.v` |
| 5 | 79,212 | 84,158 | `m3_c9.v` |
| 6 | 84,158 | 87,938 | `m3_c13.v` |
| 7 | 87,938 | 215,907 | `lin3c3_s0/s0_c32.v` |
| 8 | 215,907 | 345,355 | `s0_c66.v` |
| 9 | 345,355 | script step 1,199 | `lin3c4_s2/s2_c1.v` |
| 10 | step 1,199 | step 1,618 (CHILD9 at 1,605, ABSORB8 at 1,612) | dump, fitted against `s2_c1.v` |
| 11 | step 1,618 | step 1,621 (CHAIN8V at 1,619) and the span bound | |

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
- The order of the pieces in the `native-compute` is 10, 0, 1, 2, 11,
  3, 4, 5, 9, 6, 7, 8, chosen so that on four processors no more than
  two of the large-memory pieces seem to run at once.
- The cuts were chosen from the CPU time per move of an earlier split,
  so that the pieces' CPU times come out roughly even.

## Timings

Both on a shared 4-core, 15 GB container with no other job, one
after the other.

| | 12 pieces, bytes | 4 pieces, tokens (`-par.sl`) |
|---|---|---|
| result | PASS, exit 0 | PASS, exit 0 |
| wall | 1,367 s | 1,785 s |
| user | 4,911 s | 4,854 s |
| peak RSS (one process) | 3.49 GB | 4.99 GB |
| pieces start after | about 40 s | about 45 s |
| largest piece (CPU) | 527 s (piece 0) | 1,721 s (piece 1) |
| sum of pieces (CPU, `ps` every 5 s) | 4,846 s | 4,800 s |

Per piece in the 12-piece run, CPU seconds and peak RSS:

| piece | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s | 527 | 514 | 443 | 450 | 448 | 503 | 412 | 333 | 220 | 351 | 333 | 312 |
| GB | 0.36 | 0.24 | 0.21 | 0.16 | 0.12 | 0.09 | 0.07 | 1.68 | 1.79 | 3.43 | 3.49 | 2.89 |

- With a processor per piece, the wall time would seem to be about
  40 s before the pieces start plus the largest piece, about 570 s,
  against about 1,770 s for the four pieces. All twelve at once would
  seem to hold about 14.5 GB, with about 0.7 GB more for `slc` itself.
- The four pieces' CPU was 1,270, 1,721, 1,204 and 605 s, at most
  0.48, 0.19, 4.99 and 3.59 GB.
- Encoding alone (the same four checkpoints, and the same twelve,
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
