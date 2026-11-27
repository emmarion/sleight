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
  checkpoints below; `bb/l3c10bound-110012-bstr.sh` runs it.

## Pieces

| piece | from | to | checkpoint source |
|---|---|---|---|
| 0 | blank | move 55,117 | `lin3c1_m1/m1_c5.v` |
| 1 | 55,117 | 64,231 | `m1_c9.v` |
| 2 | 64,231 | 71,317 | `lin3c1_m2/m2_c10.v` |
| 3 | 71,317 | 77,301 | `lin3c1_m3/m3_c2.v` |
| 4 | 77,301 | 83,198 | `m3_c8.v` |
| 5 | 83,198 | 87,938 | `m3_c13.v` |
| 6 | 87,938 | 345,355 | `lin3c3_s0/s0_c66.v` |
| 7 | 345,355 | script step 1,199 | `lin3c4_s2/s2_c1.v` |
| 8 | step 1,199 | step 1,604 | dump, fitted against `s2_c1.v` |
| 9 | step 1,604 | step 1,611 (CHILD9 at 1,605) | dump, fitted against `s2_c1.v` |
| 10 | step 1,611 | step 1,618 (ABSORB8 at 1,612) | dump, fitted against `s2_c1.v` |
| 11 | step 1,618 | step 1,621 (CHAIN8V at 1,619) and the span bound | |

- Rocq's move counts for `lin3c1_*` and `lin3c3_s0` appear to equal
  `c10-run6`'s: the pieces' end checks pass with them.
- The script is the 1,621 indices `bb/l3c10bound-110012-par.sl` runs
  (pieces 2 and 3 there), one per word in
  `bb/l3c10-bstr-data/script.txt`. The three fitted checkpoints are
  `bb/l3c10-bstr-data/q1604.sl`, `q1611.sl`, and `q1618.sl`.
- The three fitted checkpoints keep 2,970 of the 3,041 left items of
  `s2_c1.v` with 96 new runs at the head, and 6, 4 and 2 of its 21
  right items with 33,084, 125,688 and 195,654 new runs.
- The order of the pieces in the `native-compute` is 9, 0, 1, 2, 11,
  3, 4, 5, 10, 6, 7, 8, chosen so that on four processors no more than
  two of the large-memory pieces seem to run at once.

## Timings

All on a shared 4-core, 15 GB container, with another session's
compiled job taking about one core throughout; pieces got about 0.75
of a core each.

| | 12 pieces, bytes | 4 pieces, tokens (`-par.sl`) |
|---|---|---|
| result | PASS, exit 0 | PASS, exit 0 |
| wall | 2,252 s | 2,233 s |
| user | 6,218 s | 6,170 s |
| peak RSS (one process) | 3.44 GB | 4.84 GB |
| elaboration to the goal's compile | 24.4 s | 23.9 s |
| ocamlopt of the goal's program | 14.9 s | 15.6 s |
| largest piece (CPU) | 758 s (piece 9) | about 1,740 s |
| sum of pieces (CPU, `ps` every 5 s) | 6,167 s | about 6,130 s |

Per piece in the 12-piece run, CPU seconds and peak RSS:

| piece | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s | 495 | 495 | 574 | 585 | 598 | 524 | 564 | 537 | 136 | 758 | 377 | 524 |
| GB | 0.42 | 0.24 | 0.21 | 0.14 | 0.11 | 0.08 | 1.87 | 2.96 | 3.32 | 3.23 | 3.38 | 2.89 |

- With a processor per piece, the wall time would seem to be about
  40 s before the pieces start plus the largest piece, about 800 s,
  against about 1,790 s for the four pieces; but all twelve at once
  would hold about 19 GB.
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
- Piece 9's script steps (1,605 to 1,611) in the harness from its
  checkpoint: 724 s by default (from the dumping run, the same
  binary) and 616 s with `o=400`, at 4.9 GB peak against 3.2 GB for
  piece 9 in the goal run.
- So `--inline 200` seemed to change nothing, and `o=400` to save
  about a sixth of the CPU time at about twice the memory. The goal
  was not run under `o=400` here: its large pieces at about twice
  3.3 GB would not seem to fit two at a time in this container.
  `bb/l3c10bound-110012-bstr.sh` sets neither.
