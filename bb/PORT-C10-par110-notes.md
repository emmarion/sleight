# Notes on the 10^110012 goal in pieces (`bb/l3c10bound-110012-par.sl`)

These notes are a session's account of an experiment and its
measurements; they may be wrong in places.

## Files

- `bb/l3c10-par110.sl`:
  - A checkpoint is a `PQ` whose two sides are chains of `PDig`
    chunks: a token list. `PPrs` and `NPrs` parse the tokens in prefix
    form into the `PGen` and `NGen` of `bb/l3c10-par.sl` and
    `bb/l3c10-par37.sl` (tags 0 to 3, then each number as a limb count
    and its base-2^32 limbs, `LimbEv` and `NumEv`). `pprs-fn` and
    `nprs-fn` show the parse functional; `pprs` and `nprs` compute it.
  - `GenE`, `gene-fn`, `gen-e`, `RchE`, `ReachE`, `SpanE`, `rche-cat`
    and `rche0` are the `PQ` layer of `bb/l3c10-par37.sl` over the
    parse. `re-run n sc g g2` and `re-span n sc bnd g` run `c10-run6`
    for `n` moves and then `s15-run` over the script `sc`.
  - All have the types above and use no axiom.
- `bb/l3c10-par110-gen.py`: converts a Rocq `rcfg` certificate (`repL`,
  `trnD`, literals) into a `PGen` (a `trnD` is a `GTrn` with `a = 4`),
  checks that it expands to the certificate's configuration, encodes it
  as tokens, and with `--goal E SCRIPT m:s=src ... m:s` writes a goal
  whose checkpoint `m:s` is move `m` of `c10-run6` and then step `s`
  of the script.
- `bb/l3c10bound-110012-par.sl`: four pieces, moves 1 to 67,500,
  67,501 to 85,000, 85,001 to 345,355 with script steps 1 to 1,199
  (Rocq's `lin3c4_s2/s2_c1.v`), and script steps 1,200 to 1,621 with
  the span bound.

Build: the full L3 file list, then `bb/l3c10-run.sl`,
`bb/l3c10-far.sl`, `bb/l3c10-train.sl`, `bb/l3c10-trlaw.sl`,
`bb/l3c10-chf.sl`, `bb/l3c10-far2.sl`, `bb/l3c10-par.sl`,
`bb/l3c10-par37.sl`, `bb/l3c10-par110.sl` and the goal file, with
`--goal proved` and `ulimit -s unlimited`.

## Profile

User seconds of compiled runs, from separate harness runs:

| stretch | s |
|---|---|
| blank to 67,500 (`c10-move-f`) | 1,562 |
| 67,500 to 85,000 | 1,724 |
| 85,000 to 89,501 | 562 |
| 89,502 to 345,355 (`c10-move-l`) | 607 |
| script 1 to 1,199 | 507 |
| script 1,200 to 1,604 | 133 |
| script 1,605 (CHILD9) | 774 |
| script 1,612 (ABSORB8) | 446 |
| script 1,619 (CHAIN8V) | 561 |
| the other script steps after 1,604 | 11 |

- The script times are from `bb/l3c10-far2h.sl` from the configuration
  at move 345,355 with fingerprints only at steps 1,199 and 1,621
  (2,432 s for the script). The fingerprints there equal those of
  Rocq's `s2_c1.v` and `s2_c2.v`. The earlier harness run, with a
  fingerprint after every step, spent about a second per step on it.
- The three large steps seem to make about 1,780 s the floor for any
  piece that holds all of them.

## Checkpoint sizes

| checkpoint | raw | generator | as tokens |
|---|---|---|---|
| move 67,500 | 146 MB | `PQ` 134 KB, 130 nodes | 138 KB, 20 nodes |
| move 85,000 | 6.6 MB | `PQ` 152 KB, 138 nodes | 156 KB, 21 nodes |
| move 89,501 (`m3_c16.v`, 54 KB) | 1.2 GB | not converted: a `trnU` | |
| move 345,355 (`s0_c66.v`, 1.17 MB) | 1.2 GB | `PQ` 1.15 MB | |
| step 1,199 (`s2_c1.v`, 1.18 MB) | 1.2 GB | `PQ` 785 KB, 24,800 nodes | 1.16 MB, 91 nodes |
| step 1,621 (`s2_c2.v`, 1.18 MB) | 0.4 GB | `PQ` 1.16 MB | |

- At step 1,199 the right side is two `trnD` trains (63,053 and 56,847
  runs) and the left about 3.4 million runs: 1,743 `repL` blocks, about
  45,000 small literal runs, and about 1,100 large ones (548,000
  decimal digits in all).
- A `trnU` (values growing away from the head) seems not to be a
  `GTrn`, which builds from the far end; the left side's large values
  at 345,355 grow that way too (each 16 times the one before plus a
  constant), with a different stretch of small runs between each two.
- The 785 KB nested `PQ` alone ran out of memory in elaboration at
  about 9.9 GB, apparently from its nesting depth (a chain of 8,000
  `GCons` alone took more than 6.5 GB, a balanced tree of 16,000 nodes
  about 3 s). As a balanced `NGen` tree (56,000 nodes) it elaborated in
  about 14 s over the file list, but `native-compute`'s ocamlopt then
  ran for more than 19 minutes before it was stopped. As tokens it
  elaborates and compiles in under a minute.

## Timings

`bb/l3c10bound-110012-par.sl` on a shared 4-core container (load about
1 from other work): PASS, exit 0, 2,098 s wall, 7,083 s user, 4.84 GB
peak (the third piece). The pieces started about 40 s in and used about 1,450,
1,950, 1,610 and 2,030 s of CPU (from `ps` samples every 10 s), at
most 0.5, 0.2, 4.8 and 3.4 GB. `bb/l3c10bound-110012.sl` alone was
8,328 s wall in the far2 session.

## Open

- A checkpoint near script step 1,604 might bring the largest piece
  from about 2,030 s to about 1,880 s; no Rocq certificate is there,
  so it would need a fit of a dumped configuration.
