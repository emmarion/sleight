# Notes on the 10^37981 goal in pieces (`bb/l3c10bound-37981-par.sl`)

These notes are a session's account of an experiment and its
measurements; they may be wrong in places.

## Files

- `bb/l3c10-par37.sl`:
  - `DigEv k b n zs ys`: `ys` is the `k` base-`b` digits of `n`, least
    significant first, followed by `zs`. `dm-uniq` (quotient and
    remainder are unique, from `div-small`) gives `dig-fn`, and
    `dig-loop` computes it with `divmod`.
  - `PGen`: `PNil`, `PDig k b n g` (digits as above, then `g`) and
    `PG h g` (an `NGen` of `bb/l3c10-par.sl` over `g`). `PEv`, `pev-fn`
    and `pev` are its meaning, functionality and computation.
  - `PQ`, `GenP`, `genp-fn`, `gen-p`, `RchP`, `ReachP`, `SpanP`,
    `rchp-cat` and `rchp0` are `QGen`, `GenQ`, ... of
    `bb/l3c10-par.sl` over `PGen`. `rp-run` and `rp-span` are
    `rg-run` and `rg-span` with `c10-run3` (`run-from3`).
  - All have the types above and use no axiom.
- `bb/l3c10-par37-gen.py`: fits a `PQ` to a configuration (the format
  `show-cfg` prints, or the Python tuples of the par session's dumps),
  and with `--goal E LAST m=file ...` writes a whole goal file for
  10^E after LAST moves with checkpoints at moves `m`. It uses
  `l3c10-par-gen.py`'s fit, then packs every stretch of values below
  64 into `PDig` chunks of at most 1,500 digits; trains and runs of 64
  or more stay `NGen`.
- `bb/l3c10bound-37981-par.sl`: the goal of `bb/l3c10bound-37981.sl`
  in four pieces: moves 1 to 60,000, 60,001 to 71,700, 71,701 to
  81,500, and 81,501 to 89,501 with the span bound, in one
  `native-compute`.

Build: the full L3 file list, `bb/l3c10-run.sl`, `bb/l3c10-far.sl`,
`bb/l3c10-par.sl`, `bb/l3c10-par37.sl` and the goal file, with
`--goal proved`.

## Profile

Cumulative user time of `c10-move-f` per move (the far session's runs:
blank to 67,500, and 67,500 to 89,501 from its dump), in seconds:

| move | 20,000 | 30,000 | 40,035 | 45,000 | 50,000 | 55,000 | 60,000 | 65,000 | 67,500 |
|---|---|---|---|---|---|---|---|---|---|
| s | 0.3 | 8.6 | 91 | 205 | 402 | 665 | 971 | 1,331 | 1,562 |

| move | 70,000 | 72,500 | 75,000 | 77,500 | 80,000 | 82,500 | 85,000 | 87,500 | 89,501 |
|---|---|---|---|---|---|---|---|---|---|
| s | 1,771 | 1,996 | 2,225 | 2,473 | 2,729 | 2,999 | 3,281 | 3,586 | 3,855 |

- From blank to 67,500 most of the time is BIGJC (802 s) and BIGJ
  (429 s); from 67,500 to 89,501 nearly all of it is BIGJ (2,281 s of
  2,292 s), about 0.09 to 0.13 s per move, growing slowly. TRAIN takes
  about 9 s in all, so `c10-run4` would not change this goal.
- Equal quarters fall near moves 59,918, 71,702 and 81,517.

## Checkpoint sizes

Raw is the `show-cfg` text; `QGen` is `l3c10-par-gen.py`'s generator;
`PQ` is `l3c10-par37-gen.py`'s. Run counts are left/right.

| move | raw | runs | `QGen` | `PQ` |
|---|---|---|---|---|
| 60,000 | 205.7 MB | 618 / 113,714 | 246 KB | 104 KB |
| 64,500 | 188.6 MB | 618 / 125,476 | 485 KB | 130 KB |
| 67,500 | 146.2 MB | 618 / 124,774 | 485 KB | 135 KB |
| 70,000 | 115.0 MB | 618 / 124,598 | 484 KB | 138 KB |
| 71,700 | 95.9 MB | 618 / 124,294 | 483 KB | 141 KB |
| 75,000 | 63.8 MB | 618 / 123,700 | 483 KB | 146 KB |
| 78,500 | 36.9 MB | 618 / 119,874 | 484 KB | 149 KB |
| 81,500 | 19.8 MB | 618 / 113,874 | 484 KB | 151 KB |
| 85,000 | 6.6 MB | 618 / 106,874 | 484 KB | 152 KB |
| 89,000 | 0.5 MB | 618 / 98,874 | 484 KB | 154 KB |

- The raw size is nearly all one train of large runs, which BIGJ eats
  two runs at a time; four `GTrn`s cover the large runs. What is left
  is about 99,000 small runs (mostly 1, 3, 6, 9 and 12) that the
  `QGen` fit covers with about 4,000 literals, 5,700 `GRep`s and 640
  small trains, about 44,000 numbers in all. A `PQ` holds them in about
  70 `PDig` numerals; it has about 110 to 140 constructor applications,
  and its text is nearly all numeral digits, including one run of
  15,569 digits on the left.
- Rocq's checkpoints `lin3c1_m3/m3_c1.v` to `m3_c15.v` (moves 76,391 to
  89,467) are 834 to 849 KB each; `m3_c16.v` (89,501) is 54 KB. The
  configuration at 89,501 is about 1.2 GB raw; the `QGen` fit of it was
  stopped after 20 minutes, so it is not in the table.

## Timings

`slc --goal proved` on a shared 4-core container, load about 4 to 7
from other sessions while the pieces ran.

- `bb/l3c10bound-37981-par.sl`: PASS, exit 0, 2,361 s wall, 4,318 s
  user, 2.1 GB peak. Elaboration and compilation took about 60 s
  before the four compiled pieces started; they used 1,046, 1,044,
  1,132 and 1,035 s of CPU in about 2,200 to 2,290 s of wall time each,
  at most 0.5, 0.3, 0.2 and 1.4 GB.
