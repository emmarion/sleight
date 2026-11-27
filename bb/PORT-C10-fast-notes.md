# Notes on the arithmetic block jump (`bb/l3c10-blklaw.sl`)

These notes are a session's account of the code and its measurements;
they may be wrong in places.

## What the code does

- `zjump`, which ABSORB's `af-step`, CHAIN's `cf-step` and CHILD's
  `cl-step` call once per marker, first tries `vjump`. `vjump` works
  from the block's value `V` and its sum of pair deltas `D`, with the
  block word erased. Where it does not apply, `zjump` builds the word
  from `V` (`wr-list`, O(P), once) and runs the walk of
  `bb/PORT-C10-slow3-notes.md` (`zjump-l`). ABSORB's contact round,
  `wjump`, is split the same way (`wjump-v`, `wjump-l`).
- A block word is held as `Wr`: a bottom-first list (`WrL`), or no
  list, with an erased proof that the bottom pair is `pDp` (`WrV`) or
  without one (`WrN`). After a `vjump` the state stays a `WrV`.
- `trel` is lin3s7's `T_rel` stated against `PBlk`: for a block of `p`
  levels and value `r` whose frozen pairs are at most its last pair
  (`Fzl`), with `Hp w a b` the base-4 Horner value of the pair digits
  (`Tdg`: 0 for `pD` and `pDp`, 1 for `pC`, 2 for `pB` and `pBp`, 3 for
  `pA`) started from `a`, `4 b + sD w = a 4^(p+1) + 3 r`.
- `dig-lem` is lin3s7's `Tv_digit` for that form: with `T = 3 V - D`,
  the pair at level `p + 1` (`p` levels below it) has the digit
  `(T / 4^(p+1)) mod 4`. `vdig` reads a pair this way with `shr` and
  `divmod`, below a frozen-free part of the word.
- `vwalk` is `zwalk` with each pair read by `vdig`; `zstep` is the step
  both share. Once the slack of `zwalk`'s certificate (`ZOk`) is at
  least the number of unchanged levels left below the jump level, and
  at most one more than the top of the current level, `zmid` takes all
  of those levels at once, lowering the slack by one per level, and
  `zmid-s` adds their pair deltas and cell digits to the window sums as
  erased amounts, which cancel in `wtail` (`Sm2`, `psub`). The levels
  from the jump level up are again read by `vdig`. `zfin` is the end of
  the jump that `zjump-l` and `vjump` share.
- So a fast marker seems to cost one `vdig` per level below the point
  where the slack is large enough (about nine levels when the jump
  level is in the tens of thousands), one per changed level, and some
  other operations on numbers of the register's size; no list of the
  word is walked or rebuilt.
- All have the types they had (`Rch l3 c0 e -> Rs l3 c0` for the
  macros); none uses an axiom.

## Changes to shared files

- `bb/l3c10.sl`: `fq-num`, the runtime `Q` of an `FQ`.
- `dm-uniq` is in `bb/l3c10-blklaw.sl` rather than
  `bb/l3c10-par37.sl`.
- `bb/l3c10-blklaw2.sl` (`cf-step`), `bb/l3c10-chf.sl` (`cl-step`,
  `ClR`, `cl-loop`): a `Wr` in place of the list and its `Rva`.

## Agreement and timings

Shared 4-core container, single runs.

- `bb/l3c10-bstr-h.sl` built with `lin3c4_s2/s2_c1.v`'s checkpoint
  (script step 1,199), script steps 1,200 to 1,618, configuration
  printed at the end: the same configuration as with the code of
  ee7978df; 99 s user against 280 s, step 1,605 (CHILD9) 12.4 s
  against 44.8 s, step 1,612 (ABSORB8) 46.2 s against 185 s.
- The 24-piece goal, `bb/l3c10bound-110012-bstr.sh` under
  `/usr/bin/time -v`: PASS, exit 0, 16:53 wall, 3,764 s user, 3.45 GB
  peak, against 19:45, 4,451 s and 3.46 GB for ee7978df. Per piece, CPU
  seconds from `ps` every 5 s (ee7978df in parentheses): 22: 82 (271),
  23: 92 (290), 19: 301 (331), 20: 176 (181), 21: 93 (151); pieces 0
  to 18 took 63 to 187 s (74 to 216 s), with a sum over all pieces of
  3,655 s (4,368 s).
- `bb/l3c10bound.sl` after the full file list through
  `bb/l3c10-run.sl`, `--goal proved`: PASS, exit 0, 88.6 s user,
  0.63 GB peak (ee7978df: 88.5 s, 0.60 GB).

## Where the time goes

- In ABSORB8, by stack samples, most of the remaining time seems to be
  `vdig`'s shifts and divisions of `T`, `top-run` (in `zc` and
  `maxs-run`), multiplications by 3 and 4 of the block value, and the
  collector's work on the large heap that each such number allocates.
- Piece 19 is now the longest. In the harness from `m3_c13.v` (move
  87,938), the first 1,000 moves took about 105 s and the next 1,000
  about 68 s, both with this code and with ee7978df's, and later stretches of
  1,000 moves about 1 s; the stack samples there were in `c10-big`,
  `bigj-ok`, `xg`, `c-pgrp` and `c-enc`, not in the climbs.

## Open

- TRAIN's climb (`ls-train`, `bb/l3c10-trlaw.sl`) does not use these
  laws.
- `vdig` shifts all of `T` once per level read; reading the low levels
  from `T mod 4^h`, or from two `bit-test`s, might cut that, with a
  lemma relating either to `dig-lem`'s division.
- `wjump-v` reads the pair above the bottom from the digits although
  ABSORB's jump has just made it `pD`.
