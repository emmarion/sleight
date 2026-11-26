# Notes on the low-level speedups of M9, CHAIN and ABSORB

These notes are a session's account of how some hot helpers use Sleight's
low-level features, and of what was tried and measured; they may be wrong
in places. No macro changes its signature, and nothing uses an axiom.

## What the helpers do

- `phi-chk` (bb/l3c10.sl) decides whether a given register and tail are
  phi(F, s), returning the `Phi` proof. For the FE and FO families it
  walks the block word (`blk-top`, `blk-odd`) against the register token
  by token (`dt-chk`, `dgz-chk`), so the generated register stays erased;
  for FVE and FVO it builds phi's register and compares. `c-jump`'s
  verification and CHAIN/ABSORB's `id-at` use it.
- `c-pgrp` (bb/l3c10.sl) parses the register's run pairs into tokens left
  to right and proves `Xb`/`Tb` for what it emits (`t0s-x`, `tps-x`);
  `xb-split` turns these into the `XT` and `Cat` facts `LmOk` carries. So
  `c-lm` no longer writes the tokens back into runs and compares them
  with the tape. Where that comparison rejected a parse the proof would
  accept (no tokens, no tail, first run longer than 1), `c-lm` still
  answers `LmNo`.
- U62: `c-pgrp` divides a run length by 3 with `u62-divmod` after one
  `nat-fits-u62` check; `awalk` (bb/l3phi.sl) adds the digit offset with
  `u62-add` (bound from `lt-sum` and `dki-lt`) and steps `dpr` down with
  `u62-sub` under a bound checked once in `fast-try`.

## What did not help

- Arrays for `decode`'s digits (an `array-make`d `(Array (Copy (U62)))`
  filled with `array-place-imm` and read with `array-get-many`, in place
  of the reversed digit list and `nrev`): sim9 at 10^7 moves went from
  about 11.6 s to 12.2 s. A guess at the reason: these sequences are a
  few thousand digits and mostly die in OCaml's minor heap, while an
  array that size is allocated in the major heap.
- A two-pass `decode` streaming the digits without any list: no
  measurable change, perhaps because each digit then cost a small
  allocation of its own (multiple return values are tuples after
  extraction).
- Replacing the phi-run-and-compare patterns of bb/l3c10-local.sl,
  bb/l3c10-desc.sl and bb/l3c10-uniform.sl by `phi-chk`: no measurable
  change end to end, so it was left out.
- U62 elsewhere: `Succ`, `lt-dec`, `nat-eq` and matches on `Nat` already
  have inline fast paths for small values after extraction, so only
  `add`, `sub`, `div`/`divmod` and `bit-test` calls are candidates, and
  in the profiles these were a few percent in total.

## Measurements

One shared 4-core container, OCaml 4.14, user time. Before is the base
the work started from; after is this branch.

| what | before | after | Rocq |
|---|---|---|---|
| sim9, 10^6 moves (mean of 2) | 0.42 s | 0.35 s | 1.53 s |
| sim9, 10^7 moves (mean of 2) | 14.6 s | 11.8 s | 89.7 s |
| M9 moves in 22,269–38,513 | 0.13 s | 0.11 s | 0.86 s (`move9` alone) |
| hint stream 22,269–40,035 | 118 s | 97 s | – |
| the same, `s=32M` | 75 s | 58 s | – |
| CHAIN at move 38,507 (`kmain`) | 11.1 s | 9.3 s | – |
| free run to 40,035 (`rprog`) | 166 s | 150 s | 803 s |
| of which CHILD / CHAIN / ABSORB | 61 / 12 / 65 s | 49 / 9 / 68 s | 124 / 138 / 471 s |

The free run is at base 66835b71 (with `mac-absorb2`), which these
changes do not touch. The M9 row is the difference between 11 and 1 repetitions of each M9
move, divided by 10. Rocq's figures are those of the earlier notes. In
every row the outputs equal Rocq's: sim9's configurations, the hint
streams' end configurations, `kmain`'s MATCH, and the free run's entry
index on every move and configurations at 1,000, 10,000, 22,268, 38,513
and 40,035.
