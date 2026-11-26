# Notes on `bb/l3c10-blklaw.sl`

These notes are a session's account of the file; they may be wrong in
places.

## What it is

`mac-absorb3` is ABSORB (simC10 entry 23) with type
`Rch l3 c0 e -> Rs l3 c0`, built without axioms. It follows
`mac-absorb2` (`bb/l3c10-absorb2.sl`) but keeps, between markers, a
compact state instead of recomputing register blocks: the block word of
`s + 1` as a bottom-first list (`Fs`, with `Rva` to the top-first word),
its cell count and its sum of pair deltas (`sD`), and an erased bundle
(`Fb`) of the block, digit, token and cell relations.

## The laws (erased, uniform in the block)

- `frame`: in a block whose upper part has no frozen pair, the lowest
  levels can be replaced by any block of the same length and smaller
  value; the whole value drops by the same amount.
- `zframe`: the same over a bottom raised from `pDp` to `pD`, with pairs
  above it either kept or changed (`Off` gives each pair's offset); a
  slack certificate (`ZOk`, `Slk`) shows that each `pA` pair of the new
  word still fits. This covers Rocq's decrement law (lin3s7 dec_val) and
  both borrow laws (bor_val, lin3s8 bor2_val).
- `blk-snoc`: Rocq's snoc_ok and val_snoc at the `PBlk` level: under a
  frozen-free block of value rho, appending `pDp` gives the block of
  `4 rho - sD w`.
- Bookkeeping: `sd-swap` (pair deltas), `dg-split`, `dg-join`, `pa-cat`,
  `ds-swap` (cells), `rva-cat` (bottom-first list to word).

## One marker (`af-step`)

The gap `G` gives `L = (G + 4) / 6` and the jump level from the bit
length of `3 L + 1`. `zjump` walks the bottom-first list to that level
(the middle is only inspected for the slack of its lowest levels), on
through a run of `pD` pairs for the borrow shapes, and certifies the
jump target with `zframe` and `frame` (`wtail`), updating cells and
`sD` from the changed window only. The jump amount is checked against
the gap by the cell count. Then `blk-snoc` gives the next family's
block, and the contact round is certified by `wjump` on its two lowest
levels. Where any of this does not apply, the step falls back to
`am-step` and a new analysis (`ana-f`, O(P) once).

Per marker the work is a walk of the list to the jump level, which is
often about half the register's length, plus O(1) big-number operations
of register size; no block is computed from its value.

## Agreement and timings

Shared 4-core container, single runs, user time.

- The 42 dumped ABSORB instances (`/tmp/claude-0/rocqsim/K`, driver
  `bb/l3c10-blklaw-t.sl`, `bmain`) all give Rocq's output.
- Move 39,956 (10,197 markers): about 9.5 s including about 1 s of
  parse, against about 44 s for `mac-absorb2` in the same driver (Rocq
  481 s). Move 39,739: 1.4 s against 4.2 s.
- Free run from the blank tape with entry 23 set to `mac-absorb3` (a
  local edit of `bb/l3c10-run.sl`, not committed): the entry that fires
  matches Rocq's trace on all 40,035 moves and the configurations equal
  Rocq's at 1,000, 10,000, 22,268, 38,513 and 40,035. ABSORB's 42 moves
  take about 14 s (Rocq 471 s); the run to 40,035 about 100 s user.
- With the same local edit, `bb/l3c10bound.sl` under `--goal proved`
  passes in about 159 s (138 s user), compilation included.

## Additive change to shared files

`bb/l3c10.sl`: `FamE`, an alias of `Fam`'s constructor `FE`, which
`bb/l3c10-local.sl` shadows.

## Open

CHAIN (`mac-chain`) and TRAIN/TRAING do not use these laws yet.
