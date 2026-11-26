# Notes on `bb/l3c10-blklaw.sl`

These notes are a session's account of the file; they may be wrong in
places.

## Status (work in progress)

- Proven, erased, uniform: `frame` (replace the low part of a block whose
  upper part has no frozen pair by a block of the same length and smaller
  value), `blk-snoc` (Rocq's snoc_ok and val_snoc at the PBlk level), and
  list/cell bookkeeping (`sd-swap`, `ds-swap`, `dg-split`, `dg-join`,
  `rva-cat`).
- `mac-absorb3` (proven) runs ABSORB with `wjump`: the jump target's low
  levels are recomputed from their value, walked up from a bottom-first
  list. It gives Rocq's output on the instances tried, but the jump
  level is often high (window of about P/2 levels at move 39,739), so it
  is slower than `mac-absorb2`.
- Next: Rocq's decrement law at the PBlk level (top digit pA/pB to
  pC/pD, bottom pDp to pD, middle unchanged, with a slack argument for
  the pA pairs of the middle), so that only the middle's lowest levels
  are inspected.
