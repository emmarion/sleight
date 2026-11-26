# Notes on `bb/l3c10-absorb2.sl`

These notes are a session's account of the file; they may be wrong in
places.

## What it is

`mac-absorb2` is ABSORB (simC10 entry 23) with type
`Rch l3 c0 e -> Rs l3 c0`, built without axioms. Per marker, the
register's token list stays erased: the step works on register blocks
(`Pb`: the block word of the family's index, its `PBlk`, the digit and
token relations and the cell count, for `FO P 1` and `FE P 1`).

One marker (`am-step`):

- the jump of `k` rounds is `phi-chain` and `rdk-run`, with the cell
  counts of both registers from their blocks (`pb-cells`); `k` comes from
  a Newton search on the cell count (`am-k`), with an untrusted probe of
  the next round (`rnd-run`, `ucells`) so that the jump is the maximal
  one, as in `ms-jk`;
- the register after the jump with the digits `2 0` appended is the
  register of the next family at `4 s - sD(w)`; this is checked by
  computing that block (`phi-pb`) and comparing it with the old block
  plus `pDp` (`sn-chk`, `dg-ex3`, `enc-ap3`), as `bb/l3train.sl` does;
- the contact is proven from the round of that register (`conj`): the
  round's sweep is split at the appended pair (`sw-split`, which needs
  the register to end in `T0`, `E1`), and its end and walk are forced to
  be the contact's (`rd-contact`); `ct-run` is `ct-absorb` of
  `bb/l3c10-chain.sl` with those erased facts in place of the runtime
  sweep and walk;
- the round's cost is 4 because the cell count of the next register
  (its block is the round of the snoc'ed block, `rnd-run` with `rnd-blk`
  and `rnd-fn`) is 9 more than that of the jumped register (`c-four`);
  this is a runtime check.

`ab2-run` parses as `c-train` does, loops `am-step`, and rebuilds the
tape once at the end (`phi-run` and `phi-fn`). It also returns the
number of markers and the reason the loop stopped (an index into the
`AmNo` sites of `am-step`).

## Additive changes to shared files

`bb/l3c10.sl`: `fam-e` and `FeR` (the `FE` constructor of `Fam` is
shadowed by the type `FE` of `bb/l3c10-local.sl`), `FQ` and `fq-next`
(the level of a family's block), and `RndW`, an alias of `Rnd` from
`bb/l3phi.sl` (shadowed by `bb/l3c10-child.sl`).

## Status

The per-marker work is still O(P): two block computations (`blk-fast`
for the jump target and for the snoc'ed register) and a few list passes.
The contact only handles a remaining gap of 2; where the guessed jump
leaves 0 or 1 blanks, or the snoc check fails, the loop stops there.

Measured (one shared container, single runs, user time): all 42 dumped
ABSORB instances give Rocq's output (`/tmp/claude-0/rocqsim/K`); with
entry 23 of `bb/l3c10-run.sl` set to `mac-absorb2` (a local edit, not
committed), the free run from the blank tape picks Rocq's entry on all
40,035 moves and its configurations equal Rocq's at the five checkpoints.
ABSORB's moves then take about 67 s in all against about 110 s with
`mac-absorb` in the same build (Rocq 471 s), and the run to 40,035 about
172 s against 213 s. What would make it O(1) is Rocq's lin3s7/lin3s8
block laws (snoc_ok, the decrement and borrow laws, critb8), which would
give both blocks from the previous one without computing them; none of
those is ported here.

## Test

`bb/l3c10-absorb2-t.sl`'s `amain` reads an index and Rocq's input and
output configurations (the `/tmp/claude-0/rocqsim/K` dumps); index 23
runs `ab2-run`, index 200 + i runs `c10-mac i`.
