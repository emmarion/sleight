# Notes on `bb/l3c10-aend.sl`

These notes are a session's account of the file; they may be wrong in
places.

## What the file holds

simC10's entry 11, AEND (`lin3s4_aend.try_aend4`, equal to
`lin3m2_rcfg.try_aend`), as `c-aend : Rch l3 c0 e -> Rs l3 c0`. No axiom
is used. Rocq certifies AEND through the A-end theory (`aendChk`,
`lin3m2_aend.aend_x`); `c-aend` instead follows the machine through the
same run and certifies each part with proven pieces:

- the climb over the walked death debris, one marker `1^6` at a time,
  is `aend-loop`, a copy of `l3c10-chain.sl`'s `ms-loop` that picks the
  contact by the gap the jump leaves: 2 blanks take `ct-absorb` (Rocq's
  `mcontact`), any other gap takes `ct-chain` (the identity re-read of
  the marker as two `T0` tokens) followed by `stride`'s rounds; the
  jump is `ms-jk`. On the sampled instances the gaps were 2 and 0, as
  `lin3d28_climb` seems to predict;
- the Ddeath contact (`lin3d28_dd.ddcontact`) is `ct-dd`: the gadget,
  the sweep to the end, `merge` on `1 00`, a sweep over the four `T0`
  tokens of `1^12`, the 59-step local episode `c-dd` (checked by
  `sk-family`), and the walk with stack `2 2 2 3 (s+1) ...` and word
  `+ + 1 0`;
- the two entry rounds (`iterC 2 ... tE`) are `c-round`, run twice on
  the configuration `c-rounds` rebuilds.

The firing conditions mirror Rocq's where they are cheap: counter 2,
tail `1`, the debris shape `0^G (1^6 0^(6 Lp k))_(k=q..0) 1^12 0 1^2 0^Gd`
(`hc-ok`, with `6 Lp k = 2^(2k+3) - 2`), and a register that decodes to
an odd family at `s = max - 2` (`memOK`'s fresh member). Rocq's
`aendChk` is not recomputed; the run itself is checked.

## Changes outside this file

`bb/l3c10-desc.sl`: `dprop` dispatches index 11 to `c-aend`, so
`bb/l3c10-aend.sl` is loaded after `bb/l3c10-chain.sl` and
`bb/l3c10h.sl` and before `bb/l3c10-desc.sl`.

## Checking

With that load order, `dmain` on `hints mine` output for moves 1 to
40,035 checks all 641 AEND records, and all match Rocq; the final
configuration equals Rocq's. A scan of every move whose Rocq entry
comes after AEND in `msB10` (M9 included) found no configuration on
which `c-aend` fires.

## Timings (one shared 4-core container, noisy)

`tmain 11 3` against `tmain 11 1` puts the 641 AEND moves at about
7.2 s of user time; Rocq's own time for them is about 7.6 s. A
callgrind profile of one large instance (243 markers) puts about two
thirds of `c-aend` in `phi-run`, one call in the jump and one in
`ident` per marker, and much of the rest in the garbage collector, so
the cost per marker is O(P) like Rocq's `climbChk`.
