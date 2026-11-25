# Notes on `bb/l3c10-local.sl`

These notes are a session's account of what `bb/l3c10-local.sl` proves and
how it was checked; they may be wrong in places.

## Macros

Each is a function of type `Rch l3 c0 e -> Rs l3 c0` (indices as in `bb/PORT-C10.md`):

| # | name | Sleight | how |
|---|---|---|---|
| 0 | BIGJC | `try-bigjc` | `try-bigj`, `c-move9`, `try-contact` in sequence |
| 1 | BIGJ | `try-bigj` | Rocq's guard, then `c-move9` |
| 12 | L0 | `frame-tbl tbl-l0` | frame entries L0B, L0A |
| 13 | AX | `frame-tbl tbl-ax` | frame entry |
| 14 | FRAME | `frame-tbl tbl-frame` | Rocq's `tbl1` |
| 15 | TRAIN | `try-train` | Rocq's `twalk` proposal, certified by framed replay |
| 16 | TRAING | `try-traing` | the same, with Rocq's gap-1 check (`g1chk`) |
| 18 | CONTACT | `try-contact` | gadget, sweep, a contact end (`Ct`, `ct-ok`), walk |
| 19 | CONTACT0 | `try-contact0` | never fires: Rocq's `mcontact _ _ 0` seems to be `None` for every input |
| 20 | ITER | `try-iterG` | rounds chained as an `RdK` and applied by `c-apply` |
| 21 | IDENT | `try-identG` | re-tokenized register (`wtk`, `tokz`), then as ITER |
| 22 | SWEEP3 | `try-sweep3` | the `c-st3` episode and `c-sw0` trips |

## The framed simulator

`f-move` ports Rocq's frame simulator `sim6` (jump, round, walk, WIPE/CHAIN,
single steps). Each move returns an `FR e e2`: an erased function at the
fixed level `LF` that, for any far context `X`, gives a run from the
configuration `e` followed by `X` to `e2` followed by `X`. `FSq` chains them
and `fsq-run` composes the runs. A frame entry (`FE`) holds an input, an
output and an `FSq` between them; the table file `bb/l3c10-local-tbl.sl`
(written by `notes-local/gen-tbl.py` from Rocq's dump) builds each `FSq` at
compile time with `native-compute`, so a firing costs only the strip and the
rebuild of the output. `f-cert` replays `f-move` at run time towards a
proposed configuration and turns the `FSq` into an `Rch` (`fsq-rch`); TRAIN
and TRAING use it.

## Checks

`bb/l3c10-local-h.sl`'s `mmain` reads kind-3 records (Rocq's macro index and
the change); the driver mode `hm` of `notes-local/drvL.ml` writes them for
every non-M9 move. For each record whose index is ported, the macro must give
Rocq's configuration exactly; with the negative flag, every ported macro with
a smaller index must not fire, on every move, M9 moves included. On moves 1
to 40,035 all 6,313 ported instances matched (L0 1,630, AX 1,027, FRAME 484,
TRAIN 789, CONTACT 805, ITER 641, IDENT 168, SWEEP3 769) and no negative
check failed. BIGJ, BIGJC, TRAING and CONTACT0 fire nowhere in that range,
which the negative check agrees with; their positive behaviour is untested.

## Timings

One container, single runs, the macro alone on its in-situ instances, total
over moves 1 to 40,035 (Sleight from 201 repetitions against 1):

| macro | Sleight | Rocq (`msB10` entry alone) |
|---|---|---|
| L0, AX, FRAME | below noise | 2.0, 0.3, 1.4 ms |
| CONTACT | 0.04 s | 0.24 s |
| ITER | 0.17 s | 0.57 s |
| IDENT | 0.28 s | 0.38 s |
| SWEEP3 | below noise | 0.17 s |
| TRAIN | about 9.5 s | 0.08 s |

TRAIN is far slower: it replays the composite of every marker (174,807
markers over 759 of its instances) where Rocq applies its arithmetic. An
O(1)-per-marker proof would need Rocq's `comp_exact_even` web.
