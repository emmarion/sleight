# Porting Rocq's simC10 to Sleight

`bb/l3c10.sl` is the start of a one-to-one port of the counted L3
simulator simC10 of busycoq-L3 (`verify/lin3c1_csim10.v`, at commit
22cb139), at Rocq's macro granularity: a ported macro is meant to turn
Rocq's configuration into the configuration Rocq's macro produces, run
list for run list. So far it ports M9, the fallback move. These notes
are a session's reading of the Rocq sources and its measurements; they
may be wrong in places.

## Rocq's move

`moveC10 c = moveL msC10 c` tries the entries of `msB10`, each wrapped
by `lin3c1_cext.cntG`, in order, and takes the first that applies. If
none applies it takes `lin3e1b_sim9.move9`, called M9 here. The moves
each entry took from the blank tape to move 40,035 (where the step count
passes 10^15573), from drvT's per-macro statistics:

| # | name | Rocq function | moves |
|---|---|---|---|
| 0 | BIGJC | `bigJC10` | 0 |
| 1 | BIGJ | `bigJ10` | 0 |
| 2 | RET | `lin3c1_cperf.try_retS` | 544 |
| 3 | VDESC | `lin3c1_csim.vdescCS` | 2 |
| 4 | WALKN | `lin3c1_cperf.try_walkNS` | 853 |
| 5 | CHILD | `lin3c1_cchild.try_child7H` | 250 |
| 6 | BCOVF | `lin3c1_cfast2.try_bcovf2` | 424 |
| 7 | REENT | `lin3m3_reent.try_reent` | 0 |
| 8 | BEVEN | `lin3c1_cfast2.try_beven2` | 0 |
| 9 | CHAIN | `lin3s5_chain.try_chain3W` | 34 |
| 10 | DEATH | `lin3c1_cfast.try_death2` | 179 |
| 11 | AEND | `lin3s4_aend.try_aend4` | 641 |
| 12 | L0 | `try_L0` | 1,630 |
| 13 | AX | `try_AX` | 1,027 |
| 14 | FRAME | `try_frame tbl1` | 484 |
| 15 | TRAIN | `try_train` | 789 |
| 16 | TRAING | `lin3s4_traing.try_traing` | 0 |
| 17 | FDESC | `lin3c1_cfd.try_fdescKC` | 1,012 |
| 18 | CONTACT | `try_contact` | 805 |
| 19 | CONTACT0 | `lin3s4_contact0.try_contact0` | 0 |
| 20 | ITER | `lin3s4_guard.try_iterG` | 641 |
| 21 | IDENT | `lin3s4_guard.try_identG` | 168 |
| 22 | SWEEP3 | `lin3s4_sweep3.try_sweep3` | 769 |
| 23 | ABSORB | `lin3s5_absorb.try_absorb3` | 42 |
| 24 | RESUME1 | `resume1J` | 70 |
| 25 | VDESC2 | `lin3s5_vdesc.try_vdesc2` | 14 |
| – | M9 | `lin3e1b_sim9.move9` | 29,657 |

M9 is itself a chain: at an L-moment (`at_lm9`) the phi jump
(`try_jump9`, JUMP), one round (`try_round`, ROUND) or a sweep
(`try_sweep`, SWEEP); otherwise `walk_move` (WALK); otherwise, when
`is_wc`, Rocq's `macro` (WIPE, CHAIN-W or one step); otherwise `shift`
(SHIFT), and failing that `macro`. Of the 29,657 M9 moves among moves 1
to 40,035 the trace shows 22,645 single steps, 2,110 CHAIN-W, 2,084
ROUND, 1,363 WIPE, 1,201 JUMP and 254 SWEEP, and no WALK or SHIFT: the
configurations they would take seem to be taken earlier in the list.

## The Sleight side

- The configuration is `rle.sl`'s `Rq` (state, left runs nearest
  first, head bit, right runs), which has Rocq's `rcfg` shape, with
  states A to F as 0 to 5 and `S0`/`S1` as `BFalse`/`BTrue`. Its
  denotation is `Den`/`Dc`, and the invariant is `Rch l3 c0 e`: the
  configuration denotes, up to trailing blanks, one reached from `c0`.
  Each ported macro takes `Rch l3 c0 e` and returns an `Rs l3 c0`, so its
  type is its soundness statement. Run lengths are `Nat`, which the FFI
  holds as Zarith integers, unboxed below 2^62, so `U62` is not used;
  every proof object is erased.
- Rocq's list operations are ported with `Den` proofs: `cpushn`
  (`pushn`), `rpop` (`pop`, already in `rle.sl`), `rstrip` (the
  structural `strip`), `rapp` (`++`), `rest-take`, `left-split`,
  `push-runs` (`napp` of a run list without empty runs), and register
  runs are built per token by `l3jump.sl`'s `xtr` rather than per cell
  as Rocq's `rle_cells` does. `cpushn` and `rest-take` may drop
  trailing blanks, which `rch-z` absorbs through `CEz`.
- `c-move9` follows `move9` branch for branch: `c-lm` (`at_lm9`'s
  parse: `parse7`, `enc`, the strip), `c-jump` (`try_jump9` with
  `choose8`'s choice of the number of rounds), `c-round`, `c-sweep`,
  `c-walk`, `is-wc`, `c-shift` (a 24-cell window simulation of one
  period, at most 2000 steps, and the period-iteration lemma `per-run`),
  and `c-mac` (WIPE, CHAIN-W, one step). The proofs reuse `l3jump.sl`'s
  `rdk-run`, `l3life.sl`'s `phi-chain`, `l3round.sl`'s sweep, gadget and
  walk lemmas, and `rle.sl`'s `trun-frame`. The heuristic parts (the
  parse, `decode`, the choice of k) carry no proof; their results are
  checked or used only as proposals.
- `c10run` iterates `c-move9`, which makes it a port of Rocq's `sim9`.
  `bb/l3c10smoke.sl` uses it for a `NoHaltBelow` goal; it passes.
- No step counts are kept: the Sleight bounds come from the tape span.

## The oracle

`bb/l3c10drv.ml` links against Rocq's extraction `x_c1sim10c.ml`:

- `trace N DIR m1 m2 ...` records, per move, the entry Rocq took (and
  M9's branch), and writes configurations at the given moves;
- `hints A B OUT x` writes the configuration at move A and then one
  record per move up to B: for a move Rocq made by M9, its branch and a
  fingerprint of the result (state, head, first runs); for any other
  move, the change to the two run lists. `all` in place of `x` writes
  changes for every move. `OUT.end` is the configuration at B;
- `sim9 N` runs `move9` alone N times from the blank tape.

The configuration text is `q h`, then each side as a count followed by
bit and length pairs. `bb/l3c10h.sl`'s `hmain` reads a repetition count
and a hint stream, computes each M9 move with `c-move9` (as many times
as the count says, keeping the last), checks it against the
fingerprint, applies the other moves' changes, restarting `Rch` from the
patched configuration, and prints the final configuration; `smain` runs
`c10run` from the blank tape. Both are built with slc's `--build`, from
a one-line file holding `hmain` or `smain`, and need `ulimit -s
unlimited`. From the repository root, with `main.sl` holding `hmain`:

```sh
_build/release/slc std/list.sl std/immediate.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl std/macro.sl bb/skelet.sl bb/space.sl bb/sk17.sl bb/rle.sl bb/l3.sl bb/l3tok.sl bb/l3round.sl bb/l3jump.sl bb/l3phi.sl bb/l3dec.sl bb/l3life.sl bb/l3walk.sl bb/l3train.sl bb/l3c10.sl bb/l3c10h.sl main.sl --build h
(echo 1; cat hints.txt) | ./h
```

The same files with `bb/l3c10smoke.sl` in place of the last two, under
`--goal proved`, check the smoke goal.

## Measurements

One 4-core container, OCaml 4.14, single runs unless stated.

- Moves 1 to 22,268 and 22,269 to 38,513 of simC10: every M9 move
  computed by `c-move9` matches Rocq's fingerprint, and the final
  configurations equal Rocq's at 22,268 and 38,513. Rocq's `move9`
  alone takes about 0.09 s and 0.46 s on those M9 moves; the difference
  between 11 and 1 repetitions puts `c-move9` at about 0.03 s and
  0.15 s.
- Rocq's moveC10 spends about 5.5 s on the 8,152 M9 moves among moves
  22,269 to 38,513, nearly all of it in the 25 entries that are tried
  and fail first; `c-move9` alone does not try them.
- `c10run` against Rocq's `sim9` from the blank tape, equal
  configurations at the end: see the table below.

  | moves | Sleight | Rocq | Sleight, `s=8M` | Rocq, `s=8M` |
  |---|---|---|---|---|
  | 10^6 | 0.39 s | 0.84 s | 0.42 s | 0.70 s |
  | 3·10^6 | 12.2 s | 41 s | 8.2 s | 21 s |
  | 10^7 | 18.4 s | 55 s | 13.4 s | 31 s |

  Each entry is the mean of two runs; `s=8M` is `OCAMLRUNPARAM=s=8M`, a
  larger minor heap, for both. A callgrind profile of 3·10^6 moves put
  about 46% of the Sleight run in the garbage collector, and of the rest
  most in `decode`, `phi-run` and `xtr`.
