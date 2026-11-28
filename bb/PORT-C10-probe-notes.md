# Notes on a free run past the 10^110012 endpoint (feasibility probe)

These notes are a session's account of one exploratory run and its
measurements. They may be wrong in places, and the estimates in them
are guesses resting on that one run and on the busycoq-L3 logs.

## What was run

- A `Program` harness (kept outside the repository) over the load list
  of `bb/l3c10bound-110012-bstr.sh`, `bb/l3c10-bstr-h.sl` and one
  probe file. It decodes a byte-string checkpoint (`gen-b`), runs
  scripted `s15-move` indices, and then picks each move by trying a
  list of indices of `s15-ent` in order and taking the first that
  fires, with the `fired` progress guard. It prints the index, the
  CPU time of every try, and the run counts of each side.
- The order is lin3c3's msB11 order with the indices that
  `s15-ent` serves: 6, 39, 20, 23, 24, 26, 1, 28, 42, 30, 37, 40,
  33, 41, then 0 (M9). JUNC (35) is tried, just before M9, only right
  after CHAIN8V (40) or ABSORB8 (41): tried after other moves, its
  proposal was accepted by `jx-plan` at script step 1,600 and the M9
  replay of `c-certify-c` grew past 12 GB.
- Check of the order: from `lin3c4_s2/s2_c1.v` (step 1,199) the free
  run picks the script's index at all 405 steps 1,200 to 1,604.
- Start: `bb/l3c10-bstr-data/q1618.sl`, then script steps 1,619 to
  1,621 (40, 35, 39). `chk-b` finds the configuration after step 1,621
  equal to Rocq's `lin3c4_s2/s2_c2.v`. Move numbers below count from
  there. They seem to equal busycoq-L3's lin3s numbering less about
  1,220,492,848 (the run counts agree with lin3s6 `R7/log.txt` at
  its logged moves up to about move 10,594 here).

## How far it got

- Moves 1 to 10,597 run with no memory or speed problem.
- Move 10,598 is SWEEP3, which leaves a register at the blank right
  end (4,091,718 runs on the left, one on the right). This seems to be
  the configuration of lin3s9's notes at lin3s move 1,220,503,420: the
  frontier register FO182725/tE before its blank-frontier descent.
- The ported FDESC6 (index 37, `c-fdesc-k` with no level cap) fires
  there, but the run passed 9.5 GB within about 40 s and was stopped.
- With FDESC6 capped at 1,024 levels a move (`c-fdesc-k 1024`), 179
  moves of 1,024 levels (140 s of CPU) complete the descent under
  `OCAMLRUNPARAM=o=40`, at about 9.0 GB; without `o=40` the run passed
  9.5 GB after about 100 of them. The new stack is the explicit tokens
  `2^(2p+3)`, whose bits seem to add up to about 4.2 GB, as lin3s9's
  notes say.
- About 100 moves later (move 10,914), a WALKN (`c-wr`) try grew from
  9.0 GB to 12.9 GB in about 5 s and the run was stopped. lin3s9's
  notes say WALKN walks the whole stack in one move there.
- So the probe covers about 10,600 to 10,900 of the about 51,500 moves,
  about a fifth.

## First move with no fitting ported macro

- No ported macro is missing in the sense of nothing firing: M9 (or
  FDESC6) always fires. The first move where the ported table does not
  seem to be enough is move 10,598 to 10,634: the blank-frontier
  descent of FO182725/tE. Rocq's macro for it is `try_fdescB`
  (`verify/lin3s9_fdb.v`, `try_fdescB_sound`, from lin3r6's closed form
  `lin3r6_desc.fdesc_free`), which counts 0 steps and writes the
  stack as `dtrainN q`. lin3s9 ran it with `nz.ml`, an extraction-time
  replacement for Zarith holding `2^e + c` compactly; that is outside
  Rocq's proofs (the driver's integer module).
- msC15's own FDESC (`lin3c4_cfd.try_fdescT`, equal to lin3s6's
  `try_fdesc6`) is the one ported as index 37, so lin3c4's scripted
  simulator would seem to meet the same wall here.
- lin3s9's header of `lin3s9_fdb.v` says the next frontier descents are
  about 2x and 4x larger. If that is in levels, their explicit stacks
  would be about 4x and 16x the 4.2 GB above.

## Cost

Single process on a 4-core, 15 GB container, as the release `slc`
builds it:

- Moves 1 to 10,633: 1,079 s CPU in all; 532 s in the macros' tries
  and 546 s between moves (`c-lm`, which the harness computes once per
  move, the run counts, which walk both sides, and the output; about
  45 to 60 ms a move throughout).
- Per index over those moves (successful tries, then failed tries):

  | index | macro | fired | CPU when fired | largest | CPU of failed tries |
  |---|---|---|---|---|---|
  | 0 | M9 | 5,891 | 4.6 s | 0.22 s | |
  | 37 | FDESC6 | 2,078 | 28.8 s | 9.0 s | 5.5 s |
  | 20 | CONTACT | 2,076 | 2.9 s | 0.03 s | 3.6 s |
  | 33 | ITERV | 158 | 8.7 s | 0.43 s | 7.0 s |
  | 6 | WALKN | 130 | 1.9 s | 0.58 s | 0.1 s |
  | 26 | RESUME1J | 128 | 24.7 s | 0.26 s | 2.9 s |
  | 28 | DDJ | 42 | 0.3 s | 0.06 s | 2.4 s |
  | 30 | DEATH3 | 42 | 0.0 s | | 9.4 s |
  | 41 | ABSORB8 | 42 | 129.0 s | 49.4 s | 16.3 s |
  | 39 | BCOVF | 22 | 5.8 s | 0.88 s | 3.6 s |
  | 42 | CHILD9 | 21 | 200.2 s | 131.0 s | 2.1 s |
  | 40 | CHAIN8V | 1 | 62.1 s | 62.1 s | 1.5 s |
  | 35 | JUNC | 1 | 0.2 s | | |
  | 1, 23, 24 | VDESC2, IDENT, SWEEP3 | 0, 0, 1 | | | 8.0 s |

- Failed tries cost about 62 s in all, so the first-that-fires order
  seems to cost little here.
- The cost per 1,000 moves has no trend: 10 to 83 s of macro CPU,
  with the large ones at the CHILD9/ABSORB8 carries (moves 1,611,
  3,890, 6,862 and 10,555 to 10,558, the last a CHILD9 of FE125524 in
  131 s, where lin3s6 logs 414 s).
- Memory: peak RSS about 3.0 GB up to move 10,597 (at the CHILD9 of
  move 10,558), with the left side falling from 3.36 to 2.36 million
  runs and the right rising from 0.37 to 0.87 million.
- Writing a configuration with `show-cfg` took about 5 GB more for the
  rope at move 10,597 (a 19 MB dump). After the descent, a decimal
  dump would hold the 4.2 GB stack, so checkpoints there would seem to
  need a generator-level dump (`GTrn`) rather than `show-cfg`.

## Estimate (a guess)

- Moves 10,900 to about 51,500 are not measured here. lin3s9's logs
  for the same stretch (its R4 to R8, extracted Rocq with `nz.ml`) list
  as slow: a CHAIN of the level-9 register over the walked
  182,725-marker train (1,202 s), JUNC (2,128 s, `blkW2` falling back
  to `blkN`), FDESC (190 s), a CHILD of FE125524 (200 s), a frontier
  FDESC of FO251049 (93 s), and at the end of the stack phase ABSORBs
  of a 502k-digit register (421 and 1,132 s) and M9s of 25 to 37 s at
  675k digits; the other moves of R5 to R7 took about 3,500 s for
  about 41,000 moves.
- If the memory walls were solved and Sleight's speed relative to that
  log stayed as it is before move 10,600 (where it is mostly faster on
  the large moves), the whole run to the epoch-4 M9 φ-jump might take
  of the order of 3 to 10 CPU hours, plus about 40 minutes of per-move
  overhead. One trajectory is sequential, so 12 cores would help only
  through the goal's split into pieces at checkpoints; with pieces cut
  for even CPU, the wall time of the goal could be roughly a twelfth of
  that plus the largest single move.
- Memory, not time, seems to decide feasibility: the explicit stack
  after the first frontier descent is about 4.2 GB live (9 GB RSS at
  `o=40`), and if the later descents are 4x and 16x that, they would
  not fit in 24 GB with explicit `Nat` runs.

## What to port or speed up first (ranked)

1. A compact representation of the descent's tokens in the
   configuration the macros work on (as `nz.ml`'s `2^e + c`, or a
   train node in the run lists like the checkpoints' `GTrn`), with
   FDESCB (`lin3s9_fdb.try_fdescB`, `lin3r6_desc.fdesc_free`) on it.
   Without it the first frontier descent alone seems to need about
   9 GB, and the later ones more than 24 GB.
2. WALKN, CHAIN and JUNC over that stack without copying it:
   lin3s9's CHAIN of FO251050/tE over the 182,725-marker train
   (lin3s9 notes, ms36), JUNC's block words (`lin3s9_blk.blkC`,
   `lin3s9_uo.UoQ`/`memOKQ`, and lin3s20's `jtry2`/`try_junc_v2`), and
   the walk (lin3s19's `retN`/`peelV` family, if it applies).
3. The level-9/10 descents and CHILDs: `lin3s9_flev.try_fdesc12`/
   `try_fdesc13` (`flevel6_fast`), `lin3s9_child.try_child10`
   (`chainF8A`, `gapsC`), and DEATH3's pre-test with `UoQ`
   (`lin3s9_uo.v`, 120 s to 4 s in lin3s9).
4. The end of the stack phase: the counter-phase macros (AEND, L0,
   AX, FRAME, TRAIN, REENT, BEVEN; msC15 indices 9, 10, and 13 to 18)
   are ported for `c10-ent` but are not in `s15-ent`; lin3s9's R7 log
   also uses LOC and WIN, which are lin3s macros outside msC15; and
   `lin3s9_chain.try_chain9V` for the chain fallback on the
   2-million-run debris.
5. The per-move overhead (about 50 ms a move, half the CPU before
   move 10,600): `c-lm` once per move and no walk of the whole left
   side, if a goal's pieces would otherwise repeat it.
