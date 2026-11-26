# Notes on `bb/l3c10-blklaw2.sl`

These notes are a session's account of the file; they may be wrong in
places.

## CHAIN: `mac-chain3`

`mac-chain3` is CHAIN (simC10 entry 9) with type
`Rch l3 c0 e -> Rs l3 c0`, built without axioms. Its guard and output
assembly are `c-train`'s for CHAIN (tail `""`, the two `rshort`
checks). Its loop keeps the block word of `s` itself (not `s + 1` as
ABSORB does), whose bottom pair is `pDp` after every fast step:

- `cf-step`: `zjump` on the block of `s` gives the jump of K rounds
  (`frame`, `zframe`), the cell count checks that it leaves 2 blanks
  before the marker, `blk-snoc` and `hf-next` give the block of the next
  family at `V2 = 4 s1 - D`, and `ct-e` reads the 2 blanks and the
  marker `1^6` as the tokens `Tp T1 T0`, which `ap3-cat` shows are the
  appended digits `[2; 0]`. So the register after the jump is
  `phi(F2, V2)` with no further steps, as in Rocq's lin3s8 `chF`.
- `cf-one`: `cf-step` where it applies, else one step of `ms-loop`
  (`bb/l3c10-chain.sl`) after `phi-run`, and a new analysis (`cs-of`,
  `ana-f`). `ms-loop`'s hints for its next step are carried through
  both paths.

The register's tokens stay erased in the loop and are built once at the
end.

## TRAIN and TRAING: `try-train2`, `try-traing2`

`train-tgt` (`bb/l3c10-local.sl`) is `train-core`'s arithmetic proposal.
`r-run` certifies it as a chain of `Rch -> Rs` moves: `f-move`'s framed
moves (each turned into an `Rch` by `fsq-rch`), and, before a single
step, `try-ident` and `try-sweep3`. Where `f-run` single-stepped across
the register twice per marker (about 4,480 moves), the chain seems to
take about 68 moves per marker. Each marker still costs two jumps with
`phi-run` and an IDENT, all O(P).

## Changes to shared files

- `bb/l3c10-blklaw.sl`: `Hf`, `Fb`, `Wj`, `Ak` and `HfN` take the tail
  `T`, `fb-tt` relates it to a `Phi`, and `Fs` is indexed by the block
  value with `T` as a field. ABSORB passes `Tt1` and `Succ s`.
- `bb/l3c10.sl`: `FqE` and `FqO` take the tail.
- `bb/l3c10-absorb2.sl`: `fq-of` accepts any tail; `pb-of` checks `Tt1`
  itself.
- `bb/l3c10-chain.sl`: `MkMsL` also returns `ms-loop`'s last hints
  (`bb/l3c10-aend.sl` ignores them); `TzrOk` and `TzrNo` alias `TzR`'s
  constructors, which `bb/l3c10-local.sl` shadows.
- `bb/l3c10-local.sl`: `train-tgt` split out of `train-core`.

## Agreement and timings

Shared 4-core container, single runs, user time.

- `bb/l3c10-blklaw2-t.sl`'s `tmain` (index, repetitions, Rocq's input
  and output): all 34 dumped CHAIN instances (`/tmp/claude-0/rocqsim/K`)
  give Rocq's output; so do the 301 TRAIN instances among moves 25,001
  to 25,300 and 30,001 to 35,000 (dumped from Rocq's checkpoints with a
  small driver of the `drvK` kind). The 42 ABSORB dumps still match
  under `bmain`.
- Move 38,507 (CHAIN, about 1,900 markers): about 1.1 s against about
  5.5 s for `mac-chain`, parse excluded (Rocq about 127 s).
- Free run from the blank tape with entries 9, 15 and 16 set to these
  macros (a local edit of `bb/l3c10-run.sl`): the entry that fires
  matches Rocq's on all 40,035 moves and the configurations equal Rocq's
  at 1,000, 10,000, 22,268, 38,513 and 40,035. CHAIN takes about 1.5 s
  (was about 9.9 s), TRAIN about 7.8 s (was about 10.9 s; Rocq 0.8 s),
  the whole run about 92 s user.
- With the same local edit, `bb/l3c10bound.sl` under `--goal proved`
  passes in about 128 s (124 s user), compilation included.

## Open

- Each fast step still walks and rebuilds the block below the jump
  level (`zwalk`, `wtail`'s `sd-run`, `ds-dg`, `push-all`). In the
  CHAIN at move 38,507 the jump level, computed from each gap as
  `cf-step` does, goes down from about 3,800 to about 1,900, one level
  per marker, so this is thousands of levels per marker; Rocq's `fastStep8` keeps
  only the block's value, sum and bottom pair. ABSORB's `af-step` has
  the same walk.
- TRAIN is still about ten times slower than Rocq, which applies
  `comp_exact_even` per marker without simulating.
