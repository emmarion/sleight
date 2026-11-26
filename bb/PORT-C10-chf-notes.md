# Notes on `bb/l3c10-chf.sl`

These notes are a session's account of the file and its measurements;
they may be wrong in places.

## Where CHILD's time goes

`c-child-f` (`bb/l3c10-far.sl`) checks the head (`child-pre`,
`child-head`) and replays M9 with the cascade (`reach-t1`) up to the
first L-moment with tail `1`, which `certify-fc` then completes. In
per-move profiles of that replay at moves 21,268, 38,258, 39,807,
89,609 and 89,787, the replay has the same shape: the head (a jump, a
sweep and about 100 small moves), the cascade (`c-casc`), a walk of
about 13 moves per marker that lays the death train down, and the climb
over the train, one M9 jump per marker (`0^G 1^6` with `G = 6 L_j`). Each jump parses, decodes and
rebuilds the register, so the climb seems to cost time quadratic in
`P`. At move 39,807 (`P = 7827`) the 7,828 jumps took about 48 of the
replay's 74 s under the profiler, and the L-moment parses of the same
moves most of the rest.

In the counter (89,502 to 345,355) the instances have `P = 120` or
`P = 488`, all with contact rest `gc = 2`. There the climb starts with
two markers that M9 takes as a block of about `0.42 P` single rounds
and a jump each: the register in front of them seems not to be
phi-canonical, so M9's jump does not apply.

## What the file holds

- `cl-step` is `af-step` of `bb/l3c10-blklaw.sl` without the contact
  round, for a register `phi(F, s)` with tail `E` facing `0^G 1^6`:
  `zjump` certifies the jump to the block of `s - K` (the frame and
  decrement or borrow laws of `bb/l3c10-blklaw.sl`), `rdk-run` gives the
  machine run, and `blk-snoc` with `Ap3` re-views the `0^2 1^6` left in
  front of the next marker as the last two digits of the next family's
  register at `4 (s - K) - D`. `peel26` and `ap3-xb` do the run and bit
  bookkeeping.
- `cl-loop` chains `cl-step` over the markers, carrying the block word
  and an erased run from the first configuration; `cl-run` parses and
  analyses the register once (`decode`, `id-at`, `ana-f`), loops, and
  rebuilds the tape once (`phi-run`).
- `rd-batch` runs the rounds of a non-canonical register in front of a
  marker as one move: `rd-iter` chains `rd-run`'s rounds into one `RdK`
  while the tail is unchanged, the cells fit in the gap and the register
  is not phi-canonical (`canon-ok`), and `c-apply` makes the move.
- `reach-c` is `reach-t1` with `cl-run`, then `rd-batch`, tried before
  each move after the cascade; it skips both while the runs past the
  first gap are those of its last attempt. `c-child-h` is `c-child-f`
  over `reach-c`; `c10-move-h` is `c10-move-l` with entry 5 over it, and
  `c10-run6` iterates it.

All have the type `Rch l3 c0 e -> Rs l3 c0` (or return an `Rs`); none
uses an axiom. The certified step still replays the head, the walk and
the death; only the climb and the round blocks are taken by laws.

## Where CHILD can differ from Rocq

As in `c-child-r`, Rocq's chain search (`chainF2`) is not run: CHILD
fires when the head guards and the room check pass and the replay
reaches a configuration that `certify-fc` certifies. The climb and the
round blocks only shorten the replay; they are machine runs along the
same trajectory, and the target is still compared exactly. The index
agreement below covers every CHILD of the runs measured.

## Agreement

`c10-move-h` from the blank tape, with a copy of the `bb/l3c10-farh.sl`
harness that also prints `P`, `gc` and `kr` of each CHILD: the index of
every move from 1 to 69,895 equals that of Rocq's traces (`trQ` to
40,035, then the far notes' trace from 40,035), and the fingerprints
equal those of Rocq's configurations at 1,000, 10,000, 20,000, 22,268,
30,000, 38,513, 40,035, and 42,500 to 67,500 in steps of 2,500; at
89,501 the fingerprint equals that of `far/sr/c89501.txt`, which the far
notes compare with Rocq's certificate configuration there. From
`far/sr/c89501.txt` to 345,355, every index equals that of Rocq's simC10
trace, the fingerprints equal Rocq's at 100,000, 200,000 and 300,000,
and the one at 345,355 equals that of `lin3c3_s0/s0_c66.v`. A run on to
400,000 also agrees on every index, with equal fingerprints at 350,000;
its one CHILD past the counter, at move 345,938 (`P = 7843`, `gc = 3`),
takes about 7.4 s against about 39.5 s for `c10-move-l` (Rocq 137 s).

## Timings

Shared 4-core container, single runs, user time per move from the
harness; "before" is `c10-move-f` (blank tape, the far notes' runs) or
`c10-move-l` (counter, this session).

| stretch | class | instances | before | now |
|---|---|---|---|---|
| 1 to 89,501 | `P = 7827`, `gc = 1` | 2 | 86.9 s | 11.9 s |
| | `P = 1955`, `gc = 3` | 12 | 23.5 s | 3.9 s |
| | `P = 483`, `gc = 3` | 2 | 0.22 s | 0.05 s |
| | `P = 120`, `gc = 2` | 242 | 2.1 s | 0.9 s |
| | all | 258 | 112.7 s | 16.9 s |
| 89,502 to 345,355 | `P = 488`, `gc = 2` | 978 | 124.5 s | 43.4 s |
| | `P = 120`, `gc = 2` | 3,912 | 35.5 s | 16.2 s |
| | all | 4,890 | 160.0 s | 59.6 s |

All CHILD moves from the blank tape to 89,501 come before 58,055. Move
39,807 alone, from a one-configuration input, takes about 5.8 s against
about 41.7 s for `c-child-f`; of those, the climb's 7,825 markers take
about 5 s, about 0.8 ms each, most of it in `zjump`'s walk to the jump
level and `wtail`'s recount of the changed window.

## Goals

`slc` with `--goal proved`, user time:

- `bb/l3c10bound.sl` after the full file list and `bb/l3c10-run.sl`:
  PASS, exit 0, 136.4 s, 0.60 GB peak; with `bb/l3c10-far.sl`,
  `bb/l3c10-train.sl`, `bb/l3c10-trlaw.sl` and `bb/l3c10-chf.sl` added
  before it: PASS, exit 0, 136.8 s, 0.65 GB.
- A copy of `bb/l3c10bound-37981.sl` with `c10-run6` in place of
  `c10-run3`, after the full list and the five files above: PASS,
  exit 0, 3,935 s, 1.74 GB peak (the far notes give about 4,066 s and
  1.8 GB for `c10-run3`, on another day's load).

## What is left

- The climb is O(P) per marker: `zjump` walks the block word to the
  jump level. Rocq's lin3s7 `fastStep_ok` takes the step with O(1)
  big-number operations from the value, `sD` and the bottom pair (the
  digit law `T_rel`, the decrement and borrow laws on base-4 digits of
  `3 rho - D`, the canonicity criterion `critb`); porting it would need
  those laws stated against `PBlk`.
- The head, the walk and the death are still replayed; Rocq takes them
  from lin3d31's lemmas. In a `P = 488` counter instance (about 44 ms)
  the head guards (`gen-head`, `head-chk`) take about 10 ms, the climb
  about 15 ms, the two round blocks about 13 ms, and the replay of the
  walk about 5 ms.
- RESUME1 (24) still reaches CHILD through `fe-cert-f`.
