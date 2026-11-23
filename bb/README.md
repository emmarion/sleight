# Busy Beaver proofs

`bb/` proves busy beaver values in Sleight. [NOTICE.md](NOTICE.md)
credits the earlier proofs these follow.

## Checking BB(5)

The BB(5) proof can be checked against either of two statements:

- `agent/tasks/bb5/spec.sl`, the goal `BusyBeaver 5 47176870` over the
  definitions in `agent/tasks/bb5/defs.sl`. This is the recommended one.
- `bb/bbis5.sl`, the goal `BBIs 5 47176870` over `bb/tm.sl`'s
  definitions.

First build a release slc (see the top-level [README.md](../README.md)
for the dependencies):

```sh
sh self/release.sh
```

Then, from the repository root, the recommended check:

```sh
_build/release/slc std/nat.sl std/list.sl std/macro.sl std/tactics.sl std/immediate.sl agent/tasks/bb5/defs.sl agent/tasks/bb5/spec.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl bb/skelet.sl bb/sk17.sl bb/sk1.sl bb/holes.sl bb/par.sl bb/bb5.sl bb/spec.sl bb/spec5.sl --goal proved --inline 25
```

or the `BBIs` one:

```sh
_build/release/slc std/list.sl std/immediate.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl std/macro.sl bb/skelet.sl bb/sk17.sl bb/sk1.sl bb/holes.sl bb/par.sl bb/bb5.sl bb/champ5.sl bb/bbis5.sl --goal proved --inline 25
```

Each prints `--goal proved: PASS`. Most of the work runs as native code
in parallel jobs, one per core. `--inline 25` is passed on to ocamlopt.
In one set of measurements on a 12-core Mac with OCaml 4.14, higher
levels made the jobs no faster but the compile slower, and lower ones
made the jobs slower. The check took about 36 s there.

## Checking the BB(6) champion's halting time

`bb/champ6.sl` proves that the machine
`1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE`, which the bbchallenge
wiki lists as the BB(6) champion as of November 2025, halts from the
blank tape after s steps with 2↑↑2↑↑2↑↑10 < s < 2↑↑2↑↑2↑↑11. The goal
is `HaltsIn champ6 c0 lo hi`: an erased s with `HaltsAt champ6 c0 s` and
lo < s < hi. Just above it, `lo` and `hi` are bound with proofs
`(Tet3 10 lo)` and `(Tet3 11 hi)`, where `Tet3 n x` says x = 2↑↑2↑↑2↑↑n
through the relation `Tw`, so 2↑↑n is `Tw n 1`. With a release slc,
from the repository root:

```sh
_build/release/slc std/list.sl std/immediate.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl std/macro.sl bb/skelet.sl bb/space.sl bb/champ6.sl --goal proved
```

It prints `--goal proved: PASS`. The run itself follows the counter analysis
on the machine's bbchallenge wiki page: fixed tape rewrites checked by
`sk-family`, and shift and counter-decrement lemmas by induction. The bounds
on s come from the size S of the tape at the halting configuration.
`bb/space.sl` holds the machine-independent half: a step adds at most one
cell, so S < s, and a halting run never repeats a configuration, so
pigeonhole over configuration codes gives s ≤ 2^(2S+19) for a 6-state
machine. `bb/champ6.sl` then bounds S from below and above by towers of 2s,
tracking only the parities and residues mod 3 of the counter values, not
the values themselves.

## A lower bound for the BB(6) holdout L3

`bb/l3bound.sl` proves that the machine
`1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC`, a BB(6) holdout, does not
halt within 10^6000 steps from the blank tape. The goal is
`NoHaltBelow l3 c0 N` with N written out: every k with `HaltsAt l3 c0 k`
has N < k. With a release slc, from the repository root:

```sh
_build/release/slc std/list.sl std/immediate.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl std/macro.sl bb/skelet.sl bb/space.sl bb/sk17.sl bb/rle.sl bb/l3.sl bb/l3tok.sl bb/l3round.sl bb/l3jump.sl bb/l3phi.sl bb/l3dec.sl bb/l3life.sl bb/l3walk.sl bb/l3bound.sl --goal proved
```

It prints `--goal proved: PASS`; in one measurement on a 4-core
container this took about 8 minutes, nearly all of it the compiled run.
`bb/l3bound.sl` replaced by `bb/l3bound2.sl` in the same command proves
10^15568 by the same argument with a longer run; in one measurement this
took about 44 minutes.
The bound counts no steps. A run under `native-compute` reaches a
configuration whose tape, trimmed of trailing blanks, holds more than N
cells, and a step adds at most one cell (`bb/space.sl`), so any halt
comes later (`span-bound` in `bb/rle.sl`).

- `bb/rle.sl`, for any machine: run-length tapes with `Nat` run lengths,
  the invariant `Rch` (a configuration reached from c0 equals the
  tape's denotation up to trailing blanks), single steps, block shifts
  checked by window simulation, and the span argument.
- `bb/l3tok.sl`, `bb/l3round.sl`: L3's register round as relations, and
  its soundness on the machine (cell rules by `sk-family`).
- `bb/l3phi.sl`: the canonical register states phi and their
  conjugacy with one round. `bb/l3jump.sl`, `bb/l3life.sl`: chains of
  rounds on the tape, and the life jump from phi(s) to phi(s-k).
- `bb/l3walk.sl`: sweep and walk macros for rounds that touch other
  tape contents.
- `bb/l3dec.sl` and the token parser propose what a macro should try;
  they carry no proof, and each proposal is checked against the tape.

These follow the Rocq development of the same machine in
busycoq-L3 (`verify/lin3*.v`), whose analysis they port.

## The Skelet #1 runners

Two runners for the Skelet #1 job sit side by side and run the same
lazy-stride algorithm:

- The list runner, `main-run` in `bb/sk1.sl`, keeps the tape in lists.
  The BB(5) checks above use it. [SK1-LAZY.md](SK1-LAZY.md) describes
  its lazy strides.
- The array runner, `main-run-v` in `bb/sk1o.sl`, with `bb/sk1v.sl`,
  `bb/sk1z.sl`, `bb/gvec.sl` and `bb/sk1a.sl`, keeps the tape right of
  the head and the stride's scratch in byte and count vectors.
  [SK1-ARRAY.md](SK1-ARRAY.md) describes it. The BB(5) checks do not use
  it.

`bench/sk1.sh` times either one alone, from the repository root:

```sh
bench/sk1.sh                                                                       # list runner
bench/sk1.sh -x "bb/sk1a.sl bb/sk1z.sl bb/gvec.sl bb/sk1v.sl" -e main-run-v bb/sk1o.sl  # array runner
```

In one set of alternating measurements (8 runs of each, OCaml 4.14,
about 12 s per run on that machine) the two took about the same time.
The array runner allocated about 58% fewer minor-heap words and executed
about 16% more instructions on a 3M-step prefix.
