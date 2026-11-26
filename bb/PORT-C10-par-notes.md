# Notes on checking a span-bound goal in concurrent pieces (`bb/l3c10-par.sl`)

These notes are a session's account of an experiment and its
measurements; they may be wrong in places.

## Files

- `bb/l3c10-par.sl`:
  - `ReachQ m e e2`: some `Conf` `c` decodes `e` and `Rch m c e2`
    holds. `rr-cat` composes an `Rch m c0 e` with it into an
    `Rch m c0 e2` (through `rch-z`). `run-from` runs `c10-run2` from
    `e` with the zero-step `Rch` of `rq-conf`.
  - `SpanAll m e n`: an erased function from every `Rch m blank e` to
    `Span m blank n`. `span-all` is `span-check` with the run-time sums
    done first and the proof part moved into that function, so the
    last piece can produce it without an `Rch` from the blank tape.
  - `NGen` and `QGen`: a configuration generator as data (literal runs,
    `GRep` for a repeated block, `GTrn` for a train of blocks whose one
    varying run follows `v -> a*v + c - s`), in the manner of Rocq's
    `repL` and `trnU`. `GEv`, `RepEv`, `TrnEv`, `AltEv` and `GenQ` are
    its relational meaning, `gev-fn` and `genq-fn` prove it functional,
    and `gev` and `gen-q` compute it with its proof.
  - `RchG m c0 g`, `ReachG m g g2` and `SpanG m g n` are the three
    relations above with each `Rq` named by its generator; `rchg-cat`
    composes. `rg-run n g g2` is a piece: it runs `n` moves from the
    configuration `g` generates and checks with `rq-eq` that it reached
    the one `g2` generates. `rg-span n bnd g` is a last piece.
  - All of it has the types above and uses no axiom.
- `bb/l3c10bound-par.sl`: the 10^15568 goal of `bb/l3c10bound.sl` in
  four pieces: moves 1 to 35,000, 35,001 to 39,806, 39,807, and 39,808
  to 40,035, all in one `native-compute`. `bb/l3c10bound-par2.sl` is
  the same goal in two pieces, split at move 35,000.
- `bb/l3c10-par-gen.py`: reads the checkpoint configurations that
  `bb/l3c10-runh.sl` prints and writes a `QGen` for each, checking that
  it expands back to the configuration.

Build: the full L3 file list, then `bb/l3c10-run.sl`,
`bb/l3c10-par.sl` and one of the two goal files, with `--goal proved`.

## Naming a checkpoint in a type

- A type cannot contain the call `(gen p)`; slc refuses it with
  "cannot be applied in a term, where only a type or value constructor
  can be applied (§9)".
- A run-position `let` of the call is a `Settled` entry, and a type
  may name it. Two pieces that name the same entry have the same type
  there without anything being evaluated, so piece k's end and piece
  k+1's start agree. This worked with `Rq` entries (a scratch version
  of the 10^2309 goal at move 22,268 passed), but `native-compute`
  then embeds each expanded configuration in the compiled program:
  ocamlopt took about 9 minutes and 2.5 GB, and needed
  `ulimit -s unlimited`.
- `bb/l3c10bound-par.sl` instead names `QGen` entries, the generators
  as data, so only the generators are embedded; each piece expands
  them at run time, and `genq-fn` makes two expansions of one
  generator equal for the composition.

## Timings

One shared 4-core container with a load of about 3 from other work;
wall and user times of the whole `slc --goal proved` run, and the wall
time of the `native-compute` processes, from `ps` samples.

| goal | pieces | wall | user | native wall | native CPU per piece |
|---|---|---|---|---|---|
| `bb/l3c10bound.sl` | 1 | 164 s | 159 s | 90 s | 89 s |
| `bb/l3c10bound-par2.sl` | 2 | 147 s | 162 s | 72 s | 20, 71 s |
| `bb/l3c10bound-par.sl` | 4 | 179 s | 209 s | 59 s | 20, 20, 41, 12 s |

- Move 39,807 (CHILD) takes about 42 s alone, so no split by moves
  goes below that.
- The four-piece file holds 280 KB of generators (6.7 KB, 134 KB and
  138 KB for the configurations at moves 35,000, 39,806 and 39,807);
  elaborating them took about 33 s more than the file list alone, and
  the run peaked at about 3.3 GB.
- At move 22,268 (10^2309), the compiled run takes under a second, so
  the single and the four-piece goal took about 83 s and 90 s of wall
  time, nearly all of it elaboration.
