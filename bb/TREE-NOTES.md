# Notes on the cost of the BB(5) tree jobs

These notes are one session's measurements and reading of the code, not
the owner's decisions; the figures are from single runs on one 4-core
cloud container and should be read as approximate (repeat runs moved by
a few percent).

## How the numbers were taken

- The full check (bb/bb5.sl with bb/champ5.sl and bb/bbis5.sl, the file
  list of the task) under `_build/release/slc`, timed with
  `/usr/bin/time`.
- Per job: the generated OCaml of the `native-tree` batch is captured by
  pointing `OCAMLFIND_COMMANDS` at a wrapper that copies `main.ml`, is
  compiled with `ocamlfind ocamlopt -inline 200 -package zarith,unix`, and
  each `main <index>` is run separately, four at a time. Job 0 is the
  Skelet #1 run, jobs 1 to 110 the tree jobs.
- Instruction counts and the per-function split come from
  `valgrind --tool=callgrind` on job 30 (a small job, about 1.5 s), and
  per-decider counts and times from a copy of `main.ml` with counters
  patched into chosen functions. That patching is outside the repository.

## Where the time goes

Summed user time of the 110 tree jobs, and the job 30 instruction count:

| state | tree jobs (core-s) | job 30 (instructions) |
|---|---|---|
| d6f98d8 (start) | 451.5 | 13.76G |
| + filled-split options (below) | 431.6 | 12.44G |
| + cycle hand-off (below) | 406.1 | 11.69G |

The full check went from about 154 s wall / 506 s user to about 139 to
143 s wall / 468 to 480 s user. In a sampled run of 143 s, four native
jobs were alive from about 19 s to about 141 s, so the batch looks well
balanced and wall time appears to follow total core time over four
cores. The largest jobs are job 0 (Skelet #1, about 29 s) and the
subtrees 77 (about 19 s), 62 (16 s), 60 (15 s) and 54 (13 s).

Job 30 at the last state, inclusive shares of its instructions:

- certificate search reached through `stage-try` (`gen-cert`, `search`,
  `process`, `push-sn`, `sym-id`, `sn-edges`, `reg-gram`, `buf-eq`, ...):
  about 36%;
- `nsim`/`nloop` (with `plook` and the edge-candidate `scan`): about 34%,
  about 330 instructions per simulated step, of which about 175 are
  `nloop`'s own (the small helpers it calls are inlined there);
- `check-cert`: about 8%;
- the cycle check's `lsim` (the P steps of the claimed period): about 6%;
- GC about 4 to 6%, and the rest (`build`, `build-all`, `pset`, `seen`,
  `below-of`, `uf-of`, `range`, `opts`) about 12%.

In job 30, 75% of the 5.17M tree nodes at the start were machines whose
last undefined entry had just been given a move (so every transition is
defined and none halts), 15% cyclers caught by `nsim`, 5% halts, 5%
splits, and under 0.5% (23K) reached step 300 and went to certificate
search; each of those costs on the order of 170K instructions there.
Job 77 has 9.4M `nsim` calls and 254K machines at step 300; on it,
search alone is about 40% of the time.

## What the code does now, with measured effect

**Filled-split options** (bb/tree.sl `Opt`, `ag-alt`; bb/search.sl
`Fill`, `fill-of`, `fill-opt`). A `TAll` entry is now an `Opt`: either a
subtree (`OTree`, as before) or, for a move option of a split that fills
the last undefined entry, `OGo`, which carries one sample child's
`AllGo` proof; `ta-pick` turns it into an `AllGo` for the actual child
(`ag-alt`) and refutes halting with `never-full`. `build` checks this
once per split node instead of building a node per child, and `all-go`
runs only at the entry of `build-at`. Effect: 451.5 to 431.6 core-s.

**Cycle hand-off** (bb/search.sl `SnapOk`, `CndsOk`, `SideOk`, `EdgeC`,
`so-set`, `ac-set`, `sok-set`; bb/tnf.sl `check-cyc-at`, `cyc-from`;
bb/cyc.sl `prun-flip`). The snapshot and the edge candidates of `nloop`
carry, as erased predicates over the runtime records, a `PRunTo` proof
of the configuration they record; a split child transports them with
`prun-set`. A cycle `nsim` finds is checked from that configuration, so
the cycle check no longer re-simulates from step 0. A mirrored cycler
gets its run for the flipped machine from `prun-flip`. The hole
certificates still use `check-cyc`, which simulates and then shares
`cyc-from`. Effect: 431.6 to 406.1 core-s.

Both rest on checked proofs: nothing new is trusted, and the theorem in
bb/bb5.sl is unchanged.

## Tried and not kept

- Raising the first stage's limit from 300 to 600, 1000 or 2000 steps:
  jobs 30 and 77 get slower (job 77: 21.2 s at 300, 23.1, 26.7, 36.8 s).
- A larger OCaml minor heap (`OCAMLRUNPARAM=s=1M`, `4M`, `8M`): no gain.
- Emitting non-recursive functions as `let` instead of `let rec` (tried
  by editing the captured OCaml): about 1 to 2%.
- Reordering the eight stage-1 settings or lowering their caps: over
  460K stage-1 machines from jobs 30, 54 and 77, a greedy order over
  each setting at full, half and quarter cap that keeps the same machines
  solved saves about 7% of stage-1 search time, so perhaps 2 to 3%
  overall; the present order looks close to the best of those tried.
- Making `lsim` tail-recursive through the `coerce` idiom of `plook`:
  slightly more instructions.
- A two-pass `list_to_array` in the runtime (self/runtime.ml), tried on
  the captured OCaml: job 30 went from 11.69G to 11.66G instructions,
  although `check-cert`'s calls to it show about 2.9% inclusive; most of
  that cost appears to be in the per-element list view, not the copy.

## What might be the next large wins

These are guesses from the profile above, not measured.

1. Certificate search per configuration: `process` and what it calls do
   most of the work, and every success also builds a list-based `Cert`
   (`all-rows`, `cfgs-of`, `bits-of`) that `check-cert` turns back into
   arrays and re-checks. Building the checker's arrays directly, or a
   cheaper inner loop in `process`, might remove a good part of the 40%
   seen on the large jobs.
2. `nloop`'s per-step cost: most of its own instructions appear to be
   tagged `Nat` arithmetic (step, position, fuel, the two `ext` and
   `at-end` updates, `snap-at`). Keeping the counters as `U62`, looking
   transitions up in an array instead of walking `p` with `plook`, and
   indexing the edge candidates by state and symbol so `scan` stops
   walking every candidate, might each be worth several percent.
3. Per-split work in `build` (`seen`, `below-of`, `uf-of`, `range`,
   `opts`) depends only on which entries of `p` are defined and could
   perhaps be carried down from the parent.
