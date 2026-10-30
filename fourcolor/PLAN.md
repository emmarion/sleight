# Four colour theorem: plan

Written by a Claude session working without the owner. Everything here
is a proposal and an estimate, not a result; the only results are what
compiles.

## The target

`spec.sl` sets the goal `(FourColor)` of `defs.sl`: every straight-line
drawing with natural coordinates, no two edges crossing, has a proper
colouring of its points with colours below 4.

## The intended route

The route follows Gonthier and Werner's Coq proof
(https://github.com/math-comp/fourcolor), with its real-plane front end
replaced by one for straight-line drawings. It is split at
`map.sl`'s `FourColorMap`, a statement about combinatorial maps:

- **A, geometry** (`Drawing` to `PlaneMap`): `FourColorMap` implies
  `FourColor`.
- **B, combinatorics**: `FourColorMap`.

`PlaneMap` builds a loopless map an edge at a time. Each step either
adds an edge with a new endpoint, or joins two corners that lie on one
face or in different components; each such step appears to keep the
Euler genus at 0. It was chosen so that A only has to justify one local
step at a time, and B only needs the easy direction (a `PlaneMap` has
genus 0).

### A: from a drawing to a plane map

1. Orientation algebra. `Left` is a sign of a determinant over `Nat`
   (the shoelace formula with both halves kept positive). The lemmas
   needed (Knuth's CC axioms, from "Axioms and Hulls", and a few about
   collinear points) are polynomial identities and inequalities, so a
   reflective decision procedure for commutative-semiring identities over
   `Nat` would probably pay for itself.
2. Angular order of the edges around a point, as a cyclic order built
   from `Left`, so that each point's edges form one node cycle.
3. The key lemma: in a drawing, a segment that crosses no edge and
   joins two points of one component joins two corners of one face.
   This is a discrete Jordan curve argument. One candidate proof is a
   sweep along the segment that tracks the edge directly above it, as in
   a trapezoidal decomposition; vertical edges and points on the sweep
   line are the expected source of most of the case analysis.
4. Insert the edges in some order, choosing `PMIsolated`, `PMPendant` or
   `PMChord` per edge, and read the colouring back: each point takes the
   colour of a dart of its node cycle, which gives `Proper`.

### B: plane maps are 4-colourable

Following the Coq development, roughly in its file order:

1. Hypermap basics: orbits, connectivity, Euler genus; a `PlaneMap` has
   genus 0; the Jordan property; the dual, which turns vertex colouring
   into face colouring.
2. Minimal counterexample: it can be taken cubic, bridgeless and
   internally 6-connected (`cube.v`, `birkhoff.v`, `kempe.v`).
3. Reducibility: the 633 configurations (`configurations.v`) are
   C-reducible. This is the largest computation; it is done by
   reflection, a checker run under `native-compute` whose result type
   carries the erased proof (`cfmap.v`, `cfcolor.v`, `cfcontract.v`,
   `ctree.v`, `gtree.v`, `kempetree.v`, `cfreducible.v`).
4. Embedding: a configuration found in a minimal counterexample is
   really there, so reducibility contradicts minimality (`embed.v`,
   `redpart.v`, `quiz*.v`).
5. Unavoidability: discharging with the 32 rules (`discharge.v`,
   `part.v`, `hubcap.v`) and the case splits of `present5.v` to
   `present11.v`, which would be carried as data trees checked by a
   verified interpreter rather than as hand-written proofs.

### Part B, module by module

A map `(e, nd)` of `map.sl` appears to be a hypermap in the Coq proof's
sense with edge `e` and face `nd`; `Colored` is then its
`four_colorable` and `PlaneMap`'s looplessness its `bridgeless`, so part
B is its `four_color_hypermap` for the maps `PlaneMap` builds. The Coq
files group into layers by their imports (line counts of the Coq files):

| layer | Coq files | role |
|---|---|---|
| 0 | color 479, chromogram 272, dyck 51, ctree 501, gtree 315, ctreerestrict 388, gtreerestrict 277, initctree 215, initgtree 138 | colour traces and the trees of the reducibility check; no hypermaps |
| 1 | hypermap 483, walkup 646, jordan 333, geometry 813 | hypermaps, genus, the Jordan property |
| 2 | coloring 532, kempe 358, patch 657, sew 255, snip 481, revsnip 538, cube 210, cfmap 1547, cfcolor 697, cfcontract 1029, kempetree 422, cfreducible 114, quiz 494 | colourings, Kempe chains, gluing maps, configurations as maps, the reducibility semantics |
| 3 | birkhoff 677, contract 429, embed 1467, cfquiz 787, quiztree 338, part 1305, discharge 410, hubcap 431, redpart 1283 | minimal counterexamples, embedding configurations, discharging |
| 4 | present 252, present5 .. present11 (16,000 lines of scripts), unavoidability 34, configurations 2129, the job and task files, combinatorial4ct 30 | the data and the final assembly |

In Sleight the computational steps (layer 0, `cfmap`'s construction,
the reducibility and hubcap checks, the presentations) would be
certified functions run under `native-compute`; the rest would be erased
lemmas.

## Scale

The Coq proof directory is about 43,000 lines, written with heavy proof
automation. Sleight proofs are explicit terms, so a port is likely to
be several times longer unless most of the work is moved into verified
checkers. This is a multi-session project; it is not expected to be
finished in one.

## Performance

The BB(5) check, which bb/README.md times at about 36 s on a 12-core
Mac, took 2 min 40 s of wall time (9 min 21 s user) on a 4-core cloud VM
in one run. The reducibility check is expected to be the heaviest step;
`red/` is a prototype of it, written to measure that before any proof
is attached.

## Status

`reduce2.sl` proves `HypReduction`: a function giving every hypermap
of genus 0 that is bridgeless (on `hypermap.sl`'s definitions) a
`FourColoring` gives `FourColor`. So part A is done, and part B is
exactly Gonthier's `four_color_hypermap` on these definitions.
`reduce.sl` is the same with `PlaneMap` and `Colored` in place of the
hypermap notions. Checked by both compilers with

```sh
slc std/macro.sl std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/defs.sl fourcolor/orient.sl fourcolor/base.sl fourcolor/sweep.sl fourcolor/geo.sl fourcolor/plan.sl fourcolor/map.sl fourcolor/lists.sl fourcolor/planemap.sl fourcolor/walk.sl fourcolor/frontier.sl fourcolor/labels.sl fourcolor/rot.sl fourcolor/fan.sl fourcolor/build.sl fourcolor/readback.sl fourcolor/parta.sl fourcolor/reduce.sl fourcolor/hypgraph.sl fourcolor/hypperm.sl fourcolor/hypermap.sl fourcolor/hypplane.sl fourcolor/reduce2.sl --goal proved
```

- `map.sl`: `PlaneMap`, `Colored`, `FourColorMap`. Side conditions are
  positive certificates (labellings), not negations, so that later
  proofs never have to call a function held in data. `map-triangle.sl`
  builds a triangle as a `PlaneMap`, as a check of the definitions.
- `sweep.sl`: `SweepPlan`, the interface between the geometric and the
  combinatorial halves of part A (SWEEP.md).
- `parta.sl`: from a function giving every `Drawing` a `SweepPlan` and
  a function giving every `PlaneMap` a `Colored` colouring, `FourColor`
  follows. Its combinatorial content is in `frontier.sl` (the sweep's
  steps on the frontier), `fan.sl` (one step of the sweep), `build.sl`
  (a whole trace) and `readback.sl`.
- `geo.sl`, `plan.sl`: `drawing-plan`, every `Drawing` has a
  `SweepPlan`; `plan-test.sl` checks it alone.
- `hypgraph.sl`, `hypperm.sl`, `hypermap.sl`, `hypplane.sl`: part B's
  layer 1 begins. `hypgoal.sl` checks `PlaneHypermaps`: each `PlaneMap`
  is a hypermap (face `nd`, edge `e`, node e∘nd⁻¹) of genus 0 in the
  sense of the Euler equation, and bridgeless; `Colored` is equivalent to
  a Gonthier-style four-colouring. Load after `labels.sl`.
- Still open: the rest of part B.
- `ring.sl`, `orient.sl`: a reflective decision procedure for semiring
  identities over `Nat`, and Knuth's CC axioms for `Left` proved with
  it, for the geometry.
- `red/`: an unverified port of the Coq proof's C-reducibility check.
  In one run it accepted all 633 configurations under `native-compute`
  in about 4.5 minutes on a 4-core cloud VM. It carries no proofs yet.
- `unav/`: an unverified port of the unavoidability check (the
  presentations of hub arities 5 to 11, hubcaps, `redpart` through the
  quiz tree, and the bound for larger hubs). In one run every script
  passed, in about 4.4 s of compute; five broken variants of the arity-5
  script were rejected. It carries no proofs yet.
