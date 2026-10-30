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

`reduce3.sl` proves `CubicReduction`: a function giving every plain
cubic hypermap of genus 0 that is bridgeless (on `hypermap.sl` and
`hypgeom.sl`'s definitions) a `FourColoring` gives `FourColor`. So part
A and the cube reduction of part B are done; what is open is Gonthier's
theorem for plain cubic maps. `reduce.sl` and `reduce2.sl` are the
intermediate forms (with `PlaneMap`, and with all bridgeless hypermaps);
`reduce2-goal.sl` and `cube-goal.sl` check them alone. Checked by both
compilers with

```sh
slc std/macro.sl std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/defs.sl fourcolor/orient.sl fourcolor/base.sl fourcolor/sweep.sl fourcolor/geo.sl fourcolor/plan.sl fourcolor/map.sl fourcolor/lists.sl fourcolor/planemap.sl fourcolor/walk.sl fourcolor/frontier.sl fourcolor/labels.sl fourcolor/rot.sl fourcolor/fan.sl fourcolor/build.sl fourcolor/readback.sl fourcolor/parta.sl fourcolor/reduce.sl fourcolor/hypgraph.sl fourcolor/hypperm.sl fourcolor/hypermap.sl fourcolor/hypplane.sl fourcolor/reduce2.sl fourcolor/hypeuler.sl fourcolor/hypderived.sl fourcolor/hyprelabel.sl fourcolor/hypwalkup.sl fourcolor/hypgeom.sl fourcolor/cube.sl fourcolor/cubegoal.sl fourcolor/reduce3.sl --goal proved
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
- `hypeuler.sl`, `hypderived.sl`, `hyprelabel.sl`, `hypwalkup.sl`,
  `hypgeom.sl` (load in that order after `hypplane.sl`):
  `hypwalkgoal.sl` checks that every hypermap has a unique genus, that
  the dual and the mirror keep it, and that WalkupE does not raise it.
  The genus is reached by building the face permutation from the
  identity one transposition at a time, not by Walkup induction. Also
  there: permN and permF, renaming darts (`genus-relabel`), WalkupN and
  WalkupF, and as definitions only, the Jordan property and the special
  maps and face paths of `geometry.v`.
- `cube.sl`, `cubegoal.sl` (load after `hypgeom.sl`): the cube
  construction of `cube.v`, its darts laid out as six blocks of d.
  `cubegoal.sl` checks `CubeReduction`: a function four-colouring every
  planar bridgeless plain cubic hypermap gives one four-colouring every
  planar bridgeless hypermap, so with `reduce2.sl` part B appears to
  come down to plain cubic maps.
- `coloring.sl`, `colorgoal.sl` (load after `cube.sl`): from
  `coloring.v`, `colorable_bridgeless`, the colourings of the dual and
  the mirror, and `decide_colorable`, a search over the colours of each
  dart in turn whose failure is an erased function from any
  four-colouring to `False`.
- `hypjordan.sl`, `hyptree.sl`, `hypwalkeq.sl`, `hypcount.sl`,
  `hypcubic.sl`: planar maps have no Moebius path (`planar-moebius`, an
  absurd function later proofs can call directly, in place of applying
  `Jordan`), Euler_tree for genus 0, the equality case of the walkup
  genus, same_cskip_edge, and cubic_Euler; `hypjordangoal.sl` and
  `hypcubicgoal.sl` check them. Jordan implies planar is not proved.
- `cfmap.sl`, `cpmap.sl`, `cfcolor.sl`, `cpcolor.sl` (load after
  `hypgeom.sl`, interleaved with `red/` files as below): configuration
  maps built from their programs by a certified function, with ring
  traces `CpCol`; `cpcolor-c` gives the soundness half of
  ctree_mem_cpcolor, and `ctring-allp` hands its traces, rotated by one
  (`CpColR`), to the certified Kempe tree. `cfmap-run.sl` and
  `cpcolor-run.sl` ran all 633 configurations once, matching `red.sl`'s
  ring sizes and trees. The A step of the programs, planarity of
  configuration maps and the completeness direction of `cpcolor-c` are
  not done; completeness for contract colourings is in `red/ccomp.sl`.
- `colalias.sl`, `ringtrace.sl`, `kempemap.sl`, `kempegoal.sl` (load
  `colalias.sl` after `coloring.sl`, then `red/red.sl`, `red/color.sl`,
  `red/ctree.sl`, `red/gtree.sl`, `red/grestrict.sl`,
  `red/crestrict.sl`, `red/kempe.sl`, `red/bridge.sl`, `red/gramrot.sl`,
  then the other three; they also check after the whole chain of the `red/` entry
  below, `red/cfred.sl` included): ring traces of four-colourings
  (`RingTrace`, on `red/`'s colours), contract colourings and
  `MinimalCounterExample` after `coloring.v` (indexed by the levels of its
  two functions, so that a level factory can call them), and `kempe.v`.
  `kempegoal.sl` checks `KempeMap`: for a duplicate-free node cycle r of
  a genus-0 hypermap whose edges have two darts and which has
  n (n (n x)) = x off r, ring traces are closed under colour
  permutations, each matches a chromogram with a certificate (`KRing`)
  that every trace matching it is a ring trace, so the ring traces are
  a `KClosed` set of `red/bridge.sl` (`kempe-closed`), and a ring trace
  in the co-closure `KCC` of a set Q leads to a ring trace in Q
  (`kcc-kempe`). The induction uses dart-preserving Walkup transforms,
  the darts taken out kept as dead darts that colourings ignore.
- `hypsub.sl` (load after `colalias.sl`, before `red/red.sl`): lists of
  darts as sets, and `ClassesOn g xs k`, the classes of a graph counted
  among the darts of a list; `co-map` moves such a count along a pair of
  dart maps, after `adjunction_n_comp`.
- `patch.sl` (load after `kempemap.sl`): part of a port of `patch.v`.
  `Patch` glues a disk map and a remainder map, each a hypermap on its own
  darts, sent into the whole map by injections listed by their images.
  Proved, as far as slc checks them: card_patch, plain_patch and
  cubic_patch (for any order c), patch_face_r (both directions),
  patch_face_d', cFhd, patch_bridgeless, the orbit counts of edges, nodes,
  faces and glink (`edge-patch`, `node-patch`, `face-patch`,
  `glink-patch`), genus_patch and planar_patch, the colourings of the
  two parts that a colouring of the whole map gives (`patch-coloring`),
  and colorable_patch in both directions (`colorable-patch` and
  `patch-colorable`, with `RotRev` for rot 1 (rev et) and `trace-rev`
  for trace_rev).
  The rest of `patch.v` is in `patch2.sl`.
- `patch2.sl` (load after `patch.sl`; it does not need `sew.sl`): the rest
  of `patch.v`, as far as slc checks it. outer_hd in both directions
  (`outer-hd-in`, `outer-hd-out`), with `band-dec` deciding between `Fband`
  and `Kernel`; patch_face_d (`patch-face-d-pull`, with the hypothesis that
  the face of the disk dart misses bd, which outer_hd appears to make
  equivalent to Coq's); bridgeless_patch read constructively
  (`bridgeless-patch`: with both parts bridgeless, the whole map is
  bridgeless or bd has a `Chord`, a positive witness meant to stand for
  ~~ chordless bd, stated for an edge cycle with next r x read as e x);
  patch_connected_r; patch_fcard_face_r, with outer given as a `BandSplit`
  of the darts by whether their face meets the image of hr; patch_gcomp
  (`patch-gcomp`, the parts renumbered by position, through `sub-perm` and
  `sub-map`, which restrict a hypermap to a set of darts shut under its
  permutations); and minimal_counter_example_is_connected, as `gcomp-split`
  (a planar bridgeless plain precubic map with a dart is connected or
  patched along empty rings from two smaller such maps) and the level
  factory `mce-connected`, which calls the two functions of a
  `MinimalCounterExample`. Whether `Chord` matches Coq's chordless has been
  checked only by reading.
- `sew.sl` (load after `patch.sl`): sew_map and sew_map_patch of `sew.v`
  as one existence statement, `sew-exists`: a disk map with a simple edge
  cycle bd and a remainder map with a duplicate-free node cycle br of the
  same length, both lists of their own darts, are patched into a map
  whose darts are the disk darts followed by the remainder darts off br,
  numbered in order, with br sent to rev bd. Its edge and node
  permutations are glued from those of the two maps (`cmap-perm`).
  `snip.v` and `revsnip.v` are not started.
- Still open: the rest of part B. Besides `snip.v` and `revsnip.v`,
  `birkhoff.v` appears to need, from a reading of its proofs:
  Kempe_valid_init, Kempe_valid_restrict, Kempe_validP and
  Kempe_tree_closure_correct of `kempetree.v` (whether `red/kempe.sl`'s
  soundness-only `KV` covers them as `birkhoff.v` uses them is not
  checked); ctree_of_ttail and ctree_of_ttail_mem of `ctree.v`; the
  completeness direction of ctree_mem_cpcolor; cpmap_proper, cpmap_planar
  and cpmap_bridgeless of `cfmap.v`; decide_ring_trace of `coloring.v`;
  quasicubic_Euler, srcycleI and scycle_cface of `geometry.v`; and the
  Birkhoff_check computation itself, which Coq runs by vm_compute. None of
  these is ported.
- `ring.sl`, `orient.sl`: a reflective decision procedure for semiring
  identities over `Nat`, and Knuth's CC axioms for `Left` proved with
  it, for the geometry.
- `red/`: an unverified port of the Coq proof's C-reducibility check.
  In one run it accepted all 633 configurations under `native-compute`
  in about 4.5 minutes on a 4-core cloud VM. It carries no proofs yet.
- `red/color.sl` .. `red/cfred.sl`: a certified Kempe tree and
  `ctree_disjoint` (soundness direction only), over a co-closure stated on
  partial traces whose completions satisfy a predicate held as data
  (`PredC`, one parameter of any type). `red/init.sl` builds the initial
  trees together with their certificates. `red/bridge.sl` takes that
  co-closure to one on complete traces stated after `chromogram.v`
  (`KCC`), and `KCC` to `Kempe_coclosure` for every set closed by
  functions at a given level (`kcc-coclosure`, a level factory).
  `red/check.sl`'s `kempe-tree-chk` builds the Kempe tree of the ring
  traces from `cpcolor-c` with its soundness evidence. `red/gramrot.sl`
  ports gram_rot and both directions of match_gram_rot of `kempe.v`.
  `red/cfred.sl` states C_reducible of `coloring.v` on the configuration
  maps (`CRed`) and proves check_reducible_valid from a Kempe half
  (`KHalf`) and a contract half (`ContractOK`), both stated against the
  Kempe tree rather than a contract tree. The contract half does not go
  through cfctr: `red/ccomp.sl` computes, for programs of R, Y and H
  steps, a list holding the ring trace of every contract colouring (its
  completeness is `lrel-hit` and `cccol-hit`), and checks that the even
  normal form of each, without its first entry, has multiplicity zero in
  the Kempe tree (`contract-ok`). `red/ccheck.sl` defines the contract
  of a configuration on these dart numbers (`CfContract`, after
  cfcontract and ctrenum of `cfcontract.v`; written for this numbering,
  not checked against Coq's), decides `ValidContract` on the concrete map
  (`valid-c`), and puts the pieces together (`red-c`, `Reducible`).
  `red/goal-c.sl` sets and proves the goal `AllRedC` on the chunks of
  `red/configs.sl`: every configuration appears to be C-reducible, in the
  sense of `CRed`, with its contract. Load order: `std/nat.sl
  std/list.sl`, then `base map lists planemap walk frontier labels
  hypgraph hypperm hypermap hypplane hypeuler hypderived hyprelabel
  hypwalkup hypgeom` (each `.sl`), then `cfmap.sl red/red.sl cpmap.sl
  red/color.sl cfcolor.sl red/ctree.sl red/gtree.sl red/grestrict.sl
  red/crestrict.sl red/kempe.sl cpcolor.sl red/configs.sl red/bridge.sl
  red/init.sl red/check.sl red/gramrot.sl red/cfred.sl red/ccomp.sl
  red/ccheck.sl`, then `red/sanity-c.sl` or `red/goal-c.sl` (with
  `--goal proved`). `red/goal-c.sl`
  proved its goal in about 7.4 and 9 minutes of wall time (15.5 of user time)
  in two runs on a 4-core cloud VM. What `CRed` and `ValidContract` state has not
  been checked against Coq's C_reducible and valid_contract beyond
  reading them.
- `unav/`: an unverified port of the unavoidability check (the
  presentations of hub arities 5 to 11, hubcaps, `redpart` through the
  quiz tree, and the bound for larger hubs). In one run every script
  passed, in about 4.4 s of compute; five broken variants of the arity-5
  script were rejected. It carries no proofs yet.

- `unav/fit.sl`, `dbound.sl`, `hubcapc.sl`, `faces.sl`, `obsmap.sl`,
  `dscore.sl`, `runc.sl`: the part operations, dbound checks and hubcap
  check certified down to a statement about the arities around a hub;
  `runc.sl` reran every presentation through them once.
- `unav/posz.sl`, `pwalk.sl`, `hubsound.sl`, `pwsound.sl`, `conv.sl`,
  `cap.sl`, `unav.sl`, `unavgoal.sl`: these appear to link the checks to
  `dscore` on hypermaps. `unavgoal.sl` sets the goal `Unav`: the
  certified walks of arities 5 to 11 and the cap checks succeed for the
  rules of `data.sl`, some dart of a plain cubic connected pentagonal
  map of genus 0 has positive dscore, and each such dart has an
  obligation of its arity's walk (or a cap obligation, from arity 12)
  fitting exactly at some dart. One compiled run does the checks and
  asks `redpart` of every obligation (about 335,000); in one run
  `--goal proved` passed in about a minute. That `redpart` holds of the
  lists in `Unav` rests on that run, not on the type, and `redpart`
  and the quiz tree are unverified.