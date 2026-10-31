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
`hypgeom.sl`'s definitions) a `FourColoring` gives `FourColor`.
`inductfc.sl` proves `FourColorFrom` (`inductgoal.sl` checks it): an `Analysis` (`induct.sl`) gives
`FourColor`. `fcgoal.sl` proves `FourColor` from the four computed
steps of part B, taken as arguments, and `fcfinal.sl` proves `FourColor`
itself, with no hypotheses, in one unit with the runs that compute those
steps (their entries below). That proof relies on the evaluator and on
the compiled `native-compute` runs being correct (DESIGN.md §29, §72),
uses no axiom of its own, and has been checked against Coq's statements
only by reading. `fcmanyfinal.sl` proves `fcmany.sl`'s `FourColorM`, the
theorem as a program, in a unit with the same runs: `paint.sl`'s search
computes the colouring from the coordinates, and the erased proof of
`FourColor` refutes its failure. `reduce.sl` and `reduce2.sl` are the
intermediate forms (with `PlaneMap`, and with all bridgeless hypermaps);
`reduce2-goal.sl`, `cube-goal.sl` and `reduce3-goal.sl` check them alone.
Checked by both compilers with

```sh
slc std/macro.sl std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/defs.sl fourcolor/orient.sl fourcolor/base.sl fourcolor/sweep.sl fourcolor/geo.sl fourcolor/plan.sl fourcolor/map.sl fourcolor/lists.sl fourcolor/planemap.sl fourcolor/walk.sl fourcolor/frontier.sl fourcolor/labels.sl fourcolor/rot.sl fourcolor/fan.sl fourcolor/build.sl fourcolor/readback.sl fourcolor/parta.sl fourcolor/reduce.sl fourcolor/hypgraph.sl fourcolor/hypperm.sl fourcolor/hypermap.sl fourcolor/hypplane.sl fourcolor/reduce2.sl fourcolor/hypeuler.sl fourcolor/hypderived.sl fourcolor/hyprelabel.sl fourcolor/hypwalkup.sl fourcolor/hypgeom.sl fourcolor/cube.sl fourcolor/cubegoal.sl fourcolor/reduce3.sl fourcolor/reduce3-goal.sl --goal proved
```

and `FourColorFrom` with `fourcolor/coloring.sl` loaded after
`fourcolor/cubegoal.sl`, and `fourcolor/induct.sl fourcolor/inductfc.sl fourcolor/inductgoal.sl`
in place of `fourcolor/reduce3-goal.sl` (a few seconds each).

- `induct.sl`, `inductfc.sl`, `inductgoal.sl` (load `induct.sl` after `coloring.sl`):
  four_color_hypermap's induction on the number of darts, with the
  minimality of a counterexample entering as data rather than as a
  function, since a function stored in a counterexample would have to
  call the induction, and the induction the lemmas' functions, minted at
  higher levels (§17). `Reduces B` says that a map reduces to a list of
  maps (`Mp`), each planar, bridgeless, plain, precubic (`Pbpp`) and
  smaller (`Smaller`), with a `ColorFrom B`: a witness of a type the
  reduction chooses and a glue function, at any level with a `Predates`
  to the bound B, turning four-colourings of the list (`MpCols`) into one
  of the map. An `Analysis` is a function, at any level, giving every
  `Pbpp` map with a search certificate of no four-colouring
  (`NoColoring`, after `NoExt`; `color-dec` decides it) a `Reduces B`, for
  a bound B it fixes. `four-color-induct` builds from it a function
  four-colouring every `Pbpp` map: `col-all` colours a list of maps below
  a bound, each by the search or by the glue of its reduction from the
  colourings of its list below a smaller bound, calling only functions
  minted before it. `inductfc.sl` proves `FourColorFrom`
  (`four-color-from`, `Analysis` to `FourColor`, through `CubicReduction`),
  and `inductgoal.sl` sets it as a goal.
  `reduces-lift` raises the bound of a reduction.
 `PlaneMap`, `Colored`, `FourColorMap`. Side conditions are
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
  dart in turn whose failure is a certificate (`NoExt`), which
  `noext-sound` turns into a refutation of any four-colouring. The search also fixes the colours of a list
  of darts (`search-ring`); `decide_colorable` is its case with no darts.
- `hypjordan.sl`, `hyptree.sl`, `hypwalkeq.sl`, `hypcount.sl`,
  `hypcubic.sl`: planar maps have no Moebius path (`planar-moebius`, an
  absurd function later proofs can call directly, in place of applying
  `Jordan`), Euler_tree for genus 0, the equality case of the walkup
  genus, same_cskip_edge, and cubic_Euler; `hypjordangoal.sl` and
  `hypcubicgoal.sl` check them. Jordan implies planar is not proved.
  `hypcount.sl`'s `orbit-sum`: the orders of a permutation at the roots
  of its classes sum to the number of darts; `orbit-count` is its case
  with every order equal.
- `cfmap.sl`, `cpmap.sl`, `cfcolor.sl`, `cpcolor.sl` (load after
  `hypgeom.sl`, interleaved with `red/` files as below): configuration
  maps built from their programs by a certified function, with ring
  traces `CpCol`; `cpcolor-c` gives the soundness half of
  ctree_mem_cpcolor, and `ctring-allp` hands its traces, rotated by one
  (`CpColR`), to the certified Kempe tree. `cfmap-run.sl` and
  `cpcolor-run.sl` ran all 633 configurations once, matching `red.sl`'s
  ring sizes and trees. `cpcolor-c` also returns how it built its tree
  (`CpComp`, `CpCov0`, `CpCov`), which `cpcomp.sl` reads for the
  completeness half. The A step of the programs and planarity of
  configuration maps are not done; completeness for contract colourings
  is in `red/ccomp.sl`.
- `cpcomp.sl` (load after `red/bcheck.sl`): the completeness half of
  ctree_mem_cpcolor, for cubic programs, as far as both compilers check
  it. `cpcolor-mem`: for a ring trace e0 :: et of a colouring of the map
  of a cubic program with et even, et is in the tree of `cpcolor-c`;
  `cpcolor-etrace` gives the same for the even normal form of any ring
  trace without its first entry, and `bkprog-hit` for a basis program of
  the Birkhoff check (the use in chkbP of Birkhoff_valid). The proof
  goes in two parts. `steps-hit`, on the contract-colouring context of
  `red/ccomp.sl` with no contract darts, reads a colouring of the whole
  map as a run of the steps on ring traces (`StepTr`, `StepsTr`) from
  the trace c c of the first map; `cov-mem`, `cov0-mem` and `comp-mem`
  show that every trace such a run reaches has its normal form in the
  tree, using that runs commute with colour permutations (`steps-perm`)
  for the steps that `cpcolor0-c` normalises. Whether `CpCol` with
  `EvenT` matches Coq's even_trace and ring_trace has been checked only
  by reading.
- `colalias.sl`, `ringtrace.sl`, `kempemap.sl`, `kempegoal.sl` (load
  `colalias.sl` after `coloring.sl`, then `red/red.sl`, `red/color.sl`,
  `red/ctree.sl`, `red/gtree.sl`, `red/grestrict.sl`,
  `red/crestrict.sl`, `red/kempe.sl`, `red/bridge.sl`, `red/gramrot.sl`,
  then the other three; they also check after the whole chain of the `red/` entry
  below, `red/cfred.sl` included): ring traces of four-colourings
  (`RingTrace`, on `red/`'s colours), contract colourings after
  `coloring.v`, and `kempe.v`.
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
  permutations); and minimal_counter_example_is_connected without the
  minimality, as `gcomp-split` (a planar bridgeless plain precubic map
  with a dart is connected or patched along empty rings from two smaller
  such maps). Whether `Chord` matches Coq's chordless has been
  checked only by reading.
- `split.sl` (load after `patch2.sl` and `induct.sl`):
  minimal_counter_example_is_connected with minimality as data:
  `split-reduces`, for any bound above `split-glue`, gives a planar
  bridgeless plain precubic map with a dart a `Connected`, or a `Reduces`
  to the two parts of `gcomp-split`, glued by `patch-colorable-nil`.
- `sew.sl` (load after `patch.sl`): sew_map and sew_map_patch of `sew.v`
  as one existence statement, `sew-exists`: a disk map with a simple edge
  cycle bd and a remainder map with a duplicate-free node cycle br of the
  same length, both lists of their own darts, are patched into a map
  whose darts are the disk darts followed by the remainder darts off br,
  numbered in order, with br sent to rev bd. Its edge and node
  permutations are glued from those of the two maps (`cmap-perm`).
- `snip.sl` (load after `sew.sl`): part of a port of `snip.v`. `Ring e f x p`
  is a ring x :: p, a cycle of rlink on distinct faces, here not empty;
  `DiskN` is diskN, reached by dlink paths (`DPath`), and `DiskF` is diskF.
  Proved, as far as slc and the reference compiler check them: diskN_node
  both ways (`disk-node`, `disk-pre`), r in diskN (`disk-ring`), diskE_edge
  for a planar map both ways (`disk-edge`, through a Moebius path and
  `planar-moebius`, and `disk-edge-inv`), diskF_face both ways
  (`diskf-face`, `diskf-face-inv`), and snip_disk, snip_rem and snip_patch
  as one existence statement, `snip-exists`: a planar map is patched from a
  disk map on the darts hd of diskN, numbered in order, with its ring bd
  sent to r (map_snipd_ring; scycle_snipd_ring and simple_snipd_ring are
  part of the patch), and a remainder map on rev r followed by the darts zs
  off diskN (codom_snipr), with its ring br sent to rev r (map_snipr_ring,
  ucycle_snipr_ring). `ds-in`, `ds-mem` and `ds-out` relate hd and zs to
  `DiskN` (codom_snipd); hd is found from the classes of a graph whose
  classes meeting r appear to make up diskN (`DiskGraph`).
  `patch-parts-planar` gives planar_snipd and planar_snipr for any patch of
  a planar map. cface_snipd, diskFC_face and the rotation lemmas of SnipRot
  are in `revsnip2.sl`. Not done: the empty ring. `snip.sl` ends by naming
  `coloring.sl`'s `Proper` `KProper`, since `revsnip.sl` shadows it.
- `revsnip.sl` (load after `snip.sl`): the start of a port of `revsnip.v`,
  for plain maps (every edge orbit of size 2). Proved, as far as both
  compilers check them: scycle_rev_ring (`rev-ring`: rev (map e r) is a
  ring), mem_rev_ring (`rev-ring-in`, `ring-rev-in`), proper_rev_ring
  (`proper-rev`, with `Proper` for proper_ring), diskN_edge_ring
  (`disk-edge-ring`), connected_clink (`connected-clink`), and
  diskN_rev_ring for a connected map (`rev-disk`: with `rev-ctx` building
  the two rings and their disks, each dart is in exactly one of the two
  diskN, `Two`). More of `revsnip.v` is in `revsnip2.sl`.
- `revsnip2.sl` (load after `revsnip.sl`): more of `revsnip.v`, as far as
  both compilers check it. fband_rev_ring and its kernel form (`rev-subs`:
  RR and r each lie on the faces of the other, `FaceSub`, used through
  `fband-sub`, `kernel-sub` and `scattered-sub`); nontrivial_ring as
  `NonTrivial` (m + 1 darts of diskF r and m + 1 darts of diskFC r, each on
  distinct faces, `Scattered`, with diskN r and the darts off it given by a
  `DiskSplit`; that this matches Coq's fcard has been checked only by
  reading); nontrivial_ring_proper (`nontrivial-proper`) and
  nontrivial_rev_ring (`nontrivial-rev`, which uses `rev-disk` and
  `rev-subs` where Coq uses diskF_rev_ring, not stated on its own here).
  From `snip.v`: cface_snipd in both directions (`snipd-push` and
  `snipd-face-inv`, for a patch whose disk ring is sent to a ring r, as
  `snip-exists` gives), diskFC_face (`diskfc-face`, `diskfc-face-inv`, with
  diskFC r read as the darts of a `DiskSplit`'s off-part on no face of r),
  and diskN_rot and fband_rot (`disk-move`, `fband-move`, for any two lists
  with the same darts). rev_ring_cotrace in both directions, between the
  disk map of r and the remainder map of RR = rev (map e r), each given by
  `snip-exists`, with `rev-ctx`'s `RevCtx`: `cotrace` takes a ring trace et
  of the disk ring to the ring trace rot 1 et of the remainder ring (Coq
  states it on rotr 1 of that ring instead), through `Ext`, a colouring of
  the disk map extended to the whole map by faces, and `cotrace-back` goes
  back, through `Pull`. colorable_from_ring (`colorable-from-ring`).
  More of `revsnip.v` is in `revsnip3.sl`.
- `revsnip3.sl` (load after `revsnip2.sl` and `geomring.sl`): the rest of `revsnip.v` that
  `birkhoff.v` appears to use, as far as both compilers check it.
  nontrivial0P in both directions (`nontrivial-pick`, which also gives a
  dart of diskF r and one of diskFC r for any m, and `nontrivial0`).
  ring_disk_closed (`ring-disk-closed`, given cubic G): the ring traces of
  the disk map of r form a red/bridge.sl `KClosed` set, by functions at a
  level L the caller gives with a proof that `RDC` predates it. It goes through the remainder map of RR, whose ring
  br2 = init ++ [l] is read as l :: init (`ring-turn` of `kempemap.sl`), so
  that `kempe-map` applies to the traces `cotrace` rotates, with `rt-rot`
  and `rt-unrot` moving a ring trace across that rotation and `snoc-inj`
  (`hypgraph.sl`) matching the two rotations; quasicubic is read off
  node-order-patch (`oo-qcubic`). The chord rings: `Chords` holds r read
  from x1 as x1 :: A ++ x2 :: B (`ring-from`), with a dart z of diskN r
  off r on the face of x1 whose edge image is on the face of x2; it is
  symmetric (`chords-swap`). `chord-ring` and `chord-proper` give
  scycle_chord_ring and proper_chord_ring; diskN_chord_ring is read as
  `Three` (each dart is in diskN r and in exactly one of the diskN of the
  two chord rings, or in none of the three), proved along a clink path to
  z (`three-all`); `chord-split` gives the use of diskF_chord_ring that
  ring_disk_chord makes, and `chord-side` nontrivial_chord_ring, with
  x2 != next r x1 read as A non-empty. ring_disk_chord (`ring-disk-chord`)
  takes a `Chord` of the disk ring, as `bridgeless-patch` gives it, and
  returns a ring nontrivial for 0 with fewer darts. That these statements
  match Coq's has been checked only by reading. The empty ring of `snip.v`
  is not ported; from a reading of `birkhoff.v` it appears to be needed
  only where Coq's nontrivial_ring of an empty ring is false, which a
  `Ring` here, never empty, does not need.
- `ringdec.sl` (load after `ringtrace.sl`): decide_ring_trace of
  `coloring.v` (`decide-ring-trace`): a list of colours is a ring trace of
  a list of darts, or a certificate (`RTNo`) says that none is, which
  `rtno-sound` turns into a refutation of any ring trace at its own fixed
  level. It runs `search-ring` once for each first colour.
- `geomring.sl` (load after `patch.sl`): simple_cface of `geometry.v`,
  from which scycle_cface follows (`simple-cface`), and quasicubic_Euler
  (`quasicubic-euler`): in a connected map whose edges have two darts,
  with a duplicate-free node cycle R (`NCyc`) of m + 1 darts off which
  every dart has node order 3 (`OrdersOff`), and with kf faces,
  6 kf + 12 genus = d + 2 (m + 1) + 6; `quasicubic-planar` and
  `planar-quasicubic` are its two directions for genus 0. The node count
  behind it is `ring-count` (1 + i node orbits and d = m + 1 + 3 i, from
  `orbit-sum`). Stated for a non-empty R only; Coq's lemma also covers
  the empty ring.
- `srcycle.sl` (load after `snip.sl`): srcycleI of `geometry.v`, from
  srcycle to scycle rlink only (`srcycle-ring`): in a bridgeless map an
  srcycle, stated as `SRPath` with the darts that srpath keeps off a
  face told apart by face labellings (`FaceApart`), is a `Ring`.
- `cpgeom.sl` (load after `revsnip3.sl`, in its chain with `cfmap.sl`
  loaded after `hypcubic.sl` and `cpmap.sl` after `red/red.sl`; `cpmap.sl`
  ends with aliases for the names of `cfmap.sl` that `kempemap.sl` and
  `snip.sl` define again): cpmap_connected, cpmap_bridgeless and
  cpmap_planar of `cfmap.v`, as far as both compilers check them, as one
  statement, `cpmap-geom`: the map of a cubic program, with the node
  permutation of any `PointedMap` of it, is connected, bridgeless and of
  genus 0. With it, cycle_rev_cpring and ucycle_rev_cpring (`ring-cycle`:
  rev r is an `NCyc` without repeats), and the facts quasicubic_Euler takes
  of such a map, with quasicubic read as `geomring.sl`'s `OrdersOff` on rev r
  (`cpmap-qgeo`, a `QGeo`). The recursion carries Euler's equation in the
  form 6 kf = d + 2 k + 6 (`QEuler`, k the ring size) through each U and N
  step (`geo-u`, `geo-n`, `geo-y`, `geo-h`) and reads the genus off it once,
  at the end, where Coq applies quasicubic_Euler at every step. The H step
  uses a ring of at least two darts (`cprsize-proper`, through
  `ring-fixed`), as Coq's bridgeless_ecpH does. That these statements match
  Coq's has been checked only by reading. Load order: `std/nat.sl
  std/list.sl ring.sl`, then `base map lists planemap walk frontier labels
  hypgraph hypperm hypermap hypplane hypeuler hypderived hyprelabel
  hypwalkup hypgeom hypjordan hyptree hypwalkeq hypcount hypcubic cfmap cube
  coloring colalias hypsub`, `red/red.sl cpmap.sl`, `red/` `color ctree gtree
  grestrict crestrict kempe bridge gramrot`, then `ringtrace kempemap patch
  sew patch2 snip revsnip revsnip2 srcycle ringdec geomring revsnip3
  cpgeom` (each `.sl`).
- `embed.sl`, `embedgoal.sl` (load after `unav/unave.sl`, in the
  chain below): present.v's use of unavoidability and reducibility,
  with minimality as data, as far as both compilers check it.
  `embed-analysis` gives an `Analysis`, for any level X, from `UnavE cfs`, `AllRedC X css`
  with `ConcatL css cfs` (css concatenated; `concat-c` computes it with
  its evidence), and two open steps taken as hypotheses, each a function
  at a level and a bound of its own: `BirkGeo`, birkhoff.v's
  minimal_counter_example_is_plain_cubic_pentagonal (a connected `Pbpp`
  map with a `NoColoring` is a `Geo` or has a `Reduces`; its cubic part
  is coloring.v's minimal_counter_example_is_cubic, which `birkhoff3.sl`
  proves; `birkhoff3.sl` reduces `BirkGeo` to `MinArity`, and
  `minarity.sl` gives `BirkGeo` from `BirkhoffChecks`),
  and `NotEmbed X cfs`, embed.v's not_embed_reducible for the
  configurations of cfs (such a map that is a `Geo`, with a configuration
  of cfs whose kernel preembeds in the terms `CfEmbed` uses, `CRed X` for
  C_reducible, has a `Reduces`); it leaves open embed.v (`embed2.sl`
  and `contract.sl` have pieces of it), contract.v's contract_coloring,
  which embed.v uses (`contract.sl` has its colouring half), and Coq's
  embeddable for the configuration maps. The analysis colours a map with
  no dart, splits a disconnected one (`split-reduces`), and otherwise
  follows `BirkGeo`, then `UnavE` and `NotEmbed`, on the map or its
  mirror. Proved: minimal_counter_example_mirror in this form
  (`pbpp-mirror`, `nocol-mirror`, and `reduces-mirror`, a level factory
  that turns a reduction of the mirror that `MapOrMirror` names into one
  of the map, through `perm-unique` and `unav/qmirror.sl`'s
  `plain-mirror`), `allred-concat` and `reducible-mem`. `embedgoal.sl`
  sets `embed-analysis`'s type as a goal. The chain, both compilers
  (with `--goal proved`, about 1 and 2 minutes in one run each):
  `std/macro.sl std/nat.sl std/list.sl ring.sl`, `base` to `hypcubic`,
  `cube coloring induct cfmap colalias hypsub unav/faces`, the red chain
  from `red/red` to `red/ccheck` in the order of the `red/` entry above,
  `realias ringtrace kempemap patch patch2 split unav/realias`, then
  `unav/` `part` to `qmirror` as in the entry above, `unave`, and
  `embed.sl embedgoal.sl`. `realias.sl` and `unav/realias.sl` put back
  names that a later file of the chain defines again (hypcount.sl's
  `AppN` constructors, base.sl's `Or`); `colalias.sl` keeps the former.
  `fcopen.sl` chains `embed-analysis` with `inductfc.sl` in one run.
- `embed2.sl` (load after `embed.sl`, in its chain with `geomring sew
  snip srcycle revsnip revsnip2 revsnip3` loaded after `split`): first-order
  pieces of embed.v's not_embed_reducible, as far as both compilers check
  them, for the patch of the map that embed_patch would build; the
  embedding itself (embed_functor to embed_patch) is not ported, and
  of contract.v's contract_coloring only the part in `contract.sl` is. `pull-col`: a four-colouring of a map
  gives one of a second map through a dart map that sends face and edge
  images into the faces of the images (`Reach`). `embed-color`: from such
  a dart map of the disk map into a configuration map, a four-colouring of
  the configuration map with trace et on the disk ring's image, and a ring
  trace rot 1 (rev et) of the remainder map, the map is four-coloured
  (`patch-colorable`). `rem-col`: a contract colouring (`CCColoring`) whose
  contract darts miss the remainder map four-colours it. `rem-kempe`: the
  remainder map of a patch of a planar plain cubic map, its ring rotated
  by one, is a `KempeRing` (embed_closure). `cc-pull`: a contract
  colouring of the map, through a dart map that commutes with edge, sends
  faces into faces and sends the contract darts of the configuration, and
  only those, onto the map's (`InSides`), gives the fields of red/cfred.sl's
  `CcColoring` on the configuration map (the first half of embed_contract).
  The trace equations of embed_contract are in `contract.sl`, and the use
  of `CRed` and `NotEmbed` itself in `notembed.sl`. That these statements
  match Coq's has been checked only by reading.
- `traceconv.sl` (load after `ringtrace.sl`; in the birkhoff chain
  before `birkhoff.sl`, in the embed chain after `embed2.sl`): the colour
  numbers and traces of `cfcolor.sl` (`NCols`, `CTr`) read as those of
  `ringtrace.sl` (`ColOf`, `TraceFrom`) and back, and `CpCol` as a ring
  trace on the configuration's ring and back (`cpcol-of`, `cpcol-rt`).
- `contract.sl` (load after `traceconv.sl`, in the embed chain): parts of
  contract.v's contract_coloring and embed.v's embed_contract, as far as
  both compilers check them, with minimality as data. `Contraction d e n
  f cc ms` names the map contract_coloring builds by contracting cc (its
  G2) as the one map of a list ms, planar, bridgeless, plain, precubic
  and smaller (`contraction-smaller` gives the `Smaller` a `Reduces`
  takes), with a dart map p sending faces along faces and edge links as
  `LiftE` says. `cc-lift` and `contraction-lift` turn a four-colouring of
  the contracted map into a `CCColoring` of the map (the k0 of
  contract_coloring). `embed-contract-trace` gives the trace equations of
  embed_contract: for k constant on faces, kc = k . h1 a contract
  colouring of a configuration map and kr = k . hr a four-colouring of a
  remainder map, with the images of the configuration's `Cpmap` ring
  under h1 reaching along faces those of a ring R under hr, place by
  place (`Reach`), one trace et is a `CcCol` of the configuration and a
  `RingTrace` of the remainder map on R. Building a `Contraction` from a
  contract is in `contract2.sl`. That these statements match Coq's has
  been checked only by reading.
- `contract2.sl` (load after `contract.sl` in the combined chain below):
  contract_coloring's construction of the contracted map, as far as both
  compilers check it, with minimality as data. Each contract edge x, ex
  is contracted by WalkupF at x and then at ex, both kept as dead darts
  fixed by e, n and f (`contract-dead`, `CStep`); the faces of x and ex
  merge (`cf-face`, `Jump`), and a list q sends x and ex to a live dart r
  of the merged face (`Rep`, `QMap`) so that every face step, read
  through q, is a walk along the new faces (`cs-qreach`). `CHist`
  records the steps from the original map, and reads off them that the
  map is planar, precubic (`precubic-skip`), plain off the dead darts
  (`EAgree`, `LPlain`), and that the composite dart map p fixes live
  darts, is constant on contracted edges and sends faces along faces
  (`ch-pfix`, `ch-pair`, `ch-reach`). `lb-dec` decides bridgelessness off
  the dead darts (`LBridgeless`) or finds a live bridge. With no live
  bridge at the end, `ch-contraction` takes the live darts as a patch
  along empty rings (`live-part`, through `patch2.sl`'s `patch-lab`,
  which `patch-gcomp` also uses) and gives the `Contraction` of
  `contract.sl`: the live part is planar, bridgeless, plain and precubic
  (`part-pbpp`), and p renumbered by the positions of the live darts
  satisfies `Reach` and `LiftE`. A live bridge of the first contraction
  joins the faces of x and ex (`cs-bridge`, `BSides`, by merged face
  labels), so `double-dart` of `birkhoff2.sl` gives a `Reduces`
  (`bridge-reduces`). `contract-one`, for a contract of one dart, gives a
  `Contraction` or a `Reduces` (`ContractOut`). `contract-go`, for any
  nonempty contract whose insertE is sparse, gives the same or a live
  bridge arising after at least one contraction (`CGLater`), which
  `contract3.sl` handles. `notembed.sl` reads the contract off
  red/cfred.sl's `ValidContract`, whose `InsertE` is a type of the same
  shape that ringtrace.sl defines again, through `iealias.sl`. The
  combined load order,
  checked by both compilers (about 25 and 60 s in one run each): the
  birkhoff chain of the `birkhoff.sl` entry with `birkfit.sl`, then
  `birkhoff2.sl embed2.sl contract.sl contract2.sl` (`embed2.sl` does not
  appear to need `embed.sl`; `traceconv.sl` is already in that chain).
  That these statements match Coq's has been checked only by reading.
- `contract3.sl` (load after `contract2.sl`, in the chain of
  `embed5.sl` below: that chain, then `minarity embed2 contract
  contract2 embed3 embed5 contract3`): the bridgeless part of
  contract_coloring, as far as both compilers check it, with
  minimality as data. A `CGLater` bridge is read on the original map,
  where the dead darts keep the dart map the identity: each face step
  after a contraction is a walk before it that jumps along contracted
  edges (`cstep-xp`, `xp-lift1`, `xp-hist`), which gives a cyclic
  chain of contracted darts from the bridge's dart w back to it, cut
  by shortcuts to darts on distinct faces (`chain-simp`), so a proper
  ring w :: B with B in insertE (`bridge-ring`, a contract ring).
  sparse_contract_ring (`ring-nt`): the node images of the exceptional
  dart give a dart of diskF, a smaller chord ring (`node-step`,
  `mk-chords`, `chord-len`, and diskF_chord_ring as `chord-diskf`), or
  two darts of one node orbit in insertE, which sparsity refutes
  (`two-steps`, `disk-f`); diskFC comes from diskF of the reverse ring.
  contract_ring_max (`ring-max`, by `pigeonhole` on the contract darts
  the ring's darts come from). `contract-all` takes valid_contract's
  size conditions read on the map (`CSize`: one to three darts, or
  four with red/cfred.sl's `Triad`) and gives a `ContractOut`
  (contract3_valid through `birkhoff-reduces`), or, for four darts, a
  contract ring of five darts nontrivial for 0 (`CAFive`): that case is
  triad_valid, which `triad.sl` proves (`notembed.sl` takes it as
  `TriadFive`). `contract2.sl` and `birkhoff2.sl`
  keep walk.sl's `Sub` and hypsub.sl's `split-cover` as `WSub` and
  `hsplit-cover`, which the `unav/` files define again. That these
  statements match Coq's has been checked only by reading.
- `embed3.sl` (load after `contract.sl`, in the embed chain): the first
  part of embed.v's embedding construction, as far as both compilers
  check it, on an `EEnv` (the configuration map with its ring, arities
  and `KernelList`, a `Geo` map and a `Preembedding` hl of the kernel).
  The kernel is closed under face both ways (`ker-face`,
  `ker-face-inv`); cface_ac_h and cface_h_ac (`face-h`, `h-face-back`);
  cface_inj_embed (`cface-inj`). embed is the relation `HEmb` (h x on
  the kernel, otherwise read off edge x, node x or node (edge x), the
  first in the kernel, as Coq's embed), total (`h1-exists`) and listed
  on the darts 0..dc-1 with its values darts of the map (`h1-list`,
  read by `embl-at`), in the list form `embed-contract-trace` and
  `cc-pull` take. embedE at every dart (`embed-e`) and embedN at every
  dart off rc (`embed-n`) are proved from two certificates taken as
  hypotheses: `GcOK`, per dart of the configuration map, edge an
  involution, node keeping rc and of order 3 off it, and the conclusions
  of edge_perimeter, chordless_perimeter and embed_cases (decided on the
  configuration maps in `embed4.sl`), and
  `FunctorAll`, embed_functor's conclusion (each kernel dart whose edge
  image is in the kernel is central; `embed4.sl` proves it for the
  configuration maps). More of embed.v is in
  `embed5.sl`. That these statements match Coq's has been checked only
  by reading.
- `embed5.sl` (load after `embed3.sl`): more of embed.v, as far as both
  compilers check it, on an `EEnv` with `GcOK` and `FunctorAll` as
  hypotheses. embed is a function (`hemb-fn`). embed_full is a
  certificate over the pairs of kernel darts (`FullAll`), and `full-dec`
  decides it: the certificate, or a pair where it fails (`FullBad`).
  From the certificate: pre_embed_inj (`pre-embed-inj`), embed_inj off rc
  (`embed-inj`), and embed2.sl's `InSides` for ie = insertE cc and
  ins = insertE (map h1 cc) (`ins-sides`, with ie off rc, stated with
  ringtrace.sl's `InsertE`, which shadows red/cfred.sl's; `notembed.sl`
  converts a `ValidContract`'s). embedE at every dart
  and embedN off rc are given as patch.sl's `MorphOff` lists
  (`h1-morph-e`, `h1-morph-n`). `embed-main`, a level factory, gives for a
  connected `Pbpp` map with a `NoColoring` a `Reduces` or an `EmbedOut`
  (h1, those lists, the certificate and an `EmbedPatch`: the `Patch` and
  dart maps that `embed-color` and `rem-col` take, hd = h1 . embd, the
  disk ring sent to rev (map edge rc), Coq's map edge of its ring, which
  is rev rc here, embd onto the darts off rc (`InEither`), and cface_h1),
  from two hypotheses: `FullRedR` (a `FullBad` pair, with the
  configuration's `Radius2` and `KerMax` certificates, gives a `Reduces`; in Coq
  radius2, the reductions of the path to a hom ring of at most five
  darts, Birkhoff, and trivial_hom_ring; `fullred.sl`'s `full-red-of`
  gives it from `BirkhoffChecks` and `TrivRed`) and `PatchOpen` (the
  construction of embed_disk, embed_rem and embed_patch, with cface_h1,
  for a ring rc that is a `NodeRing`: rev rc, Coq's ring as it appears
  to be read here, a node cycle on distinct faces, embeddable's sfcycle
  node; `embed6.sl`'s `patch-open` proves it). `run` takes the
  certificates `NodeRing`, `Radius2` and `KerMax` of the configuration as
  arguments. embed_valid_contract is in `evalid.sl`. Chain: that of
  `birkhoff3.sl`, then `embed2 contract embed3 embed5` (about 70 s with
  slc in one run). That these statements match Coq's has been checked
  only by reading.
- `fullred.sl` (load after `embed5.sl`, in its chain): part of embed.v's
  embed_full, as far as both compilers check it, with minimality as data.
  Coq's proof uses the radius of the kernel (radius2 of embeddable) and,
  for five darts, the ring arities behind adj_kernel_max, which are not
  facts of `EEnv`, `GcOK` and `FunctorAll`; so embed5.sl's `FullRedR`
  takes two certificates that `embed4.sl`'s run decides: `Radius2` (a
  kernel dart x0 and, for each kernel dart, the two edge steps that reach
  it from the face of x0) and `KerMax` (after adj_kernel_max, which Coq
  reads off good_ring_arity: from each dart off the kernel, one of its
  first five face iterates has its edge image off the kernel). `bad-hom` follows the
  first two reductions of embed_full:
  a `FullBad` pair and the certificate give a walk of five rlink steps
  through the face of x0, which `shorten` (Coq's induction on the path)
  turns into a `HomBad`, a pre_hom_ring of at most five darts whose last
  dart does not rlink to its first (told apart by a face labelling,
  `Kernel`). `hom-birk` decides whether the image ring is nontrivial for
  the m of `BkMode`, and then reduces the map through
  `birkhoff-reduces`, or gives a `HomTrivial` (one side of the ring meets
  at most m faces off it, `TrivSide`). `full-red-of` gives a `FullRedR`
  from `BirkhoffChecks` and `TrivRed` (a `HomTrivial` gives a `Reduces`,
  for any bound above the level of `birk-glue`), taken as a hypothesis,
  which `trivred.sl` gives from a narrower one.
  That these statements match Coq's has been checked only by reading.
  Chain: that of `minarity.sl`, then `embed2 contract embed3 embed5
  fullred` (in one run about 66 s with slc and 161 s with the reference
  compiler).
- `trivred.sl` (load after `fullred.sl`): fullred.sl's `TrivRed` from
  one hypothesis, `TrivFive`, as far as both compilers check it, with
  minimality as data. `triv-hom` is trivial_hom_ring: an rlink walk of
  kernel darts whose image is a ring of the map with an empty diskF
  (`FEmpty`, read off a ring with the same darts) closes, by Coq's
  induction through the two chord rings at the node of the last dart
  (`chords-of` builds revsnip3.sl's `Chords`, `fe-chord` carries `FEmpty`
  to the chord ring through `Three`). `side-hd` applies it when the diskN
  side of a `HomTrivial` meets no face off the ring, and `side-zs` when
  the other side does not, on the reversed ring rot 1 (rev (map edge R)),
  the image of the edge images of the walk (`edges-h`, `rpath-rev-c`),
  whose diskN side is the other side of R (`hd-zs`, through revsnip.sl's
  `rev-disk`); `hom-proper` is hp_ok. What is left of a `HomTrivial`
  (`ht-five`) is a `HomFive`: a hom ring of five darts that does not
  close, whose diskN side meets exactly one face off it. `TrivFive` (a
  `HomFive` gives a `Reduces`, for any bound above the level of
  `birk-glue`) is taken as a hypothesis (`triv-red-of` gives `TrivRed`
  from it), which `trivfive.sl` proves. The two statements give a
  `Reduces` rather than `False`, since the five-dart case goes through
  Birkhoff (chordless_spoke_ring, adj11_edge), which gives a `Reduces`
  here. That these statements match Coq's has been checked only by
  reading.
- `trivfive.sl` (load after `triad.sl`, in the chain of `fcgoal.sl`):
  trivred.sl's `TrivFive`, the five-dart case of embed.v's embed_full,
  as far as both compilers check it, with minimality as data.
  `triv-five` gives it by `five-red`. The one face off the ring that the
  diskN side meets, that of y, is read as triad.sl's `FRec` (or the map
  reduces, `fr-make`); its spoke labels are labels of the ring
  (`spk-sub`: the node image of each spoke is in diskN, so on a face of
  the ring), so with more than four darts it is adjacent to every face
  of the ring (`cover`). For each ring dart v, n v is on the face of y,
  or the map reduces (`ring-adj`, through evalid.sl's `adj11`; n (e v)
  on it would put e v in diskN, against diskN_edge_ring). Then the next
  ring dart is f (f (e v)) (`ring-step`, two spokes of one face on one
  face being one), the walk's next dart in the configuration map is
  f (f (e x)) (`cfg-step`, through embed_functor and cface_inj_embed),
  and so the node images t0 .. t4 of the walk satisfy f t(i+1) = t i,
  with their edge images in the kernel (`en-in`). If t4 is in the
  kernel, the ring would close (`close`: n (f (f (e z))) and n x have one
  image, so are one dart); otherwise embed5.sl's `KerMax` at t4 is
  contradicted (`kr-dead`), which is where Coq uses adj_kernel_max. In
  a test run a broken variant (`close` without identifying the image of
  t4) was rejected. That these statements match Coq's has been checked
  only by reading.
- `notembed.sl` (load after `contract3.sl` and `embed6.sl`, with `iealias.sl` loaded after
  `red/cfred.sl`): not_embed_reducible of embed.v with minimality as data,
  as far as both compilers check it. `not-embed` gives embed.sl's
  `NotEmbed CRX cfs` from `BirkhoffChecks`, embed5.sl's `FullRedR`
  (with `embed6.sl`'s `patch-open`), and three hypotheses: `CfCerts cfs`
  (the per-configuration certificates: embed4.sl's `GcOK` and
  `FunctorAll` and embed5.sl's `NodeRing`, `Radius2` and `KerMax`, for a
  configuration of cfs; `embed4proof.sl` proves it), `EmbedValid`
  (embed_valid_contract: the image map h1 cc of the configuration's
  contract is a `ValidContract` of the map for the empty ring, or the map
  reduces, given cface_h1 as the `EmbedPatch` gives it; `evalid.sl`
  proves it) and `TriadFive` (contract3.sl's `CAFive` case, with the map's
  `Pbpp`, `Connected`, `Geo`, `NoColoring` and `BirkhoffChecks`, gives a
  `ContractOut`; `triad.sl` proves it). A disconnected map splits (`split-reduces`); otherwise
  `embed-main` embeds the kernel or the map reduces, and the contraction
  of map h1 cc (`contract-all`, with its `CSize` read off the size
  conditions of that `ValidContract`) is the one map of a `Reduces` whose glue,
  `ne-glue`, follows embed_contract and not_embed_reducible:
  `contraction-lift`, `cc-pull`, `rem-col` and `embed-contract-trace` give
  one trace of a contract colouring of the configuration and of a
  colouring of the remainder map on its ring rotated by one, `CRed`'s
  co-closure meets the ring traces of the remainder map, Kempe-closed
  (`kclosed-at`, kempemap.sl's `kempe-closed` at a level the caller gives,
  from `rem-kempe`), in a trace of a colouring of the configuration map,
  and `ne-finish` turns it into the arguments of `embed-color`. The levels
  follow red/cfred.sl's caller recipe: NL for the closed set, NR, NW and NY,
  then NK for the glue, all at the top level. Along the way: face sends the
  edge images of the configuration's ring to the ring rotated by one
  (`ring-fe`); h1 rc and hr (rotr 1 br) are paired along faces
  (`reach-step`, `reach-unsnoc`, `reach-flip`); and `Disj hr ins` follows
  from `PatchParts` (`ins-off`, `ins-hr`, `ie-off-erc`). In a test run two
  broken variants (the pairing not flipped, and NK minted before NY) were
  rejected, and in another a variant passing `CAFive`'s insertE to
  `TriadFive` without equating it to that of the `ValidContract`. That these statements match Coq's has been checked only by
  reading.
- `embed4.sl`, `embed4proof.sl`, `embed4goal.sl` (load after `fcopen.sl` and `native.sl`, in the chain
  of `fcgoal.sl` below, in place of `fcgoal.sl`):
  embed.v's embed_functor and the facts of embeddable that the embedding
  reads, for the configuration maps, as far as both compilers check them.
  A run decides, per configuration of red/configs.sl on the map cpmap.sl
  builds, a bundle `CfGc` (listed by `AllGc`): its kernel, embed3.sl's
  `GcOK`, `NodeRing` (rc read backwards along node, as embed5.sl states
  it), `Radius2`, `KerMax` (`kmall-c`), and for each kernel dart whose edge image is in the
  kernel a refutation (`Refut`) of its not being central. `cf-gcok`,
  `cf-functor` and `cfcerts-of` move these to any `KernelList` and any
  `EEnv` on the map of a configuration of cfs (through `cpmap-fn` and
  `hyper-node-unique`), `embed4proof.sl` proves `CfCerts cfs`
  (`cfcerts-proof`, cfs that of `fcopen.sl`), and `embed4goal.sl` sets it
  as a goal and discharges it. embed_functor is not ported along
  Coq's induction on disks: a refutation is a case tree on the centrality
  of kernel darts, closed at each leaf by a clash, by `node-rule` (at a
  node with every dart and edge image in the kernel, two central darts
  make the third central, from hF and the cubic map) or by a cut of the
  kernel faces (`RfCut`, a face labelling) whose crossing darts the branch
  knows are not central, which the preembedding's rlink paths of central
  darts refute (`cut-sound`, `path-cross`). The search is unchecked; its
  tree is checked. The run reads the map's permutations, the face labels
  and each cut's labelling through `Tab`, the list held as an array, each
  read checked by `tab-q` against the list it stands for; `embed4proof.sl`
  queues one native.sl job per chunk of css (chain: `native.sl` before
  `embed4.sl`). In single measurements on a 4-core cloud VM, which
  should be read as approximate: the compiled run of all 633
  configurations took about 9.5 s on one core before `Tab`, and on the
  last 133 configurations 4.2 s before and 1.3 s after; compiling the
  generated OCaml (about 7.8 MB, nearly all of it the embedded
  configurations, with about 90 KB of functions) took far longer than
  the run, about 1460 s on a loaded machine. On a 4-core cloud VM `--goal proved` passed in about
  400 s with slc and 430 s with the reference compiler (under `ulimit -s
  unlimited`), the whole chain and the compiled run, in one run each,
  before the jobs and `Tab`; with them, in one run each on a machine
  running other jobs, about 580 s with slc and 530 s with the reference
  compiler, most of it the OCaml compile. A variant whose refutation
  search had one step of fuel was rejected (a job answered `ChkNo`).
  In a test run three broken variants were rejected: `node-rule` without
  its last step (a type error), and the run with no cut leaf or with a
  flood fill that ignores the darts known not central (the run answers
  `ChkNo`). That these
  statements match Coq's has been checked only by reading.
- `evalid.sl` (load after `notembed.sl`, in the chain of `fcgoal.sl`
  below; `fcgoal.sl` also checks after it): embed_valid_contract of
  embed.v with minimality as data, as far as both compilers check it.
  `embed-valid` gives `notembed.sl`'s `EmbedValid` from `BirkhoffChecks`.
  `EmbedValid` takes cface_h1 as the `EmbedPatch` gives it (`Respects h1
  fc h1f` and `Reach fm h1 h1f`): the triad's bands appear to need it,
  since the faces of the edge images of the triad's darts may meet rc,
  where embedE and embedN alone do not seem to fix where h1 sends them.
  It takes no per-configuration fact beyond what `EmbedValid` already
  has (the configuration's `ValidContract`, which `CRed` carries, and
  `GcOK` and `FunctorAll`). Proved: the image of the contract is off the
  empty ring; embed_sparse (`embed-sparse`, a node path of the map from
  h1 a pulled back along embedN, `node-back`, then embed_inj); the size;
  and for four darts the image of the triad: its three darts on the face
  of h1 x (`img-on`, through the preembedding), distinct by embed_inj,
  with their bands through cface_h1 (`band-img`), and the dart not
  adjacent to it (`adj-pick`): of h1 y and h1 (e y), y the dart of the
  configuration's triad not adjacent to x, one is not adjacent to the
  face of h1 x, or the node image of one is on that face, which
  cface_ac_h1 (`face-back`) pulls back to an adjacency of y that the
  configuration's triad excludes, or the map reduces through adj11_edge.
  `adj11` proves adj11_edge without the spoke ring: A and e A adjacent to
  a face through its darts a1 and b1, with neither n A nor n (e A) on it,
  give the ring a1 :: A :: e b1 of three darts, nontrivial for 0 (n A in
  its diskF, n (e A) in its diskFC), so `birkhoff-reduces` applies. In a
  test run two broken variants (the diskF and diskFC darts swapped, and
  cc in place of its image) were rejected. Chain: that of `fcgoal.sl`
  with `evalid.sl` after `notembed.sl` (in one run with `fcgoal.sl` and
  `--goal proved`, about 50 s with slc and 113 s with the reference
  compiler). That
  these statements match Coq's has been checked only by reading.
- `triad.sl` (load after `evalid.sl`, whose `orbit-in` it uses, in the chain of `fcgoal.sl`): triad_valid
  of contract.v with minimality as data, and the parts of birkhoff.v's
  SpokeRing section it uses, for faces of any size, as far as both
  compilers check them. Faces are read through a `FaceLab` labelling.
  `FRec` is the face of a dart with its orbit and the distinct labels of
  the faces of its spokes (`fr-make`, scycle_spoke_ring through
  double-dart; `fr-hit` and `fr-wit` read fband_spoke_ring as membership
  in those labels). `chord-gen` is chordless_spoke_ring (the ring v :: e z
  :: e u of three darts, nontrivial for 0), `adj12` adj12_edge (a ring of
  four darts), and `adj-max` fcard_adj_max, through cross_adj (`cross`)
  and, where Coq counts faces, through the orientation of pairs of darts
  of one face (`consec`, `fan-or`, `tri-or`; three darts each the face
  image of the next would be a whole face, against `Geo`'s faces of more
  than four darts). `triad-reduces` follows triad_valid: a dart of diskF
  and one of diskFC (nontrivial-pick) each have a spoke off the faces of
  the ring, which makes the ring nontrivial for 1 (`nt1`), against
  Birkhoff, or one of them is a hub whose spokes are all on faces of the
  ring (`hub-dec`); its five or more spoke faces are then all five faces
  of the ring (`cover`), the faces of insertE are faces of the ring
  (`ins-band`: otherwise the ring is a contract ring of the contract
  without one dart, against `ring-max`), and the triad's three faces are
  adjacent to the triad dart and to the hub, against `adj-max`, or the
  triad dart is on the face of the hub, against `NotAdj`. `triad-five`
  proves `notembed.sl`'s `TriadFive`, at a level `TB` minted at the top
  level after `birk-glue`'s. It does not use the sparsity of insertE
  beyond the `NonTrivial` that `CAFive` already carries. In a test run a
  broken variant (Birkhoff for five darts given the ring nontrivial for 0
  only) was rejected. That these statements match Coq's has been checked
  only by reading.
- `fcmany.sl` (load after `defs.sl` and before `coloring.sl`, whose
  `Proper` shadows `defs.sl`'s): sets the goal `FourColorM`, the
  four colour theorem as a program: a function, not erased, from the edges
  `es` of a drawing to a list `ks` of paints, with the `Drawing` certificate
  and the `Proper` result erased. Both compilers accept it alone under
  `--goal open`.
- `paint.sl`, `paint-run.sl` (load after `readback.sl` and before
  `coloring.sl`): `paint-go`
  searches for a proper four-colouring of the endpoints of a list of
  edges from their coordinates alone, an edge at a time: it paints each
  endpoint not yet painted with each colour below 4 in turn, then checks
  the edge. It returns a colouring with its `Proper`, or a certificate
  (`NoPaint`) that `nopaint-sound` turns into a refutation of every proper
  colouring. `four-color-m` gives `FourColorM`'s function from an erased
  `FourColor`: the search, whose failure branch is refuted by the
  colouring `FourColor` gives, so that `FourColor` and `Drawing` are used
  only in erased positions. `paint-run.sl` runs the search on a drawing of
  K4 (a few seconds with either compiler). In test runs, with `FourColor`
  as a hypothesis, three broken variants were rejected: a certificate with
  the child for one colour in place of another's, a refutation recursing
  into the wrong child, and a function returning the erased colouring.
- `fcmanyfinal.sl` (load after `fcproof.sl`, `paint.sl` and `fcmany.sl`, in
  the chain below): proves `FourColorM` by `four-color-m` on `fcproof.sl`'s
  `four-color-proof`. Chain: that of `fcfinal.sl` with `paint fcmany`
  after `readback` and `fcmanyfinal` in place of `fcfinal`, with `--goal
  proved`.
  In one run on a 4-core cloud VM shared with other runs it passed with
  slc in about 578 s, at most about 0.8 GB resident.
- `fcopen.sl`, `fcgoal.sl` (load after `evalid.sl`, `triad.sl`, `trivfive.sl` and
  `red/chunks.sl`, in the chain below): `four-color-open` gives `FourColor`
  from `UnavE cfs`, `AllRedC CRX css`, `BirkhoffChecks` and `CfCerts cfs`
  (whose computed proofs are in `unav/qztproof.sl`, `red/proof-c.sl`,
  `red/bproof.sl` and `embed4proof.sl`), through
  `embed-analysis`, `birk-geo-of`, `full-red-of`, `triv-red-of`, `triv-five`, `embed-valid`, `triad-five`, `not-embed` and `four-color-from`,
  and `fcgoal.sl` sets and proves it as the goal `FourColorOpen`. Here css
  is the chunks of `red/configs.sl` as `red/chunks.sl` decodes them, and cfs
  their concatenation by `concat-c` (`fcopen.sl`), which `cfs-run` decodes
  and concatenates again at run time, with an `Eq` to cfs from `decall-fn`
  and `concat-fn`; the proof files read both from scope, so in
  one unit they are about the same entries (a variant passing a `UnavE`
  of a cfs computed again by `concat-cfs` was rejected). Chain (both compilers, with `--goal proved`; about 54 s with slc and 124 s
  with the reference compiler in one run each): `std/macro.sl std/nat.sl
  std/list.sl ring.sl`, then `defs
  orient base sweep geo plan map lists planemap walk frontier labels rot
  fan build readback parta reduce hypgraph hypperm hypermap hypplane
  reduce2 hypeuler hypderived hyprelabel hypwalkup hypgeom hypjordan
  hyptree hypwalkeq hypcount hypcubic cube cubegoal reduce3 coloring induct
  inductfc cfmap colalias hypsub unav/faces`, the red chain from `red/red`
  to `red/bcheck` as in the `embed.sl` entry, then `cpcomp iealias realias
  ringtrace kempemap patch patch2 split geomring sew snip srcycle revsnip
  revsnip2 revsnip3 cpgeom ringdec traceconv birkhoff birkfit birkhoff2
  embed2 contract contract2 unav/realias`, `unav/` `part` to `unave` as in
  the `embed.sl` entry, and `embed birkhoff3 minarity embed3 embed5
  contract3 embed6 fullred trivred notembed evalid triad trivfive red/chunks
  fcopen fcgoal` (each `.sl`). `contract2.sl` loads before `unav/`,
  whose `Sub` it would otherwise read.
- `native.sl` (load after `std/macro.sl`, before the files that use it):
  macros that put the computed checks of a unit in one `native-compute`.
  `(native-jobs name ev job ...)` queues jobs, each `(f pat)` for a
  `Settled` thunk `f` or `(T e pat)` for a thunk `-> (many T _)` with body
  `e` that the macro defines, and the erased `ev`, which may name the
  binders of the jobs' patterns. `(native-each name xs (x t r) T e pat
  step nil)` comptime-matches the `Settled` list `xs` into its elements
  and queues the job `(T e pat)` for each, with `x` the element and `t`
  its tail, and the fold of `step` (with `r` the fold of the rest) ending
  in `nil` as its evidence. `(native-then stmt ...)` queues statements.
  `(native-run)` runs every queued thunk in one `native-compute`, then
  matches each result against its pattern, binds each `name` erased to
  its evidence and runs the queued statements, in the order queued.
  Names in patterns, evidence and statements resolve where they are
  queued; the patterns' binders are renamed apart. The queue is the
  `Settled` value of the last of `native-queue-0`, `native-queue-1`, ...
  in scope, each macro binding the next. `red/proof-c.sl`,
  `red/bproof.sl`, `unav/qztproof.sl` and `embed4proof.sl` queue their
  checks (one job per chunk of css for `AllRedC` and, through
  `allgc-concat`, for `AllGc`), and `fcproof.sl` and each check's goal
  file call `native-run`; the `fcproof.sl` entry gives the size and
  times of the `fcfinal.sl` chain's one `native-compute`. In test runs, a
  `BirkhoffChecks` built from the proofs in the wrong order and a failing
  job were rejected. On an earlier 22.0 MB program of that chain,
  ocamlopt took about 595 s with `-inline 0` and about 605 s with
  `-inline 25` (`--inline`, MANUAL.md), much as without it; three of its
  thunks ran about 10 to 20% faster with `-inline 25` than with
  `-inline 0`, in one run each.
- `fcproof.sl`, `fcfinal.sl` (load after `embed4proof.sl`, in the chain
  below): `fcproof.sl` binds `four-color-proof`, `FourColor` of `defs.sl`
  with no hypotheses, by `four-color-open` on `unav-proof`,
  `all-red-proof`, `birkhoff-proof` and `cfcerts-proof`, all computed in
  the same unit, and `fcfinal.sl` sets and proves it as the goal. Chain:
  that of `fcgoal.sl` up to `fcopen.sl`, then `native embed4 red/pieces red/proof-c
  red/bproof unav/qztproof embed4proof fcproof fcfinal` (each `.sl`), with
  `--goal proved`. The jobs reach the configurations only through strings
  (the `red/configs.sl` entry, and `cfs-run` for `unav/qztproof.sl`'s
  region and cap jobs) and the presentation scripts are strings
  (`unav/data.sl`), so `native-compute` writes about 1.9 MB of OCaml with
  slc (about 3.0 MB with the reference compiler) for its 158 jobs. In
  runs on a 4-core cloud VM with a load average of about 5 to 8 from
  other runs, which should be read as approximate, the unit passed with
  slc in about 640 to 730 s of wall time (about 1050 s of CPU, at most
  about 0.75 GB resident): about 34 to 41 s of elaboration, 8 to 10 s of
  ocamlopt and 590 to 680 s running the jobs (about 1000 s of CPU
  together, the longest about 13 s of CPU); with
  `OCAMLRUNPARAM=s=8M,o=200` in about 640 and 716 s, and without it in
  about 733 s. With the scripts written as constructor applications in
  place of strings the program was about 14.8 MB, elaboration about 52
  to 79 s and ocamlopt about 25 to 27 s (at most about 1.5 GB resident),
  and the unit took about 590 to 760 s, much as with strings: the time of
  the jobs, which share the machine, appeared to outweigh the difference.
  With the reference compiler (under `ulimit -s unlimited`, with
  `s=8M,o=200`) it passed in about 874 s (about 109 s of elaboration).
  In test runs on the chain of
  `fcgoal.sl` up to `fcopen.sl`, a use of `four-color-open` with its
  second and third arguments swapped was rejected.
- `embed6.sl` (load after `embed5.sl`): embed_disk, embed_rem,
  embed_patch and cface_h1 of embed.v, as far as both compilers check
  them: `patch-open` proves embed5.sl's `PatchOpen`. Without `NodeRing`,
  the patch PatchOpen asks for appears not always to exist (for instance,
  it seems, when the ring is the union of two node cycles in different
  components). The construction (`embed-patch6`) runs on the node cycle
  rr = rev rc that a `NodeRing` names, to which `env-rev` carries `EEnv`
  and `GcOK` (they read only which darts are on the ring); `patch-at`
  reads its disk ring, sent to map edge rr = rev (map edge rc), as
  `EmbedPatch` takes it. The disk map is Coq's embed_disk on the darts
  embd off the ring, with its edge sending each dart of map edge rr to
  the next one; the remainder map is on rev (h1 . map edge rr) followed
  by the darts of the map off h1 . embd, with its node sending each dart
  of that reversed ring to the next one; both are restricted from
  permutations of the whole maps as in `snip.sl` (`bij-build`,
  `restrict`), and the patch's simple disk ring is `snip.sl`'s
  `disk-simple`. cface_h1 goes through the patch's `face-hd` where fc x
  is on the ring. In a test run, a variant passing the reversal of
  the disk ring's image the wrong way round was rejected. Chain: that of `embed5.sl`, then
  `embed6`. That these statements match Coq's has been checked only by
  reading.
- `birkhoff.sl` (load after the chain below): Birkhoff_valid of
  `birkhoff.v`, as far as both compilers check it, with the minimality of
  the map entering as data rather than as a function: `birkhoff-maps`, a
  static function, takes a ring r of h + 2 darts nontrivial for m of a
  planar bridgeless plain cubic connected map and the basis of a
  `BirkhoffCheck h m`, and gives either a ring of fewer darts nontrivial
  for 0 (`Shorter`, from a chord of a side, through `ring-disk-chord`) or
  the two sides of r and its reversed ring (`BRing`) with, for each side
  and each basis program, the map chkbP glues (`side-map`: the disk map
  sewn to the program's map on its ring a :: p read as the node cycle
  a :: rev p, after Coq's rotr 1 (rev (cpring G))), each planar,
  bridgeless, plain, precubic and smaller (`BNeed`, the maps listed by
  `Mp`); `birkhoff-ring` takes those, the other fields of the
  `BirkhoffCheck`, four-colourings of all those maps (`MpCols`) and a
  search certificate that the map has no four-colouring (`NoExt`), and
  gives `False`. It builds the `BSide`s at the fixed level `BL`
  (`mk-side`: `decide-ring-trace` for the decision, `rtno-sound` for
  disjointness, `side-trace` and `bkprog-hit` for the basis traces,
  `ring-disk-closed` for the closure) and the `BGlue` from
  `colorable-from-ring`, and calls `birkhoff-check-sound BL`, instantiated
  at the top level. The size bound of chkbP is `birkhoff-size`, from
  `outer-count` (the faces of the remainder map, through
  `patch-fcard-face-r`, number at least k + m + 1) and quasicubic_Euler,
  with one identity checked by `ring-check`. For the theorem Birkhoff,
  `birkhoff-check-at` reads the check for a ring of 2 to 5 darts off
  `BirkhoffChecks` (with m 1 for five darts and 0 below, `BkMode`), and
  `ring-two` shows a ring of a bridgeless map has two darts; the induction
  on the ring size that Coq's Birkhoff makes is in `birkhoff2.sl`. The cubicity and connectedness of a
  minimal counterexample (`birkhoff3.sl`'s `cubic-reduces`;
  `split.sl`'s `split-reduces` for connectedness) are hypotheses here. That these
  statements match Coq's has been checked only by reading. Load order:
  `std/nat.sl std/list.sl ring.sl`, then `base map lists planemap walk
  frontier labels hypgraph hypperm hypermap hypplane hypeuler hypderived
  hyprelabel hypwalkup hypgeom hypjordan hyptree hypwalkeq hypcount
  hypcubic cube coloring induct colalias hypsub`, then `cfmap red/red cpmap
  red/color cfcolor red/ctree red/gtree red/grestrict red/crestrict
  red/kempe cpcolor red/configs red/bridge red/init red/check red/gramrot
  red/cfred red/ccomp red/ccheck red/bcheck cpcomp`, then `ringtrace
  kempemap patch patch2 geomring sew snip srcycle revsnip revsnip2
  revsnip3 cpgeom ringdec traceconv birkhoff` (each `.sl`). `birkfit.sl` (load
  after `birkhoff.sl`; with `split.sl` the chain also checks) turns the
  maps `BNeed` lists into the `Smaller` list of a `Reduces`
  (`bneed-smaller`).
- `birkhoff2.sl` (load after `birkfit.sl`): the theorem Birkhoff of
  `birkhoff.v` and two of its corollaries, as far as both compilers check
  them, with minimality as data. `birkhoff-reduces`: in a planar
  bridgeless plain cubic connected map that the search finds
  uncolourable (`NoColoring`), a ring of k darts, k below 6, nontrivial
  for the m of `BkMode k m`, gives a `Reduces` to the maps of the check.
  It follows `birkhoff-maps`' `Shorter` rings down (`birkhoff-go`, on a
  bound that each shorter ring lowers) until `birkhoff-maps` names the
  maps of the check, so that one `Reduces` names all of them; its glue
  `birk-glue` reads the fields of `birkhoff-ring` off a `BirkW` and turns
  its `False` into a colouring. It takes `BirkhoffChecks` as an argument.
  nontrivial_cycle2 (`nontrivial-cycle2`, a plain lemma: a ring x :: y,
  y not the edge image of x, is nontrivial for 0 in a planar bridgeless
  plain cubic map) and double_dart (`double-dart`: two distinct darts on
  one face whose edge images are on one face give a `Reduces`, through
  the ring x :: edge y of `srcycle-ring`). That these statements match
  Coq's has been checked only by reading.
- `birkhoff3.sl` (load after `embed.sl`, in the chain below): as far as
  both compilers check it, minimal_counter_example_is_cubic of
  `coloring.v` with minimality as data, and `embed.sl`'s `BirkGeo` from
  one hypothesis. `cubic-reduces`: a `Pbpp` map is cubic, or reduces,
  through `cubic-glue`, to the one map left by WalkupE at the two darts x,
  y of a node cycle of order 2 (an order of 1 contradicts bridgelessness,
  `orders-three`). The cut is made in two stages: WalkupE twice with the
  darts kept as fixed points (`walk2`, `Walk2`), then two WalkupEs at
  those fixed darts, which only renumber (`drop-two`, `Drop2`, with H
  sending the darts of the smaller map to those of the map off x and y,
  and t back). The smaller map is planar from `walkup-e`'s genus bound,
  and bridgeless, plain and precubic through H (`cut-pbpp`); a
  four-colouring of it gives one of the map (`lift-color`), with x and y
  coloured as the faces they lie on, or 0 and 1 when e x = y and the two
  faces are x and y alone (`XYCol`). `birk-geo` gives `BirkGeo` from
  `MinArity`, birkhoff.v's min_arity at every dart with minimality as
  data, stated whole-map as `Pentagonal` or a `Reduces` for a planar
  bridgeless plain cubic connected map with a `NoColoring`, which
  `minarity.sl` proves. That these statements match Coq's has been checked
  only by reading. Chain (both compilers, about 75 s with slc in one run): that of
  `embed.sl` below, with `red/bcheck cpcomp` after `red/ccheck`, and
  `cpgeom ringdec traceconv birkhoff birkfit birkhoff2` after `revsnip3`
  (before `unav/realias`), then `embed.sl birkhoff3.sl`.
- `minarity.sl` (load after `birkhoff3.sl`, in its chain): min_arity of
  `birkhoff.v` with minimality as data, through the spoke ring, as far as
  both compilers check it. `order-list`: every dart has an order under a
  permutation, so every map has the `OrderList` of its faces that
  `Pentagonal` asks for. For a dart x whose face has k < 5 darts,
  `ring-build` gives the spoke ring, the darts face (edge u) for u on the
  face of x read along the inverse of face from x, as a `Ring` of at most
  k darts (scycle_spoke_ring, and size_spoke_ring as a bound), or a
  `Reduces` from `double-dart` when two of them share a face; `sr-in` and
  `sr-hit` give mem_spoke_ring, and `sr-diskf` and `disk-on` the parts of
  diskF_spoke_ring that min_arity uses (x is in diskF; a dart of diskN on
  no face of the ring is on the face of x). `face-small` follows
  min_arity: a dart on neither the face of x nor a face of the ring is in
  diskFC, so the ring is nontrivial for 0 and `birkhoff-reduces` applies
  (`cover`); otherwise the map is four-coloured, which `NoColoring`
  refutes. The colouring is not Coq's: a face takes `col5` (0, 1, 3, 2, 3)
  at its position in the list of the face of x followed by the faces of
  the ring, so the one chord it needs absent is one from the face of the
  second spoke to that of the fourth, in a ring of four (`chord`, the use
  of chordless_spoke_ring here: the ring of three darts through that
  chord is nontrivial for 0). `min-arity` gives `MinArity` and
  `birk-geo-of` gives `BirkGeo`, each from a `BirkhoffChecks` argument,
  which `red/bproof.sl` proves. It reads snip.sl's
  `DPath` and walk.sl's `Sub`, which `unav/` files define again, as
  `SDPath` and `WSub`, names the end of `birkhoff2.sl` keeps for it. Not
  ported: the rest of the SpokeRing section (fband_spoke_ring,
  chordless_spoke_ring in general, and the adjacency lemmas after it;
  `evalid.sl` proves adj11_edge another way). That these statements match Coq's has been
  checked only by reading. Chain (both compilers, in one run about 72 s
  with slc and 136 s with the reference compiler): that of `birkhoff3.sl`,
  then `minarity.sl`.
- Still open: the rest of part B.
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
  trees together with their certificates; the last level of its
  `ct-build` counts the matches of all three colours in one pass over
  the parent's list (`pcnt3-c`) rather than splitting the list. The
  closure loop of `red/kempe.sl` (`ktc-u`, which `ktc-c` wraps) holds
  ctu and gtu as a `UTree` and a `UGtree`, trees whose nodes have unique
  fields, so that `ctree-restrict-u` and `gtree-restrict-u` rewrite the
  nodes in place instead of building new trees; `UT` and `UG` relate
  them to the ctree and gtree that `KR` is stated on, and `ktc-c`
  converts at both ends (`ut-of`, `ug-of`, `ct-of`, `gt-of`), so that
  its signature is that of the loop on ctrees and gtrees; `kempe-tree-c`
  calls `ktc-run`, which does not convert the gtree back. Both
  restrictions return, with whether the tree they leave is empty,
  whether it is the tree they were given, at its slot (`KeepAt`,
  `GKeepAt`), and a node whose children all stay in place is rebuilt
  with every store skipped (DESIGN.md §37). The runtime functions of the two
  restrictions and of `ct-build` take a list of restrictions as an
  erased `List (Rx T)` together with an `RxL T` of it, a list whose
  cells hold each restriction's stack and tree, so that the relations
  stay stated on the `List (Rx T)`. `red/bridge.sl` takes that
  co-closure to one on complete traces stated after `chromogram.v`
  (`KCC`), and `KCC` to `Kempe_coclosure` for every set closed by
  functions at a given level (`kcc-coclosure`, by a function at a level
  the caller gives, after that level and after `KCB`).
  `red/check.sl`'s `kempe-tree-chk` builds the Kempe tree of the ring
  traces from `cpcolor-c` with its soundness evidence. `red/gramrot.sl`
  ports gram_rot and both directions of match_gram_rot of `kempe.v`.
  `red/cfred.sl` states C_reducible of `coloring.v` on the configuration
  maps (`CRed X`, by a function at a level X) and proves
  check_reducible_valid from a Kempe half
  (`KHalf`) and a contract half (`ContractOK`), both stated against the
  Kempe tree rather than a contract tree. The contract half does not go
  through cfctr: `red/ccomp.sl` follows, for programs of R, Y and H
  steps (`RYH`), the traces that the steps, from the end of the program
  (`revs-c`), make of each candidate of the empty trace, depth first,
  and checks as it reaches each ring trace that its even normal form,
  without its first entry, has multiplicity zero in the Kempe tree
  (`dfs-c`, with the evidence `Good`); no list of traces is built.
  `good-out` gives that check for every trace the steps reach (`FR`),
  and `trace-reach` and `cccol-hit` show that the ring trace of every
  contract colouring is one (`contract-ok`). In test runs, ten broken
  variants were rejected: a restriction claiming that a tree it replaced
  stays at its slot (three ways), a node rebuilt with every store
  skipped when a child moved, a restriction consing onto another
  child's list, `dfs-c` accepting a trace of nonzero multiplicity,
  starting from no candidate or following a child's candidates for fewer
  colours, `good-out` without the equation of the two candidates, and
  `cccol-hit` with another reversed program. `red/ccheck.sl` defines the contract
  of a configuration on these dart numbers (`CfContract`, after
  cfcontract and ctrenum of `cfcontract.v`; written for this numbering,
  not checked against Coq's), decides `ValidContract` on the concrete map
  (`valid-c`), and puts the pieces together (`red-c`, `Reducible`).
  The callers give these functions their levels, so that code at a
  fixed level can use `CRed`: for a set closed at a level
  L, `CRed X`'s function gives a `KCoclo L Y`, whose function at a level Y
  meets the set, from a `CoLv L Y`, levels R and W for the rotation
  (`kclosed-rot`) and the walk (`kcc-coclosure`) with `COB` and L before
  R, R before W and W before Y. A caller at a level K mints R, W, Y and
  then K at the top level after L, and needs X before K. The fixed
  top-level levels are `KCB` (`red/bridge.sl`), `COB` and `KHL`, that of
  the Kempe half (`red/cfred.sl`), `CGL`, that of the contract half
  (`red/ccomp.sl`), and `CRX` (`red/ccheck.sl`), at which `red-c` builds
  `Reducible CRX`. In a test run with both compilers, a function at a
  fixed level built this way from a `CRed CRX` and a `KClosed` checked,
  and three broken variants of it (K or L minted too early, or X a
  parameter) were rejected.
  `red/pieces.sl` (load after `red/chunks.sl`) cuts the configurations
  into the pieces `pcs` (`cut-at` on `config-srcs`, by the sizes
  `piece-sizes`, then `decode-all`), and `allredc-pieces` turns `AllRedC CRX pcs` into
  `AllRedC CRX css`. The sizes were chosen offline (not in the repository)
  from one run's measured time per configuration, so that each of the 100 pieces
  takes at most about 10 s by that measure; any sizes give a correct proof, only the
  balance depends on them. Run outside `native-compute`, as separate
  processes one at a time on a 4-core cloud VM shared with other runs,
  the 100 pieces took about 665 s of user CPU in one run, against about
  800 s in a run side by side with it of the code before the `RxL`
  lists, the skipped stores and `dfs-c` (about 770 and 795 s in two more
  runs of that code; ring-14 configurations about 470 s against about
  565 s). In earlier runs, that code took about 705 to 730 s, and, in
  one run each, about 625 s with `OCAMLRUNPARAM=o=400` (which the jobs
  of `native-compute` appear to inherit with the rest of slc's
  environment) and about 640 s with the program compiled with
  `-inline 200` (`--inline`, MANUAL.md); the code before the in-place
  closure trees took about 850 s in one run. `red/proof-c.sl` proves `AllRedC CRX css`
  (`all-red-proof`) for css the chunks of `red/configs.sl`
  (`red/chunks.sl`), with one `native.sl` job per piece, and
  `red/goal-c.sl` runs the jobs and sets and discharges the goal: every
  configuration appears to be C-reducible, in the sense of `CRed`, with
  its contract. Load order: `std/macro.sl native.sl std/nat.sl
  std/list.sl ring.sl`, then `base map lists planemap walk frontier labels
  hypgraph hypperm hypermap hypplane hypeuler hypderived hyprelabel
  hypwalkup hypgeom` (each `.sl`), then `cfmap.sl red/red.sl cpmap.sl
  red/color.sl cfcolor.sl red/ctree.sl red/gtree.sl red/grestrict.sl
  red/crestrict.sl red/kempe.sl cpcolor.sl red/configs.sl red/bridge.sl
  red/init.sl red/check.sl red/gramrot.sl red/cfred.sl red/ccomp.sl
  red/ccheck.sl`, then `red/sanity-c.sl`, or `red/chunks.sl red/pieces.sl
  red/proof-c.sl red/goal-c.sl` (with `--goal proved`). In that chain the
  goal was proved with slc (about 385 s of wall time) and with the
  reference compiler under `ulimit -s unlimited` (about 395 s) in one run
  each, side by side, on a 4-core cloud VM shared with other runs, so the
  times say little about either compiler. What `CRed` and `ValidContract` state has not
  been checked against Coq's C_reducible and valid_contract beyond
  reading them.
- `red/configs.sl`, `red/chunks.sl`: the 633 configurations as one string
  literal each (`config-srcs`, written by `red/gen.py` from
  `configurations.v`), `DCfgs`, a relation reading a string's bytes as
  configurations, and `DecList` and `DecAll`, which read a list of strings
  and a list of such lists; `dcfgs-fn`, `declist-fn` and `decall-fn` show
  that they determine what they read. `cut-at` cuts a list by sizes, with
  its `Flatten`, and `flat-dec` carries a cut of `config-srcs` over to the
  configurations. `red/chunks.sl` cuts `config-srcs` into chunks of 20
  (`chunk-srcs`) and binds css to what `decode-all` reads from them at
  elaboration, with its `DecAll` (`css-dec`); `red/pieces.sl` does the same
  for its pieces (`piece-srcs`, `pcs`), and binds `cfs-all` to all of
  `config-srcs` read in order, with the `Flatten` of css and of pcs to it
  from `flat-dec`. A native job is given a group's strings, not its
  configurations: it decodes them and checks the result, answering a
  `Decoded P ss` (a list `DecList` reads from `ss`, with `P` of it), and
  `on-chunks` turns one for each group of a cut into `P` of each list its
  `DecAll` gives (`OnChunks`). So the program `native-compute` compiles
  holds the strings (about 100 KB of source) rather than the
  configurations as built values; see the `fcproof.sl` entry for what
  that seems to change. `config-chunks` decodes the chunks for the runs
  that do not need the proof. In test runs, four broken variants were
  rejected: a job claiming the tail of the list it decoded, `on-chunks`
  without `declist-fn`, `flat-dec` without `dcfgs-fn`, and a decoder
  reading byte 2 as `SH` with the proof of `SY`. Decoding at elaboration
  and printing gave the same chunks as the configurations written out as
  terms did.
- `red/bcheck.sl`, `red/bproof.sl`, `red/bgoal.sl` (load after `red/ccheck.sl`, with `native.sl`
  before `red/bproof.sl` and `std/macro.sl` first): the
  Birkhoff check of `birkhoff.v`. `birkhoff-check-c` runs Birkhoff_check2
  from the initial trees, for ring size h + 2, kernel size m, an
  iteration count and a list of basis programs, and returns a certificate
  `BirkhoffCheck h m`, which also records Birkhoff_check1 for each program
  (`BkProg`, with the program's tree from `cpcolor-c`). Its parts are
  ctree_pick_rev (`pick-c`), ctree_of_ttail (`ttail-c`, with `tt-allp`
  for the direction of ctree_of_ttail_mem that `birkhoff.v` uses) and the
  closure loop of `red/kempe.sl`, whose evidence (`KR`, `CR`) names no
  predicate, so that one run serves every predicate; `kr-kv` turns it into
  `KV`, the validity half of Kempe_tree_closure_correct. `KVBase` and
  `CKBase` play the parts of Kempe_valid_init and Kempe_valid_restrict,
  and `kempe-sound` that of Kempe_validP. `birkhoff-check-sound`, a level
  factory, proves the part of Birkhoff_valid that rests on the check: for
  two sides `BSide` (a Kempe-closed set T of complete traces, a decision
  between T and a set NT disjoint from it, and, for each basis tree of the
  check, a trace in T whose even normal form is in the tree) related by
  `BGlue` (no trace of one side has its reverse in the other), the fields
  of a `BirkhoffCheck` give `False`. `bproof.sl` proves `BirkhoffChecks` (`birkhoff-proof`), which `bgoal.sl` sets as a goal,
  Birkhoff2 to Birkhoff5 with Coq's iteration counts and basis programs;
  in one run the computation took about 6 s under the reference compiler.
  `birkhoff.sl` builds the sides and the glue; `BkProg` carries
  `cpcolor-c`'s evidence of both halves, and `cpcomp.sl`'s `bkprog-hit`
  gives the `CtMem` that a `BSide`'s third field asks for.
- `unav/`: an unverified port of the unavoidability check (the
  presentations of hub arities 5 to 11, hubcaps, `redpart` through the
  quiz tree, and the bound for larger hubs). In one run every script
  passed, in about 4.4 s of compute; five broken variants of the arity-5
  script were rejected. It carries no proofs yet. `data.sl`, which
  `gen.py` writes from the Coq sources, spells each presentation script
  as a string of numbers that `present.sl`'s `script-of` reads at run
  time; as nested constructor applications the scripts made about 13 MB
  of the 21 MB of OCaml that `native-compute` wrote for `qztgoal.sl` in
  one run.

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
- `unav/qfit.sl`, `rdart.sl`, `redc.sl` (load after `unav.sl` and
  `data.sl`, in that order): a certified redpart.
  `qfit.sl` states fitq and qzt_fit of `quiz.v` and `quiztree.v` on the
  hypermaps of `hypermap.sl` (`QztFit`, `HasFit`). `rdart.sl` names the
  darts around a hub by a face (hub, spoke, hat or fan of a sector) and
  a number of face steps from or back to that face's base dart, and
  reads edge off a table of base darts or through the identities
  e = f e f e f and e = f' e f' e f' (f' the inverse of face), which
  `e-rot-a` and `e-rot-b` prove for plain cubic maps. `redc.sl`'s
  `redp-c` follows redpart.v's search (the hub, hat and fan nodes of
  each sector, a leaf of the quiz tree fitting the range tops, then the
  part narrowed at every tested range) and returns evidence `RedD qt p`;
  `red-sound` turns it into the contrapositive of no_fit_redpart: a dart
  fitting p exactly in a plain cubic pentagonal map gives a dart where
  qt fits. It is a new search on these names, not a port of redpart.v's
  zippers, and a tested range is narrowed to its top for the rest of the
  walk. For each triple of darts `tri-c` works out once where the walks
  of the leaves' quizzes start (`start-c`), and a leaf's walk reuses that
  start while the part is unchanged (`test-c` and `qwalk-c` report
  whether it is); a leaf whose first question cannot pass there is not
  walked (`walk-hope`).
- `unav/qwalk.sl`, `qembed.sl`, `qcert.sl`, `qtree.sl`, `qmirror.sl`,
  `qztcfs.sl`, `qztproof.sl`, `qztgoal.sl` (load after `redc.sl`, in that order; they also need
  `cfmap.sl`, loaded after `hypcubic.sl`, and `cpmap.sl`, loaded after
  `red/configs.sl`): the quiz half of the embedding. `qwalk.sl` states
  walkq and fitqz of `quiz.v` as relations (`WalkS`, `FitZ`). `qembed.sl`
  ports the QuizEmbedding section of `quiz.v`: `quiz-preembedding` takes
  a certificate `QzCert` of a configuration map Gc and a fit at a dart
  x0m of its quiz in a plain cubic map Gm (`Geo`, which also asks every
  face to have more than four darts), and gives a dart map
  `hl` sending x0c to x0m that is a `Preembedding` of the kernel of the
  ring (`KernelList`). These are list forms written for this port, after
  coloring.v's preembedding and geometry.v's kernel: at each kernel dart
  h commutes with face and keeps the arity, the face has an edge-central
  dart, and node (face x) is joined to every kernel dart by an rlink
  path of central kernel darts (this asks more than rlink_connected,
  which appears to ask it only for central darts). Where Coq's
  valid_quiz asks that the walk be simple and band the kernel, the
  certificate names the place of every kernel dart (a walk face and a
  number of face steps) and a path from each walk face to face 0 and
  back, so the parts of embedqz_central and embedqz_rlinked about Gc
  are checked on the concrete map; hc_walk, the part about Gm, is proved
  for any plain cubic map (`hc-walk`). `qcert.sl` decides the
  certificate on the maps `cpmap-c` builds (`cfqz-c`). `qtree.sl` builds
  the quiz tree by the steps of `quiz.sl` with evidence that every
  stored triple is a rotation of one from the quiz of a configuration
  with a certificate, or from its mirror image (`QInv`), and proves
  qzt_fit_cfquiz (`qzt-hit`). `qmirror.sl` proves the mirror of a plain
  cubic map plain cubic with the same arities (`geo-mirror`) and
  fitqz_flip (`fitz-flip`). `qztproof.sl` proves `UnavE cfs`
  (`unav-proof`) for the `cfs` in scope, which `qztcfs.sl` binds to the
  configurations of `red/configs.sl` by `concat-cfs` and `fcopen.sl` by
  `concat-c`; its jobs read cfs through the `cfs-run` in scope (in
  `fcopen.sl`, a decoding of `config-srcs`), and `qztgoal.sl` sets it as a goal and discharges it: every
  plain cubic connected pentagonal map of genus 0 has a configuration of
  `cfs`, with its map, ring and arities as `cpmap.sl` builds them, whose
  kernel has a preembedding into the map or into its mirror
  (`CfEmbed`). The walk of each arity is cut into regions
  (`cut-script`: the largest subtrees of 100 to 800 leaves, and the rest
  of the walk with those left as `SCut`), and `qztproof.sl` queues one
  `native.sl` job per region (`reg-c`) and one for the cap checks
  (`cap-run`); each job builds its own quiz tree from the cfs that
  `cfs-run` gives it (`cfs-tree`), so no job refers to cfs but through `cfs-run`. A region's job walks
  its subtree from the context check2-c reaches there, runs `redp-c` on
  its obligations, and checks that its cut list (the parts of the earlier
  regions of its walk, which `SCut` and `PCut` refer to) is made of parts
  of the regions after it in `regs`; `reg-claim` follows a dart of
  positive dscore from the region of its walk's root through those
  parts to the region whose obligations cover it. The load order below
  appears not to elaborate any more: `red/configs.sl`'s `take-app` reads
  the `CatNil` of `cfcolor.sl`, which it does not load (an open question
  which chain to give instead). On the chain of `fcfinal.sl` up to
  `fcopen.sl` followed by `native unav/qztproof unav/qztgoal` (each
  `.sl`), `--goal proved` passed with slc in about 54 s in one run on a
  4-core cloud VM shared with other runs (1.5 MB of OCaml, compiled in
  about 6 s; the 22 jobs about 40 s of CPU together, the longest about
  4.2 s). ocamlopt's time appears to depend much on its own GC: on the
  first 3.4 MB of an earlier, larger program for these jobs (its 50,000
  top-level constants) it took about 1000 s by default (peak RSS 0.8 GB),
  980 s with `o=200`, 330 s with `o=1000` (2.5 GB) and 210 s with
  `s=8M,o=200` (1.1 GB), one run each. A run with one reducible leaf of
  the arity-7 script replaced by an empty hubcap was rejected, and on the
  chain above one with each region's first part replaced by its second
  (`p` by `mp` in `regs`) was rejected (in each a job answered `ChkNo`). In a test run the tree built
  this way was the tree `the-quiz-tree` builds (3361 triples, compared
  structurally), and every one of the 633 configurations had a
  certificate. Load order: that of `unavgoal.sl` with `native.sl`
  after `std/macro.sl` (`std/macro.sl native.sl
  std/nat.sl std/list.sl ring.sl`, `base` to `hypcubic`, `cfmap.sl`,
  `colalias.sl unav/faces.sl red/red.sl red/configs.sl cpmap.sl`, then
  `unav/` `part quiz redpart hubcap present fit dbound hubcapc obsmap
  dscore dsum posz pwalk hubsound pwsound conv cap unav data`), then
  `unav/qfit.sl rdart.sl redc.sl qwalk.sl qembed.sl qcert.sl qtree.sl
  qmirror.sl unave.sl qztcfs.sl native.sl qztproof.sl qztgoal.sl` with `--goal proved` (`unave.sl` holds
  `UnavE`, `CfEmbed` and `MapOrMirror`, so that `embed.sl` can load
  without the goal). Not done: embed.v (from the preembedding to an
  embedding), the radius and ring-arity checks of embeddable that
  cfquiz.v also makes, and the contradiction with C-reducibility; how
  `embed.sl` puts the rest together is in its entry below.
  Whether `Preembedding`, `KernelList` and the mirror match Coq's has
  been checked only by reading.
