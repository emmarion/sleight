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

- `map.sl`: `PlaneMap`, `Colored`, `FourColorMap`. `map-triangle.sl`
  builds a triangle as a `PlaneMap`, as a check of the definitions.
- `ring.sl`: `ring-check`, a normaliser of `Expr` to sorted lists of
  monomials, and `ring-sound`, which turns equal normal forms into
  `(Eq (Nat) n1 n2)` for any two `Eval` derivations; `ring-test.sl`
  uses it on (a+b)(a+b). `orient.sl`: Knuth's CC axioms 1, 2, 4 and 5
  for `Left` (`left-rot`, `left-antisym`, `left-interior`, `left-trans`)
  and, in place of axiom 3, `left-dec`, which decides between `Left p q r`,
  `Left q p r` and `Collinear p q r`; `orient-test.sl` states them as a
  goal. Both test files pass `--goal proved` under slc and the reference
  in the runs this session made.
