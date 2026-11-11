# The four colour theorem for drawings with real coordinates

This directory states and proves the four colour theorem of
`fourcolor/defs.sl` for straight-line drawings whose points have
constructive real coordinates, the Cauchy reals of `real/`. It was written
by Claude sessions; the statement in `defs.sl` and `spec.sl` is the
owner's.

## What is proved

`final.sl` discharges `(goal erased (FourColorR))`, which `spec.sl` sets.
`defs.sl` states it by following `fourcolor/defs.sl` constructor by
constructor:

- an `RPoint M` has two `CReal`s at level M as coordinates;
- r is left of pq (`RLeft`) when the shoelace sum of p, q, r, built with
  `CRealMult` and `CRealPlus`, exceeds that of r, q, p by `CRealLt`;
- two edges' shared endpoints (`RShare*`) are equal by `RPointEq`, both
  coordinates `CRealEq` at a level N, and points are apart (`RPointApart`)
  when one coordinate is `CRealAppart`;
- a colouring matches a point to the first painted point provably equal to
  it, skipping points apart from it.

`FourColorR` takes the level M of a drawing's reals and the level N of its
equality proofs, and returns a level and a function from drawings to
proper four-colourings. The proof appears to rest on what
`fourcolor/README.md` lists for `FourColor`, and on `real/defs.sl` and the
statement here saying what they are meant to say.

## Running the check

From the repository root, after building the compilers as
`fourcolor/README.md` describes:

```sh
fourcolor/check.sh plane ref    # or slc
```

It loads the whole `FourColor` proof except `fcfinal.sl`, then `real/`,
then this directory, and prints `--goal proved: PASS` on success. One run
with the reference compiler on a 4-core cloud VM took about 2.5 minutes
of wall time, nearly all of it the `FourColor` proof.

## Structure

`reduce.sl`'s `four-color-r-of` builds `FourColorR` from `FourColor` and
a `Rounding` of each real drawing: a `Nat` drawing whose endpoints
correspond to the real ones, with each pair of real endpoints provably
equal, with one grid point, or apart. `pullback.sl` reads the real
colouring back from the `Nat` one. `round.sl`'s `rounds` builds the
`Rounding`:

1. `pairs.sl`: every pair of a real drawing's endpoints is equal or apart,
   using `pointkit.sl`'s `PointKit` and `approx.sl`'s `LeftKit` (a point
   strictly left of pq is apart from p and from q).
2. `reps.sl`: each endpoint's representative, the first endpoint equal to
   it, so that equal endpoints get one grid point.
3. A threshold certificate for every strict inequality of the drawing,
   computed once (two calls of one function cannot be shown to agree), and
   an index j below all of them.
4. Each endpoint becomes its representative's terms at j, a rational
   point near it; `approx.sl`'s `left-approx` shows that left turns
   survive this, and `real/creal.sl`'s `creal-lt-near-at` that apartness
   does.
5. `grid.sl` scales and shifts the rational points onto the `Nat` grid,
   keeping left turns, apartness, and equal points.

Lemmas that call a real's functions are factories over the levels of the
reals and of the equality proofs (DESIGN.md §57), returning functions at a
level minted after them.

`example.sl`, which the check does not load, builds constant reals and the
`RDrawing` of an edge and of a triangle, to show the hypotheses can be met.
