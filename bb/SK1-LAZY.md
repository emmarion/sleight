# Lazy strides in the Skelet #1 run: a nested design (idea, not built)

This note describes a possible further speedup of `main-run` in
`bb/sk1.sl`. Nothing here is implemented, and the claims about cost are
estimates from profiling, not measurements of a built version.

## Background

`main-run` follows the Coq proof `BusyCoq/Skelet1.v`: about 88 million
symbolic steps over configurations `MkCf d l r`. On rightward steps it
first tries a stride, `tstride az 1 r`, a single pass over the whole
right tape (a few hundred symbols). Strides are about 14 million of the
steps. Between two strides the head seems to read under two right-tape
symbols on average, with rare excursions of about 120. So most of the
right tape is touched only by strides.

The run in `bb/sk1.sl` makes strides lazy at the runner level:

- the right tape is kept as an explicit window `w`, an implicit `D`, and
  a raw tail `t` that still owes `p` strides, so the real tape is
  `w ++ D :: stride(0, p, t)`;
- a stride runs only over `w` (`sw-of`, relation `Sw`) and adds its
  multiplier to `p`;
- ordinary steps run on the window, and frame lemmas (`trun-fr` and the
  lemmas under it) carry them to the full tape;
- forcing does one real `tstride az p t`; the full `MRun` for the lazy
  stretch is then rebuilt from an erased log (`Lz`), using `st-add` to
  split the summed stride back into single strides.

A second design, also built and also passing both BB(5) goals but not in
this tree, puts the laziness in the tape instead: a symbol `YL p c u`
standing for the tape `u` strided `p` times, with `c` strides of
capacity left. Its meaning is a `Tp` case (`TpL`) carrying
`St 0 (p + c) u w` for some `w`, so a stride over a tape ending in `YL`
costs only the explicit prefix plus a check against `c`. Forcing uses a
functionality lemma (`st-fn`: `St xs n t t1` and `St xs n t t2` give
`t1 = t2`). Its measured job time was about the same as the runner-level
design.

## What both designs leave on the table

In both, forcing is one real stride over the whole lazy tail, which is
O(tape). In the tape-symbol design an instrumented run showed about
360 thousand force-and-relazify cycles, each a few full passes over the
tape. These are probably a large part of the remaining cost of the
Skelet #1 job.

## The idea: nest the lazy segments

The two designs supply complementary halves.

- **Nesting, from the tape symbol.** Because `YL` is an ordinary symbol
  with its meaning in `Tp`, the tail `u` can itself end in another `YL`.
  The right tape then becomes a chain of segments, each owing its own
  number of strides:

  ```
  w1 ++ YL(p1, w2 ++ YL(p2, w3 ++ YL(p3, ...)))
  ```

- **Splitting after a `D`, from the runner design.** Splitting just
  after a `D` makes the carry into the tail 0. Then striding
  `segment ++ rest` by `n` should equal striding the segment by `n` and
  striding `rest` by `n * 4^k`, where `k` is the number of `C` symbols in
  the segment (`sw-st` proves the corresponding fact for the window).

Together these would make forcing local. Exposing the next segment means
striding only `w2` by `p1` and adding `p1 * 4^k` (with `k` the number of
`C`s in `w2`) to `p2`, after a capacity check. That is O(segment), not
O(tape). It is lazy propagation, as in a segment tree.

The template jump in `try-uni`, which strides the right tape by
`n * 215779`, could also stay lazy by adding to the outermost pending
count when the capacity allows, rather than forcing. The capacity
estimate `ms-of` would read the explicit prefix and the outer segment's
capacity.

## What it would take

- A `Tp` meaning for nested `YL`, which the tape-symbol design almost
  has already, since `u` is an arbitrary tape.
- A lemma pushing a pending stride one level down: from
  `St 0 p (w ++ YL(q, c, u)) h`, where `w` ends just after a `D`, derive
  the meaning of `stride(0, p, w) ++ YL(q + p * 4^k, c - p * 4^k, u)`.
  This combines `sw-st`-style composition with `st-fn` and `st-add`.
- Capacity bookkeeping per segment, and a rule for when to split a long
  explicit window into a new segment.

## Expected value

On its own this would probably cut the Skelet #1 job well below its
current time. But that job runs in the same parallel batch as the BB(5)
search-tree jobs, which seem to set that batch's wall time (about
175 s on 4 cores at the time of writing). So the nested design would
change the end-to-end check time only once the tree jobs are much
faster. Until then it is mainly of interest as the cleanest form of the
lazy-stride idea.
