# Lazy strides in the Skelet #1 run

This note describes how `main-run` in `bb/sk1.sl` keeps strides lazy.
The cost figures are from single instrumented runs on one machine and
should be read as rough.

## Background

`main-run` follows the Coq proof `BusyCoq/Skelet1.v`: about 88 million
symbolic steps over configurations `MkCf d l r`. On rightward steps it
first tries a stride, `tstride az 1 r`, a single pass over the whole
right tape (a few hundred symbols). Strides are a large share of the
steps, and most of the right tape seems to be touched only by strides.

## The lazy runner

`lrun` keeps the right tape as an explicit window `w`, an implicit `D`,
and a stack `Zk` of segments. Each level holds a segment, a pending
stride count (`Pn`: none, or `PnP q`) and a capacity estimate; levels
are separated by implicit `D`s, and the bottom level `ZkB` is a raw tail
with no `D` after it. The relation `Dn k x` says the stack stands for
the explicit tape `x`: each level's segment, followed by `D` and the
level below, strided by the level's pending count. Splitting just after
a `D` makes the carry into the next level 0, so striding a level by `q`
should equal striding its segment by `q` (`Swin`, `sw-of`) and the level
below by the multiplier that comes out (`sw-st` proves this).

The runner's moves:

- a stride over the window (`LzS`) runs `sw-of` on `w` only and adds the
  multiplier to the top level's count (`Kt`, `Pq`), after checking it
  against the top level's capacity;
- ordinary steps run on the window (`LzT`); the frame lemmas under
  `trun-fr` carry them to the full tape;
- when the window gets short, or the top capacity runs out, `lp-of`
  exposes the top level (`LzP`): it strides just that segment by its
  count and adds the resulting multiplier to the level below;
- when a stride succeeds and leaves a window of 16 or more symbols,
  `lz-fold` splits that strided window at its first `D` at offset 6 or
  more and moves what follows back onto the stack as segments of about
  96 symbols with no pending count (`LzF`, chunked by `ch-of`);
- entering the lazy runner (`lz-enter`) chunks the tail the same way
  (`LzB`), and the first lazy step is a stride.

The capacity of a level is `ms-k` of its segment, given the capacity of
the level below, minus its pending count. It is only a runtime estimate:
if it is too generous, a later stride of a segment fails and the run
returns `RFail`, which would show up as a failed job, not as an unsound
result.

Leaving the lazy runner (`lz-go`, used when the configuration matches
the `try-uni` or `cyc-of` pattern, or when no lazy step applies) calls
`den`, which pushes the counts down level by level and strides only the
bottom level with `tstride`, so it should cost about one pass over the
tape. The `MRun` for the lazy stretch is rebuilt from the erased log
`Lz` by `lz-force`, using `st-add` to split summed strides back into
single strides.

## Measurements

In one instrumented run, before the stack was added (a single raw tail
with one pending count), the window averaged about 100 symbols, `sw-of`
took about half of the job's instructions, and there were about 61
thousand forces, about 54 thousand of them from capacity. With the
stack there were about 14 thousand forces (about 6.4 thousand from the
`try-uni` pattern), and elaboration plus the Skelet #1 job took about
18 s user instead of about 45 s.

With the fold applied to the strided window and the sizes above, in one
set of measurements on a 4-core container the Skelet #1 job took about
12.4 s user, where folding the unstrided window (and striding its prefix
again) at 16 symbols with segments of about 8 took about 16.2 s. The
sizes came from a sweep of variants of the generated OCaml; fold lengths
from 12 to 16 and segment sizes from 64 to 128 measured within noise of
each other.

## Failing strides

After a stride of the window fails, `lstep`'s next step either removes the
window's first symbol (a `D` moved left by `r-dr`, or an `X` or `G` block
with a false flag moved left by `ac-mvr`) or pushes a segment onto the
window's end. Neither seems able to make the stride succeed: dropping a
`D` or `G` at the front changes no later segment, dropping an `X` only
lowers the carry into the first `C`, and the push adds symbols after the
point where the stride failed. `LsGo` carries a flag saying that the
window's stride is known to fail, and `lstep` then skips `sw-of`.
Skipping a stride needs no proof, since a failed stride produces none, so
a wrong flag would change the course of the run but not what it proves.
In one instrumented run about 18.7 million strides were skipped, and
running `sw-of` on each of them anyway found none that succeeded; the
Skelet #1 job took about 10.5 s user, against about 12.4 s without the
skip.

## What is left

In one instrumented run with the skip, `sw-of` made about 343 million
steps: about 219 million in about 17 million strides that succeeded, about
84 million in about 7 million that failed and were not skipped, and the
rest in strides of stack segments. `sw-of` was about 21% of the job's
instructions, with `push-ex`, `lenge`, `lstep`, `Z.add` and `rapp-of`
next at about 6 to 8% each. Things that did not help in one measurement
each: also folding on leftward steps; a non-allocating pre-check before
`sw-of`, before every stride or only after a failed one (a scan of the
list seems to cost about as much per symbol as the stride); and
remembering the failing segment by the identity of its first cell, which
predicted most failures but whose walk to that cell cost about as much
again.

`bb/sk1a.sl` is an experiment that keeps the window in a tag buffer and
a count array instead of a list (`main-run-a`), still folding before the
stride and without the skip; in one measurement its job took about 16.0 s
user, so it is not used. Its stride costs less per symbol than `sw-of` in
a micro-benchmark, but writing counts, appending and reading cells back
into lists for the stack took more than that saved.
