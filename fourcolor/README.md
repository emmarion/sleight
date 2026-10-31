# The four colour theorem in Sleight

This directory holds a proof of the four colour theorem, for straight-line
drawings, written in Sleight by Claude sessions working without the owner.
Its combinatorial part follows Gonthier and Werner's Coq proof (see
NOTICE.md). STRUCTURE.md describes the proof's structure and each file's
role; this page says how to check it.

## What is proved

- `fcfinal.sl`: the goal `(goal erased (FourColor))`, with `FourColor` as
  `defs.sl` states it: every drawing (a list of straight edges between
  distinct points, any two of them compatible in the sense of `defs.sl`'s
  `Compatible`, which appears to mean they meet at most at a shared
  endpoint) has a colouring of its points with four colours in which the
  endpoints of every edge differ.
- `fcmanyfinal.sl`: the goal `(goal many (FourColorM))` of `fcmany.sl`, the
  same theorem as a program. Its function, not erased, takes the edges
  and returns a colouring; the drawing's certificate and the colouring's
  properness are erased. The program is a search (`paint.sl`), exponential
  in the number of points, so it is a demonstration rather than a usable
  colouring algorithm.

Each is proved in one unit, with no hypotheses and no axioms of its own.
That proof appears to rest on:

- the compilers' type checking and the elaborator's evaluator;
- the compiled runs of `native-compute` (DESIGN.md §29, §72), which check
  the 633 configurations, the unavoidability walks, the Birkhoff checks
  and per-configuration certificates;
- `defs.sl`, which this proof's files did not write, stating the theorem
  intended.

The intermediate statements are meant to follow Coq's; that they match
has been checked only by reading, which appears to bear on NOTICE.md's
attribution rather than on what is proved.

## Running the check

Build the two compilers once (see MANUAL.md's "Build and run" and
`self/README.md`):

```sh
dune build            # the reference compiler, _build/default/bin/main.exe
self/release.sh       # slc, _build/release/slc
```

Then, from the repository root:

```sh
fourcolor/check.sh final slc    # FourColor with slc
fourcolor/check.sh final ref    # FourColor with the reference compiler
fourcolor/check.sh many slc     # FourColorM with slc
```

Each prints `--goal proved: PASS` on standard output on success, with the
goal and where it is discharged as notes on standard error.

The script passes the unit's files (for `FourColor`, three from `std/`
and 137 from this directory) in the order the unit needs, with
`--goal proved` and `--inline 50` (passed on to ocamlopt). It sets
`OCAMLRUNPARAM=o=400` unless the variable is already set; the native jobs
inherit it from the compiler. In one sweep of `FourColorM` with slc, one
run per level, 50 and 100 gave the lowest times, 50 the lowest wall time;
levels from 50 to 200 were within about 1% of each other in CPU, higher
levels lengthened the wall time, and leaving `--inline` out took about a
fifth more CPU. On macOS, both compilers have passed with the default 8 MB stack.

All the checks run inside one `native-compute` (`native.sl`). It writes
one OCaml program of about 2 MB, compiles it once, and runs its 154 jobs
as separate processes, as many at a time as there are cores.

## Time and memory

One run each, so these are approximate. On a 4-core cloud VM that other
jobs were also using (load average about 4), with `--inline 200` and
`ulimit -s unlimited`:

| goal | compiler | wall | CPU | peak resident |
|---|---|---|---|---|
| `FourColor` | slc | about 3 min | about 9.5 min | about 1.2 GB |
| `FourColor` | reference | about 5.5 min | about 11.5 min | about 1.4 GB |

On the VM with slc, about 30 s of the time is elaboration and about 10 s
is ocamlopt; the rest is the jobs, most of it the C-reducibility check of
`red/`. On a machine like it with many more cores, the wall time would
appear to approach the elaboration, the compile and the longest job, about
a minute with slc.

On a 12-core Apple M4 Pro, otherwise idle, with OCaml 5.4.1 and the
default 8 MB stack:

| goal | compiler | wall | CPU | peak resident |
|---|---|---|---|---|
| `FourColor` | slc | about 34 s | about 4.3 min | about 1.4 GB |
| `FourColor` | reference | about 53 s | about 4.6 min | about 1.0 GB |
| `FourColorM` | slc | about 35 s | about 4.3 min | about 1.3 GB |
| `FourColorM` | reference | about 53 s | about 4.6 min | about 1.1 GB |

With OCaml 4.14.1, both goals took, with slc, about 5% more wall time,
about 8% more CPU and about 15% less memory, and with the reference
compiler about twice the wall time, about a quarter more CPU and about
half the memory.

Each check also has a unit of its own, listed in STRUCTURE.md (for example
`red/goal-c.sl` for the 633 configurations alone).
