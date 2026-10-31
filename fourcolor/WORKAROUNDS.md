# Workarounds and wishes

Written by Claude sessions working without the owner. Each item below is
something the proof in this directory does in a roundabout way, because
of how Sleight or its compilers behave as these sessions understood them,
followed by what would have made it unnecessary. Nothing here is a design
decision: the wishes are proposals for the owner, and the readings of the
language behind them may be wrong. Numbers are not reused.

## Levels and functions held in data

1. **Functions stored in data cannot be called.** A function that is a
   field of a value has a level that was minted elsewhere, so code
   defined earlier cannot call it (DESIGN.md §17–§18). Facts are
   therefore given as first-order certificates, not as functions. For
   example, `map.sl`'s labelling certificates stand in for negations, and
   `coloring.sl`'s `NoExt`, `ringdec.sl`'s `RTNo` and `induct.sl`'s
   `NoColoring` stand in for refutations. Where a function must be passed,
   it goes through a level factory: a function that takes the levels it
   needs and returns a function minted after them (`parta.sl`,
   `minarity.sl`'s `min-arity`, `fullred.sl`'s `full-red-of`).
   *Wish:* a way to call a function held in data, or a documented pattern
   for this, so that certificates are a choice rather than a necessity.

2. **Minimality enters as data.** The induction on darts (`induct.sl`'s
   `col-all`) is one recursive function, and every function minted while
   it runs is at a higher level than it, so it cannot call them. The
   minimal-counterexample argument is therefore inverted. Each reduction
   (`Reduces`, `ColorFrom`) names the smaller maps it needs, and a static
   glue function at a fixed level turns their colourings into one of the
   map. `birkhoff.sl`, `birkhoff2.sl`, `embed5.sl`, `notembed.sl`,
   `contract2.sl` and the rest return `Reduces` instead of calling a
   minimality hypothesis.
   *Wish:* a form for well-founded induction whose step may receive the
   induction hypothesis as a callable value.

3. **C-reducibility at fixed top-level levels.** `CRed`'s co-closure
   function has to be callable from glue code at a fixed level, so it is
   indexed by levels minted at the top level of the `red/` files (`KCB`,
   `COB`, `KHL`, `CGL`, `CRX`). Callers build `CoLv` evidence to reach it,
   as PLAN.md's section on C-reducibility and levels describes. This is the same
   issue as item 1.

## One goal per unit, one long unit

4. **One goal per unit.** A unit may set only one goal, so each computed
   check is split into a proof file, which leaves its proof as a
   top-level value (`red/proof-c.sl`, `red/bproof.sl`,
   `unav/qztproof.sl`, `embed4proof.sl`, `fcproof.sl`), and a goal file
   of two or three lines.

5. **Names collide across the ~140 files of one unit.** All files share
   one namespace, so a later file's `Perm`, `Sub`, `Or`, `SNil`, `AppNil`
   or `InsertE` hides an earlier one for every file after it. The proof
   works around this with:
   - alias files: `colalias.sl`, `realias.sl`, `unav/realias.sl` and
     `iealias.sl`;
   - aliases appended to the ends of files: `CRPath` in `cpmap.sl`;
     `SDPath`, `WSub` and `hsplit-cover` in `birkhoff2.sl`;
   - renames: `cpcomp.sl`'s `StNil`/`StCons`, `cfcolor.sl`'s
     `CatNil`/`CatCons`, `ring.sl`'s `Ins` and `PMulNil`/`PMulCons`, and
     `unav/pwalk.sl`'s `InCut`;
   - load-order constraints: `contract2.sl` must load before the `unav/`
     files; `paint.sl` and `fcmany.sl` must load before `coloring.sl`.

   Some of these collisions show up only in the combined unit, as
   errors far from their cause.
   *Wish:* module-qualified names, or a warning when a type or constructor
   name is redefined across files.

6. **Numerals are opaque in types.** A numeral in a type does not unfold
   to `Succ` applications, so types spell numbers as `Succ` chains, and
   `ring.sl` provides lemmas (`unary-4`, `lit-lt-7-9`, ...) that say what
   small numerals are. Expanding the `unary` macro late in the unit costs
   about 95 ms per use under slc, so most uses go through the lemmas.

## Native computation

7. **One `native-compute` for the whole unit.** Each `native-compute`
   statement writes and compiles one OCaml program holding everything
   elaborated so far, whatever its thunk count. `native.sl`'s macros
   (`native-jobs`, `native-each`, `native-then`, `native-run`) therefore
   queue every check's jobs and run them in a single statement, after the
   busy beaver proof's `bb/par.sl`.
   *Wish:* a compiler that emits only what the thunks reach, and that
   compiles one statement while another's jobs run.

8. **Big Settled values are kept out of the native program.** A value
   that non-erased code refers to is written into the program as one OCaml
   `let` per block, and ocamlopt's time grows faster than the number of
   such lets. In one test, 2,500 cells took 4 s and 10,000 took 29 s,
   while one marshalled string of 50,000 cells took 0.27 s. So:
   - the 633 configurations reach the jobs as byte strings
     (`red/configs.sl`), decoded at run time. A decoding relation proved
     functional (`DecAll`, `dcfgs-fn`) ties what is decoded to the Settled
     lists the goal types mention.
   - `fcopen.sl`'s and `unav/qztcfs.sl`'s `cfs-run` re-decode the list
     inside a job and return an `Eq`.
   - the presentation scripts are strings (`unav/data.sl`, written by
     `unav/gen.py`).
   - the unavoidability regions are stored as small keys, recomputed in
     their job and checked there (`PartIn` in `unav/qztproof.sl`).

   A reference from an erased position embeds nothing.
   *Wish:* an extractor that writes Settled data compactly, for example as
   one marshalled string.

9. **Run settings.** `fourcolor/check.sh` passes `--inline 200` and sets
   `OCAMLRUNPARAM=o=400`, which the native jobs inherit from the compiler.
   In one pair of runs the two together cut the CPU time by about a
   quarter. The reference compiler is run under `ulimit -s unlimited`;
   slc passes with the default 8 MB stack.
   *Wish:* a documented way to pass GC settings to the native jobs alone.

## Run-time shape of the checks

10. **Tail calls, to keep stacks short.** A deep non-tail recursion keeps
    every frame on the stack, and every minor collection scans the
    stack. `unav/qztproof.sl`'s `allred-c` at 134,000 frames ran in about twice the
    time of the same work as a loop. Hot recursions are therefore written
    as tail calls.

11. **Unique trees rewritten in place.** The Kempe closure's working
    trees are `unique` (`UTree`, `UGtree` in `red/crestrict.sl`,
    `red/grestrict.sl`) and are rewritten in place. A rewrite skips the
    store when a child is unchanged (DESIGN.md §37). Rebuilding the trees
    each iteration appears to make garbage collection about a third of
    the time, mostly through promotion.

12. **Arrays for lookups.** `embed4.sl`'s `Tab` holds a dart permutation
    as an `Array (Copy Nat)`, for constant-time lookups in place of `Nth`
    walks along lists.

13. **Multi-value returns allocate.** Several hot functions return
    several values, and each call appears to allocate a tuple.
    *Wish:* unboxed multi-value returns in compiled code.

## Elaboration cost

14. **Warnings appear to cost time even when nothing is printed.** In
    profiles, each lopsided-match warning cost about 35–40 ms under both
    compilers, apparently because its text is built from the whole scope.
    Shadowing warnings cost slc about 7% of its elaboration time. Matches
    in this directory are written as `let-match` with branches instead.
    CLAUDE.md rule 17 asks for lazy diagnostics, so this may be a bug
    rather than intended behaviour; it is not reported in BUGS.md.

15. **Where the reference compiler's elaboration goes.** In stack samples,
    about 27% was `Env.opens_ruled`, which walks every opened Matchable
    on each rule, and about 11% was `Env.hide`, which takes the length of
    the scope on each `let`. Neither can be changed from the proof.

16. **No unused-definition check.** `--warn-unused` checks local binders,
    not top-level definitions, so dead code across files is found with a
    script.
    *Wish:* an unused top-level definition report for a unit.

17. **No phase timings.** Elaboration, compile and job times are measured
    with strace markers and a shim around ocamlfind.
    *Wish:* a flag that reports the time of each file, each
    `native-compute` compile and each job.
