# Bugs

Defects found in the implementation, for the owner to get to. Written by
Claude sessions; each entry says how it was reproduced, and nothing here
is a design decision. Remove an entry when it is fixed.

1. **A `tail` mark is refused in a function whose returns are all
   erased.** With `g : (unique (Nat) x) -> (unique (Nat) r at x)`, the
   body `(let ((unique y)) (tail (g x))) (Zero)` of a function returning
   `(erased (Nat) e)` is refused as not in tail position: `project_code`
   short-circuits on an empty list of kept results, so the trailing erased
   code never becomes `(values)` for `check_marks` to fold. Such a
   function is only ever called erased, so nothing runs wrongly.

13. **Diagnostics found wanting by the sweep.** `slc` and the
    reference differ in wording on some refusals; one seen is an absurd-by-proof branch written with no
    body, `(absurd (C ...))`, which the reference refuses with "a body
    needs a final expression" and `slc` with "malformed branch".
    Another is a refuted branch in a run-position `match`
    (`proposals/self-formal/proto/aftererr/17_type_error_first.sl`,
    line 2): the reference says "omit it or write `(absurd Zero)`" at
    column 45, `slc` "omit it or write `absurd`" at column 44.
    `self/README.md:304-309` allows the column to differ but says the
    first message is the reference's on every error test; this file is
    not one of `tests/`, so that claim may not cover it.


18. **`self/eval.sl` answers a failed step with an ordinary value.**
    Audit 2026-10-07 A2 and A3 (`audit/2026-10-07-audit.md` and its
    reproducers under `audit/2026-10-07/`, in the tree at `aa84d4e`) are two
    instances. A survey of
    `self/eval.sl` and `self/heap.sl` at `f9d57e1` (read from the code;
    beyond A2/A3 and the `heap-strs-fuel` case, reproduced separately,
    none of the cases below was reproduced) found the
    same shape in several places, in three groups:

    - *Fuel.* No longer a fixed 1000000: `flatten-value` seeds
      `rope-walk` with twice the store's allocation count (`store-size`;
      the rope pair spends two units per level), `ErListToArray` seeds
      `list-refs` with the count itself, and running out becomes a
      `BError` ("out of fuel") rather than `REmpty` or `Nil`. With that,
      A2's and A3's reproducers match the reference under `--interpret`
      and compiled, under `ulimit -s unlimited` (at the default 8 MB
      stack, `slc` overflows on them before and after); no test
      was added yet. That the count suffices on an acyclic heap is an
      informal pigeonhole argument, not a proof. Nothing at the meta
      level excludes a cycle (`store-write` stores a body over the whole
      current history, and `CCellWrite` writes `BTag` blocks). On one,
      the report is an error block, with the limits of the third group
      below. `heap-strs`, `heap-pairs`, and `heap-jobs`, which read the
      lists a `ConfinePaths` or `Exec` request carries, still take a
      fixed `heap-strs-fuel` of 1000000 (`self/eval.sl:1018`) and answer
      running out with `Nil`, so a longer list seems to be cut short
      with no report. Reproduced for `ConfinePaths`, on the tree at
      `5fba336`, under `ulimit -s unlimited` (at the default 8 MB
      stack the reference, `slc --interpret`, and the binary `slc
      --build` makes all crash on it), with
      `proposals/self-formal/proto/bugs/heap_strs_cut.sl` (a `reads`
      list of 1000000 entries `"absent-dir"` then `"."`, then a
      `Stat "."`): under `slc --interpret` it prints
      `confine ok` and `stat cwd refused`, while the reference and
      the binary `slc --build` makes print `stat cwd ok`, as `slc
      --interpret` does with 999999 entries. `Exec`'s lists were
      not tried. This seems to conflict with DESIGN.md §31: "The
      semantics is that of a machine with unlimited stack and heap. A
      real run may crash where the host cannot represent what is asked
      of it. A crash produces no value, never a different one."
    - *A block of the wrong shape, or a missing argument.* `rope-walk`
      returns `REmpty` on a block that is neither `BTag` nor a
      string/char `BExt`. `list-refs` and `ctor-fields` return `Nil`
      on a non-`BTag`. `heap-str` returns `SNil`, `field-nat` returns 0,
      and `apply-extern`'s `na`/`nb`/`sa`/`sb` default to 0 or `SNil` on
      a missing argument. `ExFlatten` gives `SNil` on a missing
      argument, and `ErListToArray`, `ErArrayMake`, `ErArrayCopy`,
      `ErArraySub` and `ErArrayBlit` build from `Nil` when `array-fields`
      or the argument is missing. `ErWrite` and
      `ErArrayBlit` keep the store unchanged on a `list-nth` miss.
      Well-typed input may never reach these; nothing in the evaluator
      shows that.
    - *Error blocks that don't stop evaluation.* Where the evaluator
      does report (`error-vals`, out of fuel included, and
      `array-construct` and `apply-array-change`), the report is a
      `BError` value. It becomes a `runtime error:` only when read as
      a final or a request, applied (`apply`'s `BError` case), or
      emitted (`failwith`). As read, `dispatch` returns `None` for a
      `BError` scrutinee, and `CMatch`'s `None` path then runs the
      first branch over `ctor-fields` of the error block, so a matched
      error might turn into an ordinary result. A dropped one
      disappears. Separately, `sub`, `div`, `divmod`, `nat-mod` and
      `str-split` report through `ErPayload $ PStr "..."`. That seems to
      allocate a string `BExt` rather than a `BError`, though the
      ASSUMPTIONS entry on the arithmetic externs says an error block.
      Their proof arguments may make those branches unreachable.

    A likely structural fix, not decided: give the evaluator's results
    a `Result`-shaped type, i.e. a failure with its message or the
    values. Each helper above would return that type, and `eval` and
    its mutual group would short-circuit on a failure at every step,
    making exhaustion and shape mismatches impossible to answer with an
    ordinary value. The `BError` block would then remain only as the
    emitted representation, if anywhere. Cheaper partial alternatives
    are a `BError` that `dispatch` and every block-inspecting helper
    propagate (each site an obligation, and a missed one keeps the
    bug), or a host-level abort primitive, which would be a design
    addition. Separately, the acyclicity a measure-based traversal
    would need is a question about `heap.sl`'s store invariant.

19. **The compilers run a final value that is not in the last file at
    different times.** The reference runs a file's final value as soon as
    it reaches it, before reading the files after it on the command line;
    `slc`, compiled or under `--interpret`, elaborates every file first
    and runs the finals afterwards. Reproduced with two files: `a.sl`
    ending in a `Program` that writes to stderr and exits with 0, and
    `b.sl` holding only a `compile-warn`. The reference writes the
    program's line and never reads `b.sl`, so it gives no warning; `slc`
    writes the warning, then the program's line. With a final that does
    not exit, the reference's warnings from later files would follow the
    program's output instead of preceding it. No test has this shape;
    `self/bootstrap.sh` compares each side's whole stderr, warnings
    included, so one that did would fail there. The two also differ in
    acceptance when a later file fails: with
    `proposals/self-formal/proto/review5/01_prog_first.sl`, whose
    `Program` writes `effect` and exits with 0, followed by
    `proposals/self-formal/proto/review2/rf_b.sl` (a syntax error) or
    `proposals/self-formal/proto/review5/01_late_error.sl` (a
    `compile-error`), the reference writes `effect` and exits 0,
    reporting nothing about the second file, while `slc`, compiled or
    under `--interpret`, reports the second file's error and exits 1
    without running the `Program` (on the tree at `5fba336`). Which
    order is wanted is not decided here.

20. **The two compilers disagree on a `let` of a constant before a
    `delegate` call.** In a function `f at g` whose body is
    `(let ((many s)) (settled-of many g)) (delegate (g ...))`, the
    reference refuses the `delegate` as not in tail position, and `slc`,
    compiled or under `--interpret`, accepts it. `(cell-same u u)` in
    place of the `settled-of` splits the same way. The reference's
    normalizer folds away a `let` of constants only when its right-hand
    side is a `values` of constants, and both forms compile to a bare
    constant; `slc`'s folding appears to cover that case. DESIGN.md §19
    says a `delegate`-bodied function is nothing but the call once lets
    that only rename are resolved away, which seems not to settle a let of
    a constant. Which answer is wanted is not decided here. No test has
    this shape.

21. **`slc` refuses a `tail` call returned beside an `at` entry.** With
    `f` returning `(unique (World) w2 at w) (many (Nat) n)` and `g`
    returning `(many (Nat) n)`, both in one `def-fns` block, the body
    `(values w (tail $ g rest))` of `f` is accepted by the reference and
    refused by `slc` as "a `tail`-marked call is not in tail position",
    on `origin/main` as of `e6ebf28` and after `5da2b75`; the same holds
    with `(many (Nat) j at k)` in place of the world. The reference drops
    an `at` entry from the returns before judging tail position (DESIGN.md
    §19, §36); `slc`'s `tails-ok` and `call-report` appear to see a
    `values` form of two entries and treat every entry as non-tail. No
    test has this shape; `open-contradicts` in `self/elab-main.sl` takes and
    returns the macro world so that `elab-refute` avoids it.

22. **Checking is exponential in a term's sharing.** Canonical forms
    are expanded in full and walked as trees, so the cost seems to
    track the expanded size, not the source. Reproduced with n lets
    `(let ((erased x{i+1})) (Node x{i} x{i})))` in a function body:
    the reference takes 6.8 s and 301 MB at n=20 and times out at
    n=22; `slc` overflows its stack at n=18 (3.1 s and 196 MB under
    `ulimit -s unlimited`). An unshared chain stays flat, even 1000
    deep. The same growth was seen at `many`, in run position, through
    a call's `is` return, and with the chain then matched, `is`-checked,
    used as a type index, or given to `prove-subterm`. A failing
    `prove-subterm` is worst, since its message prints the expanded
    term (22 s and 5.2 MB at n=18). Memoizing `canon` alone (not
    committed) left the time exponential in `fold_vars` and `unify`, so
    a fix probably has to make every term walk sharing-aware, in both
    compilers.

23. **`slc`'s compile-time printer cuts a deep value short with `_`.**
    `show-at` (`self/elab.sl:4680-4725`) is started at a depth of
    100000 (`self/elab.sl:4730`, `self/interp.sl:15`) and spends it
    twice per nested field, once in `show-at` and once in
    `shown-field`, and prints `_` when it runs out, with no report.
    So a list of more than about 50,000 elements prints wrongly.
    Reproduced on the tree at `5fba336`, with
    `ulimit -s unlimited`, by three files under
    `proposals/self-formal/proto/bugs/`, each building a list of 50002
    `0`s: `show_at_final.sl` as a final value under `slc --interpret`
    (`final-text`, `self/interp.sl:15`), `show_at_match.sl` in a
    failed `comptime-match`'s message (`show-typed`), and
    `show_at_dump.sl` in a `dump-context` report (`entry-value`). Each
    prints 49,999 `Cons _ 0` and then `Cons _ _ _)`; the reference
    prints all 50002 and `Nil _` in each. `show_at_fn.sl` builds the
    same list in a final function: `slc --interpret` cuts it the same
    way, and the binary `slc --build` makes from it prints the whole
    list, since the emitted OCaml printer seems to have no depth bound.
    This seems to conflict with DESIGN.md §45, whose cases that print
    `_` are "a union with more than one" and "an erased field, a cell, a
    slot, a function, an opaque proof, and a value whose type has no
    readable `Matchable`", and with §31's "A crash produces no value,
    never a different one". §28 asks a failed `comptime-match` to
    print "the actual value, including its discriminant and
    arguments". `dump-context`'s report is defined by MANUAL.md (§54),
    so whether §45 governs it is not decided here.

24. **`self/README.md` has claims the code seems not to bear out.**
    Checked against the tree at `5fba336`, read from the code:
    - `README:254-258` says the interpreter and the generated printer
      take "a fuel of 1000000 or 100000" and that "running out returns
      an error value, never a wrong answer silently". The interpreter's
      default fuel is 1000000000 (`self/core.sl:3614`, and MANUAL.md
      says the same); the only 1000000 in `self/` seems to be
      `heap-strs-fuel` (`self/eval.sl:1018`, entry 18). The emitter's
      `show-fuel` of 100000 (`self/emit.sl:4`) falls back to
      `show_any` when it runs out (`self/emit.sl:1380`), which prints
      `?` (`self/runtime.ml:18`) rather than returning an error value;
      that case was not reached in a run. `show-at`'s 100000, which
      prints `_` silently (entry 23), seems not to be mentioned there.
    - `README:385-386` puts the sugar budget "as its first `subterm`
      parameter, ahead of the raw". In `elab-expr-demand`
      (`self/elab-main.sl:752`) it is `sugar`, after the `subterm`
      parameters `fuel`, `callbacks`, and a `hop-` index.
    - `README:463-465` lists macros as "Not modelled", "which the
      reference does not implement either". `self/elab-main.sl`
      expands macros (`env-expand`, `:509` onward), the reference
      runs them, and `README:61-62` and `:128` themselves say slc
      takes `std/macro.sl`'s macros and holds macro expansion.

25. **After its first error, `slc` reports false facts about later
    run-position values.** Once an error is recorded, `slc` stops
    running run-position code. A run-position `let` whose right-hand
    side needed no hoisted temporaries then gets the erased token as
    its binders' value (`env-set-tokens`, `self/elab-main.sl:2209-2216`;
    also `:672-678`), and the discriminant read takes a token as the
    word 0 (`self/eval.sl:51`), so the binder seems to read as its
    type's first fieldless constructor, or as the `Nat` 0, whatever
    was written. Reproduced on the tree at `5fba336`, compiled and
    under `--interpret`, with files under
    `proposals/self-formal/proto/aftererr/` that each start with
    `(compile-error "first")`: in `02_bfalse.sl`, `x` bound to
    `(BFalse)` is reported as "expected `BFalse`, got `(BTrue)`"; in
    `04_lit.sl`, `x` bound to `3` as "expected `Succ`, got 0"; and in
    `05_lit_missing.sl`, `(comptime-match many x (Zero))` on that `3`
    passes with no message. `17_type_error_first.sl` gives the same
    false message after a refuted branch as its first error.
    `proposals/self-formal/10-slc-after-error.md` reports more such
    cases, including ones where a binder is called `Hypothetical`, and
    that macro expansion has no such gate; those were not re-run here.
    The reference stops at the first error and prints only that one;
    `self/README.md:301-302` says only that `slc` "may report a few
    more that follow from it".
    Acceptance seems unaffected, since the first error already makes
    `slc` exit 1, and `--first-error` hides the later messages.
    DESIGN.md seems not to say whether more than one error is reported;
    the later messages seem to conflict with §27's "its results become
    `Settled` with the resulting values" and §28's "the error prints
    the expected constructor and the actual value". Which answer is
    wanted is not decided here.

26. **The reference interpreter's `-imm` blits corrupt its heap.** `lib/ffi.ml:117-119`
    maps `array-blit-imm`, `array-blit-many-imm`, and `array-move-imm` to
    `blit_imm` (`:89`), which calls `Ffi_core.array_blit_imm`, a raw word copy
    with no write barrier (`lib/ffi_core.ml:319-321`). In compiled code
    the elements of such an array are immediates, which is what the
    `Imm` evidence of §44 is for, but in the interpreter such an element,
    a `U62` in the reproduction below, is a heap-allocated `VWord`
    (`lib/value.ml:22`), so the copy moves
    pointers behind the garbage collector's back. Reproduced with
    `_build/default/bin/main.exe std/immediate.sl
    proposals/self-formal/proto/bugs/blit_imm_interp.sl`, which blits
    freshly computed `U62` values into an older array, allocates, and
    reads them back: a segmentation fault (exit 139) in every run tried;
    with `OCAMLRUNPARAM=s=4k` it stops instead with "runtime error: not
    an extern integer: _". The same program with `array-blit` prints
    `0`. `--build` crashes too, since the reference runs the top-level
    call at compile time. `slc --interpret` prints `0`: `self/core.sl:482`
    maps the three `-imm` blits to the ordinary blit.
    `proposals/self-formal/proto/review6/08_blit_many_imm_interp.sl`
    does the same with `array-blit-many-imm`: a segmentation fault in
    every run tried, the same message under `OCAMLRUNPARAM=s=4k`, and
    `0` under `slc --interpret`.
    `proposals/self-formal/proto/bugs/move_imm_interp.sl` does it with
    `array-move-imm`, moving two placed `U62`s into an older array of
    `Vacant` slots: a segmentation fault in every run tried, three with
    the default minor heap, three with `s=4k`, and three under `--build`,
    which writes no binary, while the same program with `array-move`
    prints `0`, and `slc --interpret` prints `0`. In two sweeps of 40
    smaller runs (1, 3, 10, or 100 trials, with 0, 50, 300, 1000, or
    2000 allocation steps around the move, each with the default minor
    heap and with `s=4k`), no run printed a value other than `0`: each
    printed `0` or stopped, with a segmentation fault (exit 139), an
    abort (exit 134, "Fatal error: out of memory" in each one examined),
    or, in the second sweep, "runtime error: not an extern integer: _"
    (exit 1). Repeating one configuration can change how it stops.
    §31 says a real run "may crash where the host cannot represent
    what is asked of it", which these small programs seem not to
    approach. The analysis, and the reasoning that
    compiled `-imm` stores are safe when both words are immediates, are
    in `proposals/self-formal/08-gc-imm-stores.md`.
