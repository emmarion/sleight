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


18. **`self/eval.sl` answers a failed step with an ordinary value.**
    Audit 2026-10-07 A2 and A3 (`audit/2026-10-07-audit.md` and its
    reproducers under `audit/2026-10-07/`, as of `aa84d4e`) are two
    instances. A survey of
    `self/eval.sl` and `self/heap.sl` at `f9d57e1` (read from the code;
    beyond A2/A3, none of the cases below was reproduced) found the
    same shape in several places, in three groups:

    - *Fuel.* No longer a fixed 1000000: `flatten-value` seeds
      `rope-walk` with twice the store's allocation count (`store-size`;
      the rope pair spends two units per level), `ErListToArray` seeds
      `list-refs` with the count itself, and running out becomes a
      `BError` ("out of fuel") rather than `REmpty` or `Nil`. With that,
      A2's and A3's reproducers match the reference under `--interpret`
      and compiled, under `ulimit -s unlimited` (at the default 8 MB
      stack, `slc` overflows on them before and after, as in 11); no test
      was added yet. That the count suffices on an acyclic heap is an
      informal pigeonhole argument, not a proof. Nothing at the meta
      level excludes a cycle (`store-write` stores a body over the whole
      current history, and `CCellWrite` writes `BTag` blocks). On one,
      the report is an error block, with the limits of the third group
      below.
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
    included, so one that did would fail there. Which order is wanted
    is not decided here.

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
