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

4. **`(share u)` is accepted as the head of a type form.**
   `tests/type_head_unique_const_degrade.sl` expects it, although a type
   is an erased position, where `share` is an error. `elab_term` reads
   the head through `special_of` without the position check that
   `read_special` makes. Reported by a review session; not reproduced
   independently.

11. **Inputs beyond the host's limits escape as OCaml exceptions
    rather than a `runtime error:` line.** `Program.explain` maps only
    the language's own exceptions, so each of these ends with "Fatal
    error: exception ...", exit 2, in the interpreter and, where it
    runs, in the extracted program: `(nat-shl 1 4611686018427387904)`
    (`Z.Overflow`; `shl` has no `fits_int` guard, `shr` has one);
    `(array-new (Nat) 100000000000000000000000)` (`Z.Overflow`) and
    `(array-new (Nat) 1000000000000000000)`
    (`Invalid_argument("Array.make")`), which audit B2 once covered;
    a numeral of 2^62 or more under `--no-extern` (`Z.Overflow` from
    `Z.to_int` in `nat_value`'s Peano ladder); and stack overflows in
    the source models under `--no-extern` (`array-new` of 200000, a
    `Rope` of 100000 `RCat`s flattened), where the FFI is fine. §31
    allows a crash where the host cannot represent what is asked, so
    only the form of the report may be at issue. `slc --interpret`
    overflows its stack on the deep `Rope` too (it runs the model at
    compile time); `ulimit -s unlimited` makes it print 100000.

13. **Diagnostics found wanting by the sweep.** `slc` and the
    reference differ in wording on some refusals, as audit M3 already
    records; one seen since is an absurd-by-proof branch written with no
    body, `(absurd (C ...))`, which the reference refuses with "a body
    needs a final expression" and `slc` with "malformed branch".

16. **`slc` embeds a compile-time value that nothing reaches.** On
    `bench/comptime_garbage.sl`, whose list of 12000 elements is built at
    compile time and folded away, `slc` at 30db0c9 writes 3469217 bytes of
    OCaml, about 24000 constant blocks holding the list, where the
    reference writes 60788. Both programs print 71994000. Since 7f3a568
    (BUGS 14) `slc` takes about 0.38 s on the sample, 0.14 s at f944496
    before it, and its output there was 162177 bytes. This session's guess,
    not checked against the code, is that `slc` emits a run-position
    argument's hoisted temporary as a Const whether or not anything
    reaches it. `ocamlopt` overflows its stack on that output at the
    default 8 MB limit and builds it with `ulimit -s unlimited`; `ocamlc`
    builds it. No test compares output size, and nothing runs `bench/`.

17. **Investigate a cheaper `uses-join`.** `uses-join-at`
    (`self/core.sl`) walks the whole of its first uses map into the
    second at every join of branches, so its cost seems to grow with
    branches times live entries; the at redesign's slot entries made the
    maps larger. Its own cost under callgrind, `slc` on its own sources,
    went from 142M instructions at 3091d12 to 244M at dbb1525, about 1.4
    percent of that run. A join that visits only what a branch changed
    might cost less; not tried.

18. **`self/eval.sl` answers a failed step with an ordinary value.**
    Audit 2026-10-07 A2 and A3 are two instances. A survey of
    `self/eval.sl` and `self/heap.sl` at `04a736f` (read from the code;
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
