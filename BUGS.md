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
