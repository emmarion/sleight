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

13. **Diagnostics found wanting by the sweep**, each a refusal that is
    right with a message that is not: `(match many xs (at _) ...)` says
    "expected a telescope or `_`, got `at`" though `_` is what §40
    forbids (`result_tele` sees the `at` wrapper only around a list);
    `_` as an entry of a `values` or inside `slot-of` says "unbound
    name `_`" with "hint: nearest in scope: :"; a binder forwarded from
    a literal is named by the literal's anonymous entry
    (`(let ((many five)) 5) (coercible-wrap (Shared) five five)` says
    "`_1` is not a value constructor"); `(open-adt unique m)` on an
    abstract type followed by a `many` match blames readability where
    the cause is a `unique` binder read at many without `share`; an
    `open-absurd` annotation written `(at (...))` is accepted silently
    (`result_tele`'s flag is dropped); a returned closure whose `at`
    names an argument that was not a variable fails "no caller word
    for `at` `_1`" with no hint that naming the argument first works.
    a second decrease annotation on a call, or `(predates p)` after the
    first argument, is reported as an arity error; a lower-level call
    from a function at a factory-returned level names that level as
    `(level-of h)` in its refusal. `slc` and the reference also differ
    in wording on several refusals (`(absurd C)` against `absurd`, a literal written as a
    binder), as audit M3 already records.
