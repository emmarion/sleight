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

13. **Diagnostics found wanting by the sweep.** `slc` and the
    reference differ in wording on some refusals, as audit M3 already
    records; one seen since is an absurd-by-proof branch written with no
    body, `(absurd (C ...))`, which the reference refuses with "a body
    needs a final expression" and `slc` with "malformed branch".


18. **`self/eval.sl` answers a failed step with an ordinary value.**
    Audit 2026-10-07 A2 and A3 (`audit/2026-10-07-audit.md` and its
    reproducers under `audit/2026-10-07/`, as of `89c37b6`) are two
    instances. A survey of
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

20. **A run-position call's result entries stay `Dyn`.** At run position
    every entry of the table is meant to be `Const` (the owner's
    statement in chat). DESIGN.md needs to change too, as the owner
    said: section 29 makes `Const` only the names a run-position
    statement introduces. The reference leaves the anonymous entries a call
    returns `Dyn`, and the `let` binders that take the results alias to
    them as the older atoms, so a `Const` binder canonicalizes to a `Dyn`
    entry. Reproduced with `(let ((many len) (erased lp)) (two 5))` for
    `two : (many (Nat) a) -> (many (Nat) q) (erased (Eq (Nat) q q) p)`:
    `dump-context` shows `len` at the slot of an anonymous entry minted
    at the call, and `lp : (Eq (Nat) len len)` names it; the prelude's
    `u8-modulus`, `u62-modulus` and `lt-dec` bindings show the same.
    `slc` does the same, and in both a match's results, a `coerce`'s and
    an argument bound first (section 15) alias the same way; erased
    results stay `Dyn` too. It shows beyond `dump-context` where a reader
    takes the state of the canonical atom rather than of the binder.
    With a type declared in a function `mk` that returns its `TyCtor`,
    two constructors `C` and `D` and its `Matchable`, bound by
    `(let ((erased T) (many C) (many D) (many m)) (mk))` and opened by
    `(open-adt many m)`, and `(let ((many v)) (C))`:
    `(comptime-match many v (C))` is refused in both compilers with
    "`__1` is not a run-position constructor" (`ctor_of`, `ctor-of`);
    printing `v` gives `_` in the reference, extracted or not
    (`shown_ctor`), but `(MkU)` under `slc --interpret`, the name the
    declaration gave; and a refuted branch on `D` is named by an
    anonymous marker rather than `D`. A dispatching `match` on such a
    value, head dispatch through a binder of a call's `Special` result,
    and `constant-of` on that binder seemed to behave as expected; they
    read the binder. Found with scratch probes; no test has this shape.

21. **A constructor application in a signature whose `at` target is not
    a variable leaves the signature naming a dead entry.** With
    `MkW : (erased (Slot) s) (erased (Nat) x at s) -> (W s)` for
    `W : ((Slot) s) -> Type`, a `def-fns` function with the parameter
    `(erased (Eq (W (slot-of v)) (MkW (slot-of v) v) (MkW (slot-of v) v)) e)`
    after `(many (Nat) v)` makes the reference die with an uncaught
    `Not_found`, raised by `Env.fact` from `Env.bind` of the function's
    entry in `elab_def_fns`. A return entry mentioning `(MkW (slot-of v) v)`
    does the same. `slc` accepts the definition, but the type it records
    names an entry with no fact: the call `(f 3 (Refl _ _))` is refused
    with "expected `__?1`, got `(W <error: no fact for 19387>)`". With a
    variable target, `(MkW s v)` for a parameter `(many (Slot) s)` and
    `(many (Nat) v at s)`, both accept the function, and so do both with
    the `(MkW (slot-of v) v)` term in a body, as a `let` of its `Refl`.
    The likely cause, read from the reference's `check_args` and not
    confirmed: an argument that is not a variable, for a field whose slot
    a later field's `at` names, is bound to a temporary entry that the
    application's term then mentions (section 15), and in a signature
    that entry is gone once the header has been elaborated. Section 15
    places such a binding just before the statement that contains the
    call, which a telescope does not have. Found while prototyping a
    prelude change with `(UninitAt A (slot-of v) v)` in `array-pluck`'s
    returns; returning that proof as an entry of its own avoids it.
