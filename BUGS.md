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

5. **A `_` for an `is`-typed parameter or field is solved without a
   type check, so a value of the wrong type reaches a non-erased
   position.** With `g : (erased (False) j) (many j is x) ->
   (many (False) r)` and body `x`, the call `(g _ 3)` is accepted: the
   meta for `j` is solved to `3` by the value equation `x is j`
   (`solve_sg`'s `Is` case checks the value alone, and `Env.unify_in`
   assigns a meta without comparing its type with the term's), so a
   `many` `(False)` comes back and an `absurd` function given it runs
   ("runtime error: absurd code reached", in the interpreter and in the
   extracted OCaml). The same through a constructor field
   `(erased (False) a) (many a is b)` built as `(C _ (MkUnit))`. With
   `(erased (Nat) j)` and `(BTrue)` a `Bool` is read as a `Nat` (prints
   1 in every backend); with a list the interpreter stops with "not an
   extern integer" and the extracted program prints garbage. Without
   the `_` the value check refuses it. `slc` accepts the same programs.
   A fix this session did not apply or test: also unify the argument's
   type with the type of the `is` expression (`mini/`'s `UAssign` does
   the equivalent at every meta assignment).

6. **An `at` entry's word can be read from a temporary whose runtime
   binding has closed.** `location_var` scans the scope for any entry
   marked `word` in the slot when the entry the `at` names is not
   itself readable (an `at` return whose target is another `at` return
   of the same call, `r1 at x` then `r2 at r1`). Temporaries bound by
   `check_args`, `elab_head`, `scrutinee` and `elab_cell_match` keep
   `word` after the `CLet` that binds them has closed; only `Env.hide`
   clears it. Both programs below are accepted and fail with
   "runtime error: unbound at runtime: N", exit 1, where `(MkBox 3)` is
   expected; the temporary read is the one bound for the argument
   `(id-box z)`, whose binding closed with the `open-adt`'s expression
   in the first and with the match's scrutinee in the second. Extracted
   OCaml of the same shape does not compile ("Unbound value vN").
   `slc` prints `(MkBox 3)` for both, so the defect is the reference's
   alone.

   ```scheme
   (def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
   (def-fns _ $ (many id-box : (many (Box) x) -> (many (Box) r at x)) x)
   (def-fns _ $ (many get-m : (many (Box) x) -> (many (Matchable enum Box (many MkBox)) m)) (matchable-of Box))
   (def-fns _ $ (many twice : (many (Box) x) -> (many (Box) r1 at x) (many (Box) r2 at r1)) (values x x))
   (def-fns _ $ (many go : (many (Box) z) -> (many (Box) b))
     (open-adt many (get-m (id-box z)))
     (let ((many a) (many b)) (twice z))
     b)
   (go (MkBox 3))
   ```

   ```scheme
   (def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
   (def-fns _ $ (many id-box : (many (Box) x) -> (many (Box) r at x)) x)
   (def-fns _ $ (many copy-box : (many (Box) x) -> (many (Box) r)) (let-match many x (MkBox n)) (MkBox n))
   (def-fns _ $ (many twice : (many (Box) x) -> (many (Box) r1 at x) (many (Box) r2 at r1)) (values x x))
   (def-fns _ $ (many go : (many (Box) z) -> (many (Box) b))
     (match many (copy-box (id-box z)) (((Box) b))
       ((MkBox n)
         (let ((many a) (many b)) (twice z))
         b)))
   (go (MkBox 3))
   ```

7. **Printing a function type whose `at` names a closed-over variable
   asserts.** `Env.show` and `Env.show_tele` canonicalize the term, and
   `Env.canon` turns a place `SlotOf (Var z)` into the slot atom
   `Var s`; `Term.tele_strings` accepts only `SlotOf _` as a place and
   has `| _ -> assert false` (lib/term.ml:151). A target that is an
   earlier binder of the telescope stays `SlotOf (Bound k)` and prints.
   So every diagnostic that shows such a type dies with "Fatal error:
   exception ... Assertion failed", exit 2: a type mismatch against
   `inner : (many (Nat) x) -> (many (Nat) q at z)` defined inside
   `outer`'s body with `z` its parameter, `(dump-context)` in that body,
   or an arity error on a function with a parameter `at z`. `slc`
   prints the message.

8. **A `many` cell of a nullary constructor, copied, extracts to OCaml
   that does not compile.** `(match many x _ ((A u) (u)) ((B n u)
   (u n)))` over `enum (many A : -> (D)) (many B : (many (Nat) n) ->
   (D))` runs in the interpreter (prints `(A)`), but `--extract`
   emits `K6_0 r55 -> ...` for the copy of the nullary cell:
   `field_match` in lib/extract.ml always writes the pattern `K r`.
   ocamlopt: "The constructor K6_0 expects 0 argument(s), but is
   applied here to 1". The same for `(cell-write u (A))` on a `many`
   cell and for a union's nullary constructor; a `unique` nullary cell
   and the full-at form are unaffected.

10. **The unmarked same-level-call warning crashes when the callee was
    bound by a match branch.** `check_marks` builds the warning "same-
    level call to `f` is unmarked" with the body's final environment,
    in which a callee bound by a `match` branch has no fact-table
    entry, so `Env.fact` raises `Not_found` ("Fatal error: exception
    Not_found", exit 2). With `Pack : (many (Fn L (subterm many (Nat)
    n) -> (many (Nat) r)) f) -> (Packed)` and `g` at `L` matching its
    `Packed` parameter in a `Succ` branch and calling `(f (subterm p)
    k)` unmarked, `(g (Pack g) 2)` crashes; marking the call `notail`
    runs it. The same for a callee bound by a `let-match` inside a
    branch, and for a `let` alias of the function made inside a branch,
    `(let ((many g2)) g)`. A callee from a `let-match` at the body's
    own level, which binds outward, warns as intended
    (tests/recursion_through_pointer.sl).

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
