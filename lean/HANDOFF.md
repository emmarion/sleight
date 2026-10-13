# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's. At the last run 106 tests were
accepted with OCaml's value, none mismatched, 248 refusals agreed, and
185 + 238 were refused as unsupported. Three tests the OCaml suite
refuses are accepted:

- `compile_warn_erased_bad.sl`: an `erased` `let` binder of a `Settled`
  `String` forwards the literal's non-erased entry, and the elaborator's
  scope does not record the binder's own multiplicity, so the message is
  taken.
- `extern_missing.sl` and `msg_subterm_not_param_bad.sl`, as before.

`lean/prelude.py` regenerates `lean/prelude.sl` from `lib/prelude.sl`
(141 of 220 forms; it now keeps `;! warn` lines). It takes about six
minutes, because it runs `--full` on every prefix.

## Next, none of it decided

1. **`coerce` and the `coercible-*` forms (DESIGN.md sections 33, 34).**
   A session got part way into an implementation and did not commit
   it. Its plan, unproved:
   - The stripped run takes newtype wrappers out of the values it builds
     (`Prog.unwrap`, applied wherever `RunS` turns a term into a value:
     results, arguments, primitive values, scrutinees). A wrapping
     constructor is a non-phantom constructor of a `newtype` type with
     exactly one non-erased field (`Prog.wrapField`).
   - `Real` gets a rule `wrap`: a stripped value stands for a wrapped
     full value when it stands for its field. `Real.con` then requires a
     constructor that does not wrap.
   - `Core.mtch` and `Core.case` get a field `nt : Option Nat`. On a
     newtype scrutinee (`some k`) the stripped run takes the one real
     branch without looking, as an erased match does, with the
     scrutinee's value as field `k`. The checker requires the type to
     be a newtype exactly when `nt` is set (`Shape` gets an output flag),
     every non-phantom constructor's one non-erased field to be `k`, and
     at most one real branch. `Ctx.advBr` and `BranchOK.fixedOut` must
     then refuse newtype scrutinees, since a known stripped value of a
     newtype is its field.
   - `Coercible` is a built-in opaque type: an `Adt` with an `opaque`
     mark, which `Shape.decl`, `matchable-of` and `no_false` exclude. Its
     values in the full run are the pair `(a, b)`, and `VTy` holds of a
     pair when every stripped value that stands for `a` stands for `b`
     and the converse. `coerce` is then the second of the pair in the
     full run and the source in the stripped run, and each
     `coercible-*` form is a primitive that builds its pair.
   - Printing must then be by type, since the stripped run no longer
     shows a wrapper: re-wrap a value of a newtype type at the result's
     type.
   About 20 tests name `coerce`; `char-cmp`, `str-cmp` and the `U62`
   operations of the prelude need it too.
2. **`unique`** (sections 13, 15, 16, 32): about 160 tests stop at it.
3. **A type whose `def-adts` mentions top-level entries is not first
   class** (`String` passed as a value, `StrLt` as `Cmp`'s order). Its
   mentions are lifted into leading parameters, and the core has no
   partial application of a type constructor.
4. **The full evaluator on the prelude.** `u62-modulus` is `2^62` in
   unary, so `prelude.py`, which checks each form with `--full`, drops it
   and everything over `U62`. The stripped run never computes it.
5. Settled head dispatch reads a head's type through the facts of
   top-level `let-match`es on `Eq` proofs only, a stand-in for
   canonicalizing against the facts of the innermost run position.
6. Macros, `def-unique`, slots, `at` and cells, as before.
