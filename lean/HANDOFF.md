# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's. At the last run 138 tests were
accepted with OCaml's value, none mismatched, 312 refusals agreed, and
155 + 173 were refused as unsupported. No test the OCaml suite
refuses is accepted. Of the tests it accepts, one is refused
(`thunk_extern_first_class.sl`) and two time out at ten seconds:
`comptime_tail.sl` finishes in about a minute, and
`extern_tail.sl` ran out of memory on this session's machine.

`lean/prelude.py` regenerates `lean/prelude.sl` and
`lean/prelude-full.sl` from `lib/prelude.sl`, keeping the `extern` marks. It takes several minutes, because it runs
`--full` on every prefix.

`unique` is done, checked by the elaborator (`lean/README.md`).
`delegate-of`, `coercible-of` and the `Delegate` type are done, with the
stripped run passing only non-erased arguments and results and binding a
delegate to its target (`lean/README.md`). One consequence for the
elaborator: a run-position call whose callee's type it does not know
records no view of the callee's erasures (`Core.call`'s `ve` is `none`),
and the stripped run then uses the callee's own; inference fills it in
before checking, and the checker requires it.

## Next, none of it decided

1. **A signature that mentions an earlier function of its block** other
   than through `level-of` (section 53), and `delegate-of` in a type.
2. **`at`, slots and cells** (sections 35 to 41 and 66), now the
   largest gap: the `unique` tests that remain unsupported stop at them,
   and so do `Program` (its continuation returns the world `at` the one
   it took), arrays and macros (`MacroWorld`). Like `unique`, they
   change nothing in an immutable run, which suggests checking them in
   the elaborator; but slot facts come from forcing too (section 36's
   writers), which the elaborator does not do. Not started.
3. **A type whose `def-adts` mentions top-level entries is not first
   class** (`String` passed as a value, `StrLt` as `Cmp`'s order). Its
   mentions are lifted into leading parameters, and the core has no
   partial application of a type constructor.
4. **The full evaluator on the prelude.** `u62-modulus` is `2^62` in
   unary, so `prelude-full.sl`, which `--full` and `--unchecked` load,
   leaves out it and everything over `U62`. `prelude.sl` has them, since
   the stripped run never computes it.
5. **A result typed with the program's own entries** is checked as a
   result of any type (`ArgsTy.anyCons`), so `checked_runs` says nothing
   of its type. The printer finds such types separately (`retTypes`,
   untrusted), since the stripped run holds a newtype's value as its
   field and printing needs the type.
6. Settled head dispatch reads a head's type through the facts of
   top-level `let-match`es on `Eq` proofs only, a stand-in for
   canonicalizing against the facts of the innermost run position.
7. `comptime-match` and the checker's known values do not look through
   a newtype: on one, `comptime-match` is a `case` the stripped run takes
   without looking, and `BranchOK.fixedOut` is refused.
8. `dump-context` shows a type only where the elaborator knows it, which
   is not the case for a `let` binder written without one.
9. Macros and handles (sections 62 to 65), which need `at` for `MacroWorld`.
