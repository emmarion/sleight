# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's. At the last run 113 tests were
accepted with OCaml's value, none mismatched, 267 refusals agreed, and
175 + 218 were refused as unsupported. No test the OCaml suite refuses
is accepted. Of the tests it accepts, six are refused (four need cells,
`comptime_call_ctor.sl` and `thunk_extern_first_class.sl`) and two time
out at ten seconds (`comptime_tail.sl`, `extern_tail.sl`).

`lean/prelude.py` regenerates `lean/prelude.sl` from `lib/prelude.sl`,
keeping the `extern` marks. It takes several minutes, because it runs
`--full` on every prefix.

## Next, none of it decided

1. **`delegate-of`, the `Delegate` proof and `coercible-of`** (sections
   19, 33, 41). `coerce` and the other `coercible-*` forms are done:
   `VTy` reads `(Coercible sa A a sb B b)` as "a stripped value stands
   for `a` exactly when it stands for `b`". A `Delegate` proof turned
   into a `Coercible` would need the stripped value of a
   `delegate`-bodied `g` to stand for the full value of its target `f`,
   and `Real` relates closures only of one function. A plan, unproved:
   - The stripped run's call passes the callee its non-erased
     arguments as a stream, in the order of the caller's view of the
     callee's type, and the callee spreads them over its own non-erased
     parameters, with a token at each erased one. `Core.call` then needs
     the caller's erasure of each argument. For an ordinary call this is
     the same environment up to erased entries; for a call that reaches
     `f` where the full run calls `g`, it is what the `delegate`
     pass-through rule guarantees.
   - The stripped run's `defFns` binds a `delegate`-bodied function to
     its target's value, and `Real` gets a rule: a stripped value stands
     for the closure of a `delegate`-bodied function when it stands for
     the target that closure's environment holds. `Real.clo` then
     requires a function that does not delegate.
   - The call case of `eval_sound` then needs the shape of a delegate
     body, which a typing rule for it would provide.
   `char-cmp`, `str-cmp` and about ten tests need it.
2. **`unique`** (sections 13, 15, 16, 32): about 170 tests stop at it.
   Without it, a non-erased `coerce` needs `(Shared)` on both sides,
   which inference enforces.
3. **A type whose `def-adts` mentions top-level entries is not first
   class** (`String` passed as a value, `StrLt` as `Cmp`'s order). Its
   mentions are lifted into leading parameters, and the core has no
   partial application of a type constructor.
4. **The full evaluator on the prelude.** `u62-modulus` is `2^62` in
   unary, so `prelude.py`, which checks each form with `--full`, drops it
   and everything over `U62`. The stripped run never computes it.
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
9. Macros, `def-unique`, slots, `at` and cells, as before.
