# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision, and the claims
below that `lake build` does not check are that session's reading, which
may be mistaken.

## Where things stand

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's. At the last run 230 tests were
accepted with OCaml's value, none mismatched, 419 refusals agreed, and
57 + 66 were refused as unsupported; 7 tests OCaml accepts are refused
(`at_match_union`, `at_target_wild`, `cell_append`,
`coercible_ctor_infer`, `macro_body`, `macro_splice`,
`slot_of_predates`). No test the OCaml suite
refuses is accepted. Of the tests it accepts, two time out at ten seconds:
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

0. **Native arithmetic, one proved extern at a time.** The owner's
   plan, from chat: no extern's native code is ever trusted as an
   axiom. The stripped run already holds the prelude's `Nat` as a
   number (`lean/README.md`); next, an extern function gets native code
   only once a Lean proof shows it agrees with its model, starting with
   `add`. A session's proposal, not yet built: keep in Lean a fixed
   copy of the extern's elaborated body, prove the native code against
   that copy, and use the native code only when the program's body is
   that copy, warning when it is not (the owner asked for a warning,
   not a silent fallback). Whether the warning belongs in WARNINGS.md
   is an open question for the owner.

1. **A signature that mentions an earlier function of its block** other
   than through `level-of` (section 53). `delegate-of` in a type names the
   proof that `def-fns` mints after its block, so it is refused in the
   block's own signatures.
2. **What `at`, slots and cells still lack** (`lean/README.md` lists
   what is done): `Placed` (section 66; `placed-slot` needs a slot
   semantics the core does not have, and the placings are `def-prim`s
   with non-erased returns), arrays and bytes (cells of extern types
   inside extern bodies; `inExtern` is never set), `World` and
   `Program`, a cell binder in `comptime-match`, the full-`at`
   invocation counted as erased by the `tail` check, a non-erased
   at-match on a union, and the gaps the README's slot item lists.
   The user asked that mutation state be left until everything else is
   done, so the non-mutation items here come first.
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
