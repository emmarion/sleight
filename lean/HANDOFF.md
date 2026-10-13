# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision.

## Towards the full language (one session, with the owner)

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's (`unsupported`, `refuse`, `accept`,
`mismatch`, `stuck`); at the last run 79 tests were accepted with
OCaml's value and none mismatched. `lean/prelude.py` regenerates
`lean/prelude.sl` from `lib/prelude.sl` (135 of 215 forms). A checked
program prints from the stripped run; `--full` runs `eval`, which
computes erased values and so is slow on the prelude (about 3 s).

Next, as this session planned it, none of it decided:

1. `Matchable` is in, stages 2 to 4 of the plan: `open-adt`, matches
   through an opened `Matchable` (`Shape`), what an open asserts,
   through one oracle that `unify` consults on every equation between
   atoms (`Ctx.atoms`, `AtomSound`), and `open-absurd`
   (`CoreTy.chkOpnFail`).
2. Unification unifies the signatures of two atoms it equates when both
   have `TyCtor` or `ValCtor` types, as the OCaml checker's forcing
   does; `tests/is_for_type_refute.sl` is accepted. It does not equate
   types when a variable is assigned a term that is not an atom, which
   the OCaml checker's forcing does not do either.
