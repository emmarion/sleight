# lean/ handoff

Work in progress on `lean/`, handed from one session to the next. Written
by a Claude session; nothing here is a design decision.

## Towards the full language (one session, with the owner)

`lean/` reads the full syntax and supports what `lean/README.md` lists.
`lean/compare.sh` runs it over `tests/` and prints, per test, the verdict
the test expects and the runner's (`unsupported`, `refuse`, `accept`,
`mismatch`, `stuck`); at the last run about 45 tests were accepted with
OCaml's value and none mismatched. `lean/prelude.py` regenerates
`lean/prelude.sl` from `lib/prelude.sl` (128 of 215 forms). A checked
program prints from the stripped run; `--full` runs `eval`, which
computes erased values and so is slow on the prelude (about 3 s).

Next, as this session planned it, none of it decided:

1. `Matchable` stage 2 is in: `open-adt` (`Chk.opn`, `Ctx.opened`), and
   matches through an opened `Matchable` (`Shape`, `Shape.sound`). Next,
   as planned, none of it decided: stage 3, what an open asserts, which
   `tests/open_adt_unify.sl` and `tests/matchable_former_unchecked.sl`
   need and `tests/open_adt_bad.sl`, `tests/open_adt_clash_bad.sl` and
   `tests/open_newtype_phantom.sl` need refused: distinct listed
   constructors, disjointness of the constructors of one opened
   `Matchable` in `unify`, and the invariant of DESIGN.md section 8 that
   two opened `Matchable`s naming one thing are unified, which
   `tests/open_tyctor.sl`'s `told` also needs, besides `matchable-of` in
   a type. Then stage 4, `open-absurd`.
2. Unification now unifies the signatures of two variables it equates
   when both have `TyCtor` or `ValCtor` types (`Ctx.sig`, `sigEqs`), as
   the OCaml checker's forcing does; `tests/is_for_type_refute.sl` is
   accepted. It does not equate types when a variable is assigned a
   non-variable term, which the OCaml checker's forcing does not do
   either. The `Matchable` invariant of DESIGN.md section 8, as in
   `tests/open_tyctor.sl`'s `told`, waits on `open-adt` (item 1).
