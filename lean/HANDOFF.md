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

1. `Matchable` stage 2 (stage 1, the former `Tm.mtbl`, `VTy.mtbl` and
   `matchable-of`, is in). The plan: `Ctx.branch` takes the constructor
   term and the scrutinee type's head in place of `d` and `c`; a `Shape`
   relation lists (constructor term, signature, phantom mark) for a
   declared type (`vc d c`, `D.ctors[c]`) or for an opened `Matchable`
   (its listed constructors, signatures read from their `ValCtor`
   types); `mtch`, `case` and `BranchOK` are stated over a shape; a
   branch tuple's first component becomes the pattern's field count,
   which `realBr` needs, since `d` is unknown for an opened `Matchable`;
   `open-adt` is a new `Chk` kind that adds the entry to an `opened` list
   in `Ctx`, which only the checker consults. In `match_setup`, an opened
   `Matchable` gives, through `VTy.mtbl`, the declared type, and each
   listed constructor's value is `vc d c`, so its signature substitutes
   to `P.ctor d c`. Branch keys stay constructor positions, so `eval`
   and `RunS` do not change. Then stage 3, disjointness of the
   constructors of one opened `Matchable` in `unify`, and stage 4,
   `open-absurd`.
2. Unification now unifies the signatures of two variables it equates
   when both have `TyCtor` or `ValCtor` types (`Ctx.sig`, `sigEqs`), as
   the OCaml checker's forcing does; `tests/is_for_type_refute.sl` is
   accepted. It does not equate types when a variable is assigned a
   non-variable term, which the OCaml checker's forcing does not do
   either. The `Matchable` invariant of DESIGN.md section 8, as in
   `tests/open_tyctor.sl`'s `told`, waits on `open-adt` (item 1).
