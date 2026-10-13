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
2. Equating the types of the two sides when unification assigns a
   variable, as the OCaml checker does. `VTy` does not give a value one
   type (`univ` and `top` hold of every value, and `.tok` of every true
   `Predates` and `Subterm`), so the proof would need a lemma for the
   types where a value's type is unique, or a narrower `VTy`. The owner
   asked whether it is really unjustified; this session overstated it and
   has not checked. For data values, value constructors (`VTy.vc` fixes
   the signature), type constructors, levels and closures a value's type
   looks unique, which may be enough: the narrow route is to prove that
   two entries with one value have one type outside `Type`, proofs and
   `.nil`, add the type equation to `unify` for those entries only, and
   see whether `UnifySound` goes through; the broad one is to narrow
   `VTy.univ` to type terms and have a proof value carry its statement.
   The session's one attempt at a counterexample, two proofs of
   different statements forced equal through `JMEq`, did not go through:
   the indices refute the branch first. What it would buy:
   `tests/is_for_type_refute.sl` (the `ctor-type-is` functions, two
   `ValCtor` variables forced equal) and the `Matchable` invariant of
   DESIGN.md section 8, as in `tests/open_tyctor.sl`'s `told`, which
   refutes `IsNat` through a constructor's signature.
