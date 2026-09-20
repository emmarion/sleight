# Q6. U13's text as written needs two repairs to elaborate

Status: open question about the spec's example, ASSUMPTIONS 183 and 167.
The prelude's code is faithful.

## The rule

UNIQUE.md U13 gives the array API in full, "written against the rules as
recorded, not machine-checked". `lib/prelude.sl` carries it, and
ASSUMPTIONS 167 admits two "elaboration repairs".

## The observation

The prelude was diffed against U13's code blocks line by line. The only
differences are the two repairs, and each is necessary:

1. `(array-new _ n1)` becomes `(array-new A n1)`. Reverting it gives
   "argument 1 is _ and cannot be inferred": the recursive call sits in
   `(let (unique tl) (erased q) ...)` with no annotation on either
   binder, so there is no expectation to solve the `_` against, exactly as
   SUGAR.md 6's boundary rule predicts. `A` is what the `_` would have to
   be, so no meaning changes.
2. `(coercible-wrap _ Init x)` becomes `(coercible-wrap _ Init _ x)`.
   Reverting it gives "expected 2 arguments, got 1": `coercible-wrap`
   takes the constructor's whole telescope, erased entries included, as
   every other use in the prelude does, and `Init` has an erased `Type`
   argument.

Everything else, the relations, the four externs, `init-witness`, the
two-name absurd pattern, the `(at)` invocations, is byte-identical.

## The question

Whether U13's text should be brought into line with the prelude, which
under CLAUDE.md rule 12 is the owner's wording to confirm, or whether
SUGAR.md 6 should let an unannotated `let` solve a `_` from the callee's
own signature, which is a design change.
