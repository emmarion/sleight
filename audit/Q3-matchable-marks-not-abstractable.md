# Q3. Structural Matchable marks prevent abstracting over extern and non-extern

Status: open question, ASSUMPTIONS 183; ASSUMPTIONS 160 records the
consequence without a decision.

## The rule

UNIQUE.md U9: "The `newtype` and `extern` marks live in the type's
`Matchable`, beside its `enum`/`union` tag, so eligibility is read off the
opened Matchable listing the constructor, which unifying two opened
Matchables forces equal too." DESIGN.md section 19's invariant already
forces the tag, the constructor count, each constructor's marker and the
constructors.

## The observation

The marks are two booleans in the `Matchable` term kept by structural
equality, so a mismatch contradicts rather than unifies, in both
implementations. That is what U9 says. But the `Matchable` former accepts
only the literal tokens, so an absent mark means "unmarked", not
"unknown": there is no meta or variable position for a mark, as there is
for the type and the constructors. A signature written
`(Matchable enum T (many Z) (many S))` can no longer receive `Nat`'s
Matchable at all:

```
error: type mismatch: expected (Matchable enum Nat (many Zero) (many Succ)),
                      got (Matchable enum extern Nat (many Zero) (many Succ))
```

The first-class regression tests were split into marked and unmarked
helpers because of this. Two opened Matchables differing only in a mark
contradict at the second `open-adt`, which appears to be what U9 wants.

## The question

Is losing mark-polymorphic first-class Matchable signatures intended, or
should the former admit a `_`-shaped mark position that unifies with
either? U9 and U17 do not mention the narrowing.
