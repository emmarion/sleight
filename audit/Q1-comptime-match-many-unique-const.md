# Q1. `comptime-match many` on a unique Const cannot write its `share`

Status: open question, ASSUMPTIONS 183.

## The rule

UNIQUE.md U5: `comptime-match` at `unique` "does not degrade a unique
Const, but merely consumes it at unique". U6: the elaborator's other reads
of a Const, a special form at a head or a Matchable a match reads, are
many uses, "comptime-match is not such a read". U3: degradation is written
`(share e)` where the value is used at many.

## The observation

Neither passage says whether the `many` mode's own read of the value is a
many use of the binder. The implementation treats it as one, and the
scrutinee of `comptime-match` must be a bare variable, so the `share`
cannot be written in place:

```scheme
; error: explicit share
(def-adts $ Box : -> Type enum (many B : (many (Nat) n) -> (Box)))
(let (unique x) (B (Succ (Zero))))
(comptime-match many x (B n))
n
```

The workaround is a preceding `(let (many y) (share x))`. Both
implementations agree.

## Related

`elab_comptime_match` does not record a many use of the scrutinee's
Matchable, while `match` and `let-match` do; U6's rule about a Matchable a
match reads arguably does not cover `comptime-match`, which verifies
against the stored value rather than dispatching, but the three forms
differ here. Also, `elab_let_match` has a readability check that can never
fire because `scrutinee` already performs it.

## The question

Is the `many` mode's read of the value a many use of the binder, in which
case the scrutinee should perhaps admit `(share x)`, or not a use, as the
`unique` mode's consumption is described?
