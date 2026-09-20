# F6. A type former's head recorded as a use, inconsistently across positions

Status: fixed in `fa5747a` (`lib/elab.ml` `elab_term`, `self/elab.sl` the
type-form branch of the term elaborator); tests
`tests/type_head_unique_const.sl`,
`tests/type_head_unique_const_degrade.sl`. Severity: rejects a valid
program, and an internal inconsistency. This fix rests on a reading; see
the caveat. ASSUMPTIONS 182.

## The rule

DESIGN.md section 20 lists "a type or `is` expression" among the erased
positions. UNIQUE.md U2: "An erased mention is never a use and is allowed
anywhere, before or after the binder is consumed: a proof or a type may
name a consumed value." U6: where the elaborator must read a Const as a
value, "a special form or macro at a head (section 4)", that read is a
many use.

## The defect

`elab_term`, the pure type elaborator, called `read_special` on a type
former's head, which records a many use of the head's entry. `elab_term`
is not wrapped by `elab_expr`, so the usage-erased flag was whatever the
enclosing expression left: false in a `let` binder's annotation and in a
match annotation, where the use was recorded, but in a `def-fns`
signature the environment is discarded, so the same mention counted for
nothing. Reachable only when a type former is shadowed by a unique
binder, so the practical reach is small.

## Reproducer

```scheme
; expect: 1
(def-lvl lv)
(def-fns lv $ many idf : (many (Nat) n) -> (many (Nat) r) n)
(let (unique u) (%Fn))
(let (many (u lv (many (Nat) n) -> (many (Nat) r)) g) idf)
(g (Succ (Zero)))
```

Before the fix: "unique value u needs an explicit share". Written with the
`share`, the annotation degraded `u`, so a later unique use of `u` was
refused, while the same annotation in a `def-fns` parameter telescope was
accepted.

## The fix

Drop the `read_special` in the type elaborator. The expression-head and
statement-head reads are unchanged.

## Caveats

This reads section 20 and U2 as controlling: a type former's head is a
section 5 position, not a section 4 dispatch, and sits in an erased
position. If the owner means U6's rule to cover every Const read, type
formers included, the signature path is the one that was wrong and the
fix goes the other way. Either way the two paths must agree.
