# F9. The untyped printer overflows the stack on a cycle through a slot word

Status: fixed in `66d05b6` (`lib/value.ml` `show`). Severity: crash.

## The rule

DESIGN.md section 38: a slot's value "is inert and may sit in a field or a list
like any other value". ASSUMPTIONS 163 says a printed Slot or Cell is
opaque and "its arbitrary held word is not recursively interpreted".

## The defect

That claim held for the typed printer, which renders a slot as `<slot>`.
But `Elab.show_value` degrades to `Value.show` on any failure, and
`Value.show` walked constructor fields and extern array elements with no
cycle guard. A value that made the typed walk raise, easiest through a
`union` whose first candidate's arity differs from the value's, reached
the untyped walk, which followed the slot word round the cycle until the
stack overflowed.

## Reproducer

```scheme
(def-adts $ UC : -> Type union
  (many UC0 : -> (UC))
  (many UC1 : (many (Slot) s) -> (UC)))
(let (unique a) (erased all) (array-new (Slot) (Succ (Zero))))
(let-match erased all (AUCons _ _ _ q))
(let-match erased q (AUNil _))
(let (unique b) (erased placed)
  (array-place _ _ a (Zero) (Init _ (SlotHolds a)) _ (NthZ _ _ _ _)))
(let-match erased placed (SetZ _ _ _ _ _))
(let (many u) (UC1 (SlotHolds b)))
u
```

Before: `Fatal error: exception Stack overflow`. After: prints
`(UC1 (ACons <cycle> (ANil)))`.

## The fix

`Value.show` carries the values it is inside and prints `<cycle>` on
meeting one again. The self-hosted printer is fuel-bounded already.

## Caveats

The text `<cycle>` is a display choice the owner has not confirmed. This
program is not a test, because the extracted program prints `_` for it:
that disagreement is B1.
