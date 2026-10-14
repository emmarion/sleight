# F8. The extractor asserts false printing a union or newtype value

Status: fixed in `66d05b6` (`lib/extract.ml` `show`); test
`tests/show_union_newtype.sl`. Severity: crash of extraction, and a
divergence between the reference and the self-hosted compiler.

## The rule

DESIGN.md section 42's invariant and OPEN.md 2's tiers require a
program to compile in every mode. Section 44 declares `MaybeUninit` as `union
newtype` with two constructors.

## The defect

`Extract.show` builds one printing arm per constructor the value's type
does not refute and hands them all to `dispatch`. For the `Union` and
`Untagged` shapes, which have no runtime discriminant, `dispatch` accepts
at most one arm and has `assert false` for more. So extracting any program
whose printed final value contains a `MaybeUninit`, an
`(Array (MaybeUninit A) n)` included, died with an OCaml assertion, while
the interpreter printed the value. The self-hosted emitter already kept
only the first arm, so it did not share the defect.

## Reproducer

```scheme
; expect: _
(def-adts $ MU : (Type A) -> Type
  union newtype
  (many MUNone : (erased Type A) -> (MU A))
  (many MUSome : (erased Type A) (unique A value) -> (MU A)))
(let (many m) (MUSome _ (Succ (Zero))))
m
```

## The fix

For a discriminant-free shape keep the first arm, which is what the
interpreter's typed printer and the self-hosted emitter do.

## Caveats

This removes the crash but does not decide what such a value should print
as; see B1 for the remaining disagreement between the interpreter's
fallback rendering and the extracted one.
