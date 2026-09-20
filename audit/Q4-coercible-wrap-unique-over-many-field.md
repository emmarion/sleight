# Q4. `coercible-wrap (Unique)` over a many-labelled field mints unique aliases

Status: open question, ASSUMPTIONS 183. Spec-faithful; nothing found that
exploits it.

## The rule

UNIQUE.md U7: "`coercible-wrap` mints `s` as its target side and, as its
source side, `s` over a unique-labelled field and `(Shared)` over a
many-labelled one." U1: "A `unique` binder is the only reference to its
value."

## The observation

With `s` at `(Unique)` over a many-labelled field the proof is `(Shared)`
to `(Unique)`, so a live many value can be coerced into as many distinct
`unique` binders as one writes, all aliasing it:

```scheme
(def-adts $ B : -> Type enum newtype (many MkB : (many (Nat) n) -> (B)))
(let (many n) (Succ (Zero)))
(let (unique b1) (coerce n (coercible-wrap (Unique) MkB n)))
(let (unique b2) (coerce n (coercible-wrap (Unique) MkB n)))
(let (many k1) (coerce b1 (coercible-sym (coercible-wrap (Unique) MkB n))))
(let (many k2) (coerce b2 (coercible-sym (coercible-wrap (Unique) MkB n))))
(nat-add k1 k2)
```

prints `2`. The attempts to turn it into an unsoundness all failed: the
target of a `(Shared)`-to-`(Unique)` proof is always a newtype, which has
no cell, so nothing updates the wrapper in place; getting the field back
at unique needs a wrap whose source side is `(Unique)`, which U7 gives
only over a unique-labelled field; `coercible-trans` refuses the
composition U7's reading warns about; and a field's multiplicity cannot be
forged through a first-class `ValCtor` parameter, since telescope
multiplicities are part of type equality. A `unique` destructure of such a
wrapper hands the field out at `many` anyway.

## The question

U1's sentence is literally false for `b1` and `b2`. Is that acceptable as
long as newtypes have no in-place operation, or should
`coercible-wrap (Unique)` over a many-labelled field be refused, so that a
`unique` newtype wrapper is always really unique?
