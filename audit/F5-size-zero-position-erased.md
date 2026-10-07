# F5. A size-zero position treated as erased

Status: fixed in `fa5747a` (`lib/elab.ml` `pos_of`; `self/core.sl`
`PosOf`, `pos-of`, `pos-mult`; `self/elab.sl` `single`); tests
`tests/zero_size_tail.sl`, `tests/zero_size_use_bad.sl`. Severity:
rejects a valid program, and a use-counting gap. This fix rests on a
reading; see the caveat. ASSUMPTIONS 182.

## The rule

DESIGN.md section 27: `(values)` is the size-zero expression. Section 14
lists the erased positions and closes "Every other position is
non-erased". Section 54 says a zero-binder `let` "is expected to matter
once linear or unique types arrive, invoking a destructor, or similar".
DESIGN.md section 36 speaks of "a tail call from a function returning none"; section 15
requires exactly one non-erased use of a unique binder per path.

## The defect

`pos_of` answered Erased when every expected multiplicity was Erased, and
`List.for_all` is vacuously true of the empty list. So every size-zero
expression elaborated as if in an erased position: the usage-erased flag
was set, so nothing in it counted as a use, and the `tail`/`delegate`
guard refused a mark there. Self mirrored this in `pos-mult` and in the
`PosOf` proof's `PoNil` constructor.

## Reproducers

A `tail` mark in a body returning nothing was refused as "tail in an
erased position":

```scheme
; expect: 0
(def-fns _ $ many g : (many (Nat) n) -> (values))
(def-fns _ $ many f : (many (Nat) n) -> (tail (g n)))
(let (f (Zero)))
(Zero)
```

A call in a size-zero position consumed nothing, so this was accepted:

```scheme
; error: conflicting non-erased uses
(def-fns _ $ many drop : (unique (Nat) n) ->
  (let (many a) (share n))
  (values))
(def-fns _ $ many f : (unique (Nat) n) -> (many (Nat) r)
  (let (drop n))
  (share n))
(f (Succ (Zero)))
```

## The fix

An empty expectation is `Many`. In self the `PosOf` relation gained a
base constructor for the singleton erased list, its step now requires a
non-empty rest, and the empty list's constructor is indexed `(Many)`, so
`single`'s erased arm reads one constructor instead of two. F7 is the
companion change that makes the emitted code agree.

## Caveats

Section 14's clause "the final expression of the right-hand side of a
`let` whose binders are all `erased`" is vacuously met by no binders, and
section 15's remark that `(let (values))` "needs no new meaning" shows the owner
considered zero-binder lets. Under that reading the second reproducer is
not a bug and only the `tail` guard needed relaxing. The fix takes the
non-erased reading because of section 14's closing sentence, section 54's
destructor motivation, and section 36's phrase; the owner may prefer the other,
in which case `pos_of` reverts and the `tail`/`delegate` guard alone
changes.
