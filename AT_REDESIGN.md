# Redesign of `at`

A working document for the owner's proposal to redesign `at`, made in a
design session in chat. It records what the owner proposed and decided
there. It changes nothing in DESIGN.md or UNIQUE.md until its parts are
carried into them under CLAUDE.md rules 11 and 12. Section references
with `§` are to DESIGN.md, and with `§U` to UNIQUE.md. A passage marked
*reading* is a session's inference from the decisions, not a decision;
the TBDs and open questions are listed at the end. Names are tentative,
as CLAUDE.md rule 10 has them.

The direction is for the `at` system to subsume the existing `coerce`
system (§38, §U7), in stages; the core semantics come first, and the
relaxations in A12 wait until those are settled.

## A1. `Slot` is opaque

`Slot` stays a type but is treated like `Level` (§8): opaque, with no
constructors, so `SlotVacant` and `SlotHolds` (§U10) are gone, and no
`Matchable`. It is not erased by kind: a `Slot` binder may be `many`.

A global constant of type `(Slot)`, the **null slot**, is what an
allocation that provides nothing defaults to, in place of
`(SlotVacant)`.

## A2. Automatic slots

For every named non-erased variable without a written `at` (A5), the
elaborator inserts an anonymous `many` binder of type `(Slot)`, its
**automatic slot**, and the variable is `at` that slot. This applies to
function parameters and return entries, so a signature carries, in its
mental model, roughly twice as many non-erased entries, and to the
non-erased fields a match on a non-erased scrutinee binds, with the same
effect. Erased variables get none.

A `let` needs nothing of its own here: the entries of its right-hand
side enter the containing expression anonymously (§16), bringing their
slots with them.

An automatic slot is `at` itself. Only automatic slots are: a written
`at` cannot name the entry it is written on.

## A3. What reaches runtime

What reaches runtime is exactly the automatic slots. An entry with a
written `at`, as a parameter, a return entry or a match annotation
entry, is omitted after erasure: its word is the word of what it is
`at`, so it need not be passed. The number of non-erased words passed
and returned therefore stays what it is today.

Which entries reach runtime is read off the signature as written: the
runtime signature of a function is the non-erased entries without a
written `at`. It never depends on what an `at` canonicalizes to, which
may differ from one match branch to another.

## A4. `at` in the fact table

The at-database of §U8 is replaced. Every entry has, beside its type and
its `is` (§3, §18), an **at**: as its type must canonicalize to a type,
its at must canonicalize to a `(Slot)`. Whether two variables are at one
slot is then decided by the fact table's ordinary canonicalization.

## A5. Written `at`

In a function's parameter or return telescope, an entry may be written
`at` an earlier entry or a variable from an enclosing scope. The target
must be non-erased.

The target is a `many` or `unique` variable `v` of any type, not
necessarily a `(Slot)`. The entry's at (A4) is `(slot-of v)`, always,
even where `v` is itself a slot.

Neither `at` nor `slot-of` (A6) may appear in the telescope of a type
constructor or a value constructor.

## A6. `slot-of`

`(slot-of x)`, for a non-erased variable `x`, denotes `x`'s at. The
elaborator replaces it with a reference to a real entry in the fact
table, which is why it may appear in type-like positions, function
telescopes included: for an `x` without a written `at`, its automatic
slot; for an `x` written `at v`, which has none (A2), a slot the fact
table equates with `(slot-of v)`.

`(slot-of x)` is not a use of `x` (§U2).

*Reading:* after replacement `x` does not occur, so `(slot-of x)` stays
allowed after `x` is consumed.

## A7. `slot-self`

`(slot-self s)`, an expression, takes a non-erased variable `s` in
scope whose type canonicalizes to `(Slot)` and yields a proof that
`(slot-of s)` and `s` are `is`-equal.

*Reading:* a `Slot` the user binds is an ordinary non-erased variable,
so it has an automatic slot of its own and is omitted after erasure
(A3); `slot-self` is how a program learns what is always true at
runtime, that a slot's word is itself.

## A8. Cells at `many`

A `match` at `many` gives a cell as well, as one at `unique` does
(§U5), the cell being at `many` rather than at `unique`; otherwise
everything is as at `unique`. The cell binder is mandatory in both
modes, and in both it is `at` the scrutinee (§U5), so it gets no
automatic slot (A2).

A `cell-write` at `many` copies: the new cell is not `at` the old one.
So does an invocation of a cell at `many` that is not full-at. A full-at
invocation of a cell at `many` costs nothing at runtime.

## A9. At-matches

A match is an **at-match** when its return annotation is written in an
`at` form, the usual annotation telescope inside it:

```scheme
(match many xs (at (((List (Nat)) ns at xs)))
  ...)
```

Every entry of its annotation is erased or `at`. An at-match skips its
runtime. Its branches erase to nothing, or to a reordering of
variables.

## A10. At-functions

A function is an **at-function** when its `def-fns` line puts `at`
before its name:

```scheme
(def-fns L $ (many at unwrap : ...) ...)
```

Its return entries are all erased or `at`; its parameters are not
restricted. Its body erases to nothing, or to a reordering of
variables. Calling an at-function skips its runtime.

Being an at-function is not part of the function's type. As for
`Delegate` (§38), `def-fns` mints an erased proof object for it, a
fetch form in the manner of `delegate-of` yields it, and a new form
opens it.

*Reading:* the type alone could not decide it. `array-place` (§U13)
returns only an `at` entry and an erased proof, so a call returns no
word, yet the call writes into the array and cannot be skipped. What
makes a call skippable is the body, a fact about the definition, as a
`delegate` body is.

A call may be asserted to be a call of an at-function by wrapping it,
`(at (f ...))`, as the full-at form wraps a cell invocation (§U9). The
assertion is optional and a hard error when it fails. A call through a
first-class `f` is skipped only where an at-function proof for `f` is
opened. Such a call still carries its `predates` or `subterm` proof
(§9).

## A11. Delegates

A `delegate`-bodied function (§9) may write `at` after its name,
followed by the function it delegates to:

```scheme
(def-fns L $ (many g at f : ...) (delegate (f ...)))
```

For now the annotation is optional. Where it is written it must be
accurate.

## A12. To be decided

Loosenings, deliberately left out of the first version so that the core
semantics are settled first:

1. Relaxing §12's one-real-branch rule for an at-match, which does not
   dispatch at runtime.
2. Allowing the function in an `at` call to be erased, as a
   `Coercible` proof is erased today.
3. Further changes around erasure.

## A13. Open questions

1. The names of the null slot, the at-function proof's type, its fetch
   form and the form that opens it.
2. The type of `slot-self`'s proof, for instance the prelude's
   `(Eq (Slot) (slot-of s) s)`, erased.
5. Whether a `Cell` type's indices become slot terms, `(slot-of f)` in
   place of `(SlotHolds f)` and the null slot in place of
   `(SlotVacant)`.
6. Soundness: two `Slot` terms that canonicalize equal must denote one
   word at runtime. Forcing in a branch may equate two `Slot` atoms, as
   it may two `Level` atoms. ASSUMPTIONS 183 notes that a user type
   indexed by `(Slot)` already reaches the corresponding merge.
8. What becomes of `coerce`, `Coercible`, the `coercible-*` forms,
   `Delegate` and §U15's `at-coercible` as the subsumption proceeds.
9. The exceptions to A8's cell binder, presumably those §U5 has today:
   a newtype, an extern type outside its model's body, a phantom
   constructor.

## A14. `at-coercible` deferred further

§U15's `at-coercible`, as stated today, is potentially unsound, and is
deferred further.
