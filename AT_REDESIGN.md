# Redesign of `at`

A working document for the owner's proposal to redesign `at`, made in a
design session in chat. It records what the owner proposed and decided
there. It changes nothing in DESIGN.md or UNIQUE.md until its parts are
carried into them under CLAUDE.md rules 11 and 12. Section references
with `§` are to DESIGN.md, and with `§U` to UNIQUE.md. The TBDs and
open questions are listed at the end. Names are tentative,
as CLAUDE.md rule 10 has them.

The direction is for the `at` system to subsume the existing `coerce`
system (§38, §U7), in stages; the core semantics come first, and the
relaxations in A12 wait until those are settled. In version one the
`coerce` machinery does not change (A12).

## A1. `Slot` is opaque

`Slot` stays a type but is treated like `Level` (§8): opaque, with no
constructors, so `SlotVacant` and `SlotHolds` (§U10) are gone. It is not erased by kind: a `Slot` binder may be `many`.

A global constant of type `(Slot)`, the **null slot**, written
`vacant-slot`, is what an
allocation that provides nothing defaults to, in place of
`(SlotVacant)`.

A `Cell` type (§U9) is indexed by slot terms: `(slot-of f)` in place of
`(SlotHolds f)`, and the null slot in place of `(SlotVacant)`.

## A2. Automatic slots

For every non-erased variable without a written `at` (A5), named or
anonymous, the elaborator inserts an anonymous `many` binder of type `(Slot)`, its
**automatic slot**, and the variable is `at` that slot. This applies to
function parameters and return entries, so a signature carries, in its
mental model, roughly twice as many non-erased entries, and to the
non-erased fields a match on a non-erased scrutinee binds, with the same
effect. Erased variables get none. As an invariant, every `many` or
`unique` entry of the fact table has a corresponding slot: an argument
bound first (§U2a), the anonymous entries a `let`'s right-hand side
brings in, and a constructor application's own entry (§3) included.

A `let` needs nothing of its own here: the entries of its right-hand
side enter the containing expression anonymously (§16), bringing their
slots with them.

An automatic slot is `at` itself. Only automatic slots are: a written
`at` cannot name the entry it is written on.

## A3. What reaches runtime

What reaches runtime is exactly the automatic slots. An entry with a
written `at`, as a parameter, a return entry or a match annotation
entry, is omitted after erasure: its word is the word of what it is
`at`, so it need not be passed. A signature written today therefore
passes and returns as many words as it does today.

Which entries reach runtime is read off the signature as written: the
runtime signature of a function is the non-erased entries without a
written `at`. It never depends on what an `at` canonicalizes to, which
may differ from one match branch to another.

## A4. `at` in the fact table

The at-database of §U8 is replaced. Every non-erased entry has, beside its type and
its `is` (§3, §18), an **at**: as its type must canonicalize to a type,
its at must canonicalize to a `(Slot)`. Whether two variables are at one
slot is then decided by the fact table's ordinary canonicalization.

## A5. Written `at`

As in §U8, a function's return entries and a match's annotation entries
may be written `at`; in addition, a function's parameters may be, and
the target may be any earlier entry of the telescope, a return entry
included, or a variable from an enclosing scope. The target must be
non-erased.

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

## A7. `slot-self`

`(slot-self s)`, a statement (§16), takes a non-erased variable `s` in
scope whose type canonicalizes to `(Slot)` and mints, outward, the fact
that `(slot-of s)` and `s` are `is`-equal. It yields no proof object. It is a
compile error if minting the fact leaves the fact table contradictory;
we currently believe that cannot happen.

## A8. Cells at `many`

A `match` at `many` gives a cell as well, as one at `unique` does
(§U5), the cell being at `many` rather than at `unique`; otherwise
everything is as at `unique`, except what the cell mints: a cell at
`unique` may mint its value at `unique`, while a cell at `many` mints
its value only at `many`. The cell binder is mandatory in both
modes, and in both it is `at` the scrutinee (§U5), so it gets no
automatic slot (A2). Which constructors have no cell binder is the same in both
modes as at `unique` today (§U5, §U9): a newtype's, an extern type's
outside its model's body, and a phantom constructor's.

A `cell-write` at `many` copies: the new cell is not `at` the old one,
and is itself at `unique`, so a write whose items are all `_` copies a
shared block into a unique cell.
So does an invocation of a cell at `many` that is not full-at. A full-at
invocation of a cell at `many` costs nothing at runtime. Invoking a
cell at `unique` to mint a `unique` value consumes the cell (§U9).

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
`Delegate` (§38), `def-fns` mints an erased proof object for it, of
type `(AtFn F f)` for a function `f` of type `F`, the first half of
`Delegate`'s shape; `(at-fn-of f)` fetches it, in the manner of
`delegate-of`, and a new form, `open-at-fn`, opens it. The proof is
minted when a header claiming `at` is elaborated, before the block's
bodies, so a call within the block to a function so marked is skipped;
a body that then fails to erase to nothing is a compile error.

A call may be asserted to be a call of an at-function by wrapping it,
`(at (f ...))`, as the full-at form wraps a cell invocation (§U9). The
assertion is optional and a hard error when it fails. A call through a
first-class `f` is skipped only where an at-function proof for `f` is
opened. Such a call still carries its `predates` or `subterm` proof
(§9).

The prelude is eventually to gain extern at-functions over arrays,
inside whose bodies cells reappear, which takes the subsumption of
`coerce` further. A function marked both `extern` and `at` has no FFI
implementation: the marks are a promise. It is still legal to treat it
as an ordinary function for higher-order purposes, including passing it
to a function that expects a function and does not know it is an
at-function, so the compiler emits a dummy function for it, and
invoking that cannot crash.

## A11. Delegates

A `delegate`-bodied function (§9) may write `at` after its name,
followed by the function it delegates to:

```scheme
(def-fns L $ (many g at f : ...) (delegate (f ...)))
```

For now the annotation is optional. Where it is written it must be
accurate.

## A12. To be decided

Left for later: loosenings deliberately left out of the first version
so that the core semantics are settled first (1-3), and follow-up work
(4-5, 11).

1. Relaxing §12's one-real-branch rule for an at-match, which does not
   dispatch at runtime.
2. Allowing the function in an `at` call to be erased, as a
   `Coercible` proof is erased today.
3. Further changes around erasure.
4. Version two: what becomes of `coerce`, `Coercible`, the
   `coercible-*` forms and `Delegate`. This needs further work; if it
   works out, perhaps with some tweaks, they are all deleted. In
   version one they do not change.
5. §U14's tier 1 list, to be extended with the new forms: the `at`
   mark on at-functions and at-matches, cells from `many` matches,
   `slot-of`, `slot-self` and `vacant-slot`.
11. The prelude's `array-pluck`, its signature changed so that the slot
   it returns is exactly the slot of the value it returns, `(Uninit A
   (slot-of v))` in its `ASet` proof for the `v` it returns, and an
   `extern at` function that puts a plucked value back. The motivating
   example: a jagged array's row, or any unique value mutated inside an
   outer array, is taken out with `array-pluck`, mutated in place, and
   put back by an at-function whose call is erased, so that putting it
   back costs nothing.

## A13. Open questions

6. Soundness of slot equality: what the claim must be, and whether it
   holds. The owner believes the system is sound.

## A14. `at-coercible` deferred further

§U15's `at-coercible`, as stated today, is potentially unsound, and is
deferred further.
