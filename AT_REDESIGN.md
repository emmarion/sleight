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
relaxations in A12 wait until those are settled. In version one the
`coerce` machinery does not change (A12).

## A1. `Slot` is opaque

`Slot` stays a type but is treated like `Level` (§8): opaque, with no
constructors, so `SlotVacant` and `SlotHolds` (§U10) are gone, and no
`Matchable`. It is not erased by kind: a `Slot` binder may be `many`.

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

In a function's parameter or return telescope, or a match's return
annotation (§U8), an entry may be written `at` an earlier entry or a
variable from an enclosing scope. The target
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

`(slot-self s)`, a statement (§16), takes a non-erased variable `s` in
scope whose type canonicalizes to `(Slot)` and mints, outward, the fact
that `(slot-of s)` and `s` are `is`-equal. It yields no proof object. It is a
compile error if minting the fact leaves the fact table contradictory;
we currently believe that cannot happen.

*Reading:* a `Slot` the user binds is an ordinary non-erased variable,
so it has an automatic slot of its own and is omitted after erasure
(A3); `slot-self` is how a program learns what is always true at
runtime, that a slot's word is itself.

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
and is itself at `many`.
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

*Reading*, of "erase to nothing" here and in A10: what is left after
erasure, once `at` returns, full-at invocations (§U9), calls of
at-functions and at-matches are dropped as erased, is nothing but
`let`s that rename. Without those drops a recursive at-function such as
A16's would not qualify.

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
`delegate-of`, and a new form, `open-at-fn`, opens it.

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

An extern type has no cells outside its model's body (§U12). The
prelude is eventually to gain extern at-functions over arrays, inside
whose bodies cells reappear, which takes the subsumption of `coerce`
further: an `Array` conversion such as §U13's `init-witness` then need
not go through `coerce`.

## A11. Delegates

A `delegate`-bodied function (§9) may write `at` after its name,
followed by the function it delegates to:

```scheme
(def-fns L $ (many g at f : ...) (delegate (f ...)))
```

For now the annotation is optional. Where it is written it must be
accurate.

*Reading:* §9's pass-through check is then judged on A3's runtime
shape, the entries without a written `at`; a parameter written `at` is
passed as no word of its own.

## A12. To be decided

Loosenings, deliberately left out of the first version so that the core
semantics are settled first:

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

## A13. Open questions

6. Soundness: wherever two `Slot` terms canonicalize equal, they must
   denote one word at runtime, since skipped stores, omitted `at`
   entries and skipped at-functions all rest on it. The owner believes
   the system is sound. *Reading:* equalities from a written `at`, from
   `slot-self` and from forcing in a `many` or `unique` match look
   honest by induction over construction; forcing in erased code rests
   on §10's consistency claim, as every forced fact does, though a false
   slot fact would corrupt memory rather than merely prove something
   false. `Slot` having no constructors and no `Matchable`, forcing may
   equate two slots but never refutes a branch over them, and nothing
   relies on two slots being distinct. ASSUMPTIONS 183 notes that a
   user type indexed by `(Slot)` already reaches the corresponding
   merge.

## A14. `at-coercible` deferred further

§U15's `at-coercible`, as stated today, is potentially unsound, and is
deferred further.

## A15. Reading: the null slot and `MaybeUninit`

*Reading*, not a decision. With `(slot-self null)`, the null slot is its
own at, so a full-at invocation of a cell from `(cell-alloc Uninit)`
with the null slot as its argument checks with no store. `(Uninit A
(slot-of v))` and `(Init A v)`, both newtype applications at their
non-erased argument (§U9), are at one slot: §U13's `MaybeUninit`
without a special case. Two different values at one slot are fine, no
form turning sharing a slot into being one value.

## A16. Worked example: unwrapping a list

Written against the rules above, not machine-checked: nothing
implements them yet. §40's `unwrap-all` as an at-function, with no
`Coercible`:

```scheme
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-fns _ $ (many at unwrap : (subterm many (List (Meters)) ms) ->
    (many (List (Nat)) ns at ms))
  (match many ms (at (((List (Nat)) r at ms)))
    ((Nil _ u) (at (u _)))
    ((Cons _ m tl u)
      (let-match many m (MkMeters n))
      (let ((many r)) (unwrap tl))
      (at (u _ n r)))))
```

- The `many` match gives each branch a cell `u` at `ms` (A8).
- `n` is at `m`, a newtype destructure putting its field at the
  scrutinee (§U9), and `r` is at `tl` by `unwrap`'s own return.
- So `(u _ n r)` is full-at, the cell's slots being `m`'s and `tl`'s,
  and mints `(Cons (Nat) n r)` at `ms`, at `many` as a cell at `many`
  must (A8). After the drops of A9's reading the body is nothing, and a
  call of `unwrap` skips its runtime.
