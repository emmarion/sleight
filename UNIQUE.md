# Uniqueness: a supplement to DESIGN.md

Read after DESIGN.md. It records what the owner decided, in a design
session over the owner's proposal for unique types, on top of the
language DESIGN.md describes; DESIGN.md itself is unchanged, and where
it says linear or unique types are punted (§6) this file is the
continuation. Section references with `§` are to DESIGN.md. A passage
marked *reading* is a session's inference from the decisions, not a
decision; §U15 lists what is not decided, as questions. Names are
tentative throughout, as CLAUDE.md rule 10 has them.

## U1. A third multiplicity, and a fourth match mode

A binder may be declared `unique` beside `erased` and `many` (§6, §20):
function parameters and return entries, constructor fields, `let`
binders, and a match's scrutinee. A `unique` binder is the only
reference to its value, which is what lets an operation on it run in
place; the guarantee is the binder's, not the type's, so there is no
unique type, no unique type or value constructor, and no phantom
analogue. `match`, `let-match` and `comptime-match` gain two modes,
`unique` and `peek` (§U5); `peek` is a match mode only, never a
binder's multiplicity.

## U2. Uses

Each binder is checked by the uses it has on each path through the
code, with no order among them. On one path a `unique` binder may have
at most one non-erased use, and that use is either the one unique use
or any number of `many` uses; a unique use beside any other non-erased
use of the same binder is an error, whichever the elaborator meets
first. The order in which such errors are reported is implementation-
dependent. An erased mention is never a use and is allowed anywhere,
before or after the binder is consumed (§20's erased positions): a
proof or a type may name a consumed value.

Over the branches of a match, a binder's state afterwards is the
maximum of its states after each branch in the order unused, then used
at many, then used at unique, where "used at many" leaves the binder
usable at many and never at unique, and "used at unique" leaves it
usable only erased. Three kinds of branch contribute nothing, having no
non-erased mention: an `(absurd C)` branch, an absurd-by-proof branch,
and a phantom constructor's branch under a `many`, `unique` or `peek`
scrutinee, whose body is elaborated with everything erased (§12). An
`else` branch has an ordinary body and takes part like any other.

A `unique` value need not be used: GC reclaims it (the proposal's
"at most one use"), and `(let (values))` needs no new meaning.

## U3. Born unique, degraded explicitly

A `unique` value is born unique: a fresh constructor application in a
unique position, a `unique` return of a call, a `unique` field taken by
a `unique` destructure (§U4), or an extern that mints one (§U12).
Nothing turns a `many` or erased value unique, except as §20 already
has it in an erased position or a phantom branch, where nothing runs.

Degradation from `unique` to `many` is explicit: a `unique` binder in a
`many` position is an error unless the degradation is written (the
form's name is open, §U15). The written degradation is that binder's
many use, after which it is usable at many everywhere and never again
at unique.

## U4. Fields

A field is labelled `erased`, `many` or `unique`. What a destructure
hands out for a field, by the scrutinee's mode:

| field label | `erased` | `many` | `unique` | `peek` |
|---|---|---|---|---|
| erased | erased | erased | erased | erased |
| many | erased | many | many | many |
| unique | erased | many | unique | erased |

A unique-labelled field under a `many` scrutinee comes out `many`: a
shared cell shares everything it owns, with no per-field bookkeeping.
Construction is the dual, by the position's multiplicity:

| field label | erased position | many position | unique position |
|---|---|---|---|
| erased | erased | erased | erased |
| many | erased | many | many |
| unique | erased | many | unique |

A `unique` field of a constructor built at `many` is requested at
`many` (the proposal's 1e). §12's warning for a phantom constructor with
a `many` field covers a `unique` one too.

## U5. The new match modes

`(match unique x ann branches)` consumes `x` and binds each branch's
fields per §U4's `unique` column. `(match peek x ann branches)` is also
a use of `x` at unique, and gives the value back: each branch binds a
fresh `unique` binder that `is x` and is `at x` (§U8), so the
discipline stays order-free (a peek after the binder is consumed is the
usual conflict) and nothing restores a consumed binder in place.

Both modes add one binder to every pattern, after the fields, mandatory
and `_` when unwanted (§U16): at `unique` it names the cell the
constructor occupied, a UniqueCstr at `x` (§U9); at `peek` it names the
returned value. A branch gets it out of the match through an `at`
entry of the annotation (§U8). At `peek` the `else` branch binds it
too, `(else x2 body)`, the value being the same whichever constructor
the else stands for; this is the first `else` that binds anything. At
`unique` an `else` binds nothing, the cell's constructor being unknown,
and the consumed cell is dropped.

`let-match` takes the same modes and the same extra binder, binding
outward as before (§16). `comptime-match` at `unique` is a destructure
like any other and does not degrade a unique Const; the elaborator's
other reads of a Const (a special form or macro at the head, a
Matchable read, §U6) do. Readability requirements for a dispatching
match are as in §19.

*Reading.* On a source type `peek` is a `unique` destructure followed by
a full-at reinvocation of the same constructor at the scrutinee (§U9),
which costs nothing; on an extern type it is primitive, through the
FFI's peek unwrap (§U12).

## U6. Closures and the top level

A function defined by `def-fns` is a closure over its scope and may
mention a `unique` binder of that scope only erased or, after an
explicit degradation, at many; the proposal's `def-unique` defines a
function of a new former, UniqueFn, that may close over `unique`
binders as unique, consuming them, and is itself callable only from a
`unique` binder, or erased. Its shape and level are open (§U15).

A top-level binder, and so a Const (§34), may be `unique` under the same
rules, run-position statements being sequential. A unique Const the
elaborator must read as a value, a special form or macro at a head (§4)
or a Matchable a match reads, is degraded to many by that read;
`comptime-match` is not such a read (§U5).

## U7. `Coercible` with multiplicities

`Coercible` (§38) gains a multiplicity on each side: `Coercible m_a A a
m_b B b`. A minting form chooses the target side, and the source side
of each field is the multiplicity a constructor application at the
target side would use that argument at, the meet of the target side and
the field's label (§U4's construction table). So `coercible-wrap` over
a many-labelled field yields Many to Many or Many to Unique, over a
unique-labelled field Many to Many or Unique to Unique; `coercible-ctor`
applies the meet per field on each side; `coercible-refl` is uniform;
`coercible-of` is Many to Many, a function value never being unique.
`coercible-sym` is unconditional, every mintable shape being uniform or
the harmless "unique wrapper of a many field to its field at many";
`coercible-trans` requires the middle multiplicities equal; and any
proof weakens to Many on both sides (the proposal's 1j). `(coerce a p)`
in a position of multiplicity `m` uses `a` at `m_a` and yields its
result at `m_b`, an error where `m_b` is Many and `m` is Unique.

*Reading.* Without the sides, a proof composed through two newtypes of
one field type, one labelled `many` and one `unique`, would carry a
many value into a unique-labelled wrapper; the sides refuse it at
`coercible-trans`. A newtype's shape (§38) reads "exactly one
non-erased field".

## U8. `at`

A return entry of a function's telescope, or an entry of a match's
annotation, may add `at v`: the value returned is at the same location
as `v`, a non-erased argument for a function, a non-erased closed-over
variable for a match or a UniqueFn. The promise is verified where the
function or branch returns; a phantom branch under a non-erased
scrutinee, an absurd branch, a refuted branch and an `erased` or
`absurd` function are exempt. An `at` return may be `many`, and may
combine with `is`: a read of a unique array is `(unique a is r at a)`.

Beside the fact table the elaborator keeps the **at-database**, a
partition of scope entries into classes of one location. Its writers,
and nothing else: a destructure at `unique` (the minted UniqueCstr with
the scrutinee), a placement invocation (the new value with its
UniqueCstr), `coerce` (its result with its source), a forwarding `let`
(§9), a call's `at` return, and a match's `at` result. A forced atom
rule from entering a branch does not merge classes, and neither does
canonical equality: two separately built cells with equal contents are
`is`-equal and are two blocks. It is read by binder, before
canonicalization, and a membership ends with the scope that minted it.
A class may hold consumed entries; address equality does not change
when contents do.

An `at` return is absent from a call's physical values in every
implementation, as an erased return is; a `let` binds it as any
return, and the elaborator supplies its word from the argument the
promise names. The `tail` and `delegate` checks (§9) read the
post-erasure code with `at` returns dropped from a call's results, as
they read coerces as renamings, so a call whose only non-erased results
are `at` returns is a tail call from a function returning none.

## U9. Placement: UniqueCstr and the invocation

For a type that is neither `newtype` nor `extern`, a value constructor
`C` has a cell type `(UniqueCstr C s1 ... sn)`, a type former (§5) with
one `Slot` (§U10) per non-erased field of `C`. A cell is obtained by an
allocation form (open, §U15), every slot `SlotVacant`, or by a
destructure at `unique` (§U5), each slot `(SlotHolds f)` for the
field's binder `f`, the cell being at the scrutinee. Since every such
type must be a real block for this, an unmarked type of newtype shape is
no longer represented as its field (§38's leeway is withdrawn), and a
constructor with no non-erased field has an empty cell.

**Invocation.** A UniqueCstr-typed head is a fourth applicable type in
§4's tier 1: `(u a1 ... an)` is a constructor application that mints
`(C a1 ... an)` at `u`, using each argument at the field's multiplicity
as `(C a1 ... an)` would, and consuming `u` at `unique` whatever the
position's multiplicity, so a `many` value may be built this way. An
argument followed by `(at)` asserts that the slot already holds it,
its variable being in the slot's `SlotHolds` class, and the store is
skipped; a hard error otherwise, as for `tail`. A full-at invocation,
every argument so marked (its spelling is open), performs nothing and
is treated as erased by the `tail` and `delegate` checks, as a `coerce`
is, so it may follow a tail call.

**Writes.** A write form (spelling open) takes the cell at `unique` and,
per non-erased field, a `Slot` value or an omission, and returns at
`unique` a cell whose type records the slots written. A write is a
physical store into memory the invocation will re-mint; it does no
usage accounting, whatever its raw refers to, the invocation being the
semantic mint.

*Reading.* Under these rules a slot can never end up referencing a cell
owned elsewhere in a minted value: the invocation supplies each field
at its multiplicity, so a consumed unique cannot be named there.

## U10. `Slot` and `cstr-let`

`Slot` is a nullary type with two value constructors, `SlotVacant` and
`(SlotHolds v)`, `v` a fact-table variable (§3), never a telescope
binder; a signature that speaks of a slot abstracts over it as an
erased `(Slot)` parameter, `(erased (Slot) s) (unique (UniqueCstr Pair2
s s) u)` saying its two slots hold one thing. A `SlotHolds` term is
handled by the at-database and not the fact table: its argument is not
rewritten by `is` rules, canonicalizing it takes the argument to its
at-class, two `SlotHolds` are equal exactly when their arguments share a
class, and a forcing unification merges the classes. `Slot` is not
matchable. At runtime a slot's value is the word in it.

`cstr-let` reads a cell's words out, a statement binding outward:
`(cstr-let many u (C s1 ... sn))` with `u` at many, never degrading it
(degradation being explicit, `u` must already be many), and
`(cstr-let peek u (C s1 ... sn u2))` with `u` at unique, `u2` the cell
given back as §U5's peek does. The `si` are fresh `many` binders of
type `(Slot)`; one forced unification of `(UniqueCstr C s1 ... sn)`
against `u`'s type mints their `is` rules, as entering a branch unifies
a scrutinee's type (§18). It decides nothing about a slot: an `si` is
whatever `u`'s type said, a `SlotHolds`, a `SlotVacant`, or an abstract
slot. What the words are for is a write into another cell and §U14's
comparison.

## U11. Tail call modulo cons, a reading

*Reading.* `map` over a list allocates a cell, writes the head, and
calls a helper in destination-passing style with the cell and the tail,
the helper's return being `at` the cell; the helper allocates the next
cell, writes it into the tail slot, tail-calls itself, and follows the
call with a full-at invocation, which is erased for the check. The
helper holds the head at `many`, since the invocation uses it there, so
a cell's slot type in a signature says nothing the helper cannot supply.
The outer `map` is a plain call and returns the value.

## U12. Extern types and functions

A `unique` value of an extern type is the FFI's to mutate in place. Two
binding constraints on the FFI author, beside §41's: the FFI supplies a
peek unwrap beside its match unwrap, returning the discriminant and the
many-labelled fields and sharing nothing mutable (today's String view
shares its buffer, which a mutable type may not); and an `at` return
promised by an extern's signature is honoured physically, the model's
body being checked against the promise like any body, so such a model
is written with §U9's placement over its own cells. Part 1 of the
proposal is useful before parts 2 to 4 exist: an update `(unique (Array
A) a) ... -> (unique (Array A) r)` is O(1) and returns one word the
caller already holds. Placement is not available on an extern type.

*Reading.* In the prototype an extern type's construction and matching
live in its ADT record and run through one dispatch for a Const-known
and a held Matchable alike; extraction of a Const-known one goes
through its template (ASSUMPTIONS 133), the hint, a held one through
its runtime unwrap. A peek unwrap adds an operation to the record, a
`peek` template key, a mode on the match node, and makes a held
Matchable's runtime value a record of unwraps; the held path's cost is
an accepted edge case.

## U13. Erasure is conservative, in two tiers

§23's invariant becomes two claims, each that the transformed program
compiles and runs identically, both intended and unverified as §23 is:

- **Tier 1** collapses `unique` to `many`: `peek` becomes a `many`
  match, a UniqueFn a `Fn`, an extern update allocates and its `at`
  return is an ordinary return, a placement invocation allocates, a
  write returns its cell unchanged, `(at)` marks are plain arguments,
  degradation is the identity, and the at-database is vacuous.
- **Tier 2** is §23 applied after tier 1, erased to many.

In both, a collapsed multiplicity is not deleted but kept as an inert
designator that no longer governs erasure or usage and must still
coincide under §18's unification: in `ValCtor` and `Fn` telescopes for
tier 1, and in those and in `Matchable` markers for tier 2 (a Matchable
records only `erased`/`many`, §17, and no constructor is unique). That
keeps every refutation and `open-absurd` the original program had.
Tier 2 presupposes tier 1: collapsing erasure alone would turn an
erased mention of a consumed unique into a second use.

## U14. The risky forms

- A `Coercible` from two variables in one at-class is minted only when
  both are live: with one consumed, its contents may have changed while
  its address has not, and a `coerce` through the proof would give a
  value whose `is` refutes branches its bits reach. Two live variables
  at one address are both many, whose contents no longer change.
- Pointer comparison of two slots yields `(Eq (Slot) a b)` with a
  proof, matched through the at-database (§U10), so `Refl` puts the two
  in one class and never forces an `is`.

## U15. Open

Questions, not proposals: the spelling of the degradation form, of the
allocation form, of the write form and its omission marker, of `(at)`
(after the argument) and of the full-at invocation; `def-unique` and
UniqueFn (its level, what it closes over, its type former in §5);
whether an `at` return may name a closed-over variable of a `def-fns`
function; the extern array API; `cstr-let`'s name; whether `Slot`
values may sit in fields and lists; the `Maybe`-shaped `at` return
through a returned type (the proposal's part 3); the shadowing sugar
(deferred by the proposal); §27's registry entries for the new forms;
KERNEL.md's interpreter-trust note against in-place mutation; and the
FFI on an extern UniqueCstr (not allowed for now).

## U16. `_` as a binder name

Promoted here from ASSUMPTIONS 2, the owner's decision: `_` as a binder
name mints an anonymous entry wherever a binder is expected, a `let`
binder, a telescope entry, a pattern field, and now §U5's extra pattern
binder; it is not special anywhere else, `_` in an argument (SUGAR.md
6) and as an annotation (SUGAR.md 2) being their own things.
