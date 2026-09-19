# Uniqueness: a supplement to DESIGN.md

Read after DESIGN.md. It records what the owner decided, in design
sessions over the owner's proposal for unique types, on top of the
language DESIGN.md describes; DESIGN.md itself is unchanged, and where
it says linear or unique types are punted (§6) this file is the
continuation. Section references with `§` are to DESIGN.md. A passage
marked *reading* is a session's inference from the decisions, not a
decision; §U17 lists what is not decided, as questions. Names are
tentative throughout, as CLAUDE.md rule 10 has them. The worked
example of §U13 is written against the rules as recorded, not
machine-checked, as §40 is.

## U0. What is new, in one place

Multiplicity: `unique` (§U1). Match modes: `unique`, `peek` (§U5).
Statements: `def-unique` (§U6), `cell-read` (§U10). Type formers:
`UniqueFn` (§U6), `Cell` (§U9). Expressions: `share` (§U3),
`cell-alloc`, `cell-write` (§U9), `coercible-share` (§U7), and, as a
later second change, `at-coercible` and `slot-eq` (§U15, names open).
Head position: a
UniqueFn head is a call using the head at unique or erased (§U6); a
Cell head is the placement invocation, with `(at)` before an
argument and the full-at `at` around it (§U9). Annotation: `at` on a return entry or
match annotation entry (§U8); an extra binder in every `unique` or
`peek` pattern, and in an `else` at `peek` (§U5). Built-in types: `Slot`
with `(SlotVacant)` and `(SlotHolds v)` (§U10), `Sharing` with `Unique`
and `Shared` (§U7). Elaboration state: an
at-database beside §18's fact table, partitioning entries by location
(§U8). Changed: `Coercible`
takes a multiplicity on each side (§U7); `Matchable` carries the
`newtype` and `extern` marks (§U9); `_` as a binder name (§U16); §23's
invariant is two tiers (§U14). Removed: `Newtype`, `newtype-of` (§U7).
Prelude: `Array`, `MaybeUninit` and their functions (§U13).

## U1. A third multiplicity, and a fourth match mode

A binder may be declared `unique` beside `erased` and `many` (§6, §20):
function parameters and return entries, constructor fields, `let`
binders, and a match's scrutinee. A `unique` binder is the only
reference to its value, which is what lets an operation on it run in
place; the guarantee is the binder's, not the type's, so there is no
unique type, no unique type or value constructor, and no phantom
analogue. `match`, `let-match` and `comptime-match` gain two modes,
`unique` and `peek` (§U5), and `cell-read` (§U10) has `many` and
`peek`; `peek` is a match mode only, never a binder's multiplicity.

## U2. Uses

Each binder is checked by the uses it has on each path through the
code, with no order among them. On one path a `unique` binder must
either have exactly one non-erased use, at unique, beside any erased
mentions, or have any number, zero included, of erased uses and of
degraded many uses (§U3) and none at unique. A unique use beside any other non-erased use of the same
binder is an error, whichever the elaborator meets first, and the order
in which such errors are reported is implementation-dependent. An
erased mention is never a use and is allowed anywhere, before or after
the binder is consumed (§20's erased positions): a proof or a type may
name a consumed value.

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
unique position, a return of a call whose entry is declared `unique`,
a `unique`-labelled field taken by a `unique` destructure (§U4), or an
extern function whose return entry is `unique` (§U12's `array-new`).
Nothing turns a `many` or erased value unique, except as §20 already
has it in an erased position or a phantom branch, where nothing runs.

Degradation from `unique` to `many` is explicit: a `unique` binder in a
`many` position is an error unless written `(share x)`. The written
degradation is a many use of `x`, after which `x` is usable at many,
as `(share x)` every time, and never again at unique. Its result
`is x`, as a `coerce`'s result `is` the value its proof names (§38),
so a binder of it forwards `x`'s type and facts, and it is `at x`
(§U8).

## U4. Fields

A field is labelled `erased`, `many` or `unique`. A destructure, here
and below, is a `match`, `let-match` or `comptime-match` on a value,
binding its constructor's fields; a `cell-read` (§U10) is not one,
reading a cell's slots and binding no field. What a destructure hands
out for a field, by the scrutinee's mode:

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
a use of `x` at unique, and gives the value back as a new binder: each
branch binds a fresh `unique` binder that `is x` and is `at x` (§U8),
the scrutinee itself staying consumed, so the
discipline stays order-free (a peek after the binder is consumed is the
usual conflict) and nothing restores a consumed binder in place.

Both modes add one binder to every pattern, after the fields, mandatory
and `_` when unwanted (§U16): at `unique` it names the cell the
constructor occupied, a Cell at `x` whose slots hold the fields
just bound (§U9); at `peek` it names the scrutinee given back. A branch
gets that binder out of the match by returning it into an entry of the
match's annotation marked `at x` (§U8). At `peek` the `else` branch
binds it too, `(else x2 body)`, the value being the same whichever
constructor the else stands for; this is the first `else` that binds
anything. At `unique` an `else` binds nothing, the cell's constructor
being unknown, and the cell the scrutinee occupied is left to GC.

`let-match` takes the same modes and the same extra binder, binding
outward as before (§16). `comptime-match` at `unique` is a destructure
like any other and does not degrade a unique Const, but merely consumes
it at unique, binding its fields Const at their labels; the
elaborator's other reads of a Const (a special form or macro at the
head, a Matchable read, §U6) are many uses. Readability requirements for a dispatching
match are as in §19.

*Reading.* On a source type `peek` is a `unique` destructure followed by
a full-at reinvocation of the same constructor at the scrutinee (§U9),
so it does what a `many` match does, read the tag and the many-labelled
fields, and nothing more. On an extern type the FFI's peek unwrap runs
in place of those reads, and how it produces the fields, a view or a
copy, is the FFI author's choice under §U12's constraint; for the array
of §U13 it yields the discriminant alone.

## U6. Closures, `def-unique`, and the top level

A function defined by `def-fns` is a closure over its scope and may
mention a `unique` binder of that scope only erased or degraded, the
`(share x)` written inline in the body or earlier.

`def-unique` defines one function, not a block, whose type is built by
a new former, `(UniqueFn L params -> returns)`, and whose body may
close over `unique` binders as unique: each such binder the body uses
at unique is consumed by the definition itself, where the `def-unique`
is elaborated and not at each call, once modulo match branches as §U2
has it. The defined function binder is born unique; calling the
function is a use of that binder at unique, or erased, so a shared
UniqueFn is callable only erased and `share` on one leaves a dead
value; a UniqueFn-typed head is applicable in §4's tier 1 as an
`Fn`-typed one is, the one difference being that the call uses the
head at unique. Its level is
written as on a `def-fns` and may be shared with ordinary functions;
its parameters may be marked `subterm` and its body may make
same-level calls under `subterm` proofs; it may be marked `erased` or
`absurd`; its own name is in scope in its body as an erased entry, so
a self call is refused as any call through an erased head is and
recursion goes through a `def-fns` function taking the values as
parameters; its body supports `tail` and `delegate`, and `coercible-of`
fetches a delegate's proof as for a `def-fns` function.

*Reading.* The former is what a `unique` binder of `Fn` type cannot
express: after `share` a many `Fn` binder could be called repeatedly,
running the captured uniques again; a UniqueFn held at many cannot.

A top-level binder, and so a Const (§34), may be `unique` under the same
rules, run-position statements being sequential. Where the elaborator
must read a Const as a value, a special form or macro at a head (§4) or
a Matchable a match reads, that read is a many use, so a unique Const
there is an error until it is written `(share x)`, as anywhere else;
`comptime-match` is not such a read (§U5).

## U7. `Coercible` with multiplicities

`Coercible` (§38) gains a side on each end, `Coercible m_a A a m_b B
b`, each a value of a new built-in enum in the manner of `Special`,
an ordinary ADT with a Matchable and nothing special about it:

```scheme
(def-adts $ Sharing : -> Type
  enum
  (many Unique : -> (Sharing))
  (many Shared : -> (Sharing)))
```

There is no erased side: a `coerce` is never cashed erased and its
proof is always erased, so a side describes a non-erased use. The
target side is fixed at the minting form, by the expected type where
the position names one and by the rule below otherwise, and the source
side of each field is the multiplicity a constructor application at
the target side would use that argument at, the meet of the target side
and the field's label (§U4's construction table). So `coercible-wrap` over
a many-labelled field yields `(Shared)` to `(Shared)` or `(Shared)` to
`(Unique)`, over a unique-labelled field `(Shared)` to `(Shared)` or
`(Unique)` to `(Unique)`; `coercible-ctor`
applies the meet per field on each side; `coercible-refl` is uniform;
`coercible-of` takes its sides from the two functions themselves,
`(Shared)` for a `def-fns` function and `(Unique)` for a `def-unique`
one (§U6), so a UniqueFn delegating to a plain function is `(Unique)`
to `(Shared)`.
Where nothing in a form fixes its sides, `coercible-ctor` and
`coercible-refl` mint `(Unique)` on both. `coercible-sym` is unconditional,
every mintable shape being uniform or the harmless one: the sym of
`(Shared)` `x` to `(Unique)` `(MkBox x)` consumes a unique wrapper and
gives its many-labelled field back shared; `coercible-trans` requires
the middle multiplicities equal; and a new form, `coercible-share`,
weakens any proof to `(Shared)` on both sides (the proposal's 1j).
`(coerce a p)` in a position of multiplicity `m` uses `a` at `m_a`,
consuming it when that is `(Unique)`, and yields its result at `m_b`:
an error where `m_b` is `(Shared)` and `m` is `unique`, and where
`m_b` is `(Unique)` and `m` is `many` the result is a unique value in
a many position, which §U3 has needing a written `share`.

`coercible-wrap` reads a newtype's mark off the opened Matchable
(§U9); the `Newtype` object, its former and `newtype-of` are gone. A
newtype's shape (§38) reads "exactly one non-erased field".

*Reading.* Without the sides, a proof composed through two newtypes of
one field type, one labelled `many` and one `unique`, would carry a
many value into a unique-labelled wrapper; the sides refuse it at
`coercible-trans`.

## U8. `at`

A return entry of a function's telescope, or an entry of a match's
annotation, may add `at v`: the value returned is at the same location
as `v`, a non-erased argument or a non-erased closed-over variable, for
`def-fns` and `def-unique` alike, the only restriction being §18's,
that no fact outlasts an entry it mentions, which keeps a function
whose type names a closed-over variable inside that variable's scope:
a factory cannot return it, its return telescope being unable to name
the variable.
The promise is verified where the function or branch returns; a
phantom branch under a non-erased scrutinee, an absurd branch, a
refuted branch and an `erased` or `absurd` function are exempt. An
`at` return may be `many`, and may combine with `is`: a read of a
unique array is `(unique a is r at a)`.

Beside the fact table the elaborator keeps the **at-database**, a
partition of scope entries into classes of one location. Its writers,
and nothing else: a destructure at `unique` by `match`, `let-match` or
`comptime-match` (the minted Cell with the scrutinee), a
placement invocation (the new value with its Cell), `coerce` and
`share` (the result with the source, the same word), a forwarding `let`
(§9), a call's `at` return (the binder bound to it with the caller's
argument the promise names), a match's `at` result (the entry with the
variable its annotation names), and a forcing
unification (§18: entering a branch, a `let-match`, a `comptime-match`,
an open) wherever it meets two `SlotHolds` terms or two `at`
annotations in the types it unifies, which merges the classes of their
variables (§U10, the proposal's 3g) as matching `Refl` on an `(Eq
(Slot) (SlotHolds a) (SlotHolds b))` does (§U15). Such a merge puts `a`
and `b` in one at-class and nothing more: no `is` rule between them
reaches the fact table. An `at v` in a telescope entry is part of the
type and is compared through the at-database like a `SlotHolds`, not
through `is`. A forced rule between two ordinary atoms, `x is y`, says
nothing about location and merges nothing, and neither does canonical
equality: two separately built cells with equal contents are
`is`-equal and are two blocks. A non-forcing check, an argument against
a parameter, only asks whether the classes already coincide, an
abstract `(Slot)` parameter being instantiated instead. It is read by
binder, before canonicalization, and a membership ends with the scope
that minted it. A class may hold consumed entries; address equality
does not change when contents do.

An `at` return is absent from a call's physical values in every
implementation, as an erased return is; a `let` binds it as any
return, and the elaborator supplies its word from the caller's own
binder for the argument the promise names, which the caller still
holds physically whether or not the call consumed it. The `tail` and `delegate` checks (§9) read the
post-erasure code with `at` returns dropped from a call's results, as
they read coerces as renamings, so a call whose only non-erased results
are `at` returns is a tail call from a function returning none, and
vice versa, the caller's own promise being verified as always by what
follows the call, which the check requires to be erased.

*Reading, an idiom.* A function that may fail and still promises its
result at its argument returns an erased `Type T`, a `(unique T val at
a)`, and an erased constraint relating `T` to the outcome; the caller
matches the constraint and in each branch `T` is forced to the concrete
type, the intended one on success and the argument's own on failure,
the one word being at `a` either way (the pattern of
`tests/type_result_is.sl`). §38's newtype shape stays as it is.

## U9. Placement: Cell and the invocation

For a type that is neither `newtype` nor `extern`, a value constructor
`C` has a cell type `(Cell C s1 ... sn)`, a type former (§5) with
one `Slot` (§U10) per non-erased field of `C`. The newtype
representation (§38) is mandatory for a type marked `newtype` and
forbidden for one that is not, whatever its shape: an unmarked type of
newtype shape is a block, so §38's leeway is withdrawn. A constructor
with no non-erased field has an empty cell. The `newtype` and `extern`
marks live in the type's `Matchable`, beside its `enum`/`union` tag
(§17), so eligibility is read off the opened Matchable listing the
constructor (§19), which unifying two opened Matchables forces equal
too.

**Obtaining a cell.** `(cell-alloc C)` is an expression yielding a
fresh cell at unique with every slot `(SlotVacant)`; `(cell-alloc C i1
... in)` lists every non-erased field as a write does, a `(Slot)`
expression at many or `_` for a slot left `(SlotVacant)`, no partial
list.
A `unique` `match`, `let-match` or `comptime-match` on a value (§U5)
yields, through its extra pattern binder, the cell the constructor
occupied, at the scrutinee, each slot `(SlotHolds f)` for the field's
binder `f`.

**Writing.** `(cell-write u i1 ... in)` is an expression taking the
cell at `unique` and yielding the same cell under a new type, at `u`,
one item per non-erased field, a `(Slot)` expression at many or `_` to
leave the slot alone, the new type's index for each written slot being
that item's value, `(SlotHolds v)` for a `(SlotHolds v)` item. A write is a
physical store into memory the cell's eventual invocation will
re-mint; it does no usage accounting, whatever its slot refers to, the
Cell invocation below being the semantic mint.

**Invocation.** A Cell-typed head is applicable in §4's tier 1,
beside the three types §4 lists: `(u a1 ... an)` is a constructor
application that mints
`(C a1 ... an)` at `u`, using each argument at the field's multiplicity
as `(C a1 ... an)` would, erased arguments included, which have no
slot and are written as in any constructor application, and consuming
`u` at `unique` in a `many` position as in a `unique` one, so a `many`
value may be built this way; in an erased position nothing is used, as
§20 has it for every application. The value's type is `C`'s return type
instantiated, as for the plain application. An `(at)` immediately
before an argument, as `(subterm p)` sits before its argument (§32),
asserts that the slot already holds that argument, the argument's
variable being in the slot's `SlotHolds` class, and the store is
skipped; a hard error otherwise, as for `tail`. `(at (u a1 ... an))`,
wrapping the invocation as `tail` wraps a call, asserts the same of
every non-erased argument, performs nothing, and is treated as erased
by the `tail` and `delegate` checks, as a `coerce` is, so it may follow
a tail call. What is stripped is the stores only: an invocation with
every store skipped, or the full-at form, still uses each argument at
its field's multiplicity, consuming a unique one, still consumes `u`,
and still mints its value at `u` in the at-database and its `is` in
the fact table, exactly as one that stores does.

*Reading.* Under these rules a slot can never end up referencing a cell
owned elsewhere in a minted value: the invocation supplies each field
at its multiplicity, so a consumed unique cannot be named there.

## U10. `Slot` and `cell-read`

`Slot` is a nullary type with two value constructors, `SlotVacant` and
`SlotHolds`, a slot's content being `(SlotVacant)` or `(SlotHolds v)`
with `v` a fact-table variable (§3), never a telescope binder; a signature that speaks of a slot abstracts over it as an
erased `(Slot)` parameter, `(erased (Slot) s) (unique (Cell Pair2
s s) u)` saying its two slots hold one thing. A `SlotHolds` term is
handled by the at-database and not the fact table: its argument is not
rewritten by `is` rules, canonicalizing it takes the argument to its
at-class, two `SlotHolds` are equal exactly when their arguments share a
class, and a forcing unification merges the classes. `Slot` is not
matchable and has no Matchable to open. At runtime a slot's value is
the word the slot holds, a pointer or an immediate. `(SlotHolds v)`
is an ordinary expression producing a `(Slot)`, usually at many, the
position deciding as for any constructor application, and it mentions
`v` erased: it is not a use of `v`, so `v` may be a unique binder that
is still live, which stays live, or one already consumed, and either
way the result is a many slot holding `v`'s word (the proposal's 4f
and 4g). What `v` must be is declared non-erased, so that the word
exists; since every `SlotHolds` in a cell's type comes from such an
expression or from a destructure's field binders, none names an erased
variable. A slot value is inert and may sit in a
field or a list like any other value.

`cell-read` reads a cell's words out, a statement binding outward:
`(cell-read many u (C s1 ... sn))` with `u` at many, never degrading it
(degradation being explicit, `u` must already be many), and
`(cell-read peek u (C s1 ... sn u2))` with `u` at unique, `u2` the cell
given back as §U5's peek does. The `si` are fresh `many` binders of
type `(Slot)`; one forced unification of `(Cell C s1 ... sn)`
against `u`'s type mints their `is` rules, as entering a branch unifies
a scrutinee's type (§18). It decides nothing about a slot: an `si` is
whatever `u`'s type said, a `(SlotHolds v)`, a `(SlotVacant)`, or an abstract
slot. What the words are for is a write into another cell and §U15's
comparison.

## U11. Worked example: tail call modulo cons

`append` copying `xs` onto `ys` in destination-passing style, over the
prelude's `List` of §31, whose fields are both `many`:

```scheme
(def-adts
  (List : (Type A) -> Type
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) tail) ->
       (List A))))
```

The helper takes a vacant cell and the head that belongs in it, and
promises its result at the cell:

```scheme
(def-fns _ $ many append-into : (erased Type A)
    (unique (Cell Cons (SlotVacant) (SlotVacant)) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell)
  (match many xs _
    ((Nil _) (cell _ h ys))
    ((Cons _ hd tl)
      (let (unique next) (cell-alloc Cons))
      (let (unique cell2) (cell-write cell (Cons (SlotHolds h) (SlotHolds next))))
      (let (many r2) (tail (append-into _ next hd tl ys)))
      (at (cell2 _ h r2)))))

(def-fns _ $ many append : (erased Type A) (many (List A) xs) (many (List A) ys) ->
    (many (List A) r)
  (match many xs _
    ((Nil _) ys)
    ((Cons _ hd tl)
      (let (unique cell) (cell-alloc Cons))
      (append-into _ cell hd tl ys))))
```

- In the `Nil` branch the invocation mints `(Cons A h ys)` at `cell`,
  `h` and `ys` at many into the many-labelled fields (§U4), the cell
  consumed and the value many, as an invocation in a many position
  builds (§U9); the result is at `cell`, the promise.
- In the `Cons` branch the write stores `h` and the pointer to the
  fresh `next` into `cell`, two stores, mentioning both erased, so
  `next` is still live for the call; the call consumes `next` and
  returns `r2 at next`, physically nothing.
- The call is a tail call: with `at` returns dropped the callee returns
  nothing and so does this function, and what follows the call is
  erased, the invocation being full-at since `h` is in the first
  slot's class and `r2` is at `next`, which the second slot holds. Its
  result is at `cell2`, at `cell`. Leaving `h` to the invocation
  instead of the write would put a store after the call and the claim
  would fail.
- Each of `cell`, `cell2` and `next` is used once at unique; `h`, `r2`
  and the result are many, the tail being labelled `many`, which is
  why the helper returns `many` and needs no `share`. Per element, one
  allocation and two stores, in constant stack. Perhaps `List` should
  instead be defined with `unique` on both `head` and `tail` (the
  owner's remark, undecided): a many construction would still request
  them at many, and a unique one would own its whole spine.

## U12. Extern types and functions

A `unique` value of an extern type is the FFI's to mutate in place. Two
binding constraints on the FFI author, beside §41's: the FFI supplies a
peek unwrap beside its match unwrap, returning the discriminant and the
many-labelled fields and sharing nothing mutable (today's String view
shares its buffer, which a mutable type may not); and an `at` return
promised by an extern's signature is honoured physically, the model's
body being checked against the promise like any body, so such a model
is written with §U9's placement over its own cells. (*Reading*: §41's
shape check then compares the non-erased arities of the model's
constructors, not the many ones.) Part 1 of the proposal is useful
before parts 2 to 4 exist:
an update `(unique (Array A n) a) ... -> (unique (Array A n) r)` is
O(1) and returns one word the caller already holds. A `Cell` for an
extern type's constructor, and so `cell-alloc`, `cell-write`,
`cell-read` and the invocation on one, is TBD and for now not allowed:
an extern's in-place operations are its own functions, §U13's
`array-swap` and kin.

*Reading.* In the prototype's interpreter an extern type's ADT record
carries the FFI's construct and destruct, and a match reads them
through one dispatch function whether its Matchable was Const-known,
the shape settled at elaboration, or held, read at runtime. In
extraction a match on a Const-known extern Matchable is emitted inline
through the type's template, the hint of ASSUMPTIONS 133, and a match
on a held one through the runtime unwrap. A peek unwrap adds an operation to the record, a
`peek` template key, a mode on the match node, and makes a held
Matchable's runtime value a record of two unwraps, a *match unwrap*
serving `many` and `unique` alike, which hand out the same fields at
different multiplicities, and a *peek unwrap* serving `peek`; the held
path's cost is an accepted edge case.

## U13. Worked example: arrays

The owner's array API, length-indexed, elements owned, uninitialised
slots through a union newtype in the manner of Rust's `MaybeUninit`,
and one extern primitive per element operation with the rest plain
source over it. `_` is SUGAR.md 6's.

```scheme
(def-adts $ Array : (Type A) ((Nat) n) -> Type
  enum extern
  (many ANil : (erased Type A) -> (Array A (Zero)))
  (many ACons : (erased Type A) (erased (Nat) n)
                (unique A head) (unique (Array A n) tail) ->
     (Array A (Succ n))))

(def-adts $ MaybeUninit : (Type A) -> Type
  union newtype
  (many Uninit : (erased Type A) -> (MaybeUninit A))
  (many Init : (erased Type A) (unique A value) -> (MaybeUninit A)))
```

A `(MaybeUninit A)` is one word, `A`'s own under `Init` and an
unspecified one under `Uninit`, so an `(Array (MaybeUninit A) n)` is
the memory of the `(Array A n)` it becomes. Reading an `Init` out is a
`unique` match whose `Uninit` branch must be refuted, by a fact or by
proof, §12's one-real-branch rule making that Rust's `assume_init`
with evidence in place of `unsafe`. Under `peek` both of `ACons`'s
fields are erased, so the FFI's peek unwrap yields the discriminant
alone.

The relations, every field erased:

```scheme
(def-adts
  (AllUninit : (Type A) ((Nat) n) ((Array (MaybeUninit A) n) a) -> Type
    enum
    (many AUNil : (erased Type A) -> (AllUninit A (Zero) (ANil (MaybeUninit A))))
    (many AUCons : (erased Type A) (erased (Nat) n) (erased (Array (MaybeUninit A) n) tl)
                   (erased (AllUninit A n tl) p) ->
       (AllUninit A (Succ n) (ACons (MaybeUninit A) n (Uninit A) tl))))
  (AllInit : (Type A) ((Nat) n) ((Array (MaybeUninit A) n) a) -> Type
    enum
    (many AINil : (erased Type A) -> (AllInit A (Zero) (ANil (MaybeUninit A))))
    (many AICons : (erased Type A) (erased (Nat) n) (erased A x)
                   (erased (Array (MaybeUninit A) n) tl) (erased (AllInit A n tl) p) ->
       (AllInit A (Succ n) (ACons (MaybeUninit A) n (Init A x) tl))))
  (ANth : (Type A) ((Nat) n) ((Array A n) a) ((Nat) i) (A x) -> Type
    enum
    (many NthZ : (erased Type A) (erased (Nat) n) (erased A x) (erased (Array A n) tl) ->
       (ANth A (Succ n) (ACons A n x tl) (Zero) x))
    (many NthS : (erased Type A) (erased (Nat) n) (erased A h) (erased (Array A n) tl)
                 (erased (Nat) i) (erased A x) (erased (ANth A n tl i x) p) ->
       (ANth A (Succ n) (ACons A n h tl) (Succ i) x)))
  (ASet : (Type A) ((Nat) n) ((Array A n) a) ((Nat) i) (A y) ((Array A n) r) -> Type
    enum
    (many SetZ : (erased Type A) (erased (Nat) n) (erased A h) (erased A y) (erased (Array A n) tl) ->
       (ASet A (Succ n) (ACons A n h tl) (Zero) y (ACons A n y tl)))
    (many SetS : (erased Type A) (erased (Nat) n) (erased A h) (erased (Array A n) tl)
                 (erased (Nat) i) (erased A y) (erased (Array A n) tl2)
                 (erased (ASet A n tl i y tl2) p) ->
       (ASet A (Succ n) (ACons A n h tl) (Succ i) y (ACons A n h tl2)))))
```

`ANth` carries the bound, so no `Lt` accompanies an index. The
functions, each `extern` with a source model, the FFI's implementation
shedding the argument its model does not use:

```scheme
(def-fns _ $ many extern array-new : (erased Type A) (subterm many (Nat) n) ->
    (unique (Array (MaybeUninit A) n) a) (erased (AllUninit A n a) p)
  (match many n _
    ((Zero) (values (ANil _) (AUNil _)))
    ((Succ n1)
      (let (unique tl) (erased q) (array-new _ n1))
      (values (ACons _ _ (Uninit _) tl) (AUCons _ _ _ q)))))

(def-fns _ $ many extern array-swap : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (subterm many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) ->
    (unique m is old) (unique (Array A n) r at a)
    (erased (ASet A n a i x r) p)
  (match unique a _
    (absurd (ANil _ _) (match erased nth (((False) f))))
    ((ACons _ _ hd tl u)
      (match many i _
        ((Zero)
          (match erased nth _
            ((NthZ _ _ _ _)
              (values hd (u _ _ x (at) tl) (SetZ _ _ _ _ _)))
            (absurd NthS)))
        ((Succ i1)
          (match erased nth _
            (absurd NthZ)
            ((NthS _ _ _ _ _ _ q)
              (let (unique old) (unique tl3) (erased p1) (tail (array-swap _ _ tl i1 x _ q)))
              (values old (at (u _ _ hd tl3)) (SetS _ _ _ _ _ _ _ p1)))))))))

(def-fns _ $ many extern array-pluck : (erased Type A) (erased (Nat) n)
    (unique (Array (MaybeUninit A) n) a) (many (Nat) i)
    (erased (MaybeUninit A) m) (erased (ANth (MaybeUninit A) n a i m) nth) ->
    (unique m is v) (unique (Array (MaybeUninit A) n) r at a)
    (erased (ASet (MaybeUninit A) n a i (Uninit A) r) p)
  (tail (array-swap _ _ a i (Uninit _) _ nth)))

(def-fns _ $ many extern array-place : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) ->
    (unique (Array A n) r at a) (erased (ASet A n a i x r) p)
  (let (unique old) (unique r) (erased p) (array-swap _ _ a i x _ nth))
  (values r p))
```

In `array-swap`'s `ANil` branch the bound refutes itself, `nth` having
no constructor at length `(Zero)`; in its `NthZ` branch the forced
facts make `hd` canonically `m`, so it is returned as `old` with no
coerce, the head slot takes `x`, one store, and the tail is skipped; in
its `NthS` branch the recursion returns `tl3 at tl`, the reinvocation
is full-at and erased, and with `old` the only physical result on
either side the recursive call is a valid `tail`. `array-pluck` is a
`tail` and not a `delegate`, `(Uninit _)` being an argument it does not
take; its FFI reads and stores nothing, the old word staying under a
slot typed `Uninit`, which nothing can read. `array-place` drops `old`,
as at-most-one-use allows, so it is a plain call. The FFI's `array-new`
is a block of `n` words, the model's `ACons` view its first word and a
slice of the rest sharing the block.

The conversion to a plain array is an erased witness in §40's shape,
and the `coerce` is written where it is used, a wrapper function
extracting to a call where the inline `coerce` extracts to nothing:

```scheme
(def-fns _ $ erased init-witness : (erased Type A) (erased (Nat) n)
    (erased (Array (MaybeUninit A) n) a) (subterm erased (AllInit A n a) all) ->
    (erased (Array A n) b)
    (erased (Coercible (Unique) (Array (MaybeUninit A) n) a (Unique) (Array A n) b) c)
  (match erased all _
    ((AINil _)
      (values (ANil _) (coercible-ctor ANil (MaybeUninit A) A)))
    ((AICons _ n1 x tl q)
      (let (erased b1) (erased c1) (init-witness _ _ tl q))
      (values (ACons _ _ x b1)
              (coercible-ctor ACons (MaybeUninit A) A n1 n1
                 (coercible-sym (coercible-wrap Init x))
                 c1)))))

(let (erased b0) (erased c) (init-witness _ _ a all))
(let (unique arr) (coerce a c))
```

`arr` is at `a` by the `coerce` rule, and nothing runs.

## U14. Erasure is conservative, in two tiers

§23's invariant becomes two claims, each that the transformed program
compiles and runs identically, both intended and unverified as §23 is:

- **Tier 1** collapses `unique` to `many`: `peek` becomes a `many`
  match, a UniqueFn a `Fn`, an extern update allocates and its `at`
  return is an ordinary return, a placement invocation allocates, a
  write returns its cell unchanged, `(at)` marks are plain arguments,
  `at` annotations are dropped from telescopes, `share` is the
  identity, and the at-database is vacuous.
- **Tier 2** is §23 applied after tier 1, erased to many.

In both, a collapsed multiplicity is not deleted but kept as an inert
designator that no longer governs erasure or usage and must still
coincide under §18's unification: in `ValCtor` and `Fn` telescopes for
tier 1, and in those and in `Matchable` markers for tier 2 (a Matchable
records only `erased`/`many`, §17, and no constructor is unique). That
keeps every refutation and `open-absurd` the original program had.
Tier 2 presupposes tier 1: collapsing erasure alone would turn an
erased mention of a consumed unique into a second use.

Open (§U17): where §U15's two forms stand under tier 1. Keeping the
at-database as inert designators too would let `at-coercible` still
mint, and its `coerce` stays sound since a copy has its original's
contents; `slot-eq` observes addresses at runtime, and once every
invocation allocates, two slots that held one cell may hold two.

## U15. Two further forms, proposed as a later second change

The proposal's part 5 adds two special forms, both new, names open,
and proposed as a second change after the rest of this file lands;
the restrictions are the owner's.

**A `Coercible` from the at-database.** `(at-coercible x y)`, say,
mints `(Coercible (Shared) X x (Shared) Y y)` for two variables `x` and
`y` in
one at-class. It is minted only when both are live, neither consumed:
with one consumed,
its contents may have changed while its address has not, and a `coerce`
through the proof would give a value whose `is` refutes branches its
bits reach. Two live variables at one address are both many, whose
contents no longer change, so the proof is sound there.

**Comparing two slots.** `(slot-eq a b)`, say, compares the words of
two `(Slot)` values at many, at runtime, and answers with evidence in
the equal case, in the shape of the prelude's `Dec`:

```scheme
(def-adts
  (SlotEq : ((Slot) a) ((Slot) b) -> Type
    enum
    (many SlotSame : (erased (Slot) a) (erased (Slot) b) (erased (Eq (Slot) a b) e) -> (SlotEq a b))
    (many SlotDiffer : (erased (Slot) a) (erased (Slot) b) -> (SlotEq a b))))
```

Matching `Refl` on the `Eq` unifies two `SlotHolds` through the
at-database (§U10), putting their variables in one class and forcing
no `is`; that is what makes the equal case usable, an `(at)` or a
full-at invocation then holding where it did not before. The unequal
case carries no evidence for now; whether it should carry a refutation,
a function to `(False)` at some fixed level, is open with the names.

## U16. `_` as a binder name

Promoted here from ASSUMPTIONS 2, the owner's decision: `_` as a binder
name mints an anonymous entry wherever a binder is expected, a `let`
binder, a telescope entry, a pattern field, and now §U5's extra pattern
binder; it is not special anywhere else, `_` in an argument (SUGAR.md
6), as an annotation (SUGAR.md 2), and as a `cell-write` or
`cell-alloc` item (§U9) being their own things.

## U17. Registry additions and open questions

Additions to §27's registry. Statements: `def-unique`, `cell-read`.
Type formers: `UniqueFn`, `Cell`. Other expressions: `share`,
`cell-alloc`, `cell-write`, the full-at wrapper `at`, `coercible-share`,
and §U15's `at-coercible` and `slot-eq`, names open; a UniqueFn or
Cell head is an applicable type in §4's tier 1, not a special
form. Annotation tokens:
`unique`, `peek`, and `at` before an argument or after a telescope
entry. Built-in types: `Slot` with `SlotVacant` and `SlotHolds`, and
`Sharing` with `Unique` and `Shared`, beside §17's opaque objects
though not opaque; `Coercible` changed. Removed:
`Newtype`, `newtype-of` and §27's item 9a; `Matchable`'s type gains the
`newtype` and `extern` marks.

Open, as questions: the names of §U15's two forms and whether `slot-eq`'s
unequal case carries a refutation; whether those forms fall under
tier 1 (§U14); whether `cell-read` should be an expression returning
its slots as `is` entries, `(cell-read peek u)` bound by a `let`,
rather than a statement, nothing it mints needing to bind outward as
`let-match`'s facts do; a `Cell` for an extern type's constructor
(TBD, for now not allowed); the shadowing sugar the
proposal defers, same-name rebinding, `(let (unique x) (f x))`, being
the idiom until then.
