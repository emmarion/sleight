# The language

This file is the specification of the language: its syntax, scope and
fact table, types, multiplicities, termination, data types and
matching, expressions and compile time, coercion, slots and cells, the
prelude and the FFI, the surface sugar, the special-form registry, and
worked examples. OPEN.md lists the open questions; README.md describes
the implementations and their command lines; EXAMPLES.md indexes the
tests. Sections are cited by number from the code and from the other
files.

- Syntax: §1 to §4.
- The scope environment and the fact table: §5 to §8.
- Types: §9 to §12.
- Multiplicities and erasure: §13 to §16.
- Termination: §17 to §20.
- Data types and matching: §21 to §25.
- Expressions, statements and compile time: §26 to §32.
- Coercion: §33, §34.
- Slots, `at` and cells: §35 to §41.
- The prelude, the FFI and literals: §42 to §45.
- Sugar: §46 to §53.
- The special-form registry: §54.
- Worked examples: §55 to §61.

## 1. Syntax

S-expressions. A file is a sequence of statements, optionally followed
by one expression (§27). `;` starts a comment that runs to the end of
the line; `;!` starts a pragma (§4). An atom is any run of characters
other than whitespace, parentheses and `;`; a token beginning with `"`
is a string literal, and digit-only atoms and `#\c` atoms are numeral
and character literals (§45).

`_` as a binder name mints an anonymous entry wherever a binder is
written: a `let` binder, a telescope entry, a pattern field, a cell
binder, a `def-lvl`, or the name a `def-fns`, `def-unique` or
`def-adts` defines. Its other meanings are separate forms: an inferred
argument or type (§50), an annotation (§47), a `def-fns`
level (§46), a cell item (§37). No other name may begin
with `_`; such spellings are reserved for the compilers' messages.

The language's syntax is ASCII. The multiplicities are the words
`erased`, `many` and `unique`, not Idris's `0` and `ω`.

## 2. `$`

`$` parses exactly like `(`, opening a new list form, except that it
does not consume the `)` that ends it: it reads items until its
enclosing form's terminator and leaves that terminator for the
enclosing form. With no enclosing form the missing `)` is an error.
Only a bare `$` token is special; `foo$bar` is an ordinary atom.

A telescope written in a form that also carries something else is
bracketed: a `let`'s binders, and a `def-fns`, `def-unique` or
`def-adts` signature up to and including its returns. What follows the
bracket is the body. A value constructor has no body, so its clause is
that bracket alone.

## 3. Telescope entries: expression before name

A typed telescope entry is `([subterm] mult Type name [at v])`, type
before name: an entry may only depend on the entries before it, so
everything a type can reference sits to its left and the name, which
nothing can yet reference, comes last. A `TyCtor` entry omits the
multiplicity (§11). An `is` entry is `(mult expr is name [at v])` for
the same reason. `at v` is §36.

`$` cannot end such an entry when a name would follow, since `$` reads
to the enclosing form's terminator; plain parentheses are used there.

`let` sees backwards only: a binding never sees itself or anything
declared after it. All recursion, mutual recursion included, goes
through `def-fns` and `def-adts`.

Examples. `reify-add`'s type:

```scheme
(Fn L (many (Nat) a b) (erased (Nat) c) (erased (Add a b c) p) ->
   (many c is d))
```

`divmod`'s type:

```scheme
(Fn L (subterm many (Nat) n) (many (Nat) d) -> (many (Nat) q) (many (Nat) r))
```

A length-indexed vector's type constructor, with no multiplicities:

```scheme
(TyCtor (Type A) ((Nat) n) -> Type)
```

A value constructor whose runtime field is pinned by `is`: `a` and `b`
are erased indices, and `lst` is stored at runtime and is
definitionally the two-element list built from them, so it serves as
data and in type position at once:

```scheme
(ValCtor (erased (Nat) a) (erased (Nat) b)
   (many (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat)) is lst) -> (Two a b))
```

## 4. User-defined warnings

A pragma line `;! warn NAME message` names a type constructor or a
value constructor in scope, read through its aliases, and a message.
Afterwards every non-erased application of that constructor, or every
non-erased `match`, `let-match` or `comptime-match` on that type,
warns with the message and a note pointing at the pragma, except
inside an `extern` function's body. A `;! warn` is written between
top-level forms; a second one for the same name, a
name not in scope or naming anything else, or a missing message is an
error.

`;! suppress warn NAME` silences such warnings for `NAME` until the
matching `;! restore warn NAME`, or to the end of the file; the pair
may sit at any nesting depth, and any text after the name is ignored. A
region that silences nothing warns. A second `suppress` for a name
already open, or a `restore` with none open, is an error. Any other
`;!` word is an error.

Warnings go to standard error and do not stop elaboration;
`--warnings-as-errors` fails a run that warns, a silenced warning not
counting (README.md).

## 5. Scope environment

The scope environment is a list of entries, with shadowing. An entry
carries:

- a **name**, optional: anonymous entries exist;
- a **state**, `Const` or `Dyn` (§28, §29);
- a **stored value**, present only in state `Const`; for an erased
  entry it is a token asserting that the value exists, not data;
- a **multiplicity** (§13), declared at the binder or fixed by the
  entry's kind (§14);
- a **level-mint marker**, set on an entry introduced by `def-lvl`
  (§18);
- an **introduction order**, which orders `Predates` (§18) and decides
  what a `delegate` may name (§19);
- an **automatic slot** (§35).

An entry's **type** and its **`is` rule** (§12) live in the fact table
(§7), not on the entry. Each is a tree whose leaves reference entries
(§9); an `is` tree may reference its own entry. Both are
scope-relative: an entry's type may be refined inside a match branch
and revert when the branch ends.

Every type-constructor or value-constructor application has an entry
of its own, typically anonymous, whose `is` rule is that application.
So the fact table's reference graph is the whole structure of anything
in §9's grammar; there is no separate term structure beside it.

Elaboration also carries two pieces of ambient context: the **current
level**, the level of the function body being elaborated into, or a
marker for the file's top level, which sits above every level (§20);
and the **enclosing subterm arguments**, the entries bound by the
enclosing function's `subterm`-marked parameters, in declaration order
(§19).

## 6. Head dispatch

Macros and special forms are first-class values. Invoking one, as
against holding it, requires the head of the form to be constant-known
where the form stands: a name bound inside a function body or a match
branch is `Dyn`, a function is `Dyn` within the bodies of its own
`def-fns` block, and the binders of a statement in run position (§27)
are `Const` in the code after it (§29).

A list is elaborated by its head:

1. If the head's type is a type constructor, a value constructor, an
   `Fn`, a `UniqueFn` or a `Cell` (§32, §37), the list is an
   application. No constant-knownness is required: any of these is
   applied through a first-class value.
2. Otherwise, if the head is `Const`, non-erased and of type
   `(Special)` (§19), the form is the special form its stored value
   names. A head written `(share n)` with `n` such an entry dispatches
   the same way (§16). An erased `Const` holds only §5's token
   and has no value to dispatch on.
3. Otherwise the list is an error.

## 7. The fact table and forced unification

The scope environment (§5) and one rewrite database, the **fact
table**, are the sole sources of truth for checking. The table maps
entries to a type and an optional rewrite rule, atom to expression.
Types live in the table because entering a branch refines the
scrutinee's type as it refines its structure.

Facts are read canonically: a rule or type is canonicalized to a fixed
point against the rules in force when it is read. The table is written
by declaration sites (`is` declarations, signatures, telescopes, `let`
inference), by run-position statements running (§29), by
`comptime-match` verifications against a stored value, by opens (§8),
and by forced unifications on entering a branch (below). A
branch-forced rule lands even when it rewrites a `Const` entry: the
rule is justified by the branch running.

**A fact ends with the scope it was minted in.** A branch-forced rule
ends with its branch whatever entries it mentions: matching a `(Nat)`
against `Zero` forces `n is (Zero)`, which names no branch-local entry
and is still gone after the match. A fact mentions only entries in
scope where it is minted, so it never outlasts an entry it mentions.
Only run-position statements run at compile time (§27, §20), and their
match branches are gated as any other's, so one table suffices.
Compile-time effects in unreachable code still happen. A
`comptime-match`'s verified fact, recorded in run position,
holds afterwards, so a later match on the same `Const` finds the
contradicting branches refuted structurally.

Before an occurs check, and before recursing into either side of an
equation, both sides are canonicalized. Canonicalization never
consults a `Const` entry's stored value: it is driven by `is` facts
alone, uniformly over `Const` and `Dyn`.

**Forcing.** Entering a branch equates the scrutinee with the branch's
constructor applied to its fresh fields, and the scrutinee's type with
the type that application has. This is not a check: it adds `is` facts
wherever that is not already provably impossible, recursively through
matching non-atom arguments. A fresh atom, or an atom with no
conflicting fact, always unifies. When two atoms are unified the newer
becomes an alias of the older, and what the two must share is then
unified too: their signatures where both are type or value
constructors, and the opened `Matchable`s they head where both are type
constructors (§8). The forced facts hold while the branch is checked;
`match` keeps them inside the branch, `comptime-match` exports them
after verifying the constructor against the stored value, `let-match`
after refuting every other constructor (§27), and facts minted while
testing a constructor do not escape the test.

Forcing fails, refuting the branch, in exactly three ways:

1. an atom `x` equated with an expression containing `x`, after
   resolving existing atom-to-atom aliases (`x = x` is a no-op);
2. two value constructors that one opened `Matchable` lists equated;
   or two atoms whose signatures cannot be unified; or two atoms
   equated whose opened objects would then name one thing and cannot
   be unified (§8's invariant). A declared name has no distinctness
   of its own: two type constructors of identical signature and no
   opened `Matchable` unify;
3. a variable equated with an expression mentioning a binder of the
   telescope under comparison: `k` against `x` when
   `(Fn L ((Nat) x) -> (k is y))` meets `(Fn L ((Nat) x) -> (x is y))`.
   A rule maps an atom to a closed expression, so no rule could make
   the two sides identical; the language has no eta rule.

## 8. `Matchable` and constructor disjointness

Constructors are first class (§24), so two constructor-valued
variables are not known to be distinct from being syntactically
distinct. There is no third, indeterminate outcome when two
constructor-headed terms meet: forcing either succeeds, adding facts,
or contradicts by §7's rules. Two atoms conflict only when one opened
`Matchable` lists both, their signatures cannot unify, or the opened
objects that would then name one thing cannot; nothing is refuted on a
name's identity.

A `Matchable` does nothing by being in scope: nothing consults it until
it is **opened**. Two forms open one, each taking an expression of
`Matchable` type and reading it for its type, not its value:

- `(open-adt m e)`, a statement (§27): an anonymous `let` of `e` at
  the multiplicity `m`, checked as a `let` binder is (§19), then the
  open of that binder. The open asserts that the listed constructors
  are pairwise distinct after canonicalization and that the invariant
  below holds, minting whatever facts that takes; otherwise it is an
  error. Its extent is that of the entries minted beside it: a match
  branch discards it with the branch's facts, a `let`'s right-hand
  side retains it (§27).
- `(open-absurd e ann)`, an expression whose size and result types
  `ann` gives, a return telescope as a `match`'s or `_` for the
  enclosing one (§26). It takes `e` at `erased`, records and mints
  nothing, and requires the open to *fail*: it cashes a contradiction
  between the facts in force and the `Matchable`, as an absurd branch
  does one with a pattern (§21).

**The invariant.** At most one opened `Matchable` names a given type
constructor or value constructor, canonically. Whenever two opened
`Matchable`s would name one thing, at an open or when a forcing (§7)
equates two type constructors or two value constructors, they are
unified, forcing, through the `enum`/`union` tag, the marks, the
constructor count, each constructor's multiplicity marker, the
constructors and the type constructor, hence their signatures. Two that
cannot be unified contradict; two that can become one, the entry kept
being the one the elaborator can best read: `Const` with the type's own
declaration, else non-erased and still bound. So two opened
`Matchable`s for one type are never ambiguous: they are one, or they
contradict.

**What requires an open.** §7's disjointness rule; `match`, `let-match`
and `comptime-match`; the emptiness check of §25 and §51;
`matchable-of`, which finds only an opened `Matchable`; `coercible-wrap`,
which reads the `newtype` mark off the opened `Matchable` listing its
constructor (§33); and the cell rules of §37. `delegate-of` and
`at-fn-of` fetch from ambient scope instead (§33, §39). §7's occurs check and its refutation by signature are
not gated. A match or `let-match` that dispatches at runtime, one at
`many` or `unique` on a non-erased scrutinee, uses its `Matchable` at
`many` and requires the opened entry to be **readable**: `Const` with
the type's declaration, or non-erased and still bound. A
`comptime-match` requires the stricter half, `Const` with the
declaration. Readability is judged at the match: a `many` parameter
opened at `erased` serves no dispatching match. An unopened `Matchable`
leaves its type constructor opaque, so an unopened first-class type
constructor unifies with any other of its signature.

`def-adts` is the sole minting site: declaring an ADT mints an
anonymous `Matchable` from its tag, marks and constructor markers, and
opens it. The built-in `Special` and `Sharing` are opened at the start
(§42). The opaque built-ins, `Level`, `Predates`, `Subterm`,
`Coercible`, `Delegate`, `AtFn` and `Slot`, have no `Matchable` and are
never opened, so they are neither matchable nor empty (§25).

`(matchable-of T)` takes a bare unapplied type constructor and yields
the opened `Matchable` for it, an error when none is open; a name is
read through its aliases (§19). A `let` gives it a name.

## 9. Restricted dependent types

A type never involves a function call. A type is built from:

1. variable references,
2. applications of a type constructor,
3. applications of a value constructor,
4. applications of a type former: `Fn`, `UniqueFn`, `TyCtor`, `ValCtor`
   (§11), `Matchable` (§24), `Cell` (§37).

An `is` expression (§12) follows the same grammar. Type checking is
canonicalize, then compare for identity (§7).

A former's telescope entries bind names (§26, §3). Bound occurrences
are de Bruijn indices; free references are entries of §5. Pattern
matching assumes uniqueness of identity proofs (Axiom K).

## 10. `Type : Type`, no strict positivity

There is no universe stratification and no positivity requirement on
function or datatype signatures. `Type` is built by the nullary type
constructor `Univ`: `Type` is an entry whose `is` rule is `(Univ)`, and
`(Univ)`'s type is `(Univ)`.

## 11. Type formers for functions and constructors

Types are first class (§24), so there are expressions that produce
them. A function's telescope, a type constructor's and a value
constructor's differ in grammar, so there is one former for each:

1. `Fn`: `(Fn L params -> returns)`, a level (§17) and two telescopes
   whose entries each choose their multiplicity; a parameter may be
   marked `subterm`, and a parameter or return may be written `at`
   (§36). `UniqueFn` has the same shape (§32). The
   function's own multiplicity is not part of the type (§14).
2. `TyCtor`: `(TyCtor params -> Type)`. Its entries carry no
   multiplicity, type-constructor arguments being always erased (§21),
   and the return is `Type`, a single one.
3. `ValCtor`: `(ValCtor fields -> (T args))`. No level, no `subterm`;
   each field chooses its multiplicity; the return is one saturated
   application of a type constructor in scope, never one of the
   former's own binders, and carries no multiplicity, phantomness
   being declared on the `def-adts` line and recorded in the
   `Matchable` (§21, §24).

Only `Fn` and `UniqueFn` have a return telescope (§26). All three share
the telescope notion of §3. Neither `at` nor `slot-of` may appear in a
`TyCtor` or `ValCtor` telescope (§36). The declaration syntax
`name : (telescope) -> (telescope)` of §55 and §56 is sugar over these
formers plus a name and, for a function, a body; a function's level is
written on its `def-fns`. `is` (§12) works in any of the three
telescopes; in a `TyCtor`'s it is legal but pointless, every entry
there being erased.

## 12. `is` in place of a type

Wherever a variable is introduced, instead of its type one may write
that the variable `is` another expression; its type is then that
expression's. The expression is in §9's grammar. `let` is the one
binder where both type and `is` may be omitted, the right-hand side
fixing them.

Given `Add : (Nat) (Nat) (Nat) -> Type`:

```
reify-add : (many (Nat) a b) (erased (Nat) c) (erased (Add a b c) p) ->
            (many c is d)
```

`c` and `p` are erased, and the return `d` is `c` at multiplicity
`many`: `is` gives `d` its type through `c` while its multiplicity
differs, which is how an erased witness is reified. An argument
landing on an `is` parameter or field, or a result landing on an `is`
return, is written like any other and must canonicalize identically to
the `is` expression; its multiplicity is the position's.

## 13. Multiplicities

Every binder declares a multiplicity: `erased`, `many` or `unique`.
`erased` is Idris 2's multiplicity 0 and `many` its ω, spelled as
words (§1). There is no default: wherever a multiplicity is a choice,
it is written.

A binder may be declared `unique` beside `erased` and `many` (§14):
function parameters and return entries, constructor fields, `let`
binders, and a match's scrutinee. Where a value can be mutated in
place, through the cell a destructure gives back (§37) or by an extern's
own in-place operation (§43), a `unique` binder on it is the only
reference to it. Where nothing can mutate the value the sole-reference
property is neither promised nor needed, and a `unique` binder there
may alias a live `many` one (§34). The guarantee is the binder's, not
the type's: there is no unique type, no unique constructor, and a
`def-adts` constructor marker or a `Matchable` marker is never
`unique`. `match`, `let-match` and `comptime-match` take the mode
`unique` (§23).

## 14. Declared erasure

Every binder declares its multiplicity, so every name's erasure is
known where it is bound, and an expression's erasure is fixed by the
position it occupies. Nothing is derived from usage. The binders:

- function parameters, return entries and constructor fields: their
  telescope entries (§11, §3);
- a value constructor: its `def-adts` marker (§21); a function: its
  `def-fns` or `def-unique` marker, which is neither part of its type
  (§11) nor written at a call;
- `let` binders: per binder (§19);
- a match's scrutinee: the mode on the `match`, which fixes the branch
  fields (§21, §22); `let-match` and `comptime-match` fields
  likewise (§28, §27);
- everything minted by kind: a `Level`, a proof and a type constructor
  are `erased`; a `Matchable` is `many` (§24); a slot is as §35 has it.

The **erased positions**: an argument at an erased-declared parameter
or field; any argument of a type constructor (§21); a type or `is`
expression (§9, §12); the final expression of the right-hand side of a
`let` whose binders are all `erased`, each entry of a `values` there
taking its own binder's multiplicity; the scrutinee of an `erased`
match; the proof argument of a `coerce`, every argument of a
`coercible-*` form, of `prove-subterm`, `prove-predates` and the three
axioms, and the proof inside `(subterm p)` and `(predates p)` (§18, §19,
§33); the body of an absurd-by-proof branch and of an `absurd` function
(§21, §25); and every sub-expression of an erased expression. A
phantom constructor's branch under a non-erased scrutinee is erased
throughout (§21), and so is the body of an `erased` function: it is
checked with every return entry `erased`, whatever its signature says,
so such a function is only ever held or called at `erased`. Every other
position is non-erased, a position of size zero included.

Checking is local. Referencing an `erased` name from a non-erased
position is an error; referencing a `many` name from anywhere is fine.
A non-erased value is copied into an erased position for free, never
the reverse: that way needs a proof, `coerce` (§33) or `is` reification
(§12).

A multiplicity written on a form must match the form's position: a
`match` in an erased position writes `erased`, and `many` or `unique`
there is an error. A statement's position is that of the expression it
belongs to (§27), so the rule reaches `let-match`.

For a call or constructor application:

1. If the result is erased there is no further constraint: any
   callee, any argument erasures.
2. If the result is non-erased, each argument on a non-erased
   parameter or field must itself be non-erased, and the callee must
   be non-erased.

Phantom constructors, `erased` functions and type constructors enter
scope erased, so by rule 2 none of them produces a non-erased result.
Multiplicity is relative to position, not a property of a value: any
function may be invoked in an erased position with erased arguments,
so a `many` parameter may hold a value built by an erased constructor.

Erasure is settled from a unit's text alone, a function body over its
signature or a run-position statement over its binders, before that
unit is compiled or run.

## 15. Uses of unique binders

Each binder is checked by the uses it has on each path through the
code, with no order among them. On one path a `unique` binder either
has exactly one non-erased use, at unique, beside any erased mentions,
or has any number, zero included, of erased uses and of degraded many
uses (§16) and none at unique. A unique use beside any other non-erased
use of the same binder is an error, whichever the elaborator meets
first. An erased mention is never a use and is allowed anywhere, before
or after the binder is consumed: a proof or a type may name a consumed
value.

Over the branches of a match a binder's state afterwards is the maximum
of its states after each branch, in the order unused, then used at
many, then used at unique: used at many leaves the binder usable at
many and never at unique; used at unique leaves it usable only erased.
A branch with no non-erased mention contributes nothing: an
`(absurd C)` branch, an absurd-by-proof branch, and a phantom
constructor's branch under a `many` or `unique` scrutinee (§21). An
`else` branch takes part like any other.

A `unique` value need not be used. A `let` with no binders runs its
right-hand side, a position of size zero being non-erased (§14), which
is how a value is consumed for its effect alone.

**Four kinds of mention.** A variable occurs in code in one of four
ways, of which the second and third are uses:

- an **erased mention**, §14's erased position, allowed before or
  after the binder is consumed;
- a **use at many**, a non-erased position at `many`; a `unique`
  binder stands there only inside a `share` (§16);
- a **use at unique**, a non-erased position at `unique`, which
  consumes it;
- a **direct variable reference**, the argument of `slot-of` (§35):
  the variable itself, never a telescope binder; the occurrence is not
  a use, so it neither degrades nor consumes and may follow the
  consumption.

Every argument to a constructor, a function or a cell is as if bound
to an anonymous variable first. An argument that is already a
variable is not rebound; one that is not is bound before the call when
its parameter is non-erased in a non-erased position or when a later
entry of the signature names its slot (§36, §35).

## 16. `share`

A `unique` value is born unique, by a constructor application in a
unique position, a cell invocation (§37) or `def-unique` (§32), and
reappears unique as a `unique`-declared return of a non-erased call, as
a `unique`-labelled field taken by a `unique` destructure (§22), or as
the result of a `coerce` in a non-erased position whose target side is
`(Unique)` (§34).

Degradation from `unique` to `many` is explicit: a `unique` value in a
`many` position is an error unless written `(share e)`. With `e` a
variable `x`, the form is a many use of `x`, an error beside a use of
`x` at unique on the same path (§15), after which `x` is usable at many,
as `(share x)` every time, and never again at unique; its result `is
x`, so a binder of it forwards `x`'s type and facts, and it is at `x`
(§36). With `e` any other expression, `e` is elaborated at `unique` and
the fresh result is shared. A `share` in an erased position is an
error, nothing being used there. A head written `(share n)` dispatches
as `n` does (§6).

## 17. Function levels

Every function has a level, a natural number, erased and part of the
function's type (§11). A function may call a function of a strictly
lower level, and a function of its own level only under the `Subterm`
discipline of §19. All functions of one `def-fns` block share one level,
written once on the block. Type and value constructors have no level,
and there is no currying, for functions or constructors.

Termination rests on levels. A function's parameters may be marked
`subterm`, as part of its signature. A call decrements a lexicographic
order whose most significant component is the level, followed by the
`subterm`-marked arguments left to right. An ADT may have zero
constructors (`False`).

## 18. Built-ins backing termination

- `Level`: a nullary type constructor, so the type is `(Level)`.
- `Predates : (Type A) (A a) ((Level) l) -> Type`.
- `Subterm : (Type A) (A a) (Type B) (B b) -> Type`, heterogeneous.

All three are opaque (§8), erased by kind (§14). Three axioms, each a
special form taking its two premises as arguments:

- `predates-trans`: from `(Predates A a l1)` and
  `(Predates (Level) l1 l2)`, `(Predates A a l2)`;
- `subterm-trans`: from `(Subterm A a B b)` and `(Subterm B b C c)`,
  `(Subterm A a C c)`;
- `predates-subterm`: from `(Predates A a l)` and `(Subterm B b A a)`,
  `(Predates B b l)`.

Proofs are minted by two forms.

`(prove-subterm a b)` asserts that `a` is a subterm of `b`. Both are
expressions in §9's grammar; after canonicalization `a` must be a
strict subtree of `b`, where the search walks through type-constructor
and value-constructor applications (productions 2 and 3) and treats a
type former (production 4) as opaque.

`(def-lvl L)` mints a fresh `Level`, erased, with §5's level-mint
marker. A level minted later is strictly higher than one minted
earlier, so a function at a later level cannot be called from code at
an earlier one. `(prove-predates x L)` mints `(Predates A x L)`: `x` is
a variable that was in scope when the `def-lvl` of `L` ran, and `L`
must canonicalize to a `def-lvl`-minted entry.

## 19. Namespaces, special forms, macros, call-site proofs

**One namespace.** Special forms, types and values share one
namespace, and everything in it may be shadowed, special forms and
types included.

**State-forwarding `let`.** A `let` binder takes the state of the
right-hand-side entry it corresponds to: `Const` or `Dyn` (§5), the
stored value if `Const`, and, through an alias rule in the fact table
(§7), its type and `is`. This holds whenever that entry is an
expression in §9's grammar and so has an entry of its own; it is per
binder, so with `(let ((many a) (many b)) (values x y))` `a` takes from
`x` and `b` from `y`. A call, a match or a `coerce` forwards nothing:
its results are `Dyn` inside a body (§28), and in run position (§27)
the statement is run and its binders are minted `Const` (§29).
Forwarding is one way a `Const` reaches a function body, a special
form renamed locally say; the others are a direct reference to the
entry and a macro expansion that mentions it.

**`let` binders.** Each binder is a telescope entry with the type
omissible: `(many x)`, `(erased (Nat) x)`, `(many c is d)` (§3). The
multiplicity is mandatory and is the binder's declaration (§14): a
`many` binder needs a non-erased value, a `unique` one a unique value
(§16), and an `erased` binder accepts anything. A type or
`is` clause, when written, is checked for identity against the
inferred one (§9); a mismatch is an error. A binder may not be written
`at` (§36).

**Special forms as data.** A special form is a nullary constructor of
the built-in enum `Special` (§42). The elaborator dispatches on one in
head position only when that head is `Const` and non-erased (§6);
held as a value it is ordinary data. `Special`'s constructors are §54's
registry, the annotation tokens included.

**Macros.** `Macro` is a type with one constructor holding a function
from a list of unelaborated terms (`Raw`) to one. Expansion counts
against a global limit. Neither `Macro` nor `Raw` is implemented in the
prototype, so a `Macro` head is an error there.

**Call-site proofs.** How §17's decrease is discharged depends on the
kind of call:

- A call to a strictly lower-level function carries `(predates p)`
  immediately after the callee, `p` a `Predates` relating the callee's
  level, read from its `Fn` or `UniqueFn` type, to the current level
  (§5). A `Predates` about the function value itself, which
  `predates-subterm` can produce, is not accepted here.
- A same-level call carries `(subterm p)` immediately before the
  decreasing argument, `p` a `Subterm` relating that argument to the
  enclosing subterm argument at the same subterm index (§5). The
  argument must sit on a `subterm`-marked parameter, every
  `subterm`-marked argument before it must be identical, after
  canonicalization, to its enclosing counterpart, and the enclosing
  function must have a subterm parameter at that index.
- A call carries at most one of the two. A call inside a body with
  neither is given one (§48); at the top level a call carries
  none (§20).
- Every application, a constructor's, a lower-level call, a same-level
  call, marked or not, works through a first-class value. Only a macro
  or special form needs a constant-known head (§6).

**`tail` and `notail`.** `(tail (f ...))` asserts that the call
compiles to a tail call; `(notail (f ...))` asserts the opposite. A
claim the compiler cannot honour is an error. Tail position is judged
on the post-erasure code, with erased positions, types and coercions
gone and every `let` that only renames resolved away (§33): the call is
the body's final expression, or its results are bound by a `let` and
returned in order by a final `values`, coerced or not; a match in tail
position puts its branches in tail position. An `at` return is dropped
from a call's results for this reading (§36). The marks wrap a
call and nothing else, and are an error in an erased position.

**`delegate`.** `(delegate (f ...))` is `tail` plus the same
pass-through requirement on the arguments: on the post-erasure code the
marked function's body is nothing but the call, with the non-erased
parameters passed straight through in order. The callee is named by a
variable introduced before the function whose body it is, in §5's
introduction order: never the function itself, a later function of its
block, a parameter, or anything the body binds. The two functions'
non-erased behaviour is then identical, and `def-fns` mints a
`Delegate` proof recording it, which `delegate-of` fetches and
`coercible-of` turns into a `Coercible` (§33). A function marked
`extern` may not have a `delegate` body (§42). The function may name
its callee on its header line, `(many g at f : ...)` (§41).

## 20. The top level calls freely

At the file's top level, anywhere outside a function body, the match
branches of a top-level statement included, any constructor and any
function may be called with no `Predates` or `Subterm` proof. A
decrease annotation written there is an error, not ignored: there is no
level to check it against. The top level sits above every function
level, and no function body can call into it.

## 21. Data types and match branches

**Two kinds of data type.** An `enum` has a non-erased discriminant, a
`union` an erased one. Independently, each value constructor's
declaration in `def-adts` carries `erased` or `many`: the multiplicity
the constructor's entry takes, `erased` making it **phantom**. The
marker is recorded in the type's `Matchable` (§24), not in the
constructor's `ValCtor` type (§11). Each field is declared `erased`,
`many` or `unique` (§22). Subterm recursion (§17) may go
through an erased field.

A type marked `newtype` has **newtype shape**: an enum with exactly one
non-phantom constructor holding exactly one non-erased field, or a
union whose non-phantom constructors each hold either only erased
fields or exactly one non-erased field, at least one of them the
latter. A value of it is represented as that field (§33).

**A constructor returns its own type.** Every value constructor is
declared under exactly one type constructor in `def-adts`, and its
return is a saturated application of that type constructor, one
argument per entry of its telescope. The arguments are expressions in
the constructor's own telescope under §9's grammar.

**Indices are not shared scope.** A type constructor's parameters are
in scope in its own telescope only. A constructor that constrains an
index redeclares a variable for it, with its type, in its own
telescope.

**Match-proved equality is not substitutability.** Two expressions a
branch forces equal (§7) may still differ in multiplicity, which is a
separate axis.

**Matching.** The multiplicity of the fields a branch binds follows
from the scrutinee's mode: at `many` each field at its declared
multiplicity (a `unique` field comes out `many`), at `erased` every
field erased, at `unique` as §22 has it.

A branch on a phantom constructor under a `many` or `unique` scrutinee
can never run, since no non-erased value is headed by a phantom
constructor (§14, rule 2). Everything in scope there is erased, the
branch's fields included whatever their declarations say, and so is
the branch's result: its body is checked with every result erased, and
it must still produce the declared values. (Without the body, a `many`
function from a type whose only constructor is phantom to `False` would
need no branch, and `(F)` inhabits that type in erased positions.)
Under an `erased` scrutinee a phantom constructor's branch is an
ordinary branch: an erased value may be phantom-headed.

**Four kinds of branch:**

1. **present**: `((C f1 ... fn) body)`, one binder per field, the
   erased ones included, plus a cell binder where the type has cells
   (§23).
2. **absurd, automatic**: `(absurd C)`, a constructor refuted by the
   facts in force (§7), with no fields and no body. It is optional: an
   unlisted constructor that is refuted needs no branch. It is an error
   when `C` is not refuted.
3. **absurd, by proof**: `(absurd (C f1 ... fn) body)`, a branch that
   refutes (§51) or produces a value of an empty type (§25)
   instead of the match's result.
4. **else**: `(else body)`, at most one per match, standing for every
   constructor not listed by name that is not refuted. It binds
   nothing, except the scrutinee itself where §23 says so, and
   its body is checked against the annotation as written, with no
   branch-forced facts. It is an error when it stands for no
   constructor.

Each constructor has at most one branch. A listed present branch whose
forced unification contradicts is an error. A constructor with no
branch must be refuted or stood for by the `else`.

**One real branch.** A match in an erased position is unconstrained.
If at least one of its results is non-erased: with a non-erased
discriminant, a `many` or `unique` match on an enum, there is a runtime
tag to dispatch on; with an erased discriminant, an `erased` match or a
union in any mode, at most one branch may be **real**. The others are
automatically absurd, absurd by proof, or a phantom constructor's
branch under a non-erased scrutinee. An `else` counts as one real
branch unless every constructor it stands for is phantom under a
non-erased scrutinee, when it counts as none and its body is erased
throughout.

**First-classness.** Types, type constructors and value constructors
are first class (§24). Every argument of a type constructor is erased,
a type constructor enters scope erased, and so does a phantom
constructor (§14). A value of type `Type` is erased.

## 22. Fields under each mode

A field is labelled `erased`, `many` or `unique`. A destructure is a
`match`, `let-match` or `comptime-match` on a value, binding its
constructor's fields; a `cell-match` (§38) is governed separately.

What a destructure hands out for a field, by the scrutinee's mode:

| field label | `erased` | `many` | `unique` |
|---|---|---|---|
| erased | erased | erased | erased |
| many | erased | many | many |
| unique | erased | many | unique |

A unique-labelled field under a `many` scrutinee comes out `many`: a
shared block shares everything it owns. Construction is the dual, by
the position's multiplicity:

| field label | erased position | many position | unique position |
|---|---|---|---|
| erased | erased | erased | erased |
| many | erased | many | many |
| unique | erased | many | unique |

A `unique` field of a constructor built at `many` is requested at
`many`.

## 23. The `unique` match mode and the cell binder

`(match unique x ann branches)` consumes `x` and binds each branch's
fields per §22's `unique` column.

On a type whose constructors have cells (§37), a pattern may add one
binder after the fields: `((C f1 ... fn u) body)` beside
`((C f1 ... fn) body)`. The extra binder names the cell the
constructor occupied, at the scrutinee's own multiplicity, `many` or
`unique`, of type `(Cell C (slot-of g1) ... (slot-of gk))` with one
slot per non-erased field binder `gi` in order, and it is at `x` (§36).
A branch gets a `unique` cell out of the match by returning it into an
entry of the match's annotation marked `at x`. A cell at `unique` may
mint its value at `unique`; a cell at `many` mints its value only at
`many` (§37). The `else` branch may bind the scrutinee back,
`(else x2 body)`: `x2` is a fresh binder at the scrutinee's
multiplicity, `is x` and at `x`, the same whichever constructor the
`else` stands for; a lone item after `else` is the body. A pattern on a
constructor with no cell (§37), or under an `erased` scrutinee, has no
extra binder.

`let-match` takes the same modes and the same extra binder, binding
outward (§27). `comptime-match` at `unique` is a destructure like any
other: it consumes the `Const` at unique and binds its fields `Const`
at their labels; at `many` it reads the `Const` at many. Its scrutinee
may be written `(share x)` at `many`, the written degradation a unique
`Const` needs; `(share x)` at `unique` is an error. The elaborator's
other reads of a `Const`, a special form at a head or a `Matchable`
read, are many uses (§32). Readability requirements for a dispatching
match are §8's.

A value is read without giving up its uniqueness by a `unique`
destructure followed by a full-at reinvocation of the same constructor
in each branch (§37), which erases to the tag read and nothing else; at
`many` the same reinvocation costs nothing and gives the value back at
`many`.

## 24. First-class objects

Each of the following is ordinary first-class data:

1. an ADT value;
2. a function, of `Fn` or `UniqueFn` type;
3. a type constructor, unapplied;
4. a value constructor, unapplied;
5. a `Matchable`;
6. a `Type`;
7. a cell or a slot (§37, §38);
8. an opaque object: a `Level`, a `Subterm` or `Predates` proof (§18),
   a `Coercible` or `Delegate` proof (§33), an `AtFn` proof (§39).

`Special` and `Sharing` values (§19, §33) are ADT values. Applying a
held constructor is ordinary application.

A `Matchable` is typed `(Matchable d marks T (e1 C1) ... (en Cn))`: `d`
is `enum` or `union`, `marks` is `newtype`, `extern`, both in either
order, or neither, `T` the type constructor, and the `Ci` its value
constructors in declared order, each with its multiplicity `ei`,
`erased` or `many`. `T` and the `Ci` are bare and unapplied; `List`'s
is `(Matchable enum List (many Nil) (many Cons))`. The tag, the marks
and the `ei` are exactly what no type records: a `TyCtor` type carries
no discriminant and a `ValCtor` type no phantom marker. A `Matchable`
is minted only by `def-adts` (§8), at `many`; its value holds an
`extern` type's construction and matching (§42) and nothing else, so a
match that dispatches at runtime on an extern type needs one it can
read (§8). Nothing consults a `Matchable` until it is opened (§8).

A `Matchable` is what tells the checker a type's constructors are
disjoint (§8); what lets a match work through first-class type and
value constructors; and what a match reads: its type for the tag,
each branch's discriminant and the marks, so the constructors named in
a match may be erased, and its value only for an extern type.

## 25. Absurd functions

A function marked `absurd` on its `def-fns` or `def-unique` line,
beside its name and multiplicity, `(def-fns L $ (many absurd explode :
...))`, has a body that, instead of its declared returns, produces one
value of a type with no constructors (`False`), read off the type's
opened `Matchable` (§8), or refutes the facts in force (§51).
It is the function-level counterpart of §21's absurd-by-proof branch
and carries the same token (§59). Its body is an erased position (§14)
and it compiles to no code.

A contradiction that lives in the fact table rather than in a value,
two constructors of one opened `Matchable` equated, is cashed by
`open-absurd` (§8), which produces the declared result with no empty
type in between. Where a scrutinee is at hand, a match whose branches
are all refuted produces its declared result (§21).

## 26. Multiple return values

A function returns zero or more values, and a later return may depend
on an earlier one: the return telescope is a telescope like the
parameter telescope, each entry depending only on the entries before
it. This is a function-only feature; a type or value constructor
returns exactly one value (§11), and there is no sigma type: a
multi-value expression has no type of its own, each entry of a
`values` is a size-one location (§27), and several values cannot nest
or be passed as one.

`values` introduces several values and `let` eliminates them, one
binder per value: `(let ((many q) (many r)) (divmod n d))`. A `let`'s
items are its binders, bracketed, then any statements, then the final
expression. The binders are a flat list, not a telescope: an earlier
binder is an ordinary scope entry to a later one. The dependency among
returns lives in the function's return telescope (§11), which a `let`
receives instantiated.

`match` is written `(match m x ann branch ...)`: `m` is the scrutinee's
multiplicity, `erased`, `many` or `unique` (§21, §14, §23),
`x` the scrutinee, and `ann` the result annotation, a telescope of
types with no multiplicities, `(((Nat) r))` say, which fixes the
match's size (§27). The annotation is mandatory: it is the match
motive, and in a dependent match the branches' result types mention
branch-forced facts. `_` reuses the telescope the position expects
(§47), and `(at (...))` makes an at-match (§40).

## 27. Expressions, statements and size

Every expression has a **size**, the number of values it produces.

An expression is a series of **statements** followed by a final form:
a `values`, each entry of which is a size-one expression, or a single
form of any size, a call, a match, a `coerce` or a `tail`-marked call.
A one-entry `values` may be left implicit, so `x` and `(Cons A hd tl)`
are size-one expressions equal to `(values x)` and
`(values (Cons A hd tl))`; `(values)` has size zero.

Every form binds within its own sub-expressions. A **statement** also
binds outward: its names, and the facts it mints, enter the expression
containing it, visible to the rest of that expression and gone when it
ends. A statement produces no values. The statements are `let`,
`def-lvl`, `def-fns`, `def-unique` (§32), `def-adts`,
`comptime-match`, `let-match`, `open-adt` (§8), `slot-self` and
`open-at-fn` (§35, §39), `unary` (§49) and
`dump-context` (README.md). All but `comptime-match` may appear at the
top level or inside a body. `def-fns` and `def-adts` bind the defined
names outward and each definition's parameters inward.

A `let`'s right-hand side is an expression, so the statements before
its final expression are statements of the expression containing the
`let`: their names are visible within the right-hand side only, but
their entries, facts and opened objects (§8) enter the expression
after the `let`, anonymously, at the multiplicities they were declared
with. Those statements run, or their code is emitted, whether or not
the `let`'s binders are erased; only the final expression is the
position §14 calls the right-hand side.

`match` binds inward only: a branch's fields and the facts forced by
entering it reach the branch and no further. So a `match` is an
expression, of the size its annotation gives (§26).

`(let-match m x (C f1 ... fn))` is a statement binding outward: it
requires that exactly one constructor of the scrutinee survives the
automatic refutation an ordinary `match` applies (§7), each
constructor checked independently from the environment before the
form, with fresh fields and without the facts learned while checking
another. The named constructor must be the survivor; its fields and
the facts of its branch stay in scope for the rest of the containing
expression. It is an error when no constructor survives, when more
than one does, or when the pattern names a refuted constructor. The
survivor may be phantom when `m` is `erased`, its fields then erased;
at `many` or `unique` a phantom constructor is refused. Nothing
inspects the scrutinee's stored value, so the scrutinee need be neither
`Const` nor non-erased and the form is not confined to run position.
The fields take their declared multiplicities under `m` as a match's
do (§14); the `Matchable` must be open and, where the form dispatches
at runtime, readable (§8). With further branches the form is
§52.

Most positions require size one. The exceptions are fixed by something
written elsewhere: a function body, by its return telescope (§26); a
match branch body, by the match's annotation; a `let`'s right-hand
side, by its binders.

**The top level.** A file's top level is an expression and so has size
one. Several files on one command line share one scope, in order. A
file ending in a statement produces nothing. Otherwise the final
value's type decides what the driver does with it: a function from one
`many (String)` to one `many (String)` is applied to all of standard
input and its result written to standard output; an `IO` value (§42)
is performed, the driver consuming it at `unique` and applying each
request's continuation once; a function from no arguments to one
`many` or `unique` return is applied and its result printed, which is
how a program asks for its final value to be computed by compiled code;
any other value is printed (§45). A function with erased
parameters or extra erased returns is not read as either function
form.

**Run position.** A statement is in run position when it sits under no
function body and no match branch. It is run as soon as it has been
elaborated, before the code after it is checked: the statement is
elaborated, its erased positions stripped, the code run by the
evaluator, and its binders minted `Const` with the resulting values
(§29). This nests: a `let`'s right-hand side may contain statements,
and those in run position complete before the enclosing `let`'s. A
file's top level is run position, so calls there need no proofs (§20).
Nothing under a function body or a match branch runs at compile time.
A run-position statement's binders declare their multiplicities (§19),
which is what lets it be stripped and run before the code after it is
elaborated.

## 28. Call and match results; `comptime-match`

A call's result, a match's result, a constructor application and a
`coerce` (§33) are `Dyn` where they stand, even over `Const`
arguments: nothing is folded through them. Inside a function body or a
match branch every binding is `Dyn`. Anywhere else, run position (§27),
a statement is run as soon as it is elaborated and its binders are
minted `Const` (§29); a definition wanted as `Const` is bound by its
own `let` in run position (§57's `xs`).

`(comptime-match m x (C f1 ... fn))` asserts at elaboration time that
the `Const`, non-erased entry `x` holds a value headed by `C`, and is
an error otherwise. `m` is `many` or `unique` (§23); `x` is a
variable, or `(share x)` (§16), naming the entry whose stored
value is read, not an expression; the type is an enum, never a union;
`C` is not phantom; the pattern binds every field, the erased ones
included, and a cell binder where the type has cells. It is the one
statement confined to run position (§27). It consults the type's
`Matchable` (§24) for the discriminant and binds the fields `Const` at
their declared multiplicities under `m` (§22): `many` fields
with the values projected from the stored value, erased ones as §5's
tokens, the stored value lacking them.

On a mismatch the error prints the expected constructor and the actual
value, discriminant and arguments. This serves as a diagnostic
channel: assert the expected constructor of a wrapper enum whose other
constructors carry the message to report, and the payload is printed.

## 29. `Const` formation and compile-time inspection

The states are `Const` and `Dyn` (§5). `Const` arises at three sites,
each with the multiplicity declared:

1. **A statement in run position** (§27, §20): every name it introduces
   is `Const` once it has run. A `let` is elaborated, stripped of its
   erased positions, run by the evaluator, and its binders take the
   resulting values at their declared multiplicities (§19). A
   `def-lvl`, `def-fns`, `def-unique` or `def-adts` involves no
   evaluation: a function's value is its compiled code, a `Level` an
   erased token, a `Matchable` the FFI's wrapper for an `extern` type
   and nothing otherwise (§24). Within the bodies of a `def-fns` block
   the block's functions are `Dyn`; they are `Const` after it, at the
   multiplicity on their lines.
2. **`comptime-match` field binding** (§28), at the fields' declared
   multiplicities.
3. **State-forwarding `let`** (§19).

Nothing else mints `Const`. Inside a function body or a match branch
every binding is `Dyn`, nested definitions included, so a `Special` or
`Macro` that is ever invoked (§6) originates in run position. A
constructor application over `Const` arguments is `Dyn` (§28).

**Inspection requires `Const` and non-erased.** A stored value is read
in three places: §6's head dispatch, `comptime-match`'s discriminant
read, and the running of a run-position statement that references the
entry, where the value is embedded in the code run. §7's engine
consults no stored value. All three require the entry `Const` and
non-erased: an erased `Const` holds only §5's token, its value never
having been computed, since the erased positions are stripped before
the evaluator runs. An erased `Const` may still be referenced from a
statement's erased positions, which are stripped rather than read.

**The checker never evaluates.** The checker computes only what the
source spells out: constructor application assembles data whose shape
the source dictates, and `comptime-match` verifies an asserted
discriminant and projects. Selecting a match branch from a value would
be evaluation, so a match's results stay `Dyn` even on a `Const`
scrutinee (§28); binding the match with its own `let` in run position
hands the branching to the evaluator. The inspection sites are checks
rather than forwarding: by the time one runs, the inspected entry's
multiplicity is settled, so no erasure demand flows backwards into code
already checked, stripped and run. Nothing crosses an evaluation
boundary: no erasure demand and no branch-hypothetical fact.

**The round trip.** Checking a run-position statement is a dialogue:
the elaborator checks it and produces code with the erased positions
removed; the evaluator runs that code; the values come back to be
stored (§5) and embedded as constants. Round trips nest, a nested
statement in run position running before the enclosing statement's own
trip. A run-position statement resembles an anonymous nullary function:
its binders declare their multiplicities at its boundary, like a
signature, and its result type needs no annotation. Every fact minted
from a stored value, a `comptime-match` and whatever follows from the
fields it binds, rests on the evaluator having evaluated correctly.

## 30. Bottom-up type inference

Types are written at ADT definitions, function parameters and returns,
and match results (§26). Everywhere else they are inferred.
Multiplicity, by contrast, is declared at every binder (§14).

## 31. Evaluation strategy

Evaluation is eager. The semantics is that of a machine with unlimited
stack and heap; a real run may crash where the host cannot represent
what is asked of it, and a crash produces no value, never a different
one.

## 32. Closures, `def-unique`, and the top level

A function defined by `def-fns` is a closure over its scope and may
mention a `unique` binder of that scope only erased or degraded, by a
`(share x)` written in the body or earlier.

`(def-unique L $ (unique f : params -> returns) body)` defines one
function, not a block, whose type is built by the former
`(UniqueFn L params -> returns)` and whose body may close over
`unique` binders as unique: each such binder the body uses at unique
is consumed by the definition itself, where the `def-unique` is
elaborated and not at each call, once modulo match branches as §15 has
it. The defined binder is born unique; calling the function is a use
of it at unique, or erased, so a shared `UniqueFn` is callable only
erased and `share` on one leaves a dead value. A `UniqueFn`-typed head
is applicable in §6's tier 1 as an `Fn`-typed one is, the call using
the head at unique. The level is written as on a `def-fns`, `_`
included (§46), and may be shared with ordinary functions; the
parameters may be marked `subterm` and the body may make same-level
calls under `subterm` proofs; the marker is `unique` or `erased`, and
`absurd`, `extern` and `at` (§39, §41) may follow it; the function's
own name is in scope in its body as an erased entry, so a self call is
refused as any call through an erased head is, and recursion goes
through a `def-fns` function taking the values as parameters; the body
supports `tail`, `notail` and `delegate`, and `delegate-of` fetches a
delegate's proof as for a `def-fns` function.

A top-level binder, and so a `Const` (§29), may be `unique` under the
same rules, run-position statements being sequential. Where the
elaborator reads a `Const` as a value, a special form at a head (§6) or
a `Matchable` that a `match`, `let-match` or `comptime-match` reads,
that read is a many use, so a unique `Const` there is an error until it
is written `(share x)`. A `comptime-match`'s scrutinee is used at the
mode written on the form (§23). The driver consumes a program's final
`IO` value at unique (§27), applying each continuation once.

## 33. `coerce`

A `coerce` reinterprets one value as another of identical runtime
representation, at no runtime cost, on the strength of an erased proof
that the two are coercible (§60).

**The proof types.** `Sharing` is a built-in enum with the nullary
constructors `Unique` and `Shared` (§42). `Coercible : ((Sharing) sa)
(Type A) (A a) ((Sharing) sb) (Type B) (B b) -> Type` is opaque (§8),
erased by kind. A side describes a non-erased use: there is no erased
side, since a `coerce` is never cashed erased and its proof is always
erased. `Delegate : ((Sharing) sg) (Type G) (G g) ((Sharing) sf) (Type F)
(F f) -> Type` has the same shape and records that `g`'s body is a
`delegate` call to `f` (§19); `def-fns` and `def-unique` are its only
introduction, with `(Shared)` for an `Fn` side and `(Unique)` for a
`UniqueFn` side.

**The expression.** `(coerce a p)`, with `p : (Coercible sa A a sb B b)`:
`a` must be identical, after canonicalization, to the value in `p`'s
type, and `b` is read from it. It produces one value `d : B` with
`d is b` (§12), `Dyn` where it stands (§28) and `Const` when a
run-position `let` binds it (§29). In a position of multiplicity `m`,
with `sa` and `sb` canonicalizing to `(Unique)` or `(Shared)` there,
the form uses `a` at `sa`'s multiplicity, consuming it when `(Unique)`
(§15), and yields its result at `sb`'s: an error where `sb` is
`(Shared)` and `m` is `unique`, and a unique value in a many position,
needing a written `share` (§16), where `sb` is `(Unique)` and
`m` is `many`. `p` is erased always. The result is at `a` (§36).

**Minting proofs.** All of the following are special forms (§54),
checked at elaboration. `s` is a `(Sharing)` value, `_` solving it from
the expected type (§50).

1. `(coercible-refl s e)`: `(Coercible s A e s A e)`; since types
   canonicalize (§9) this relates any two `is`-equal values.
2. `(coercible-sym p)`: from `a` to `b`, conclude `b` to `a`, the sides
   swapped. Its one non-uniform case, `(Shared)` `x` to `(Unique)`
   `(MkBox x)` reversed, consumes a unique wrapper and gives its
   many-labelled field back shared.
3. `(coercible-trans p q)`: from `a` to `b` and `b` to `c`, conclude `a`
   to `c`; the two middle sides must be equal.
4. `(coercible-share p)`: `p` with both sides `(Shared)`.
5. `(coercible-wrap s C arg1 ... argn)`: wrapping into a **newtype**. A
   type is a newtype by its `def-adts` mark, which requires newtype
   shape (§21). A non-phantom constructor holding a non-erased field is
   a **wrapping constructor**: the enum's one constructor, or each such
   constructor of the union; phantom constructors count neither way.
   The form reads the `newtype` mark off the opened `Matchable` listing
   `C` (§8), which is what makes it trustworthy: the mark is what
   guarantees that `C` heads inhabited values, and a wrap through a
   constructor no mark covers would make a value with no inhabitant.
   The arguments are `C`'s telescope in order, so exactly one of them,
   `f`, sits at the non-erased field. The proof is
   `(Coercible src F f s T (C arg1 ... argn))`, `src` being `s` over a
   `unique` field and `(Shared)` over a `many` one; unwrapping is its
   `coercible-sym`.
6. `(coercible-ctor s C ...)`: the same constructor on both sides with
   fields that may differ. The arguments follow `C`'s telescope: an
   `erased` field takes two, its source and target values, and a
   non-erased field takes one `Coercible` proof between the values at
   that position, with sides `s` over a `unique` field and `(Shared)`
   over a `many` one. Each is checked against its field type
   instantiated with the source values on the source side and the
   target values on the target side, so `C`'s return type, and any
   index in it, may differ between the sides. The proof is
   `(Coercible s T (C sources) s T' (C targets))`. Using it at a
   `coerce` needs the source to canonicalize to `(C sources)`, which is
   what entering a `C` branch forces (§7), so such a proof is built
   per branch from the branch's binders. The form consults no
   `Matchable` and does not refuse a phantom `C`: a proof between two
   phantom-headed values is never cashed, no non-erased value being
   headed by one (§14).
7. `(coercible-of d)`: from `d : (Delegate sg G g sf F f)`, the
   `(Coercible sg G g sf F f)`.
8. `(delegate-of g)`: for a function `g` whose body is a `delegate`
   call to `f` (§19), the `Delegate` proof `def-fns` minted anonymously,
   fetched from ambient scope by naming `g`, read through its aliases
   (§19). `g` is `Dyn` within its own block (§29), so its body cannot
   use its own proof.

**Representation.** Coercion is zero-cost only if representations
coincide, so this is a requirement on the implementation. Values have
a uniform representation: every value is one word, an immediate or a
pointer to a block, whatever its type, so a `Cons` block holds a
`(Meters)` and a `(Nat)` alike and a wrapper's field may be
existentially typed. A value is the tuple of its constructor's
non-erased fields, one field standing bare; it carries a tag only when
its type is an enum with more than one non-phantom constructor, the
tag being the constructor's position among those and all a tag ever
distinguishes. A phantom constructor takes no discriminant. With no
non-erased field a value is the tag alone when its type is tagged, and
an unspecified word otherwise; a union never carries a tag. A newtype
value built by a wrapping constructor is represented exactly as that
constructor's one non-erased field, with no tag and no wrapper; that
representation is mandatory for a type marked `newtype` and forbidden
for one that is not, an unmarked type of newtype shape being a block
(§37). A union newtype value built by a constructor with only
erased fields is an unspecified word. A word is never read as the
field of a constructor that did not build it: a non-erased match on a
union has a single real branch, and unwrapping needs the value to
canonicalize to the wrapping constructor's application. Erased fields
occupy no space. A `delegate`-bodied function's pointer is
interchangeable with its callee's (§19). An extern type (§42) may be
marked `newtype`, its FFI author then guaranteeing the field
representation, and a newtype may wrap a field of an extern type.

Only non-phantom constructors and non-erased functions matter in items
5 to 8: a `coerce` produces a non-erased value, which none of the
others can head (§14).

Proofs over containers, every element of a list wrapped say, are built
by recursion in an `erased` function returning the proof (§14),
checked for termination like any other (§17) and never run.

**Tail and delegate.** A `coerce` erases to a renaming, so §19's `tail`
and `delegate` checks read through it: a call counts as `tail` when its
returns are bound by a `let` and repackaged in a `values` in the same
order, coerced or not, and as `delegate` when its arguments likewise
pass straight through.

## 34. `Sharing` sides

`Coercible` (§33) carries a side on each end, a value of the built-in
enum `Sharing` (§42):

```scheme
(def-adts $ (Sharing : -> Type)
  enum
  (many Unique : -> (Sharing))
  (many Shared : -> (Sharing)))
```

There is no erased side: a `coerce` is never cashed erased and its
proof is always erased, so a side describes a non-erased use.
`coercible-refl`, `coercible-wrap` and `coercible-ctor` take a
`(Sharing)` value `s` as their first argument, `_` solving it from the
expected type (§50) with no default. `coercible-ctor` and
`coercible-refl` mint `s` on both sides; a field proof `coercible-ctor`
takes has `s` on both sides over a unique-labelled field and `(Shared)`
over a many-labelled one. `coercible-wrap` mints `s` as its target
side and, as its source side, `s` over a unique-labelled field and
`(Shared)` over a many-labelled one. `Delegate` (§33) takes a side on
each end too, set where the proof is minted from the two functions'
types, `(Shared)` for an `Fn` and `(Unique)` for a `UniqueFn`, so a
`UniqueFn` delegating to an `Fn` is `(Unique)` to `(Shared)`;
`coercible-of` carries the sides across. `coercible-sym` is
unconditional; `coercible-trans` requires the two middle sides equal;
`coercible-share` weakens any proof to `(Shared)` on both sides. How a
`coerce` uses its source and yields its result under the sides is
§33's.

## 35. Slots in the fact table

Every entry of the scope environment (§5), erased ones and metas
included, is minted together with an anonymous entry of type `(Slot)`
at the entry's own erasure, its **automatic slot**, which is not in the
scope's list of names; the slot entry's own slot is itself. An erased
variable has no word, so its slot has none behind it, and §14 keeps the
slot out of non-erased positions as it keeps the variable; two erased
slots are atoms like any two slots, and equating them says nothing
about the variables. In a call in an erased position an erased
argument may fill a `many` parameter (§14, rule 1); the parameter's
slot is then that argument's erased slot. A forwarding `let` binder
(§19) sits at its source's slot whatever its erasure. Whether two
variables are at one slot is decided by the fact table's ordinary
canonicalization: an entry's slot is an atom, a rule may equate it with
another, and two slots are equal exactly when their canonical atoms
are. A slot fact is minted by forcing (§7) and ends with its scope.

`(slot-of x)`, for a variable `x` of any multiplicity, denotes `x`'s
slot: for an `x` without a written `at`, its automatic slot; for an
`x` written `at v`, a slot the fact table equates with `(slot-of v)`.
It is resolved by `x`'s binder, never through `x`'s `is` rule, which is
what keeps `at` and `is` separate. It is erased exactly when `x` is,
so it stands only in erased positions for an erased `x`. Its argument
is a direct variable reference (§15), not a use of `x`. It may be
written in a type or `is` expression, a function telescope included,
where it may name an earlier binder of the same telescope; it may not
appear in a type or value constructor's telescope. As an expression it
takes the multiplicity of its position, `unique` included, its word is
`x`'s word, and the result is at `x`, so a `let` of it sits where `x`
does.

A variable of type `(Slot)` is not its own slot by being declared:
like any entry it has an automatic slot distinct from itself.
`(slot-self s)`, a statement (§27), takes a non-erased variable `s`
whose type canonicalizes to `(Slot)` and mints, outward and by forcing,
the fact that `(slot-of s)` and `s` are equal; a contradiction is an
error. After it, `s` is the slot that `(many A a at s)` names and that
a cell type `(Cell C s)` indexes. `vacant-slot`, the built-in `many`
constant of type `(Slot)` (§42), is its own slot, which makes a cell
type naming it the type of a fresh cell; its runtime word is what
`cell-alloc` fills a vacant slot with.

## 36. `at`

A function's parameters and return entries, and the entries of a
match's or `cell-match`'s annotation, may add `at v`, several names
sharing one: `(many (Nat) r at x)`, `(unique a is r at a)`. The value
is at the same location as `v`, which may be any variable in scope: an
earlier entry of the same telescope, a return entry included, or a
variable from an enclosing scope, for `def-fns` and `def-unique` alike.
The one restriction is §7's, that no fact outlasts an entry it
mentions, which keeps a function whose type names a closed-over
variable inside that variable's scope. The entry's slot (§35) is
`(slot-of v)`, always, even where `v` is itself a `(Slot)`. An erased
entry may be `at` any variable; a `many` or `unique` entry only `at` a
`many` or `unique` one, its word being its target's and an erased
target having none. `at` may not be written on a `let` binder, in a
type or value constructor's telescope, or with a literal as target.
An `at` return may be `many` and may combine with `is`.

**What reaches runtime.** The runtime signature of a function is its
non-erased entries without a written `at`. An entry written `at`, a
parameter, a return or an annotation entry, is omitted after erasure:
its word is the word of what it is `at`. Which entries reach runtime is
read off the signature as written, never off what an `at` canonicalizes
to. At a call, the argument for a parameter written `at` is elaborated
at the parameter's multiplicity and its uses count as any argument's,
it is bound first if it is not a variable, its slot must equal the
target's slot instantiated with the earlier arguments, and it is not
passed; `_` cannot stand for it. The check is made in erased positions
too. Inside the body the parameter is a rename of its target's word. An
`at` return is absent from a call's physical values; a `let` binds it
as any return, and the elaborator supplies its word from a non-erased
entry in the same slot, the caller's own binder for the argument the
promise names, which the caller still holds whether or not the call
consumed it. A match's `at` entries are likewise produced by no branch
and read back by the consumer. The promise of an `at` return is
verified where the function or branch returns, by the slots' canonical
identity; a phantom branch under a non-erased scrutinee, an absurd
branch, a refuted branch and an `erased` or `absurd` function are
exempt.

**Writers.** Beside the declaration sites, the facts equating slots
(§35) are minted by: a destructure's cell binder and `else` binder
(with the scrutinee, §23); a `unique` or `many` destructure of a newtype
(its non-erased field with the scrutinee) and a newtype constructor
application (the value with its non-erased argument, §37); a cell
invocation (the value with its cell) and a `cell-write` on a `unique`
cell (the result with its input); `coerce` and `share` (the result with
the source); a forwarding `let` (§19); a `let` of `(slot-of x)` (with
`x`); a call's `at` return and parameter, and a match's `at` entry
(with their targets); `slot-self` (§35); and a forcing unification
(§7) wherever the types it unifies mention slots, `Cell` types and
types indexed by `(Slot)` included, since a slot is an atom of the fact
table. A forced rule between two ordinary atoms, `x is y`, says nothing
about slots, and neither does canonical equality: two separately built
cells with equal contents are `is`-equal and are two blocks. A
non-forcing check, an argument against a parameter, asks only whether
the two slots already coincide. A slot fact ends with the scope that
minted it, as any fact does. A slot may belong to consumed entries;
address equality does not change when contents do.

**Tail and delegate.** The `tail` and `delegate` checks (§19) read the
post-erasure code with `at` entries omitted, as they read coerces as
renamings, so a call whose only non-erased results are `at` returns is
a tail call from a function returning none, and vice versa, the
caller's own promise being verified as always by what follows the
call, which the check requires to be erased.

## 37. Placement: `Cell` and the invocation

A value constructor `C` of a type that is neither `newtype` nor
`extern` has a cell type `(Cell C s1 ... sn)`, a type former (§9) with
one `(Slot)` (§38) per non-erased field of `C`; a constructor with no
non-erased field has an empty cell. Inside an extern function's body
the `extern` mark does not count, so an extern type's constructors have
cells there (§43). A phantom constructor has no cell in any context:
`Cell` on one, and `cell-alloc` of one, are refused. Eligibility is
read off the opened `Matchable` listing the constructor (§8), whose
`newtype` and `extern` marks are structural (§24); an abstract
constructor must be listed by an opened `Matchable`. The newtype
representation (§33) is mandatory for a type marked `newtype` and
forbidden for one that is not.

**Newtypes.** A newtype has no cell, its representation being its
non-erased field's word (§33). A `unique` or `many` destructure of one
puts the field it binds at the scrutinee, and an application of its
constructor is at its non-erased argument. In an erased position the
application is at nothing.

**Obtaining a cell.** `(cell-alloc C)` is an expression yielding a
fresh cell at unique, at no slot, with every slot `vacant-slot` (§35);
`(cell-alloc (C i1 ... in))` lists every non-erased field, each item a
`(Slot)` expression at many or `_` for `vacant-slot`, no partial list.
A destructure at `many` or `unique` yields, through its cell binder
(§23), the cell the constructor occupied, at the scrutinee, each slot
`(slot-of g)` for the field binder `g`.

**Writing.** `(cell-write u (C i1 ... in))` is an expression with one
item per non-erased field, each a `(Slot)` expression at many or `_` to
leave the slot alone; `C` must be the cell's own constructor,
canonically, and the new type's index for each written slot is that
item's value. With `u` a `unique` cell the form takes it at `unique`
and yields the same cell under the new type, at `u`: a physical store
into memory the cell's eventual invocation re-mints, with no usage
accounting of its own. With `u` a variable declared `many`, the form
uses it at many and copies: the result is a fresh block holding the old
words with the written slots replaced, at unique and at nothing, so a
write whose items are all `_` copies a shared block into a unique
cell. A cell given by any other expression is taken at unique.

**Invocation.** A `Cell`-typed head is applicable in §6's tier 1:
`(u a1 ... an)` is a constructor application that mints `(C a1 ... an)`
at `u`, using each argument at the field's multiplicity as
`(C a1 ... an)` would, erased arguments included, which have no slot
and are written as in any constructor application. The value's type is
`C`'s return type instantiated. With `u` at `unique` the invocation
consumes `u`, in a `many` position as in a `unique` one, so a `many`
value may be built this way. With `u` at `many` the invocation uses `u`
at many and mints its value only at `many`, at the cell when every
store is skipped (below) and otherwise as a fresh copy at nothing. In
an erased position nothing is used (§14).

An `(at)` immediately before an argument, as `(subterm p)` sits before
its argument (§56), asserts that the slot already holds that argument,
its variable's slot being the slot's, and the store is skipped; a hard
error otherwise, as for `tail`. The marked argument must be non-erased.
`(at (u a1 ... an))`, wrapping the invocation as `tail` wraps a call,
asserts the same of every non-erased argument and performs nothing; it
is treated as erased by the `tail` and `delegate` checks, as a `coerce`
is, so it may follow a tail call. What is skipped is the stores only:
an invocation with every store skipped still uses each argument at its
field's multiplicity, consuming a unique one, still consumes a unique
`u`, and still mints its value at `u` and its `is` in the fact table.

## 38. `Slot` and `cell-match`

`Slot` is an opaque nullary type, with no constructors and no
`Matchable` (§8); it is not erased by kind, a `(Slot)` binder being
`many`, `unique` or `erased` as declared. A slot's value at runtime is
a word, a pointer or an immediate, and a slot is inert: it may sit in
a field or a list like any other value, and a unique copy of its word
aliases nothing that matters (§13). A signature that speaks of a slot
abstracts over it as a `(Slot)` parameter, `(erased (Slot) s) (unique
(Cell Pair2 s s) u)` saying its two slots hold one thing. Two slots are
equal exactly when they canonicalize to one atom (§35); forcing never
refutes on two slots, `Slot` having no constructors, and nothing relies
on two slots being distinct. A slot says nothing about contents: a
slot's content is not a subterm of it, and `is` alone speaks to
contents.

`cell-match` reads a cell's words out: an expression in two modes,
`(cell-match many u ann (C s1 ... sn) body)` with `u` at `many` and
`(cell-match unique u ann (C s1 ... sn u2) body)` with `u` at `unique`,
`ann` being a return annotation as a `match`'s (§26); an `erased` mode,
and an erased position, are refused (§14). In either mode the `si` are
fresh `many` binders of type `(Slot)`, one per non-erased field, and
one forced unification of `(Cell C s1 ... sn)` against `u`'s type mints
their rules, as entering a branch unifies a scrutinee's type (§7). At
`unique`, `u2` is mandatory: the cell given back, a fresh `unique`
binder `is u` and at `u`, which `body` gets out by returning it into
an entry of `ann` marked `at u`. `body` is not in run position (§27),
wherever the `cell-match` sits. The form decides nothing about a slot:
an `si` is whatever `u`'s type said. What the words are for is a write
into another cell.

## 39. At-functions

A function is an **at-function** when its `def-fns` or `def-unique`
line puts `at` before its name, `(many at unwrap : ...)`, the marks
`absurd`, `extern` and `at` coming before the name in any order. Its
return entries are all erased or `at` (§36); its parameters are not
restricted. Its body **erases to nothing**: after erasure, with `at`
entries omitted, the post-erasure code holds no call that is not
skipped, no constructor application, no allocation, no store and no
copy; renames, constants, loads from a block, a `values`, a match whose
every branch erases to nothing, dispatch included, a nested definition
whose rest erases and absurd code all count as nothing. Calling an
at-function skips its runtime. A function marked `erased` may not be
marked `at`: it is called only where nothing runs, so the mark would
claim nothing. An `absurd` at-function's body is a refutation (§25) and
is not checked for erasing. A function marked both `extern` and `at`
has no FFI implementation: the marks are a promise, and its model is
checked as any at-function's body is.

Being an at-function is not part of the function's type. `def-fns`
mints an erased proof object for it, of type `(AtFn F f)` for a
function `f` of type `F`, when the header claiming `at` is elaborated,
before the block's bodies, so that a call within the block to a
function so marked, its own recursive call included, is skipped; a body
that then fails to erase to nothing is an error. `(at-fn-of f)` fetches
the proof from ambient scope, as `delegate-of` does, and may be
written in a type (§53); `(open-at-fn e)`, a statement, opens a
proof held in `e`. A non-erased call is skipped exactly when an opened
`AtFn` proof names the callee's canonical atom. A skipped call still
carries and checks its `predates` or `subterm` proof (§19), and may not
be marked `tail`, `notail` or `delegate`. Whatever the body an
at-function compiles to a function that does nothing and returns no
word, so a first-class call that reaches it without an opened proof
runs and cannot crash, and the caller reconstructs the `at` returns as
it would anyway.

A call may be asserted to be a call of an at-function by wrapping it,
`(at (f ...))`, as the full-at form wraps a cell invocation (§37). The
assertion is optional and a hard error when it fails, and an error in
an erased position, as the marks of §19 are there.

## 40. At-matches

A match is an **at-match** when its return annotation is written in an
`at` form, a telescope inside it:

```scheme
(match many xs (at (((List (Nat)) ns at xs)))
  ...)
```

Every entry of the annotation is erased or `at`. Each branch's code
must erase to nothing as an at-function's body must (§39), and the
match skips its runtime: its code is empty and the consumer reads its
`at` entries back from their targets (§36). Coverage and the
one-real-branch rule (§21) are checked as for any match. The annotation
inside the `at` is written out; `_` does not stand for it.

## 41. The delegate annotation

A `delegate`-bodied function (§19) may write `at` after its name,
followed by the function it delegates to:

```scheme
(def-fns L $ (many g at f : ...) (delegate (f ...)))
```

The annotation is optional. Where it is written it must be accurate:
the function named must be the one the body's `delegate` call names,
canonically, and a body with no such call is an error.

## 42. Built-ins, the prelude and the FFI

**Built-ins.** Before any file, the scope holds, all erased unless
said otherwise: `Univ` and `Type` (§10); `Level`, `Predates`,
`Subterm` (§18); `Slot`, an opaque nullary type constructor, and
`vacant-slot`, a `many` constant of type `(Slot)` (§38,
§35); `Sharing`, an enum with the `many` nullary constructors `Unique`
and `Shared`, its `Matchable` opened; `Coercible` and `Delegate` (§33);
`AtFn` (§39); and `Special`, an enum with one `many` nullary
constructor per special form, its `Matchable` opened, each form's name
bound `many` to its constructor (§19, §54). `--no-prelude` starts from
these alone.

**The `extern` mark.** A `def-adts` entry or a `def-fns` function may
be marked `extern` (§54). The declaration is then a *model*: for a
type, its constructors and `Matchable` say what its values are and how
they are taken apart, and the FFI supplies the representation with
construction and matching over it; for a function, the body says what
it computes and the FFI supplies an implementation whose non-erased
arity is the model's. An extern type is a type like any other, its
values non-erased and one word (§33); it may be marked `newtype`, the
FFI author then guaranteeing the field representation, and a newtype
may wrap a field of an extern type. An extern function may not have a
`delegate` body. A function marked both `extern` and `at` has no FFI
implementation (§39). An `extern` implementation must agree
with its model: running the models in place of the implementations
gives a program the same values, not the same cost. The prototype's FFI
is a fixed table keyed by the declared name, so an `extern` declaration
of a name the table lacks, or of a name already claimed, is an error;
`--no-extern` runs the models instead, and `dune test` runs every test
both ways. Inside an extern function's body no type counts as marked
`extern` for the purposes of §37 and §43.

**The source prelude** `lib/prelude.sl` is elaborated before a
program's files, its names ordinary and shadowable. Levels in it are
anonymous except `nat-lvl`, `char-lvl`, `str-lvl` and `thunk-lvl`,
which a program proves `Predates` against; a function calling
`nat-add` at level `L` proves `(prove-predates nat-lvl L)`. Its proofs
are erased fields and erased functions, so none is built at runtime.
Its contents:

- **Equality and arithmetic.** `False`; `Eq : (Type A) (A x) (A y)`
  with `Refl`; the relations `Add`, `Lt`, `Double`, `Pow2`, `Mod`,
  `Mul`, every field erased, with `Add` recursing on its first argument
  (`AddZero : (Add (Zero) b b)`); `Dec a b` (`Yes`, `No`) and
  `Cmp T R a b` (`CLt`, `CEq`, `CGt`), the latter parametric in a
  carrier and its strict order with every field erased, so a value is
  its tag alone and two instances differ by a coercion.
- **`Nat`**, the Peano enum of §56 marked `extern`, held by the FFI as
  an arbitrary-precision integer. The extern functions over it return
  their specifications beside their values: `add` (an `Add`), `sub`
  (exact, given `(Lt b (Succ a))`, returning an `Add`), `mul` (a
  `Mul`), `div`, `divmod` and `nat-mod` (given `(Lt (Zero) c)`,
  returning `Mul`, `Add`, `Lt` and `Mod` evidence), `nat-cmp` (a
  `Cmp (Nat) Lt a b`), `lt-dec` (a `Dec`), `shl` and `shr` (through
  `Pow2` and `Mul`), `nat-and`, `nat-or`, `nat-xor` (a `Bitwise`
  relation over `Bit` and `BitOp`), `nat-halve` (a `Half n`, the extern
  enum of `HZ`, `H1`, `H2` by which a `Nat` is walked digit by digit).
  `nat-add`, `nat-mul`, `nat-shl` and `nat-shr` are `delegate`s that
  drop the proofs; `double` and `pow2` are plain source. The lemmas
  over these (`lt-trans`, `add-le-left`, `lt-subterm`, which turns
  `(Lt a b)` into the `Subterm` a decrease wants, and others) are
  erased functions. There is no narrowing function from `Nat` to
  `U8`.
- **`U8`** and **`U62`**, each an enum marked `newtype` with one
  constructor over a `Nat` and an erased `Lt` proof of its bound:

  ```scheme
  (def-adts $ (U8 : -> Type)
    enum newtype
    (many MkU8 : (many (Nat) n) (erased (Lt n u8-modulus) p) -> (U8)))
  ```

  `u8-modulus` is a `many` top-level constant, `(pow2 eight)` bound
  with its `Pow2` proof; `u62-modulus` and `sixty-two` are erased
  top-level bindings, so the prelude never computes 2^62. A `U8` is
  built by `MkU8` with a proof, for a hand-built value by reflection
  (a `comptime-match` on a decided `lt-dec`, §28) and for a computed
  one by matching `lt-dec`, and is taken apart by matching. The `U62`
  operations take `Nat`s with erased proofs that operands and results
  are below the modulus: `u62-add`, `u62-sub`, `u62-mul`, `u62-div`,
  `u62-mod`, `u62-divmod`, `u62-cmp`, `u62-lt-dec`, `u62-shl`,
  `u62-shr`, `u62-and`, `u62-or`, `u62-xor`, `u62-inc`, `u62-dec`,
  each extern and modelled on the `Nat` primitive it corresponds to,
  so the FFI runs each as one machine operation. This rests on the
  host having native integers of at least 63 bits, which the FFI
  checks.
- **Numerals.** `Bin`, bijective base 2 (`BZ`, `B1`, `B2`); the
  relation `Numeral b n`; `bin-to-nat`, returning a `Nat` with its
  `Numeral` proof; `BinSucc`; and the erased lemmas `numeral-zero`,
  `numeral-fn`, `numeral-inj`, `numeral-succ`, `double-fn`,
  `double-inj`, `double-parity` that §45 and §49 rest
  on.
- **Characters and strings.** `Char`, an enum marked `newtype` over
  `U8`; `CharLt`; `char-cmp`, which is `u62-cmp` on the codes by
  `delegate` under coercions; `String`, an enum marked `extern` of
  `SNil` and `SCons` over `Char`, held by the FFI as a byte slice;
  `Append`, `StrLt`, `StrLength`; the extern `append`, `str-cmp`,
  `str-length`, `str-split` (the first `k` characters and the rest,
  given the length), `nat-str` (decimal) and `trim` (whose return
  `is` its argument, its implementation a copy); `str-append`, a
  `delegate` over `append`; `Rope` (`REmpty`, `RStr`, `RCat`,
  `RChar`) with the extern `flatten` returning a `Flat` proof.
- **Containers.** `Unit`, `Bool`, `Maybe`, `Result` (whose `Fail`
  carries a `String`), `List` (§55), `Pair`, `EntryKind` (`IsFile`,
  `IsDir`, `IsOther`, `Missing`), `Change` (`Changed`, `Unchanged`).
- **`thunk` and `unique-thunk`** at `thunk-lvl`: `thunk` takes a value
  and returns a nullary `Fn` holding it, at any type and any level;
  `unique-thunk` the same for a unique value and a `UniqueFn`.
- **`IO`.** `(IO L)`, an enum indexed by a level, read by the driver
  (§27). Every constructor but `Exit`, which carries a `U8` exit code,
  carries its arguments, all `many`, and a continuation
  `(unique (UniqueFn L answer -> (unique (IO L) next)) k)` from the
  request's answer to the next request, so an `IO` value is unique
  throughout and each continuation is applied once:

  | request | arguments | answer |
  |---|---|---|
  | `Step` | | none |
  | `WriteOut`, `WriteErr` | `(String)` | none |
  | `ReadLine` | | `(Maybe (String))` |
  | `ReadRemaining` | | `(String)` |
  | `ReadFile` | path | `(Result (String))` |
  | `WriteFile`, `AppendFile` | path, text | `(Result (Unit))` |
  | `ListDir` | path | `(Result (List (String)))` |
  | `Stat` | path | `(Result (EntryKind))` |
  | `MkDir`, `DeleteFile`, `DeleteDir` | path | `(Result (Change))` |
  | `GetArgs` | | `(List (String))` |
  | `GetEnv` | name | `(Maybe (String))` |
  | `GetEnvs` | | `(List (Pair (String) (String)))` |
  | `GetCwd` | | `(String)` |
  | `ConfineDir` | directory | `(Result (Unit))` |
  | `ConfineOutputBytes` | `(Nat)` | `(Result (Unit))` |

  The driver performs each request, flushing after every write, and
  applies the continuation to the answer; it never recurses, so an
  unbounded interaction is the driver's loop over total functions, and
  there is no `bind`. `ReadLine` strips the newline and answers `None`
  at end of input; `ListDir` sorts and omits `.` and `..`; `MkDir`
  makes one level; `Stat` answers `Missing` for an absent path and
  `Fail` for one it cannot read; the deletes answer `Unchanged` for an
  absent path. README.md describes `ConfineDir`,
  `ConfineOutputBytes` and the command-line flags that stand in for
  them.
- **Arrays**: §44.

## 43. Extern types and functions

A `unique` value of an extern type is the FFI's to mutate in place.
One binding constraint on the FFI author beside §42's: an `at` return
promised by an extern's signature is honoured physically, the model's
body being checked against the promise like any body. Inside an extern
function's body no type counts as marked `extern` for §36's `at` rules
and §37's cells, so a model is written with §37's placement over its
type's own cells; §42's shape check compares the non-erased arities of
the model's constructors with the implementation's. Outside an extern
function's body a `Cell` for an extern type's constructor, and so
`cell-alloc`, `cell-write`, `cell-match` and the invocation on one, is
not allowed: an extern's in-place operations are its own functions,
§44's `array-swap` and kin.

## 44. Arrays

The prelude's array API is length-indexed, elements owned, with
uninitialised slots through a union newtype in the manner of Rust's
`MaybeUninit`, and one extern primitive per element operation modelled
in source over the type's own cells (§43). `_` is §50's.

```scheme
(def-adts $ (Array : (Type A) ((Nat) n) -> Type)
  enum extern
  (many ANil : (erased Type A) -> (Array A (Zero)))
  (many ACons : (erased Type A) (erased (Nat) n)
                (unique A head) (unique (Array A n) rest) ->
     (Array A (Succ n))))

(def-adts $ (MaybeUninit : (Type A) -> Type)
  union newtype
  (many Uninit : (erased Type A) (many (Slot) s) -> (MaybeUninit A))
  (many Init : (erased Type A) (unique A value) -> (MaybeUninit A)))

(def-adts $ (Copy : (Type A) -> Type)
  enum newtype
  (many MkCopy : (erased Type A) (many A v) -> (Copy A)))
```

A `(MaybeUninit A)` is one word, `A`'s own under `Init` and its slot's
under `Uninit`, so an `(Array (MaybeUninit A) n)` is the memory of the
`(Array A n)` it becomes. Reading an `Init` out is a `unique` match
whose `Uninit` branch must be refuted, by a fact or by proof, §21's
one-real-branch rule making that `assume_init` with evidence in place
of `unsafe`. `Copy`'s field being `many`, an element of an
`(Array (Copy A) n)` is read in place. `Immediate A` is an enum with
`ImmU62`, `ImmU8`, `ImmChar`, `ImmBool` and `ImmCopy`, the types whose
values are immediates, which the `-imm` operations take as evidence.

The relations, every field erased, with their index shapes:

- `(AllUninit A n a)` and `(AllInit A n a)` over an
  `(Array (MaybeUninit A) n) a`, each element `(Uninit A vacant-slot)`
  or `(Init A x)` respectively;
- `(ANth A n a i x)`: element `i` of `a` is `x`, carrying the bound so
  that no `Lt` accompanies an index;
- `(ASet A n a i y r)`: `r` is `a` with element `i` set to `y`;
- `(ArrayIsList A xs n a)` and `(ArrayRepeat A n x a)` over an
  `(Array (Copy A) n)`.

The functions, each `extern` with a source model in `lib/prelude.sl`,
the FFI's implementation shedding the arguments the model does not use:

```scheme
array-new : (erased Type A) (subterm many (Nat) n) ->
    (unique (Array (MaybeUninit A) n) a) (erased (AllUninit A n a) p)
array-swap : (erased Type A) (erased (Nat) n) (unique (Array A n) a)
    (subterm many (Nat) i) (unique A x) (erased A m) (erased (ANth A n a i m) nth) ->
    (unique m is old) (unique (Array A n) r at a) (erased (ASet A n a i x r) p)
array-place : (erased Type A) (erased (Nat) n) (unique (Array A n) a)
    (many (Nat) i) (unique A x) (erased A m) (erased (ANth A n a i m) nth) ->
    (unique (Array A n) r at a) (erased (ASet A n a i x r) p)
array-pluck : (erased Type A) (erased (Nat) n) (unique (Array (MaybeUninit A) n) a)
    (subterm many (Nat) i) (erased (MaybeUninit A) m)
    (erased (ANth (MaybeUninit A) n a i m) nth) ->
    (unique m is v) (unique (Array (MaybeUninit A) n) r at a)
    (erased (ASet (MaybeUninit A) n a i (Uninit A (slot-of v)) r) p)
array-unpluck : (erased Type A) (erased (Nat) n) (unique (Array (MaybeUninit A) n) a)
    (subterm many (Nat) i) (unique A x)
    (erased (ANth (MaybeUninit A) n a i (Uninit A (slot-of x))) nth) ->
    (unique (Array (MaybeUninit A) n) r at a)
    (erased (ASet (MaybeUninit A) n a i (Init A x) r) p)
array-get : (erased Type A) (erased (Nat) n) (unique (Array (Copy A) n) a)
    (subterm many (Nat) i) (erased A x)
    (erased (ANth (Copy A) n a i (MkCopy A x)) nth) ->
    (many x is v) (unique a is r at a)
array-get-many : (erased Type A) (erased (Nat) n) (many (Array A n) a)
    (subterm many (Nat) i) (erased A x) (erased (ANth A n a i x) nth) ->
    (many x is v)
array-length : (erased Type A) (erased (Nat) n) (subterm unique (Array A n) a) ->
    (many n is len) (unique a is r at a)
array-length-many : (erased Type A) (erased (Nat) n) (subterm many (Array A n) a) ->
    (many n is len)
list-to-array : (erased Type A) (subterm many (List A) xs) ->
    (erased (Nat) n) (unique (Array (Copy A) n) a) (erased (ArrayIsList A xs n a) p)
array-make : (erased Type A) (subterm many (Nat) n) (many A x) ->
    (unique (Array (Copy A) n) a) (erased (ArrayRepeat A n x a) p)
```

`array-swap-imm` and `array-place-imm` are `array-swap` and
`array-place` with an extra `(erased (Immediate A) imm)` parameter and
a `many` index. `array-pluck` leaves the plucked element's word in the
array under `Uninit`, whose slot is exactly the slot of the value
returned, so the value may be mutated in place and put back by
`array-unpluck`, an `extern at` function (§39) whose call costs
nothing; until then the array may keep the plucked value alive.
Constructing an `ACons` copies its tail, and taking an array apart
through the model's `ACons` view is O(n). `init-witness` is the erased
witness, in §60's shape, that an all-`Init` `(Array (MaybeUninit A) n)`
coerces to an `(Array A n)` at `(Unique)` on both sides; the `coerce`
is written where it is used, a wrapper function extracting to a call
where the inline `coerce` extracts to nothing.

## 45. Literals

Numerals, character literals and string literals are sugar over the
prelude (§42): each stands for values the prelude's own types express,
and a program with literals means what it would with those values
written out.

**Syntax.** A numeral is a digit-only atom with no leading zero, `0`
or `42`; it is never a name, and a binder spelled as a numeral is an
error. A character literal is `#\c` for a single byte `c` that the
word syntax admits, `#\space`, `#\newline`, `#\tab` or `#\xHH`, `HH`
two hexadecimal digits; `#\(`, `#\)` and `#\;` are written in the hex
form. A string literal is `"..."`, starting at the start of a token,
with the escapes `\n`, `\t`, `\"` and `\\`; any other byte, a newline
included, stands for itself.

**Denotation.** A numeral denotes a `Nat` together with an erased
proof `(Numeral b n)` relating it to its spelling `b`, a `Bin` in
bijective base 2: `(BZ)` is zero, `(B1 b)` is 2b+1 and `(B2 b)` is
2b+2, least significant digit outermost, so each number has exactly
one spelling; these are the two values `(bin-to-nat b)` returns. A
character literal denotes a `Char`, the prelude's newtype over `U8`,
itself a newtype over a `Nat` below `u8-modulus`, together with the
erased proof of that bound; any byte is a `Char`. A string literal
denotes a `String`, the prelude's extern enum of `SNil` and `SCons`
over `Char`: its characters consed up, in order.

**Interning.** A literal is interned once per program by what it
denotes: a numeral by its number, a character by its code, a string by
its characters, so `#\a` and `#\x61` are one entry and every
occurrence of `"ab"` is one entry. The entries a literal stands for
enter just before the top-level form that first mentions it, as if by
run-position statements there, and refer to the prelude's own `Nat`,
`Char`, `String` and their constructors whatever names the program has
since shadowed. They are anonymous and outside the scope: nothing can
name, shadow or rebind them, and an occurrence of the literal resolves
to them by the literal itself. A character literal interns its code's
numeral as well.

**What the checker sees.** A numeral is opaque: a `Const` `Nat` with
no `is` rule, beside its erased `Numeral` proof; `3` is not
`(Succ (Succ (Succ (Zero))))`. `(numeral-of lit)` yields a literal's
proof by its spelling, a character literal yielding its code's, and a
string literal or a name being an error; so two spellings equated in a
branch refute it, and `unary` and `distinct` (§49) mint the one rule
or refutation a `Succ` shape or a disjointness needs. A character
literal is transparent down to its opaque `Nat`: its entry carries
`is (MkChar (MkU8 n p))`, `n` the entry of its code's numeral and `p`
the erased proof of its bound, asserted rather than decided, so a
character is its code to the checker. A string literal is opaque: a
`Const` `String` with no rule; `comptime-match` reads its value, and a
match inside a function takes it apart at runtime.

**Printing.** A value of type `Nat`, `Char` or `String` prints as the
literal it reads back from: a numeral in decimal; a character bare
where the word syntax admits it, else `#\space`, `#\newline`, `#\tab`
or `#\xHH`; a string with the four escapes above. Any other value
prints by its type: a tagged enum names its constructor, a type with
exactly one non-phantom constructor names it, a union with more
prints `_`, as does an erased field, a cell, a slot, a function, an
opaque proof and a value whose type has no readable `Matchable` (§8);
a last argument that is itself an application is written with `$`
(§2). Reading a printed literal back yields a literal denoting the same
value.

**Left to the implementation.** How a `Nat`, `Char` or `String` is
held at runtime, and whether a literal's entries are produced by
elaborating statements or minted directly to the same effect. §42's
requirement applies: stripping the extern implementations leaves every
literal meaning the same value.

## 46. `_` as a `def-fns` level

`_` where a `def-fns` or `def-unique` block's level goes (§17, §54)
inserts a `def-lvl` immediately above the block, minting an anonymous
level, and defines the block's functions at it.

## 47. `_` in a match's return annotation

Where a position already fixes the telescope a `match` must produce,
`_` in place of the annotation (§26) reuses it: the final expression
of a function body, of a match or `else` branch body, of a
`cell-match` body (§38), of a `let` whose binders all carry
a type or `is` clause, and an argument position, whose parameter gives
the expectation; the expectation passes down through `values`, `tail`,
`notail`, `delegate` and the `at` wrapper. The reused telescope may
hold no `_` still to infer (§50). `(open-absurd e _)` reuses it the
same way (§8).

## 48. `_` in a call's decrease annotation, and no annotation at all

`(predates _)` reads the callee's level (`level-of`, §54) and the
current level and builds the `Predates` proof relating them.
`(subterm _)` builds the `Subterm` proof for the argument it precedes
against the enclosing subterm argument at the same index. Neither
searches: both fail wherever a proof needs §18's transitivity axioms,
comes from a parameter or a call, or is carried in data, and such a
call writes its proof out (§19).

A call inside a function body may carry no annotation at all. The
elaborator then supplies one: `(predates _)` when the callee's level
and the current level do not canonicalize equal, otherwise
`(subterm _)` before the first `subterm`-marked argument that does not
canonicalize equal to its counterpart among the enclosing function's
`subterm` arguments (§5, §19). The proof is built and checked as if
written. A same-level call whose `subterm` arguments all canonicalize
equal to their counterparts is an error. At the top level a bare call
is what §20 has, and a written annotation is an error.

## 49. `unary` and `distinct`

Both reason about a numeral through the prelude's `Numeral` relation
(§45) rather than about its opaque `Nat`, and both elaborate
into ordinary calls on prelude lemmas, in the prelude's scope so that
no shadowing reaches them; neither carries meaning of its own. Either
takes a numeral or a character literal, a character standing for its
code.

`(unary a b)`, a statement, with `b` below `a`, mints one rule,
`a is (Succ ... b)` under as many successors as separate them: the
one-step proofs from `numeral-succ`, each given the `BinSucc` witness
that one spelling steps to the next, folded together by `eq-cong-succ`
and `eq-trans` and carried out by a single `let-match`. `(unary a)` is
the same with `(Zero)` as the floor, reached through `numeral-zero`.
The literals walked over are not mentioned by the rule and stay
opaque, so `(unary 5 3)` says `5 is (Succ (Succ 3))` and nothing about
`4`. The distance is at most 4096. What the rule buys is a literal
usable where a `Succ` shape is wanted: peeling a `Vec`, or, with each
literal down to zero given its own `unary`, standing as a `Vec`'s
length.

`(distinct a b)`, an expression, yields an erased `(False)` in a
context that has equated the two literals, by a vacuous match on
`numeral-inj`'s `Eq` between their spellings: a `Nat` has one bijective
base-2 spelling, so two spellings for one `Nat` conflict through
`Bin`'s `Matchable`. Its cost is the spellings' depth rather than the
difference between the numbers. Outside such a context, or on two
equal literals, it is an error.

## 50. `_` for an inferred argument

**Where `_` may stand.** As an argument that is erased where it
stands: an erased argument of any application in §6's tier 1, a cell
invocation included, or any argument of a call in an erased position.
Also as an argument of `coercible-wrap`, as the `Sharing` argument of
`coercible-refl`, `coercible-wrap` and `coercible-ctor` (§34),
and in place of any type, a whole binder type or annotation entry
included. Each such `_` is a fresh unification variable, a **meta**.
`_` cannot stand for an argument of a parameter written `at`
(§36). `_` as a `cell-alloc` or `cell-write` item (§37) and `_` as a binder (§1) are separate forms, not metas.

**Expectation.** Some positions expect a telescope, each entry a type
or an `is` term, which helps solve the metas inside them: a function
body (its returns), a match branch (its annotation), a `let` whose
binders all carry a type or `is` clause, and an argument (its
parameter, given the arguments before it). The expectation passes down
through `values`, `tail`, `notail`, `delegate` and `at`, and never
passes up.

**Boundaries.** A meta never reaches the fact table. Every form that
records a fact is a *boundary*, and a meta still unsolved at a
boundary is an error. The boundaries are a call's `)`, a `let`
binding, a scrutinee, a match annotation, a body's results, a special
form's operands, run position, and each telescope entry as it is
bound. A constructor application and a cell invocation are not
boundaries: their metas may stay open for the surrounding form to
solve, so `(f _ (Nil _) xs)` is accepted while `(len _ (Nil _))` is
refused at the call's `)`. A `_` in a signature is accepted when its
own entry solves it.

**Solving.** By unification only, with no search and no computation.
Boundaries settle inside out: everything within one boundary is solved
together, and a boundary nested inside it closes first, using only
what is known at that point. A match's annotation is settled before
its branches, so no meta crosses into a branch. A bare `_` as a whole
annotation entry or binder type is a meta of type `Type`; `_` is not
accepted as an entry of a `values` or as the scrutinee of a
`let-match`. After the arguments are solved, §48's decrease annotation
is inferred.

## 51. Refuting in an absurd body

In the body of an `absurd` function or of an absurd-by-proof branch
(§21, §25), after its statements, the final expression may *refute*
the facts in force instead of producing a value of an empty type.
Those statements may include a `let-match`, as in
`(absurd (Zero) (let-match erased le (LtS x y l1)) l1)`. A refutation
produces no value and binds nothing. It is one of:

- a `match` annotated `_`, erased, which refutes when every
  constructor is refuted: each of its branches is `(absurd C)` or
  absurd by proof, whose body refutes in turn, and it has no `else`;
- `(open-absurd e _)`, which refutes when the open contradicts (§8);
- any other expression `e`, elaborated as an erased value and accepted
  when `(match erased e _)` with no branches would refute, so `(False)`
  works, and so does `(Lt a (Zero))`. One match deep, no search.

## 52. `let-match` with branches

`(let-match m s (C f ...) branch ...)` takes §21's four branch kinds,
written as in a `match`, and `(C f ...)` binds outward as before. With
more than one real branch, the pattern included, it elaborates to
`(match m s A ((C f ...) rest ...) branch ...)`, with `A` the
containing expression's annotation and `rest ...` what follows. With
one, it stays a statement and its absurd branches just refute.
Coverage replaces "exactly one survives" (§27). Any branch not headed
by `absurd`, an `else` included, counts as real here.

More than one real branch requires a function body, a `match` or
`else` branch body, or a `cell-match` body (§38). A `let`
right-hand side, run position and absurd bodies (§51) admit absurd
branches only.

## 53. Fetch forms in a type

`(level-of f)`, `(matchable-of T)`, `(delegate-of g)`,
`(numeral-of n)`, `(slot-of x)` and `(at-fn-of f)` may be written in a
type or an `is` expression, where each elaborates to the entry it
yields as an expression, a variable reference, which is §9's first
production. It is read where it is written, against the facts in force
there. A `def-fns` block's own names are in scope in its bodies but
not in its signatures, so a signature cannot name the block's level
through one of them. `coercible-of` is not a fetch form, minting a
fresh proof at each use, and may not appear in a type.

## 54. Special form registry

Every special form, as `Special`'s constructors (§19), grouped as §27
splits them. Each is specified where the entry points.

**Statements** (§27):

- `let`: zero or more binders, bracketed, then statements, then the
  final expression (§19, §26, §12). Zero binders runs the right-hand
  side for its effect on uniques (§15).
- `def-lvl`: mints a fresh `Level` (§18).
- `def-fns`: one or more mutually recursive functions at one level,
  written on the form, each with its own `erased`/`many` marker (§14),
  and optionally `absurd` (§25), `extern` (§42), `at` (§39)
  or `at g` (§41). May be nested in a body. Mints a
  `Delegate` proof for each `delegate`-bodied function (§33) and an
  `AtFn` proof for each at-function.
- `def-unique`: one function of `UniqueFn` type (§32).
- `def-adts`: one or more mutually recursive ADTs, each `enum` or
  `union` and optionally `newtype` and `extern`; mints and opens each
  type's `Matchable` (§21, §8, §33, §42).
- `comptime-match`: compile-time discriminant assertion on a `Const`
  (§28); confined to run position.
- `let-match`: destructures a scrutinee of which exactly one
  constructor survives refutation, binding outward (§27, §52).
- `open-adt`: opens a `Matchable` (§8).
- `slot-self`: makes a `(Slot)` variable its own slot (§35).
- `open-at-fn`: opens an `AtFn` proof (§39).
- `unary`: rewrites a numeral to successor form (§49).
- `dump-context`: stops elaboration with a report of the context
  (README.md); also an expression and a type.

**Type formers** (§9, production 4):

- `Fn` and `UniqueFn` (§11, §32), `TyCtor`, `ValCtor` (§11),
  `Matchable` (§24), `Cell` (§37).

**Expressions:**

- `match` (§26, §21, §23, §40), `values` (§26, §27).
- function call, constructor application and cell invocation (§6, §19,
  §37): a call carries `(predates p)` after the callee or
  `(subterm p)` before the decreasing argument, so its item count
  exceeds the callee's arity.
- `coerce` (§33), `share` (§16), `cell-alloc`, `cell-write`,
  `cell-match` (§37, §38), `open-absurd` (§8), `distinct`
  (§49).
- the `at` wrapper around a cell invocation or an at-function call
  (§37, §39).

**Proof forms**, all erased (§14):

- `prove-subterm`, `prove-predates`, `predates-trans`, `subterm-trans`,
  `predates-subterm` (§18).
- `coercible-refl`, `coercible-sym`, `coercible-trans`,
  `coercible-share`, `coercible-wrap`, `coercible-ctor`, `coercible-of`
  (§33).

**Fetch forms**, which may also be written inside a type or `is`
expression (§53):

- `level-of` (§17), `matchable-of` (§8), `delegate-of` (§33),
  `numeral-of` (§45), `slot-of`, `at-fn-of` (§35,
  §39).

**Annotation tokens**, which annotate a form rather than heading a
list:

- `erased`, `many`, `unique`: the multiplicities (§13).
- `:`: separates a name from its signature at a declaration (§3,
  §55). `is`: separates an `is` expression from the name it introduces
  (§12, §3). `->`: separates parameters from returns (§11).
- `subterm`: marks a parameter as in the lexicographic order (§17, §19,
  §3) and heads the call annotation naming the decreasing argument;
  `predates`: heads the call annotation carrying a lower-level call's
  proof (§19).
- `enum`, `union`: the discriminant's erasure (§21); `newtype` (§33),
  `extern` (§42): marks after it; `absurd`: on a `def-fns` line (§25)
  or before a branch's pattern (§21).
- `tail`, `notail`, `delegate`: calling-convention marks wrapping a
  call (§19).
- `else`: heads the branch standing for every unlisted constructor
  (§21).
- `at`: on a telescope entry, before an argument of a cell invocation,
  wrapping an invocation or a call, around a match annotation, before
  a `def-fns` name, and after one (§36, §37, §39, §40, §41).

## 55. Worked example: `List`

```scheme
(def-adts
  ((List : (Type A) -> Type)
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) rest) ->
       (List A))))
```

- `List : (Type A) -> Type` is the type constructor's signature; no
  level (§17).
- `enum`: `List` is walked over at runtime, so it carries a tag (§21).
- `Nil` and `Cons` each redeclare `A`; no telescope is shared at the
  head (§21).
- `(erased Type A)`: expression before name (§3), erased because `A`
  is a type (§21).
- `many` on both constructor lines: neither is phantom (§21); the
  marker is what the type's `Matchable` records (§24).
- `(List A)` on both returns: the saturated application of the type
  constructor each is declared under (§21).

The prelude declares `List` exactly so (§42); `tests/list.sl`
redeclares it.

## 56. Worked example: `length`

```scheme
(def-adts $ (Nat : -> Type)
  enum
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-lvl L)

(def-fns L $ (many length : (erased Type A) (subterm many (List A) xs) ->
    (many (Nat) n))
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl)
      (let ((erased p)) (prove-subterm tl xs))
      (Succ $ length A (subterm p) tl))))
```

- `Nat : -> Type` is a nullary type constructor, so the type is
  `(Nat)`, the shape of `Univ` and `Type` in §10.
- `(def-lvl L)` mints the level `length` is defined at (§18).
- `many length` is the function's own multiplicity (§14).
- `(match many xs (((Nat) r)) ...)`: the scrutinee's multiplicity
  first, then the annotation as one bracketed telescope of types (§26).
- Every field gets a binder, the erased `a` included (§21).
- `(prove-subterm tl xs)` mints the proof (§18): entering the `Cons`
  branch forces `xs is (Cons A hd tl)` (§7), so `tl` canonicalizes to
  a strict subtree of `xs`.
- `(subterm p)` precedes the decreasing argument (§19): position names
  the argument, so nothing can shadow it.

## 57. Worked example: level-polymorphic `map`

`map` calls the function it is given, so by §17 it sits at a level
strictly above that function's, and the call wants a `Predates` proof.
The proof cannot be minted inside `map`: `f` is `map`'s own parameter,
so it was not in scope when `map`'s level was minted (§18). The relation
is established where the level is minted, so `map` is produced by a
factory.

```scheme
(def-lvl F)

(def-fns F $ (many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped))
  (def-lvl L)
  (let ((erased pml)) (prove-predates M L))
  (def-fns L $ (many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys))
    (match many xs (((List B) r))
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (let ((erased p)) (prove-subterm tl xs))
        (Cons B (f (predates pml) hd) $ map A B f (subterm p) tl))))
  (values L map))
```

```scheme
(def-lvl I)

(def-fns I $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(let ((erased ML) (many map-nat)) (map-factory I))

(let ((many xs)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(map-nat (Nat) (Nat) inc xs)
```

- The factory mints the level and returns it; naming `L` in the return
  telescope lets the second return's type mention it (§26).
- `prove-predates` discharges inside the factory, `M` being in scope
  when `def-lvl L` runs (§18).
- `A` and `B` stay parameters of `map`: types carry no level.
- `(f (predates pml) hd)` is the lower-level call and
  `(map A B f (subterm p) tl)` the same-level recursion (§19).
- The usage is statements in run position, each elaborated and run in
  turn (§27, §20): calls need no proofs, and every binder is minted
  `Const` (§29). `ML` and `map-nat` match the `erased`, `many` of the
  factory's return telescope; `xs` is a constructor application bound
  `many`.

§58 is the same program with sugar.

## 58. Worked example: `map` with sugar

§57's program with `_` levels and annotations, inferred arguments and
bare calls:

```scheme
(def-fns _ $ (many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped))
  (def-fns _ $ (many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys))
    (match many xs _
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (Cons B (f hd) $ map A B f tl))))
  (values (level-of map) map))
```

```scheme
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(let ((erased ML) (many map-nat)) (map-factory (level-of inc)))

(let ((many xs)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(map-nat (Nat) (Nat) inc xs)
```

## 59. Worked example: absurd `explode`

```scheme
(def-adts $ (False : -> Type)
  enum)

(def-lvl X)

(def-fns X $ (many absurd explode : (erased Type A) (many (False) f) ->
    (many A a))
  f)
```

- `False` has no constructors (§17); its `Matchable` is
  `(Matchable enum False)`, which is how §25 reads the type as empty.
- `many absurd explode`: the multiplicity (§14) and the `absurd` token
  (§25) share the line with the name.
- The body is `f`, a single value of `(False)`, where the signature
  promises `(many A a)`; marked `absurd`, that is accepted. It compiles
  to no code, and holding it at `many` is fine: the pointer is never
  followed.

`tests/absurd.sl` is this program.

## 60. Worked example: unwrapping a list with `coerce`

```scheme
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl U)

(def-fns U $ (erased unwrap-witness : (subterm many (List (Meters)) ms) ->
    (erased (List (Nat)) ns)
    (erased (Coercible (Shared) (List (Meters)) ms (Shared) (List (Nat)) ns) p))
  (match erased ms (((List (Nat)) ns)
                    ((Coercible (Shared) (List (Meters)) ms (Shared) (List (Nat)) ns) p))
    ((Nil a) (values (Nil (Nat)) (coercible-ctor (Shared) Nil (Meters) (Nat))))
    ((Cons a m tl)
      (let ((erased sp)) (prove-subterm tl ms))
      (let ((erased ws) (erased q)) (unwrap-witness (subterm sp) tl))
      (match erased m (((List (Nat)) ns)
                       ((Coercible (Shared) (List (Meters)) ms (Shared) (List (Nat)) ns) p))
        ((MkMeters n)
          (values (Cons (Nat) n ws)
                  (coercible-ctor (Shared) Cons (Meters) (Nat)
                    (coercible-sym (coercible-wrap (Shared) MkMeters n))
                    q)))))))

(def-lvl V)

(let ((erased puv)) (prove-predates U V))

(def-fns V $ (many unwrap-all : (many (List (Meters)) ms) ->
    (many (List (Nat)) ns))
  (let ((erased ws) (erased p)) (unwrap-witness (predates puv) ms))
  (coerce ms p))
```

- `Meters` is marked `newtype`: one non-phantom constructor with one
  non-erased field, so §33 makes a `(Meters)` exactly a `(Nat)` at
  runtime, and a `(List (Meters))` exactly a `(List (Nat))`.
  `unwrap-all` is the zero-cost witness of that.
- `unwrap-witness` is `erased` (§14): it never runs, but it is a
  function like any other, with a level, a `subterm` parameter and §17's
  termination check on the recursive call.
- Its two returns form a telescope (§26): the witness list `ns`, then
  the proof whose type names it. Both matches carry that telescope as
  their annotation, types only.
- `(coercible-ctor (Shared) Nil (Meters) (Nat))`: `Nil`'s one erased
  field takes a source and a target value (§33).
- In the `Cons` branch `ms is (Cons a m tl)` is forced (§7), and in
  the inner `MkMeters` branch `m is (MkMeters n)`. So
  `(coercible-wrap (Shared) MkMeters n)` relates `n` to `m`, its
  `coercible-sym` is the head proof, and the `coercible-ctor` for
  `Cons` takes source and target `A`, that head proof and the recursive
  tail proof `q`, producing a proof whose source canonicalizes to `ms`.
- Both matches are `erased`: the whole body is an erased position, and
  §21's one-real-branch rule never applies.
- `unwrap-all` calls `unwrap-witness` from a higher level, with the
  `Predates` proof minted in run position after `def-lvl V` (§18, §19).
  The `let`'s binders are all `erased`, so the call is an erased
  position (§14) and never runs. `(coerce ms p)` is the only runtime
  content, and it erases to nothing.

A `delegate` proof, reusing `inc` from §57 at level `I`:

```scheme
(let ((erased piv)) (prove-predates I V))

(def-fns V $ (many inc-noted : (many (Nat) n) (erased (Nat) note) ->
    (many (Nat) m))
  (delegate (inc (predates piv) n)))

(let ((erased ig)) (coercible-of (delegate-of inc-noted)))
```

- After erasure `inc-noted`'s body is nothing but the call to `inc`
  (§19), so `def-fns` mints the `Delegate` proof, `delegate-of` fetches
  it and `coercible-of` reads the `Coercible` off it:
  `ig : (Coercible (Shared) (Fn V ...) inc-noted (Shared) (Fn I ...) inc)`.
  `(coerce inc-noted ig)` is then `inc`'s own pointer.

`tests/coerce.sl` is this program.

## 61. Worked example: tail call modulo cons

`append` copying `xs` onto `ys` in destination-passing style, over the
prelude's `List` (§55), whose fields are both `many`. The helper takes
a vacant cell and the head that belongs in it, and promises its result
at the cell:

```scheme
(def-fns _ $ (many append-into : (erased Type A)
    (unique (Cell Cons vacant-slot vacant-slot) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell))
  (let-match many xs (Cons _ hd tl) ((Nil _) (cell _ h ys)))
  (let ((unique next)) (cell-alloc Cons))
  (let ((unique cell2)) (cell-write cell (Cons (slot-of h) (slot-of next))))
  (let ((many r2)) (tail (append-into _ next hd tl ys)))
  (at (cell2 _ h r2)))

(def-fns _ $ (many append : (erased Type A) (many (List A) xs) (many (List A) ys) ->
    (many (List A) r))
  (let-match many xs (Cons _ hd tl) ((Nil _) ys))
  (let ((unique cell)) (cell-alloc Cons))
  (append-into _ cell hd tl ys))
```

- In the `Nil` branch the invocation mints `(Cons A h ys)` at `cell`,
  `h` and `ys` at many into the many-labelled fields (§22), the cell
  consumed and the value many, as an invocation in a many position
  builds (§37); the result is at `cell`, the promise.
- In the `Cons` case the write stores `h`'s word and the pointer to the
  fresh `next` into `cell`, two stores, mentioning both through
  `slot-of`, which is no use (§15), so `next` is still live for the
  call; the call consumes `next` and returns `r2` at `next`, physically
  nothing.
- The call is a tail call: with `at` returns dropped the callee
  returns nothing and so does this function, and what follows the call
  is erased, the invocation being full-at since `h` is in the first
  slot and `r2` is at `next`, which the second slot holds. Its result
  is at `cell2`, at `cell`. Leaving `h` to the invocation instead of
  the write would put a store after the call and the claim would fail.
- Each of `cell`, `cell2` and `next` is used once at unique; `h`, `r2`
  and the result are many, the tail being labelled `many`, which is
  why the helper returns `many` and needs no `share`. Per element, one
  allocation and two stores, in constant stack.

`tests/cell_append.sl` is this program.
