# Sleight

This file is the specification of Sleight, the language. OPEN.md lists the open
questions. MANUAL.md describes the implementations and their command
lines; README.md introduces the repository. EXAMPLES.md indexes the tests. The code and the other files cite
sections of this file by number.

The language has three aims besides its design. It matches the dynamism
of Kernel, John Shutt's Lisp dialect, while still compiling cleanly
with static types; the constant-knownness of a head (§6) is what
reconciles the two. It supports LLMs writing code in it, which is
explicitly one purpose of the language and its tooling. And it lets a
certified program be written so that it could run fast: what a program
proves is erased (§13 to §16), a `unique` binder is the only reference
to its value, so the value can be updated in place rather than copied
(§13, §15), and nothing in the language stops a program's runtime part
from being shaped to compile to tight machine code. This is an aim for
the language, not for the implementations, whose own speed, and the
speed of the code they produce, are not aims.

- Syntax: §1 to §4.
- The scope environment and the fact table: §5 to §8.
- Types: §9 to §12.
- Multiplicities and erasure: §13 to §16.
- Termination: §17 to §20.
- Data types and matching: §21 to §25.
- Expressions, statements and compile time: §26 to §32.
- Coercion: §33, §34.
- Slots, `at` and cells: §35 to §41, and §66 to §70.
- The prelude, the FFI and literals: §42 to §45.
- Sugar, provisional: §46 to §53.
- The special-form registry: §54.
- Worked examples: §55 to §61.
- Macros: §62 to §65.
- Goals: §71.

## 1. Syntax

The syntax is s-expressions. A file is a sequence of statements,
optionally followed by one expression (§27). A `;` starts a comment that
runs to the end of the line. A `;!` starts a pragma (§4). An atom is any
run of characters other than whitespace, parentheses and `;`. A token
that begins with `"` is a string literal. Atoms made only of digits, and
atoms of the form `#\c`, are numeral and character literals (§45). A
token `#"..."` is a raw name: the string's bytes, read as a string
literal (§45), whatever they are. It is always a name, so `#"_"`,
`#"45"` and `#""` are names, and `#"let"` is `let`.

`_` as a binder name creates an anonymous entry. This applies wherever
a binder is written: a `let` binder, a telescope entry, a pattern
field, a cell binder, a `def-lvl`, or the name defined by `def-fns`,
`def-unique` or `def-adts`. `_` has other meanings in other places,
each a separate form: an inferred argument or type (§50), an
annotation (§47), a `def-fns` level (§46), and a cell item (§37). A
name written without `#"` may not begin with `__`; such a name is
written raw. Those spellings are reserved for the compilers' messages,
which write a name that does not read back plain as a raw name.

Every built-in name and built-in syntax is ASCII. The multiplicities are
written as the words `erased`, `many` and `unique`, not as Idris's `0`
and `ω`.

## 2. `$`

`$` opens a list form exactly as `(` does, but it does not consume the
`)` that ends it. The form reads items until the terminator of the
enclosing form, and leaves that terminator for the enclosing form to
consume. If there is no enclosing form, the missing `)` is an error.
Only a bare `$` token is special; `foo$bar` is an ordinary atom.

When a form carries a telescope and something else, the telescope is
bracketed: the binders of a `let`, and the signature of a `def-fns`,
`def-unique` or `def-adts` up to and including its returns. What
follows the bracket is the body. A value constructor has no body, so
its clause is that bracket alone.

## 3. Telescope entries: type before name

A typed telescope entry is written `([subterm] mult Type name [at v])`:
the type comes before the name. An entry may only depend on the entries
before it, so everything a type can refer to is to its left, and the
name, which nothing can yet refer to, comes last. A `TyCtor` entry
omits the multiplicity (§11). An `is` entry is written
`(mult expr is name [at v])` for the same reason. `at v` is described
in §36.

A `$` cannot end such an entry when a name follows, because `$` reads
up to the enclosing form's terminator. Plain parentheses are used
there.

`let` sees backwards only: a binding never sees itself or anything
declared after it. All recursion, including mutual recursion, goes
through `def-fns` and `def-adts`.

Examples. The type of `reify-add`:

```scheme
(Fn L (many (Nat) a b) (erased (Nat) c) (erased (Add a b c) p) ->
   (many c is d))
```

The type of `divmod`:

```scheme
(Fn L (subterm many (Nat) n) (many (Nat) d) -> (many (Nat) q) (many (Nat) r))
```

The type constructor of a length-indexed vector. Its entries have no
multiplicities:

```scheme
(TyCtor (Type A) ((Nat) n) -> Type)
```

A value constructor whose runtime field is fixed by `is`. `a` and `b`
are erased indices. `lst` is stored at runtime and is definitionally
the two-element list built from them, so it serves both as data and in
type position:

```scheme
(ValCtor (erased (Nat) a) (erased (Nat) b)
   (many (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat)) is lst) -> (Two a b))
```

## 4. User-defined warnings and errors

A pragma line `;! warn NAME message` names a type constructor, a value
constructor or a function, meaning an entry of `Fn` or `UniqueFn`
type, that is in scope, resolved through its aliases, and gives a
message. After it, every non-erased application of that constructor
warns with the message, and so does every non-erased `match`,
`let-match` or `comptime-match` on that type, and every non-erased call
of that function. Each warning carries a note pointing at the pragma.
No warning is given inside the body of an `extern` function or an
at-function (§39), or inside a branch of an at-match (§40), and none is
given for an at-match itself or for a skipped call (§39). A `;! warn`
must be written between top-level forms. It is an error to write a
second `;! warn` for the same name, to name something not in scope or
neither a constructor nor a function, or to omit the message.

`;! suppress warn NAME` silences these warnings for `NAME` until the
matching `;! restore warn NAME`, or to the end of the file if there is
none. The pair may appear at any nesting depth. Text after the name is
ignored. A region that silences nothing produces a warning. A second
`suppress` for a name that is already open, or a `restore` with no open
`suppress`, is an error.

`;! file "name"` ends the file being read and starts one named `name`.
Each file a source holds this way means what it would as a separate
file of the unit (§27), its lines counted from 1 after the pragma,
except that its name grants nothing to `read-file` (§65). Its one
argument is a non-empty string literal; anything else is an error. A
position rebuilt from a `Pos` belongs to the place the `Pos` names.

Pragmas are read from source text alone. Nothing a macro returns is a
pragma, and no parser from text to `Raw` may process one.

Any other word after `;!` is an error.

Warnings go to standard error and do not stop elaboration.
`--warnings-as-errors` makes a run that warns fail; a silenced warning
does not count (MANUAL.md).

`(compile-error m)` and `(compile-warn m)` report an error or a warning
with the text of `m` at the form's position. `m` is read as a head is
(§6): it is elaborated, and its result must be a `Settled`,
non-erased entry whose minted type canonicalizes to the prelude's
`String` against the facts of the innermost enclosing run position.
`compile-error` may stand anywhere a form may; `compile-warn` is a
statement. Either fires wherever it is elaborated, erased code
included. Neither form is subject to `;! suppress`.

## 5. Scope environment

The scope environment is a list of entries. Shadowing is allowed. An
entry has:

- a **name**, which is optional: anonymous entries exist;
- a **state**, `Settled` or `Hypothetical` (§28, §29). An entry
  becomes `Settled` only at the sites §29 lists, and every `Settled`
  entry holds outside every hypothesis, which is what lets the
  compiler rely on it at elaboration. Every other entry is
  `Hypothetical`, whether or not it also holds;
- a **stored value**, present only in state `Settled`. For an erased
  entry the stored value is a token that records that the value exists;
  it is not data;
- a **minted type**, present only in state `Settled`: the type the entry
  had when it became `Settled`, which special-form dispatch reads (§6,
  §29);
- a **minted `is`**, present only in state `Settled`: the term the entry
  was when it became `Settled`, which a macro's handle denotes (§29,
  §64);
- a **multiplicity** (§13), declared at the binder or fixed by the kind
  of entry (§14);
- a **level-mint marker**, set on an entry introduced by `def-lvl`
  (§18);
- an **introduction order**, which orders `Predates` (§18) and decides
  what a `delegate` may name (§19); a forwarding `let` takes it over
  from a source that has one (§19), and a literal's entries have none
  (§45);
- an **automatic slot** (§35).

An entry's **type** and its **`is` rule** (§12) are stored in the fact
table (§7), not on the entry, unlike its minted type and minted `is`.
Each is a tree whose
leaves refer to entries (§9); an `is` tree may refer to its own entry.
Both depend on the scope: an entry's type may be refined inside a match
branch and revert when the branch ends.

Every application of a type constructor or value constructor has an
entry of its own, usually anonymous, whose `is` rule is that
application. The reference graph of the fact table is therefore the
whole structure of every term in §9's grammar. There is no separate
term structure next to it.

Elaboration also keeps two pieces of ambient context. The **current
level** is the level of the function body being elaborated, or a
marker for the file's top level, which is above every level (§20). The
**enclosing subterm arguments** are the entries bound by the enclosing
function's `subterm`-marked parameters, in declaration order (§19).

## 6. Head dispatch

Macros and special forms are first-class values. To invoke one, rather
than merely hold it, the head of the form must be constant-known at
that point. A name bound inside a function body or a match branch is
`Hypothetical`. A function is `Hypothetical` in every body of its own `def-fns` block
and in the signatures that follow its own in that block (§53). The
binders of a statement in run position (§27) are `Settled` in
the code after it, and so is the result of every form in run
position, from the moment the form is elaborated (§29).

A list is elaborated according to its head:

1. The head is elaborated first. If its result is a `Settled`,
   non-erased entry whose minted type canonicalizes to `(Special)`
   against the facts of the innermost enclosing run position (§27),
   the list is the special form named by that entry's stored value. A
   name or a literal is its own entry. A head that is a form is
   `Settled` in run position, since it runs as soon as it is
   elaborated (§29); inside a body it is `Settled` only when it
   forwards a `Settled` entry, as `(share n)` does (§16). In a type,
   no head is computed (§9). An erased
   `Settled` holds only the token of §5 and has no value to dispatch
   on. A head that is not dispatched is elaborated only once, and is
   the callee of item 2. Annotation tokens (§54) are not heads, and are
   recognised only where written as a name or `(share n)`.
2. Otherwise, if the head's type is a type constructor, a value
   constructor, an `Fn`, a `UniqueFn` or a `Cell` (§32, §37), the list
   is an application. This needs no constant-knownness: each of these
   can be applied through a first-class value.
3. Otherwise the list is an error.

## 7. The fact table and forced unification

The scope environment (§5) and one rewrite database, the **fact
table**, are the only sources of truth for checking. The table maps
entries to a type and an optional rewrite rule from an atom to an
expression. Types are kept in the table because entering a branch
refines the scrutinee's type as well as its structure.

Facts are read canonically: when a rule or type is read, it is
canonicalized to a fixed point against the rules in force. The table
is written by declaration sites (`is` declarations, signatures,
telescopes, `let` inference), by run-position forms when they run
(§29), by `comptime-match` verifications against a stored value, by
opens (§8), and by forced unifications when a branch is entered
(below). A branch-forced rule is recorded even when it rewrites a
`Settled` entry; the rule is justified by the branch running.

**A fact ends with the scope it was created in.** A branch-forced rule
ends with its branch, whatever entries it mentions. For example,
matching a `(Nat)` against `Zero` forces `n is (Zero)`; this names no
branch-local entry and is still gone after the match. A fact can only
mention entries that are in scope where it is created, so a fact never
outlives an entry it mentions. Only run-position forms run at
compile time (§27, §29), and their match branches are gated like any
other. Special-form dispatch is decided at compile time anywhere, so
it reads the table as it stood at the innermost enclosing run position
(§6). One table is therefore enough. Compile-time effects in unreachable code
still happen. A fact verified by a `comptime-match` in run position
holds afterwards, so a later match on the same `Settled` finds the
contradicting branches refuted.

Before an occurs check, and before recursing into either side of an
equation, both sides are canonicalized. Canonicalization never reads a
`Settled` entry's stored value. It is driven by `is` facts alone, in the
same way for `Settled` and `Hypothetical`.

**Forcing.** Entering a branch equates the scrutinee with the branch's
constructor applied to its fresh fields, and equates the scrutinee's
type with the type of that application. This is not a check. It adds
`is` facts wherever that is not already provably impossible, recursing
through matching non-atom arguments. A fresh atom, or an atom with no
conflicting fact, always unifies. When two atoms are unified, the newer
becomes an alias of the older, and whatever the two must share is then
unified as well: their signatures, if both are type or value
constructors, and the opened `Matchable`s they head, if both are type
constructors (§8). A literal's entry (§45) is older than every other
entry, and of two literals the one interned first is the older. The
forced facts hold while the branch is checked.
`match` keeps them inside the branch. `comptime-match` exports them
after verifying the constructor against the stored value. `let-match`
exports them after refuting every other constructor (§27). Facts added
while testing a constructor do not escape the test.

Forcing fails, and so refutes the branch, in exactly three cases:

1. An atom `x` is equated with an expression that contains `x`, after
   existing atom-to-atom aliases are resolved. (`x = x` is a no-op.)
2. Two value constructors listed by one opened `Matchable` are equated;
   or two atoms whose signatures cannot be unified are equated; or two
   atoms are equated whose opened objects would then name one thing and
   cannot be unified (the invariant of §8). A declared name has no
   distinctness of its own: two type constructors with identical
   signatures and no opened `Matchable` unify.
3. A variable is equated with an expression that mentions a binder of
   the telescope being compared. Example: `k` against `x` when
   `(Fn L ((Nat) x) -> (k is y))` meets `(Fn L ((Nat) x) -> (x is y))`.
   A rule maps an atom to a closed expression, so no rule could make
   the two sides identical. The language has no eta rule.

## 8. `Matchable` and constructor disjointness

Constructors are first class (§24), so two constructor-valued
variables are not known to be distinct just because they are
syntactically distinct. A list of known-disjoint constructors kept in
the scope environment would not be first class; a `Matchable` is that
list as first-class data. When two constructor-headed terms meet, there
is no third, indeterminate outcome: forcing either succeeds and adds
facts, or contradicts by the rules of §7. Two atoms conflict only when
one opened `Matchable` lists both, or their signatures cannot unify, or
the opened objects that would then name one thing cannot unify.
Nothing is refuted on the identity of a name.

A `Matchable` does nothing just by being in scope. Nothing consults it
until it is **opened**. Two forms open one. Each takes an expression of
`Matchable` type and reads its type, not its value:

- `(open-adt m e)` is a statement (§27). It is an anonymous `let` of
  `e` at multiplicity `m`, checked like a `let` binder (§19), followed
  by the open of that binder. The open asserts that the listed
  constructors are pairwise distinct after canonicalization and that
  the invariant below holds, adding whatever facts that takes.
  Otherwise it is an error. The open lasts as long as the entries
  created next to it: a match branch discards it with the branch's
  facts, and a `let`'s right-hand side keeps it (§27).
- `(open-absurd e ann)` is an expression. Its size and result types are
  given by `ann`, a return telescope like a `match`'s, or `_` for the
  enclosing one (§26). It takes `e` at `erased`, records nothing, adds
  nothing, and requires the open to *fail*: it uses a contradiction
  between the facts in force and the `Matchable`, in the same way an
  absurd branch uses one with a pattern (§21).

**The invariant.** At most one opened `Matchable` names a given type
constructor or value constructor, canonically. Whenever two opened
`Matchable`s would name one thing, whether at an open or when a forcing
(§7) equates two type constructors or two value constructors, they are
unified by forcing. The unification goes through the `enum`/`union`
tag, the marks, the number of constructors, each constructor's
multiplicity marker, the constructors and the type constructor, and so
their signatures. Two that cannot be unified contradict. Two that can
be unified become one; the entry kept is the one the elaborator can
best read, which is a `Settled` with the type's own declaration if there
is one, and otherwise one that is non-erased and still bound. So two
opened `Matchable`s for one type are never ambiguous: either they are
one, or they contradict. The facts this adds are justified by
`def-adts` being the only place a `Matchable` is created: two that name
one constructor describe one declaration.

**What requires an open.** The disjointness rule of §7; `match`,
`let-match` and `comptime-match`; the emptiness check of §25 and §51;
`matchable-of`, which finds only an opened `Matchable`;
`coercible-wrap`, which reads the `newtype` mark from the opened
`Matchable` that lists its constructor (§33); and the cell rules of
§37. `delegate-of` and `at-fn-of` fetch from the ambient scope instead
(§33, §39). The occurs check of §7 and its refutation by signature are
not gated. A match or `let-match` that dispatches at runtime, meaning
one at `many` or `unique` on a non-erased scrutinee, uses its
`Matchable` at `many` and requires the opened entry to be
**readable**: either a `Settled` with the type's declaration, or
non-erased and still bound. A `comptime-match` requires the stricter
of the two, a `Settled` with the declaration. Readability is judged at
the match. A `many` parameter opened at `erased` therefore serves no
dispatching match. An unopened `Matchable` leaves its type constructor
opaque, so an unopened first-class type constructor unifies with any
other type constructor of the same signature.

`def-adts` is the only place a `Matchable` is created. Declaring an
ADT creates an anonymous `Matchable` from its tag, its marks and its
constructor markers, and opens it. The built-in `Special` and
`Sharing` are opened at the start (§42). The opaque built-ins `Level`,
`Predates`, `Subterm`, `Coercible`, `Delegate`, `AtFn`, `Slot` and
`World` have no `Matchable` and are never opened, so they are neither
matchable nor empty (§25).

`(matchable-of T)` takes a bare, unapplied type constructor and yields
the opened `Matchable` for it. It is an error when none is open. The
name is resolved through its aliases (§19). A `let` gives the result a
name.

## 9. Restricted dependent types

The elaborated form of a type never contains a function call, and
elaborating a type calls none: the only code that runs is a macro's
expansion (§62). A type is built from:

1. variable references,
2. applications of a type constructor,
3. applications of a value constructor,
4. applications of a type former: `Fn`, `UniqueFn`, `TyCtor`, `ValCtor`
   (§11), `Matchable` (§24) or `Cell` (§37).

An `is` expression (§12) follows the same grammar. Type checking is:
canonicalize, then compare for identity (§7).

The telescope entries of a former bind names (§26, §3). Bound
occurrences are de Bruijn indices; free references are entries of §5.
Pattern matching assumes uniqueness of identity proofs (Axiom K).

## 10. `Type : Type`, no strict positivity

There is no universe stratification, and no positivity requirement on
function or datatype signatures. `Type` is built by the nullary type
constructor `Univ`: `Type` is an entry whose `is` rule is `(Univ)`, and
the type of `(Univ)` is `(Univ)`.

## 11. Type formers for functions and constructors

Types are first class (§24), so there are expressions that produce
them. A function's telescope, a type constructor's telescope and a
value constructor's telescope have different grammars, so each has a
former of its own:

1. `Fn`: `(Fn L params -> returns)`. `L` is a level (§17). Both
   telescopes choose a multiplicity per entry. A parameter may be
   marked `subterm`. A parameter or a return may be written `at` (§36).
   `UniqueFn` has the same shape (§32). The function's own multiplicity
   is not part of the type (§14).
2. `TyCtor`: `(TyCtor params -> Type)`. Its entries carry no
   multiplicity, because type-constructor arguments are always erased
   (§21). The return is `Type`, and there is exactly one return.
3. `ValCtor`: `(ValCtor fields -> (T args))`. There is no level and no
   `subterm`. Each field chooses its multiplicity. The return is one
   saturated application of a type constructor in scope; it may not be
   one of the former's own binders. The return carries no multiplicity:
   whether a constructor is phantom is declared on its `def-adts` line
   and recorded in the `Matchable` (§21, §24).

Of the three formers, only `Fn` and `UniqueFn` have a return
telescope; a match's annotation is one too (§26). All three formers
use the telescope notion of §3. In a `TyCtor` or `ValCtor` telescope,
`at` may not be written on an entry, and neither `slot-of` nor an `at`
in a function type nested there may name an entry of that telescope or
of a constructor telescope enclosing it (§35, §36). The declaration
syntax `name : (telescope) -> (telescope)` used in §55 and §56 is sugar
for these formers plus a name and, for a function, a body. A
function's level is written on its `def-fns`. `is` (§12) may be used
in any of the three telescopes; in a `TyCtor` it is legal but useless,
since every entry there is erased.

## 12. `is` in place of a type

Wherever a variable is introduced, one may write that the variable
`is` another expression instead of giving its type. Its type is then
the type of that expression. The expression must be in §9's grammar.
`let` is the one binder where both the type and the `is` clause may be
omitted; the right-hand side fixes them.

Given `Add : (Nat) (Nat) (Nat) -> Type`:

```
reify-add : (many (Nat) a b) (erased (Nat) c) (erased (Add a b c) p) ->
            (many c is d)
```

Here `c` and `p` are erased, and the return `d` is `c` at multiplicity
`many`. The `is` clause gives `d` its type through `c` while its
multiplicity differs. This is how an erased witness is turned into a
runtime value. An argument supplied for an `is` parameter or field, or
a result supplied for an `is` return, is written like any other and
must canonicalize to the same term as the `is` expression. Its
multiplicity is that of the position.

## 13. Multiplicities

Every binder declares a multiplicity: `erased`, `many` or `unique`.
`erased` is Idris 2's multiplicity 0 and `many` is its ω, written as
words (§1). There is no default: wherever the multiplicity is a
choice, it is written, which cuts down on mistakes while the design is
in flux.

`unique` may be declared on function parameters and return entries,
constructor fields, `let` binders, and a match's scrutinee (§14). Where
a value can be mutated in place, either through the cell a destructure
hands back (§37) or by an extern's own in-place operation (§43), a
`unique` binder on that value is the only reference to it. Where
nothing can mutate the value, the sole-reference property is neither
promised nor needed, and a `unique` binder may alias a live `many` one
(§34). The guarantee belongs to the binder, not to the type: there is
no unique type and no unique constructor, and a constructor marker in
`def-adts` or in a `Matchable` is never `unique`. `match`, `let-match`
and `comptime-match` have a `unique` mode (§23).

## 14. Declared erasure

Every binder declares its multiplicity, so the erasure of every name is
known where the name is bound, and the erasure of an expression is
fixed by the position it occupies. Nothing is derived from usage. The
binders and where each gets its multiplicity:

- function parameters, return entries and constructor fields: their
  telescope entries (§11, §3);
- a value constructor: its marker in `def-adts` (§21); a function: its
  marker in `def-fns` or `def-unique`, which is not part of its type
  (§11) and is not written at a call;
- `let` binders: each binder (§19);
- a match's scrutinee: the mode written on the `match`, which also
  fixes the fields of the branches (§21, §22); the fields of
  `let-match` and `comptime-match` in the same way (§28, §27);
- everything created by its kind: a `Level`, a proof and a type
  constructor are `erased`; a `Matchable` is `many` (§24); a slot is as
  §35 says.

These are the **erased positions**:

- an argument for a parameter or field declared erased;
- any argument of a type constructor (§21);
- a type or `is` expression (§9, §12);
- the final expression of the right-hand side of a `let` whose binders
  are all `erased`; in a `values` there, each entry takes the
  multiplicity of its own binder;
- the scrutinee of an `erased` match;
- the proof argument of a `coerce`; every argument of a `coercible-*`
  form, of `prove-subterm`, of `prove-predates`, of `prove-literal-lt`
  and of the three axioms; and the proof inside `(subterm p)` and
  `(predates p)` (§18, §19, §33, §45);
- the body of an absurd-by-proof branch and the body of an `absurd`
  function (§21, §25);
- the head of a call written `(at erased (f ...))` (§39);
- every sub-expression of an erased expression.

The branch of a phantom constructor under a non-erased scrutinee is
erased throughout (§21). So is the body of an `erased` function: it is
checked with every return entry `erased`, whatever its signature says,
so such a function can only be held or called at `erased`. Every other
position is non-erased, including a position of size zero that is not
inside an erased position.

Checking is local. Referring to an `erased` name from a non-erased
position is an error. Referring to a `many` name from anywhere is
allowed. A non-erased value may be used in an erased position freely;
the reverse needs a proof: `coerce` (§33) or `is` (§12).

A multiplicity written on a form must match the form's position. A
`match` in an erased position must be written `erased`; `many` or
`unique` there is an error. The multiplicity written in an `at` around
a call or a cell invocation instead names how its head is taken (§37,
§39). A statement's position is that of the
expression it belongs to (§27), so this rule also covers `let-match`,
every binder of a `let`, and `open-adt`.

For a call or a constructor application:

1. If the result is erased, there is no further constraint: any callee
   and any argument erasures are allowed.
2. If the result is non-erased, each argument for a non-erased
   parameter or field must itself be non-erased, and the callee must be
   non-erased, except in `(at erased (f ...))` (§39).

Phantom constructors, `erased` functions and type constructors enter
scope erased, so by rule 2 none of them can produce a non-erased
result. Multiplicity is relative to the position, not a property of a
value. Any function may be invoked in an erased position with erased
arguments, so a `many` parameter may hold a value built by an erased
constructor.

Erasure is decided from the text of one unit alone, a function body
against its signature or a run-position statement against its binders,
before that unit is compiled or run.

Erased code obeys the `at` rules of §36 and gets the slot facts of §35
and §36 that the same code would get at `many` or `unique`. Where the
two differ, it gets what the `unique` form gets, as a call already
does through its callee's signature (§36); this matters for a cell
invocation (§37), whose value is then at its cell, and for a
`cell-write` (§37), whose result is then at the cell it writes. A form
whose only
claim or effect is about the
run is refused in an erased position: `tail`, `notail` and `delegate`
(§19), the `at` wrapper around a call (§39), `share` (§16),
`cell-match` (§38), `cell-same` (§68) and
`fn-same` (§70); and an `erased` function may not be marked `at` (§39).

## 15. Uses of unique binders

Each binder is checked by the uses it has on each path through the
code. The order of the uses does not matter. On one path a `unique`
binder must either have exactly one non-erased use, at unique, plus any
number of erased mentions, or have any number of erased uses and
degraded many uses (§16), including none, and no use at unique. A use
at unique together with any other non-erased use of the same binder is
an error, reported at whichever one the elaborator meets first. An
erased mention is never a use and is allowed anywhere, before or after
the binder is consumed: a proof or a type may name a consumed value.

After a match, a binder's state is the maximum of its states after each
branch, in the order unused, then used at many, then used at unique.
Used at many leaves the binder usable at many and never at unique. Used
at unique leaves it usable only erased. A branch with no non-erased
mention contributes nothing: an `(absurd C)` branch, an absurd-by-proof
branch, and the branch of a phantom constructor under a `many` or
`unique` scrutinee (§21). An `else` branch takes part like any other.

A `unique` value need not be used. A `let` with no binders runs its
right-hand side, because a position of size zero is non-erased outside
an erased position (§14).
This is how a value is consumed for its effect alone.

**Four kinds of mention.** A variable occurs in code in one of four
ways. The second and third are uses:

- an **erased mention**, in an erased position of §14; allowed before
  or after the binder is consumed;
- a **use at many**, in a non-erased position at `many`; a `unique`
  binder can only stand there inside a `share` (§16);
- a **use at unique**, in a non-erased position at `unique`; this
  consumes the binder;
- a **direct variable reference**, the argument of `slot-of` (§35).
  This is the variable itself, never a telescope binder. It is not a
  use: it neither degrades nor consumes, and it may follow the
  consumption.

Every argument to a constructor, a function or a cell behaves as if it
were first bound to an anonymous variable. An argument that is already
a variable is not rebound. That binding is a statement (§27)
placed just before the statement or final form that contains the call,
so its entry stays in scope, anonymously, for the rest of the
expression around it, as the entries of a `let`'s right-hand-side
statements do.

## 16. `share`

A `unique` value is born unique in three ways: a constructor
application in a unique position, a cell invocation (§37), or
`def-unique` (§32). It comes back unique as the `unique`-declared
return of a non-erased call, as a `unique`-labelled field taken by a
`unique` destructure (§22), or as the result of a `coerce` in a
non-erased position whose target side is `(Unique)` (§34).

Degrading a value from `unique` to `many` is explicit. A `unique` value
in a `many` position is an error unless it is written `(share e)`. If
`e` is a variable `x`, the form is a many use of `x`. It is an error if
`x` is also used at unique on the same path (§15). Afterwards `x` can
be used at many, written `(share x)` each time, and never again at
unique. If `e` is any other expression, `e` is elaborated at `unique`
and its result is shared. Either way, the result of `(share e)` is the
result of `e`, at `many`: it has the type of `e`, it `is` whatever `e`
is, so a binder of it forwards the type and facts of `e`, and it is at
the location of `e` (§36). A `share` in an erased position is an error,
because nothing is used there. A head written `(share n)` dispatches as
`n` does (§6).

## 17. Function levels

Every function has a level: a natural number that is erased and is
part of the function's type (§11). A function may call a function of a
strictly lower level. It may call a function of its own level only
under the `Subterm` rules of §19. All functions in one `def-fns` block
share one level, written once on the block. Type and value
constructors have no level. There is no currying, for functions or for
constructors.

Termination rests on levels. A function's parameters may be marked
`subterm`; the marks are part of its signature. Every call decreases a
lexicographic order whose first component is the level, followed by
the `subterm`-marked arguments from left to right. An ADT may have no
constructors at all (`False`).

## 18. Built-ins backing termination

- `Level`: a nullary type constructor, so the type is `(Level)`.
- `Predates : (Type A) (A a) ((Level) l) -> Type`.
- `Subterm : (Type A) (A a) (Type B) (B b) -> Type`. It is
  heterogeneous.

All three are opaque (§8) and erased by kind (§14). There are three
axioms. Each is a special form that takes its two premises as
arguments:

- `predates-trans`: from `(Predates A a l1)` and
  `(Predates (Level) l1 l2)`, conclude `(Predates A a l2)`.
- `subterm-trans`: from `(Subterm A a B b)` and `(Subterm B b C c)`,
  conclude `(Subterm A a C c)`.
- `predates-subterm`: from `(Predates A a l)` and `(Subterm B b A a)`,
  conclude `(Predates B b l)`.

Two forms create proofs.

`(prove-subterm a b)` asserts that `a` is a subterm of `b`. Both must
be expressions in §9's grammar. After canonicalization, `a` must be a
strict subtree of `b`. The search walks through applications of type
constructors and value constructors (productions 2 and 3) and treats a
type former (production 4) as opaque.

`(def-lvl L)` creates a fresh, erased `Level` with the level-mint
marker of §5. A level created later is strictly higher than one created
earlier, so a function at a later level cannot be called from code at
an earlier level. `(prove-predates x L)` creates `(Predates A x L)`.
`x` and `L` are each a variable or a fetch form (§53), such as
`level-of`; both are read by their binders and never canonicalized. `L`
must be an entry created by `def-lvl`, or a `let` binder forwarding
from one (§19). `x` must have an introduction order (§5) earlier than
`L`'s. A literal has none (§45) and is refused; a `let` binder
forwarding from a literal has an order of its own.

## 19. Namespaces, special forms, macros, call-site proofs

**One namespace.** Special forms, types and values share one
namespace. Everything in it may be shadowed, including special forms
and types.

**State-forwarding `let`.** A `let` binder takes over the state of the
right-hand-side entry it corresponds to: `Settled` or `Hypothetical` (§5), the
stored value, minted type and minted `is` if `Settled`, its level-mint
marker and its
introduction order (§5), except that a binder forwarding from a
literal's entry (§45), which has none, keeps an introduction order of
its own, and, through an alias rule in the fact table (§7), its type
and `is` rule. This happens whenever that entry is an
expression in §9's grammar and so has an entry of its own. It is
decided per binder: in `(let ((many a) (many b)) (values x y))`, `a`
takes from `x` and `b` from `y`. A call, a match or a `coerce` has an
entry of its own for each of its results (§28), at the multiplicity
its own position gives it, and a binder of one of them forwards from
that entry as from any other. Inside a body those entries are
`Hypothetical`; in run position they are `Settled` from the moment
the form has run (§29). An `erased` binder of a `Settled` entry
holds the token of §5, not its value. A `unique` binder of a
`Settled` entry does not forward its state, because it takes the
value over: in run position it is minted afresh, with its own type
as its minted type and itself as its minted `is` (§29), and inside a
body it is `Hypothetical`.
Forwarding is one way a `Settled` can reach a function body, for example
a special form renamed locally. The other ways are a direct reference
to the entry, and a macro expansion that mentions it.

**`let` binders.** Each binder is a telescope entry whose type may be
omitted: `(many x)`, `(erased (Nat) x)`, `(many c is d)` (§3). The
multiplicity is mandatory and is the binder's declaration (§14). A
`many` binder needs a non-erased value, a `unique` binder needs a
unique value (§16), and an `erased` binder accepts anything. If a type
or `is` clause is written, it is checked for identity against the
inferred one (§9); a mismatch is an error. This is deliberately strict
for now. A `let` binder may not be
written `at` (§36).

**Special forms as data.** A special form is a nullary constructor of
the built-in enum `Special` (§42). The elaborator dispatches on one in
head position only when that head is `Settled` and non-erased (§6). Held
as a value, it is ordinary data. The constructors of `Special` are the
registry of §54, including the annotation tokens.

**Macros.** A head whose entry is `Settled` and non-erased, and whose
minted type canonicalizes to the prelude's `(Macro)` against the facts
of the innermost enclosing run position, is dispatched as a special
form is (§6), with `(Macro)` in place of `(Special)`: the list is a
macro call, which expands as §62 describes. Macros rest on the
prelude's types, so under `--no-prelude` there are none.

**Call-site proofs.** How the decrease of §17 is discharged depends on
the kind of call:

- A call to a function of a strictly lower level carries
  `(predates p)` immediately after the callee. `p` is a `Predates`
  relating the callee's level, read from its `Fn` or `UniqueFn` type,
  to the current level (§5). A `Predates` about the function value
  itself, which `predates-subterm` can produce, is not accepted here.
- A call to a function of the same level carries `(subterm p)`
  immediately before the decreasing argument. `p` is a `Subterm`
  relating that argument to the enclosing subterm argument at the same
  subterm index (§5). The argument must be supplied for a
  `subterm`-marked parameter. Every `subterm`-marked argument before
  it must be identical, after canonicalization, to its enclosing
  counterpart. The enclosing function must have a subterm parameter at
  that index.
- A call carries at most one of the two. A call inside a body that
  carries neither is given one (§48). At the top level a call carries
  none (§20).
- Every kind of application works through a first-class value: a
  constructor application, a lower-level call, a same-level call,
  marked or not. Only a macro or special form needs a constant-known
  head (§6).

**`tail` and `notail`.** `(tail (f ...))` asserts that the call
compiles to a tail call. `(notail (f ...))` asserts the opposite. A
claim the compiler cannot honour is an error. Tail position is judged
on the post-erasure code, where erased positions, types, coercions and
placings are gone and every `let` that only renames has been resolved
away (§33, §42). The call is in tail position if it is the final
expression of the body, or if its results are bound by a `let` and
returned in order by a final `values`, with or without coercions and
placings. A match in tail
position puts its branches in tail position. An `at` return is dropped
for this purpose, from the call's results and from the function's own
returns alike (§36). The marks wrap a call and nothing else. They are
an error in an erased position.

**`delegate`.** `(delegate (f ...))` is `tail` plus the same
pass-through requirement on the arguments: in the post-erasure code the
marked function's body is nothing but the call, and the non-erased
parameters without a written `at` (§36) are passed straight through, in
order. The function names its callee on its header line, as in
`(many g at f : ...)` (§41), and the call must be to a callee that
canonicalizes to it. The header sees only what was introduced before
the function (§53), so the function it names can never be the function
itself, a later function of its block, a parameter, or anything the
body binds. The non-erased behaviour of the two functions is then
identical. `def-fns` creates a `Delegate` proof recording this;
`delegate-of` fetches the proof and `coercible-of` turns it into a
`Coercible` (§33). A function marked `extern` may not have a `delegate`
body (§42).

## 20. The top level calls freely

At the file's top level, which means anywhere outside a function body,
including the match branches of a top-level statement, any constructor
and any function may be called with no `Predates` or `Subterm` proof. A
decrease annotation written there is an error, not ignored, because
there is no level to check it against. The top level is above every
function level, and no function body can call into it.
## 21. Data types and match branches

**Two kinds of data type.** An `enum` has a non-erased discriminant. A
`union` has an erased discriminant. Separately from that, each value
constructor's declaration in `def-adts` carries `erased` or `many`.
That is the multiplicity the constructor's entry takes; `erased` makes
the constructor **phantom**. The marker is recorded in the type's
`Matchable` (§24), not in the constructor's `ValCtor` type (§11). Each
field is declared `erased`, `many` or `unique` (§22). Subterm
recursion (§17) may go through an erased field.

A type marked `newtype` must have **newtype shape**: every non-phantom
constructor holds exactly one non-erased field, and there is at least
one non-phantom constructor, and exactly one if the type is an enum.
A value of such a type is represented as that field (§33).

**A constructor returns its own type.** Every value constructor is
declared under exactly one type constructor in `def-adts`. Its return
is a saturated application of that type constructor, with one argument
per entry of the type constructor's telescope. The arguments are
expressions in §9's grammar, and may refer to the constructor's own
telescope and to any entry in scope.

**Indices are not shared scope.** A type constructor's parameters are
in scope only in its own telescope. A constructor that constrains an
index declares its own variable for it, with its type, in its own
telescope.

**Match-proved equality is not substitutability.** Two expressions that
a branch forces equal (§7) may still differ in multiplicity. That is a
separate axis.

**Matching.** The multiplicity of the fields bound by a branch follows
from the scrutinee's mode. At `many`, each field has its declared
multiplicity, except that a `unique` field comes out `many`. At
`erased`, every field is erased. At `unique`, see §22.

A branch on a phantom constructor under a `many` or `unique` scrutinee
can never run, because no non-erased value is headed by a phantom
constructor (§14, rule 2). Everything in scope in such a branch is
erased, including the branch's fields, whatever their declarations say,
and so is the branch's result. Its pattern may still bind a cell
binder (§23), erased like the fields. The body is checked with every result
erased, and it must still produce the declared values. (If the body
could be omitted, a `many` function from a type whose only constructor
is phantom to `False` would need no branch at all, and `(F)` inhabits
that type in erased positions.) Under an `erased` scrutinee, the
branch of a phantom constructor is an ordinary branch, because an
erased value may be headed by a phantom constructor.

**Four kinds of branch:**

1. **present**: `((C f1 ... fn) body)`, with one binder per field,
   including the erased fields, optionally followed by a cell binder
   where the type has cells (§23).
2. **absurd, automatic**: `(absurd C)`, for a constructor that is
   refuted by the facts in force (§7). It has no fields and no body. It
   is optional: an unlisted constructor that is refuted needs no branch.
   It is an error if `C` is not refuted.
3. **absurd, by proof**: `(absurd (C f1 ... fn) body)`, a branch that
   refutes the facts in force (§51) or produces a value of an empty
   type (§25) instead of the match's result.
4. **else**: `(else body)`, at most one per match. It stands for every
   constructor that is not listed by name and is not refuted. It binds
   nothing, except the scrutinee itself where §23 allows it. Its body
   is checked against the annotation as written, with no branch-forced
   facts. It is an error if it stands for no constructor.

Each constructor has at most one branch. A present branch whose forced
unification contradicts is an error. A constructor with no branch must
either be refuted or be covered by the `else`.

**One real branch.** A match in an erased position is unconstrained,
and so is an at-match (§40) on a union under a `many` or `unique`
scrutinee, which does not dispatch. Otherwise, if at least one of its
results is non-erased: when the discriminant is non-erased, that is, a
`many` or `unique` match on an enum, there is a runtime tag to
dispatch on. When the discriminant is erased, that is, an `erased`
match or a match on a union in any mode, at most one branch may be
**real**. The others must each be automatically absurd, absurd by
proof, or the branch of a phantom constructor under a non-erased
scrutinee. An `else` counts as one real branch, unless every
constructor it stands for is phantom under a non-erased scrutinee, in
which case it counts as none and its body is erased throughout.

**First-classness.** Types, type constructors and value constructors
are first class (§24). Every argument of a type constructor is erased.
A type constructor enters scope erased, and so does a phantom
constructor (§14). A value of type `Type` is erased.

## 22. Fields under each mode

A field is labelled `erased`, `many` or `unique`. A destructure is a
`match`, `let-match` or `comptime-match` on a value, which binds the
fields of its constructor. A `cell-match` (§38) has separate rules.

What a destructure hands out for a field, by the scrutinee's mode:

| field label | `erased` | `many` | `unique` |
|---|---|---|---|
| erased | erased | erased | erased |
| many | erased | many | many |
| unique | erased | many | unique |

A unique-labelled field under a `many` scrutinee comes out `many`: a
shared block shares everything it owns. Construction is the mirror
image, by the position's multiplicity:

| field label | erased position | many position | unique position |
|---|---|---|---|
| erased | erased | erased | erased |
| many | erased | many | many |
| unique | erased | many | unique |

A `unique` field of a constructor built at `many` takes its argument at
`many`.

## 23. The `unique` match mode and the cell binder

`(match unique x ann branches)` consumes `x` and binds the fields of
each branch according to the `unique` column of §22.

When the type's constructors have cells (§37), a pattern may add one
binder after the fields: `((C f1 ... fn u) body)` as well as
`((C f1 ... fn) body)`. The extra binder names the cell the constructor
occupied. Its multiplicity is the scrutinee's, `erased`, `many` or
`unique`, except in the branch of a phantom constructor under a `many`
or `unique` scrutinee, where it is `erased` like the fields (§21). Its
type is `(Cell C (slot-of g1) ... (slot-of gk))`, with
one slot per field whose label is non-erased, in order, `gi` being that
field's binder, and it is at `x` (§36). A
branch passes a `unique` cell out of the match by returning it into an
entry of the match's annotation marked `at x`. A cell at `unique` may
produce its value at `unique`; a cell at `many` produces its value only
at `many` (§37). The `else` branch may bind the scrutinee back, as
`(else x2 body)`. Then `x2` is a fresh binder at the scrutinee's
multiplicity, `is x` and at `x`, whichever constructor the `else`
stands for. A single item after `else` is the body. A pattern on a
constructor with no cell (§37) has no extra binder.

`let-match` takes the same modes and the same extra binder, and binds
outward (§27). `comptime-match` at `unique` is a destructure like any
other: it consumes the `Settled` at unique and binds its fields as
`Settled` at their labels. At `many` it reads the `Settled` at many. Its
scrutinee may be written `(share x)` at `many`, which is the explicit
degradation a unique `Settled` needs; `(share x)` at `unique` is an
error. The elaborator's other reads of a `Settled`, a special form at a
head or a `Matchable` read by a match, are many uses (§32). The
readability requirements for a dispatching match are those of §8.

A value can be read without giving up its uniqueness: destructure it at
`unique`, then in each branch reinvoke the same constructor with every
store skipped (§37). That erases to reading the tag and nothing else.
At `many` the same reinvocation costs nothing and gives the value back
at `many`.

## 24. First-class objects

Each of the following is ordinary first-class data:

1. an ADT value;
2. a function, of `Fn` or `UniqueFn` type;
3. an unapplied type constructor;
4. an unapplied value constructor;
5. a `Matchable`;
6. a `Type`;
7. a cell or a slot (§37, §38);
8. an opaque object: a `Level`, a `Subterm` or `Predates` proof (§18),
   a `Coercible` or `Delegate` proof (§33), or an `AtFn` proof (§39).

`Special` and `Sharing` values (§19, §33) are ADT values. Applying a
held constructor is ordinary application.

A `Matchable` has the type `(Matchable d marks T (e1 C1) ... (en Cn))`.
`d` is `enum` or `union`. `marks` is `newtype`, `extern`, both in
either order, or neither. `T` is the type constructor. The `Ci` are its
value constructors in declared order, each with its multiplicity `ei`,
which is `erased` or `many`. `T` and the `Ci` are bare and unapplied.
The former checks nothing further, so a `Matchable` type may list
entries that are not constructors. Only `def-adts` creates a
`Matchable` (§8), so such a type is uninhabited: opening a binder of
it is allowed, and a match that names a non-constructor is an error.
A mark written twice counts once.
For example, the `Matchable` of `List` is
`(Matchable enum List (many Nil) (many Cons))`. The tag, the marks and
the `ei` are exactly the facts that no type records: a `TyCtor` type
carries no discriminant and a `ValCtor` type carries no phantom marker.
A `Matchable` is created only by `def-adts` (§8), at `many`. Its value
holds the construction and matching of an `extern` type (§42) and
nothing else, so a match that dispatches at runtime on an extern type
needs a `Matchable` it can read (§8). Nothing consults a `Matchable`
until it is opened (§8).

A `Matchable` has three jobs. It tells the checker that a type's
constructors are disjoint (§8). It lets a match work through
first-class type and value constructors. And it is what a match reads:
its type gives the tag, each branch's discriminant and the marks, so
the constructors named in a match may be erased; its value is read only
for an extern type.

## 25. Absurd functions

A function may be marked `absurd` on its `def-fns` or `def-unique`
line, next to its name and multiplicity, as in
`(def-fns L $ (many absurd explode : ...))`. Its body does not produce
its declared returns. Instead it produces one value of a type with no
constructors, such as `False`, which the type's opened `Matchable` (§8)
shows to be empty, or it refutes the facts in force (§51). This is the
function-level counterpart of the absurd-by-proof branch of §21, and
uses the same token (§59). Its body is an erased position (§14), and
it compiles to no code.

A contradiction that lives in the fact table rather than in a value,
for example two constructors of one opened `Matchable` equated, is
used by `open-absurd` (§8), which produces the declared result directly
with no empty type in between. When a scrutinee is available, a match
whose branches are all refuted produces its declared result (§21).

## 26. Multiple return values

A function returns zero or more values. A later return may depend on an
earlier one: the return telescope is a telescope like the parameter
telescope, where each entry depends only on the entries before it.
This is for functions and for the annotation of a `match`,
`cell-match` or `open-absurd` (below, §38, §8). A type or value
constructor returns exactly one value (§11). There is no sigma type: an expression of several
values has no type of its own, each entry of a `values` is a size-one
location (§27), and several values cannot be nested or passed as one.

`values` introduces several values and `let` takes them apart, with one
binder per value: `(let ((many q) (many r)) (divmod n d))`. The items
of a `let` are its binders, bracketed, then any statements, then the
final expression. The binders are a flat list, not a telescope: to a
later binder, an earlier binder is an ordinary scope entry. The
dependency among the returns is in the function's return telescope
(§11); a `let` receives that telescope already instantiated.

A match is written `(match m x ann branch ...)`. `m` is the
scrutinee's multiplicity: `erased`, `many` or `unique` (§21, §14,
§23). `x` is the scrutinee. `ann` is the result annotation: a
telescope of types with no multiplicities, for example `(((Nat) r))`.
It fixes the match's size (§27). The annotation is mandatory. It is
the match motive, and in a dependent match the result types of the
branches mention branch-forced facts. `_` reuses the telescope the
position expects (§47). `(at (...))` makes an at-match (§40).

## 27. Expressions, statements and size

Every expression has a **size**: the number of values it produces.

An expression is a series of **statements** followed by a final form.
The final form is either a `values`, each entry of which is a size-one
expression, or a single form of any size: a call, a match, a `coerce`
or a `tail`-marked call. A `values` with one entry may be written as
just that entry, so `x` and `(Cons A hd tl)` are size-one expressions
equal to `(values x)` and `(values (Cons A hd tl))`. `(values)` has
size zero.

Every form binds names within its own sub-expressions. A **statement**
also binds outward: its names, and the facts it creates, enter the
expression that contains it, are visible to the rest of that
expression, and are gone when it ends. A statement produces no values.
The statements are `let`, `def-lvl`, `def-fns`, `def-unique` (§32),
`def-adts`, `comptime-match`, `let-match`, `open-adt` (§8), `slot-self`
and `open-at-fn` (§35, §39), `unary` (§49), `dump-context`
(MANUAL.md), `compile-error` and `compile-warn` (§4), and `goal` and `qed` (§71). All of them
except `comptime-match`, `goal` and `qed` may appear at the top level or inside a body. `def-fns` and `def-adts` bind the names they
define outward and each definition's parameters inward.

The right-hand side of a `let` is itself an expression, so the
statements before its final expression are statements of the
expression that contains the `let`. Their names are visible only
within the right-hand side, but their entries, facts and opened
objects (§8) enter the expression after the `let`, anonymously, at the
multiplicities they were declared with. Those statements run, or their
code is emitted, whether or not the `let`'s own binders are erased.
Only the final expression is the position that §14 calls the
right-hand side.

`match` binds inward only. A branch's fields, and the facts forced by
entering it, reach that branch and no further. So a `match` is an
expression, of the size its annotation gives (§26).

`(let-match m x (C f1 ... fn))` is a statement that binds outward. It
requires that exactly one constructor of the scrutinee survives the
automatic refutation an ordinary `match` applies (§7). Each constructor
is checked separately, from the environment before the form, with
fresh fields and without the facts learned while checking any other
constructor. The named constructor must be the survivor. Its fields,
and the facts of its branch, stay in scope for the rest of the
containing expression. It is an error if no constructor survives, if
more than one survives, or if the pattern names a refuted constructor.
The survivor may be phantom when `m` is `erased`; its fields are then
erased. At `many` or `unique` a phantom constructor is refused. Nothing
inspects the scrutinee's stored value, so the scrutinee need not be
`Settled` or non-erased, and the form is not confined to run position.
The fields take their declared multiplicities under `m`, as the fields
of a match do (§14). The `Matchable` must be open and, if the form
dispatches at runtime, readable (§8). A `let-match` with further
branches is described in §52.

Most positions require size one. The exceptions are positions whose
size is fixed elsewhere: a function body, by its return telescope
(§26); a match branch body, by the match's annotation; and the
right-hand side of a `let`, by its binders.

**The top level.** A file's top level is an expression and so has size
one. `goal` and `qed` (§71) do not change this, but `--goal open` and `--goal
proved` turn off the driver described here. Several files on one command line share one scope, in order. A
file that ends in a statement produces nothing. Otherwise the type of
the final value decides what the driver does with it. A `Program`
value (§42) is run: the driver consumes it at `unique` and applies each
step's continuation once. Any other final value is used at `many`,
so a `unique` one is written `(share x)` (§16). A final value of `Fn`
type must have one of two forms, at any level `L`.
`(Fn L (many (String) x) -> (many (String) y))`, with the prelude's
`String`, is applied to all of standard input, and its result is
written to standard output. `(Fn L -> (many T y))`, for any type `T`,
is applied and its result is printed (§45); this is how a program asks
for its final value to be computed by compiled code. A final value of
`Fn` type in neither form, or of `UniqueFn` type, is an error. Any
other value is printed (§45).

**Run position.** A form is in run position when it is under no
function body and no match branch. Such a form runs as soon as it has
been elaborated, before the code after it is checked: it is
elaborated, its erased positions are stripped, the evaluator runs the
code, and its results become `Settled` with the resulting values
(§29). Its code is then those values, so the form around it does not
run it again. A form in an erased position runs nothing, and its
results are `Settled` with the token of §5. This nests: the forms
inside a form run before it does, and the statements of a `let`'s
right-hand side complete before the enclosing `let` does. A file's top level is run position, so calls
there need no proofs (§20). Elaborating code under a function body or
a match branch never runs it; such code runs at compile time only when
called from run position, or when it is part of a macro's
implementation, the function the macro holds, which runs each time a
call of that macro is expanded (§19). The binders of a run-position statement
declare their multiplicities (§19), which is what allows the statement
to be stripped and run before the code after it is elaborated.

## 28. Call and match results; `comptime-match`

Inside a function body or a match branch, the result of a call, the
result of a match, a constructor application and a `coerce` (§33) are
`Hypothetical`, even when their arguments are `Settled`: nothing is
folded through them there, and every binding there is
`Hypothetical`. Everywhere else, in run position (§27), each of them
runs as soon as it is elaborated and its results are `Settled`
(§29), as are the binders of the statements there. A definition that
is wanted as `Settled` is therefore written in run position (see `xs`
in §57). This may be relaxed if it proves heavy.

`(comptime-match m x (C f1 ... fn))` asserts, at elaboration time, that
`x` is a `Settled`, non-erased value headed by `C`. It is an error
otherwise. `m` is `many` or `unique` (§23). `x` is a size-one
expression taken at `m`. Since the form is in run position, `x` runs
as soon as it is elaborated (§27), and the stored value of its
`Settled` result is read. A variable is read as it is, and
`(share x)` (§16) at `many` is the explicit degradation a unique
`Settled` needs. The type must be an enum, not a union. `C`
must not be phantom. The pattern binds every field, including the
erased ones, and may bind a cell binder where the type has cells
(§23). This is the
one statement confined to run position (§27). The form consults the
type's `Matchable` (§24) for the discriminant and binds the fields as
`Settled` at their declared multiplicities under `m` (§22): `many` fields
take the values projected from the stored value, and erased fields take
the tokens of §5, since the stored value does not contain them. Its
purpose is proof by reflection: a decidable proposition is discharged
by computing it in run position and asserting the outcome, as
`tests/u8.sl` does for the bound of a `U8`.

On a mismatch, the error prints the expected constructor and the actual
value, including its discriminant and arguments. This can be used as a
diagnostic channel: assert the expected constructor of a wrapper enum
whose other constructors carry a message, and the message is printed.

## 29. `Settled` formation and compile-time inspection

The states are `Settled` and `Hypothetical` (§5). `Settled` arises at three sites.
At each, the multiplicity is declared.

1. **A form in run position** (§27, §20). Every entry it creates and
   leaves in scope is `Settled` once the form has run: its results,
   the elaborator's own binders for its head, arguments and scrutinee
   (§15), the binders and fields of a statement, and the automatic
   slot (§35) of each, which holds the word of its entry, or the token
   where the entry is erased. A `let` is elaborated, stripped of its
   erased positions, and run by the evaluator; its binders take the
   resulting values at their declared multiplicities (§19). A `def-lvl`, `def-fns`, `def-unique` or
   `def-adts` involves no evaluation: a function's value is its
   compiled code, a `Level` is an erased token, and a `Matchable` is
   the FFI's wrapper for an `extern` type and nothing otherwise (§24).
   In the bodies of a `def-fns` block, and in the signatures of the
   block that follow their own (§53), the block's own functions are
   `Hypothetical`. After the block they are `Settled`, at the multiplicity
   written on their lines.
2. **Field binding by `comptime-match`** (§28), at the fields'
   declared multiplicities.
3. **State-forwarding `let`** (§19), in run position as elsewhere,
   except that a `unique` binder of a `Settled` entry is minted at
   site 1 in run position.

Nothing else creates a `Settled`. Inside a function body or a match
branch, every binding is `Hypothetical`, including nested
definitions, except one that forwards a `Settled` entry (site 3). So
any `Special` or `Macro` that is ever invoked (§6) comes from run
position. Inside a body, a constructor application over `Settled`
arguments is `Hypothetical` (§28).

**The minted type and minted `is`.** At sites 1 and 2, an entry
records its type, as it is there, as its minted type, and itself as
its minted `is` (§5); at site 3 it takes its source's of both (§19). Special-form dispatch canonicalizes the minted type
against the facts of the innermost enclosing run position (§6), so a
later run-position fact refines it and a branch-forced one does not.

**Inspection requires `Settled` and non-erased.** A stored value is read
in three places: head dispatch (§6), the discriminant read of
`comptime-match`, and the running of a run-position form that
refers to the entry, where the value is embedded in the code that is
run. The engine of §7 reads no stored value. All three places require
the entry to be `Settled` and non-erased. An erased `Settled` holds only
the token of §5; its value was never computed, because the erased
positions are stripped before the evaluator runs. An erased `Settled` may
still be referred to from the erased positions of a statement, because
those positions are stripped, not read.

**The checker never evaluates.** The checker computes only what the
source spells out. A constructor application assembles data whose
shape the source dictates. A `comptime-match` verifies an asserted
discriminant and projects the fields. Selecting a match branch from a
value would be evaluation, so inside a body the results of a match
stay `Hypothetical` even when the scrutinee is `Settled` (§28). In run
position the match itself runs (§27), which hands the branching to
the evaluator. The inspection sites are checks, not forwarding: by the
time one of them runs, the multiplicity of the inspected entry is
already decided, so no erasure demand flows backwards into code that
has already been checked, stripped and run. Nothing crosses an
evaluation boundary: no erasure demand and no branch-hypothetical
fact.

**The round trip.** Checking a run-position form is a dialogue.
The elaborator checks the form and produces code with the erased
positions removed. The evaluator runs that code. The resulting values
come back to be stored (§5) and embedded as constants. Round trips
nest: a form in run position runs before the form that contains it. A run-position statement is like an anonymous
function of no arguments: its binders declare their multiplicities at
its boundary, as a signature does, and its result type needs no
annotation. Every fact derived from a stored value, that is, a
`comptime-match` and everything that follows from the fields it binds,
relies on the evaluator having evaluated correctly.

## 30. Bottom-up type inference

Types are written at ADT definitions, at function parameters and
returns, and at match results (§26). Everywhere else they are
inferred. Multiplicity, by contrast, is declared at every binder (§14).

## 31. Evaluation strategy

Evaluation is eager. The semantics is that of a machine with unlimited
stack and heap. A real run may crash where the host cannot represent
what is asked of it. A crash produces no value, never a different one.
How a crash is reported is not specified; it need not be a runtime
error.

## 32. Closures, `def-unique`, and the top level

A function defined by `def-fns` is a closure over its scope. It may
mention a `unique` binder of that scope only erased or degraded, that
is, through a `(share x)` written in the body or earlier.

`(def-unique L $ (unique f : params -> returns) body)` defines one
function, not a block. Its type is built by the former
`(UniqueFn L params -> returns)`. Its body may close over `unique`
binders as unique: each such binder that the body uses at unique is
consumed by the definition itself, where the `def-unique` is
elaborated, not at each call, and once modulo match branches as in
§15. The defined binder is born unique. Calling the function is a use
of that binder at unique, or an erased use. A shared `UniqueFn` can
therefore be called only erased, and `share` on one leaves a dead
value. This is what a `unique` binder of `Fn` type cannot express:
once shared, it could be called repeatedly, running its captured unique
values again. A head of `UniqueFn` type can be applied in item 2 of §6, like a
head of `Fn` type; the call uses the head at unique. The level is
written as on a `def-fns`, and `_` is allowed (§46); the level may be
shared with ordinary functions. The parameters may be marked `subterm`,
and the body may make same-level calls under `subterm` proofs. The
marker is `unique` or `erased`, and `absurd`, `extern` and `at` (§39,
§41) may follow it. The function's own name is in scope in its body
as an erased entry, so a call to itself is refused, like any call
through an erased head; recursion goes through a `def-fns` function
that takes the values as parameters. The body supports `tail`,
`notail` and `delegate`, and `delegate-of` fetches a delegate's proof
as for a `def-fns` function.

A top-level binder, which is a `Settled` (§29), may be `unique` under the
same rules, since run-position statements are sequential. When the
elaborator must read a `Settled` as a value, for a special form at a head
(§6) or for a `Matchable` that a `match`, `let-match` or
`comptime-match` reads, that read is a many use. A unique `Settled` there
is an error until it is written `(share x)`. The scrutinee of a
`comptime-match` is used at the mode written on the form (§23). The
driver consumes a program's final `Program` value at unique (§27) and
applies each continuation once.

## 33. `coerce`

A `coerce` reinterprets one value as another value with the same
runtime representation, at no runtime cost, on the strength of an
erased proof that the two are coercible (§60).

**The proof types.** `Sharing` is a built-in enum with the nullary
constructors `Unique` and `Shared` (§42). `Coercible : ((Sharing) sa)
(Type A) (A a) ((Sharing) sb) (Type B) (B b) -> Type` is opaque (§8)
and erased by kind. A side describes a non-erased use. There is no
erased side, because a `coerce` is never used erased and its proof is
always erased. `Delegate : ((Sharing) sg) (Type G) (G g) ((Sharing) sf)
(Type F) (F f) -> Type` has the same shape. It records that the body of
`g` is a `delegate` call to `f` (§19). Only `def-fns` and `def-unique`
introduce it, with `(Shared)` for an `Fn` side and `(Unique)` for a
`UniqueFn` side.

**The expression.** `(coerce a p)`, where `p : (Coercible sa A a sb B b)`.
`a` must be identical, after canonicalization, to the value in the
type of `p`, and `b` is read from that type. The form produces one
value `d : B` with `d is b` (§12). `d` is `Hypothetical` inside a body (§28)
and `Settled` in run position, from the moment the `coerce` has run
(§29). In a position of
multiplicity `m`, with `sa` and `sb` canonicalizing to `(Unique)` or
`(Shared)` there, the form uses `a` at the multiplicity of `sa`,
consuming it if that is `(Unique)` (§15), and yields its result at the
multiplicity of `sb`. If `sb` is `(Shared)` and `m` is `unique`, that
is an error. If `sb` is `(Unique)` and `m` is `many`, the result is a
unique value in a many position and needs a written `share` (§16). `p`
is always erased. The result is at `a` (§36).

**Creating proofs.** All of the following are special forms (§54),
checked at elaboration. `s` is a `(Sharing)` value; `_` solves it from
the expected type (§50).

1. `(coercible-refl s e)`: `(Coercible s A e s A e)`. Since types
   canonicalize (§9), this relates any two `is`-equal values.
2. `(coercible-sym p)`: from `a` to `b`, conclude `b` to `a`, with the
   sides swapped. Its one non-uniform case is reversing `(Shared)` `x`
   to `(Unique)` `(MkBox x)`: that consumes a unique wrapper and gives
   its many-labelled field back shared.
3. `(coercible-trans p q)`: from `a` to `b` and `b` to `c`, conclude
   `a` to `c`. The two middle sides must be equal.
4. `(coercible-share p)`: `p` with both sides `(Shared)`.
5. `(coercible-wrap s C arg1 ... argn)`: wrapping into a **newtype**. A
   type is a newtype because of its `def-adts` mark, which requires
   newtype shape (§21). Every non-phantom constructor of a newtype is a
   **wrapping constructor**: the single one of an enum, or each one of
   a union. Phantom constructors are not wrapping constructors. The form reads the `newtype`
   mark from the opened `Matchable` that lists `C` (§8). That mark is
   what makes the form trustworthy: it guarantees that `C` heads
   inhabited values, whereas wrapping through a constructor without
   the mark could produce a value with no inhabitant. The arguments
   are the telescope of `C`, in order, so exactly one of them, `f`, is
   at the non-erased field. The proof is
   `(Coercible src F f s T (C arg1 ... argn))`, where `src` is `s` for a
   `unique` field and `(Shared)` for a `many` field. Unwrapping is its
   `coercible-sym`.
6. `(coercible-ctor s C ...)`: the same constructor on both sides, with
   fields that may differ. The arguments follow the telescope of `C`.
   An `erased` field takes two arguments, its source value and its
   target value. A non-erased field takes one `Coercible` proof between
   the values at that position, with sides `s` for a `unique` field and
   `(Shared)` for a `many` field. Each argument is checked against its
   field type instantiated with the source values on the source side
   and with the target values on the target side, so the return type
   of `C`, including any index in it, may differ between the two sides.
   The proof is `(Coercible s T (C sources) s T' (C targets))`. To use
   it in a `coerce`, the source must canonicalize to `(C sources)`,
   which is what entering a `C` branch forces (§7); such a proof is
   therefore built per branch from the binders of the branch. The form
   consults no `Matchable` and does not refuse a phantom `C`, because a
   proof between two phantom-headed values is never used: no non-erased
   value is headed by a phantom constructor (§14).
7. `(coercible-of d)`: from `d : (Delegate sg G g sf F f)`, the proof
   `(Coercible sg G g sf F f)`.
8. `(delegate-of g)`: for a function `g` whose body is a `delegate`
   call to `f` (§19), the `Delegate` proof that `def-fns` created
   anonymously. It is fetched from the ambient scope by naming `g`,
   resolved through its aliases (§19). It is in scope in the signatures
   of the block that follow that of `g`, in every body of the block,
   that of `g` included, and after the block, as the names the block
   defines are.

**Representation.** Coercion is free only if the representations
coincide, so the following is a requirement on the implementation.
Values have a uniform representation: every value is one word, either
an immediate or a pointer to a block, whatever its type. So a `Cons`
block holds a `(Meters)` and a `(Nat)` in the same way, and the field
of a wrapper may be existentially typed. A value is the tuple of its
constructor's non-erased fields; a single field is stored bare. A
value carries a tag only when its type is an enum with more than one
non-phantom constructor. The tag is the constructor's position among
the non-phantom constructors, and that is all a tag ever
distinguishes. A phantom constructor takes no discriminant. A type is
**hollow** when it is not marked `extern`, carries no tag, and none of
its non-phantom constructors has a non-erased field. A value with no
non-erased field is the tag alone when its type is tagged, the word of
`vacant-slot` (§35) when its type is hollow, however the value was
built, and an unspecified word otherwise. A union never carries a tag. A newtype
value built by a wrapping constructor is represented exactly as that
constructor's one non-erased field, with no tag and no wrapper. That
representation is mandatory for a type marked `newtype` and forbidden
for a type that is not marked: an unmarked type of newtype shape is a
block (§37). A word is never read as the
field of a constructor that did not build it: a non-erased match on a
union has a single real branch unless it is an at-match, whose `at`
entries every real branch must justify (§40), and unwrapping requires
the value to canonicalize to the application of the wrapping
constructor. Erased fields occupy no space. The pointer of a
`delegate`-bodied function is its callee's pointer (§19). An extern
type (§42) may be marked `newtype`; its FFI author then guarantees the
field representation. A newtype may wrap a field of an extern type.

Only non-phantom constructors and non-erased functions matter in items
5 to 8, because a `coerce` produces a non-erased value, which none of
the others can head (§14).

A proof about a container, for example a proof that every element of a
list is wrapped, is built by recursion in an `erased` function that
returns the proof (§14). Such a function is checked for termination
like any other (§17) and never runs.

**Tail and delegate.** A `coerce` erases to a renaming, so the `tail`
and `delegate` checks of §19 see through it, as they see through a
placing (§42). A call counts as `tail` when its returns are bound by a
`let` and repackaged in a `values` in the same order, with or without
coercions and placings, and as `delegate` when its arguments likewise
pass straight through.

## 34. `Sharing` sides

`Coercible` (§33) carries a side on each end. A side is a value of the
built-in enum `Sharing` (§42):

```scheme
(def-adts $ (Sharing : -> Type)
  enum
  (many Unique : -> (Sharing))
  (many Shared : -> (Sharing)))
```

There is no erased side: a `coerce` is never used erased and its proof
is always erased, so a side describes a non-erased use.
`coercible-refl`, `coercible-wrap` and `coercible-ctor` take a
`(Sharing)` value `s` as their first argument; `_` there is solved
from the expected type (§50), with no default. `coercible-ctor` and
`coercible-refl` put `s` on both sides. A field proof taken by
`coercible-ctor` has `s` on both sides for a unique-labelled field and
`(Shared)` for a many-labelled field. `coercible-wrap` puts `s` on its
target side, and on its source side `s` for a unique-labelled field
and `(Shared)` for a many-labelled field. `Delegate` (§33) also has a
side on each end, set where the proof is created from the types of the
two functions: `(Shared)` for an `Fn` and `(Unique)` for a `UniqueFn`.
So a `UniqueFn` that delegates to an `Fn` is `(Unique)` to `(Shared)`.
`coercible-of` carries the sides across. `coercible-sym` is always
allowed. `coercible-trans` requires the two middle sides to be equal.
Without the sides, a proof chained through two newtypes of one field
type, one labelled `many` and one `unique`, would carry a `many` value
into a unique wrapper; `coercible-trans` refuses it.
`coercible-share` weakens any proof to `(Shared)` on both sides. How a
`coerce` uses its source and yields its result under the sides is
described in §33.

## 35. Slots in the fact table

Every entry of the scope environment (§5), including erased entries,
is created together with an anonymous entry of type `(Slot)` at the
entry's own erasure. This is the entry's **automatic
slot**. It is not in the scope's list of names, and its own slot is
itself. An erased variable has no word, so its slot has no word behind
it, and §14 keeps the slot out of non-erased positions as it keeps the
variable. Two erased slots are atoms like any other two slots, and
equating them says nothing about the variables. In a call in an erased
position, an erased argument may fill a `many` parameter (§14, rule
1); the parameter's slot is then that argument's erased slot. A
forwarding `let` binder (§19) is at its source's slot, whatever its
erasure. Whether two variables are at one slot is decided by the
ordinary canonicalization of the fact table: an entry's slot is an
atom, a rule may equate it with another atom, and two slots are equal
exactly when their canonical atoms are equal. A slot fact is created by
forcing (§7) and ends with its scope.

`(slot-of x)`, for a variable `x` of any multiplicity, denotes the slot
of `x`. For an `x` without a written `at`, that is its automatic slot.
For an `x` written `at v`, it is a slot that the fact table equates
with `(slot-of v)`. It is resolved by the binder of `x`, never through
the `is` rule of `x`; this is what keeps `at` and `is` separate. It is
erased exactly when `x` is, so for an erased `x` it may stand only in
erased positions. Its argument is a direct variable reference (§15),
not a use of `x`. It may be written in a type or `is` expression,
including a function telescope or a match annotation, where it may
name an earlier entry of the same telescope. What it may name is
restricted as the target of `at` is (§36). As an expression it takes the multiplicity of its
position, including `unique`. Its word is the word of `x`, and the
result is at `x`, so a `let` of it is at the same slot as `x`.

A variable of type `(Slot)` is not its own slot merely by being
declared. Like any entry, it has an automatic slot distinct from
itself. `(slot-self s)` is a statement (§27). It takes a variable
`s`, of any multiplicity, whose type canonicalizes to `(Slot)` and
creates, outward
and by forcing, the fact that `(slot-of s)` and `s` are equal. A
contradiction is an error. After it, `s` is the slot that an entry
`(many A a at s)` names and that a cell type `(Cell C s)` indexes.
`vacant-slot`, the built-in `many` constant of type `(Slot)` (§42), is
its own slot. That makes a cell type that names it the type of a fresh
cell. Its runtime word is what `cell-alloc` puts in a vacant slot, and
the word of every value of a hollow type (§33).

## 36. `at`

The parameters and return entries of a function, and the entries of
the annotation of a `match` or `cell-match`, may add `at v`. Several
names may share one `at`: `(many (Nat) r at x)`,
`(unique a is r at a)`. The value is at the same location as `v`. `v`
may be any variable in scope: an earlier entry of the same telescope,
including a return entry, or a variable from an enclosing scope, for
`def-fns`, `def-unique` and a match annotation alike, except an entry
of a type or value constructor's telescope that is still being
written. Such an entry is refused in the later entries of that
telescope and in its return, however deeply the `at` is nested there,
for example in a function type that is a field's type: a function
telescope does not stop the search outward. A constructor's telescope
refuses only its own entries and those of a constructor telescope
enclosing it, so an entry of a function telescope that a `TyCtor` or
`ValCtor` type is written in may be named. The argument of `slot-of`
is restricted in the same way (§35). Beyond this, there is the rule of
§7 that no fact outlives an entry it mentions, which keeps a function
whose type names a closed-over variable inside that variable's scope.
The slot of the entry (§35) is `(slot-of v)`, always, even when `v` is
itself a `(Slot)`. An erased entry may be `at` any variable. A `many`
or `unique` entry may only be `at` a `many` or `unique` variable,
because its word is its target's word and an erased target has none.
`at` may not be written on a `let` binder, on an entry of the
telescope of a type or value constructor, or with a literal as its target. An `at` return
may be `many`, and may be combined with `is`.

**In a value constructor.** To keep a field's word at a slot, declare
the field with a `Placed` type indexed by that slot (§42). After a
destructure, `(placed-slot s T v p)` on the field's binder `p` proves
that its slot is `s`.

**What reaches runtime.** The runtime signature of a function consists
of its non-erased entries that have no written `at`. An entry written
`at`, whether a parameter, a return or an annotation entry, is omitted
after erasure: its word is the word of whatever it is `at`. Which
entries reach runtime is read from the signature as written, never from
what an `at` canonicalizes to. At a call, the argument for a parameter
written `at` is elaborated at the parameter's multiplicity and its uses
count like any argument's. If it is not a variable, it is bound first.
Its slot must equal the target's slot, instantiated with the earlier
arguments, and it is not passed. `_` cannot stand for it, nor for any
argument whose slot the signature names (§50). Inside the
body, the parameter is a
rename of its target's word. An `at` return is absent from the physical
values of a call. A `let` binds it like any return, and the elaborator
supplies its word from a non-erased entry in the same slot: the
caller's own binder for the argument the promise names, which the
caller still holds whether or not the call consumed it, or, where the
promise names an earlier return, that return's own entry (§19), whose
word the call returned whatever the `let` binds it at. The `at`
entries of a match are likewise produced by no branch and read back by
the consumer. The promise of an `at` return is verified where the
function or branch returns, by the canonical identity of the slots. An
absurd body (§21, §25) produces no declared returns, so the promise of
its function or branch has nothing to apply to.

A function that may fail can still promise its result at its argument.
It returns an erased `(Type T)`, a `(unique T v at a)` and a
non-erased outcome whose type is indexed by `T`. Matching the outcome
forces `T` to the intended type on success and to the argument's own
type on failure, and the one word is at `a` either way.

**Writers.** Besides the declaration sites, facts equating slots (§35)
are created by: the cell binder and `else` binder of a destructure
(equated with the scrutinee, §23); a destructure of
a newtype (its non-erased field with the scrutinee) and an application
of a newtype constructor (the value with its non-erased argument, §37);
a cell invocation (the value with its cell) and a `cell-write` on a
`unique` cell (the result with its input); `coerce` and `share` (the
result with the source); a forwarding `let` (§19); a `let` of
`(slot-of x)` (with `x`); the `at` return and `at` parameter of a call
and the `at` entry of a match (with their targets); the delegate annotation (`g` with `f`, §41);
an application of a constructor of a hollow type, and a `cell-alloc`
of one, where an opened `Matchable` lists the constructor (the value
or cell with `vacant-slot`, §33);
`slot-self` (§35);
and a forcing unification (§7) whenever the types it unifies mention
slots, including `Cell` types and types indexed by `(Slot)`, since a
slot is an atom of the fact table. A forced rule between two ordinary
atoms, `x is y`, says nothing about slots. Neither does canonical
equality: two separately built cells with equal contents are
`is`-equal and are two blocks. A non-forcing check, such as an argument
against a parameter, only asks whether the two slots already coincide.
A slot fact ends with the scope that created it, like any fact. A slot
may belong to consumed entries; address equality does not change when
contents do.

**Tail and delegate.** The `tail` and `delegate` checks (§19) read the
post-erasure code with `at` entries omitted, just as they read coerces
as renamings. So a call whose only non-erased results are `at` returns
is a tail call from a function that returns nothing, and the other way
round. The caller's own promise is verified as always, by what follows
the call, which the check requires to be erased.

## 37. Placement: `Cell` and the invocation

A value constructor `C` of a type that is not `extern`, and that is
phantom or of a type not marked `newtype`, has a cell type
`(Cell C s1 ... sn)`. This is a type former
(§9) with one `(Slot)` (§38) per non-erased field of `C`. A constructor
with no non-erased field has an empty cell. Inside the body of an
extern function the `extern` mark does not count, so the constructors
of an extern type have cells there (§43). A phantom constructor has a
cell too, but since no non-erased value is headed by one (§14),
`cell-alloc` of a phantom constructor, and a `cell-write` on or an
invocation of its cell, are allowed only in an erased position, and a
`cell-match` on its cell is refused. Eligibility is read from the opened `Matchable` that lists the
constructor (§8), whose `newtype` and `extern` marks are part of its
type (§24). An abstract constructor must be listed by an opened
`Matchable`. The newtype representation (§33) is mandatory for a type
marked `newtype` and forbidden for a type that is not.

**Newtypes.** A newtype's non-phantom constructors have no cell. Its representation is the word of
its non-erased field (§33). A destructure of a newtype puts the field
it binds at the scrutinee, and an application of its constructor is at
its non-erased argument.

**Obtaining a cell.** `(cell-alloc C)` is an expression that yields a
fresh cell at unique, at no slot, with every slot `vacant-slot` (§35).
When the opened `Matchable` that lists `C` is that of a hollow type,
the cell is instead at `vacant-slot` (§36).
`(cell-alloc (C i1 ... in))` lists every non-erased field; each item is
a `(Slot)` expression at many, or `_` for `vacant-slot`. A partial list
is not allowed. A destructure in any mode yields, through its cell
binder (§23), the cell the constructor occupied, at the scrutinee, with
each slot `(slot-of g)` for the binder `g` of a field whose label is
non-erased.

**Writing.** `(cell-write m u (C i1 ... in))` is an expression. `m`,
`erased`, `many` or `unique`, is the multiplicity the cell is taken at,
and must match the form's position (§14); the items are one per
non-erased field. Each item is
a `(Slot)` expression at many, or `_` to leave that slot alone. `C`
must be the cell's own constructor, canonically. The index of the new
type for each written slot is the value of that item. At `unique` the
form takes `u` at unique and yields the same cell under the new type,
at `u`. This is a physical store into memory that the cell's eventual
invocation re-creates; it does no usage accounting of its own. At
`many` the form uses `u` at many and copies: the result is a fresh
block holding the old words with the written slots replaced, at unique
and at nothing. So a write whose items are all `_` copies a shared
block into a unique cell. At `erased` the form uses nothing and yields
the same cell under the new type, at `u`, as at `unique` (§14).

**Invocation.** A head of `Cell` type can be applied in item 2 of §6.
`(u a1 ... an)` is a constructor application that creates
`(C a1 ... an)` at `u`. It uses each argument at the multiplicity of
its field, as `(C a1 ... an)` would, including erased arguments, which
have no slot and are written as in any constructor application. The
type of the value is the return type of `C`, instantiated. The cell is
taken at the multiplicity of the invocation's own position (§14),
whatever expression `u` is. At `unique` the invocation consumes `u` and
creates its value at `u`; `(share (u a1 ... an))` is how a `many` value
is built in place. At `many` it uses `u` at many and produces its value
at `many`: at the cell when every store is skipped (below), and
otherwise as a fresh copy at nothing. In an erased position nothing is used
(§14).

An `(at)` written immediately before an argument, in the way
`(subterm p)` is written before its argument (§56), asserts that the
slot already holds that argument, that is, that the variable's slot is
the slot in the cell's type, and the store is skipped. If the assertion
is false, that is a hard error, as for `tail`. The marked argument must
be non-erased. `(at m (u a1 ... an))`, which wraps the invocation as
`tail` wraps a call, asserts the same of every non-erased argument and
performs nothing. `m` is the multiplicity the cell is taken at, which
is that of the invocation's position; any other is an error. The `tail` and `delegate` checks treat it as erased,
as they treat a `coerce`, so it may follow a tail call. Only the stores
are skipped. An invocation with every store skipped still uses each
argument at its field's multiplicity and `u` at its position's,
consuming unique ones, and still creates its value at `u` and its `is`
fact in the fact table.

## 38. `Slot` and `cell-match`

`Slot` is an opaque nullary type with no constructors and no
`Matchable` (§8). It is not erased by kind: a `(Slot)` binder is
`many`, `unique` or `erased` as declared. At runtime, the value of a
slot is a word, either a pointer or an immediate. A slot is inert: it
may be stored in a field or a list like any other value, and a unique
copy of its word aliases nothing that matters (§13). A signature that
speaks of a slot abstracts over it as a `(Slot)` parameter; for
example, `(erased (Slot) s) (unique (Cell Pair2 s s) u)` says that the
two slots hold one thing. Two slots are equal exactly when they
canonicalize to one atom (§35). Forcing never refutes on two slots,
because `Slot` has no constructors, and nothing relies on two slots
being distinct. A slot says nothing about contents: the content of a
slot is not a subterm of the slot, and only `is` speaks about contents.

`cell-match` reads the words of a cell out. It is an expression with
two modes: `(cell-match many u ann (C s1 ... sn) body)`, with `u` at
`many`, and `(cell-match unique u ann (C s1 ... sn [u2]) body)`, with `u`
at `unique`. `ann` is a return annotation like a `match`'s (§26). An
`erased` mode is refused, and so is an erased position (§14). In both
modes the `si` are fresh `many` binders of type `(Slot)`, one per
non-erased field, and one forced unification of `(Cell C s1 ... sn)`
against the type of `u` gives them their rules, in the same way that
entering a branch unifies the type of a scrutinee (§7). At `unique`,
`u2` is optional. It is the cell given back, a fresh `unique` binder
that `is u` and is at `u`, and `body` passes it out by returning it
into an entry of `ann` marked `at u`. Without it the cell is consumed. `body` is not in run position
(§27), wherever the `cell-match` is written. The form decides nothing
about a slot: each `si` is whatever the type of `u` said. The words are
for writing into another cell.

## 39. At-functions

A function is an **at-function** when its `def-fns` or `def-unique`
line puts `at` before its name, as in `(many at unwrap : ...)`. The
marks `absurd`, `extern` and `at` come before the name, in any order.
All the return entries of an at-function must be erased or `at` (§36).
Its parameters are not restricted. Its body must **erase to nothing**:
after erasure, with `at` entries omitted, the post-erasure code holds
no call that is not skipped, no constructor application, no allocation,
no store and no copy. Renames, constants, loads from a block, a
`values`, a match whose every branch erases to nothing (including its
dispatch), a nested definition whose remainder erases, and absurd code
all count as nothing. So does an application of a constructor `C`, or
a `cell-alloc` of `C`, when the opened `Matchable` that lists `C` is
that of a hollow type (§33). Calling an at-function skips its runtime; its
arguments are still evaluated, as §15 binds them. A
function marked `erased` may not be marked `at`: it is only ever called
where nothing runs, so the mark would claim nothing. The body of an
`absurd` at-function is a refutation (§25) and is not checked for
erasing. A function marked both `extern` and `at` has no FFI
implementation: the marks are a promise, and its model is checked like
the body of any at-function.

Being an at-function is not part of the function's type. `def-fns`
creates an erased proof object for it, of type `(AtFn F f)` for a
function `f` of type `F`. The proof is created when the header that
claims `at` is elaborated, before the bodies of the block, so a call
within the block to a function so marked, including the function's own
recursive call, is skipped. A body that then fails to erase to nothing
is an error. `(at-fn-of f)` fetches the proof from the ambient scope,
as `delegate-of` does, and may be written in a type (§53).
`(open-at-fn e)` is a statement that opens a proof held in `e`. A
non-erased call is skipped exactly when an opened `AtFn` proof names
the callee's canonical atom. A skipped call still carries and checks
its `predates` or `subterm` proof (§19), and may not be marked `tail`,
`notail` or `delegate`. Whatever its body, an at-function compiles to a
function that does nothing and returns no word. So a first-class call
that reaches it without an opened proof runs without crashing, and the
caller reconstructs the `at` returns as it would anyway.

A call may be asserted to be a call of an at-function by wrapping it:
`(at m (f ...))`, as the full-at form wraps a cell invocation (§37).
`m` is the multiplicity the head is taken at: `erased` for an `Fn`,
and `unique` for a `UniqueFn`, which the call uses at unique as any
call does (§32). Any other is an error. In `(at erased (f ...))` the
head is an erased position (§14), so it may be erased: the call is
skipped, and no word of the head is read. Only the head is erased: the
call stays in its non-erased position, so each argument for a
non-erased parameter must be non-erased (§14, rule 2), and its
arguments are still evaluated, as for any skipped call. A skipped call
that is not wrapped needs a non-erased head. The assertion is optional.
It is a hard error if it fails, and an error in an erased position,
like the marks of §19.

## 40. At-matches

A `match` or `cell-match` (§38) is an **at-match** when its return
annotation is wrapped in an `at` form, with the telescope inside:

```scheme
(match many xs (at (((List (Nat)) ns at xs)))
  ...)
```

Every entry of the annotation must be erased or `at`. The code of each
branch must erase to nothing, as the body of an at-function must
(§39). The match skips its runtime: its scrutinee is evaluated as for
any match, but the match itself, its dispatch and its branches,
compiles to no code, and the consumer reads its `at` entries back from
their targets (§36).
Coverage is checked as for any match. On a union under a `many` or
`unique` scrutinee, the one-real-branch rule of §21 does not apply,
because nothing dispatches: such an at-match may have several real
branches. Under an `erased` scrutinee the rule applies as for any
match. The annotation inside the `at` must be written out; `_` cannot
stand for it.

## 41. The delegate annotation

A `delegate`-bodied function (§19) writes `at` after its name,
followed by the function it delegates to:

```scheme
(def-fns L $ (many g at f : ...) (delegate (f ...)))
```

The annotation is required on a `delegate`-bodied function and is
resolved in the scope of the header (§53). The function it names must
be the one named by the body's `delegate` call, canonically. A body
with no such call is an error. `def-fns` or `def-unique` creates the
`Delegate` proof (§33) when the header is elaborated, before the bodies
of the block, as it creates an `AtFn` proof (§39). The annotation also
puts `g` at `f` (§36). `(slot-of g)` is `(slot-of f)` in the signatures
of the block that follow that of `g`, in every body of the block, and
after the block.
## 42. Built-ins, the prelude and the FFI

**Built-ins.** Before any file is read, the scope holds the following,
all erased unless stated otherwise: `Univ` and `Type` (§10); `Level`,
`Predates` and `Subterm` (§18); `Slot`, an opaque nullary type
constructor, and `vacant-slot`, a `many` constant of type `(Slot)`
(§38, §35); `World`, an opaque nullary type constructor (§42);
`Sharing`, an enum with the `many` nullary constructors
`Unique` and `Shared`, with its `Matchable` opened; `Coercible` and
`Delegate` (§33); `AtFn` (§39); and `Special`, an enum with one `many`
nullary constructor per special form, with its `Matchable` opened and
each form's name bound `many` to its constructor (§19, §54).
`--no-prelude` starts from these alone.

**The `extern` mark.** A `def-adts` entry or a `def-fns` or
`def-unique` function may be marked `extern` (§54) only in the source
prelude, or anywhere in a program run with `--no-prelude`. Marking one
`extern` anywhere else is an error. The declaration is then a *model*. For a
type, its constructors and `Matchable` say what its values are and how
they are taken apart, and the FFI supplies the representation together
with construction and matching over it. For a function, the body says
what it computes, and the FFI supplies an implementation whose
non-erased arity is the model's. An extern type is a type like any
other: its values are non-erased and one word (§33). It may be marked
`newtype`, in which case the FFI author guarantees the field
representation, and a newtype may wrap a field of an extern type. An
extern function may not have a `delegate` body. A function marked both
`extern` and `at` has no FFI implementation (§39). An `extern`
implementation must agree with its model: except through `slot-eq`
(§67), running the models instead of the implementations must give a
program the same values, though not the same cost, and either may crash
where the other does not (§31).
The prototype's FFI is a fixed table keyed by the declared name. An
`extern` declaration of a name the table lacks, or of a name already
claimed, is an error. `--no-extern` runs the models instead, and
`dune test` runs every test both ways. Inside the body of an extern
function, no type counts as marked `extern` for the purposes of §37
and §43.

**The source prelude** `lib/prelude.sl` is elaborated before a
program's files. Its names are ordinary and may be shadowed. Its
levels are anonymous except `nat-lvl`, `char-lvl`, `str-lvl` and
`thunk-lvl`, which a program proves `Predates` against; for example, a
function at level `L` that calls `nat-add` proves
`(prove-predates nat-lvl L)`. Its proofs are erased fields and erased
functions, so none is built at runtime. It contains the following,
along with further types, functions and lemmas not described here, for
which `lib/prelude.sl` is the reference:

- **Equality and arithmetic.** `False`; `Eq : (Type A) (A x) (A y)`
  with `Refl`; the relations `Add`, `Lt`, `Double`, `Pow2`, `Mod` and
  `Mul`, with every field erased, where `Add` recurses on its first
  argument (`AddZero : (Add (Zero) b b)`); `Dec a b` with `Yes` and
  `No`; and `Cmp T R a b` with `CLt`, `CEq` and `CGt`. `Cmp` is
  parametric in a carrier and its strict order, and every field is
  erased, so a value is only its tag and two instances differ by a
  coercion.
- **`Nat`**, the Peano enum of §56, marked `extern`. The FFI holds it
  as an arbitrary-precision integer. The extern functions over it
  return their specifications along with their values: `add` returns
  an `Add`; `sub` is exact, takes `(Lt b (Succ a))`, and returns an
  `Add`; `mul` returns a `Mul`; `div`, `divmod` and `nat-mod` take
  `(Lt (Zero) c)` and return `Mul`, `Add`, `Lt` and `Mod` evidence;
  `nat-cmp` returns a `Cmp (Nat) Lt a b`; `lt-dec` returns a `Dec`;
  `shl` and `shr` go through `Pow2` and `Mul`; `nat-and`, `nat-or` and
  `nat-xor` return a `Bitwise` relation over `Bit` and `BitOp`;
  `nat-halve` returns a `Half n`, the extern enum of `HZ`, `H1` and
  `H2` through which a `Nat` is walked digit by digit. `nat-add`,
  `nat-mul`, `nat-shl` and `nat-shr` are `delegate`s that drop the
  proofs. `double` and `pow2` are plain source. The lemmas over these,
  such as `lt-trans`, `add-le-left` and `lt-subterm`, which turns
  `(Lt a b)` into the `Subterm` that a decrease needs, are erased
  functions. There is no narrowing function from `Nat` to `U8`.
- **`U8`** and **`U62`**. Each is an enum marked `newtype` with one
  constructor that holds a `Nat` and an erased `Lt` proof of its bound:

  ```scheme
  (def-adts $ (U8 : -> Type)
    enum newtype
    (many MkU8 : (many (Nat) n) (erased (Lt n u8-modulus) p) -> (U8)))
  ```

  `u8-modulus` is a `many` top-level constant, `(pow2 eight)`, bound
  together with its `Pow2` proof. `u62-modulus` and `sixty-two` are
  erased top-level bindings, so the prelude never computes 2^62. A
  `U8` is built by `MkU8` with a proof: by reflection for a hand-built
  value (a `comptime-match` on a decided `lt-dec`, §28), and by
  matching `lt-dec` for a computed value. It is taken apart by
  matching. The `U62` operations take `Nat`s with erased proofs that
  the operands and results are below the modulus: `u62-add`,
  `u62-sub`, `u62-mul`, `u62-div`, `u62-mod`, `u62-divmod`, `u62-cmp`,
  `u62-lt-dec`, `u62-shl`, `u62-shr`, `u62-and`, `u62-or`, `u62-xor`,
  `u62-inc` and `u62-dec`. Each is extern and modelled on the
  corresponding `Nat` primitive, so the FFI runs each as one machine
  operation. This relies on the host having native integers of at
  least 63 bits, which the FFI checks.
- **Numerals.** `Bin`, bijective base 2, with `BZ`, `B1` and `B2`; the
  relation `Numeral b n`; `bin-to-nat`, which returns a `Nat` with its
  `Numeral` proof; `BinSucc`; and the erased lemmas `numeral-zero`,
  `numeral-fn`, `numeral-inj`, `numeral-succ`, `double-fn`,
  `double-inj` and `double-parity` that §45 and §49 rely on.
- **Characters and strings.** `Char`, an enum marked `newtype` over
  `U8`; `CharLt`; `char-cmp`, which is `u62-cmp` on the codes by a
  `delegate` under coercions; `String`, an enum marked `extern` with
  `SNil` and `SCons` over `Char`, which the FFI holds as a byte slice;
  `Append`, `StrLt` and `StrLength`; the extern functions `append`,
  `str-cmp`, `str-length`, `str-split` (the first `k` characters and
  the rest, given the length), `nat-str` (decimal) and `trim` (whose
  return `is` its argument and whose implementation is a copy);
  `str-append`, a `delegate` over `append`; and `Rope`, with `REmpty`,
  `RStr`, `RCat` and `RChar`, with the extern `flatten`, which returns
  a `Flat` proof.
- **Containers.** `Unit`, `Bool`, `Maybe`, `Result` (whose `Fail`
  carries a `String`), `List` (§55) with the list relations `Length`,
  `Nth`, `SetNth` and `Repeat` (§44), `Pair`, `EntryKind` (`IsFile`,
  `IsDir`, `IsOther`, `Missing`) and `Change` (`Changed`, `Unchanged`).
- **`thunk` and `unique-thunk`**, at `thunk-lvl`. `thunk` takes a
  value and returns a nullary `Fn` that holds it, at any type and any
  level. `unique-thunk` does the same for a unique value and a
  `UniqueFn`.
- **`Program` and `Request`.** `(Program L)` is an enum indexed by a
  level, read by the driver (§27). `Exit` carries a `U8` exit code.
  `Continue` carries a continuation
  `(unique (UniqueFn L (unique (World) w) -> (unique (World) w2 at w) (unique (Program L) next)) k)`,
  which the driver applies to the world, the one value of `World`,
  which only the driver supplies; the `Program` it returns is the next
  step. So a `Program` is unique throughout, and each continuation is
  applied once. `(Request A)` is an enum indexed by the type of its
  answer, and the special form `world-do` performs one:

  ```scheme
  (world-do A w req) : (erased Type A) (unique (World) w) (unique (Request A) req) ->
                       (unique (World) w2 at w) (many A r)
  ```

  Its arguments are checked as a call's are, and `A` may be `_`
  (§50). It names the prelude's `Request`, so, like literals, it is
  unavailable under `--no-prelude`. `lib/prelude.sl` is the reference
  for the requests and their answers.

  The driver flushes after every write. It never recurses, so an
  unbounded interaction is the driver's loop over total functions, and
  there is no `bind`. MANUAL.md describes `ConfinePaths`,
  `ConfineOutputBytes` and the command-line flags that stand in for
  them.
- **Positions.** `Pos`: `NoPos`, or `MkPos` of a file (`String`), a
  line and a column (`Nat`). A message about a form at `NoPos` carries
  no location, not even a file; one at `MkPos` names exactly that
  position.
- **Macros.** `Macro`, `Symbol`, `Raw`, `Mult`, `Resolution`, `JMEq`,
  the opaque `Gensym`, `MacroWorld` and `Settled`, and the primitives
  `gensym`, `gensym-unique`, `settled-type`, `settled-erase`,
  `settled-mult`, `settled-value`, `settled-eq`, `intern-nat`,
  `intern-char`, `intern-string`, `mint-settled`, `mint-settled-erased`,
  `resolve` and `read-file`, and the function `symbol-eq`. §62 to §65 describe them and the special forms
  `settled-of`, `settled-ty-apply` and `settled-val-apply`.
- **Placement.** The opaque `Placed` and the primitives `place-at`,
  `place-at-many`, `unplace-at`, `unplace-at-many`, `placed-slot` and
  `placed-eq`. §66 describes them. §67 describes `slot-eq`.
- **Slot tables.** `Slots`, marked `extern`, with `SlotItem`, `NthLast`,
  `SlotFind` and `SlotIntern`, and the extern functions `slots-new`,
  `slots-find`, `slots-intern` and `slots-length`. §69 describes them.
- **`ErasedOr`**, with `EONonErased` and the phantom `EOErased`. §68
  describes it and `cell-same`, and §70 describes `fn-same`. On it the
  prelude builds these `extern at` and at-functions (§39):

  ```scheme
  nat-same : (subterm many (Nat) a) (many (Nat) b at a) ->
      (many (ErasedOr (Eq (Nat) a b)) r at vacant-slot)
  u8-same : (subterm many (U8) a) (many (U8) b at a) ->
      (many (ErasedOr (Eq (U8) a b)) r at vacant-slot)
  char-same : (subterm many (Char) a) (many (Char) b at a) ->
      (many (ErasedOr (Eq (Char) a b)) r at vacant-slot)
  string-same : (subterm many (String) a) (many (String) b at a) ->
      (many (ErasedOr (Eq (String) a b)) r at vacant-slot)
  bytes-same : (erased (List (U8)) xs) (erased (List (U8)) ys)
      (subterm many (Bytes xs) a) (many (Bytes ys) b at a) ->
      (many (ErasedOr (JMEq (Bytes xs) a (Bytes ys) b)) r at vacant-slot)
  half-same : (erased (Nat) n) (erased (Nat) k)
      (subterm many (Half n) a) (many (Half k) b at a) ->
      (many (ErasedOr (JMEq (Half n) a (Half k) b)) r at vacant-slot)
  array-same-factory : (erased (Level) M) ->
      (erased (Level) L)
      (many (Fn L (erased Type A)
                (many (Fn M (subterm many A x) (many A y at x) ->
                          (many (ErasedOr (Eq A x y)) r at vacant-slot)) eq)
                (erased (AtFn _ eq) eq-at)
                (erased (List A) xs) (erased (List A) ys)
                (subterm many (Array A xs) a) (many (Array A ys) b at a) ->
                (many (ErasedOr (JMEq (Array A xs) a (Array A ys) b)) r at vacant-slot))
            same)
      (erased (AtFn _ same) same-at)
  ```
- **Arrays**: see §44.

## 43. Extern types and functions

A `unique` value of an extern type may be mutated in place by the FFI.
The FFI author has one constraint beyond those of §42: an `at` return
promised by an extern function's signature must be honoured
physically, and the model's body is checked against the promise like
any body. Inside the body of an extern function, no type counts as
marked `extern` for the `at` rules of §36 or the cells of §37, so a
model is written with the placement of §37 over the cells of its own
type. The shape check of §42 compares the non-erased arities of the
model's constructors with the implementation's. Outside the body of an
extern function, there is no `Cell` for the constructor of an extern
type, and so no `cell-alloc`, `cell-write`, `cell-match` or invocation
on one. The in-place operations of an extern type are its own
functions, such as `array-swap` in §44.

## 44. Arrays

The prelude's array API is indexed by the list of the array's elements.
Elements are owned, and uninitialised slots go through a union newtype
in the manner of Rust's `MaybeUninit`. There is one extern primitive
per element operation, each modelled in source over the type's own
cells (§43). `_` is as in §50.

```scheme
(def-adts $ (Array : (Type A) ((List A) xs) -> Type)
  enum extern
  (many ANil : (erased Type A) -> (Array A (Nil A)))
  (many ACons : (erased Type A) (erased (List A) xs)
                (unique A head) (unique (Array A xs) rest) ->
     (Array A (Cons A head xs))))

(def-adts $ (MaybeUninit : (Type A) -> Type)
  union newtype
  (many Uninit : (erased Type A) (many (Slot) s) -> (MaybeUninit A))
  (many Init : (erased Type A) (unique A value) -> (MaybeUninit A)))

(def-adts $ (Copy : (Type A) -> Type)
  enum newtype
  (many MkCopy : (erased Type A) (many A v) -> (Copy A)))
```

A `(MaybeUninit A)` is one word: the word of `A` under `Init`, and the
word of its slot under `Uninit`. So an `(Array (MaybeUninit A) xs)` is
the same memory as the `(Array A ys)` it becomes. Reading an `Init` out
is a `unique` match whose `Uninit` branch must be refuted, by a fact or
by proof; the one-real-branch rule of §21 makes this `assume_init`
with evidence in place of `unsafe`. Since the field of `Copy` is
`many`, an element of an `(Array (Copy A) xs)` is read in place.
`Immediate A` is an enum with `ImmU62`, `ImmU8`, `ImmChar`, `ImmBool`
and `ImmCopy`, naming the types whose values are immediates; the
`-imm` operations take it as evidence.

The index proofs are generic relations on lists, which the prelude
declares next to `List` (§42), with every field erased:

- `(Length A xs n)`: `xs` has `n` elements. Its constructors are
  `LengthNil` and `LengthCons`.
- `(Nth A xs i x)`: element `i` of `xs` is `x`. Its constructors are
  `NthHere` and `NthThere`. It carries the bound, so no `Lt` accompanies
  an index.
- `(SetNth A xs i y ys)`: `ys` is `xs` with element `i` set to `y`. Its
  constructors are `SetHere` and `SetThere`.
- `(Repeat A n x xs)`: `xs` is `n` copies of `x`. Its constructors are
  `RepeatNil` and `RepeatCons`.

One relation belongs to the arrays themselves. `(AllInit A xs ys)`
pairs a list `xs` of `(MaybeUninit A)` whose every element is
`(Init A x)` with the list `ys` of those `x`; its constructors are
`AINil` and `AICons`.

The functions. Each is `extern` with a source model in
`lib/prelude.sl`; the FFI's implementation drops the arguments the
model does not use:

```scheme
array-new : (erased Type A) (subterm many (Nat) n) ->
    (erased (List (MaybeUninit A)) xs) (unique (Array (MaybeUninit A) xs) a)
    (erased (Repeat (MaybeUninit A) n (Uninit A vacant-slot) xs) p)
array-swap : (erased Type A) (erased (List A) xs) (unique (Array A xs) a)
    (subterm many (Nat) i) (unique A x) (erased A m) (erased (Nth A xs i m) nth) ->
    (unique m is old) (erased (List A) ys) (unique (Array A ys) r at a)
    (erased (SetNth A xs i x ys) p)
array-place : (erased Type A) (erased (List A) xs) (unique (Array A xs) a)
    (many (Nat) i) (unique A x) (erased A m) (erased (Nth A xs i m) nth) ->
    (erased (List A) ys) (unique (Array A ys) r at a) (erased (SetNth A xs i x ys) p)
array-pluck : (erased Type A) (erased (List (MaybeUninit A)) xs)
    (unique (Array (MaybeUninit A) xs) a) (subterm many (Nat) i)
    (erased (MaybeUninit A) m) (erased (Nth (MaybeUninit A) xs i m) nth) ->
    (unique m is v) (erased (List (MaybeUninit A)) ys)
    (unique (Array (MaybeUninit A) ys) r at a)
    (erased (SetNth (MaybeUninit A) xs i (Uninit A (slot-of v)) ys) p)
array-unpluck : (erased Type A) (erased (List (MaybeUninit A)) xs)
    (unique (Array (MaybeUninit A) xs) a) (subterm many (Nat) i) (unique A x)
    (erased (Nth (MaybeUninit A) xs i (Uninit A (slot-of x))) nth) ->
    (erased (List (MaybeUninit A)) ys) (unique (Array (MaybeUninit A) ys) r at a)
    (erased (SetNth (MaybeUninit A) xs i (Init A x) ys) p)
array-get : (erased Type A) (erased (List (Copy A)) xs)
    (unique (Array (Copy A) xs) a) (subterm many (Nat) i)
    (erased A x) (erased (Nth (Copy A) xs i (MkCopy A x)) nth) ->
    (many x is v) (unique a is r at a)
array-get-many : (erased Type A) (erased (List A) xs) (many (Array A xs) a)
    (subterm many (Nat) i) (erased A x) (erased (Nth A xs i x) nth) ->
    (many x is v)
array-length : (erased Type A) (erased (List A) xs)
    (subterm unique (Array A xs) a) ->
    (many (Nat) len) (erased (Length A xs len) p) (unique a is r at a)
array-length-many : (erased Type A) (erased (List A) xs)
    (subterm many (Array A xs) a) ->
    (many (Nat) len) (erased (Length A xs len) p)
list-to-array : (erased Type A) (subterm many (List (Copy A)) xs) ->
    (unique (Array (Copy A) xs) a)
array-make : (erased Type A) (subterm many (Nat) n) (many A x) ->
    (erased (List (Copy A)) xs) (unique (Array (Copy A) xs) a)
    (erased (Repeat (Copy A) n (MkCopy A x) xs) p)
```

`array-swap-imm` and `array-place-imm` are `array-swap` and
`array-place` with an extra parameter `(erased (Immediate A) imm)` and
a `many` index. `array-pluck` leaves the plucked element's word in the
array under `Uninit`, and the slot of that `Uninit` is exactly the slot
of the value returned. So the value may be mutated in place and put
back with `array-unpluck`, an `extern at` function (§39) whose call
costs nothing. This is for a unique value kept inside an outer array,
such as a row of a jagged array: it is plucked, mutated in place, and
put back at no cost. Until it is put back, the array may keep the plucked
value alive. Constructing an `ACons` copies its tail, and taking an
array apart through the model's `ACons` view is O(n). `init-witness`
is an erased witness, in the shape of §60, that an
`(Array (MaybeUninit A) xs)` with `(AllInit A xs ys)` coerces to an
`(Array A ys)`, at `(Unique)` on both sides. The `coerce` is written
where it is used: a wrapper function would extract to a call, while
the inline `coerce` extracts to nothing.

## 45. Literals

Numerals, character literals and string literals are sugar over the
prelude (§42). Each stands for values that the prelude's own types
express, and a program with literals means what it would mean with
those values written out.

**Syntax.** A numeral is an atom made only of digits, with no leading
zero: `0` or `42`. A numeral written plain is never a name, and a binder
written as a plain numeral is an error; `#"42"` is a name (§1). A
character literal is `#\c` for a single byte `c` that the word syntax
admits, or `#\space`, `#\newline`, `#\tab` or `#\xHH`, where `HH` is two
hexadecimal digits. `#\(`, `#\)` and `#\;` must be written in the hex
form. A string literal is `"..."`, starting at the start of a token,
with the escapes `\n`, `\t`, `\"`, `\\` and `\xHH`, where `HH` is two
hexadecimal digits giving one byte. Any other byte, including a newline,
stands for itself.

**Meaning.** A numeral denotes a `Nat` together with an erased proof
`(Numeral b n)` that relates it to its spelling `b`, a `Bin` in
bijective base 2: `(BZ)` is zero, `(B1 b)` is 2b+1 and `(B2 b)` is
2b+2, with the least significant digit outermost, so each number has
exactly one spelling. These are the two values `(bin-to-nat b)`
returns. A character literal denotes a `Char`, the prelude's newtype
over `U8`, which is itself a newtype over a `Nat` below `u8-modulus`,
together with the erased proof of that bound. Any byte is a `Char`. A
string literal denotes a `String`, the prelude's extern enum of `SNil`
and `SCons` over `Char`: its characters consed up, in order.

**Interning.** A literal is interned once per program, by what it
denotes: a numeral by its number, a character by its code, a string by
its characters. So `#\a` and `#\x61` are one entry, and every
occurrence of `"ab"` is one entry. The entries a literal stands for
are the same wherever the literal is met, in whatever scope; they
depend on the prelude alone, as if minted by run-position forms,
and have no introduction order (§18). They refer to the prelude's
own `Nat`, `Char` and `String` and their constructors, whatever names
the program has shadowed since. They are anonymous and outside every
scope: nothing can name, shadow or rebind them, and an occurrence of
the literal resolves to them by the literal itself. A character literal
also interns the numeral of its code.

**What the checker sees.** A numeral is opaque: a `Settled` `Nat` with no
`is` rule, next to its erased `Numeral` proof. `3` is not
`(Succ (Succ (Succ (Zero))))`. `(numeral-of lit)` yields a literal's
proof by its spelling; for a character literal it yields the proof of
the character's code, and for a string literal or a name it is an
error. So two spellings equated in a branch refute the branch, and
`unary` (§49) produces the one rule that a `Succ` shape needs.
`(prove-literal-lt a b)`, for numerals `a` below `b`, creates
`(Lt a b)`, asserted as a character's bound is. A character literal is
transparent down to its opaque `Nat`: its entry carries
`is (MkChar (MkU8 n p))`, where `n` is the entry of its code's numeral
and `p` is the erased proof of its bound, asserted rather than decided.
So to the checker a character is its code. A string literal is opaque:
a `Settled` `String` with no rule. A rule exposing its characters would
make every canonical form that mentions the literal expand to all of
them. `comptime-match` reads its value, and
a match inside a function takes it apart at runtime.

**Printing.** A value of type `Nat`, `Char` or `String` prints as the
literal it reads back from: a numeral in decimal; a character bare where
the word syntax admits it, and otherwise as `#\space`, `#\newline`,
`#\tab` or `#\xHH`; a string with `"` and `\` escaped and every byte
outside `0x20` to `0x7e` escaped, a newline as `\n`, a tab as `\t` and
any other as `\xHH`. A constructor's name prints plain where that reads
back as the same name, and otherwise raw (§1). Any other value prints by
its type. A tagged enum names its constructor. A type with exactly one
non-phantom constructor names it. A union with more than one prints `_`.
So does an erased field, a cell, a slot, a function, an opaque proof,
and a value whose type has no readable `Matchable` (§8). A last argument
that is itself an application is written with `$` (§2). Reading a
printed literal back gives a literal that denotes the same value.

**Left to the implementation.** How a `Nat`, `Char` or `String` is
held at runtime, and whether a literal's entries are produced by
elaborating statements or created directly to the same effect. The
requirement of §42 applies: stripping the extern implementations must
leave every literal meaning the same value.

## 46. `_` as a `def-fns` level

`_` written where the level of a `def-fns` or `def-unique` block goes
(§17, §54) inserts a `def-lvl` immediately above the block, creating
an anonymous level, and defines the block's functions at it.

## 47. `_` in a match's return annotation

Where a position already fixes the telescope that a `match` must
produce, `_` may be written in place of the annotation (§26) to reuse
it. Those positions are: the final expression of a function body; the
final expression of a match or `else` branch body; the final
expression of a `cell-match` body (§38); the final expression of a
`let` whose binders all carry a type or `is` clause; and an argument
position, where the parameter gives the expectation. The expectation
passes down through `values`, `tail`, `notail`, `delegate` and the
`at` wrapper. The reused telescope may not contain a `_` that is still
to be inferred (§50). `(open-absurd e _)` reuses the telescope in the
same way (§8).

## 48. `_` in a call's decrease annotation, and no annotation at all

`(predates _)` reads the callee's level (`level-of`, §54) and the
current level, and builds the `Predates` proof that relates them.
`(subterm _)` builds the `Subterm` proof for the argument it precedes,
against the enclosing subterm argument at the same index. Neither
searches. Both fail whenever a proof needs the transitivity axioms of
§18, or comes from a parameter or a call, or is carried in data. Such a
call writes its proof out (§19).

A call inside a function body may carry no annotation at all. The
elaborator then supplies one: `(predates _)` when the callee's level
and the current level do not canonicalize to the same level, and
otherwise `(subterm _)` before the first `subterm`-marked argument that
does not canonicalize to the same term as its counterpart among the
enclosing function's `subterm` arguments (§5, §19). The proof is built
and checked as if it had been written. A same-level call whose
`subterm` arguments all canonicalize to the same terms as their
counterparts is an error. At the top level a bare call is what §20
describes, and a written annotation is an error.

## 49. `unary`

`unary` reasons about a numeral through the prelude's `Numeral`
relation (§45) rather than about its opaque `Nat`. It elaborates into
ordinary calls on prelude lemmas, in the prelude's scope, so that no
shadowing reaches them, and carries no meaning of its own. It takes a
numeral or a character literal; a character stands for its code.

`(unary a b)` is a statement. `b` must be below `a`. It creates one
rule, `a is (Succ ... b)` with as many successors as separate the two.
The rule is built from the one-step proofs of `numeral-succ`, each
given the `BinSucc` witness that one spelling steps to the next, folded
together by `eq-cong-succ` and `eq-trans`, and carried out by a single
`let-match`. `(unary a)` is the same with `(Zero)` as the floor,
reached through `numeral-zero`. The literals walked over are not
mentioned by the rule and stay opaque: `(unary 5 3)` says
`5 is (Succ (Succ 3))` and nothing about `4`. The distance is at most
4096. What the rule buys is a literal that can be used where a `Succ`
shape is wanted: to peel a `Vec`, or, with a `unary` for each literal
down to zero, to stand as the length of a `Vec`.

## 50. `_` for an inferred argument

**Where `_` may stand.** As an argument only when all of these hold:

1. the argument is erased where it stands: an erased argument of any
   application in item 2 of §6, including a cell invocation, or any
   argument of a call that is in an erased position;
2. its parameter is not written `at` anything (§36);
3. no other entry of the signature is `at` it, including returns and
   entries of nested types;
4. no other entry of the signature applies `slot-of` (§35) to it, with
   the same scope.

Together, items 3 and 4 say that a `_` never stands for an argument
whose slot the signature mentions, so no question arises of what slot
a `_` argument has. Also as an argument of `coercible-wrap`, as the
`Sharing` argument of `coercible-refl`, `coercible-wrap` and
`coercible-ctor` (§34), and in place of any type, including a whole
binder type or annotation entry. Each such `_` is a fresh unification
variable, a **meta**. `_` as an item of `cell-alloc` or `cell-write`
(§37), and `_` as a binder (§1), are separate forms, not metas.

**Expectation.** Some positions expect a telescope, each entry a type
or an `is` term, and that expectation helps solve the metas inside
them. These positions are: a function body (its returns), a match
branch (its annotation), a `let` whose binders all carry a type or
`is` clause, and an argument (its parameter, given the arguments
before it). The expectation passes down through `values`, `tail`,
`notail`, `delegate` and `at`. It never passes up.

**Boundaries.** A meta never reaches the fact table. Every form that
records a fact is a *boundary*, and a meta that is still unsolved at a
boundary is an error. The boundaries are: the `)` of a call, a `let`
binding, a scrutinee, a match annotation, the results of a body, the
operands of a special form, run position, and each telescope entry as
it is bound. A constructor application and a cell invocation are not
boundaries: their metas may stay open for the surrounding form to
solve. So `(f _ (Nil _) xs)` is accepted, while `(len _ (Nil _))` is
refused at the `)` of the call. A `_` in a signature is accepted when
its own entry solves it.

**Solving.** Metas are solved by unification only, with no search and
no computation. A meta's solution must have the meta's type, the type
of the position it stands for, as a written argument must: solving a
meta to a term also unifies the meta's type with the term's type.
Boundaries settle from the inside out: everything within one boundary
is solved together, and a boundary nested inside it closes first, using
only what is known at that point. A match's annotation is settled
before its branches, so no meta crosses into a branch. A bare `_` as a
whole annotation entry or binder type is a meta of type `Type`. `_` is
not accepted as an entry of a `values` or as the scrutinee of a
`let-match`. After the arguments are solved, the decrease annotation of
§48 is inferred.

## 51. Refuting in an absurd body

In the body of an `absurd` function or of an absurd-by-proof branch
(§21, §25), after its statements, the final expression may *refute*
the facts in force instead of producing a value of an empty type. The
statements may include a `let-match`, as in
`(absurd (Zero) (let-match erased le (LtS x y l1)) l1)`. A refutation
produces no value and binds nothing. It is one of:

- a `match` annotated `_`. It is erased, and it refutes when every
  constructor is refuted. Each of its branches is `(absurd C)`, or is
  absurd by proof with a body that refutes in turn. It has no `else`.
- `(open-absurd e _)`, which refutes when the open contradicts (§8).
- any other expression `e`. It is elaborated as an erased value and
  accepted when `(match erased e _)` with no branches would refute. So
  `(False)` works, and so does `(Lt a (Zero))`. This is one match
  deep, with no search.

## 52. `let-match` with branches

`(let-match m s (C f ...) branch ...)` takes the four kinds of branch
of §21, written as in a `match`. `(C f ...)` binds outward as before.
If there is more than one real branch, counting the pattern itself,
the form elaborates to `(match m s A ((C f ...) rest ...) branch ...)`,
where `A` is the annotation of the containing expression and
`rest ...` is what follows the `let-match`. If there is exactly one
real branch, the form stays a statement and its absurd branches simply
refute. Coverage replaces the "exactly one survives" rule of §27. Any
branch not headed by `absurd`, including an `else`, counts as real
here.

More than one real branch is allowed only in a function body, a
`match` or `else` branch body, or a `cell-match` body (§38). In the
right-hand side of a `let`, in run position, and in absurd bodies
(§51), only absurd branches are allowed.

## 53. Fetch forms in a type

`(level-of f)`, `(matchable-of T)`, `(delegate-of g)`,
`(numeral-of n)`, `(slot-of x)` and `(at-fn-of f)` may be written in a
type or an `is` expression. Each elaborates to the entry it would yield
as an expression, which is a variable reference, the first production
of §9. It is read where it is written, against the facts in force
there. The names of a `def-fns` block are in scope in every body of
the block. In a signature, only the functions before it in the block
are in scope, as `Hypothetical` entries (§6). A signature never sees its own
function or a later one. `coercible-of` is not a fetch form: it creates a
fresh proof at each use, and it may not appear in a type.

## 54. Special form registry

Every special form, as a constructor of `Special` (§19), grouped as
§27 groups them. Each entry points to the section that specifies it.

**Statements** (§27):

- `let`: zero or more binders, bracketed, then statements, then the
  final expression (§19, §26, §12). With zero binders it runs the
  right-hand side for its effect on unique values (§15).
- `def-lvl`: creates a fresh `Level` (§18).
- `def-fns`: one or more mutually recursive functions at one level,
  written on the form, each with its own `erased`/`many` marker (§14),
  optionally `absurd` (§25), `extern` (§42) or `at` (§39), and `at g`
  on a `delegate`-bodied function, where it is required (§41). It may
  be nested in a body. It creates a `Delegate` proof for
  each `delegate`-bodied function (§33) and an `AtFn` proof for each
  at-function.
- `def-unique`: one function of `UniqueFn` type (§32).
- `def-adts`: one or more mutually recursive ADTs, each `enum` or
  `union`, and optionally `newtype` and `extern`. It creates and opens
  each type's `Matchable` (§21, §8, §33, §42).
- `comptime-match`: a compile-time discriminant assertion on a `Settled`
  (§28). Confined to run position.
- `let-match`: destructures a scrutinee of which exactly one
  constructor survives refutation, binding outward (§27, §52).
- `open-adt`: opens a `Matchable` (§8).
- `slot-self`: makes a `(Slot)` variable its own slot (§35).
- `open-at-fn`: opens an `AtFn` proof (§39).
- `unary`: rewrites a numeral to successor form (§49).
- `dump-context`: stops elaboration with a report of the context
  (MANUAL.md). Also usable as an expression and as a type.
- `compile-error`, `compile-warn`: report an error or a warning (§4).
  `compile-error` is also usable as an expression and as a type.
- `goal`: sets the unit's goal; only a bare top-level form of a file (§71).
- `qed`: discharges the unit's goal; only a bare top-level form of a file (§71).

**Type formers** (§9, production 4):

- `Fn` and `UniqueFn` (§11, §32), `TyCtor` and `ValCtor` (§11),
  `Matchable` (§24), `Cell` (§37).

**Expressions:**

- `match` (§26, §21, §23, §40) and `values` (§26, §27).
- function call, constructor application and cell invocation (§6, §19,
  §37). A call carries `(predates p)` after the callee or `(subterm p)`
  before the decreasing argument, so it has more items than the
  callee's arity.
- `coerce` (§33), `share` (§16), `cell-alloc`, `cell-write` and
  `cell-match` (§37, §38), `open-absurd` (§8), `world-do` (§42),
  `settled-of`, `settled-type`, `settled-erase`, `settled-mult` and
  `settled-value` (§64), `gensym`, `settled-eq`, `intern-nat`,
  `intern-char`, `intern-string`, `mint-settled`, `mint-settled-erased`,
  `resolve`, `read-file`, `settled-ty-apply` and `settled-val-apply` (§65),
  `place-at`, `place-at-many`, `unplace-at` and `unplace-at-many`
  (§66), `slot-eq` (§67), `cell-same` (§68) and `fn-same` (§70).
- the `at` wrapper around a cell invocation or an at-function call,
  `(at m (...))`, `m` the multiplicity its head is taken at (§37,
  §39).

**Proof forms**, all erased (§14):

- `prove-subterm`, `prove-predates`, `predates-trans`, `subterm-trans`
  and `predates-subterm` (§18).
- `gensym-unique` (§65).
- `coercible-refl`, `coercible-sym`, `coercible-trans`,
  `coercible-share`, `coercible-wrap`, `coercible-ctor` and
  `coercible-of` (§33).
- `prove-literal-lt` (§45).
- `placed-slot` and `placed-eq` (§66).

**Fetch forms**, which may also be written inside a type or `is`
expression (§53):

- `level-of` (§17), `matchable-of` (§8), `delegate-of` (§33),
  `numeral-of` (§45), `slot-of` and `at-fn-of` (§35, §39).

**Annotation tokens**, which annotate a form rather than heading a
list:

- `erased`, `many`, `unique`: the multiplicities (§13).
- `:` separates a name from its signature at a declaration (§3, §55).
  `is` separates an `is` expression from the name it introduces (§12,
  §3). `->` separates parameters from returns (§11).
- `subterm` marks a parameter as part of the lexicographic order (§17,
  §19, §3) and heads the call annotation that names the decreasing
  argument. `predates` heads the call annotation that carries the proof
  of a lower-level call (§19).
- `enum` and `union` give the erasure of the discriminant (§21).
  `newtype` (§33) and `extern` (§42) are marks written after it.
  `absurd` is written on a `def-fns` line (§25) or before the pattern
  of a branch (§21).
- `tail`, `notail` and `delegate`: calling-convention marks that wrap
  a call (§19).
- `else` heads the branch that stands for every unlisted constructor
  (§21).
- `at` appears on a telescope entry, before an argument of a cell
  invocation, around an invocation or a call, around the annotation
  of a `match` or `cell-match`, before a `def-fns` name, and after one
  (§36, §37, §39, §40, §41).

## 55. Worked example: `List`

```scheme
(def-adts
  ((List : (Type A) -> Type)
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) rest) ->
       (List A))))
```

The prelude declares `List` exactly like this (§42). `tests/list.sl`
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

## 57. Worked example: level-polymorphic `map`

`map` calls the function it is given, so by §17 it sits at a level
strictly above that function's level, and the call needs a `Predates`
proof. The proof cannot be created inside `map`: `f` is `map`'s own
parameter, so it was not in scope when `map`'s level was created (§18).
The relation must be established where the level is created, so `map`
is produced by a factory.

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

§58 is the same program with sugar.

## 58. Worked example: `map` with sugar

The program of §57 with `_` levels and annotations, inferred arguments
and bare calls:

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

The body is `f`, a `(False)`, where the signature promises `(many A a)`;
`absurd` accepts that. The function compiles to no code, and holding it
at `many` is fine: the pointer is never followed. `tests/absurd.sl` is
this program.

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

The whole body of `unwrap-witness` is an erased position, so the
one-real-branch rule of §21 never applies, and the proof's source
canonicalizes to `ms` because each branch forces the matching `is` fact.
In `unwrap-all` the call is in an erased position and never runs;
`(coerce ms p)` is the only runtime content, and it erases to nothing.

A `delegate` proof, reusing `inc` from §57 at level `I`:

```scheme
(let ((erased piv)) (prove-predates I V))

(def-fns V $ (many inc-noted at inc : (many (Nat) n) (erased (Nat) note) ->
    (many (Nat) m))
  (delegate (inc (predates piv) n)))

(let ((erased ig)) (coercible-of (delegate-of inc-noted)))
```

`(coerce inc-noted ig)` is then the pointer of `inc` itself.
`tests/coerce.sl` is this program.

## 61. Worked example: tail call modulo cons

`append` copies `xs` onto `ys` in destination-passing style, over the
prelude's `List` (§55), whose fields are both `many`. The helper takes
a vacant cell and the head that belongs in it, and promises its result
at the cell:

```scheme
(def-fns _ $ (many append-into : (erased Type A)
    (unique (Cell Cons vacant-slot vacant-slot) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell))
  (let-match many xs (Cons _ hd tl) ((Nil _) (share (cell _ h ys))))
  (let ((unique next)) (cell-alloc Cons))
  (let ((unique cell2)) (cell-write unique cell (Cons (slot-of h) (slot-of next))))
  (let ((many r2)) (tail (append-into _ next hd tl ys)))
  (share (at unique (cell2 _ h r2))))

(def-fns _ $ (many append : (erased Type A) (many (List A) xs) (many (List A) ys) ->
    (many (List A) r))
  (let-match many xs (Cons _ hd tl) ((Nil _) ys))
  (let ((unique cell)) (cell-alloc Cons))
  (append-into _ cell hd tl ys))
```

The write stores `h` before the call: left to the invocation, that
store would follow the call and the `tail` claim would fail. Per
element: one allocation, two stores, constant stack.

`tests/cell_append.sl` is this program.

## 62. Macro expansion

A macro is a value of the prelude's `Macro`, a newtype over the
function it holds:

```scheme
(def-adts $ (Macro : -> Type)
  enum newtype
  (many MkMacro : (erased (Level) L)
     (many (Fn L (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
               (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out)) f)
     -> (Macro)))
```

A list whose head dispatches as a macro is a macro call (§6, §19). The
function is applied to a macro world (§65), the position of the call's
opening `(` or `$`, and the call's arguments as `Raw` (§63),
unexpanded and unresolved; the head is not passed. The forms it returns
replace the call. In statement position each of them is a statement; in
final position the last is the final form and the ones before it are
statements before it. A call also expands in a telescope, among the
binders of a `let` and as one of its entries, as a branch of a `match`
or `let-match`, as a constructor of a `def-adts`, and as an argument or
an entry of a `values`, where its forms take its place. Anywhere else it
must return exactly one form. The forms are elaborated and checked as if
they had been written there, so a macro can only steer what it
generates. At most 10000 expansions run in one run, every file on the
command line included.

## 63. `Symbol` and `Raw`

```scheme
(def-adts $ (Symbol : -> Type)
  enum
  (many SName : (many (String) s) -> (Symbol))
  (many SGen : (many (Nat) n) (many (String) s) (erased (Gensym n s) g) -> (Symbol)))

(def-adts $ (Raw : -> Type)
  enum extern
  (many RawSymbol : (many (Pos) pos) (many (Symbol) s) -> (Raw))
  (many RawWild : (many (Pos) pos) -> (Raw))
  (many RawList : (many (Pos) pos) (many (List $ Raw) items) -> (Raw))
  (many RawSettled : (many (Pos) pos) (erased (Mult) m) (erased Type A) (erased A a) (many (Settled m A a) c) -> (Raw)))
```

`Pos` is that of §42. `Raw` is `extern` so that its representation is
the reader's own syntax tree: a macro's arguments and output pass
without copying, which would let nested expansions cost exponentially
more than the macros' own work. `RawWild` is a `_`; a raw name `#"_"` is
a `RawSymbol` (§1).

A name in the source reaches a macro as `(RawSymbol p (SName s))`. A
literal reaches it as an `MMany` handle (§64) to its interned entry
(§45): each top-level form of the source has its literals interned and
replaced by such handles just before it is elaborated. So `Raw` has no
literal constructor, and a macro builds a literal by interning it
(§65). A handle to a literal is treated as the literal wherever a
refusal is worded, and is shown as the literal.

A name resolves exactly. `SName s` is the source's own name `s`, and
any `s` can be written raw (§1). `SGen n s g` is a gensym (§65): it is
identified by `n` alone, and no source spelling stands for it. A
message shows it as `__g` and `n` and `_`, followed by `s` spelled as a
name is spelled: `__g1_tmp`, or `__g1_#"a b"` where `s` is not a plain
name. An unbound gensym gets no "nearest in scope" hint.

```scheme
symbol-eq : (many (Symbol) x) (many (Symbol) y) -> (many (Maybe (Eq (Symbol) x y)) r)
```

`symbol-eq` is ordinary prelude code. It answers `Some` for two names
whose texts `str-cmp` finds equal, and for two gensyms whose numbers
`nat-cmp` finds equal, where `gensym-unique` (§65) gives that their
texts are equal too; any other pair answers `None`.

## 64. Handles

```scheme
(def-adts $ (Mult : -> Type)
  enum
  (many MErased : -> (Mult))
  (many MMany : -> (Mult))
  (many MUnique : -> (Mult)))

(def-opaque $ (Settled : ((Mult) m) (Type T) (T t) -> Type))
```

A handle `(Settled m T t)` denotes `t`, of type `T`, held at
multiplicity `m`. `Settled` is opaque, like `Slot`: it has no
constructors and no `Matchable`, and it is not erased by kind. A handle
names the `Settled` entry (§5, §29) it was minted from, and reads it in
one of two ways: as the entry's minted `is`, at its minted type, or as
its minted type, at `Type`.

`(settled-of m x)` is a handle that reads `x`'s minted `is`, where `x`
is a `Settled` entry, named, given by a handle, or written as a literal
(§45), and `m` is a written multiplicity: `erased` for any entry, `many` for an entry declared
`many`, and `unique` for one declared `unique`. Its `Mult` is the
matching constructor. It is not a use of `x`; each splice of the handle
is. The other forms on handles are primitives:

```scheme
(def-prim $ (many settled-type : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
    (many (Settled (MErased) Type T) h)))

(def-prim $ (many settled-erase : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
    (many (Settled (MErased) T t) h)))

(def-prim $ (many settled-mult : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
    (many m is r)))

(def-prim $ (many settled-value : (erased Type T) (erased T t) (many (Settled (MMany) T t) c) -> (many t is v)))
```

`settled-type` turns a handle that reads an entry's minted `is` into
the handle that reads its minted type, and does not canonicalize the
type. `settled-erase` makes the `MErased` handle on the same entry,
read the same way. `settled-mult` gives a handle's `Mult`.
`settled-value` gives the value of an `MMany` handle. There is none for
an `MErased` handle, which would only rename its own erased index, and
none for an `MUnique` handle, whose read would happen outside the
elaborator's use accounting, possibly after the value was consumed and
mutated in place. These four read a handle anywhere, not only during an
expansion, and an `MMany` handle carries its value into an extracted
program. Only built-in forms create handles, so a handle denotes its
index.

`RawSettled` puts a handle in a macro's output. Spliced there, it is a
reference to the term it denotes, bypassing scope, as a variable
reference is to its entry, and it is checked as if `x` had been written
there with the handle's multiplicity: an `MErased` handle may stand only
in an erased position, an `MMany` handle is used at many, and an
`MUnique` handle is used at unique, which consumes it. A handle cannot
be a binder, any more than anything else that is not a name can.

## 65. The macro world

```scheme
(def-opaque $ (MacroWorld : -> Type))
(def-opaque $ (Gensym : ((Nat) n) ((String) s) -> Type))

(def-adts $ (JMEq : (Type A) (A a) (Type B) (B b) -> Type)
  enum
  (many JMRefl : (erased Type A) (erased A a) -> (JMEq A a A a)))
```

The macro world is the elaborator's program store: the run-position
entries with their values and facts, the literal table, the gensym
counter and the expansion count. It is threaded sequentially through
all of elaboration, carried out of every scope where uses are carried,
and passed along rather than joined. Only the expander supplies a
`MacroWorld`, to a macro's function. It has no constructor and is no
entry, so a non-erased one never escapes an expansion, and the forms below that take
one run only there. A function that takes a macro world returns it `at`
its parameter. The forms below are primitives, apart from the two
special forms that end this section, checked as calls:

```scheme
(def-prim $ (many gensym : (unique (MacroWorld) mw) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Nat) n) (erased (Gensym n s) g)))

(def-prim $ (erased gensym-unique : (erased (Nat) n) (erased (String) s) (erased (String) t)
    (erased (Gensym n s) a) (erased (Gensym n t) b) ->
    (erased (JMEq (Gensym n s) a (Gensym n t) b) e)))

(def-prim $ (many settled-eq : (erased (Mult) ma) (erased Type A) (erased A a)
    (erased (Mult) mb) (erased Type B) (erased B b)
    (unique (MacroWorld) mw) (many (Settled ma A a) p) (many (Settled mb B b) q) ->
    (unique mw is mw2 at mw) (many (Maybe (JMEq A a B b)) r)))

(def-prim $ (many intern-nat : (unique (MacroWorld) mw) (many (Nat) n) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (Nat) n) h)))

(def-prim $ (many intern-char : (unique (MacroWorld) mw) (many (Char) c) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (Char) c) h)))

(def-prim $ (many intern-string : (unique (MacroWorld) mw) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (String) s) h)))

(def-prim $ (many mint-settled : (unique (MacroWorld) mw) (erased Type T) (many (Settled (MErased) Type T) th) (many T v) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) T v) h)))

(def-prim $ (many mint-settled-erased : (unique (MacroWorld) mw) (erased Type T) (many (Settled (MErased) Type T) th) (erased T v) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MErased) T v) h)))

(def-adts $ (Resolution : -> Type)
  enum
  (many RSettled : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) h) -> (Resolution))
  (many RHypothetical : -> (Resolution))
  (many RUnbound : -> (Resolution)))

(def-prim $ (many resolve : (unique (MacroWorld) mw) (many (Symbol) s) ->
    (unique mw is mw2 at mw) (many (Resolution) r)))

(def-prim $ (many read-file : (unique (MacroWorld) mw) (many (Pos) here) (many (String) path) ->
    (unique (MacroWorld) mw2 at mw) (many (Result (String)) r)))
```

`gensym` mints a number, counting from 1 over the whole run, every file
included, and returns it with a `Gensym` witness for it and the text
`s`. Nothing else makes a witness, so a gensym cannot be forged:
building an `SGen` at `many` needs one. `gensym-unique` is an axiom,
resting on the counter minting each number once, with one text.

`settled-eq` answers `Some` exactly when the terms the two handles
denote, and their types, are identical after canonicalizing against the
facts of the innermost run position enclosing the call, never
branch-forced ones, so that an answer stays true wherever the macro's
output goes and a call expands the same way in every branch. It first
enters the declaration facts of the literals it needs into those facts.

`intern-nat`, `intern-char` and `intern-string` intern the literal (§45)
where they run, and give an `MMany` handle to its entry.

`mint-settled` and `mint-settled-erased` mint a fresh anonymous `Settled`
entry where they run, holding `v` at `many`, or the token of §5 at
`erased`, and give a handle at the matching `Mult` that reads its minted
`is`. Its minted type is the term `th` denotes. Like a string literal's
entry (§45), it is opaque: it has no `is` rule, and the checker learns
nothing of `v` through it. Each call mints a new entry, even for a value
equal to one minted before, and no fact relates two such entries. Like a
literal's entry, it is outside every scope and has no introduction order
(§18).

`resolve` looks a name up in the scope at the macro call: a `Settled`
entry answers `RSettled` with a handle that reads its minted `is`, at
the entry's declared multiplicity, any other bound entry
`RHypothetical`, and a name not in scope `RUnbound`. The lookup is not a
reference to the entry.

`read-file` reads a file relative to a source file or to a name
`--comptime-unconfine` adds, one per occurrence, without reading or
checking it. `here` must name one of these, spelled as the command line
names it; standard input is not one. `path` is resolved against that
name's directory and must land, through any symlinks, inside that directory or
below it. Otherwise, for `NoPos`, and where the read fails, it
answers `Fail`. The fence (MANUAL.md) does not apply to it.

`(settled-ty-apply mw c a1 ... an)` and `(settled-val-apply mw c a1 ... an)`
take `mw` at `unique` and handles `c : (Settled m C t)` and
`ai : (Settled mi Ai ti)` at `many`. They give
`(unique (MacroWorld) mw2 at mw)` and
`(many (Result (Settled m R (t t1 ... tn))) r)`, where `R` is the type of
`(t t1 ... tn)`. Where the form is written:

- `C` must canonicalize to a `TyCtor` former, or to a `ValCtor` former for
  `settled-val-apply`;
- `(t t1 ... tn)` must check as a term (§9);
- every handle must be `MErased`, except that for `settled-val-apply` `m`
  may be `(MMany)`, and then so is each non-erased field's handle.

Where it runs, the application is checked again, against the facts
`settled-eq` reads. On failure the form answers `Fail` with the
elaborator's report, located at the form; the report's text may change.
Otherwise it answers `Ok` with a handle to a fresh anonymous `Settled`
entry, outside every scope, whose `is` rule is the application. At
`(MMany)` that entry holds the constructor applied to the fields' values.
In an erased position the form mints nothing.

## 66. `Placed`

The prelude declares an opaque type that holds a value at a slot named
in its type:

```scheme
(def-opaque $ (Placed : ((Slot) s) (Type T) (T v) -> Type))

(def-prim $ (many place-at : (erased Type T) (unique T x) ->
    (unique (Placed (slot-of x) T x) p at x)))

(def-prim $ (many place-at-many : (erased Type T) (many T x) ->
    (many (Placed (slot-of x) T x) p at x)))

(def-prim $ (many unplace-at : (erased (Slot) s) (erased Type T) (erased T v)
    (unique (Placed s T v) p) -> (unique v is x at p)))

(def-prim $ (many unplace-at-many : (erased (Slot) s) (erased Type T) (erased T v)
    (many (Placed s T v) p) -> (many v is x at p)))

(def-prim $ (erased placed-slot : (erased (Slot) s) (erased Type T) (erased T v)
    (erased (Placed s T v) p) -> (erased (Eq (Slot) (slot-of p) s) e)))

(def-prim $ (erased placed-eq : (erased (Slot) s) (erased Type T) (erased T v)
    (erased (Placed s T v) p) (erased (Placed s T v) q) ->
    (erased (Eq (Placed s T v) p q) e)))
```

A `(Placed s T v)` holds `v` and is represented as the word of `v`.
Like `Settled`, it has no constructors and no `Matchable`, and it is not
erased by kind. It rests on the prelude's `Eq`, so under `--no-prelude`
there is none.

A call of `place-at`, `place-at-many`, `unplace-at` or
`unplace-at-many` is a **placing**. It erases to a renaming of its
argument, as a `coerce` does (§33).

`placed-slot` and `placed-eq` are axioms. The first says that a
`Placed` value is at the slot its type names, the second that two
`Placed` values of one type are equal.

A `Placed` value lets a function pass a value through code whose
signatures do not mention where it is. A function that promises a
result `at` its parameter `a` can place `a`, hand the `Placed` value to
a function whose signature names only an erased `(Slot) s`, take
back a `(Placed s T w)`, unplace it, and use `placed-slot` to show that
the result is at `a` (`tests/placed_thread.sl`). A constructor field
kept at a slot is declared the same way (§36).

## 67. `slot-eq`

```scheme
(def-prim $ (many slot-eq : (many (Slot) a) (many (Slot) b) ->
    (many (Maybe (Eq (Slot) a b)) r)))
```

`Some` proves that `a` and `b` hold one word (§38). `None` proves
nothing, so an implementation may always answer it, and which one a
call answers may differ between runs. `slot-eq` requires the prelude.

## 68. `cell-same`

```scheme
(def-adts $ (ErasedOr : (Type P) -> Type)
  enum
  (many EONonErased : (erased Type P) (erased P p) -> (ErasedOr P))
  (erased EOErased : (erased Type P) -> (ErasedOr P)))
```

`(cell-same u1 u2)` takes two cells at `many` whose constructors one
opened `enum` `Matchable` lists and whose slots are already equal
(§36). It yields an `(ErasedOr (JMEq T1 u1 T2 u2))` at `vacant-slot`
(§36), `Ti` the type of `ui`: `EONonErased` wherever it runs, and
`EOErased` where it is reached only erased (§14). It compiles to nothing, is refused in an
erased position, and requires the prelude.

## 69. `Slots`

A `Slots` is a table of placed values (§66), each numbered by when it
was added and found by its slot. It targets finding a slot in O(1),
where a search with `slot-eq` (§67) is O(n).

```scheme
(def-adts $ (NthLast : (Type A) ((List A) xs) ((Nat) i) (A x) -> Type)
  enum
  (many NthLastHere : (erased Type A) (erased A x) (erased (List A) xs) (erased (Nat) n) (erased (Length A xs n) p)
     -> (NthLast A (Cons A x xs) n x))
  (many NthLastThere : (erased Type A) (erased A y) (erased (List A) xs) (erased (Nat) i) (erased A x)
     (erased (NthLast A xs i x) p) -> (NthLast A (Cons A y xs) i x)))

(def-adts $ (SlotItem : (Type A) -> Type)
  enum newtype
  (many MkSlotItem : (erased Type A) (erased (Slot) s) (erased A v) (many (Placed s A v) p) -> (SlotItem A)))

(def-adts $ (SlotFind : (Type A) ((List (SlotItem A)) xs) ((Slot) s) (Type U) (U u) -> Type)
  enum
  (many SlotFound : (erased Type A) (erased (List (SlotItem A)) xs) (erased (Slot) s) (erased A v) (erased (Placed s A v) p)
     (many (Nat) i) (erased (NthLast (SlotItem A) xs i (MkSlotItem A s v p)) nl) -> (SlotFind A xs s A v))
  (many SlotMissing : (erased Type A) (erased (List (SlotItem A)) xs) (erased (Slot) s) -> (SlotFind A xs s (Slot) s)))

(def-adts $ (SlotIntern : (Type A) ((List (SlotItem A)) xs) ((Slot) s) ((List (SlotItem A)) ys) -> Type)
  enum
  (many SlotExisting : (erased Type A) (erased (List (SlotItem A)) xs) (erased (Slot) s) (erased A v) (erased (Placed s A v) p)
     (many (Nat) i) (erased (NthLast (SlotItem A) xs i (MkSlotItem A s v p)) nl) -> (SlotIntern A xs s xs))
  (many SlotAdded : (erased Type A) (erased (List (SlotItem A)) xs) (erased (Slot) s) (erased A v) (erased (Placed s A v) p)
     (many (Nat) i) (erased (Length (SlotItem A) xs i) n) -> (SlotIntern A xs s (Cons (SlotItem A) (MkSlotItem A s v p) xs))))

(def-adts $ (Slots : (Type A) ((List (SlotItem A)) xs) -> Type)
  enum extern
  (many MkSlots : (erased Type A) (many (List (SlotItem A)) xs) -> (Slots A xs)))
```

```scheme
slots-new : (erased Type A) -> (unique (Slots A (Nil (SlotItem A))) l)
slots-find : (erased Type A) (erased (List (SlotItem A)) xs) (unique (Slots A xs) l) (many (Slot) s) ->
    (erased Type U) (many U x at s) (many (SlotFind A xs s U x) r) (unique l is l2 at l)
slots-intern : (erased Type A) (erased (List (SlotItem A)) xs) (unique (Slots A xs) l)
    (erased (Slot) s) (erased A v) (many (Placed s A v) p) ->
    (erased (List (SlotItem A)) ys) (many (SlotIntern A xs s ys) r) (unique (Slots A ys) l2 at l)
slots-length : (erased Type A) (erased (List (SlotItem A)) xs) (unique (Slots A xs) l) ->
    (many (Nat) n) (erased (Length (SlotItem A) xs n) p) (unique l is l2 at l)
```

The models search with `slot-eq`, so §42's exception for `slot-eq`
covers what the implementations answer. How an implementation finds a
slot is left to it. Taking a `Slots` apart through `MkSlots`, or building
one with it, goes through the model and costs time linear in the table;
the prelude warns at each.

## 70. `fn-same`

`(fn-same f g)` takes two values at `many` whose types canonicalize to
one `Fn` or `UniqueFn` type (§11, §32), the same for both, and whose
slots are already equal (§36). It yields an `(ErasedOr (Eq F f g))` at
`vacant-slot` (§36), `F` the type of `f`: `EONonErased` wherever it
runs, and `EOErased` where it is reached only erased (§14). It compiles
to nothing, is refused in an erased position, and requires the prelude.
It is available only under `--fn-same` (MANUAL.md); without the flag it
is an error.

## 71. Goals

`(goal m T)` sets the **goal** of a unit, the files on one command line. `m` is `erased`, `many` or `unique`. `T` is a type (§9) elaborated in run position where the form stands (§27), so later shadowing does not change it. `(qed e)` discharges the goal: `e` is checked against `T` at `m`, as a body's final expression checks against its return telescope (§26), and runs as any form in run position does (§27). A `qed` before the goal is set is an error. `goal` and `qed` are each allowed only as a bare top-level form of a file, at most once per unit. The elaborator counts both itself, so a renamed one or one produced by a macro counts the same.

`--goal` (MANUAL.md) is `none`, `open` or `proved`. Under `none`, the default, a goal requires nothing and the driver is as §27 describes. Under `open` and `proved`, the driver is off: a final expression runs as any form in run position does, and nothing is printed, applied or written after elaboration. `open` requires a goal and no `qed`. `proved` requires a goal and a `qed`. On success, each reports the goal and where it is set, and `proved` also where it is discharged (MANUAL.md).

A goal is one type, not a telescope; an existential, such as a function with its level, is packaged by an ADT (§21).
