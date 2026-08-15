# Language design notes

Design decisions here come directly from the repo owner. This file is a
running record, added to as design sessions happen.

## 1. Syntax

Scheme syntax (s-expressions).

## 2. `$` for closing-paren reduction

Borrowed from Haskell's `$`. `$` parses exactly like `(`, opening a new
list form, except it does not consume the `)` that ends it: it reads
items until its *enclosing* form's terminator, then leaves that
terminator in place for whichever form opened it to consume. With no
enclosing form, the missing `)` is reported as missing, since none
exists. Only a bare `$` token is special — `$` inside a run of other
characters (e.g. `foo$bar`) is just part of an ordinary atom.

## 3. Scope environment

The scope environment is a list of variables (shadowing allowed). Each
variable is in exactly one of three states:

- **comptime**: has a stored type, a stored *value*, and an "is"
  statement (a canonicalization/rewrite rule introduced via matching on
  a dependent type).
- **dynamic**: has a stored type and an "is" statement, but no stored
  value.
- **inacc** (inaccessible): same shape as dynamic (type + "is"
  statement), but the variable cannot be accessed at all — the
  motivating case is a dynamic variable from an enclosing scope becoming
  inaccessible inside a comptime block.

## 4. Orthogonality: Kernel-level dynamism with static types

Goal: match Kernel's level of dynamism while still supporting clean
compilation with static types. The mechanism for reconciling these is
analyzing the *constantness* of the head of an s-expression:

- Macros and special forms are first-class values — they can be passed
  around at runtime like any other value.
- To actually *invoke* something as a macro/special form (as opposed to
  merely holding it as a value), the head of the s-expression must be
  constant-known.
- Constant-known-ness is relative to where you are: something can be
  dynamic while evaluating inside a comptime block, yet become
  constant-known once evaluation leaves that block.

## 5. Restricted dependent types

Dependent types are supported, but restricted: a type may never involve
function invocation. A type can only be built from:

1. variable references,
2. application of a type constructor,
3. application of a value constructor.

The same restriction applies to "is" statements (the
canonicalization/rewrite rules from §3). The intended consequence of this
restriction is a simple type-checking rule: canonicalize, then compare
for identity.

## 6. Erasure

Erasure follows Idris 2's approach, living on the binding — i.e. the 0/ω
multiplicity distinction from Idris 2's quantitative type theory.
Linear/unique types are punted on for now.

## 7. Function levels

Every function has an associated level — a natural number, normally
erased — that is part of the function's type signature. A function may
call functions of a strictly lower level freely, and may call functions
of its own level only under the restrictions in §9 (an explicit `Subterm`
proof, in place of the `Predates` proof a lower-level call needs).
Currying is not supported, for functions or for type/value constructors.
Type and value constructors have no associated level.

The point of levels (and of the same-level call restrictions deferred
above) is termination. ADTs with zero variants are supported (e.g.
`False`). A function's parameters can be individually annotated
`subterm`; this is part of the function's signature. A function call
decrements a lexicographic ordering whose most significant component is
the function's level, followed by its `subterm`-annotated arguments in
left-to-right order.

## 8. Built-ins backing termination

Names below are placeholders (see CLAUDE.md §10) — the owner is open to
better ones. These reify §7's level/subterm machinery as actual types,
usually fully erased:

- `Level`: essentially an integer.
- `Predates` (tentative name, replaces `LevelLT`/`After`):
  `(A: Type) (a: A) -> Level -> Type` — asserts a level decrease.
- `Subterm` (heterogeneous): `(A: Type) (a: A) (B: Type) (b: B) -> Type`.

Three core axioms/functions:

1. Predates transitivity: `Predates a b -> Predates b c -> Predates a c`
2. Subterm transitivity: `Subterm _ a _ b -> Subterm _ b _ c -> Subterm _ a _ c`
3. Predates transitivity through subterm:
   `Predates _ a L -> Subterm _ a _ b -> Predates _ b L`

There are also two ways for these to be "born" (introduced):

- **`Subterm` birth.** A special form takes two expressions, asserting
  the first is a subterm of the second. Both are canonicalized/rewritten
  first; both are restricted to the "is"/type grammar of §5 (variable
  references and type-/value-constructor application — no function
  invocation). The birthed claim then requires the first, post-
  canonicalization, to be a strict subtree of the second.

- **`Level` birth.** A `def-lvl` form births a fresh `Level`. Mental
  model (a model only — fully erased in practice, not a real runtime
  counter): imagine a single global counter that increments each time a
  `def-lvl` is "invoked"; its value at that point is the birthed level.
  The language being immutable and acyclic is what makes "before"/"after"
  a well-defined ordering here: a variable in scope above (lexically
  enclosing, prior to) a `def-lvl` statement counts as "before" it.

  A second special form — tentatively also named `Predates` (argument
  order still open, see CLAUDE.md §10) — births the `Predates` claim
  relating a variable to a level. It takes: 1) a `Level` value that must
  itself have been born by a `def-lvl` that is before the current code,
  and 2) a variable that was in scope at the time that `def-lvl` ran.

## 9. Namespaces, special forms, macros, call-site proofs

- **One namespace.** Special forms, types, and values all share a single
  namespace. Everything in it can be renamed/shadowed, special forms and
  types included.
- **State-inheriting `let`.** A `let` binding whose right-hand side is a
  single term causes the left-hand side to inherit the right-hand side's
  entire variable state (comptime/dynamic/inacc from §3, wholesale — type,
  stored value if comptime, "is" rule). This holds even when the
  right-hand side is `inacc`: renaming an inaccessible variable this way
  is not a compile error (motivation deferred — relates to macros).
- **Special forms as data.** A special form is a nullary variant of a
  `Special` type (in effect an enum). The elaborator dispatches on seeing
  a `Special` variant in head position. Open question: whether `Special`
  should be exposed to the user as an ordinary type or stay
  implementation-internal.
- **Macros as data.** `Macro` is a type with one constructor with one
  field, a function — tentatively `List Raw -> Raw`, from a list of
  unelaborated ("raw") terms to a raw term.
- **Macro termination (interim).** The owner has a real design for this
  but it's complicated and deferred to v2. For now: a single global
  counter of macro expansions, checked against a limit configurable via
  a command-line flag with some sane (TBD) default; hitting the limit is
  the only termination guard on macro expansion.
- **Call-site proofs.** This is how §7's level-decrease requirement gets
  discharged, and it differs by whether the call is a level-decreasing
  call or a same-level call:
  - A call to a strictly-lower-level function needs a `Predates` proof,
    and no `Subterm` proof.
  - A same-level call needs no `Predates` proof, but needs exactly one
    `Subterm` proof instead. The call syntax must say explicitly which
    argument is the subterm-decreasing one; every `subterm`-annotated
    argument preceding it (§7's left-to-right order) must be identical,
    post-canonicalization, to its counterpart at the call site — i.e. the
    usual lexicographic-decrease discipline: equal up to the chosen
    position, strictly decreasing there.
  - Either kind of call can be made through a function pointer (a
    first-class function value), not only by naming the function
    directly.
- **`tail` marker.** A call can be marked `tail`, asserting the
  programmer's claim that it compiles to a tail call. If the compiler
  cannot honor that claim, it is a hard compile error, not a silent
  fallback.

## 10. `Type : Type`, no strict positivity

`Type : Type` (no universe stratification), and there is no strict-
positivity requirement on function or datatype signatures.

The owner's own summary of why: termination is carried entirely by the
lexicographic level/subterm decrease of §§7–8, not by any restriction on
recursive occurrences in a datatype, and types cannot compute because of
§5's ban on function invocation inside types. On that basis the owner
asserts — explicitly *without* a soundness argument yet, expected to be a
future, separate design session — that the language is nevertheless
sound despite `Type : Type` and unrestricted positivity. Recorded here as
the owner's claim/target, not a settled or verified result.

## 11. Multiple return values (built-in sigma)

A function can return multiple values, including zero, and later return
values can depend on earlier ones — this is, in effect, a built-in sigma
(dependent tuple) type rather than something layered on top. As usual,
each entry — argument or return value — may only depend on the entries
before it, left to right.

`match` requires an explicit result-type annotation: it lists the return
type(s) (plural, to match a function's possibly-multiple return values)
together with each one's erasure (the 0/ω multiplicity from §6).

## 12. Data types, erasure, and match branch kinds

**Two kinds of data type.** **Enums** have a non-erased discriminant,
stored at runtime. **Unions** have an erased discriminant. Independent of
that: each constructor can individually be marked erased or not, and each
field (like each function argument) is individually annotated erased or
not (sane default still TBD). Subterm recursion (§7) can go through an
erased argument.

**Match-proved equality isn't substitutability.** When a match proves two
expressions equal (they rewrite/canonicalize identically, §5), that alone
doesn't make them substitutable for one another — their erasure ("silo"?
— tentative term, see CLAUDE.md §10) can still differ, and that's a
separate axis from canonicalization equality.

**Matching on enums** is (mostly) straightforward. For a non-erased
scrutinee:
1. Variables introduced via a non-erased constructor inherit the field's
   declared erasure.
2. Variables introduced via an erased constructor are always erased,
   regardless of the field's own annotation (open question: maybe such
   fields should be required to be annotated erased, rather than silently
   overridden).

But: when evaluating a branch reached through an erased constructor,
everything in scope — and, more importantly, the expected type of the
branch's own result — is erased.

Matching on unions, and matching on an erased enum scrutinee, is more
involved.

**Three kinds of match branch** (orthogonal to whether the matched
constructor is itself erased; names all tentative, see CLAUDE.md §10):
1. **present** — an ordinary branch.
2. **absurd, automatic** — a branch refuted structurally by the type
   checker; written with special syntax, likely omitting the
   would-be-introduced variable names (fewer parens, etc.), since there's
   nothing to bind.
3. **absurd, by proof** — a branch that, instead of producing the match's
   expected result, must produce a value of the empty ADT (§7's
   zero-variant type, e.g. `False`) — the programmer supplies a proof of
   impossibility rather than relying on automatic refutation.

**When a non-erased result is on the line.** If a match is entirely
erasable, it's unconstrained. But if at least one branch is non-erased
(produces a non-erased result, or does something non-erased), then
either: the scrutinee must be "known" — i.e. a non-erased enum, so
there's a real runtime tag to dispatch on — or there is at most one
non-absurd branch (so no runtime choice is actually needed).

**First-classness and type erasure.** Types, type constructors, and value
constructors are all first class. All arguments to a type constructor are
always erased. Types themselves should be erased.
