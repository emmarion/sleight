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

The scope environment is a list of entries (shadowing allowed). Each
entry carries:

- a **name** — optional; anonymous entries are allowed.
- a **state**: `comptime`, `dynamic`, or `inacc` (inaccessible — the
  motivating case is a `dynamic` entry from an enclosing scope becoming
  inaccessible inside a comptime block).
- a **type** — like an "is" statement (below), just a tree whose leaves
  are references to entries in this same table (§5).
- an **erasure** (the `erased`/`many` multiplicity from §6) — orthogonal
  to state.
- an **"is" statement** — a rewrite/canonicalization rule (§5), which is
  just a tree whose leaves are references to entries in this same table
  (possibly this entry itself).
- a **stored value**, present only if the state is `comptime`. If the
  entry is also erased, this isn't a real value — it's a *token* that
  just asserts the value exists/is true, not actual data.
- an (implicit) **introduction order** — needed to make the `Predates`
  assertion (§8) well-founded.

A type-constructor or value-constructor application expression also gets
its own (typically anonymous) entry, with an `is` statement set to that
application. So "is"/type trees aren't a separate expression structure
sitting apart from the scope table — every application anywhere is
itself a scope entry, letting the rewrite engine "see into" and
canonicalize through them uniformly (§18), the same as for any named
variable. Consequence worth calling out explicitly: the scope table's
reference graph *is* the whole expression structure for anything in the
restricted `is`/type grammar — no separate AST is needed alongside it for
the rewrite engine to work with.

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

**The elaborator's actual head-dispatch algorithm**, elaborating a list
by examining its head:
1. Look at the head's *type*: if it's a type constructor, a value
   constructor, or a function type, that's ordinary application — proceed
   (this needs no comptime-known-ness at all, matching §9: any of these
   can be called through a first-class pointer).
2. Otherwise, if the head is *additionally* comptime-known: if its value
   is a `Special` or a `Macro` (§9), proceed — this is the
   constant-known-head requirement above, made precise.
3. Otherwise, it's an elaboration error.

This resolves §27's open question: constructor/function application
isn't dispatched through the `Special` mechanism at all — it's a
separate, type-driven tier (1) that runs before the comptime-known
`Special`/`Macro` tier (2) is even considered.

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

The language assumes Axiom K (uniqueness of identity proofs) — relevant
to the dependent pattern matching / rewrite rules used inside match
branches (§12).

## 6. Erasure

Erasure follows Idris 2's approach, living on the binding — i.e. the
0/ω multiplicity distinction from Idris 2's quantitative type theory,
written as the tokens `erased` and `many` (self-annotating and
ASCII-only, §28, rather than terse symbols easily confused with the
number `0` or the operator `*`). For now, multiplicity is always written
explicitly, wherever it's an actual choice — no default-when-omitted, to
cut down on mistakes while the design is still in flux. Linear/unique
types are punted on for now.

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
- **Special forms as data.** A special form is a nullary variant of the
  `Special` ADT (settled: an ordinary ADT, not opaque). The elaborator
  dispatches on seeing a `Special` variant in head position. `Special`'s
  variants cover §16's construct inventory (`Match`, `Let`, `def-lvl`,
  etc.), plus lower-level tokens that also need first-class status:
  `erased`, `many` (§6), `:`, and `is` (§14) — §27's registry.
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
  - Every kind of application — type-constructor, value-constructor, a
    lower-level call, a same-level call, `tail`- or `delegate`-marked —
    works fine through a first-class pointer/value, not only by naming
    the callee directly. None of these require a constant-known callee
    at the head — that requirement is specific to invoking a macro or
    special form (§4), not to ordinary application.
- **`tail` marker.** A call can be marked `tail`, asserting the
  programmer's claim that it compiles to a tail call. If the compiler
  cannot honor that claim, it is a hard compile error, not a silent
  fallback. Tail-ness is judged *after* stripping erasure (§23): you can
  store a tail call's result, do further work with only phantom/erased
  values, and then return, and it still counts as `tail` — the actual
  requirement is just that the (non-erased) return value(s) and their
  order match what the called function itself returns.
- **`delegate` marker.** Same idea as `tail`, plus the same restriction
  applied to the call's arguments: the non-erased arguments must also
  pass straight through. The consequence is stronger than `tail` — after
  stripping erasure, the marked function's body reduces to nothing but
  the delegated call, so the two functions' non-erased behavior is
  identical, and the outer function's function pointer could just *be*
  the inner one's.

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
before it, left to right. This is a function-only feature: type and
value constructors always have exactly one return (§29) — `Type` for a
type constructor, the constructed type itself for a value constructor.

`match` requires an explicit result-type annotation: it lists the return
type(s) (plural, to match a function's possibly-multiple return values)
together with each one's erasure (the `erased`/`many` multiplicity from
§6).

## 12. Data types, erasure, and match branch kinds

**Two kinds of data type.** **Enums** have a non-erased discriminant,
stored at runtime. **Unions** have an erased discriminant. Independent of
that: each constructor can individually be marked erased ("phantom") or
not, and each field (like each function argument) is individually
annotated erased or not (sane default still TBD). Subterm recursion (§7)
can go through an erased argument.

**Type indices aren't shared scope.** An indexed ADT's index variables
aren't bound once at the type's own head the way an ordinary (uniform,
`List`-style) parameter is — they go out of scope right after the head.
Each constructor that needs to reference or constrain an index has to
redeclare its own variable for it, with an explicit type, inside that
constructor's own signature — it doesn't get to reuse a shared name from
the head.

**Match-proved equality isn't substitutability.** When a match proves two
expressions equal (they rewrite/canonicalize identically, §5), that alone
doesn't make them substitutable for one another — their erasure ("silo"?
— tentative term, see CLAUDE.md §10) can still differ, and that's a
separate axis from canonicalization equality.

**Matching on enums** is (mostly) straightforward. For a non-erased
scrutinee:
1. Variables introduced via a non-erased constructor inherit the field's
   declared erasure.
2. Variables introduced via a phantom constructor are always erased,
   regardless of the field's own annotation (open question: maybe such
   fields should be required to be annotated erased, rather than silently
   overridden).

But: when evaluating a branch reached through a **phantom** constructor
(a constructor marked erased in its own declaration — distinct from a
scope entry merely being erased, §3), everything in scope — and, more
importantly, the expected type of the branch's own result — is erased.
Concretely: such a branch's body can, and in fact must, return entirely
erased values, and that's considered valid even when the match itself was
annotated (§11) to return some non-erased result(s) — this branch is
exempted from matching the match's declared erasures. §20 covers the
underlying erasure-propagation model this fits into.

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
erasable, it's unconstrained. But if at least one branch does non-erased
computation (or has a non-erased return):
- if the discriminant is non-erased (a non-erased enum), there's a real
  runtime tag to dispatch on, and no further restriction applies;
- if the discriminant is erased — an erased enum, or a union regardless
  of its own erasure — there can be at most one "real" branch. Every
  other branch must be one of: 1) automatically absurd (the rewrite rules
  derive a contradiction), 2) absurd by proof, or 3) a branch matching a
  phantom constructor (its body is already fully erased per the
  enum-matching rule above, so it needs no runtime dispatch of its own).

**First-classness and type erasure.** Types, type constructors, and value
constructors are all first class. All arguments to a type constructor are
always erased, and a type constructor itself always enters scope as
erased — same for a phantom (marked-erased) value constructor (§20).
Types themselves should be erased.

## 13. TBD (v2 candidate): a unified lexicographic-decrease proof

§9's call-site proof is currently two separate cases (a `Predates` proof,
or a single `Subterm` proof plus a side condition that earlier
`subterm`-marked arguments canonicalize identically). A possible future
replacement: one proof structure that directly reifies the whole
lexicographic order as a nested OR — level decreases, OR (levels equal
AND (first `subterm`-marked argument is a `Subterm`, OR (that argument is
equal AND the second is a `Subterm`, OR (…)))). Not designed yet.

Motivation: §9's current scheme forces the call site to statically name
which argument is the decreasing one. But which argument decreases may
itself only be known via some erased computation — the call can still be
known valid without any single position being fixed in advance. A nested
disjunction wouldn't require committing to one; it would carry whichever
disjunct that erased computation produced.

## 14. "Is" as an alternative to a type annotation

Wherever a variable is introduced into scope, instead of giving its
(possibly dependent) type, one can instead say the variable "is" another
value; the variable's type is then computed from that "is" expression.
"Is" expressions follow the same restricted grammar as types (§5):
variable references and type-/value-constructor application, no function
invocation. `let` is the one binding site where a type (or "is" clause)
is optional altogether, since it can be inferred from the right-hand
side.

Motivating example, given `Add : Nat -> Nat -> Nat -> Type`:

```
reify-add : (many a b : Nat) (erased c : Nat) (erased p : Add a b c) ->
            (many d is c)
```

`c` and the proof `p` are erased (multiplicity `erased`); the return
value `d` "is `c`" but is declared with multiplicity `many`. The "is"
clause gives `d` its type (`Nat`, via `c`) while letting its erasure
differ from `c`'s — this is the mechanism for reifying an erased witness
into a materialized runtime value.

## 15. Match/call results, and a compile-time discriminant assertion

For now: both a function call's result and a match statement's result
are always `Dyn` — never `Const`, never `Inacc`. No automatic constant-
folding through calls or matches yet. One consequence: a match's
scrutinee itself can only be `Const` or `Dyn` (never `Inacc`, which can't
be accessed at all — §3).

A special form, `comptime-match`, works specifically on a `Const`
(comptime-known) scrutinee whose discriminant is non-erased — i.e. an
enum, never a union (§12): it asserts the value has a given discriminant,
and is a compile error if it doesn't. It binds the matched constructor's
fields as `Const`, the way a state-inheriting `let` would (§9). The
intent is "proof via reflection/computation" — matches what's
called "proof by reflection" in Coq (a real, externally-confirmed term
for this general technique — a decidable proposition discharged by the
compiler just computing/normalizing, rather than the programmer
constructing a proof term by hand; whether this design's mechanism lines
up with Coq's in the details is still just a plausible guess).

Open items, not yet resolved:
- Before binding a match branch's fields, we need a rule for how an
  introduced variable's erasure relates to the scrutinee's own erasure.
- Whether `is`-declared constructor fields (§14) and forced type-index
  unification in a match are literally the same mechanism — suspected
  yes, not yet confirmed.

## 16. Core language construct inventory

Everything in the language is an expression — there's no separate
statement category. The construct list below is split by whether
evaluating it extends the ambient scope for later/surrounding code:

- **Scope-extending** (bindings visible to subsequent/surrounding code):
  `let`; `def-lvl`; `def-fns` (defines one or more, possibly mutually
  recursive, functions — a single function is just the one-element case,
  §28); `def-adts` (likewise, for one or more mutually recursive ADTs,
  §28); `match` (branch-local field variables, and possibly refined `is`
  facts on pre-existing variables, §14); `comptime-match` (§15). Every one
  of these can appear at top level or
  nested inside a function body — nothing here is top-level-only. None of
  these take an explicit body/continuation the way a classic `let` would
  — see `begin`, below, for what actually delimits their scope.
- **Locally scoped** (bindings usable only within the construct's own
  extent, not exported to arbitrary surrounding code): the three
  type-formers — function, type-constructor, value-constructor (§29) —
  each with parameters usable in a later parameter's type or the return
  type, §11, but nowhere else; a `Matchable`-type former (§17); `begin`
  — a sequence of expressions, evaluating to its last one, that hosts the
  scope-extending forms above: each one just adds its binding to the
  ambient `begin`, visible to the rest of the sequence, and gone once the
  `begin` itself ends. Function bodies, `comptime` bodies, match branch
  bodies, and the top-level scope of a file are all *implicitly* `begin`
  — none of them need the keyword written out explicitly.
- **Ordinary, scope-neutral expressions**: `Subterm` birth and `Predates`
  birth (§8); `comptime` (one argument, forces its compile-time
  evaluation); the three function-call forms — lower-level with a
  `Predates` proof, same-level with a `Subterm` proof, and the TBD v2
  multi-proof form (§9, §13); type-constructor application;
  value-constructor application; the three transitivity axioms (§8, for
  now special forms rather than ordinary prelude functions); a
  still-unnamed form that bundles multiple values into a function's or
  match's multi-value return (§11).

## 17. First-class objects

Everything below can be passed around as ordinary first-class data:

1. an ADT value
2. a function
3. an ADT type constructor, unapplied
4. an ADT value constructor, unapplied
5. a `Matchable` object — see below
6. a `Type`
7. an opaque object (a `Level`, or a `Subterm`/`Predates` proof, §8)

`Special` and `Macro` (§9) are both ordinary ADT values. Applying a held,
unapplied constructor (items 3–4) is ordinary constructor application,
nothing special — no distinct mechanism needed despite the lack of
currying (§7).

Some scope entries need an external annotation beyond the fields in §3 —
e.g. marking that a given entry *is* the `Type` universe itself (as
opposed to merely having `Type` as its own type, which is true of many
entries), or marking which `Matchable` is the canonical one describing
`Special`'s own shape. Not yet worked out mechanically.

Item 5, tentatively typed `Matchable [union|enum] T [C1(e1) ... Cn(en)]`
(a tag for union-vs-enum, the type constructor being described, and its
value constructors in declared order with each one's erasure), has two
jobs: it's what lets the compiler know a type's constructors are
disjoint (§19), and it's what lets you match on a first-class object
whose type is described only via first-class type/value constructors —
i.e. not a syntactically fixed, named ADT.

## 18. Match-branch rewrite algorithm (working formulation)

The current working picture for how entering a match branch updates the
in-scope rewrite rules:

- The scope table (variables, their types, their `is` statements) is the
  sole source of truth the rewrite/type-checking engine needs — almost
  everything is answerable from just that.
- Before an occurs-check, and before recursing into any equation's LHS or
  RHS, both sides are first canonicalized/rewritten to normal form via
  the applicable `is` statements.
- This canonicalization engine deliberately does not consult a comptime
  variable's actual stored value — it works uniformly across `Const` and
  `Dyn`, driven solely by `is` facts, even though `Const` carries
  strictly more information. A deliberate simplification, not an
  oversight.
- Entering a branch **forces** a unification: the scrutinee is equated
  with the branch's constructor applied to the newly-bound fields, and
  the scrutinee's type is equated with the type computed from that same
  constructor application. "Forces" means this isn't a passive check —
  it's licensed to add new `is` facts outright (recursively, into
  matching non-atom arguments) wherever doing so isn't already provably
  impossible. A freshly-introduced (atom) variable, or a pre-existing
  atom with no conflicting `is` fact, always succeeds this way, with no
  recursion needed for that step.
- This is sound because a branch's unification only ever happens as the
  consequence of a branch that was actually, genuinely entered — gated by
  a real discriminant check (a runtime tag comparison for a non-erased
  enum, or `comptime-match`'s compile-time computation) — not performed
  as a free-floating comparison between two arbitrary atoms.
- The only two ways forcing a unification fails, i.e. produces a
  contradiction: (1) `x` equated with an expression containing `x`
  (checked after resolving through any existing atom-to-atom `is`-alias
  chains, not just against a new equation's literal surface form; `x = x`
  itself is a no-op, not a contradiction); (2) two already-known, distinct
  constructors equated (arity mismatch is one easy sufficient symptom of
  this given fixed arities and no currying, not a separate case).

## 19. `Matchable` and constructor disjointness

Since constructors are first class (§17), two constructor-*valued
variables* aren't necessarily known to be the same or different just from
being syntactically distinct — the constructor a variable holds might
itself be dynamic/unresolved. A scope-table field listing known-disjoint
constructors was considered for this and set aside: it couldn't itself be
passed around as a first-class object, in tension with §9's
everything-is-first-class goal.

The resolution is `Matchable` (§17): the disjointness judgment itself
stays a fixed structural rule (§18's rule 2, not an `is` statement), but
what it quantifies over — a type's full, ordered, disjoint constructor
list — is reified as genuine first-class data via `Matchable`, rather
than staying hidden compiler bookkeeping.

There's no third "stuck/indeterminate" outcome for comparing two
constructor-headed terms, only §18's forced-unify-or-contradict: if
neither side is yet known to conflict with the other, unification simply
succeeds by adding the needed `is` fact(s).

A `Matchable` doesn't need to be threaded through explicitly — having one
for the relevant type anywhere in ambient scope is enough for the
compiler to consult it. If multiple, mutually-inconsistent `Matchable`s
for the same type are simultaneously in scope and it's genuinely
ambiguous which one a match should use, that ambiguity is itself a
compile error, not something resolved arbitrarily/silently.

## 20. Bottom-up erasure

Erasure doesn't need pervasive annotation — it's computed bottom-up.
Explicit erasure annotation is only needed at the boundary: function
arguments and return results (and, symmetrically, constructor fields,
§12). Everywhere else it's derived, not declared.

This works because the language is immutable, effect-free, and total
(§7–§8): there's no observable difference between computing a value and
not computing it if the value is never needed, so "erased" just means
"not needed," and that's decidable from how a result is actually used
rather than something that has to be stated everywhere by hand.

The propagation rule for a function call or constructor application:
1. If the overall result is erased, there's no further constraint —
   any function/constructor, any argument erasures, all fine.
2. If the overall result must be non-erased: each field/argument that's
   declared non-erased in the callee's own signature must itself be
   non-erased at the call site, *and* the function or constructor being
   called must itself be non-erased.

Consequence of rule 2: a phantom (marked-erased) constructor can only
ever produce an erased result — it fails the "function/constructor
itself must be non-erased" half of the rule. An ordinary (non-phantom)
constructor can produce either, depending on context. Phantom
constructors, and all type constructors regardless of individual marking
(§12), always enter scope as erased.

This extends down to plain variable reference, not just calls: any
variable, erased or not, can be referred to from an erased context. One
(perhaps confusing) mental model: a non-erased value can be "copied" into
an erased one for free, but never the reverse — going the other way needs
something like §21's still-undesigned coercion mechanism, or §14's `is`
reification.

## 21. v2 TODO: coercion and coercibility proofs

Some variant of `coerce` plus a proof-of-coercibility: two values counted
as the same modulo erased values, and/or modulo entering/leaving a
Haskell-newtype-style wrapper type. Not designed yet.

## 22. Evaluation strategy

The language is eagerly evaluated.

## 23. Invariant: erasure is conservative

Erasure (§6, §12, §20) is, in a sense, just an optimization — a
substantial one, but not semantics-changing. Invariant: take any program
that validly compiles, strip out every erasure marking and phantom
designator, and give `Level` and friends (§8) some ordinary non-erased
representation instead — the result should still compile and run
identically to the original. Recorded as an intended invariant/target,
not something verified yet (in the spirit of §10).

The non-erased stand-in for `Level` and friends would most likely just be
`Unit` (an enum with one constructor, no fields) — but other
representations (e.g. `Level` as a wrapper around an actual `Nat`) would
satisfy the invariant too.

## 24. Comptime blocks call freely at top level

At the "top level" of a `comptime` block (§16, §20) — i.e. directly in
the block's own body, not inside a function defined within it — any type
or value constructor can be invoked (unsurprising, since constructors
have no level, §7), and so can any function, with no `Predates` or
`Subterm` proof required at all. In a sense, comptime-block top level
sits at the "highest" level, above every ordinary function level.

The owner's own reasoning for why this should still be sound: there's no
way for an ordinary (leveled) function's body to call *into* a comptime
block, so this unrestricted-calling privilege can never be reached
through the leveled function-call graph that §7's termination machinery
actually checks. Recorded as the owner's claim, not a verified result.

## 25. Bottom-up type inference

The compiler does bottom-up type inference. Explicit types are required
only at: ADT definitions, function arguments, function return results,
and match return results (§11). Everywhere else, inference should
suffice — the same "annotate only at the boundary" shape as §20's
bottom-up erasure.

## 26. v2 TODO: `_` sugar

Allow `_` as sugar in a few spots: a match return annotation (§11,
sometimes); a newly-defined function's level, implicitly creating a
fresh `def-lvl` and defining the function at it; the proof argument
(`Predates`/`Subterm`, §9) of a function call; extracting the level of a
function (it's part of the function's type, §7, but `_` may be useful
sugar for pulling it out). Not designed yet.

## 27. Special form registry

Every special form (§9's `Special` ADT variants) established so far, in
one place. Grouped by §16's scope categories; each entry cross-references
where it's actually specified.

**Scope-extending:**
1. `let` — introduces a binding; type/`is` optional, inferred from the
   right-hand side (§9, §14); state-inheriting when the right-hand side
   is a single bare variable (§9).
2. `def-lvl` — births a fresh `Level` (§8).
3. `def-fns` — defines one or more (possibly mutually recursive)
   functions; a single function is just the one-element case (§28).
   Possibly nested inside another function's body (§9, §16).
4. `def-adts` — defines one or more (possibly mutually recursive) ADTs,
   same one-element-case pattern as `def-fns` (§28); possibly nested;
   index variables aren't shared across constructors (§12, §16).
5. `match` — pattern match; three branch kinds: present, absurd
   (automatic), absurd (by proof) (§12).
6. `comptime-match` — compile-time discriminant assertion on a `Const`,
   non-erased-discriminant scrutinee; binds the matched fields as `Const`
   (§15).

**Locally scoped:**
7. The function-type former (§7, §11, §16, §29).
8. The type-constructor-type former (§29).
9. The value-constructor-type former (§29).
10. A `Matchable`-type former (§17).
11. `begin` — sequences expressions, hosts the scope-extending forms
    above, evaluates to its last expression; implicit (no keyword needed)
    in function bodies, `comptime` bodies, match branch bodies, and a
    file's top level (§16).

**Scope-neutral:**
12. `Subterm` birth (name doubles as the type it births, §8) — asserts
    one expression is a subterm of another.
13. `Predates` birth (name doubles as the type it births, §8) — relates
    a variable to a `Level` born by an earlier `def-lvl`.
14. `comptime` — forces its one argument to evaluate at compile time; its
    body is an implicit `begin` (§16, §24).
15. Function call — three proof flavors (a `Predates` proof for a
    lower-level call, a `Subterm` proof for a same-level call, a TBD v2
    multi-proof form, §9/§13); can be marked `tail` and/or `delegate`
    (§9).
16. Type-constructor application (§5, §12).
17. Value-constructor application (§5, §12).
18. A multi-value bundling form (name TBD) — packages multiple values
    into a function's or match's multi-value return (§11).
19. The three transitivity axioms — `Predates` transitivity, `Subterm`
    transitivity, `Predates`-through-`Subterm` (§8). Special forms for
    now, rather than ordinary prelude functions.

Items 16–17 (constructor application) are *not* actually dispatched
through the `Special` mechanism the rest of this list uses — see §4's
head-dispatch algorithm for the real two-tier answer.

**Telescope-entry tokens** (also `Special`, but lower-level than the
above — they annotate a telescope entry rather than heading a list):
20. `erased` — the 0-multiplicity (§6).
21. `many` — the ω-multiplicity (§6).
22. `:` — separates a telescope entry's name from its type.
23. `is` — separates a telescope entry's (or any binding's) name from an
    `is` expression instead of a type (§14).

## 28. ASCII only

The language's own syntax is ASCII-only. Consequence already applied
throughout this file: the multiplicities are written as the self-
annotating keywords `erased`/`many` rather than Idris's `0`/`ω` symbols
(§6).

## 29. Three type-formers

Types are first class (§17), so there need to be actual expressions that
produce them — not just declaration-site sugar. One type-former isn't
enough, because a function's telescope, a type constructor's telescope,
and a value constructor's telescope aren't structurally the same grammar,
not just semantically different:

1. **Function-type former** (§16) — takes a level (§7), plus a telescope
   where each entry freely chooses its own multiplicity and can be marked
   `subterm`; produces a function type.
2. **Type-constructor-type former** — no level (§7); its telescope
   entries carry *no* multiplicity choice at all, since type-constructor
   arguments are unconditionally erased (§12, §20) — there's nothing to
   annotate; the return is always `Type`, a single one — no multi-return.
3. **Value-constructor-type former** — no level, no `subterm` (constructors
   don't recurse); its telescope entries freely choose multiplicity per
   field, same freedom as a function's arguments (§12); the return is a
   single, whatever concrete type the constructor builds — no
   multi-return here either. Multiple returns (§11) are function-only.

All three share an underlying "telescope" notion (a list of annotated
`name : Type` entries, §5's restricted grammar), just permitting
different annotations and requiring different things of the return
position. The distinct tagging is also what lets §4's head-dispatch tier
1 tell a function, a type constructor, and a value constructor apart when
deciding how to elaborate an application.

The `name : [level] (telescope) -> (telescope)` declaration syntax used
for `length`/`List`/`Cons` in recent examples is sugar over these three
formers plus a name and (for functions) a body — not a separate
mechanism.

More examples. Multi-return is function-only (above), but `is` (§14) is
not — it works in a type-constructor's or value-constructor's telescope
too, same as a function's:

`reify-add`'s type (§14), with an `is` return instead of a plain type:
```scheme
(Fn L (many a b : Nat) (erased c : Nat) (erased p : Add a b c) ->
   (many d is c))
```

`divmod`'s type, with two (non-dependent, here) returns — function-only:
```scheme
(Fn L (subterm many n : Nat) (many d : Nat) ->
   (many q : Nat) (many r : Nat))
```

A "homogeneous pair" type constructor, `B` forced to match `A` via `is`
(no multiplicity marker either way — forced erased regardless):
```scheme
(TyCtor (A : Type) (B is A) -> Type)
```

A value constructor using the same reify pattern as `reify-add`, but on
a field instead of a return — `c2` materializes the erased `c` at a
different (non-erased) multiplicity:
```scheme
(ValCtor (erased a b c : Nat) (erased p : (Add a b c)) (many c2 is c) ->
   (Reified a b))
```
