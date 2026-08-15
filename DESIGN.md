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
- an **erasure** (the 0/ω multiplicity from §6) — orthogonal to state.
- an **"is" statement** — a rewrite/canonicalization rule (§5), which is
  just a tree whose leaves are references to entries in this same table
  (possibly this entry itself).
- a **stored value**, present only if the state is `comptime`. If the
  entry is also erased, this isn't a real value — it's a *token* that
  just asserts the value exists/is true, not actual data.
- an (implicit) **introduction order** — needed to make the `Predates`
  assertion (§8) well-founded.

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

The language assumes Axiom K (uniqueness of identity proofs) — relevant
to the dependent pattern matching / rewrite rules used inside match
branches (§12).

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
that: each constructor can individually be marked erased ("phantom") or
not, and each field (like each function argument) is individually
annotated erased or not (sane default still TBD). Subterm recursion (§7)
can go through an erased argument.

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
reify-add : (a b : Nat) (0 c : Nat) (0 p : Add a b c) -> (ω d is c)
```

`c` and the proof `p` are erased (multiplicity `0`); the return value `d`
"is `c`" but is declared with multiplicity `ω`. The "is" clause gives `d`
its type (`Nat`, via `c`) while letting its erasure differ from `c`'s —
this is the mechanism for reifying an erased witness into a materialized
runtime value.

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
  `let`; `def-lvl`; (possibly mutual) function definitions, which can
  appear at top level or nested inside another function's body;
  (possibly mutual) ADT definitions, likewise nestable inside a function;
  `match` (branch-local field variables, and possibly refined `is` facts
  on pre-existing variables, §14); `comptime-match` (§15).
- **Locally scoped** (bindings usable only within the construct's own
  extent, not exported to arbitrary surrounding code): a function-type
  former (parameters usable in a later parameter's type or the return
  type, §11, but nowhere else); a `Matchable`-type former (§17).
- **Ordinary, scope-neutral expressions**: `Subterm` birth and `Predates`
  birth (§8); `comptime` (one argument, forces its compile-time
  evaluation); the three function-call forms — lower-level with a
  `Predates` proof, same-level with a `Subterm` proof, and the TBD v2
  multi-proof form (§9, §13); type-constructor application;
  value-constructor application; the three transitivity axioms (§8) —
  scope-neutral regardless of whether they end up as special forms or
  ordinary prelude functions, which is still undecided; a still-unnamed
  form that bundles multiple values into a function's or match's
  multi-value return (§11).

## 17. First-class objects

Everything below can be passed around as ordinary first-class data:

1. an ADT value
2. a function
3. an ADT type constructor, unapplied
4. an ADT value constructor, unapplied
5. a `Matchable` object — see below
6. a `Type`
7. an opaque object (a `Level`, or a `Subterm`/`Predates` proof, §8)

`Special` (§9) is either an opaque object or an ordinary ADT value
(undecided which); `Macro` (§9) is an ordinary ADT value. Applying a
held, unapplied constructor (items 3–4) is ordinary constructor
application, nothing special — no distinct mechanism needed despite the
lack of currying (§7).

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
