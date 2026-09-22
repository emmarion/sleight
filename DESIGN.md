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

The scope environment is a list of entries (shadowing allowed), a pure
registry. Each entry carries:

- a **name** — optional; anonymous entries are allowed.
- a **state**: `Const` or `Dyn` (§15, §34).
- a **stored value**, present only if the state is `Const`. If the
  entry is erased, this isn't a real value — it's a *token* that just
  asserts the value exists/is true, not actual data.
- an **erasure** (the `erased`/`many` multiplicity from §6) — every
  entry is minted with it known, declared at its binder or fixed by its
  kind (§20).
- a **level-mint marker** — set when the entry was introduced by
  `def-lvl` (§8). `prove-predates` requires its `Level` argument to be
  such an entry, not merely some value of type `(Level)`.
- an (implicit) **introduction order** — needed to make the `Predates`
  assertion (§8) well-founded.

An entry's **type** and its **"is" statement** (a
rewrite/canonicalization rule) live not on the entry but in the
rewrite database, the **fact table** (§18). Each is just a tree whose
leaves are references to entries in this same table (§5); an "is" tree
may reference its own entry. Both are scope-relative — a type is as
hypothesis-sensitive as a rule (§18), so the same entry's type may be
refined inside a match branch and revert when the branch ends.
Declaration sites (signatures, telescopes, `let` inference),
match-branch refinements and `comptime-match` verifications all write
the one table (§18).

A type-constructor or value-constructor application expression also gets
its own (typically anonymous) entry, with an `is` rule set to that
application. So "is"/type trees aren't a separate expression structure
sitting apart from the registry and fact table — every application
anywhere is itself a scope entry, letting the rewrite engine "see into"
and canonicalize through them uniformly (§18), the same as for any named
variable. Consequence worth calling out explicitly: the fact table's
reference graph *is* the whole expression structure for anything in the
restricted `is`/type grammar — no separate AST is needed alongside it for
the rewrite engine to work with.

Alongside the table, elaboration carries two pieces of ambient context:

- the **current level** — the level of the function body being elaborated
  into, or a marker that elaboration is at the file's top level, which
  sits above every ordinary level (§24). Entering a function body
  replaces it with that function's level. §9's lower-level call rule
  wants a `Predates` proof relating the callee's level to this one.
- the **enclosing subterm arguments** — references to the entries bound
  by the enclosing function's `subterm`-marked parameters, in declaration
  order. §9's same-level call rule compares a call's arguments against
  these.

## 4. Orthogonality: Kernel-level dynamism with static types

Goal: match Kernel's level of dynamism while still supporting clean
compilation with static types. The mechanism for reconciling these is
analyzing the *constantness* of the head of an s-expression:

- Macros and special forms are first-class values — they can be passed
  around at runtime like any other value.
- To actually *invoke* something as a macro/special form (as opposed to
  merely holding it as a value), the head of the s-expression must be
  constant-known.
- Constant-known-ness is relative to where you are: a name bound inside
  a function body or a match branch is `Dyn`, and a function is `Dyn`
  within the bodies of its own `def-fns` block, yet a statement in run
  position (§16) has run by the time the code after it is elaborated,
  so its binders are constant-known there (§15, §34).

**The elaborator's actual head-dispatch algorithm**, elaborating a list
by examining its head:
1. Look at the head's *type*: if it's a type constructor, a value
   constructor, or a function type, that's ordinary application — proceed
   (this needs no Const-known-ness at all, matching §9: any of these
   can be called through a first-class pointer).
2. Otherwise, if the head is *additionally* Const-known **and
   non-erased** (§34) and of type `(Special)` or `Macro` (§9), proceed,
   dispatching on its stored value — this is the constant-known-head
   requirement above, made precise. An erased `Const` entry stores only
   §3's token; there is no value to dispatch on.
3. Otherwise, it's an elaboration error.

This resolves §27's open question: constructor/function application
isn't dispatched through the `Special` mechanism at all — it's a
separate, type-driven tier (1) that runs before the Const-known
`Special`/`Macro` tier (2) is even considered.

## 5. Restricted dependent types

Dependent types are supported, but restricted: a type may never involve
function invocation. A type can only be built from:

1. variable references,
2. application of a type constructor,
3. application of a value constructor,
4. application of a type former (`Fn`, `TyCtor`, `ValCtor`, §29;
   `Matchable`, §17; or `Newtype`, §38).

The same restriction applies to "is" statements (the
canonicalization/rewrite rules from §3). The intended consequence of this
restriction is a simple type-checking rule: canonicalize, then compare
for identity.

A former's telescope entries bind names (§11, §30). Bound occurrences are
de Bruijn indices; free references remain scope-table pointers as in §3.

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

All functions defined by one `def-fns` block share a single level,
written once on the block rather than per function (§27).

## 8. Built-ins backing termination

These reify §7's level/subterm machinery as actual types, usually fully
erased:

- `Level`: essentially an integer; a nullary type constructor, so the
  type it builds is `(Level)`.
- `Predates`: `(Type A) (A a) ((Level) l) -> Type` — asserts a level
  decrease.
- `Subterm` (heterogeneous): `(Type A) (A a) (Type B) (B b) -> Type`.

Three core axioms/functions, each as premises and conclusion:

1. `Predates` transitivity: from `(Predates A a l1)` and
   `(Predates (Level) l1 l2)`, conclude `(Predates A a l2)`.
2. `Subterm` transitivity: from `(Subterm A a B b)` and
   `(Subterm B b C c)`, conclude `(Subterm A a C c)`.
3. `Predates` through `Subterm`: from `(Predates A a l)` and
   `(Subterm B b A a)`, conclude `(Predates B b l)`.

There are also two ways for these to be "minted" (introduced):

- **`Subterm` minting.** The special form `prove-subterm` takes two
  expressions, asserting the first is a subterm of the second. Both are
  canonicalized/rewritten first, and both are restricted to §5's
  "is"/type grammar. The minted claim then requires the first,
  post-canonicalization, to be a strict subtree of the second, where the
  search walks only through type-constructor applications and
  applications of an ADT's value constructors (§5's productions 2 and
  3). A type former (production 4) is opaque — nothing inside its
  telescope counts as a subterm of it.

- **`Level` minting.** A `def-lvl` form mints a fresh `Level`. Mental
  model (a model only — fully erased in practice, not a real runtime
  counter): imagine a single global counter that increments each time a
  `def-lvl` is "invoked"; its value at that point is the minted level.
  The language being immutable and acyclic is what makes "before"/"after"
  a well-defined ordering here: a variable in scope above (lexically
  enclosing, prior to) a `def-lvl` statement counts as "before" it.

  A level minted later is strictly higher than one minted earlier, so a
  function defined at a later-minted level cannot be called from code at an
  earlier one. Once there is a `main`, that includes anything minted after
  `main`'s own level: such a function is unreachable from `main`, though
  the top level can still call it, at compile time only (§24).

  A second special form, `prove-predates`, mints the `Predates` claim
  relating a variable to a level. It takes them in the order the type
  above puts them: 1) a variable that was in scope when some earlier
  `def-lvl` ran, and 2) the `Level` that `def-lvl` minted, which must be
  before the current code.

## 9. Namespaces, special forms, macros, call-site proofs

- **One namespace.** Special forms, types, and values all share a single
  namespace. Everything in it can be renamed/shadowed, special forms and
  types included.
- **State-forwarding `let`.** A `let` binder takes on the entire variable
  state of the right-hand-side entry it corresponds to, wholesale —
  state (§3), stored value if `Const`, and, via an alias rule recorded
  in the fact table (§18), its type and "is" —
  whenever that entry is an expression in §5's grammar and so has a
  scope entry of its own (§3). This is per-binder:
  with `(let (many a) (many b) (many c) (values x y z))`, each of `a`,
  `b`, `c` takes from
  `x`, `y`, `z` respectively. Where an entry is a call, a match or a
  `coerce` (§38) there is nothing to forward, §15 making those results
  `Dyn` inside a function body or a match branch; in run position (§16)
  the statement is run
  instead and its binders are minted `Const` (§34). Forwarding is one of
  the ways a `Const` reaches into a function body — a special form or
  macro renamed locally (§4) — the others being a direct reference to
  the entry and a macro expansion that mentions it.
- **`let` binders.** Each binder carries a mandatory multiplicity and
  an optional type-or-`is` clause, in telescope-entry shape with the
  type omissible (§30): `(many x)`, `(erased (Nat) x)`, `(many c is d)`.
  The multiplicity is the binder's declaration (§20): a `many` binder
  needs its right-hand-side value non-erased — a `many` return entry of
  a non-erased call, a non-erased constructor application, or a `many`
  entry — while an `erased` binder accepts anything. The type, when
  given, is a checked redundancy, compared for identity with the
  inferred one (§5); a mismatch is a hard compile error. Deliberately
  strict for now; usage may argue for softening later.
- **Special forms as data.** A special form is a nullary variant of the
  `Special` ADT (settled: an ordinary ADT, not opaque). The elaborator
  dispatches on a `Special` variant in head position, and only when that
  head is Const-known and non-erased (§4, §34); held as a value it is
  ordinary data.
  `Special`'s variants are §27's registry — §16's statements and
  expressions, plus the lower-level tokens that annotate a form rather
  than heading a list.
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
    and no `Subterm` proof. The proof relates the callee's level, read
    from its `Fn` type (§29), to the current level (§3); a `Predates`
    about the function value itself, though §8's axiom 3 can produce
    one, is not a call-site proof.
  - A same-level call needs no `Predates` proof, but needs exactly one
    `Subterm` proof instead. The `(subterm p)` annotation marks which
    argument is the subterm-decreasing one by sitting immediately before
    it (§27, §32); every `subterm`-annotated argument preceding it (§7's
    left-to-right order) must be identical, post-canonicalization, to its
    counterpart at the call site — i.e. the usual lexicographic-decrease
    discipline: equal up to the chosen position, strictly decreasing
    there.
  - Every kind of application — type-constructor, value-constructor, a
    lower-level call, a same-level call, `tail`- or `delegate`-marked —
    works fine through a first-class pointer/value, not only by naming
    the callee directly. None of these require a constant-known callee
    at the head — that requirement is specific to invoking a macro or
    special form (§4), not to ordinary application.
- **`tail` marker.** A call can be marked `tail`, asserting the
  programmer's claim that it compiles to a tail call. If the compiler
  cannot honor that claim, it is a hard compile error, not a silent
  fallback. Tail-ness is judged on the post-erasure AST — erased
  positions, types and coercions (§38) all gone (§23): you can store a
  tail call's result, do further work with only phantom/erased values,
  and then return, and it still counts as `tail` — the actual
  requirement is just that the (non-erased) return value(s) and their
  order match what the called function itself returns, which includes
  binding them with a `let` and repackaging them, coerced or not, in
  a `values` in the same order. The check reads the post-erasure form
  with `let`s that merely rename resolved away — a `coerce` erases to
  exactly such a renaming (§38), so a non-erased `let` of a coerced
  result is fine — and the same reading applies to a `delegate`'s
  arguments.
- **`delegate` marker.** Same idea as `tail`, plus the same restriction
  applied to the call's arguments: the non-erased arguments must also
  pass straight through, on the same post-erasure AST. The consequence
  is stronger than `tail` — after stripping erasure, the marked
  function's body reduces to nothing but the delegated call, so the two
  functions' non-erased behavior is identical, and the outer function's
  function pointer could just *be* the inner one's — which §38's
  `Delegate` proof records, and `coercible-of` turns into a `Coercible`.

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

`Type` is itself built by a nullary type constructor, `Univ : -> Type`.
`Type` is then an ordinary scope entry whose `is` statement (§14) is the
application `(Univ)` — the same `is` mechanism used everywhere else, not
a special case. So `Univ` is the type constructor and `Type` the name for
the universe it builds, leaving `Type : Type` above reading unchanged.

## 11. Multiple return values (sigma-like)

A function can return multiple values, including zero, and later return
values can depend on earlier ones — in practice similar to a built-in
sigma (dependent tuple), rather than something layered on top. As usual,
each entry — argument or return value — may only depend on the entries
before it, left to right. This is a function-only feature: type and
value constructors always have exactly one return (§29) — `Type` for a
type constructor, an application of its own type constructor for a
value constructor (§12).

The resemblance stops short of it being a type: there is no sigma type
former (§29), so a multi-size expression has no type of its own, and
several values are never a single value. Each entry of a `values` is a
size-one location (§16), so multiple values cannot nest, and there is
nothing to pass into an argument slot or match on.

Multiple values are introduced by `values` and eliminated by `let`,
which binds one variable per value: `(let (many q) (many r) (divmod n d))`
binds both
of `divmod`'s returns. A `let`'s items are its binders, then any
statements, then the final expression, which is the last item; the
right-hand side is that expression together with the statements before
it, an expression in §16's sense. The binders are a flat list, not a
telescope. `let` is a statement (§16), so its binders enter the
containing expression as ordinary scope entries, and an earlier binder
is, to a later one, just another in-scope variable — a scope-table
reference, not a de Bruijn index (§5). The dependency among a function's
returns lives instead in the function's own return telescope, which is
part of a closed, first-class type (§29) and does bind positionally; a
`let` receives that telescope already instantiated.

`match` carries, before its scrutinee, the scrutinee's multiplicity —
`erased` or `many`, mandatory (§12, §20), and `erased` in an erased
position — and after it an explicit
result-type annotation listing the return type(s) (plural, to match a
function's possibly-multiple return values). The types are mandatory —
they play the role of a match motive, and in a dependent match the
branches' own result types mention branch-refined facts, so we believe
the common generalization cannot reliably be inferred from the
branches. The annotation carries no multiplicities: the results'
erasures are fixed by the match's position (§20). The annotation is
what fixes the match's size (§16).

## 12. Data types, erasure, and match branch kinds

**Two kinds of data type.** **Enums** have a non-erased discriminant,
stored at runtime. **Unions** have an erased discriminant. Independent of
that: a value constructor's declaration in `def-adts` carries a
multiplicity marker, `erased` or `many` (§30, §31) — the multiplicity the
constructor's own scope entry takes, `erased` making it "phantom." The
same marker is recorded in the type's `Matchable` (§17), which is where
phantom-ness is read from when destructing; the constructor's `ValCtor`
type does not carry it, and its return position has no multiplicity of
its own (§29). Each field (like each function argument) is individually
annotated erased or not (sane default still TBD). Declaring a phantom
constructor with any `many` field is a warning. Subterm recursion (§7)
can go through an erased argument. A type marked `newtype` — which
must have exactly one non-phantom constructor holding exactly one
`many` field, or be the union analogue — is required to be represented
as that field alone (§38).

**A constructor returns its own type.** Every value constructor is
declared inside exactly one type constructor's entry in `def-adts`, and
its return must be a saturated application of that type constructor —
`(T i1 ... in)`, one argument per entry of `T`'s telescope, since there
is no currying (§7). In a mutually recursive `def-adts` that means the
specific type constructor it is nested under, not merely one of the
group. The arguments are ordinary expressions in the constructor's own
telescope under §5's grammar — which is where the redeclared index
variables of the paragraph below appear.

**Type indices aren't shared scope.** An indexed ADT's index variables
aren't bound once at the type's own head the way an ordinary (uniform,
`List`-style) parameter is — they go out of scope right after the head.
Each constructor that needs to reference or constrain an index has to
redeclare its own variable for it, with an explicit type, inside that
constructor's own signature — it doesn't get to reuse a shared name from
the head.

**Match-proved equality isn't substitutability.** When a match proves two
expressions equal (they rewrite/canonicalize identically, §5), that alone
doesn't make them substitutable for one another — their erasure can
still differ, and that's a separate axis from canonicalization
equality.

**Matching on enums** is (mostly) straightforward: the erasure of the
variables a branch introduces follows from the scrutinee's declared
multiplicity (§11, §20) — each field at its declared multiplicity under
`many`, all erased under `erased`.

But: a branch reached through a **phantom** constructor (one whose own
`def-adts` declaration is marked erased, as against a binding elsewhere
that merely holds a constructor at multiplicity `erased`, §3) under a
`many` scrutinee can never run, since no non-erased value is headed by
a phantom constructor (§20's rule 2). So everything in scope there is
erased — the variables the branch introduces included, whatever their
fields' annotations say — and, more importantly, so is the expected
type of the branch's own result. Concretely: such a branch's body can,
and in fact must, return entirely erased values, and that's considered
valid even when the match's position (§20) calls for non-erased
result(s) — this branch is exempted from the match's result erasures.
The exemption is from the erasures, not from the result: the body still
produces the declared values, erased. Otherwise a `many` function from a
type whose only constructor is phantom to `False` would need no branch
at all, and `(F)` inhabits that type in erased positions, so the
function would prove `False` (`tests/phantom_false_bad.sl`).
Under an `erased` scrutinee the exemption does not apply: an erased
value may well be phantom-headed, so a phantom constructor's branch is
an ordinary branch there, its fields erased like every other branch's,
and it must produce the match's declared result. §20 covers the
underlying erasure model; an `erased` function's body is the same
situation as the exempted branch.

Matching on unions, and matching on an erased enum scrutinee, is more
involved.

**Four kinds of match branch** (orthogonal to whether the matched
constructor is itself erased; names all tentative, see CLAUDE.md §10):
1. **present** — an ordinary branch.
2. **absurd, automatic** — a branch refuted structurally by the type
   checker, written `(absurd C)`: the token, then the bare constructor
   name, with no fields and no body, since there's nothing to bind
   (§27).
3. **absurd, by proof** — a branch that, instead of producing the match's
   expected result, must produce a value of the empty ADT (§7's
   zero-variant type, e.g. `False`) — the programmer supplies a proof of
   impossibility rather than relying on automatic refutation. The token
   `absurd` heads the branch, before its pattern (§27). §37 gives a
   function body the same option, with the same token.
4. **else** — written `(else body)`, at most one per match: it stands
   for every constructor not listed by name whose forced unification
   does not contradict, binds nothing, and its body is checked with no
   branch-forced facts, against the match's return annotation as
   written. It is an error when it stands for no constructor.

A constructor listed by no branch must be refuted, or stood for by the
`else`; `(absurd C)` records a refutation but is optional. Each
constructor has at most one branch.

**When a non-erased result is on the line.** If a match sits in an
erased position (§20), it's unconstrained. But if at least one of its
results is non-erased:
- if the discriminant is non-erased (a `many` match on an enum), there's
  a real runtime tag to dispatch on, and no further restriction applies;
- if the discriminant is erased — an `erased` match, or a union
  regardless of the keyword — there can be at most one "real" branch. Every
  other branch must be one of: 1) automatically absurd (the rewrite rules
  derive a contradiction), 2) absurd by proof, or 3) a branch matching a
  phantom constructor under a `many` scrutinee — a union matched at
  `many` — which can never run per the phantom-branch rule above and so
  needs no runtime dispatch of its own. Under an `erased` scrutinee a
  phantom constructor's branch counts as real. An `else` counts as one
  real branch, unless every constructor it stands for is phantom under
  a `many` scrutinee: then it counts as none, and its body is erased
  throughout like such a branch's.

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
side; its multiplicity is mandatory per binder (§9).

Motivating example, given `Add : (Nat) (Nat) (Nat) -> Type`:

```
reify-add : (many (Nat) a b) (erased (Nat) c) (erased (Add a b c) p) ->
            (many c is d)
```

`c` and the proof `p` are erased (multiplicity `erased`); the return
value `d` "is `c`" but is declared with multiplicity `many`. The "is"
clause gives `d` its type (`(Nat)`, via `c`) while letting its erasure
differ from `c`'s — this is the mechanism for reifying an erased witness
into a materialized runtime value.

## 15. Match/call results, and a compile-time discriminant assertion

For now: a function call's result, a match's result, a constructor
application and a `coerce` (§38) are all `Dyn` where they stand, even
over `Const` arguments — never `Const`. No automatic constant-folding
through calls, matches or constructors. Inside a function body or a
match branch every binding is `Dyn`. Anywhere else — run position (§16),
the file's top level included — a statement is run as soon as it is
elaborated, and every binder it introduces is minted `Const` (§34). So a
definition wanted as `Const` is bound by its own `let` in run position
(see §33's `xs`). This is deliberate; it may be relaxed later if it
proves heavy.

A special form, `comptime-match`, works specifically on a `Const`,
itself non-erased (§34) scrutinee whose discriminant is also non-erased
— i.e. an enum, never a union (§12): it asserts the value has a given
discriminant, and is a compile error if it doesn't. It is written
`(comptime-match mult x (C field ...))`: a mandatory multiplicity, as a
`match` carries before its scrutinee (§11); a variable naming the entry
whose stored value is read, not an expression; and the constructor with
one binder per field, the erased ones included, as a match pattern has
(§32). It is the one
statement confined to run position (§16): every binding inside a
function body or a match branch is `Dyn`, so any `Const` it could
inspect there is a run-position one anyway, and asserting it in run
position, before the body, records the same fact unconditionally (§18). It consults the
type's `Matchable` (§17) for both the enum/union tag and the
discriminant's position in the constructors' declared order. It binds
the matched constructor's fields as `Const` at their declared
multiplicities: `many`-declared fields bind with their values projected
out of the stored value; `erased`-declared fields bind as §3's tokens —
the stored value physically lacks them, the interpreter having run code
with erased positions stripped (KERNEL.md). The
intent is "proof via reflection/computation" — matches what's
called "proof by reflection" in Coq (a real, externally-confirmed term
for this general technique — a decidable proposition discharged by the
compiler just computing/normalizing, rather than the programmer
constructing a proof term by hand; whether this design's mechanism lines
up with Coq's in the details is still just a plausible guess).

On a discriminant mismatch the compile error prints the expected
constructor and the actual value — discriminant and arguments. This is
deliberately usable as a diagnostics channel: assert the expected
variant of a wrapper enum whose other variants carry whatever payload
the failure should report, and the payload becomes the error message.
No dedicated mechanism needed.

Open item, not yet resolved: whether `is`-declared constructor fields
(§14) and forced type-index unification in a match are literally the
same mechanism — suspected yes, not yet confirmed.

## 16. Expressions, statements, and size

Every expression has a **size**: the number of values it produces.

An expression of any size is a series of **statements** followed by a
`values` line, where each entry of the `values` is itself an expression.
A one-entry `values` may be left implicit, written as just that entry,
so `x` and `(Cons A hd tl)` are ordinary size-one expressions with no
statements, exactly equivalent to `(values x)` and
`(values (Cons A hd tl))`. `(values)`, with no entries, is the size-zero
expression.

Every form binds within its own sub-expressions — a function's
parameters in its body, a match branch's fields in that branch, a
telescope entry in the entries after it. That is unremarkable and gets
no name. A **statement** is a form that binds *outward* as well: its
names, and the facts it mints, enter the expression containing it,
visible to the rest of that expression and gone once it ends. Statements
produce no values.

The statements are `let`, `def-lvl`, `def-fns`, `def-adts`,
`comptime-match`, `let-match` and `open-adt` (§19). All but `comptime-match` can appear at
top level or nested inside a function body; `comptime-match` is confined
to run position (below, §15). `def-fns` and `def-adts`
do both at once — the defined names go outward, while each definition's
own parameters stay inward — and it is only the outward half that makes
them statements.

A `let`'s right-hand side is itself an expression (§11), so the
statements before its final expression are statements of the expression
containing the `let`: their names are visible within the right-hand side
only, but their entries, and the facts and opened objects (§19) they
mint, enter the expression after the `let`, anonymously, at the
multiplicities they were declared with. The names a `let` hides are all
it hides, so nothing a right-hand side minted outlives an entry it
mentions, and a `many` binder there stays `many`: those statements run,
or their code is emitted, whether or not the `let`'s own binders are
erased. Only the final expression is the position §20 calls the
right-hand side.

`match` binds inward only. Its branch-local fields, and any `is` facts
refined by entering a branch, reach that branch and no further, since
different branches learn different things and none of it persists past the
match. So `match` is an ordinary expression, of the size given by its
return annotation (§11). `comptime-match` binds outward for the
complementary reason: having no branches, it asserts a single
discriminant, so what it learns is unambiguous. `let-match` binds
outward when the facts in force leave exactly one possible constructor of
the scrutinee. The named constructor must be that constructor. Its fields
and the facts learned by entering its branch remain in scope for the rest
of the containing expression.

Possibility is determined by the same automatic structural refutation used
by ordinary `match` (§12, §18). Each constructor is checked independently
from the environment before the `let-match`, with fresh fields. Facts
learned while checking one constructor must not influence the checks of
the others. Once exactly one constructor survives, its fields and
refinements are introduced outward.

It is an error if no constructor survives, if more than one survives, or
if the pattern names a refuted constructor. The surviving constructor may
be phantom when the scrutinee is matched at `erased`; all its fields are
then bound erased. A `many` `let-match` refuses a phantom constructor.
Being phantom does not itself refute an alternative: every other
constructor must still be automatically structurally refuted. `let-match`
has no form for supplying an absurd-by-proof branch.

No inspection of the scrutinee's stored value is used to establish which
constructor is possible. Consequently, `let-match` requires neither a
`Const` nor a non-erased scrutinee and is not confined to run position.
Its fields retain their declared multiplicities under the scrutinee's
matched multiplicity (§20); nothing non-erased comes out of an erased
value. The existing requirements for an opened and, where applicable,
readable `Matchable` remain unchanged (§19).

Most locations require a size-one expression. The exceptions are the
three places where a size is fixed by something written down elsewhere:

- a function body, matching the function's declared return telescope
  (§11);
- a match branch body, matching the match's own return annotation (§11);
- a `let`'s right-hand side, matching the number of variables it binds.

A file's top level is an expression like any other, and so requires size
one. What consumes its result is not yet settled: the intent is for it
eventually to be a `String -> String` function, and for now it is simply
the value a REPL would print.

A statement is in **run position** when it sits under no function body
and no match branch. A statement in run position is run as soon as it
has been elaborated, before the code after it is checked, and its
binders enter scope `Const` (§34). This nests: a `let`'s right-hand
side may itself contain statements (§11), and those in run position
complete their own round trips (KERNEL.md) before the enclosing `let`'s.
A file's top level is run position, so calls there need no proofs (§24).
Nothing under a function body or a match branch is run at compile time
— a `comptime` form for that is deferred to v2 alongside `hoist` (§36).

A run-position statement's binders declare their erasures (§9), which
is what lets it be stripped and run before the code after it is
elaborated (§34).

## 17. First-class objects

Everything below can be passed around as ordinary first-class data:

1. an ADT value
2. a function
3. an ADT type constructor, unapplied
4. an ADT value constructor, unapplied
5. a `Matchable` object — see below
6. a `Type`, or a `Newtype` object (§38)
7. an opaque object (a `Level`, a `Subterm`/`Predates` proof, §8, or a
   `Coercible` or `Delegate` proof, §38)

`Special` and `Macro` (§9) are both ordinary ADT values. Applying a held,
unapplied constructor (items 3–4) is ordinary constructor application,
nothing special — no distinct mechanism needed despite the lack of
currying (§7).

Some scope entries need an external annotation beyond the fields in §3 —
e.g. marking that a given entry *is* the `Univ` type constructor (§10),
as opposed to merely having `Type` as its own type, which is true of many
entries; or marking which `Matchable` is the canonical one describing
`Special`'s own shape. Not yet worked out mechanically.

Item 5 is typed `(Matchable enum T (e1 C1) ... (en Cn))`, the first
token being `enum` or `union`: a tag for union-vs-enum, the type
constructor being described, and its value constructors in declared
order with each one's multiplicity — so `List`'s is `(Matchable enum
List (many Nil) (many Cons))`. `T` and the `Ci` are bare and unapplied —
an applied type such as `(List (Nat))` cannot appear there, since the
variant set belongs to the constructor, not to any application of it.
The tag is §12's discriminant and the `ei` are §12's phantom markers,
which between them are exactly the facts no type records: a `TyCtor`
type carries no discriminant, and a `ValCtor` type no phantom marker. A
`Matchable` is minted only by `def-adts` (§19), at `many`: its value
holds an `extern` type's construction and matching (§41) and nothing
else, so a match that dispatches at runtime needs one it can read (§19).
It does nothing by being in scope: nothing consults it until it is
opened (§19).

It has three jobs: it's what lets the compiler know a type's constructors
are disjoint (§19); it's what lets you match on a first-class object
whose type is described only via first-class type/value constructors —
i.e. not a syntactically fixed, named ADT; and it is what a match reads:
its type for the tag and each branch's discriminant, so the constructors
named in a match may be `erased`, and its value only for an `extern`
type's wrapper, stamped in where the `Matchable` is `Const` (§34).

## 18. Match-branch rewrite algorithm (working formulation)

The current working picture for how the engine stores what it knows and
how entering a match branch updates it:

- The scope table (§3) plus one rewrite database, the **fact table**,
  are the sole sources of truth the rewrite/type-checking engine needs.
  The table maps entries to a **type** and an optional **rewrite rule**
  (atom → expression); types live in the table, not on entries (§3),
  because entering a branch forces unification on the scrutinee's type
  as well as its structure — a type is as hypothesis-sensitive as a
  rule, and "the" type of an entry is a scope-relative notion.
- Rules and types are recorded after canonicalizing the proto-form
  against the rules already in force: fact *creation* depends on the
  facts already in force, so a fact minted under a branch hypothesis has
  that hypothesis baked into its canonicalized form. The table is
  maintained self-consistently under its own canonicalization.
- The table is written by declaration sites (`is`-declarations,
  signatures, telescopes, `let` inference), by run-position statements
  running (§34), by `comptime-match` verifications against a real
  stored value, and by match-branch entry's forced unifications
  (below). Branch-forced rules land *even when they rewrite a `Const`
  entry*: a match may scrutinize a `Const`, and the forced rule is a
  claim justified by the match running, pending at elaboration time
  since a branch is never selected during elaboration (§34).
- An open (§19) also writes the table: unifying two opened objects mints
  `T is T'` and `Ci is Ci'` into the scope of the open. These facts are
  not branch-gated, and the soundness argument below for forcing does
  not cover them; what justifies them is that `def-adts` is the sole
  minting site (§19), so two `Matchable`s naming one constructor
  describe one declaration. Recorded as the owner's justification from
  the proposal, not a verified result.
- **A fact ends with the scope it was minted in.** A branch-forced rule
  ends with its branch whatever entries it mentions: matching a `(Nat)`
  against `Zero` forces `n is (Zero)`, which names no branch-local
  entry and must still be gone after the match. This is what makes
  §16's "none of it persists past the match" true. A fact can only mention
  entries in scope where it is minted, so it also never outlasts an entry
  it mentions.
- One table suffices because the only code run at compile time is a
  run-position statement (§16, §24), and its own match branches run
  under the same gating as any other's: a branch's facts hold in exactly
  the branch that runs. The one elaboration-time effect that can occur
  inside a branch, macro expansion, consults no branch hypothesis for
  what it computes, running on `Raw` (§9); `comptime-match` is confined
  to run position (§15, §16). An earlier formulation kept a second,
  hypothesis-free database for a `comptime` form that could run code
  inside a branch regardless of the branch's reachability; that form is
  deferred to v2 (§16, §36).
- Two consequences, recorded as decisions: compile-time effects in
  unreachable code still happen — a macro expansion in an unreachable
  branch still runs, elaboration-time effects being unconditional by
  nature. And a `comptime-match`'s verified fact, recorded in run
  position, holds unconditionally afterwards, so a later match on the
  same `Const` finds the contradicting branches refuted structurally
  (verified `Nil` meets a `Cons` pattern, §12): that is how a branch is
  proven unreachable from a stored value, with no dedicated mechanism.
- Before an occurs-check, and before recursing into any equation's LHS or
  RHS, both sides are first canonicalized/rewritten to normal form via
  the applicable `is` statements.
- This canonicalization engine deliberately does not consult a `Const`
  variable's actual stored value — it works uniformly across `Const`
  and `Dyn`, driven solely by `is` facts, even though `Const`
  carries strictly more information. A deliberate simplification, not an
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
- A constructor's forced facts hold conditionally while checking its
  branch. Ordinary `match` keeps those facts inside that branch;
  `comptime-match` exports them after verifying the constructor against
  the stored value. `let-match` exports them only after independently
  refuting every other constructor (§16). Hypothetical facts introduced
  while testing a constructor do not escape that test.
- The only three ways forcing a unification fails, i.e. produces a
  contradiction: (1) `x` equated with an expression containing `x`
  (checked after resolving through any existing atom-to-atom `is`-alias
  chains, not just against a new equation's literal surface form; `x =
  x` itself is a no-op, not a contradiction); (2) two value constructors
  equated that one opened `Matchable` (§19) lists, or two atoms whose
  signatures cannot be unified, or two atoms equated whose opened
  objects would then name one thing and cannot be (§19's invariant),
  decided recursively (arity mismatch is one easy sufficient symptom of
  this given fixed arities and no currying, not a separate case); (3) a
  variable equated with an expression mentioning a binder of the
  telescope under comparison -- `k` against `x` when `(Fn L ((Nat) x) ->
  (k is y))` meets `(Fn L ((Nat) x) -> (x is y))`. A rule maps an atom
  to a closed expression and canonicalizing a closed expression keeps it
  closed, so no rule could make the two sides identical under §5; the
  closed case, `x` against a constructor there, already fails as a
  mismatch of shape, the form (2) takes in the engine. Decided at
  ASSUMPTIONS 73; the reading leans on §5 stating no eta rule, and §42
  holds an open question that could revisit it.

## 19. `Matchable` and constructor disjointness

Since constructors are first class (§17), two constructor-*valued
variables* aren't necessarily known to be the same or different just from
being syntactically distinct — the constructor a variable holds might
itself be `Dyn`/unresolved. A scope-table field listing known-disjoint
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
succeeds by adding the needed `is` fact(s). Two atoms conflict only when
one opened `Matchable` lists both, or their signatures cannot unify, or
the opened objects that would then name one thing cannot (the invariant
below); nothing is refuted on a name's identity.

A `Matchable`, or a `Newtype` (§38), does nothing by being in scope:
nothing consults it until it is **opened**. Two forms open one, each
taking an expression of `Matchable` or `Newtype` type and reading it for
its type, not its value:

- `(open-adt mult e)`, a statement (§16): an anonymous `let` of `e` at
  the multiplicity `mult`, checked as a `let` binder is (§9), then the
  open of that binder. The open asserts that the `Matchable`'s listed
  constructors are pairwise distinct after canonicalization, and that
  the invariant below holds, minting whatever facts that takes;
  otherwise it is an error. Its extent is that of the entries minted
  beside it: a match branch discards it with the branch's facts, a
  `let`'s right-hand side retains it (§16).
- `(open-absurd e ann)`, an expression whose size and result types `ann`
  gives, a return telescope as a `match`'s or `_` for the enclosing one
  (§11). It takes `e` at `erased`, records and mints nothing, and
  requires the open to *fail*: it cashes in a contradiction between the
  facts in force and the `Matchable`, as an absurd branch does one with
  a pattern (§12).

**The invariant.** At most one opened `Matchable` names a given type
constructor or value constructor, and at most one opened `Newtype` a
given constructor, canonically. Whenever two opened objects of one kind
would name one thing — at an open, or when entering a branch, a
`let-match` or a `comptime-match` forces two type constructors or two
value constructors equal (§18) — they are unified, forcing, through the
`enum`/`union` tag, the constructor count, each constructor's
multiplicity marker, the constructors and the type constructor, hence
their signatures. Two that cannot be unified contradict; two that can
become one, the entry kept being the one the elaborator can best read:
`Const` with the type's own declaration, else non-erased and still bound
(§34). So two opened `Matchable`s for one type are never ambiguous: they
are one, or they contradict. A `Newtype` is only recorded: opening one
merges it with an opened `Newtype` naming the same constructor and
asserts nothing else, and `open-absurd` refuses one, its contradicting
form being undecided.

**What requires an open.** §18's disjointness rule; `match`, `let-match`
and `comptime-match`; §12's and §37's emptiness check; `matchable-of`
and `newtype-of`, which find only an opened object; and
`coercible-wrap`, which needs an opened `Newtype` for its constructor.
`delegate-of` still fetches from ambient scope (§38). §18's occurs
check and its refutation by signature are not gated. A `many` match on a
`many` scrutinee and a `let-match` at `many` use their `Matchable` at
`many` and require the opened entry to be readable: `Const` with the
type's declaration, or non-erased and still bound. A `comptime-match`
consults its `Matchable` at elaboration time and so requires the
stricter half, the opened entry `Const` with the type's declaration, and
uses it at `many` as those do. Readability is judged
at the match, so a `many` parameter opened at `erased` serves no such
match. An unopened `Matchable` leaves its type constructor opaque: type
constructors are told apart only by their opened `Matchable`s, so an
unopened first-class one unifies with any other.

`def-adts` opens what it mints, as does the FFI (§41) for the built-in
`Special`. The opaque built-ins, `Level`, `Predates`, `Subterm`,
`Coercible` and `Delegate` (§8, §38), have no `Matchable` and are never
opened, so they are neither matchable nor empty (§37): no `absurd`
function can hand back one of their proofs as its contradiction.

`def-adts` is the sole minting site: declaring an ADT mints an anonymous
`Matchable` describing it, from the `enum`/`union` tag and the
constructors' declaration markers (§12). Nothing else introduces one.

A special form, `matchable-of`, takes a bare unapplied type constructor
and yields the opened `Matchable` for it, an error when none is open. A
`let` (§9) gives it a name where one is wanted.

## 20. Declared erasure

Every binder declares its multiplicity, so every name's erasure is
known where it is bound, and an expression's erasure is fixed by the
position it occupies. Nothing is derived from usage. The binders, and
where each gets its multiplicity:

- function parameters and return entries, constructor fields: their
  telescope entries (§29, §30);
- a value constructor: its `def-adts` marker (§12); a function: its
  `def-fns` marker, `erased` or `many` per function (§27), which is
  neither part of its `Fn` type (§29) nor written at a call;
- `let` binders: mandatory per binder (§9);
- a match's scrutinee: mandatory on the `match`, `erased` or `many`
  (§11), which fixes the branch fields — at their declared
  multiplicities under `many`, all `erased` under `erased`, and all
  `erased` in a phantom constructor's branch whatever the keyword (§12);
- a `let-match`'s fields: their declared multiplicities under the
  scrutinee's own, as for a match's branch fields above (§16, §27);
- `comptime-match` fields: their declared multiplicities (§15);
- everything minted by kind — a `Level`, a proof, a type constructor — is
  `erased` (§8, §12); a `Matchable` is `many` (§17).

The erased positions, where an expression is erased: an argument at an
erased-declared parameter or field; any argument of a type constructor
(§12); a type or `is` expression (§5, §14); the final expression of the
right-hand side of a `let` whose binders are all `erased`, each entry of
a `values` there taking its own binder's multiplicity (the statements
before it are the enclosing expression's, §16); the scrutinee of an
`erased` match; the proof argument of a `coerce` and every argument of a
`coercible-*` form (§38); and every sub-expression of an erased
expression. The body of a phantom constructor's branch under a `many`
scrutinee is erased throughout (§12), and so is the body of an `erased`
function: it is checked with every return entry `erased`, whatever its
signature says — the analogue of the phantom branch — so such a function
can only ever be held or called at multiplicity `erased`. Every other
position is non-erased.

Checking is then local. Referencing an `erased` name from a non-erased
position is an error; referencing a `many` name from anywhere is fine —
a non-erased value can be "copied" into an erased one for free, but
never the reverse. Going the other way needs a proof: §38's
`coerce`, or §14's `is` reification.

A multiplicity written on a form rather than a binder must match the
form's position: a `match` in an erased position writes `erased`, and
`many` there is an error. A statement's position is that of the
expression it belongs to (§16), so the rule reaches `let-match`.

The rule for a function call or constructor application:
1. If the overall result is erased, there's no further constraint —
   any function/constructor, any argument erasures, all fine.
2. If the overall result must be non-erased: each field/argument that's
   declared non-erased in the callee's own signature must itself be
   non-erased at the call site, *and* the function or constructor being
   called must itself be non-erased.

Phantom constructors, `erased` functions and all type constructors
enter scope as erased (§12). Consequence of rule 2: none of them can
produce a non-erased result — each fails the "function/constructor
itself must be non-erased" half of the rule. An ordinary constructor or
a `many` function can produce either, depending on position.

Multiplicity is relative to the enclosing position, not a global
property of a value. Any function can be invoked in an erased position,
and there its arguments may themselves be erased — so a parameter
declared `many` may hold a value built by an erased constructor. `many`
licenses runtime use if the enclosing invocation itself happens at
runtime.

Erasure is sound to strip because the language is immutable,
effect-free, and total (§7–§8): there's no observable difference
between computing a value and not computing it if the value is never
needed, so "erased" just means "not needed." It is settled from a
unit's text alone — a function body over its signature, a run-position
statement over its `let` binders (§9) — before that unit is compiled or
run, which is what makes the round trip (KERNEL.md) well-ordered.

## 21. Coercion

Designed as `coerce`, §38: two values counted as the same modulo
erased values (`coercible-ctor`), or modulo entering/leaving a
Haskell-newtype-style wrapper type (`coercible-wrap`).

## 22. Evaluation strategy

The language is eagerly evaluated.

Everything here is said of a machine with unlimited stack and heap. A
real run may crash where the host cannot allocate or represent what is
asked of it; a crash produces no value, never a different one.

## 23. Invariant: erasure is conservative

Erasure (§6, §12, §20) is, in a sense, just an optimization — a
substantial one, but not semantics-changing. Invariant: take any program
that validly compiles, strip out every erasure marking and phantom
designator, give `Level` and friends (§8) some ordinary non-erased
representation instead, and replace every `(coerce a p)` by the `b`
from `p`'s type, which the stripped program has as a real value (§38) —
the result should still compile and run identically to the original.
Recorded as an intended invariant/target, not something verified yet
(in the spirit of §10).

"Identically" is the values, not the time or memory taken; the
transformed program may crash on resource exhaustion where the original
did not (§22). `tail` and `delegate` marks are kept but unchecked,
though `def-fns` still mints the `Delegate` proof (§38).

The non-erased stand-in for `Level` and friends would most likely just be
`Unit` (an enum with one constructor, no fields) — but other
representations (e.g. `Level` as a wrapper around an actual `(Nat)`) would
satisfy the invariant too.

## 24. The top level calls freely

At the file's top level (§16, §20) — anywhere outside a function body,
a match branch of a top-level statement included — any type or value
constructor can be invoked (unsurprising, since constructors have no
level, §7), and so can any function, with no `Predates` or `Subterm`
proof required at all. A decrease annotation written there is an
error, not ignored: there is no level to check it against.
In a sense, the top level sits at the "highest" level, above every
ordinary function level.

The owner's own reasoning for why this should still be sound: there's no
way for an ordinary (leveled) function's body to call *into* the top
level, so this unrestricted-calling privilege can never be reached
through the leveled function-call graph that §7's termination machinery
actually checks. Recorded as the owner's claim, not a verified result.

## 25. Bottom-up type inference

The compiler does bottom-up type inference. Explicit types are required
only at: ADT definitions, function arguments, function return results,
and match return results (§11). Everywhere else, inference should
suffice. Erasure, by contrast, is declared at every binder (§20).

## 26. Sugar

Surface sugar is recorded in SUGAR.md.

## 27. Special form registry

Every special form (§9's `Special` ADT variants) established so far, in
one place. Grouped as §16 splits them, statements from expressions, with
the type formers separated out; each entry cross-references where it's
actually specified.

**Statements** (§16):
1. `let` — introduces zero or more bindings, one per value of the
   right-hand side: the binders come first, then any statements, then
   the final expression as the last item (§11); multiplicity mandatory
   and type/`is` optional per binder (§9, §14); state-forwarding per
   binder, from the corresponding right-hand-side entry when that entry
   is in §5's grammar (§3, §9). Zero bindings is useless as the language
   stands, being pure and total, but is expected to matter once linear or
   unique types arrive (§6) — invoking a destructor, or similar.
2. `def-lvl` — mints a fresh `Level` (§8).
3. `def-fns` — defines one or more (possibly mutually recursive)
   functions at a shared level, written on the form itself, each
   function carrying its own `erased`/`many` marker (§20); a single
   function is just the one-element case. Possibly nested inside another
   function's body (§9, §16). A body may be marked `absurd` (§37) or
   `extern` (§41). Mints a
   `Delegate` proof for each `delegate`-bodied function (§38).
4. 4. `def-adts` — defines one or more (possibly mutually recursive)
   ADTs, same one-element-case pattern as `def-fns`; possibly nested;
   index variables aren't shared across constructors (§12, §16); mints,
   and opens, each type's `Matchable` (§19), and its `Newtype` when
   marked (§38). A type may also be marked `extern` (§41).
5. `comptime-match` — compile-time discriminant assertion on a `Const`,
   itself non-erased scrutinee with a non-erased discriminant, in run
   position only (§16); binds the matched fields as `Const` at their
   declared multiplicities; a mismatch is a compile error printing the
   actual value (§15, §34).
5a. `let-match` — destructures a scrutinee for which exactly one
   constructor survives automatic structural refutation, binding that
   constructor's fields and refinements outward (§16, §18). The pattern
   must name the surviving constructor; a phantom constructor is permitted
   only when the scrutinee is matched at `erased`. Fields retain their
   declared multiplicities under the scrutinee's matched multiplicity
   (§20). Constructor selection does not inspect a stored value, so the
   scrutinee need not be `Const` or non-erased, and the form is not confined
   to run position.
5b. `open-adt` — opens a `Matchable` or `Newtype`: an anonymous `let` of
   its argument at the written multiplicity, then the open of that
   binder, asserting §19's invariant and minting the facts it takes
   (§16, §19).

**Type formers:**
6. `Fn` — the function-type former (§7, §11, §16, §29).
7. `TyCtor` — the type-constructor-type former (§29).
8. `ValCtor` — the value-constructor-type former (§29).
9. `Matchable` — the `Matchable`-type former (§17).
9a. `Newtype` — the `Newtype`-type former (§38).

Items 6–9a are also §5's production 4, i.e. they may appear inside a
type or an `is` expression, not only at a declaration site.

**Other expressions:**
10. `match` — pattern match, its scrutinee marked `erased` or `many`
    (§11, §20); four branch kinds: present, absurd (automatic), absurd
    (by proof), else (§12); its size is fixed by its return annotation (§11,
    §16).
11. `matchable-of` — yields the opened `Matchable` for a bare unapplied
    type constructor (§19); `newtype-of` does the same for a wrapping
    constructor's `Newtype` (§38).
11a. `open-absurd` — the contradicting open: an expression of its return
    annotation's size, or `_`'s, requiring the open of its argument to
    contradict the facts in force (§19).
12. `level-of` — yields the `Level` a function is defined at, read from
    its type (§7). Not strictly needed, since that level is always in
    scope anyway, but useful for sugar (SUGAR.md).
13. `prove-subterm` — asserts one expression is a subterm of another,
    minting the `Subterm` proof (§8).
14. `prove-predates` — relates a variable to a `Level` from an
    earlier `def-lvl`, minting the `Predates` proof (§8).
15. Function call — the callee, its arguments, and a decrease
    annotation: `(subterm p)` immediately before the decreasing argument
    for a same-level call, or `(predates p)`, `p` about the callee's
    level, immediately after the callee for a lower-level one (§9, §32);
    the v2 multi-proof form is TBD
    (§13). Can be marked `tail` and/or `delegate` (§9). A call's item
    count therefore exceeds the callee's arity.
16. Type-constructor application (§5, §12).
17. Value-constructor application (§5, §12).
18. `values` — packages values into an expression's result; a one-entry
    `values` may be left implicit, and `(values)` is the size-zero
    expression (§11, §16).
19. The three transitivity axioms — `Predates` transitivity, `Subterm`
    transitivity, `Predates`-through-`Subterm` (§8). Special forms for
    now, rather than ordinary prelude functions.
20. `coerce` — reinterprets a value as the one named by an erased
    `Coercible` proof, at no runtime cost (§38).
21. `coercible-refl`, `coercible-sym`, `coercible-trans` — reflexivity,
    symmetry and transitivity of `Coercible` (§38), special forms like
    item 19.
22. 22. `coercible-wrap` — mints the proof wrapping a value into a
    transparent type's one non-phantom constructor, whose `Newtype` must
    be open (§38); unwrapping is its `coercible-sym` (§38).
23. `coercible-ctor` — mints the proof between two applications of the
    same non-phantom constructor, from per-field values and proofs
    (§38).
24. `coercible-of` — yields the `Coercible` a `Delegate` proof carries
    (§38).
24a. `delegate-of` — yields the `Delegate` proof `def-fns` mints for a
    `delegate`-bodied function, from ambient scope (§38), as
    `matchable-of` does for a `Matchable`.

Items 16–17 (constructor application) are *not* actually dispatched
through the `Special` mechanism the rest of this list uses — see §4's
head-dispatch algorithm for the real two-tier answer.

**Annotation tokens** (also `Special`, but lower-level than the above —
they annotate a form rather than heading a list):
25. `erased` — the 0-multiplicity (§6).
26. `many` — the ω-multiplicity (§6).
27. `:` — separates a name from the signature being given to it, at a
    declaration (§30, §31). Whether this reorders the way telescope
    entries do is still open (§30).
28. `is` — separates an `is` expression from the name it introduces, in
    place of a type (§14, §30).
29. `->` — separates a signature's parameter telescope from its return
    telescope (§29).
30. `subterm` — marks a telescope entry as participating in the
    lexicographic subterm order (§7, §9, §30), and heads the call-site
    annotation that names the decreasing argument by position (§32).
31. `enum` — declares an ADT's discriminant non-erased (§12, §31).
32. `union` — declares an ADT's discriminant erased (§12).
33. `tail` — marks a call as compiling to a tail call; a hard compile
    error if the compiler can't honor the claim (§9).
34. `delegate` — `tail` plus the same pass-through requirement on the
    call's non-erased arguments (§9).
35. `predates` — heads the call-site annotation carrying a lower-level
    call's proof (§9).
36. `absurd` — marks a function, on its `def-fns` line, or a match
    branch, before its pattern, as producing a value of a
    zero-constructor type in place of its declared result (§12, §37);
    `(absurd C)`, a bare constructor with no fields and no body, records
    an automatically refuted branch, which may also be left unwritten
    (§12).
37. `newtype` — marks a `def-adts` entry, after its `enum`/`union`
    token, as a newtype (§38).
38. `extern` — marks a `def-adts` entry, after its `enum`/`union` token
    and any `newtype`, or a function on its `def-fns` line, as
    implemented by the FFI, the source being its model (§41).
39. `else` — heads the branch standing for every constructor a match
    does not list (§12).

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

1. **Function-type former**, `Fn` — takes a level (§7), plus a
   telescope where each entry freely chooses its own multiplicity and can
   be marked `subterm`; produces a function type. The function's own
   multiplicity is not part of it, being declared on the `def-fns` line
   (§20), just as a constructor's phantom marker is not part of its
   `ValCtor` type (item 3).
2. **Type-constructor-type former**, `TyCtor` — no level (§7); its
   telescope entries carry *no* multiplicity choice at all, since
   type-constructor arguments are unconditionally erased (§12, §20) —
   there's nothing to annotate; the return is always `Type`, a single
   one — no multi-return.
3. **Value-constructor-type former**, `ValCtor` — no level, no `subterm`
   (constructors don't recurse); its telescope entries freely choose
   multiplicity per field, same freedom as a function's arguments (§12);
   the return is a single, whatever concrete type the constructor builds
   — no multi-return here either (§11 multi-return is function-only).
   The return carries no multiplicity of its own, phantom-ness being
   declared on the constructor's `def-adts` line and recorded in the
   type's `Matchable` (§12, §17).

Return-position multiplicity therefore appears in exactly one of the
three, `Fn` — the only one whose return is a telescope at all (§11).

All three share an underlying "telescope" notion (a list of annotated
`Type name` or `expr is name` entries, §30, built from §5's restricted
grammar), just permitting different annotations and requiring different
things of the return position. The distinct tagging is also what lets
§4's head-dispatch tier 1 tell a function, a type constructor, and a
value constructor apart when deciding how to elaborate an application.

The `name : (telescope) -> (telescope)` declaration syntax used for
`length`/`List`/`Cons` in recent examples is sugar over these three
formers plus a name and (for functions) a body — not a separate
mechanism. A function's level is written on its enclosing `def-fns`
(§27), not in the declaration.

Multi-return is function-only (above), but `is` (§14) is not — it works
in a type-constructor's or value-constructor's telescope too, same as a
function's. In a type constructor's it is legal but pointless: every
entry there is unconditionally erased (above), so there is no
multiplicity difference for an `is` to bridge and the entry can always be
substituted away. See §30 for worked examples of all three formers
(`reify-add` and `divmod`'s function types, a length-indexed vector's
type constructor, and a value constructor pinning a runtime field with
`is`) — written expression-before-name, per §30.

## 30. Expression-before-name telescope entries; backwards references only

A typed telescope entry is written
`([subterm] [multiplicity] Type name...)` — type before name, Java-style
rather than OCaml/Haskell `name : Type` style. Motivation: an entry may
only depend on entries before it, left to right (§11) — a type can never
mention the very name it's typing. Putting the type first makes source
order track dependency order all the way down to a single entry, not
just across entries: everything a type can reference sits to its left;
the name being introduced, which nothing yet can reference, comes last.

`is`-entries are ordered the same way, `expr is name`, and for the same
reason: the expression may only reference entries to its left, and the
name being introduced — which nothing can yet refer to — comes last. It
reads as an ordinary definition, "(the two-element list) is `lst`", with
the new name in final position.

Whether the *outer* declaration-level naming (`length : Fn ...`) reorders
the same way is still open — that's a binding (`let`-like: "give this
name to this signature"), possibly not the same kind of thing as a
telescope entry at all.

`let` also runs the other way: `(let (many p) rhs)` puts the names first and the
right-hand side last, where the rule above would have the names last.
Left as is for now — worth reconsidering.

Caveat: this breaks `$` when a name would trail a `$`-headed expression,
since `$` reads greedily until the enclosing form's terminator and would
swallow the trailing name as another argument. Plain parens are needed
there instead of `$`.

`let` requires backwards references only, OCaml-`let` style: a binding
can never see itself or anything declared after it. This is what keeps
`let` cleanly non-recursive, with all (possibly mutual) recursion
required to go through `def-fns`/`def-adts` (§16, §27) instead — no
separate `let rec` needed.

Retrofitted examples:

`reify-add`'s type:
```scheme
(Fn L (many (Nat) a b) (erased (Nat) c) (erased (Add a b c) p) ->
   (many c is d))
```

`divmod`'s type:
```scheme
(Fn L (subterm many (Nat) n) (many (Nat) d) -> (many (Nat) q) (many (Nat) r))
```

A length-indexed vector's type constructor. Its entries carry no
multiplicities at all (§29):
```scheme
(TyCtor (Type A) ((Nat) n) -> Type)
```

A value constructor whose runtime field is pinned to a compound
expression. `a` and `b` are erased indices of `Two`; `lst` is stored at
runtime and is definitionally the two-element list built from them, so it
serves as data and in type position at once. A plain
`(many (List (Nat)) lst)` field would carry the same bytes with unknown
identity:
```scheme
(ValCtor (erased (Nat) a) (erased (Nat) b)
   (many (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat)) is lst) -> (Two a b))
```

## 31. Worked example: `List`

```scheme
(def-adts
  (List : (Type A) -> Type
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) tail) ->
       (List A))))
```

Pulls together most of the design established so far:
- `def-adts` (§16, §27) — one-or-more, possibly mutually recursive ADTs;
  here just one.
- `List : (Type A) -> Type` — the type constructor's own signature, no
  level (§7).
- `enum`, not `union` — `List` needs a real runtime tag to be walked over
  (§12).
- `Nil` and `Cons` each independently redeclare `A` — no shared telescope
  at the head, full GADT-style (§12's index-scoping rule applies here
  too, not just to genuinely-indexed types).
- `(erased Type A)` — expression-before-name (§30); `erased` because `A`
  is `Type`-sorted (§12); multiplicity always explicit.
- `(many A head)` / `(many (List A) tail)` — ordinary non-erased fields.
- `many` on both declaration lines — neither constructor is phantom
  (§12); the marker is the multiplicity the constructor enters scope
  with, and is what the type's `Matchable` records (§17).
- `(List A)` on both returns — the saturated application of the type
  constructor they are declared under (§12), carrying no multiplicity of
  its own (§29).

Paren balance checked with a script rather than by eye when this was
drafted (12 opens, 12 closes).

## 32. Worked example: `length`

```scheme
(def-adts $ Nat : -> Type
  enum
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-lvl L)

(def-fns L $ many length : (erased Type A) (subterm many (List A) xs) ->
    (many (Nat) n)
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl)
      (let (erased p) (prove-subterm tl xs))
      (Succ $ length A (subterm p) tl))))
```

- `Nat : -> Type` — a nullary type constructor, so the type it builds is
  `(Nat)`, the same shape as `Univ`/`Type` in §10.
- `$` (§2) heads both definitions and the `Succ` application, saving a
  paren pair each.
- `(def-lvl L)` mints the level `length` is defined at (§8, §27).
- `many length` — the function's own multiplicity (§20), in the slot
  where `many Zero` sits in the `def-adts`.
- `(match many xs (((Nat) r)) ...)` — the scrutinee's multiplicity comes
  first (§11, §20); §11's result annotation is one parenthesized
  telescope of types directly after the scrutinee, so it cannot be
  mistaken for a branch.
- `(let (erased p) ...)` — every binder declares its multiplicity (§9);
  a proof is erased.
- `((Cons a hd tl) ...)` — a branch is a pattern list followed by a body.
  Every field gets a binder, the erased ones included.
- `(prove-subterm tl xs)` mints the proof (§8). Entering the `Cons`
  branch forces `xs is (Cons A hd tl)` (§18), so `tl` canonicalizes to a
  strict subtree of `xs`. The form's name differs from the `Subterm` type
  it produces.
- `(subterm p)` precedes the decreasing argument at the call site.
  Position is what answers §9's "which argument is the
  subterm-decreasing one", so no variable name is involved and nothing
  can shadow it.
- A call's item count therefore does not equal the callee's arity. The
  same holds for a lower-level call, which carries a `predates`
  annotation instead.

## 33. Worked example: level-polymorphic `map`

`map` calls the function it is given, so by §7 it must sit at a level
strictly above that function's, and §9 wants a `Predates` proof for the
call. The proof cannot be discharged inside `map`: the function is
`map`'s own parameter, so it was not in scope when `map`'s level was
minted, which is what `prove-predates` requires (§8). The level relation
has to be established where the level is minted, so `map` is produced by a
factory.

```scheme
(def-lvl F)

(def-fns F $ many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped)
  (def-lvl L)
  (let (erased pml) (prove-predates M L))
  (def-fns L $ many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys)
    (match many xs (((List B) r))
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (let (erased p) (prove-subterm tl xs))
        (Cons B (f (predates pml) hd) $ map A B f (subterm p) tl))))
  (values L map))
```

```scheme
(def-lvl I)

(def-fns I $ many inc : (many (Nat) n) -> (many (Nat) m)
  (Succ n))

(let (erased ML) (many map-nat) (map-factory I))

(let (many xs) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(map-nat (Nat) (Nat) inc xs)
```

- The factory mints the level and returns it. Naming `L` in the return
  telescope is what lets the second return's type mention it (§11); a
  single-return factory would have had to take the level as an argument,
  since a signature is fixed before its body runs.
- `prove-predates` discharges inside the factory, `M` being in scope when
  `def-lvl L` runs (§8).
- `A` and `B` stay ordinary parameters of `map`. Types carry no level
  (§7), so only the function's level has to be baked in.
- Both call flavours appear in one body: `(f (predates pml) hd)` is the
  lower-level call, `(map A B f (subterm p) tl)` the same-level
  recursion (§9, §27).
- The usage is a sequence of statements in run position, each elaborated
  and run in turn (§16, §24): calls need no proofs, and every binder is
  minted `Const` (§34). Each `let` declares its binders' multiplicities
  (§9): `ML` and `map-nat` match the `erased`, `many` of `map-factory`'s
  return telescope, and `xs` is a non-erased constructor application
  bound `many`.
- `ML` is bound only because it is the first return; it is erased and
  never used again.

## 34. Const formation and compile-time inspection

The states are `Const` and `Dyn` (§3). This section collects how
`Const` arises and what may be done with it.

**Const values are minted with known erasure.** The minting sites:

1. **A statement in run position** (§16, §24) — every name such a
   statement introduces is `Const` once the statement has run. A `let`
   is elaborated, stripped and run (KERNEL.md), and its binders take the
   resulting values at their declared multiplicities (§9). A `def-lvl`,
   `def-fns` or `def-adts` involves no evaluation:
   a definition's value is built by elaboration itself — a function
   value is its own compiled code; a `Level` is an erased token; a
   `Matchable` holds the FFI's wrapper for an `extern` type and nothing
   otherwise (§17). Within the bodies of a `def-fns` block the block's own
   functions are `Dyn`, their code not yet complete; they become `Const`
   after the block, at the multiplicity each carries on its `def-fns`
   line (§20).
2. **`comptime-match` field binding** (§15) — erasure is the field's
   declared multiplicity.
3. **State-forwarding `let`** (§9) — strictly forwarding of state and
   value; the binder's multiplicity is its own declaration (§9).

Nothing else mints `Const`. Inside a function body or a match branch
every binding is `Dyn`, nested definitions included: a `def-fns`,
`def-adts` or `def-lvl` there mints `Dyn` entries, so a `Special` or
`Macro` that is ever invoked (§4) originates in run position. A
constructor application over `Const` arguments is still `Dyn` (§15) —
bind it with its own `let` if `Const` is wanted.

**Inspection requires Const and non-erased.** A `Const` entry's stored
value is read in three places: §4's head dispatch (invoking a `Special`
or `Macro`), `comptime-match`'s discriminant read (§15), and the
running of a run-position statement that references the entry — the value
gets embedded into the code the interpreter runs. §18's rewrite engine
consults no stored values. All three require the entry to be `Const`
and non-erased: an erased `Const` entry stores only §3's existence
token, the value behind it never having been computed — the round trip
strips erased positions before the interpreter runs (KERNEL.md). For
statement execution this requirement is just erasure checking doing its
job: an erased `Const` may still be referenced from the statement's own
erased positions, which are stripped, not read.

**The checker never evaluates.** The dividing line for what the checker
itself computes: only work whose entire trace is spelled out in the
source. Constructor application assembles data whose shape the source
dictates; `comptime-match` *verifies* an asserted discriminant and
projects — the programmer wrote the answer down. Selecting a match
branch from a value would be the value steering elaboration — the first
step of evaluation — so `match` results stay `Dyn` (§15) even on a
`Const` scrutinee; the delimited alternative is binding the match with
its own `let` in run position, handing the branching to the
interpreter. This is also
why the inspection sites above stay checks rather than forwarding: by
the time any of them runs, the inspected entry's erasure is already
settled, so no erasure demand ever flows backwards into code that has
been checked, stripped, and run. The same shape governs the fact table
(§18): nothing — erasure demands, branch-hypothetical facts — crosses
an evaluation boundary.

**Run-position boundary erasure.** A run-position `let` is compiled and
run before the code after it is elaborated, so its binders' erasures
must be known at its boundary — and they are, being declared on the
binders (§9). A run-position statement thus resembles an anonymous
nullary function: erasure declared at its boundary, like a signature.
Its result *type* needs no annotation, though — we believe the only true
need for declared return types on functions is self-reference
(recursion, §25), and a statement, being anonymous and uncallable,
cannot recurse into itself.

§23's invariant appears to survive all of this: stripping erasure only
turns erased positions non-erased, so a program valid under these rules
should remain valid — argued by inspection, not verified.

## 35. v2 sketch: macro hygiene via entry references

Not settled — a recorded direction, from a design discussion, for the
v2 macro system (§9 defers macro termination to v2 as well).

`Raw`'s variable leaves could be of two kinds: a **name**, resolved at
the expansion site (capturable, occasionally wanted), or an **entry
reference** — the identity of a scope entry from the macro's definition
site (unique ids, not table positions). References are identity-based,
so shadowing at the expansion site cannot capture them; that is the
hygiene property.

At expansion, a reference to an entry still in scope resolves directly.
A reference to an out-of-scope entry is, for now, simply an error: the division
of labor is that expansion-site material enters through the macro's
arguments, while captured definition-site material must still be in scope.
In principle an out-of-scope entry could instead be *merged* into the
current scope — a form of scope merging — but the rules for merging scopes and
combining their rewrite rules are complicated and not designed.
Recorded as an open v2 question, nothing more.

This is in the tradition of syntactic closures (Bawden) more than
Racket's scope-sets, we believe, without having verified the
correspondence. An earlier formulation had a third entry state,
`Inacc` (inaccessible), for a `Dyn` entry captured from an enclosing
scope into compile-time code, with a deferred, macro-related motivation
for letting `let` rename such an entry; with compile-time evaluation
confined to the top level (§16) the state has no motivating case and
was dropped. Whether hygiene wants something like it back is a v2
question.

## 36. v2 sketch: `hoist`

Not settled. Compile-time evaluation is confined to the file's top level
(§16); a `comptime` form for running code at compile time inside a
function body is deferred to v2 together with this. In the worked
examples the top level does pure level-hoisting: a body can only call
into the past (nothing minted during a body's execution is callable by
that body), so manufacture must happen before the consumer's level is
minted, and a top-level statement is how manufacture runs "early". A
special form `(hoist L body)` would name that directly: `body` may
reference only entries introduced at or before the in-scope `def-lvl`
that minted `L`, and its own mints count as happening just before `L`'s —
so its product predates `L` and everything after, callable with ordinary
`Predates` proofs, and the factory pattern becomes writable inline.

Much remains to litigate before this is real: the fact table would need
caching at every `def-lvl`, with canonicalization of the body run
against that cached view; and where the body actually *runs* is
unsettled — one reading executes it in place with only its mint order
fictionalized (purity arguing the difference is unobservable), while
the top-level analogy argues for running it at the hoisted-to point and
caching/closing over its value.

## 37. Absurd functions

A function marked `absurd` on its `def-fns` line, next to its name and
multiplicity — `(def-fns L $ many absurd explode : ...)` — has a body
that, instead of producing its declared return telescope, produces a
single value of a type with no constructors (§7's zero-variant ADTs,
e.g. `False`), read off the type's `Matchable` (§19). It is the
function-level counterpart of §12's absurd-by-proof branch, which
carries the same token (worked example in §39). Assuming §10's
consistency, such a function can never be called at runtime, since a
call would need the values from which its body derives the
contradiction, so it compiles to no code: its function pointer may be
null, or anything at all.

Its counterpart for a contradiction that lives in the fact table rather
than in a value, two constructors of one opened `Matchable` equated, is
`open-absurd` (§19): it produces the declared result directly, with no
empty type in between, and the marker is not needed on that route. Where
a scrutinee is at hand, neither is: a match whose branches are all
refuted produces its declared result (§12).

The owner's expectation, not yet applied to the rest of the design:
with absurd functions available, a non-erased `match` with no branches
— the previous route from an empty type to an arbitrary result — is no
longer needed.

## 38. `coerce`

A `coerce` reinterprets one value as another of identical runtime
representation, at no runtime cost, on the strength of an erased proof
that the two are coercible. It is the coercion §21 asked for (worked
example in §40).

**The proof type.** `Coercible : (Type A) (A a) (Type B) (B b) -> Type`,
heterogeneous like `Subterm` (§8), an opaque object (§17), always
erased.

**The delegate proof.** `Delegate : (Type G) (G g) (Type F) (F f) ->
Type`, the same shape, likewise opaque and always erased. It records
that `g`'s body is a `delegate` call to `f` (§9); `def-fns` is its only
introduction rule, so item 7's fetch has nothing to choose between.

**The expression.** `(coerce a p)`, with `a` the value being
reinterpreted and `p : (Coercible A a B b)`; `a` must be identical,
post-canonicalization, to the value in `p`'s type, and `b` is read from
it. It produces one value `d` of type `B` with `d is b` (§14); `d` is
`Dyn` where it stands, like a call's result (§15), and `Const` when a
run-position `let` binds it, like anything else (§34). A `coerce` in a
non-erased position demands `a` non-erased (§20); `p` is erased always.
§23's invariant is stated with each `coerce` replaced by its `b`,
which the stripped program has as a real value.

**Minting proofs.** All of the following are special forms (§27),
checked entirely at elaboration time:

1. `(coercible-refl e)` — `(Coercible A e A e)`; since types canonicalize
   (§5), this relates any two `is`-equal values.
2. `(coercible-sym p)` — from `a` to `b`, conclude `b` to `a`.
3. `(coercible-trans p q)` — from `a` to `b` and `b` to `c`, conclude `a` to
   `c`.
4. 4. `(coercible-wrap C arg1 ... argn)` — wrapping into a **newtype**.
   A type is a newtype by declaration: its `def-adts` entry carries the
   `newtype` mark after its `enum`/`union` token (§27), and it must then
   have the newtype shape, a hard error otherwise — an enum with exactly
   one non-phantom constructor holding exactly one `many` field, or a
   union in which, among the non-phantom constructors, every one but one
   has only `erased` fields and the remaining one has exactly one `many`
   field. Phantom constructors never head a non-erased value (§20) and
   do not count either way. A type of that shape left unmarked is not a
   newtype: an implementation may still represent it as its field, but
   promises nothing and admits no `coerce`. The mark mints an erased
   `(Newtype C)` alongside the type's `Matchable`, `C` the wrapping
   constructor the shape above singles out, bare and unapplied as in a
   `Matchable`; the type is read off `C`'s return type, so the object
   carries nothing else. `Newtype` is a type former (§5), the object is
   first class (§17), and `newtype-of` fetches the opened one by naming
   `C`, as `matchable-of` does by naming the type (§19).
   `coercible-wrap` verifies that a `Newtype` for `C` is open — its
   being minted only by `def-adts` or the FFI (§41) is what makes it
   trustworthy — so a first-class wrap goes through a `(Newtype C)`
   parameter, opened first. That one object is the proof that `C` heads
   inhabited values: the proof's target `(C arg1 ... argn)` is what a
   non-erased `coerce` produces, and by §20's rule 2 no non-erased value
   is headed by a phantom constructor, so a wrap through a constructor
   no `Newtype` names — a phantom one with a `many` field, say — would
   make a value with no inhabitant at runtime, and a match on it would
   reach absurd code. The arguments are `C`'s telescope in order, so
   exactly one of them, `f`, sits at the `many` field. The proof is
   `(Coercible F f T (C arg1 ... argn))`, unwrapping being its
   `coercible-sym`.
5. `(coercible-ctor C ...)` — the same constructor on both sides,
   with fields that may differ. The arguments follow `C`'s telescope in
   order: an `erased` field takes two, its source and target values,
   and a `many` field takes one, a `Coercible` proof between the values
   at that position. Each is checked against its field type
   instantiated with the source values on the source side and the
   target values on the target side, so `C`'s return type, and with it
   any type index, may differ between the sides. The proof is
   `(Coercible T (C sources) T' (C targets))`. Using it at a
   `coerce` needs the source to canonicalize to `(C sources)`, which
   is what entering a `C` branch forces (§18), so such a proof is built
   per branch from the branch's binders.
6. `(coercible-of d)` — from a `d : (Delegate G g F f)`, the
   `(Coercible G g F f)`. It forgets only why the two coincide.
7. `(delegate-of g)` — for a `many` function `g` whose body is a
   `delegate` call to `f` (§9), the `(Delegate (Fn ...) g (Fn ...) f)`
   `def-fns` minted anonymously, fetched from ambient scope by naming
   `g`, as `matchable-of` does. `g` is `Dyn` within its own block (§34),
   so its body cannot use its own proof.

**Representation requirement.** Coercion is zero-cost only if the
representations really coincide, so the following is a requirement on
the implementation, not an optimization it may choose. Values have a
uniform representation, OCaml-style: every value is one word, an
immediate or a pointer to a block, whatever its type — a `Cons` block
holds a `(Meters)` and a `(Nat)` alike, and a wrapper's field may be
existentially typed. A value is the tuple of its constructor's `many`
fields, one field standing bare; it carries a tag only when its type
is an enum with more than one non-phantom constructor, the tag being
the constructor's position among them and all a tag ever
distinguishes. With no `many` fields a value is therefore the tag alone
when its type is tagged, and an unspecified word otherwise. A union
never carries one, its discriminant being erased (§12). So every
newtype, as item 4 defines it, is represented exactly as its
one `many` field — no tag, no wrapper — which is the guarantee the
mark buys; a value built by one of a union newtype's other non-phantom
constructors is an unspecified word, which
nothing ever reads as the field: a `many` match on the union has a
single real branch, and unwrapping needs the value to canonicalize to
the wrapper's application. Erased fields occupy no space (§34). A
`delegate`-bodied function's pointer is interchangeable with its
callee's (§9). An extern type (§41) may be marked `newtype` like any
other, its FFI author then guaranteeing the field representation, and
a newtype may wrap a field of an extern type.

Only non-phantom constructors and `many` functions matter in items 4–7:
a `coerce` produces a non-erased value, which by §20's rule 2 none of
the others can head. So `coercible-ctor` consults no `Matchable` and
does not refuse a phantom `C`, a proof between two phantom-headed values
never being cashed, while `coercible-wrap` manufactures its target and
must.

Proofs over containers — every element of a list wrapped, say — are
built by recursion, in an `erased` function returning the proof (§20),
checked for termination like any other (§7) and never run.

**Tail and delegate.** A `coerce` erases to nothing, so §9's `tail` and
`delegate` checks read the post-erasure AST with erased positions,
types and coercions gone (§23): a call still counts as `tail` when its
returns are bound by a `let` and repackaged in a `values` in the same
order, coerced or not, and as `delegate` when its arguments likewise
pass straight through.

## 39. Worked example: absurd `explode`

```scheme
(def-adts $ False : -> Type
  enum)

(def-lvl X)

(def-fns X $ many absurd explode : (erased Type A) (many (False) f) ->
    (many A a)
  f)
```

- `False` has no constructors (§7); its `Matchable` (§17) is
  `(Matchable enum False)`, which is how §37 knows the type is empty.
- `many absurd explode` — the multiplicity marker (§20) and the
  `absurd` token (§37) share the line with the name.
- The body is `f`, a single value of `(False)`, where the signature
  promised `(many A a)`. Marked `absurd`, that is accepted (§37): the
  function is ex falso. It compiles to no code, and holding it at
  `many` is fine — the pointer is never followed.

## 40. Worked example: unwrapping a list with `coerce`

Written against §38's rules as recorded, not machine-checked — nothing
implements them yet.

```scheme
(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl U)

(def-fns U $ erased unwrap-witness : (subterm many (List (Meters)) ms) ->
    (erased (List (Nat)) ns)
    (erased (Coercible (List (Meters)) ms (List (Nat)) ns) p)
  (match erased ms (((List (Nat)) ns)
                    ((Coercible (List (Meters)) ms (List (Nat)) ns) p))
    ((Nil a) (values (Nil (Nat)) (coercible-ctor Nil (Meters) (Nat))))
    ((Cons a m tl)
      (let (erased sp) (prove-subterm tl ms))
      (let (erased ws) (erased q) (unwrap-witness (subterm sp) tl))
      (match erased m (((List (Nat)) ns)
                       ((Coercible (List (Meters)) ms (List (Nat)) ns) p))
        ((MkMeters n)
          (values (Cons (Nat) n ws)
                  (coercible-ctor Cons (Meters) (Nat)
                    (coercible-sym (coercible-wrap MkMeters n))
                    q)))))))

(def-lvl V)

(let (erased puv) (prove-predates U V))

(def-fns V $ many unwrap-all : (many (List (Meters)) ms) ->
    (many (List (Nat)) ns)
  (let (erased ws) (erased p) (unwrap-witness (predates puv) ms))
  (coerce ms p))
```

- `Meters` is transparent (§38): one non-phantom constructor with one
  `many` field, so §38's representation requirement makes a `(Meters)`
  exactly a `(Nat)` at runtime, and a `(List (Meters))` exactly a
  `(List (Nat))`. `unwrap-all` is the zero-cost witness of that.
- `unwrap-witness` is `erased` (§20): it never runs, but it is a
  function like any other — level `U`, a `subterm` parameter, and §7's
  termination check on the recursive call.
- Its two returns form a telescope (§11): the witness list `ns` first,
  then the proof, whose type names `ns`. Both matches carry that same
  telescope as their annotation, with types only (§11).
- `(coercible-ctor Nil (Meters) (Nat))` — `Nil`'s telescope has one
  `erased` field, so two arguments: source and target values (§38).
- In the `Cons` branch, `ms is (Cons a m tl)` is forced (§18), and in
  the inner `MkMeters` branch, `m is (MkMeters n)`. So
  `(coercible-wrap MkMeters n)` relates `n` to `m`, its `coercible-sym`
  is the head proof, and the `coercible-ctor` for `Cons` takes source
  and target `A`, that head proof, and the recursive tail proof `q`,
  producing a proof whose source canonicalizes to `ms`.
- Both matches are `erased`: the whole body is an erased position, and
  §12's one-real-branch rule never bites since no result is non-erased.
- `unwrap-all` calls `unwrap-witness` from a higher level, with the
  `Predates` proof minted in run position after `def-lvl V` (§8, §9). The
  `let`'s binders are all `erased`, so the call is an erased position
  (§20) and never runs. `(coerce ms p)` is the only runtime content,
  and it erases to nothing (§38).

A `delegate` proof, reusing `inc` from §33 at level `I`:

```scheme
(let (erased piv) (prove-predates I V))

(def-fns V $ many inc-noted : (many (Nat) n) (erased (Nat) note) ->
    (many (Nat) m)
  (delegate (inc (predates piv) n)))

(let (erased ig) (coercible-of (delegate-of inc-noted)))
```

- After erasure `inc-noted`'s body is nothing but the call to `inc`
  (§9), so `def-fns` mints the `Delegate` proof, `delegate-of` fetches
  it and `coercible-of` reads the `Coercible` off it:
  `ig : (Coercible (Fn V ...) inc-noted (Fn I ...) inc)` (§38).
  `(coerce inc-noted ig)` is then `inc`'s own pointer.

## 41. Extern types, the FFI, and the prelude

Partly designed. Settled: the `extern` mark and what it promises, the
invariant below, and the prelude's `Nat` and `U8`. The prototype's FFI
is a fixed table (ASSUMPTIONS.md); a source-level way to add to it is
not designed.

**The `extern` mark.** A `def-adts` entry or a `def-fns` function may
be marked `extern` (§27). The declaration is then a *model*: for a type,
its constructors and `Matchable` say what its values are and how they
are taken apart, and the FFI supplies the representation together with
construction and matching over it; for a function, the body says what
it computes, and the FFI supplies an implementation. An extern type is
a type like any other — it has a `Matchable`, its values are non-erased
and one word (§38), so they sit in a `List` or a `many` field — and it
may be marked `newtype`, the FFI author then guaranteeing that its
representation is that of the field and that a `coerce` through it is
safe; a newtype may equally wrap a field of an extern type.

**Invariant: externs are conservative.** In the spirit of §23: every
extern implementation stands in for a declaration in the language, and
stripping every extern implementation — running the models instead —
must leave a program that compiles and runs identically: the same
values, not the same cost, and either side may crash on resource
exhaustion where the other does not (§22). Recorded as an intended
invariant; the prototype checks it on its own tests.

**`Nat`.** The prelude declares `Nat` as the Peano enum of §32, marked
`extern`, and the FFI holds it as an arbitrary-precision integer;
`add` is likewise extern over a structural definition, returning an
`Add` proof beside the sum; `nat-add` is a `delegate` over it that
drops the proof. There are no
numeric literals for now.

**`U8`.** An enum with one constructor, `MkU8`, holding a
`(Nat)` and an erased proof that it is below the modulus:

```scheme
(def-adts $ U8 : -> Type
  enum newtype
  (many MkU8 : (many (Nat) n) (erased (Lt n u8-modulus) p) -> (U8)))
```

`Lt` is the prelude's strict order on `Nat`. The modulus is a top-level
`Const` proved to be 2^8 by construction: `Pow2 k v` relates an
exponent to its power through a `Double` relation, `pow2` computes the
power and returns the proof, and `(pow2 eight)` with `eight` spelled in
unary binds `u8-modulus`. Its constructors are its API — a `U8` is taken
apart by matching, and built by `MkU8` with a proof: for a hand-built
value by reflection (a `comptime-match` on a decided comparison, §15),
and for a computed one by binding it and matching `lt-dec`, where the
caller says what out of range means (§5 keeps the call itself out of
the `Dec` index, so the binding is not optional). There is no
narrowing function. `u8-add` (wrapping) delegates to `add-u8`, plain source over `add` and
the extern `nat-mod`, which returns a `U8Add` relating the fields
through `Add` and `Mod`; `U8` is marked
`newtype`, so it is its `Nat` field alone (§38) and needs no extern of
its own.

Open, not decided: a source-level declaration of extern types and
functions; what guarantees an extern implementation agrees with its
model beyond the invariant above; numeric literals.

## 42. TBD: a rewriting engine without the atom requirement

§18's fact table maps an atom to an expression, and canonicalization is
substitution through those rules. To consider: a perhaps more complex
engine without that requirement, whose rules rewrite expression to
expression, canonicalizing directly from one to the other. Not designed.
What the atom requirement decides today is §18's third failure mode: an
equation with a binder occurrence on one side and a variable on the
other has no atom rule that could express it, so the branch is refuted
(ASSUMPTIONS 73). Whether an engine able to record an equation between
the two telescopes themselves should treat such a branch differently,
given §5's identity, and what expression-level rules would do to §5's
canonicalize-then-compare rule and to §18's occurs check and
self-consistency of the table, are open.
