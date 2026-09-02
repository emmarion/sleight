# Implementation assumptions log

A running log of the assumptions the prototype interpreter (`lib/`,
`bin/`) makes where DESIGN.md is silent, ambiguous, or where the
implementation takes a shortcut. Written by a Claude session working
autonomously at the owner's request; nothing here is a design decision.
Every item is a candidate question for the owner, and the owner's answer
may well be different from what the code does. Numbers in
SPEC-REVIEW.md are cited as `SR n` where an item there covers the same
ground.

## Reader

1. **Comments** are `;` to end of line. Atoms are any run of characters
   other than whitespace, parens and `;`; there are no numeric or string
   literals (SR 10).
2. **`_` as a binder name** births an anonymous entry, wherever a binder
   is expected (let binders, telescope entries, pattern fields). It is
   not special anywhere else (SR 10, SR 11).
3. **Annotation tokens go through the namespace.** `many`, `:`, `->`,
   `is`, `subterm`, `enum`, `absurd` and friends are recognized only by
   resolving the atom to a `Const`, non-erased entry whose value is the
   corresponding `Special` variant, exactly as `let` or `match` are
   (section 4's tier 2). So all of them can be shadowed (section 9).

## Prelude

4. **What is built in.** `Univ`/`Type`, `Level`, `Predates`, `Subterm`,
   `Coercible`, the `Special` ADT and one entry per special form. The
   opaque types are type constructors with no `Matchable`, so they can
   neither be matched on nor count as empty (SR 6). `List`, `Nat`,
   `False` are not built in; the examples define them (SR 12).
5. **Names of the `Special` variants** are the form name prefixed with
   `%` (`%let`, `%match`, ...), so that the entry `let` — whose value is
   `(%let)` — is distinct from the constructor. Only the prefix is an
   invention; it is not settled by DESIGN.md.
6. **`Macro` and `Raw` are not implemented.** DESIGN.md gives no way to
   construct a `Raw`, and macros are interim in section 9 anyway (SR 11).
   Head dispatch on a `Macro` value is therefore an error for now.
7. **Names of the transitivity axioms** (SR 11): `predates-trans`,
   `subterm-trans`, `predates-subterm`, in the order section 8 lists
   them. Each takes its two premises as arguments.

## Grammar shapes DESIGN.md leaves open

8. **A body's final item** may be a single form of any size (a call, a
   match or a `coerce` producing several values), as well as a `values`
   (SR 1). A non-final item must be a statement.
9. **`tail` and `delegate` wrap the call**: `(tail (f ...))`,
   `(delegate (f ...))`, following section 40's only example (SR 2).
10. **`comptime-match` syntax** is `(comptime-match x (C field ...))`,
    mirroring a match pattern, with every field bound (SR 11).
11. **Where return entries end and a body begins**: after `->`, the
    leading items that are lists headed by a multiplicity token are
    return entries; the rest is the body. The same rule separates a
    `let`'s binders from its right-hand side (SR 10).
12. **A file may end in a statement** (section 40 does); then nothing
    is printed (SR 27). Otherwise the final expression's one value is
    printed. Several files on the command line share one scope, in
    order.
13. **A `def-fns` level** may be any variable whose type is `(Level)`,
    not only a `def-lvl`-born one; only `prove-predates` insists on the
    birth marker, after canonicalizing the level. Its subject stays the
    variable named when that variable is old enough; a newer alias of an
    older variable (a `let ... is`) is resolved to what it canonicalizes
    to, so that the proof is about the older variable (SR 20).

14. **`def-adts` ordering**: a type constructor's own telescope may
    mention types defined earlier in the same `def-adts`, not later
    ones; every constructor may mention every type of the group.
15. **A position of size zero is erased** (all zero of its entries
    are), so the right-hand side of a `let` with no binders, or a match
    with an empty annotation, is checked but never run. Section 27
    calls such a `let` useless as the language stands.
16. **A match in an erased position** elaborates its scrutinee erased
    whatever the keyword says, per section 12's "unconstrained".
17. **Tail position** for `tail`/`delegate` (section 9): the marked
    call is the body's final expression, or its results are bound by a
    `let` and returned in order by a final `values`; between the call
    and the return only `let`s whose right-hand side is erased may
    appear; before the call, any statements for `tail`, none but erased
    `let`s for `delegate`; a match in tail position puts its branches in
    tail position. A `delegate` callee must be a named variable, and
    `coercible-of` returns the first anonymous `Coercible` proof about
    the function found in scope.
18. **Warnings** (a phantom constructor with a `many` field) go to
    stderr and do not stop elaboration.

## Type checking

19. **Every non-grammar argument, scrutinee or result gets an
    anonymous entry** (SR 14, second option): a call's returns, a
    match's returns and a `coerce` are bound to fresh anonymous `Dyn`
    entries carrying their types and any `is` rule, and dependent
    telescopes are instantiated with those. Grammar expressions are
    kept as trees rather than as anonymous entries with an `is` rule
    (section 3's picture); canonicalization should agree either way,
    but this is a representation choice, not the one section 3 draws.
20. **`is` entries at use sites** (SR 13): an argument landing on an
    `is` parameter or field, or a result landing on an `is` return, is
    written like any other and must canonicalize identically to the
    `is` expression; its erasure is that of the position.
21. **Match branches**: every constructor of the `Matchable` must
    appear exactly once, in any order (SR 17). A present branch whose
    forced unification contradicts is an error telling the programmer
    to write `(absurd C)`; an `(absurd C)` whose unification succeeds is
    an error. A `comptime-match` inside a branch that contradicts the
    branch's facts stops elaborating that branch and counts it as
    absurd (SR 7).
22. **An absurd-by-proof branch body, and an `absurd` function body,
    are erased positions** (SR 18); they must produce one value of a
    type with an empty `Matchable`.
23. **Proof arguments** to `predates`, `subterm`, the transitivity
    forms and the `coercible-*` forms are elaborated as erased
    expressions, so they may be calls to erased functions (SR 18).
24. **`(predates p)` accepts both shapes** (SR 15): the proof's subject
    may be the callee's level or the callee itself, compared after
    canonicalization; its level must be the current one.
25. **`(subterm p)`** must sit before an argument whose parameter is
    `subterm`-marked; the enclosing function must have a subterm
    parameter at the same subterm index, and the proof's second subject
    must be that parameter (SR 16). Fewer enclosing subterm parameters
    than the index is an error.
26. **Top-level calls**: a decrease annotation written at the top level
    is elaborated (so the proof must exist) but not checked against any
    level, since there is none (section 24); the `_` sugar forms are
    simply ignored there.
27. **Atom-vs-atom unification** makes the newer entry an alias of the
    older one (SR 21). Unifying a variable with a term that mentions a
    telescope binder (something inside an `Fn` type, say) is a hard
    error rather than a contradiction, since treating it as a
    contradiction would refute a branch on no evidence; no realistic
    program has hit this.
28. **Facts are read canonically to a fixpoint** rather than stored
    canonical at birth with re-canonicalization on every new rule (SR
    21); occurs checks on the canonical form keep the rules acyclic.
29. **Facts born inside a `let`'s right-hand side survive it** unless
    they mention entries that went out of scope; only match branches
    restore the fact table on exit. The design's "a fact dies with the
    scope it was born in" is not enforced for right-hand sides. The
    facts in question come from `comptime-match` verifications, which
    are unconditionally true, so this looked harmless.
30. **Constructors are `Const` even when born inside a body**, holding
    the unapplied constructor as their value; section 34 says nested
    definitions birth `Dyn`. No observable difference was found, since
    constructor application never consults the state.
31. **`Type` is compared by canonicalizing to `(Univ)`**; error messages
    print it that way. A `many` parameter or field of type `Type` (SR
    22) is accepted at its declaration and simply cannot be supplied in
    a non-erased position.

## Runtime representation

32. **Erased positions still occupy a slot.** Erased arguments and
    fields are passed and stored as a token value, printed `_`, rather
    than physically removed; erased `let` binders and match fields are
    left unbound. Only erasure *checking* stops non-erased code from
    reading them.
33. **Transparent types are represented as their `many` field**
    (section 38's requirement), so `coerce` is the identity at runtime.
    A value built by another constructor of a transparent type is the
    token (SR 23, "unspecified bits"). Since a match may go through a
    first-class constructor whose identity is only known at runtime
    (section 17), the evaluator looks up the representation when the
    match runs, from the constructors the branches name.
34. **Union values carry a constructor tag** in the interpreter, since
    nothing observes its absence; matches on unions with one real
    branch dispatch on it, which agrees with the one branch that can run.
35. **An absurd function's code raises** if ever reached; a match whose
    real branches are all absurd or phantom likewise compiles to code
    that raises.

## Not implemented

36. Macros (`Macro`, `Raw`, the expansion limit). `lib/kernel_input.ml`
    is untouched and unused (SR 28). The `--repl` flag reads one form
    at a time and prints every expression's value, which goes beyond
    section 16's one-expression file; it is a convenience only.

## Sugar (SUGAR.md)

37. All four forms are implemented as SUGAR.md describes them: `_` as
    a `def-fns` level births an anonymous level; `_` as a match
    annotation inherits the telescope of the enclosing function body or
    match branch, and is an error elsewhere; `(predates _)` proves
    `Predates` between the callee's level, which must canonicalize to a
    variable, and the current level; `(subterm _)` proves `Subterm`
    between the annotated argument and the enclosing subterm parameter
    at the same subterm index. All naive, as SUGAR.md says.
