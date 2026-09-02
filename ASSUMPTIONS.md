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
17. **Tail position** for `tail`/`delegate` (section 9) is judged on
    the post-erasure code after every `let` that only renames (which is
    what a `coerce`, or a `let` of a variable, erases to) is resolved
    away: the marked call is then the body's final expression, or its
    results are bound by a `let` and returned in order by a final
    `values`; before a `tail` call any code may run, before a `delegate`
    call none; a match in tail position puts its branches in tail
    position. A `delegate` callee must be a named variable, and its
    arguments must resolve to the function's non-erased parameters in
    order. `coercible-of` returns the newest anonymous `Coercible` proof
    about the function found in scope, so an anonymous proof born later
    (a `(let (erased _) (coercible-refl g))`, say) shadows the delegate
    proof; harmless, any such proof being true, but not what section 38
    says it fetches. Open.
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
    an error.
22. **An absurd-by-proof branch body, and an `absurd` function body,
    are erased positions** (SR 18); they must produce one value of a
    type with an empty `Matchable`.
23. **Proof arguments** to `predates`, `subterm`, the transitivity
    forms and the `coercible-*` forms are elaborated as erased
    expressions, so they may be calls to erased functions (SR 18).
24. **`(predates p)` accepts the level shape only** (SR 15; settled by
    the owner, section 9): the proof's subject must canonicalize to the
    callee's level and its level to the current one. A `Predates` about
    the function value, which `predates-subterm` can produce, is
    rejected at a call.
25. **`(subterm p)`** must sit before an argument whose parameter is
    `subterm`-marked; the enclosing function must have a subterm
    parameter at the same subterm index, and the proof's second subject
    must be that parameter (SR 16). Fewer enclosing subterm parameters
    than the index is an error.
26. **Top-level calls**: a decrease annotation written at the top level,
    the `_` sugar forms included, is an error (settled by the owner,
    section 24).
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
    facts in question come from `comptime-match` verifications in a
    run-position right-hand side, which are unconditionally true, so
    this looked harmless.
30. **Nested definitions birth `Dyn`**, as section 34 says: a
    `def-adts`, `def-lvl` or delegate proof inside a body births `Dyn`
    entries, and the body's code binds each nested constructor's value.
    In run position the same births are `Const`, and the values of
    `Const` entries form the runtime environment every closure and
    run-position statement runs in (section 34's "embedded into the
    code").
31. **`Type` is compared by canonicalizing to `(Univ)`**; error messages
    print it that way. A `many` parameter or field of type `Type` (SR
    22) is accepted at its declaration and simply cannot be supplied in
    a non-erased position.

## Runtime representation

32. **Erased positions occupy no slot at runtime** (sections 34, 38).
    A closure takes only its `many` parameters, a call passes only its
    `many` arguments, a constructor value holds only its `many` fields,
    a `values` and a function's results carry only the `many` entries,
    and printing shows a value as its constructor over those fields.
    An all-erased `let` compiles to nothing; a mixed one binds its
    `many` binders. The token value stands in only where elaboration
    needs a Const for an erased entry (an erased `let` binder in run
    position, an erased `comptime-match` field, a `Level`).
33. **Representation is decided at elaboration**, per section 38: a
    value is the tuple of its `many` fields, one field bare and none the
    token (SR 23's "unspecified bits"), and it carries a tag only when
    its type is an enum with more than one non-phantom constructor. A
    constructor's runtime value carries its tag flag, so applying a
    first-class constructor needs no lookup; a match reads whether to
    dispatch off the `Matchable` in scope (its type plus the listed
    constructors' `ValCtor` types), so a first-class match compiles the
    same way as a named one. `coerce` is the identity at runtime.
34. **Unions are never tagged**, so a match on one binds its single
    real branch's fields from the tuple without inspecting anything;
    the interpreter prints an untagged value as its fields, with no
    constructor name. A transparent union's other non-phantom
    constructors build the token.
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
    The telescope `_` inherits from a function body is the return
    telescope with the parameters substituted in; an earlier version
    substituted without regard to each entry's depth, so a second
    return entry mentioning the parameters (an `(Add a b c)` proof after
    the sum `c`, say) was checked against the wrong statement
    (`tests/nat_add.sl`). Fixed; an explicit annotation was never
    affected.

## Soundness fixes from an audit session

A later autonomous session, asked to check that nothing false (in
particular `(False)`) can be proved, probed the checker and changed the
interpreter in four places. Items 38-41 record those changes. As
elsewhere in this file, each is the implementation's reading, offered as
a candidate question, not a settled decision, except item 41, which the
owner has since settled. The reasoning is a Claude session's and may be
wrong (CLAUDE.md rule 1); where possible it was checked by compiling
(rule 2).

38. **`comptime-match` rejects a phantom constructor pattern.** §15 has
    `comptime-match` read a non-erased scrutinee with a non-erased
    discriminant, and §20 rule 2 says no non-erased value is ever headed
    by a phantom constructor, so asserting a phantom constructor of a
    real value can never be a legitimate use. The prior code, on a
    transparent enum, treated the phantom (unspecified-repr) constructor
    as having no `many` fields and skipped the discriminant check
    entirely, so `(comptime-match x (F f))` for a phantom `F` succeeded
    against any value and birthed `F`'s erased fields as `Const` tokens
    — and since erased fields carry no runtime bytes (KERNEL.md), a
    field of type `(False)` among them was forged into scope, collapsing
    consistency. The pattern's constructor is now rejected when it is
    phantom. This looks like plugging an implementation gap rather than
    a design choice, but it is recorded here in case the owner reads §15
    as permitting a phantom pattern with some other intended meaning.

39. **A `let` binding a call's leading `many` returns at `erased`
    projects the results.** Post-erasure code for a call carried every
    one of the callee's `many` returns. A `let` (or any position) that
    took some of those leading returns at multiplicity `erased` then
    misaligned the rest: in run position it popped the wrong values, and
    in a compiled body it raised an arity mismatch, both observable.
    The call's code is now narrowed to the returns the position keeps
    `many` before they are bound. Pure correctness as far as the session
    could tell; the values a `let` binds should be its own.

40. **An atom/atom unification never writes a rule onto a rigid entry.**
    §18's forced unification aliases the newer of two atoms to the
    older. Constructors and type constructors are `rigid` (born so in
    the prelude and by `def-adts`), and two distinct rigid atoms
    unifying is §18's second contradiction. The prior orientation went
    purely by entry id, so a `def-adts`-born constructor whose id
    happened to exceed a `Dyn` variable's could receive a rewrite rule,
    aliasing one rigid constructor to another and defeating the
    disjointness check (§19). Orientation now always lands the rule on a
    non-rigid entry; two rigids still contradict. A correctness fix, not
    a design choice.

41. **A phantom-constructor branch under an *erased* scrutinee is an
    ordinary branch** (settled by the owner; §12 now says so). §12's
    exemption of a phantom branch from the match's result erasures, and
    its exclusion from the one-real-branch count, rested on the
    invariant that no non-erased value is headed by a phantom
    constructor (§20 rule 2, SPEC-REVIEW 9). That holds for a `many`
    scrutinee only: an erased value may well be phantom-headed. So a
    phantom branch counts as dead only under a `many` scrutinee; under
    an `erased` one it is a real branch, subject to the one-real-branch
    rule and producing the match's declared result, its fields erased
    like every other branch's.
