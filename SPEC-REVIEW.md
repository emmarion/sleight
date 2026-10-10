# Spec review: bugs and ambiguities

A review of DESIGN.md as a handoff target: could
an implementer build an interpreter or compiler from them without
inventing core semantics? Written by a Claude session, not by the owner.
Every item is a reading of the text that may be mistaken, and every
suggested option is a question for the owner, not a decision. Nothing
here changes the design; it lists where the design appears to be
inconsistent or silent.

## 1. Apparent contradictions

1. **Multi-value expressions have no grammar.** §27 defines an
   expression as statements followed by a `values` line whose entries
   are each size one, a one-entry `values` being implicit. §26, §57 and
   §60 put a bare multi-return call such as `(divmod n d)` or
   `(unwrap-witness ...)` as a `let` right-hand side. That call has
   size two and cannot be written as a `values`. It seems the grammar
   needs a second terminal shape: a single call, match or `coerce` whose
   size is whatever it produces. A `tail` call returning several values
   as a function body seems to need the same.

2. **`tail` / `delegate` syntax.** §54 files them as annotation tokens
   that "annotate a form rather than heading a list", and §19 says a call
   is "marked". §60 writes `(delegate (inc ...))`, a wrapping head.
   `tail` is never shown.

3. **`Const` inside bodies.** §6, §28 and §29 say every binding inside a
   function body or match branch is `Dyn`, "nested definitions
   included", and §29 says "nothing else mints Const". §19 and §29
   item 3 say a state-forwarding `let` mints `Const` and is "one of the
   ways a Const reaches into a function body". The blanket statements
   appear to need a forwarding carve-out.

4. **Field multiplicity default.** §21 says the default is "still TBD";
   §13 and §14 say multiplicity is always explicit. Looks stale.

5. **Zero-branch match.** §25 says a non-erased match with no branches
   is "no longer needed" but does not forbid it, and under §21's rules
   it seems still legal as an exhaustive match over zero constructors.
   Open: is it allowed?

6. **Opaque built-ins and emptiness.** `Level`, `Predates`, `Subterm`
   and `Coercible` are written with `-> Type` signatures like type
   constructors, have no constructors, and no `def-adts`. §25 reads
   "empty" off a `Matchable`. If those types had one, an `absurd`
   function could apparently return a `Predates` proof as its
   contradiction. Open: do opaque types have no `Matchable`, and are
   they therefore neither matchable nor empty? Narrowed by §8's
   opening: nothing is matchable or empty until a `Matchable` for it
   is opened, and the built-ins have none to open. Settled: §8 now
   says so, the owner's decision.

7. **Contradiction discovered in a present branch.** §21 says the
   automatically refuted branch is written `(absurd C)`. Unstated: is a
   present branch whose entry unification contradicts an error, and is
   `(absurd C)` an error when no contradiction derives? §7 also lets a
   `comptime-match` prove a branch absurd mid-body; it does not say
   whether the rest of the body still elaborates or whether that branch
   then counts as absurd for §21's one-real-branch count.

8. **"Only run-position statements run at compile time."** §7 and §27
   say so, but macro expansion runs a `Macro`'s function at elaboration
   time inside any body. Probably wording only.

9. **The phantom-branch exemption rests on an unstated invariant.** §21
   lets a phantom branch's body ignore the match's erasures, and OPEN.md 2
   claims stripped programs run identically. Both seem to hold only if
   no non-erased value is ever headed by a phantom constructor. §14
   rule 2 appears to guarantee that, but the invariant is load-bearing
   and is not written down.

## 2. Gaps an implementer could not fill without guessing

10. **The reader beyond `$`.** Atom character set, case sensitivity,
    comments, whether numeric or string literals exist, and what `_` is.
    Also whether `:`, `->`, `is`, `many` and friends are resolved
    through the namespace, as §19's "everything can be shadowed"
    suggests, or recognized by the reader. Signature parsing needs a
    rule for where return entries end and the body begins; the only
    rule inferable from the examples is "items headed by a multiplicity
    token are return entries". Settled: a telescope is written in a
    bracket of its own, the owner's decision, so the rule is no longer
    inferred. Zero-parameter and zero-return forms
    such as `(Fn L ->)` are never shown.

11. **Forms with no syntax.** `comptime-match` has semantics in §28 and
    §54 but no shown syntax for the pattern or field binders. Settled
    for `comptime-match` alone: §28 now gives its syntax, the owner's
    decision; the rest of this item stands. The three
    §18 transitivity axioms have no names. `Macro` construction, the
    `Raw` type, anonymous `def-lvl`, and anonymous pattern binders are
    missing. §56 says every field gets a binder, so an implementer needs
    to know whether `_` is one.

12. **No prelude.** `List`, `Nat`, `False`, `Raw`, `Special`, `Macro`,
    `Univ`, the opaque types, and the `Special` entries for `let`,
    `match` and the rest must exist before user code. §19's macro type
    `List Raw -> Raw` depends on §55's user-defined `List`. Open: what
    is built in?

13. **Use-site rule for `is` entries.** §3 and §12 define
    `expr is name` and say the type comes from the expression, but do
    not say what is checked when a call argument lands on an `is`
    parameter, a body returns into an `is` return, or a constructor
    application fills an `is` field. One reading: the supplied
    expression must canonicalize identically to the `is` expression
    while its erasure is judged syntactically. Also unstated: whether
    the `is` field's argument is written at a constructor application
    at all, given saturation requires one argument per telescope entry.

14. **Dependent instantiation with non-grammar arguments.** Return
    telescopes and later parameter types are instantiated with a call's
    arguments. §9 bans calls in types and §5 gives anonymous entries
    only to constructor applications. A nested call `(f (g x))` or a
    match as an argument leaves a dependent type nothing to refer to.
    Options seen: restrict dependent positions to §5-grammar
    expressions, or give every non-atomic argument, `values` entry and
    scrutinee an anonymous `Dyn` entry. The `tail` and `delegate` checks
    and the scrutinee's forced rule seem to need the same decision.

15. **What `(predates p)` accepts.** §57 uses `(Predates (Level) M L)`
    with `M` the callee's level read from its `Fn` type. §18's axiom 3
    instead produces `(Predates (Fn ...) f L)` about the function value.
    Open: which shapes are accepted, and are both endpoints compared
    post-canonicalization against the callee's level and the current
    level?

16. **What `(subterm p)` checks, and mismatched subterm arities.**
    Unstated: that `p` must be `(Subterm A arg B counterpart)` with
    `arg` the annotated argument and `counterpart` the enclosing subterm
    argument at the same subterm index, and that the annotated argument
    must sit on a callee parameter marked `subterm`. Also undecided: the
    case where the caller has fewer subterm parameters than the chosen
    index, or none at all, and the case where the callee has fewer than
    the caller. §17's lexicographic order is only defined for tuples of
    equal length.

17. **Match exhaustiveness and order.** Not stated whether every
    constructor in the `Matchable` must appear exactly once, whether
    branch order matters, or what a duplicate means. Settled:
    ASSUMPTIONS 21, §21.

18. **Erased-position list.** §14 omits the arguments of
    `prove-subterm`, `prove-predates`, `level-of`, `matchable-of` and
    the transitivity forms, the proof inside `(subterm p)` and
    `(predates p)`, the body of an absurd-by-proof branch, and the body
    of an `absurd` function. §25's "compiles to no code" suggests
    erased, but §59's body is a `many` value so the example does not
    settle it. The multiplicity of the empty-type value is also
    unstated.

19. **Dependent motive checking.** §26 makes the annotation mandatory
    but does not say the branch body is checked against the annotation
    re-canonicalized under that branch's forced facts. That seems to be
    the only reading under which a dependent match works.

20. **`def-fns` level and the level-mint marker.** Must the level on a
    `def-fns` be a `def-lvl`-minted entry, or any `(Level)`-typed
    variable such as a parameter? Does `prove-predates` canonicalize its
    arguments first, so an alias made by `(let ((erased L2)) L)` works?
    §5's forwarding list omits the marker, so as written an alias
    apparently cannot be used there.

21. **Fact table maintenance.** §7 records rules canonical when minted,
    but later branch-forced rules make earlier stored forms stale.
    Unstated whether reads canonicalize to a fixpoint or every new rule
    re-canonicalizes the table with undo on branch exit. Also unstated
    which atom becomes the alias when two atoms unify.

22. **`(many Type A)`.** §21 only says types "should" be erased. A
    `many` field or parameter of type `Type` is writable but appears
    uninhabitable under §14 rule 2, since type constructors enter
    erased. Open: forbid, or note.

23. **Transparent unions.** §33 represents the type as its one `many`
    field, but values built by the other all-erased non-phantom
    constructors have no field. Their representation seems to need
    stating, e.g. as unspecified bits of the field's size.

## 3. Smaller ambiguities and housekeeping

24. §18 refers to `main`'s level, but nothing designates a `main`; §27
    says the top-level value is what a REPL would print.
25. §8's "multiple inconsistent Matchables for the same type" seems
    unable to arise if `def-adts` is the sole minting site and each
    mints a fresh type constructor. Open: how can it occur? Settled by
    §8's invariant (the owner's decision): two opened `Matchable`s
    naming one thing are unified and merged, or contradict, so the
    ambiguity error is gone.
26. Return-telescope names are positional and apparently not in scope
    in the body, while parameter names are. Not stated.
27. §27 requires the file to end in a size-one expression; §60's
    fragment ends in a statement.
28. `lib/kernel_input.ml` (since deleted, having stayed unused) carried
    `Comptime` and `Inacc` plus optional multiplicities on binders and
    match returns, all removed by §14, §27 and OPEN.md 8. README.md is the
    dune hello-world stub.
29. Whether an opened `Newtype` for `C` beside an opened `Matchable`
    marking `C` phantom is a contradiction (§8, §33): the proposal
    left it unsettled. Settled: it is not, the owner's decision; §8's
    "a `Newtype` is only recorded" stands, and
    `tests/open_newtype_phantom.sl` shows the pair recorded. The
    argument that such a pair is dead code by inhabitation is not one
    this language admits, a `many` parameter holding a phantom
    constructor in an erased call (§14), which the same test shows.
30. OPEN.md 2's erasure invariant has no clause for `open-absurd` (§8),
    which compiles to absurd code and never runs; the proposal listed
    the clause as unsettled.
31. Whether `open-absurd` with `_` as a whole function body makes
    §25's `absurd` marker redundant for the route through a
    `Matchable` contradiction; listed as unsettled by the proposal.
    Settled: §25 now names the division, the owner's decision.

The three items most likely to make a handoff fail outright appear to
be 1, 13 and 14, since an implementer would have to invent core
semantics to get past them.

## 4. From the bug sweep after the `at` redesign

Found by a Claude session probing the implementation against DESIGN.md
after the merge of the spec files; each is a reading that may be
mistaken and a question for the owner, not a decision. BUGS.md 5 to 13
hold the implementation side.

32. **The cell `at` forms in an erased position.** §39 makes
    `(at (f ...))` an error in an erased position, as §19 does `tail`.
    §37 says nothing for `(at (u ...))` or the per-argument `(at)`
    marks there, and the implementation does three things: the
    wrapping form is accepted and used for nothing, the per-argument
    mark is checked and, since nothing is bound in an erased position,
    fails on any argument that is not a variable, and the call form is
    refused. Open: which of refusing, ignoring and checking is meant.
