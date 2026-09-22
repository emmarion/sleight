# Tooling wishlist for writing .sl by hand (or by LLM)

Observations from one session rewriting `mini/` without fuel: each item is a
point where the session lost time or guessed, with what would have helped.
Nothing here is a design decision; it is a log of friction, in the order met.

1. **Paren-depth locator.** Every unbalanced file was diagnosed with an ad hoc
   script printing the nesting depth at each `(many f :` line. A checker
   error like `line N: syntax error: missing )` names the end of the file; a
   per-form report ("form starting at line N opened 3 more than it closed")
   would have found each of the five imbalances met so far at once.
   Closed by `bin/shape`, which reports each form's opening `line:col` and
   the line it closes on; see item 26.

2. **Error locations inside a form.** Type errors report the line of the
   enclosing `def-fns` (e.g. `expected 3 arguments, got 2` on a 20-line
   function). The offending sub-expression, or at least its line, would cut
   most of the guesswork.

3. **Shadowing report.** `Canonical` exists in both `mini/canon.sl` (two
   arguments) and `mini/elab.sl` (three); after loading both, the first is
   unreachable by name and a use of it fails with an arity error far from
   the cause. A warning on redefinition, or a way to qualify names, would
   have caught this immediately.

4. **`let-match` on GADT-refined evidence.** `let-match` insists on a
   single-constructor type, so evidence types with two constructors (one
   of them ruled out by the index) still force a nested `match`, which is
   what makes these functions 20 levels deep. Accepting a `let-match` when
   the index leaves one constructor possible would flatten most of
   `elabfn.sl`.
   Implemented in DESIGN.md §16: `let-match` now accepts the unique
   structurally unrefuted constructor, including a phantom at `erased`.

5. **`else` does not refine.** After `(else ...)` the scrutinee is not known
   to differ from the listed constructors, so an empty erased match there is
   refused; the workaround is enumerating the remaining constructors by hand
   (14 keys in `axiom-check`). A refined `else` would remove that noise.

6. **Arithmetic on `Lt`.** `Lt n (Succ (Succ n))` from `lt-succ` needs
   `lt-weaken`, `le-trans` needs its middle term spelled, and every one of
   these was a compile-fix round. A small solver for `Lt`/`Succ` goals over
   the prelude lemmas, even one that only chains `lt-succ`/`lt-weaken`/
   `le-trans`, would remove a class of errors.

7. **Wrapper boilerplate.** Facts about the entries of a context are stated
   over a `(MkCtx n s e r a l sa)` record, so every wrapper (`Sc`, `ScL`,
   `Has`, `Grew`, `Cov`, ...) carries seven erased fields and every use is
   `(MkSc _ _ _ _ _ _ _ t p)`. Record projections usable inside types, or a
   way to define a wrapper by "the `e` field of `ctx`", would remove most of
   the underscores in `mini/ctx.sl` and `mini/elabfn.sl`.

8. **Positional evidence lists.** Constructors with 20 to 40 erased fields
   (`EXCall`, `EBCons`, `MkWF`) are called positionally; a misordered pair
   surfaces as a type mismatch with no hint of which position. Named
   fields, or an error naming the position, would help.

9. **Subterm bookkeeping.** Mutual recursion needs every function of a group
   to align the same number of `subterm` positions, with `is`-typed
   constants (`(POuter (PInner))`, `(Nil (Raw))`) as fillers. A way to
   declare "this call is a sub-call of that one" (or an implicit phase
   position) would remove the filler arguments.

10. **Whole-file compile per fix.** Each fix recompiles the whole prefix of
    files; an incremental mode that keeps the earlier files' environment
    would make the edit loop several times faster.

11. **Duplicate constructor names across files.** `CRNil` (a helper in the
    new `elabfn.sl`) silently shadowed `CRNil` of `CheckRets` in
    `mini/elab.sl`, and `ALOk` shadowed `AfterList`'s; `AOk` is already
    defined by both `mini/unify.sl` and `mini/elab.sl`. The symptom is an
    arity error at the use site. A one-line `uniq -d` over constructor
    names found all of them at once; the checker could do the same.

12. **Branch misalignment reads as a type error.** When a branch closes one
    paren too few, the next branch lands in the enclosing `match`, and the
    error is `BTrue is not a constructor of SameDec` or `Ref is not a
    constructor of ExprArgsDec`, far from the missing paren. An editor
    that shows the enclosing `match` of each branch (or the checker naming
    the branch's scrutinee and line) would turn each of these into a
    one-line fix; a formatter that re-indents by nesting would make the
    imbalance visible before compiling.

13. **No branching on erased data, so keys are enumerated.** An erased
    proof of `AxiomKey k` cannot be matched with three real branches, and
    `else` does not refine `k`, so the three axiom keys are dispatched by
    matching `k` itself and the other fourteen keys each get an empty
    erased match. Either a refined `else` (item 5) or an erased match that
    only refines (no runtime branch) would remove that.

14. **The good news, for calibration.** Once the parens balanced, the
    whole 2700-line elaborator type-checked with the subterm discipline
    (three lexicographic positions across a group of sixteen mutually
    recursive functions, `is`-typed constants as phases) accepted on the
    first try; the checker's GADT refinement through erased single-branch
    matches and omitted impossible branches behaved exactly as guessed.
    The cost was almost entirely in bookkeeping, not in the type system.

15. **A stack overflow says nothing about where it came from.** Three
    of the `mini/` end-to-end programs overflowed the OCaml stack inside
    `slc` under the default 8MB limit. This item used to read that the
    overflow was in the compile-time interpreter and wanted a
    heap-allocated continuation for it; both were wrong. The overflow
    was in the emitter, in two walks over the compile-time store that
    recursed once per allocated block, and an accumulator in each was
    the whole fix (ASSUMPTIONS 148). Finding that took a debugger,
    because `Fatal error: exception Stack overflow` names neither the
    function nor the depth, and the wrong guess stood in two files for
    a session. A runtime that named the deepest frame, or a compiler
    flag that reported which recursions are not in tail position, would
    have answered it directly. It happened a second time, to a later
    session: asked whether the *reference* interpreter overflowed too,
    it measured a program whose result was a 200000-deep `Nat` and read
    the overflow as the evaluator's, when the backtrace put it in
    `Ffi_core.nat_view` spelling that `Nat` in unary to print it
    (ASSUMPTIONS 150). Both times the fix was to look at a backtrace
    instead of at the source, and both times the wrong guess was
    written down first.

16. **A way to ask for a tail call and be told when it is not one.**
    The `tail` mark does this for a call the programmer suspects, and
    marking the two walks above pins them against a later edit. What is
    missing is the other direction: nothing lists the recursions in a
    program that are *not* in tail position, so a walk whose depth grows
    with the input is found by overflowing rather than by reading.

17. **A result type's new constructor ripples through every caller.**
    Giving unification's walk a stuck answer meant turning each
    `(let ((erased o) (many st) (erased p)) (call ...))` in six mutually
    recursive functions into a two-armed `match` whose second arm wraps
    the rest of the body, fifteen times, by script. Either a refactoring
    tool for "this call's result gained a case" or a language form that
    threads a `Stuck`-like case through a sequence of `let`s (the shape
    an error monad has) would make such a change a one-liner per site.

18. **Pattern variables silently shadow outer bindings.** `(TotIs a b c
    ty p sc)` inside a function that had already matched its context as
    `(MkCtx n s e r a l sa)` rebound `a`, and the error was a type
    mismatch on a later use of `a`, three lines away. A warning on a
    pattern variable that shadows a binding of the enclosing function
    would name the problem at its source.

19. **No forward references between `def-adts` groups.** A relation may
    mention one declared later in the same group but not in a later
    group, so adding a premise that used `Mem` and `NotApp` meant moving
    those two out of their groups to above the user. Either allowing
    a file's groups to refer to each other or reporting the fix
    ("declared below, at line N") would save the shuffle.

20. **Adding an index to a relation edits every constructor site.**
    Giving `Scoped` a depth meant one more positional erased argument at
    each of about 170 applications and patterns of its eleven
    constructors across three files, nearly all of them `_` or a dummy
    binder, done by script and checked by the compiler. Named or
    optional erased arguments, or a pattern form that names only the
    fields it uses, would make such a change local to the definition.

21. **A `_` in an unannotated top-level `let` has nothing to solve it.**
    Test files that build evidence by hand had to spell out every depth
    (`(ScTyApp ents (Zero) ...)`) where the same term inside a function
    body infers it from the expected type. Letting a run-position `let`
    take an expectation from a later use, or reporting which `_` is
    unsolved with its expected type, would help.

22. **Unannotated result binders look like grouped binders.** While writing
    the palindrome proofs, `(let ((erased before) (erased after)) ...)` was
    accidentally shortened to `(let ((erased before after)) ...)`. The latter
    means a binder named `after` with type `before`, unlike the explicitly
    typed groups in signatures. A diagnostic suggesting separate result
    binders when the supposed type names a value would identify the typo.

23. **A library-only check mode with explicit success.** The palindrome
    development repeatedly checked a growing library with both the reference
    checker and `slc`. Successful reference checks print nothing; `slc`
    produces OCaml even when only checking is wanted. A shared `--check`
    mode reporting files checked and elapsed time would make this workflow
    clearer. A String-to-String final expression instead makes the driver
    wait for stdin; reporting that transition would distinguish waiting for
    input from a slow checker.

24. **An erasure report for proof-heavy programs.** The Manacher proof uses
    recursive list decompositions and enumerates excluded window lengths in
    erased code. Confirming these costs disappear currently means reading
    generated OCaml. A report of retained functions and runtime fields,
    optionally with call counts, would make both proof erasure and the
    linear number of expansion steps easier to audit.

25. **Show what an inference hole resolved to.** Cleaning up the palindrome
    proofs replaced repeated erased indices and whole `Cons`/`Succ` trees
    with `_`, as well as type arguments. An editor hover or elaboration
    report showing each hole's resolved term would make these shorter calls
    easier to review. A refactoring preview of inferable arguments would
    also help choose which explicit terms still explain the proof.

Items 26 onward are from a session writing `tests/longest_palindrome.sl`,
`tests/palindrome_bridge.sl` and `tests/manacher.sl` (a linear-time search
with its correctness proof, about 1100 lines), in the order met. Those three
files are not in this tree; they are at commit `4912ada`
(`origin/palindrome-archive/fable` at the time of writing).

26. **Item 1, closed.** `shape.ml` came over from the pre-restart history
    (`simply-typed-archive/main`, tip `06b9f3e`, last touched there by
    `56d9a2f`) and now builds as `bin/shape`: `shape file` lists every form
    spanning more than one line with the line it closes on, `shape --closers
    file` says what each run of `)` closes, and a diff of two runs reduces a
    stray paren to one hunk. It found all four imbalances the originating
    session met, including the branch-nested-in-a-branch case of item 12,
    from the `--closers` view. It now reads the checker's own lexer, so the
    comment and string caveat recorded here is gone; on this session's check
    the text-scanning version it replaced had been reporting `final depth 6`
    for the balanced `self/emit.sl`. One caveat stands: a surplus `)` at the
    top level pops an empty stack silently, so for that case the checker's
    `line N: unexpected )` is the sharper report.

27. **Arithmetic again, now on `Add`.** Item 6's `Lt` chains recurred
    (`lt-le-trans` wanting its middle term as `(Succ x)`, `add-le-left`
    giving `Lt a (Succ c)` where the strict form was needed), and `Add`
    added its own: associativity, functionality, cancellation against
    `Lt`, and `Double` as `Add a a` were each written as a lemma on the
    spot (`add-assoc`, `add-fn`, `add-cancel-lt`, `double-add`,
    `double-lt-inv`, `radius-lt`). About one compile round in five was
    one of these. A prelude section for `Add`/`Lt`/`Double` algebra, or
    the solver item 6 asks for, would have removed them.

28. **A list-relation library.** `Nth`, `Drop`, `Take`, `Concat`,
    `Length`, a reversed-prefix relation and a zipper, with the obvious
    lemmas (functionality, existence under a length bound, composition
    of drops, prefix from concat and length), were written from scratch
    here and, on this session's reading, partly overlap `self/base.sl`.
    Some forty of the file's lemmas are of this kind. Whether such a
    library belongs in the prelude is the owner's call; the wish is for
    it to exist once.

29. **Item 9's phase trick, recorded.** Three mutually recursive
    functions calling each other in a cycle on the same suffix were
    accepted with a second `subterm` position that is an *erased* `Nat`
    carried with an `Eq` proof pinning it to a literal (`2` for the
    step, `1` for the transition, `0` for the scan); the caller passes
    the smaller literal and the bare call infers the `Subterm` proof from
    the pinned value. It costs nothing at runtime and no filler value,
    which is better than item 9's `is`-typed constants, but it is still
    a trick a reader has to be told about.

30. **Item 20 again, three times.** Adding an input-list index to the
    radius list, to its bound and to the loop's state (so that a chain of
    certificates could be read back from a known start without a
    uniqueness lemma about zippers) touched about fifteen sites across
    three ADTs and one `def-fns` group, all by script. Same wish.

31. **More calibration.** A runtime value as a type index
    (`Bound m b xs l r bk`, with `bk : Back m xs l r` holding `many`
    fields) worked on the first try, as did an erased `match` with `many`
    results and one real branch nested four deep, `let-match` on a
    single-constructor certificate, and calling a `many` decider
    (`take-dec`, `nat-cmp`) from an erased lemma. The erased half of the
    file, some 60 lemmas, extracts to unit stubs. As in item 14, the
    checker was never the obstacle; the rounds went to arithmetic,
    parens and positional arguments.

32. **Inspect post-erasure code around a failed mark.** The uniqueness port
    exposed tail/delegate failures caused by singleton result wrappers and
    unused erased bindings. A bounded dump of one function before and after
    normalization, including physical result multiplicities and binder IDs,
    would likely make these failures easier to diagnose than temporary source
    instrumentation. Showing logical versus physical at returns alongside it
    would help check that stores remain before the exposed tail call.

33. **Item 32, met again.** Finding why a let-bound match multiplied the
    output took a temporary printer in `lib/elab.ml` and another in
    `self/elab.sl`, the second re-extracted into the compiler to read one
    function's code before and after normalization. The same dump, with
    the environment's counters beside it (entries minted, rules in force,
    words in scope), would also have shown at once which of those grew
    with the program, which took prefix timings and a profile to see.

34. **A hermetic bootstrap.** `self/bootstrap.sh` reads `self/*.sl` when
    it extracts the compiler and again, minutes later, when the compiler
    compiles itself, so an edit or a `git stash` in between feeds the two
    steps different sources and the fixpoint compares the wrong things.
    Copying the sources into the build directory at the start would make
    a run answer for one tree. `bench/bench.sh` has the complementary
    problem: its pinned commit is unreachable in a shallow clone, and
    where it is reachable the pinned sources no longer elaborate under
    the current prelude, so the "slc on pinned slc" line measures nothing
    and says so only in passing.

35. **Profiles and growth.** Extraction keeps function names, so
    `callgrind` on a `-g` build of `slc.ml` reads directly in terms of
    the source; a script for that, and a sample under `bench/` whose
    elaboration re-runs one file after a large scope (which is how the
    cost growing with the scope was first seen, `self/base.sl` costing
    six times as much at the end of the program as at its start), would
    have saved the setup. Three of the four costs found this way were
    linear walks of lists that grew with the program (the words list,
    the temporaries, the rules list), and one was an exponential copy;
    a counter per list in the same dump as item 33 would show them
    without a profiler.

36. **`and` and `or` evaluate both operands.** They are functions, so
    `(and cheap expensive)` runs the expensive test whether or not the
    cheap one failed; `hide-words` tested every word's membership in the
    temporaries list even below its bound. A short-circuiting form
    (a nested `match` today, a macro once macros land) is the idiom, and
    the base helpers' names invite the mistake.

37. **Backwards references and helpers.** A helper defined later in the
    file is unusable earlier (`atoms-of` at line 2241 of `self/elab.sl`
    could not serve `prepare-argument` at line 1590), so a smaller copy
    was written above it. Not a tooling gap, but a report of where a
    name is defined against where it was wanted would have settled it
    faster than the arity error that followed.

38. **Identity re-matches in the emitters.** A match on a plain type
    with no `else` whose every arm rebuilds the arm's own constructor
    from its fields in order could emit its scrutinee; the extracted
    slc has 39 such arms, in the trie walkers among them, each
    allocating a copy per level. The `slc-performance-investigation`
    branch had this in both emitters (its commit "Extraction: a match
    whose every arm rebuilds its own constructor is its scrutinee")
    and measured it at about a fifth of a compile that has since
    changed shape; on today's profile the trie walk is a quarter of
    the run, so the gain would be a few percent. Under mutable blocks
    it needs the argument that a block a `many` match read is mutated
    by neither side afterwards. Source-level, section 38's `coerce`
    with `coercible-ctor` says the same at zero cost.

