# Implementation assumptions log

A running log of the assumptions the prototype interpreter (`lib/`,
`bin/`) makes where DESIGN.md is silent, ambiguous, or where the
implementation takes a shortcut. Written by a Claude session working
autonomously at the owner's request; nothing here is a design decision.
Every item is a candidate question for the owner, and the owner's answer
may well be different from what the code does. Numbers in
SPEC-REVIEW.md are cited as `SR n` where an item there covers the same
ground.

## Prelude

5. **Names of the `Special` variants** are the form name prefixed with
   `%` (`%let`, `%match`, ...), so that the entry `let` — whose value is
   `(%let)` — is distinct from the constructor. Only the prefix is an
   invention; it is not settled by DESIGN.md.

## Grammar shapes DESIGN.md leaves open

13. **A `def-fns` level** may be any variable whose type is `(Level)`,
    not only a `def-lvl`-minted one; only `prove-predates` insists on the
    mint marker (section 18).

14. **`def-adts` ordering**: a type constructor's own telescope may
    mention types defined earlier in the same `def-adts`, not later
    ones; every constructor may mention every type of the group.

## Type checking

19. **Every non-grammar argument, scrutinee or result gets an
    anonymous entry**: a call's returns, a
    match's returns and a `coerce` are bound to fresh anonymous
    entries carrying their types and any `is` rule, and dependent
    telescopes are instantiated with those. Grammar expressions are
    kept as trees rather than as anonymous entries with an `is` rule
    (section 5's picture); canonicalization should agree either way,
    but this is a representation choice, not the one section 5 draws.
31. **`Type` is compared by canonicalizing to `(Univ)`**; error messages
    print it that way. A `many` parameter or field of type `Type` (SR
    22) is accepted at its declaration and simply cannot be supplied in
    a non-erased position.

## Runtime representation

32. **The token value stands in only where elaboration needs a
    `Settled` for an erased entry**: an erased `let` binder in run
    position, an erased `comptime-match` field, a `Level`.
33. **A constructor's runtime value carries its type's tag flag**, so
    applying a first-class constructor needs no lookup; a match reads
    whether to dispatch off the `Matchable` in scope (its type plus the
    listed constructors' `ValCtor` types), so a first-class match
    compiles the same way as a named one.
35. **An absurd function's code raises** if ever reached; a match whose
    real branches are all absurd or phantom likewise compiles to code
    that raises.

## Interpreter conveniences

36. The `--repl` flag reads one form
    at a time and prints every expression's value, which goes beyond
    section 27's one-expression file; it is a convenience only. An
    input that fails leaves the scope, the goal (section 71) and what
    `--extract` writes as they were before that input, except that a unique entry consumed by run-position code the input
    ran (section 27) stays consumed, since that code may have updated
    its value in place.

## Extern types and the FFI (section 42)

42. **The FFI table is `lib/ffi.ml`.** The prelude itself is
    `lib/prelude.sl`, embedded into the binary by a dune rule so the
    interpreter needs no path to it at runtime.
43. **Extern payloads.** A value of an extern type is a `Value.payload`
    (a zarith integer, a byte-string slice as in item 48, an array,
    bytes or a `Raw`) carrying its type's runtime record; an extern
    type's implementation is a pair construct/destruct over constructor
    indices, so matching, `comptime-match` and printing all go through
    destruct and see the model's constructors.
44. **The test runner elaborates the prelude per extern mode.**

## Strings and literals (sections 42 and 45)

48. **The FFI holds a `String` as a slice of an OCaml string** (offset
    and length); destructing an `SCons` yields the byte and the tail
    slice over the same buffer, so matching is structural and copies
    nothing, and same-level recursion over a string is discharged by an
    ordinary `subterm` proof. Constructing an `SCons` copies.

51. **Literal entries are minted directly.** Both compilers mint a
    numeral's two entries directly rather than elaborating
    `(let ((many _) (erased _)) (bin-to-nat <spelling>))`
    (`Elab.intern`, slc's `intern-numeral`): the `Nat` holds the FFI's
    integer, or under `--no-extern` a Peano chain built in OCaml
    (`Elab.peano`), and the proof is a token whose type spells the
    numeral in `Bin` (`Elab.bin_term`). The entries are not in the
    scope list at all; resolution goes through the literal table (212).

54. **Resource limits under `--no-extern`.** Stripped, `bin-to-nat`'s
    model runs `add` in unary, so calling it on a spelling around a
    million overflows the interpreter's stack. A numeral does not call
    it (item 51): its chain is built in OCaml, iteratively, though any
    walk that recurses down the chain, the extractor's for one, still
    has the chain's depth to cover. Printing one does not walk it: a
    printed `Nat` spells through `Z.to_string` under the FFI and counts
    the model's chain down without it (item 154). The tests keep their
    numerals small.

## Programs (section 27)

Asked for by the owner in chat: an ADT read by the driver, "quasi
monad", efficient, able to read a whole file by name, write a whole
string to a file, write to stdout or stderr with a flush, read a line
from stdin, read the command-line arguments and exit with a code, kept
alongside the `String -> String` form as an optional alternative.

57. **The level index is load-bearing.** A continuation's `UniqueFn`
    type names the level its function was defined at, and `subterm` marks
    are part of its type, so a recursive helper cannot itself be a
    continuation and a same-level wrapper cannot call it. The pattern
    the tests use (`tests/io_echo.sl`): the helper takes the world and
    gives it back `at` itself, sits at a level below the program's, and
    each step wraps it in a fresh `def-unique` at the program's level
    that calls it. A cost of the design, recorded rather than smoothed
    over.
    The index does not confine a program to one level, though:
    `tests/io_lift.sl` embeds values from two levels in a program at a
    third by coercion, at no runtime cost, and `tests/io_lift_runtime.sl`
    does the same by rewrapping each continuation; neither is in the
    prelude, their usefulness being an open question.

59. **Program arguments** are what follows `--` on the interpreter's
    command line; `; args: a b` supplies them to a test, `; stderr:
    text` lines are what it must write to stderr and `; exit: n` the
    code it must exit with (0 when absent). `ReadLine` strips the
    newline and answers `None` at end of input.

60. **String literals are bound directly.** Neither compiler elaborates
    a string literal's characters: the reference binds a `Settled`
    `String` straight to its value (`Elab.str_value`), the FFI's slice,
    or under `--no-extern` the model's list built in OCaml, its
    characters off the Peano chain numerals share (item 51), so the
    extractor, which shares by identity, emits each `Nat` once per
    program; slc's `intern-string` binds the FFI's payload. A string
    does not intern its characters' numerals.

## OCaml extraction (extract.ml)

Written by a session working autonomously at the owner's request, in
chat: extraction "in the sense of Coq's extraction", with compile-time
computation embedded in the extracted OCaml as its result rather than
recomputed, since compile-time calculation is meant as a performance
construct (the owner's words, paraphrased). Everything below is that
session's reading; the representation choices in particular are
Claude's and may be wrong, though `dune test` checks them on every test
that runs, in each of its modes.

61. **Values are embedded, functions are extracted.** The elaborator
    records each run-position `def-fns` group as it runs it, and each
    final expression's computed value with its type (`Env.trace`).
    `--extract out.ml` writes every `def-fns` group as a `let rec ...
    and ...` at its position, a nested `def-fns` as a local `let rec`,
    and a match as an OCaml `match`. Every other constant the code
    mentions, a run-position `let`'s binder, a `comptime-match` field, a
    hoisted literal, a built-in of `lib/prelude.ml`, is the value the
    interpreter computed at elaboration, embedded as data on first use
    as a top-level `let` of that entry's name. So `u8-modulus` is the
    integer 256 (or, without the FFI, 256 nested `Succ`s), not a call
    of `pow2`. A closure among those values, one a factory returned at
    the top level (`tests/main_factory.sl`), is hoisted as a `let rec
    cl<n>_<name>` over its captured environment: its free variables
    are the values captured at closure time, embedded the same way. The
    closures of one nested `def-fns` group share one environment, which
    holds them (`Eval.close`), and that is the only cycle among values:
    a closure captures only what existed when its group closed, and a
    constant built later may hold a closure but is never captured by
    it (the owner's observation, checked against `Eval.close` and
    `elab_def_fns`). So the closures sharing an environment are written
    as one `let rec ... and ...`, and every other constant is a named
    `let` in dependency order, which is mint order
    (`tests/main_factory.sl`, `tests/io_closure_in_data.sl`). Sharing
    within embedded data is kept: a block met a second time (by
    physical identity, found through a structural hash) becomes a
    named constant from then on, so a value's text is linear in the
    size of its graph, not of its unfolding (`tests/thunk_shared.sl`).
    A top-level entry has one value and is named once by its id; a
    factory's parameter or local has one value per activation, so its
    captured values are named per value (`tests/io_factory_twice.sl`).
    A top-level `def-fns` function met as a value refers to
    its `let rec` name. The final expression's value is embedded too,
    being computed at elaboration like any run-position expression; so
    a printed final value is printed from data, a `String -> String`
    program is its `main` closure applied to stdin, and a `Program` is
    its first step, whose continuation is a closure.
62. **Every extracted value is an `Obj.t`**, with `Obj.repr`/`Obj.obj`
    at every construction, application and pattern, the way Coq's
    extraction reaches for `Obj.magic`. A typed extraction is not
    attempted: dependent indices, existential erased fields, first-class
    `Matchable`s and level polymorphism have no direct OCaml types, and
    section 33's zero-cost `coerce` between distinct types would need
    the same escape anyway. The runtime shape is section 33's, so
    `coerce` is the identity and a newtype is its field. An entry is
    named `v<id>_<name>` (`v<id>_g<n>_<name>` for a gensym), the id
    being the entry's, so shadowed names stay distinct; a literal is
    `l<n>`, a closure `cl<n>_<name>`, and a constructor shape's OCaml
    type and constructors `t<n>` and `K<n>_<i>`. The source names come
    from a table `Env.bind` fills (`Env.names`). OCaml 5 gives at most
    244 constructors with fields a block tag of their own (OCaml 4,
    246), so a shape with more of them, a **wide** shape, keeps its
    nullary constructors as `K<n>_<i>` and puts every other under one
    constructor `K<n>_w`,
    whose record holds the constructor's position as an `int` field
    `d` ahead of its fields, padded with `()` to the widest
    constructor's. That `d` stands in for the tag section 33 asks for,
    held in a field rather than in the block's header.
63. **A constructor application is marked** with the call kind
    `Value.Ctor` in the post-erasure code, so that the extractor can
    tell it from a call (the interpreter ignores the mark, dispatching
    on the value). A statically known match extracts against a
    phantom-index copy of its variant: the constructors that can reach
    it (its real branches and those its `else` stands for, recorded as
    the code's `live` set) are indexed `yes` and the rest `no`, and the
    scrutinee is coerced to the `yes` instance, so OCaml's
    exhaustiveness checker accepts the match without the refuted arms
    and emits no default; an `else` stays as `_` under that type. The
    interpreter still raises on a reached absurd, extraction being the
    path that trusts the checker (the owner's reading: interpretation
    is the checked path, extraction is opted into for speed). The copy
    keeps every constructor at its arity, which is what keeps its
    representation the base type's. A wide shape (62) has no copy,
    since its constructors with fields share one OCaml constructor that
    an index cannot split: its match is against the base type and ends
    in `| _ -> absurd ()` where it has no `else`, and so does reading or
    writing a cell's fields.
64. **The FFI is shared by embedding.** `lib/ffi_core.ml` holds the
    implementations over raw zarith integers and slices, generic in the
    value type through injection/projection arguments; `ffi.ml`
    instantiates them with `Value` constructors and a dune rule embeds
    the file's text into the interpreter (`Ffi_core_source`), which the
    extractor pastes into every output as `module Ffi_core`, instantiated
    with `Obj.repr`/`Obj.obj`. An extern function extracts to a wrapper
    around `Ffi_core.<name with - as _>` of the same arity; under
    `--no-extern` the extern types are ordinary variants and the extern
    functions' compiled models are extracted instead, so section 42's
    invariant is checked on the extracted programs too. `Value.payload`'s
    `Slice` carries `Ffi_core.slice`. An embedded extern integer is
    `Z.of_string` of its decimal spelling; an embedded string is a
    literal. Without the FFI a large embedded numeral is that many
    nested constructor applications, which the OCaml compiler may refuse
    at some depth, a limit in the spirit of item 54.
65. **The driver is shared by embedding.** `lib/driver_core.ml` holds
    it; `program.ml` includes it, and the extractor pastes it into every
    output as `module Driver_core`, as item 64 does for the FFI. An
    `absurd` reached at runtime prints `<file>: runtime error: absurd
    code reached` to stderr and exits 1, the file being the one whose
    final expression is running, as `bin/main.ml` prints it (`-` for
    stdin; the test runner passes no file). Every final expression of
    every file on the command line is consumed in order, as the
    interpreter would; `--extract` stops the interpreter from running
    the final values itself (elaboration still evaluates them, the
    language being pure).
66. **A printed final value goes through a generated printer**, since
    an extracted value does not know its constructor names: for the
    final expression's type, each constructor's return type is unified
    with it (as entering a match branch does) to find the `many` fields'
    types, and one printer per type is emitted, following `Value.show`
    and section 45's printing, a value of one of the three literal
    types printing as the literal it reads back from (item 154).
    Printing the interpreter's own rendering as a string literal would
    be simpler and exact, but the printer applied to the embedded data
    is what checks the embedding.
67. **Testing.** For every test that runs (those expecting an error
    need no extraction) and each of its modes, `test/runtest.ml`
    extracts the elaborated program, drops the final expressions of the
    `needs:` files from the trace (the interpreter runner discards their
    output too), compiles with `ocamlfind ocamlc -package zarith,unix
    -linkpkg` into `_build/default/test/extract/`, runs the binary with
    the test's stdin and arguments, and requires the directives' stdout,
    stderr and exit code. A missing `ocamlfind` fails those tests rather
    than skipping them. What that shows, precisely: since final
    values are embedded, a test printing a plain value checks the
    embedding of data and closures and the printer, while the `String
    -> String`, `Program` and final-function tests (DESIGN.md section 27; the
    `tests/thunk_*.sl` files cover tagged, untagged, union, extern,
    first-class and nested types, coerce, factory closures and shared
    data) run extracted function bodies over embedded constants.

## A second soundness review

69. **Two `def-lvl` levels may unify.** With a type indexed by a level,
    `(Foo : ((Level) L) -> Type)` with one constructor returning
    `(Foo P)`, matching a `(Foo Q)` against it unifies `Q` with `P`, and
    inside the branch a `Q`-level body may call an `R`-level function
    minted after `Q` under the proof `(Predates R P)`. The branch is
    uninhabited, `(Foo Q)` having no values at any multiplicity, and a
    session found no run or proof of `False` that follows. The load
    bearing part, in a session's reading, is elsewhere:
    `prove-predates` demands strict mint order and the three axioms
    keep a proof's subject older than its level, so no `(Predates Z Z)`
    could be built, which is what keeps a diagonal `(MkBar K) : (Bar K
    K)` forcing two level parameters equal from licensing a same-level
    call that could ever run; whether that irreflexivity deserves a
    stated invariant appears to be the question of OPEN.md 5.
    An erased data field may change under `coercible-ctor` (a `(MkBox
    (Zero) n)` to a `(MkBox (Succ (Zero)) n)`), which a session read as
    harmless, the field carrying nothing at runtime and its replacement
    being typed.
## Fixes from a bug-hunting session

A session asked to look for bugs, soundness ones especially, reported
its findings in chat, and the owner picked which to fix.

72. **A `let` that returns exactly what it binds is replaced by its
    right-hand side.** `check_marks` normalizes the code to read the
    marks through renaming `let`s (section 19), drops a `let` whose body
    returns exactly its binders, and returns the normalized code as the
    function's body, so the check and the compiled code agree: a call
    whose results such a `let` binds runs as a tail call, in the
    interpreter and in the extracted OCaml alike. Believed
    semantics-preserving, the two forms producing the same values in the
    same order, and applied to every compiled body rather than only to
    marked ones, which keeps one path instead of two.
    `tests/tail_values.sl` covers the form.

## Fixes from a second bug-hunting session

A session asked to look for bugs, soundness ones especially, probed the
checker and the compiled-code path. As elsewhere in this file, each
item is the implementation's reading offered as a candidate question,
not a settled decision, unless it says otherwise; item 75 in particular
changes which programs are accepted and wants the owner's word. Where a
claim could be checked by compiling (CLAUDE.md rule 2) it was.

74. **A renaming `let` that is resolved away is substituted into nested
    function bodies too.** Item 72's normalizer, replacing a `let` that
    only renames by its right-hand side, rewrites the bodies of a nested
    `def-fns` as well as the body's own shape. `Value.map_code`, which
    the normalizer otherwise walks with, deliberately does not descend
    into them, which is what keeps the `tail`/`delegate` marks judged
    per function, so the nested bodies are rewritten separately; a
    nested function closing over such a binder would otherwise
    reference an id that nothing binds. Reached by a nested `def-fns`
    whose body mentions a binder of an enclosing `(let ((many k)) n)`,
    or of a `let` whose right-hand side is a `values` of plain
    variables. Believed semantics-preserving, the binder and its
    right-hand side denoting the same value. `tests/nested_capture.sl`.

75. **A call's same-level test reads both levels canonically.** Section
    19 splits a call by whether the callee's level is the current one,
    and section 9's identity is canonicalize-then-compare. The test
    canonicalizes the callee's level and the current level alike, as
    the `Predates` check does. Read literally instead, a fact equating
    the enclosing function's own level with an older one -- which a
    match branch can force where a constructor's return names that
    older level, ASSUMPTIONS 69's situation -- would make the
    function's *same-level self-call* read as a lower-level call,
    dischargeable by the ordinary `Predates` proof between the two
    levels and needing no `Subterm` decrease at all. That is
    unrestricted same-level recursion, which is exactly
    `tests/lt_subterm.sl`'s `loop`: the checker would accept an
    `erased` function whose one branch is that self-call and whose
    declared return is `(erased (False) f)`, so a caller able to reach
    it would bind a `False` token and section 10 would be gone. The
    session did not find a way to run one, agreeing with item 69: the
    branch forcing the equation is headed by a constructor whose return
    puts one variable in two index positions, so its values are
    diagonal, and `coercible-ctor` retargets an index only through an
    erased field, which is exactly the case where no equation is
    forced. So what the literal reading reaches appears to be an
    accepted call rather than a live loop. Read canonically, the call
    is same-level and demands the `(subterm p)` it cannot supply
    (`tests/level_alias_bad.sl`, `tests/level_alias_predates_bad.sl`).
    Open for the owner: this is a reading that alters which programs
    are accepted, and the alternative is reading the current level
    literally, so that the branch keeps its recursion.

77. **An erased `def-fns` leaves nothing in the post-erasure code.** A
    `def-fns` under a function body or match branch compiles to a
    `CLetRec` carrying only the block's `many` functions, and to
    nothing when none remain: item 32's rule applied to the block as
    well as to its functions. Section 14 has an erased function only
    ever held or called at multiplicity `erased`, so nothing at runtime
    can reach such a closure. Leaving it out also keeps an erased proof
    helper defined inside a delegating function from standing in the
    way of section 19's `delegate`, whose check reads the post-erasure
    code and wants the body to reduce to the marked call alone.
    Believed conservative, the dropped closures having no reachable
    use. The owner asked for the same reading to be applied to a
    nested `def-adts`'s *phantom* constructors, erased entries by
    section 21 and equally unreachable, so the `CLet` that statement
    emits carries only the non-phantom ones.
    `tests/delegate_erased_inner.sl` covers both statements inside a
    delegating body.

## A match reads its Matchable, not its constructors

The owner's decisions on what a match reads are in DESIGN.md §§8, 24
and 33; item 83 records how the prototype compiles a match.

83. **What a match compiles to.** The post-erasure form of a match is
    its scrutinee, one branch per real constructor keyed by that
    constructor's discriminant, and a *shape* saying how the scrutinee
    comes apart: through the FFI's destructor where it holds the type
    (§42), off the tag where the type carries one, or as the value's
    own fields where it carries neither -- the case the elaborator has
    already checked leaves a single real branch (§21). Where the opened
    `Matchable` is `Settled`, the shape is fixed at elaboration (`Known`
    in `lib/value.ml`) and no constructor or `Matchable` value is read
    at runtime, so a branch may name a constructor that is `erased`
    where it stands (`tests/erased_ctor_dispatch.sl`). Otherwise the
    shape is `Held`: the tag and the constructor order come from the
    `Matchable`'s type, and the `Matchable` held in a variable is read
    when the code runs, for its FFI destructor. The code appears to read
    a held `Matchable` whether or not its type carries the `extern`
    mark.

## A cleanup session's reading of the delegate check

From a session asked to look for bugs and to tidy the code.

88. **The tail and delegate checks drop a `let` of embedded values that
    nothing reads.** The constructors and `Matchable` a nested
    `def-adts` binds would stand between a delegating body and its
    call, so the tail-check's normalizer, which folds a renaming `let`
    away (item 72), also drops a `let` whose right-hand side is values
    embedded by elaboration -- literals in the post-erasure code, the
    entries they bind staying `Hypothetical` as §29 has every binding in
    a body -- when the rest of the body mentions none of its binders.
    That keeps item 77's guarantee for a phantom-only `def-adts`
    (`tests/delegate_erased_inner.sl`) and reads more widely than item
    77 does: a nested `def-adts` whose constructors the body never uses
    does not block a `delegate` either (`tests/delegate_inner_adts.sl`).
    Settled by the owner: this is the behaviour wanted, dropping a
    binding nothing reads changing no program's meaning.

## A compiler written in the language (self/)

Written by a session working autonomously at the owner's request, in
chat: name the language SL for now, self-host it, write in SL a program
compiling SL to OCaml that can interpret the compile-time `Settled` part,
and use the existing OCaml interpreter and extractor to get there.
`self/README.md` describes the result; the items below record what it
assumed. As elsewhere here, each is the session's reading, checked by
`self/bootstrap.sh` rather than by the owner, unless it says otherwise.

91. **The compiler checks its input.** At the owner's request ("make it
    not trusting") the compiler ports every check of `lib/elab.ml` and
    `lib/env.ml`: the three contradictions of forced unification
    (section 7), identity of types and values, erasure by position, the
    call-site proofs against the current level and enclosing subterm
    parameters, branch refutation and the one-real-branch rule,
    `comptime-match` verification, the tail and delegate marks, newtype
    shape, extern claims, and the reader's and literals' errors, with
    the reference's message texts. `self/bootstrap.sh` requires every
    error test to be refused with its text. A reading of the session,
    not the owner's: an error does not stop elaboration, so a program
    may be refused with more than one message where the reference gives
    its first. Where a message is placed is item 194's. It is not a
    second arbiter for section 10's consistency question, since it runs
    on the same reading of the design and trusts its own interpreter as
    `lib/` trusts its (DESIGN.md section 29).

92. **What the fixpoint shows, precisely.** `self/bootstrap.sh`
    extracts the compiler natively with the reference extractor, checks
    that every runnable test compiles to a program whose stdout, stderr
    and exit code match the interpreter's and every error test is
    refused with the expected text, compiles the compiler with
    that binary, and compiles the compiler again with the result,
    requiring the two OCaml outputs to be identical. Identical outputs
    mean the compiler compiled by the reference extractor and the
    compiler compiled by itself agree on the compiler's own source; they
    do not mean either agrees with the reference on every program, which
    only the test comparison speaks to, one test at a time. These checks
    are not part of `dune test`: running the compiler under the
    reference *interpreter* takes seconds per file and the stripped mode
    of item 44 would run its fuel counters in unary.

93. **Canonicalization terminates by construction, on an append-only
    list of rules.** At the owner's direction, the compiler's
    canonicalization terminates by a structural argument rather than by
    fuel. The environment holds its rewrite rules in the order they
    were appended, and every appended rule's right-hand side is
    canonical at that moment. The session's reading is that a canonical
    term mentions only variables that are rule-free then, so any rule
    they later carry was appended later, and a chase from a rule only
    ever needs the rules after it. `canon` takes that suffix as its
    first `subterm` parameter and the term as its second, so the
    checker accepts the chase as a lexicographic decrease; item 94
    proves that the rule is in the suffix, and item 191 erases the
    list.

94. **The fact table, canonicalization and unification carry erased
    proofs.** Again at the owner's direction, the owner having set
    aside a stamped version with a runtime comparison, a fully verified
    map, and an eager-substitution design, the invariant of item 93 is
    a proof rather than a reading. The fact table is a trie `Facts n`
    whose index counts its rule-free entries, with sums as the
    prelude's `Add` and the relation `Plus3` since a type may not call
    a function; `In` is the path to a rule-free entry and `RuledIn` to
    a ruled one. The environment's table carries, erased, the order
    invariant `Ord` (each rule's term avoids every key at or before it,
    witnessed by a table in which the term is fresh and the keys are
    ruled, so the witness never goes stale and no inequality on ids is
    decided) and both directions of agreement between table and list
    (`C1`: every ruled entry's rule is in the list at the key its path
    spells; `AllRuled`: every key is ruled). `canon` returns `Fr`, that
    its result mentions only rule-free entries, and its lookup in the
    suffix takes a membership proof derived from those invariants, so it
    cannot come back empty. Unification's measure is the count: a
    binding rules the entry out by its `In` proof, which refines the
    count to a successor, and `prove-subterm` on the predecessor is the
    call annotation; the occurs check is the term still being fresh
    once the variable is ruled out. The proofs cost elaboration time
    only, most of them being erased.

95. **The emitter recurses on the closure it emits.** Every function of
    the emitting block takes the closure being emitted as its first
    `subterm` parameter and the piece of code as its second, with an
    erased `Subterm` proof that the piece lies inside the closure. A
    constant met in the code is then a subterm of the closure through
    that proof, a captured variable's value is a subterm of the
    closure's environment (the map lookup returns the proof with the
    value), and a closure met inside a value is a subterm of the value,
    so each descent is a lexicographic decrease the elaborator checks.
    A run-position group is emitted under a closure built around it,
    which captures nothing. The compiler's own elaborator names its
    functions `mint-subterm` and `mint-predates`, so that they do not
    shadow the special forms `prove-subterm` and `prove-predates` in
    the files after it.

96. **The elaborator recurses on the raw it elaborates.** Every
    function of the elaborating block takes as a `subterm` parameter
    the raw, or list of raws, it elaborates. The structures a function
    parses from that raw before elaborating it are indexed by the raw
    and carry erased `Subterm` proofs for the raws they hold: telescope
    entries (`SrcEntry root`, with `Sub root` for the raws before and
    after an arrow and `Within b a` for a suffix, which may be the list
    itself), function and type headers (`Headers fns`, one per raw of
    the list), branch parts, a let's binders, a constructor's signature
    and a call's decrease annotation. A descent into one of those raws
    is then a checked decrease in the raw, and a loop over such a
    structure a decrease at a later position with the raw held fixed.
    Where a function hands its whole raw to another (a type former to
    the TyCtor or ValCtor reader, a telescope reader to the loop over
    its parsed entries) a `Steps` value decreases instead: its type
    states how many hops it must pay for, `(Steps (Succ (Succ (Zero))))`
    for a type former, so the zero case is refuted by the constructor's
    index rather than reported, and each descent supplies a fresh budget
    of a size the code's shape fixes. The session's reading is that this
    is not a fuel: no path reports exhaustion, and the checker rejects a
    budget too small for the hops below it. The numeral spelling counts
    up in `Bin` from zero and the decimal printer counts up a digit
    list, both linear in the number (a numeral in the millions costs
    that many steps, which the session judged acceptable for the
    sources and tests at hand), and the reader closes `$` frames by
    recursion on the frames below the one closed. A function or type
    header, or a constructor, with no signature after its name is
    reported and then skipped rather than elaborated as an empty
    signature.

97. **A fresh id is provably absent from the fact table.** The table is
    indexed by a bound as well as by its facts, `Table n f c`, and
    carries an erased `Above` proof that every key it holds is at most
    `c` (at each node, the key its path spells is, when the node holds
    an entry); the environment keeps its id counter as that bound, so
    the table's type is `Table nfree ffacts fresh`. Ids are ordered by
    the prelude's `Lt`. Binding takes the successor of the counter with
    an `Lt` proof, and `table-insert` refutes the position being taken:
    a taken position yields a `Taken` proof (the insertion returns one
    rather than a bare `IKept`), `Above` bounds its key by the counter,
    and the strict order refutes that. The bound moves only up: ruling
    out preserves the keys (`above-out`), inserting the fresh id keeps
    them at most the new counter (`above-ins`), the id supply's other
    client weakens the table to the new counter (`env-fresh-id`), and
    leaving a body keeps the outer table with the inner counter by
    comparing the two and weakening towards the larger, which is the
    inner one in every run but is decided rather than assumed.
    Unification threads the bound through its outcomes (`Outcome n c`)
    so that setting the table back into the environment sets the
    counter it was read with. The session's reading is that this
    proves a fresh id never lands on an occupied position of the
    table; the reference's own termination remains the one thing no
    proof here touches. The ids bound for a `def-fns` or `def-adts` are indexed by
    the headers they came from (`Bound fns hs`, `Tids adts hs`),
    headers hold their parameter and return telescopes rather than a
    type to take apart, string literals are interned by their own
    function so no name classifies as a string, the wrapping
    constructor's field is found by the search that checks it is the
    only one, and a run-position group's closures are the pairs closing
    produced. Left unproved, all reachable only after an error was
    already recorded or by the interpreter's own failure: `bind-let` and
    `first-res` on a result list whose length a reported count error
    already disagreed with, `spread` on values the interpreter failed
    to produce, and the interpreter's dynamic checks, which belong with
    its fuel. Informal by the session's reading: the `comptime-match`
    contradiction after a value was verified, and the places that read
    an id out of a term expected to be a variable and default to id
    zero otherwise. Of those last, the prelude-name lookups (`Nat`,
    `Numeral`, `Bin`'s digits, `Lt`, `MkChar`, `Char`, `String`) report
    an unbound name rather than default, since they are reachable by
    running slc without the prelude; the reader of a Matchable's
    constructor slot defaults, because the reference (`lib/env.ml`'s
    `unify`) treats those slots as ordinary variables, ruling one out
    against another when two Matchables disagree, so holding ids there
    instead of terms would change what unification does; the session's
    reading is that a slot holding anything but a variable is an
    invariant of well-formed terms of the same kind as `infer`'s.

98. **A proof's arguments are read by arity, not by position.** Reading a
    proof of `Predates`, `Subterm` or `Coercible` (`expect-proof3`,
    `expect-proof4`) takes the relation's argument count apart and
    reports "expected a ... proof" on any other shape; `nth-term` is
    used only for a call's arguments, reached after an arity error was
    already reported. The session also weighed intrinsically typed
    terms for the remaining well-formedness invariants and set them
    aside: the reference (`lib/env.ml`) adds a rule with no type check
    and makes the types agree by a second unification, as `refine`
    does, so between the two the rewritten terms are ill-typed from an
    intrinsic view, and slc must keep that order to accept and refuse
    the same programs. The reference accepts the inductive-inductive
    shape such terms would need (a type of types whose constructors
    embed terms indexed by those types) and refuses a type indexed by
    itself, both checked by compiling; the obstacle is the metatheory,
    not the declaration.
## `let-match`, and reasoning about literals through their spelling

DESIGN.md section 27 describes `let-match`. What follows is how the
session built it and what it assumed while doing so.

100. **Its code depends on the scrutinee's erasure and on run position.**
    An erased scrutinee emits nothing, matching `elab_match`'s rule
    that one real branch under an erased scrutinee compiles to that
    branch's body. In run position with a non-erased scrutinee it runs
    the scrutinee and binds the fields `Settled`, as `comptime-match`
    does, emitting nothing. Only outside run position does it emit a
    one-branch `CMatch` wrapping the rest of the enclosing expression.
    So a `let-match` at top level does not cost the code after it its
    run position.
107. **The prelude's character operations** (`lib/prelude.sl`).
    `char-cmp`'s arguments coerce down through `Char`'s and `U8`'s
    newtype wrappers to their codes, the call to `u62-cmp` is a
    `delegate` (§33), its bounds from `u8-below-u62`, and the
    `Coercible` carrying the result back up is built by an erased match
    over the three constructors — erased, so §21 puts no one-real-branch
    limit on it and it leaves no code, which is what lets the delegate
    mark stand. `tests/char_ops.sl` coerces `char-cmp` to `u62-cmp`'s
    own type and runs it on `Nat`s. `CEq` repeats its index rather than
    carrying an `Eq`, at the owner's direction, so matching it forces
    the two sides together the way `Refl` does; the branch still wants
    `pa` and `pb` identified before two `Char`s coincide, which is why
    `lt-unique` is in the prelude.

    The prelude has no `char-to-nat` or `nat-to-char`, at the owner's
    direction: converting is trivial through `U8`, which is itself
    trivial given an `Lt`, so the prelude need not choose what a `Nat`
    out of range becomes (`tests/char_convert.sl` writes both
    directions out).

## The compiler in `self/`: `let-match`

How `self/` implements the forms above; `self/bootstrap.sh` is the
check, and none of it is design.

111. **A generated form is elaborated on a budget.** The compiler's
    elaborator recurses on the raw it elaborates (96), and the `match`
    a `let-match` with branches is rewritten to (197) is a raw of its
    own making, which is no decrease; so every function of the
    elaborator's group takes a `Nat` budget of expansions as a
    `subterm` parameter, passed unchanged on every call but the one
    that elaborates a generated form, which decreases it, and the
    checker accepts that as the lexicographic decrease it accepts for
    `canon` (93). The top level starts the budget at the form's size
    (197); the zero case is reported as an internal error. `let-match`
    is ported as the reference has it, with `SMatch` as the statement
    code of a one-branch match wrapping the rest.
112. **A `U8` is its `Nat` inside the compiler too.** With `U8` a newtype
    (DESIGN.md section 42) the compiler's value model has no `U8`
    payload: a character literal's value and the `String` FFI's
    per-character value are `Nat`s, as `lib/ffi.ml` builds them.
    `char-of-code`, which the compiler uses to turn a code from the FFI
    into a `Char`, matches `lt-dec` against the modulus and maps a code
    the modulus does not bound to the character with code 0; the
    reference's `Char.chr` would raise there instead, and no program
    reaching either is typed. The compiler's own exit codes are built as
    the tests' are, by reflection at top level.

113. **A call with no decrease annotation gets one inferred** (DESIGN.md
    section 48; `Elab.elab_call`, `elab-call` in `self/elab.sl`). That
    the first differing position is the only one an annotation could
    succeed at, and so that bare calls accept exactly what a written `_`
    annotation accepts, is the session's reading, not the owner's;
    `tests/bare_call.sl`, `tests/no_predates.sl`, `tests/no_subterm.sl`
    and `tests/level_alias_bad.sl` are the evidence.

## A form's results are out of scope for its own body

Item 114 records a choice the session made, in the reference and in
`self/`, while fixing a program the owner sent. The reasoning is the
session's and may be wrong (CLAUDE.md rule 1); the tests it names are
what was checked by running (rule 2).

114. **A form's result entries are opened after the form**
    (`Elab.open_results`; `open-results` in `self/elab.sl`). A
    `match`'s or `cell-match`'s annotation is a telescope, as are a
    call's returns, and the entries opened for it stand for what the
    form produces. Their names are dropped, so nothing reaches them by
    name; but `delegate-of` and `at-fn-of` (§19, §39) find a proof by
    scanning `env.scope` for an anonymous entry of its type. Were the
    entries bound before the form's branches, body or arguments, these
    could fetch the entry the annotation had just minted, and
    `check_results` would compare that entry with itself. A `match`
    annotated with a `Delegate` from `id` to `yes`, a function of
    another type, whose `else` is `(delegate-of id)`, would then supply
    that proof, and coercing `id` through it appears to put a `Nat`
    where a `Bool` is expected (`tests/match_result_delegate_bad.sl`;
    also `match_result_atfn_bad`, `cell_match_result_atfn_bad` and
    `call_result_atfn_bad`). The results are opened after everything
    the form elaborates: for a match, the branches, the coverage check
    and the `else`. DESIGN.md does not appear to say either way. That a
    form's body may not read what the form produces looks to the
    session like plugging a circularity rather than a design choice,
    but it is recorded here in case the owner reads §21's annotation as
    binding for the branches; the entries are anonymous, so the
    question is only about the type-directed lookups. The `Matchable`
    and `Newtype` lookups (§8, §33) read only opened `Matchable`s, so
    as far as the session can tell an unopened result entry does not
    reach them (`tests/match_result_matchable_bad.sl`,
    `match_result_newtype_bad.sl`).

## `_` for an erased argument

How the elaborators implement DESIGN.md section 50. The implementation
choices below are the implementing sessions', not the owner's;
`tests/wild_*.sl` are the evidence.

115. **A `_` argument is a meta, solved by unification in its solving
    mode** (`Elab.check_args`, `Env.bind ~meta`, `Env.unify_in`;
    `check-args`, `bind-as` and `unify` in `self/`). A meta is a scope
    entry with the `meta` flag that `bind` leaves out of `env.scope`
    (and, in `self/`, out of the objects list), so nothing reaches it by
    name and none of the type-directed lookups of item 114 can fetch it.
    `unify_in` without `~force` binds only metas — a meta against a meta
    binds the newer, a meta against a term binds the meta after the
    occurs and dangling-binder checks of §7 — and requires the two sides
    identical otherwise; `refine` and the extractor force
    (`Env.unify_force`). `check_args` mints one meta per parameter, at
    the parameter's type over the metas before it (an `is`-entry's meta
    is solved by its rule at once); an argument written `_` is left to
    its meta; any other argument is elaborated with the parameter's
    instantiated signature as its expectation, checked against it, and
    bound to its meta. Where some argument is `_`, the application's
    result over the metas — `(C metas)` for a constructor, the return
    telescope instantiated for a call — is unified with the expected
    telescope before any argument is read, as a transaction (a failure
    leaves the environment as it was); at the closing paren, if a `_` is
    still open, the same unification is run again reporting the
    mismatch. The solutions replace the metas in the argument terms
    (`Env.metaless`). A `let` whose binders all carry a type or an `is`
    clause elaborates them as a telescope, `Elab.elab_tele` over the
    binder forms and `elab-src-entries` over the parsed binders in
    `self/`, and hands it to the right-hand side as its expectation
    (`tests/wild_let.sl`).

116. **`self/*.sl` writes `_` wherever slc accepts it, and `$` for a
    last argument on one line.** An erased argument of a known
    constructor or function is written `_` where slc accepts it, and a
    `let`-bound `match`'s annotation is moved onto typed binders and
    written `_` where that is possible. What stays written is, by the
    session's check of each remaining site, almost entirely erased
    *proof* arguments -- evidence such as an `Ord`, a `Fr` or a
    `Subterm` that nothing else mentions, which no unification in any
    order could supply -- and a few data-typed indices of two shapes: a
    `(Succ (Zero))` under an untyped erased `let` that only the bound
    proof's later use fixes, and a pair of occurrences of one index in a
    call that determine each other and nothing else mentions, so one of
    the two must be written. Each subform that is the last item of its
    parent and sits on one line, `(f a (g b c))`, is written
    `(f a $ g b c)` (DESIGN.md §2), where the parent is headed by a name
    rather than a multiplicity, a type former, `match`, `def-fns` or
    `def-adts`, and the subform by a name. Multi-line last items (a
    body's final `match`, a `let`'s right-hand side over several lines)
    are left as they are, a `$` at the start of a continuation line
    being a style the owner has not written.

117. **Pure terms stay open; boundaries settle** (`Elab.check_args
    ~boundary`, `Elab.settle`, `Env.bind`; `check-args`, `settle`,
    `bind-as` in `self/`). A constructor or type constructor
    application runs `check_args` without its closing checks, the term
    and type it returns may hold open metas, and `elab_expr`
    substitutes the solved ones into every result it returns
    (`Env.metaless`). `Env.bind` enforces DESIGN.md section 50's
    invariant as a backstop: a type or rule with an open meta is refused
    with "cannot infer `__?1` in ...", so any form that let one leak is
    caught where it leaks; the one exception, `~holes`, is a telescope
    under construction. A match annotation is elaborated with holes
    allowed, unified with the expected telescope (`solve_tele ~strict`)
    when there is one of the same length, and settled before the
    branches. A typed `let`'s binders are likewise elaborated with holes
    and each value is checked against its binder's entry of that
    telescope rather than a second elaboration of the clause
    (`bind_one`; `bind-let`). In `self/` the two telescopes keep their
    metas' facts through `env-restore` rather than `env-discard`.
    Whether a meta solved inside a match branch may escape it was raised
    and left out at the owner's request.

## A proof-carrying prelude

The owner decided that the FFI adder returns an `Add` proof with a
plain adder as a `delegate` over it, that `double` is derived from it,
that `trim` is transparent, that `str-append` gets a relation, and that
levels should be used judiciously with `_`. The names and the shapes
below are the session's.

118. **Primitives return their relations; the old names are forgetful
     wrappers.** `nat-mod` is extern over a structural model, with
     `nat_mod` (`Z.rem`) its implementation. `double` is `(add a a)`
     with the erased lemma `add-diag-double`, so the modulus is eight
     FFI additions rather than unary doubling; `Double` stays as the
     relation the `Numeral` lemmas invert. `add-zero-right`,
     `add-succ-right` (Coq's `plus_n_O`, `plus_n_Sm`) and the inversion
     `add-succ-right-inv` are the lemmas the `Mod` step and
     `add-diag-double` need. `Mod s c r` is `ModLt` (already below `c`)
     or `ModSub` (one more `c` subtracted), with `mod-succ-lt` and
     `mod-succ-wrap` the two cases of the successor step decided by
     `nat-cmp`, whose `CEq` forces `c is (Succ r)`; `lt-asym` refutes
     the third. `tests/prelude_proofs.sl` is the evidence.
119. **Levels in the prelude are anonymous** (`_`, DESIGN.md sections 42
     and 46) and its calls bare (DESIGN.md section 48). Two things the
     session learned writing the lemmas, recorded as its reading: a
     lemma cannot recurse on a proof another lemma's call produced,
     since that is not a subterm of anything, so `add-diag-double`
     recurses on the `Nat` instead; and two lemmas at one level can only
     call each other under section 19's positional subterm discipline,
     so each lemma is its own `def-fns _` and calls the ones above it
     with an inferred `Predates`.
120. **`lt-dec`'s model is derived from `nat-cmp`, and `Dec` is plain
     source.** `Cmp` is plain source too, and the FFI builds it through
     its constructor (123). `nat-cmp` sits at an anonymous level below
     `nat-lvl` so that `lt-dec`, at `nat-lvl`, can call it; the lemmas
     are `lt-succ` (`Lt a (Succ a)`) for the `CEq` case and `lt-weaken`
     (`Lt x y -> Lt x (Succ y)`) for `CGt`.
123. **An extern over a plain ADT takes that type's constructor or
     destructor; nothing is extern for the FFI's convenience.**
     `Ffi.note` records every declared type by name (first declaration
     winning, so the prelude's), and an implementation returning a plain
     ADT builds it through that type's constructors (`Ffi.tag`, as for
     `nat-cmp`'s `Cmp`), so `Cmp` is an ordinary tagged type, and its
     `Matchable` and `coerce`s between its instances go the ordinary
     way. This is the mirror of `flatten`'s `~rope` (item 122).

## The compiler's libraries carry evidence

The owner chose three of the session's proposals for `self/`'s library
layer — deciders return evidence, lookups return evidence, lists carry
specs — and left moving the libraries into the prelude aside. Shapes
and names below are the session's.

121. **Deciders decide into the prelude's `Cmp`; lookups return
     `Hit`/`Miss` with proofs.** `nat-cmp`, `char-cmp` and `str-cmp`
     are the prelude's. A direct equality test in `self/` matches
     `(X-cmp a b)` on `CEq`, so the equal branch runs with `b is a`
     forced; `nat-eq`, `str-eq`, `char-eq` and `nat-lt` are `Bool`
     wrappers for the `and`/`or` chains. `idmap-get` returns
     `(Lookup V k m)`: `Hit` carries the value and a `MapsTo` proof,
     `Miss` an `Absent` proof; `mapsto-subterm` derives the subterm
     proof the emitter's recursion needs. `nm-get` likewise returns
     `NLookup` over `NMapsTo`/`NAbsent`, through `nm-kid`'s `KidLookup`
     over `KidIs`/`NoKid`, the latter carrying `CharLt` evidence for
     each kid passed over. `list-nth` returns `NthLookup` (`Nth` or
     `OutOfRange`), `length` returns a `Length` proof with
     `list-length` its `delegate` wrapper, and `list-append` returns a
     `Concat` proof. `self/` uses the prelude's `Eq`, `Cmp` and `Add`,
     with its `add-zero-right` and `add-succ-right`. Not done: a `Vec`
     where a length is statically known — the one candidate,
     `check-args-go`'s arity mismatch branches, left in place though
     `check-args` compares the counts before reaching them;
     `list-mem-*` and `index-of-bin` return `Bool` and `Maybe`; and the
     fact table's `In`/`RuledIn`/`Taken` family, which resembles
     `MapsTo`, is left alone. `self/bootstrap.sh` is the evidence.

## `Rope`, and strings built in one pass

The owner asked for `Rope` without length caching for now (DESIGN.md
section 42 describes it); an `SCons` copies its tail, so building a
string by `append` is quadratic even under the FFI. Shapes are the
session's.

122. **`flatten` is an extern over a structural model**, returning the
     string with `(Flat r s)`, a relation whose `RCat` case carries the
     two halves' `Flat`s and the prelude's `Append`; `append` is a blit
     over its model. The FFI flattens into one buffer, walking the tree
     with an explicit stack (`Ffi_core.flatten ~rope ~slice ~z ~str`,
     parametric in how a node is viewed so the interpreter, the
     extractor and slc's runtime share it). The interpreter hands it
     `VCtor`s, slc's runtime its `Tag`s, and the extractor
     special-cases the name to pass a view of the `Rope` type
     (`Extract.fn`). slc's `base.sl` uses the prelude's `Rope`,
     `rope-str` delegates to `flatten`, and `main.sl` writes its output
     as one string. `RChar`, a character leaf (the owner's question, the
     session's yes), is what anything built character by character
     uses: slc's tokenizer accumulates a word or a string literal as a
     rope of `RChar`s and flattens it once, and `base.sl`'s `sanitize`
     and `ocaml-escape` build ropes the same way. slc's compile-time
     interpreter flattens a `Rope` value over its heap
     (`flatten-value`, `eval.sl`). `tests/rope.sl` is the evidence, in
     both modes and extracted. Not done: length caching, which would
     want a `Length`-style proof beside the cached field; and a
     `Request` takes `String`s, the driver never seeing a `Rope`.

## Lockstep evidence

124. **Lists the elaborator walks together carry a `Lockstep` proof, and
     generated forms are built as `Syn` values.** At the owner's
     direction, from a review of where the compiler reports internal
     errors that a type could refute. `base.sl` has
     `Lockstep A B xs ys`, that two lists have one length entry by
     entry, with `lockstep-trans` and `list-fit`, which cuts or pads a
     list to another's length and returns the proof. `open-tele` and
     `src-mults` return the proof beside the list they build, and
     `elab-expr` mints one at its tail, where the count of results
     against the expectation is decided: the results are fitted to the
     expectation with a `no-res` placeholder, the count error is
     reported, and the proof is a further return that `elab-body`
     threads through. `first-res` and `erased-term` take the proof and
     refute the empty list, `bind-let` takes proofs for its results and
     values (composed from the binders' by `lockstep-trans`) and refutes
     both empty cases, `erased-in-many` walks under the proof, and
     `check-args-go` takes the proof relating the telescope to its
     metas. Not done: the sugar budget's zero case (111) stays
     reported; the session's reading, not a proof, is that it is
     unreachable (197). Also left: `bind-let`'s `tele`, whose empty case silently
     stops checking rather than reporting. `self/bootstrap.sh` is the
     evidence.

## Code indexed by its erasures

125. **Post-erasure code is indexed by the erasures of the values it
     produces.** At the owner's direction, the next item of the same
     review. `Code` in `core.sl` is `Code ctx ms` (the `ctx` index is
     item 127's), `ms` the list of multiplicities the expression was
     elaborated at: `many-one` for a variable or a constant, and for a
     function body, a let's right-hand side, a match's branches and the
     whole of `elab-expr`'s result the expectation they were checked
     against. The evaluator returns the many values as a plain list with
     the index beside it as an erased `Picked` (item 150). The lists a
     node holds in step with its index, a `values`' codes and a let's
     non-erased ids, carry an erased `Picked` proof that they sit at the
     many positions, so the evaluator binds a let's ids to its values,
     reads the one value of a scrutinee, a callee or a `values` entry,
     and spreads a run-position let's values over its binders without a
     dynamic check. What stays dynamic is fitted at a boundary:
     `vals-fit` cuts or pads values where arity is genuinely dynamic, a
     closure's arity being a runtime property, and a constructor's
     fields and a closure's parameters bind by count. A node that has to
     make values on its own, an erased position, an application, a
     match, `absurd` and an error, holds its list as data for that. A
     call's projection of many results onto an expectation with fewer
     takes a decided `Lockstep` and builds both `Picked` proofs. The
     normalizer's dropping of a `let` whose body returns its ids needs
     care: the right-hand side's index differs from the body's in erased
     entries, as `nat-add`'s `delegate` over `add` shows, so
     `returns-same` decides that the two lists agree on their many
     entries, returning a `ManySame` proof, and `recast` rebuilds the
     code at the body's index, which changes only the lists the nodes
     hold; for that, `CLet` and `MkFunc` carry their erasures as data.
     The emitter reads these lists, and the extracted OCaml builds and
     takes apart tuples by arity. The session's reading is that no
     placeholder is ever reported: each sits behind an error already
     recorded. `self/bootstrap.sh` is the evidence.

## Types travel with their terms

126. **The elaborator never reads a type off a term after the fact.**
     At the owner's direction, in place of a depth-indexed `Term`. An
     extrinsic scopedness proof beside each closed term was considered,
     but a stored type's natural home is the fact table, whose `In`
     family indexes on the type a node holds, so the proof would have
     reached the proof family after all. Instead `self/` has no `infer`,
     the one consumer that needed closedness. `elab-term` returns the
     type it computes beside the term: a variable's from the table, a
     constructor application's by instantiating the constructor's
     return, a type former's `Type`. `check-args` returns the arguments'
     types beside their terms. An `is` entry's `SgIs` carries the type
     computed when the clause was elaborated, instantiated, abstracted
     and freed of metas along with its term but neither canonicalized
     nor unified, since it is read only when the entry is bound, where
     the table canonicalizes on read. The application result entry a `_`
     is solved against takes its type from the head's constructor,
     `ARApp` carrying the return. The proof helpers take the `Res` a
     proof came from. The session's reading is that every type this
     hands over is the one an `infer` would compute, a variable's being
     `type-of` and a constructor application's the same instantiation.
     `FrSIs` and the guard for an `is` entry carry the type as an erased
     index. The "dangling binder" case is not refuted but absent: no
     function reads a type off a term. `dangling` itself stays, deciding
     section 7's third contradiction and whether a `_` may be solved
     against an `is` entry. `self/bootstrap.sh` is the evidence.

## Code indexed by its scope

127. **Post-erasure code is indexed by the frames it binds, and the
     interpreter's environment by the same frames.** At the owner's
     direction, the first rung of a ladder the session proposed after
     reading DESIGN.md with CPDT's dependent de Bruijn representation
     in mind (`member` and `hlist`); the owner set the second rung
     (arity-indexed application) aside as common-case special casing
     (CLAUDE.md 6), and the session withdrew the third (shape-indexed
     values) on the owner's question about branch refinement: a
     binder's shape is decided by canonicalization at its binding site
     and a use site's by canonicalization under the branch's facts, and
     a polymorphic field is read at a type its construction site never
     saw, so a shape index would only move the interpreter's dynamic
     checks into narrowing nodes. Shapes and names below are the
     session's. `Code ctx ms` in `core.sl` takes the context as a list
     of frames, each a list of the non-erased ids a binder introduces;
     `CVar` carries a `Mem` proof, a path to a frame and an `At` place
     in it, both `many` since the interpreter walks them; the
     interpreter's `Frames R ctx` holds one list of values per frame
     with an erased `Lockstep` to the frame's ids, so `frames-get` is
     total. `Func gids ctx` and `Group gids ctx` bind a body over its
     parameters, its group and the scope the group was defined in;
     `Bound` in `elab.sl` carries the group's ids as an index so
     `define-fns` returns the group's `Lockstep` by construction. A
     Settled entry is reached as a `CConst` rather than through a frame,
     so the top level binds no frame, a top-level closure captures
     nothing, and run position is the empty context: `elab-let`,
     `elab-let-match` and `elab-def-fns` run code or mint a top-level
     group only under a match on the context being `Nil`, where
     `run-code` takes `Code (Nil) ms`; the environment's run-position
     flag stays for minting states. For that to hold, every branch
     body sits under a frame, the `else` body under an empty one, and
     a match with no runtime discriminant, an erased scrutinee or an
     untagged type, is a `CMatch` with the `ShNone` shape rather than
     its branch's bare body; the normalizer drops it when its one
     branch binds nothing. `StmtCode ctx ctx2` says what frame a
     statement pushes, and `elab-stmt` returns the context after it.
     The normalizer's substitution is a `Ren from ctx`, a frame of
     atoms (a variable with its place, or a constant) per frame of
     the source, weakened under each binder (`ren-weaken`), so a let
     whose right-hand side is atoms, variables or Settled entries, is
     substituted away rather than resolved through an id map. A value
     elaboration embeds, a `matchable-of` or a nested `def-adts`'s
     binding, is `CValue`, which is no atom, so lib/elab.ml's three
     cases are kept exactly: a let of such values that nothing mentions
     is dropped by `strengthen`, which rebuilds the body one frame
     shorter and fails where a variable sits in that frame, deciding
     "mentions" by construction; any other let stays, as the reference
     keeps a mentioned constant, which the session checked on probes
     the tests do not cover. A `projection` builds the places of its
     bound ids from `at-ins` before referring to them. The group frame
     holds the `many` functions of a `def-fns`; an erased one is checked
     and leaves nothing behind, as item 77 has it, `Bound` skipping it
     so the frame's ids and the group's `Lockstep` are by construction,
     and an empty group binds nothing. What stays dynamic: the
     elaborator decides a variable's place with `mem-dec` when it emits
     it, and a `Hypothetical` entry it cannot place is an internal error
     at elaboration, so the invariant that the scope's non-erased
     entries are the context's is not in the types; a closure's arity
     and a branch's fields are fitted to their frame by count, the
     second rung. `self/bootstrap.sh` is the evidence.

## The FFI's names decided once

128. **An extern mark is decided into an enum where it is read, and
     the compiler dispatches on the enum from then on.** At the owner's
     direction, the second item of the same ladder. `core.sl` declares
     `Extern`, one constructor per implementation the FFI has with its
     arity as the type's index, `ExtType` for the extern types it
     holds, and `SomeExtern` packing an `Extern` with its arity;
     `extern-of` and `ext-type-of` are the only functions that compare
     a name to the FFI's, called once by `elab-headers` and
     `define-adts` at the `extern` mark, where `claim-extern` reports an
     unknown name. `Func`, `Header`, `Adt` and `Ctor` carry the enum in
     place of the name, so the interpreter's `apply-extern` is one match
     on it, `ext-construct` one on the type, and the emitter recovers
     the runtime's `ext_` and `con_`/`des_` names through `ext-name`
     and `ext-type-name`. What stays dynamic, since the second rung was
     set aside: the arguments reach an extern as a list the elaborator
     counted against the model's telescope, and `apply-extern` takes
     its arguments from that list, an absent one being an error value;
     the arity in the type is read back by `ext-arity`, whose return
     `is` the index. The arity check at the mark is made in both
     compilers, at the owner's request (`Ffi.claim_fn` in the
     reference; `tests/extern_arity_bad.sl`). `self/bootstrap.sh` is
     the evidence.

## Code built at the expectation

129. **Every case of the expression elaborator builds its code at the
     expectation.** At the owner's direction, the fourth rung of the
     same ladder. `elab-expr` returns `Code ctx expect` from each
     case. A case producing one value, a variable, a constructor
     application, a `coerce`, a `matchable-of`, hands its
     `Code ctx (Cons pos Nil)` to `single`, which reads the
     expectation's shape and, under a proof `PosOf expect pos` that
     `pos-of` returns beside the position, has the two shapes identical
     rather than compared; an expectation of another count gets a
     placeholder, its count being reported at the expression's end. A
     special form producing one value elaborates its argument at the
     position rather than at the expectation's first entry, which
     differ only where the count error has already been reported. A
     call whose returns lockstep with the expectation is always
     projected onto it: the normalizer turns a projection that
     repackages the call's returns in order back into the call, so only
     run-position code carries the let. The session's reading is that no
     message depends on this; `self/bootstrap.sh` is the evidence.

## The compile-time interpreter's values live in a store

Proposed by the session and agreed by the owner in chat, who chose Nat
addresses over Bin ones, weakening as a coerce, and no list of
addresses kept in the heap. Everything below is the session's reading
of that agreement and of what the code does.

131. **A value is a reference into the compile-time store; a block holds
     section 33's representation.** `self/heap.sl`'s store is
     parametric in its block type, and `core.sl`'s `Block R` in its
     reference type. Widening a reference, or any holder of references
     (a list, a `Maybe`, an `IdMap`, the interpreter's frames, the
     environment's entries and finals), into a later history is a
     `coerce` whose proof an erased function builds by recursion
     (`block-widen`, `frames-widen`), so it extracts to the identity. A
     group frame in the interpreter's environment holds the group
     block's reference, and reading a member allocates its closure
     block, so `apply` re-closes nothing. Code holds no reference:
     `CConst id` names the entry and is resolved through the entries
     when the code runs, and a value elaboration embeds (`CValue`) is a
     closed block allocated when reached. Every run-position statement
     that stores a reference is one function in `eval.sl` or `core.sl`
     that reads the store out, runs or allocates, widens the entries
     and finals, sets the states and puts the store back
     (`env-run-let`, `env-run-final`, `env-close-group`,
     `env-set-fields`, `env-run-fields`, `set-state-closed`); `bind`
     takes no state, `bind-closed`/`bind-token`/`bind-erased` allocate
     afterwards, and an erased Settled is a fresh token block. What
     stays dynamic: a `BFn`'s member index against the group block
     found at its reference (an error block on a miss), and that every
     `CConst` the code names has a Settled entry when it runs and is
     emitted. The generated printer's memo keys a type with a wildcard
     for variables minted during printing (`OpWild`).
132. **`sub`, `mul`, `div` and `divmod` are extern over `Nat`** (the owner asked
     for the low-hanging Nat arithmetic; the shapes below are the
     session's, chosen to mirror `add` and `nat-mod`, and open to
     change). `Mul` is in the shape of `Add` (`MulZero`, `MulSucc`
     through an `Add` of the partial product and `b`). `sub` returns
     the difference with an erased `Add b c a`, so no new relation is
     needed; a truncating subtraction is left to be written over
     `lt-dec` where wanted. `div` returns the quotient with, all
     erased, `m`, `r`, `Mul q c m`, `Add m r s` and `Lt r c`, which is
     the session's reading of what characterises the quotient; the
     model is a wrapper dropping the remainder of `divmod`, itself
     extern over the same model shape as `nat-mod` and `succ-mod`
     (`succ-div` steps the remainder against `c` with `nat-cmp`) and
     returning the quotient and the remainder both `many`, with the
     erased characterisation once. The reference FFI returns the pair
     as two values and the extracted body is `Obj.repr` of zarith's
     pair, which is the tuple a two-value `let` takes apart. Whether
     `Mod` should be restated through `Mul` and `Add` is open. The
     implementations are zarith's `sub`, `mul`, `div` and `div_rem`;
     the interpreter of `self/eval.sl` runs the models, deciding the
     proofs with `lt-dec`. `tests/nat_arith.sl` runs each once at
     elaboration and once inside a thunk, so the extracted program
     exercises the implementations.
     Beside the lemmas section 42 names, the prelude has `lt-le-trans`,
     `add-lt-left`, `mul-lt` and `divmod-lt` (the quotient of a
     positive dividend by a divisor above one is below the dividend);
     `lt-subterm` decides `a` against the predecessor of `b` with
     `nat-cmp` in an erased position and chains `prove-subterm` through
     `subterm-trans`. In `slc`, `nat-sub` is `sub` under `lt-dec`, and
     `bin-of-nat` divides by two under `divmod-lt` and `lt-subterm`, so
     a numeral's cost does not grow with its value.
133. **An extern type's extraction goes through templates; its view stays
     for held values** (the owner's decision, after this session proposed
     it, with the owner's hole discipline: every hole but a branch body
     is filled with a variable name). `lib/ffi_templates.txt` holds, per
     extern type, a match template and per constructor a build template:
     OCaml over `Obj.t` with holes `{s}` the scrutinee, `{bI}` the body
     of constructor I's arm, `{fI.J}` the binder of its field J, `{aI}`
     a build argument and `{tK}` a temporary. A template mentions no
     program name, only holes and library names. The engine fills `{s}`
     and every `{a}` with a variable, binding the expression to a
     temporary first unless it already is a name, so nothing is
     evaluated twice; `{f}` holes take the branch's own binders, or a
     dummy for an arm without one; `{t}` holes take the instantiation's
     temporaries `x<n>_t<k>`; a body hole takes its arm's body, a live
     arm without one the `else`, bound once as a thunk `x<n>_d` when it
     stands for more than one constructor so its text is written once,
     and a refuted arm `absurd ()`. The reference numbers instantiations
     with a counter; `slc` uses the code's nesting depth (`names-depth`),
     which the session reads as sufficient because a body sits in tail
     position, so no template text follows a body in its scope, and
     every other hole is a name bound before the template's text; no
     program name starts with `x`, so a temporary captures nothing.
     `lib/ffi.ml` checks a template against the model's shape at the
     `extern` mark (each body and field binder once, each argument
     read, no hole beyond the shape); that a body sits in tail position
     is not checked, `tests/extern_tail.sl` being the evidence for the
     shipped ones, and `tests/extern_nested.sl` covers a match in
     scrutinee position, an `else` over two constructors, a build inside
     a build and matches under matches. A type without a template is
     extracted through its view; `--no-templates` strips them all, the
     test runner extracts every FFI-mode test both ways, `slc` takes
     the same flag and `self/bootstrap.sh` compiles a subset without
     them. Held constructors and Matchables go through the view
     (`tests/thunk_extern_first_class.sl`). The file is embedded in the
     interpreter by a dune rule and in `slc` through `lib/embed.sl`,
     one text parsed by both, though only the reference checks it.
134. **The driver converts a `String` held as the FFI's slice to and from
     the host's string directly** (the owner's request, after a
     performance audit). `Driver_core.make` takes optional
     `str_of_host` and `str_to_host`; `lib/program.ml` supplies them
     when `String` is the FFI's slice, `lib/extract.ml` emits them when
     `String` extracts as an extern, and `self/emit.sl` always does,
     `slc`'s `String` being the slice; without them `of_string` and
     `to_string` fold over `scons` and `un_str`, which is what
     `--no-extern` gets. The folds cons a read file one `SCons` at a
     time, and under the FFI each `SCons` copies its tail, so a
     `ReadFile` of n bytes would copy about n^2/2 bytes, every copy
     going to the major heap.
135. **`Half` is an extern type over a `Nat`, and `nat-halve` the identity
     into it.** `H1 m` and `H2 m` stand for 2m+1 and 2m+2, `m` at
     `many` with an erased `Double m d` fixing the index; `nat-halve`
     models it structurally and the FFI holds a `Half` as the `Nat`
     itself, matched and built through its own view (`half_view`,
     `half_of`) and template (`lib/ffi.ml`, `lib/ffi_templates.txt`),
     so a trie keyed by a `Nat` can walk its digits. `slc` carries it
     as `ExtHalf` with a `PHalf` payload in its compile-time
     interpreter.
136. **`Bin` is a plain type, and `slc`'s ids are `Nat`s** (the owner's
     decision: every use of `Bin` erased in `slc`, the conversion through
     `Half`). The FFI holds no `Bin`, and `lib/literal.ml` spells a
     numeral through `Half`'s view. In `slc` an id is a `Nat`:
     `nat-cmp` compares, `Succ` mints, `nat-eq-dec` decides equality,
     and every trie (`base.sl`'s `IdMap`, `heap.sl`'s store, `core.sl`'s
     fact table) walks the id's halves by `nat-halve`. In the evidence,
     a one-digit step is `(Succ d)` with an erased `Double k d` field
     beside `k`, a two-digit step `(Succ (Succ d))`, and the order is
     the prelude's `Lt`. A branch the digits refute by shape is refuted
     by `double-parity`, and two keys under one digit meet through
     `double-inj`/`double-fn`. `Bin` spells numerals into their
     `Numeral` proofs in `elab.sl`. The emitted OCaml names ids in
     decimal (`v1234_length`).
137. **Four string externs: `str-cmp`, `str-length`, `str-split` and
     `nat-str`.** `str-cmp` decides `StrLt`, the lexicographic order by
     character code, into `Cmp` as `nat-cmp` does, its model the
     structural comparison; `str-length` returns the length with a
     `StrLength s n` relation; `str-split` takes the string, a count
     `k`, and erased `StrLength s len` and `Lt k (Succ len)`, returning
     the first `k` characters and the rest with `Append a b s` and
     `StrLength a k`; `nat-str`'s model divides by ten. The
     implementations are a byte comparison of the two slices, the
     slice's stored length, two sub-slices, and `Z.to_string`.


## Opening a `Matchable` (DESIGN.md section 8)

The owner decided the points marked so; everything else is the
session's reading, with the tests as the evidence.

138. **A `let`'s right-hand side statements are statements of the
     enclosing expression.** The entries keep their ids in scope with
     their names dropped (`Env.hide`; in `self/`, `env-hide` keeps the
     inner objects and clears the added entries' names), and the
     statements before the right-hand side's final expression wrap the
     `let`'s own binding (`Elab.elab_stmts`; in `self/`, `elab-stmts`
     and the `SSeq` code a `let` returns).
     `tests/let_nested_scope.sl` refuses the name; the entry's survival
     is what `tests/open_adt_let.sl` reads.

139. **Nothing consults a `Matchable` until it is opened** (`Env.opens`,
     `Elab.open_adt`, `Env.merge_opens`; in `self/`, the fact table's
     `Opens`, `env-open-adt` and `merge-opens`). Of two opened entries
     that would name one thing, the better-ranked is kept, the older on
     a tie. The invariant is restored after every forcing, a branch
     entered (`Elab.refine`), a `let-match` or `comptime-match` as much
     as an open, rather than inside the unifier, which the session
     reads as equivalent for what is accepted (every equation is
     canonicalized before its atoms are compared, and an opened
     Matchable's constructor list is read canonically) and which keeps
     `self/`'s unifier and its termination evidence untouched. The
     open's tests: `tests/open_adt_bad.sl`, `tests/open_adt_unify.sl`,
     `tests/open_adt_clash_bad.sl`, `tests/open_adt_expr.sl`,
     `tests/matchable_prefers_many.sl`, `tests/known_matchable.sl`,
     `tests/open_adt_mult_bad.sl`, `tests/open_adt_not_bad.sl`. A match
     that dispatches at runtime reads its Matchable's value, stamped in
     where the entry is `Settled` with its ADT and read from the entry's
     binding otherwise (`Env.readable`; in `self/`, `readable` reads the
     objects list, which `env-hide` keeps; `tests/open_adt_erased_bad.sl`,
     `tests/open_adt_let.sl`). `open-absurd` shares `Elab.result_tele`
     with `match` and compiles to the absurd code
     (`tests/open_absurd.sl`, `tests/open_absurd_clash.sl`,
     `tests/open_absurd_bad.sl`). The unopened cases:
     `tests/open_tyctor.sl`, `tests/unopened_matchable_bad.sl`,
     `tests/unopened_newtype_bad.sl`, `tests/open_adt_branch_bad.sl`.
     The keywords are the owner's: `open-adt` names the minting site,
     and `open-absurd` carries the token that marks a contradiction
     elsewhere.

## More requests (section 27)

Asked for by the owner in chat: environment variables in Java's two
shapes, appending to a file, reading what is left of stdin, listing a
directory in Java's shape, the working directory, one query for what a
path holds, `MkDir` and the two deletes. The owner chose the general
`Pair`, sorted listings, the `world` for the environment and the
working directory, single-level `MkDir`, deletion that reports
`Unchanged` rather than failing on an absent path, and the `unix`
dependency; the shapes below are the session's.

143. **Ten of `Request`'s constructors**: `GetEnv`, `GetEnvs`,
     `AppendFile`, `ReadRemaining`, `ListDir`, `GetCwd`, `Stat`,
     `MkDir`, `DeleteFile` and `DeleteDir`, with the answers
     `lib/prelude.sl` gives them. `Pair` is general rather than an
     environment-specific record, the owner's choice over a two-field
     `EnvVar`. `EntryKind`'s `Missing` makes absence an ordinary answer
     and keeps `Fail` for a path the driver could not read at all, on
     the reading that a program checking whether something is there is
     not handling an error. `Change` is shared by the three requests
     that ask for a state rather than an action, so that one answer
     says both that the request was met and whether this call is what
     met it; the session's argument for it, which the owner took, is
     that `mkdir` is atomic, so collapsing the two into a plain success
     would throw away the only race-free way to learn which caller
     created a directory, while failing on an existing one (as POSIX
     and Java 6 both do) would make the ordinary case awkward.
     `ListDir` sorts and omits `.` and `..`; `Sys.readdir` already
     omits them, and sorting is so that a test may compare its output
     byte for byte, which the harness does between the interpreter and
     the compiled program. `AppendFile` creates the file if it is
     absent and, like `WriteFile`, takes no mode, the language having
     no permissions model.

144. **`GetEnv`, `GetEnvs` and `GetCwd` go through the `world`** as
     `GetArgs` does, the owner's choice, so that `test/runtest.ml` can
     supply them from `; env:` directives and a test can pin what it
     prints; the file system requests stay direct, as `ReadFile` and
     `WriteFile` are. The harness runs an extracted program under
     `env -i` with the same variables, so the interpreter's world and
     the compiled program's agree on what a program reads; the working
     directory is the real one in both, which is why
     `tests/io_stat.sl` asks `Stat` what `GetCwd` named rather than
     printing it. `ReadRemaining` reuses the world's stdin field,
     `read_rest`: for `bin/main.ml` and for an extracted program it is
     `In_channel.input_all stdin`, which is what the channel has left,
     and the test world drains its pending lines, however much
     `read_line` has taken.

145. **The driver uses `unix` rather than `Sys` alone** (the owner's
     choice). With `Sys` alone, `Sys.file_exists` answers false for a
     path whose parent denies access exactly as for an absent one, so
     `Stat` would report a denied path as `Missing` and its `Result`
     would have no reachable `Fail` at all; and it would cost `IsOther`,
     `Sys.is_regular_file` arriving only in OCaml 5.1. The classification
     reads the errno: `ENOENT` is `Missing` for `Stat` and `Unchanged`
     for the deletes, `EEXIST` on a directory is `Unchanged` for
     `MkDir`, and anything else is a `Fail` carrying the message.
     `MkDir` is the one that asks a second question, whether what is in
     the way is a directory, so its `Unchanged` is the one answer here
     that a concurrent change could in principle turn into the wrong
     report; `Changed` never can, being the syscall's own success.
     Extracted programs, the bootstrap and the benchmark compile with
     `-package zarith,unix`.

## `thunk` (section 27)

The owner proposed the in-language helper that thunks a value rather
than an anonymous function form, and accepted the extra verbosity at the
call sites; the rest below is the session's.

147. **`thunk` is a prelude function rather than a form.** Its body is
     the captured value alone, so the closure it returns needs no
     `Predates` proof of its own, and `def-fns` accepts the erased level
     parameter as the level to define at.

     Reaching `thunk` at a level `L` needs `Predates thunk-lvl L`, which
     a caller holding `L` only as an existential cannot mint for itself,
     `prove-predates` wanting a level minted by `def-lvl` with the other
     in scope (section 18). In the session's reading that is section
     57's factory rule rather than a limit on `thunk`: the relation is
     established where the level is minted, so a function that mints a
     level and hands it back returns the relation with it.

## The emitters' walks over the store (sections 27, 29)

148. **`lib/extract.ml`'s sharing table scans a bucket in tail
     position.** `Hashtbl.hash` reads a bounded prefix, so every suffix
     of a long self-similar value shares one bucket; the bucket is a
     list scanned by `List.find_opt`, which is in tail position where
     `Hashtbl.find_all`'s scan is not. Two things there are open,
     neither of them failing anything known: `value`/`plain` recurses
     once per node of the value it walks, which an accumulator cannot
     fix and an explicit worklist could, at the cost of reordering the
     `shared_N` definitions it emits; and the lookup is linear in its
     bucket, so extracting such a value appears quadratic in its depth.
     A deeper hash would not help the second, the suffixes of such a
     value differing only in length.

149. **Forcing a rule onto an atom then unifies the atom's type with its
     term's.** The owner's decision, in chat, for the minimal language
     (`mini/unify.sl`'s `UAssign`): without it an atom of a former's
     type could be given a term of another type and a later telescope
     would have no type for an `is` entry mentioning it
     (`tests/mini_untyped_rule.sl`; that program is also refused by
     section 11's rule). Whenever forcing gives an atom a rule, the atom's type
     is then unified with the type of the term it rewrites to, as the
     next equation; an atom aliased to another is the case of this that
     section 7's signature check covers, and the type equation a branch
     entry forces (section 7) follows from the scrutinee's, so
     `mini/`'s `Refine` forces the one. `lib/` and `self/` assign with
     no type check, and unify signatures only where both atoms' types
     are formers (section 7); whether they should follow, and whether
     under section 11's rule the added equation can ever change an outcome, are
     open, in the session's reading.

150. **The compile-time interpreter reaches a call in tail position by a
     tail call.** At the owner's request, who asked that `slc`'s
     compile-time evaluation not grow the stack, or at the least that
     interpreting a tail call be a tail call. In the emitted OCaml,
     `eval`'s `CLet`, `CLetRec` and `CMatch` reach their continuations
     by a tail call, the normalizer (item 125) dropping the `let` that
     would bind them.

     `eval` and `apply` return the list of many results together with
     an erased `Picked` reading it back against the index, so fitting
     the results to a call's index is a proof rather than data. Where a
     call's index and the member's declared returns differ -- they
     differ in erased entries, as item 125 records for the normalizer
     -- `apply` decides `ManySame` before the body runs, by
     `mults-same`, whose recursion is lexicographic on the two lists,
     and `picked-same` carries the proof across afterwards; being
     erased, it does not disturb the tail call. `picked-lockstep`
     derives the `Lockstep` a `let` needs from the two `Picked`s;
     `vals-one` refutes the empty list from its `Picked`; and
     `eval-picked` builds its `Picked` as it walks. `vals-fit` serves
     only where arity is genuinely a runtime property and no recursion
     follows it: an extern's results, a constructor's one value.

     A tail call in interpreted code costs no host stack. A non-tail
     call in interpreted code holds host frames, as it must without a
     heap-allocated continuation. `tests/comptime_tail.sl` is the
     guard. Its 131071 iterations decrease an *erased* `Nat` tied to a
     non-erased binary counter by the prelude's `Numeral`, which is
     what keeps the loop from building a unary `Nat`; the owner
     suggested that shape.

     `lib/eval.ml`'s `eval` and `apply` both hand back a plain `value
     list`, so `CLet`, `CLetRec`, a match branch, `CApp`'s `apply` and
     `apply`'s own `eval` are OCaml tail calls in the reference.
## An extern is run wherever it is claimed (section 42)

The shapes and the messages below are the session's.

151. **The constructors `apply-extern` builds with come from the model's
     return type.** `self/eval.sl`'s `apply-extern` produces an
     `ExtResult` — a payload, a pair of them, a constructor at its
     discriminant, or one of the array and write results — decided by
     one match over the extern. `ExNatCmp` and `ExStrCmp` take the
     constructor route, so `slc` compares at compile time without
     running the model. The constructors are found by reading the type
     constructor off the model's own return type and taking the `Adt`
     of its opened `Matchable`, rather than by a table of names as
     `lib/ffi.ml` uses: the session's reason is that the model names the
     type it builds, so no name can be shadowed out from under the
     lookup. What the FFI has to record per extern is the shape that
     type must have (`ext-result-shape`), checked as `Ffi.check_shape`
     checks an extern type's (`ext-type-shape`). The reference's
     `lib/eval.ml` `apply` runs the implementation.
152. **The FFI's tables are one record per extern.** `lib/ffi.ml` has
     one `fn_spec` per function and one `ty_spec` per type, holding an
     implementation's arity, the plain types it builds, and the shape
     its view has, so half-registering one is a type error ("Some
     record fields are undefined"). A plain type's shape is in
     `plain_shapes`, and a missing shape for a plain type a `needs`
     entry names is an error ("the FFI records no shape"). `claim_fn`
     and `claim_type` are the single entry points, ordered so that an
     arity or shape mismatch is reported ahead of the already-bound
     check, which is what `tests/extern_arity_bad.sl` depends on, `add`
     being bound by the test's first declaration already.
153. **A test may ask for the FFI alone.** `; externs: only` runs a test
     with the implementations and not again with them stripped, for one
     whose source model is too slow to run. The session's reading is
     that this is a hole in section 42's requirement that `dune test`
     run every test both ways, and should stay rare.
     `self/bootstrap.sh` needs no directive of its own, running the
     reference with the FFI as `slc` always does.

154. **A `Nat`, `Char` or `String` printed as its literal** (DESIGN.md
     section 45). `Literal.spell` is `Literal.classify`'s inverse. Its
     character and string cases live in `lib/ffi_core.ml`, which the
     interpreter, an extracted program and `slc`'s output all paste in,
     so one definition serves the three back ends. Run over all 256
     codes, it round-trips through the reader and `classify`.

     Printing in the interpreter is type-directed
     (`Elab.show_value`), as item 66's generated printer is. What
     forces that: a `Char` and a `U8` are their `Nat` at runtime
     (section 33), so nothing but the type tells those three apart, and
     a `(Half)` is a zarith integer too and must not be spelled as a
     numeral. The three are recognised as the prelude's own entries, as
     item 65's driver finds its constructors, rather than by name, so a
     program's own `Zero` or `SNil` (`tests/gmap.sl`) is untouched. A
     `Char`'s code and a `String`'s elements are not spelled as a
     literal when the `Nat` is not a byte, since `Literal.spell` has no
     reading for one: the session could not construct such a value, the
     `Lt` proof `MkU8` carries bounding both (section 42), so the guard
     is read as covering a case the checker already rules out rather
     than one the printer meets.

     Where the value is extern-backed the spelling reads the payload,
     `Z.to_string` or the slice's bytes, rather than walking the view;
     the models are walked instead. The session's reading is that this
     is the representation's own spelling rather than an optimization
     (CLAUDE.md 6).

     `comptime-match`'s diagnostic (section 28) goes through the same
     printer, so the wrapper-payload channel that section describes
     reports a `String` payload as its text.

     `tests/literal_print.sl` pins the two spellings the other tests
     only touch: every character form, and the string escapes. Each
     spelling it prints, fed back as a program, prints as itself.
     `tests/literal_diag.sl` pins the same two through the diagnostic
     above, which `tests/comptime_bad.sl` reaches for a `Nat` alone;
     they are the only tests that reach `slc`'s own compile-time
     spelling of a `Char` or a `String`, the emitted printer covering
     the rest.

155. **A warning is an output channel of its own, and is tested as one.**
     `self/main.sl` writes `slc`'s warnings ahead of either outcome,
     since a warning stands whether or not the program is then refused,
     which is the order the reference produces them in, and the message
     carries the location, as the reference's does. A warning is
     neither a program's stdout or stderr nor a refusal, so neither
     `; stderr:` nor `; error:` sees it.

     The directive `; warns:` (name proposed by the session, CLAUDE.md
     10) checks it in both harnesses. `test/runtest.ml` captures the
     reference's warnings through the `Env.warn` hook and requires them
     whichever way elaboration went. `self/bootstrap.sh` greps `slc`'s
     own stderr, on the refused path as well as the compiled one.
     `tests/phantom_warn.sl` warns and then compiles and runs.

156. **Uniqueness implementation scope and working conventions (Codex/Astra).**
     The owner allows restructuring the self-hosted heap and staged
     restoration of erased proof invariants, while preferring the compiler to
     continue exemplifying checked correctness through dependent proofs.

     Uses are recorded against the binder as written, never its canonical
     value. In a computed `share` argument, the uses needed to compute that
     expression retain their own multiplicities. Erased and unreachable
     bodies contribute no usage, including statements preceding their
     results.

157. DESIGN.md section 36's locations are represented separately from ordinary value rules.
    Location terms retain the original binder when `is` canonicalization runs;
    only location equality and the listed location-producing operations merge
    that partition. Argument temporaries preserve the caller's physical word
    before a call consumes it. Dropping a physical result must retain
    computations in its expression. The same lowering applies in the
    interpreter and extracted code, including tail/delegate validation.

158. Phantom/absurd bodies bypass both usage and multiplicity-promotion checks,
    as their runtime expressions are erased.

162. Tagged unmarked datatypes use OCaml variants with mutable Obj.t fields;
    the host constructor tag supplies the discriminant. Narrowed GADT views
    retain the prior extraction's refutation of impossible branches. Untagged
    unmarked constructors use one-constructor OCaml variants with the same
    mutable fields; their statically known match needs no discriminant test.
    Empty constructors need no mutable storage. Held extern Matchables expose
    the same ordinary tagged constructor layout.
    A store into such a block goes through the constructor's own pattern rather
    than `Obj.set_field`, at the owner's direction: the block is read at its
    constructor's type, narrowed to that one discriminant where the type is
    tagged, so the match binding the record has no other arm; whether the host
    then tests the tag is the session's expectation from the narrowing, not
    something it measured. Reading a cell's slot is the same match. The
    session's reading, not the owner's, is that this is what the `mutable`
    marks are for, a store through `Obj` into a block the host may treat as
    constant being the thing they rule out. An array block is a host array,
    so its back-patch is an unchecked element write, as the FFI's own array
    primitives are, its index being one the emitter generated by walking the
    array whose length it had just emitted. Both emitters do this and neither
    writes `Obj.set_field` or `Obj.field`.

163. Captured mutable blocks are emitted by assigning each an identity before
    following its fields, then filling those fields. This is intended to preserve
    sharing and cycles through inert Slot words.

164. Compiler-created result placeholders and expression-local temporaries are
    distinguished from caller words still available after a let. An at-class
    representative need not itself be available at runtime: reconstruction uses
    an available member, including the forwarding let's binder. Nested let
    normalization moves binding continuations into the producing expression;
    this exposes actual tail calls after location returns have been dropped.
    The section 61 append helper's emitted recursive branch ends in its recursive call,
    with the cell stores before that call.

165. Extern-model context is lexical, including nested local function
    bodies.

166. The fixed FFI boundary converts comparison results to the declared Cmp
    representation and reads Rope values through their constructor view.

167. Array place and swap update the array's slot. A captured array keeps its
    identity, assigned before its elements are filled to support Slot cycles.
    Outside extern model bodies, unique Array patterns have no cell binder even
    when extern implementations are stripped.

168. The owner's clarification confirms that proof-indexed array get/set may
    use unsafe operations. Distinct logical location classes need not imply
    distinct physical words; no at fact is inferred just because nullary
    values share an immediate representation. The source language is pure
    and specifies no observable evaluation order. Destructive updates
    implement that pure semantics; their execution order must not be
    observable in well-typed programs. The interpreter's traversal order is
    an implementation choice.

169. The self port separates semantic multiplicity from physical result shape:
    singleton Once remains unique for checking, while a runtime aggregate is
    physically Many. `slot-of` and return places use a separate location
    partition; their identities need not remain canonical in the ordinary fact
    table after consumption. A unification outcome may therefore retain a
    changed environment without decreasing the ordinary fact count. The existing
    erased history and freshness proofs govern ordinary fact traversal.

170. The self heap models updates by returning a new Store with an override
    map; each Ref retains its immutable allocation snapshot. Reads consult the
    supplied Store first and use the snapshot only when it has no override.
    The retained history proofs appear useful for allocation identity, stamp
    bounds, and widening references into a later allocation history. They do
    not establish unchanged current contents across Stores, acyclicity, or
    preservation of source typing and uniqueness by updates. In particular,
    ref-unique proves identity of allocation snapshots at a stamp; it is a
    standalone theorem with no callers. StoredBody's suffix evidence keeps
    references inside a replacement body within the current allocation history.
    Retaining the whole snapshot history is an implementation choice, not a
    requirement of DESIGN.md; a history of allocation identities may suffice for
    these structural guarantees. The diagnostic printer reads current bodies
    and bounds recursive traversal at depth 100000.

172. The owner's approved narrow repair of the computed-head erased probe
    introduces a callable-head demand: elaborate the expression once in its
    actual context, taking unique demand for a Cell or UniqueFn and many for
    an ordinary callable. A match's result annotation determines its head
    demand before checking branch bodies; singleton values and call markers
    propagate that demand. Ordinary fixed expectations, including contextual
    erasure, retain their modes. No discarded elaboration, global-state
    rollback, or warning suppression is needed. This is the narrow repair
    only; whole-body phase separation remains required follow-up work, as
    recorded in 180.

173. Ordinary unions use one-constructor native variants, one shape per payload
    arity, rather than a separate raw-array representation. Since union matching
    already knows its constructor, this shares mutable-field extraction with
    enums without a discriminant test. Nullary constructors remain immediate.

174. The self normalizer removes singleton physical value wrappers and unused
    erased or constant bindings using its existing context-strengthening proof.
    This is intended to retain the tail/delegate rules after argument
    preparation and at-return projection. Telescope identities remain marked
    throughout their signatures, including earlier parameters, and are
    restored on leaving the signature so ordinary body variables remain legal
    `slot-of` arguments.

175. Captured cells and Array backings may point to a closure that captures the
    same allocation. The ML extractor therefore buffers field
    initialization and final actions until all captured definitions have been
    emitted, with final actions retaining source order; allocation skeletons
    still precede every reference to them. This preserves field identity and closes cycles through functions as
    well as direct cell/array cycles. The self extractor separates
    skeletons, definitions and fills.

180. **Required follow-up: separate whole-body typing from multiplicity
    calculation and checking.** The owner approved finishing the narrow
    computed-head repair, while explicitly requiring this broader approach
    later. Elaborate a whole function body into a typed representation that
    retains written labels, match modes, erased expressions, source locations,
    branch/refutation information and capture scopes. A later pass should
    calculate demands and validate uses, captures, returns and word availability
    before erasure and runtime-code construction. This appears compatible with
    the language: already-known head types can direct a recursive demand walk,
    without re-elaborating source in a different context. Run-position statements
    still need checking before execution. The current repair does not implement
    that separation; its demand mode is an interim elaborator interface.

181. Self's indexed ExprDemand and DemandBridge retain the distinction between
    a head's one physical word and its semantic many/unique demand.

183. **Questions left for the owner**, none decided here:
    - The `newtype` and `extern` marks being structural (sections 24 and 37),
      an unmarked `(Matchable enum T ...)` literal does not accept an extern
      type's Matchable, and no signature abstracts over the marks.
    - `coercible-wrap (Unique)` over a many-labelled field is Shared to
      Unique (section 34 as written), so a live many value yields any number of
      unique aliases of its newtype wrapper; nothing found can exploit it,
      the wrapper having no cell.

184. **What a value prints as** (DESIGN.md section 45). Not decided, and
    left open by the owner: whether a rendering's reading back as the same
    value becomes a test of its own, which `tests/literal_print.sl` already
    does for the three literal types.

## slc's interpret mode (sections 27, 32)

The owner asked for an interpret option for `slc` in place of emitting
OCaml. The shapes below are the session's, made without the owner.

187. **A run may update a Settled the extractor then embeds.**
    With a continuation owning a top-level unique Settled, the run
    updates that Settled's block in place (`tests/io_unique_state.sl`'s
    counter), so a program extracted afterwards would begin where the
    run had ended. `--extract` runs no final, so `test/runtest.ml` takes
    the extracted sources before running the deferred final. Not a
    defect in the language on the session's reading: the Settled was
    consumed by the definition that captured it, and nothing reads it
    afterwards.

188. **`slc --interpret`** performs the elaborated program's finals in
    place of writing them out (`self/interp.sl`), each as
    `lib/program.ml`'s `consume` has it and in file order. A `Program`
    final is walked one step at a time: each `Continue` becomes a step of
    slc's own `Program`, which applies the program's continuation with
    `self/eval.sl`'s `apply` under the usual fuel, to a token standing for
    slc's own world, and walks the `Program` that comes back; `Exit` exits
    slc with the code. The evaluator threads a world of its own through
    every evaluation function, generic in its type and paired with a
    `Performer` for it: at compile time a `Unit`, whose performer answers
    a `world-do` with an error block, there being no world to perform
    with; under `--interpret` slc's own `World`, whose performer
    (`perform-request` in `self/eval.sl`) performs the request with
    `world-do` and allocates the answer into the compile-time store -- a
    `String` as the FFI's payload, a `Maybe`, `Result`, `List`, `Pair`,
    `Unit`, `EntryKind`, `Change` or `Usage` through the prelude's
    constructors, looked up by name in a list the interpreter hands it.
    The performer and the helpers it calls sit ahead of the evaluator's
    own level, so the closure the interpreter builds over them at
    `perform-lvl` can be called from inside evaluation. `Measure` answers
    the figures less a reading slc takes as it begins interpreting the
    `Program`, each floored at zero. A plain value and a thunk's result
    print through the compile-time printer (154), a `String -> String`
    function is applied to what `ReadRemaining` answers; those finals
    evaluate with the compile-time performer, having no world to reach.
    The interpreted program's arguments follow a `--` among slc's own,
    and `GetArgs` answers them without a request; its environment,
    working directory and stdin are slc's. A continuation's parameter
    type must name the prelude's `Pair` for `GetEnvs`.
    `self/bootstrap.sh` runs every test a third time this way and
    compares it with the reference as it does the compiled program.

    The evaluator's fuel is 1000000000, which the million-step tail loop
    of `tests/extern_tail.sl` needs under `--interpret`, where neither the
    reference nor the compiled program has a bound. A value the
    interpreter hands back as an error block, running out of fuel among
    them, is reported as a runtime error on stderr with exit code 1, as
    the reference's is, wherever a final or a request is read. The
    compile-time printer reads a nested field's type in the environment
    `field-types` hands back, as `show_value` passes its own down, so a
    field whose type names the outer value's indices (`tests/numeral.sl`'s
    `Vec`) prints with its fields.

189. **A let-bound match is floated into its branches only under a
    continuation of atoms.** 164's normalization copies a let's
    continuation into every branch of a right-hand-side match only when
    the normalized continuation is a variable or a `values` of
    variables, constants and erased entries, in `lib/elab.ml`'s
    `normalize` and in `slc` alike; copying under any continuation
    would multiply the code after N such matches in sequence 2^N
    times. The float exists for a continuation that only repackages
    the binders, the projection dropping an `at` return in particular;
    any other continuation stays a `let` of the match, where a marked
    call is not in tail position unless the continuation returns the
    binders, which the normalizer folds. In slc the words and
    temporaries lists are kept in descending id order (`insert-desc`),
    an invariant by construction.

190. **A call's argument or head that is already a variable is not
    bound to a temporary.** `self/elab.sl`'s `prepare-or-keep` leaves
    an argument, a callee or a constructor head whose term is a
    variable and whose code is that variable unbound, as `lib/elab.ml`
    does for an argument. Match scrutinees are bound, as the reference
    binds them.

191. **The rules list is erased.** Section 21 lets subterm recursion go
    through an erased argument, so the list is erased everywhere:
    `find-rule` walks the erased `MemRule` witness the trie's `C1`
    agreement hands it, `append-rule` is erased, and `RuleFound` is
    indexed by the term it finds, every field erased. The chase's only
    physical step is the trie lookup.

192. **A newtype is looked up among the opened objects the index lists
    for its constructor.** `find-newtype-in`, like `find-matchable-in`
    and `listed-in`, first tests membership in the candidates the opens
    index gives for the name, and the reference's `newtype_of` and
    `matchables` test an object's recorded names before canonicalizing
    its type. Exact under the index's invariant, an object being listed
    under each name its type holds canonically and the wrapper
    constructor being one of them.

193. **What an indentation warning says, and where the check runs.**
    The check of `lib/indent.ml` runs over each file the driver is
    handed, before that file is parsed; what the text left open is
    this session's, and the two implementations were compared over the
    repository's sources and a thousand generated files to settle it
    the same way on both sides. A message is
    `path:line:col: warning: text`, the shape of an error with
    `warning` for `error` (194), and each of these rules compares two
    lines, so a `note` under it names the line compared against; the
    forms a file leaves open are named one by one the same way, the
    innermost the warning and the rest its notes, which says where
    each missing `)` goes where a count would not. The depth never falls
    below zero: a `)` with nothing open is reported where it sits and
    leaves the depth alone, so one surplus `)` does not shift the
    nesting every line after it is read against, which also lets
    `self/reader.sl` hold the depth in a `Nat`. A line is the line a
    token's first character sits on, read from the token's offset
    rather than from the line `Reader.scan_upto` records for it, the
    two differing for a literal spanning lines; the tab a line is
    warned for is any tab in the source between that line's start and
    its first token, a literal's own text included, which is what
    reading the offsets amounts to. Where the lexer cannot finish, the
    check reports what was read before it stopped and no more, and
    leaves the stopping point to the syntax error the driver then
    reports; `bin/indent.ml`, which reports nothing else, prints it.
    `lib/builtin.ml`'s prelude is not checked, being no file the
    driver was given, where `slc` checks it as one named on its
    command line.

194. **Every message carries a file, a line and a column.** The owner
    asked that they, and so `lib/reader.ml`'s `loc`, which is a file
    and a position, a token's first character with both counted from
    one; the file is stamped in by `Reader.files`, so a message names
    the file its form was read from, as a `;! file` pragma names it
    (DESIGN.md section 4), rather than the file being run. The note
    pointing at `bin/shape` names the source read, the one that tool
    is run on.
    The spelling is `path:line:col: error: text`, `warning` or
    `syntax error` for `error` where those are what is meant; 193's
    warnings and section 12's phantom-constructor warning both read
    that way. A message about two places writes the second as a `note`
    on its own line under it, `path:line:col: note: text`, rather than
    describing it in prose (193). An error does the same, through
    `Env.error_with` and `slc`'s `error-at-with`, where the second
    place is what makes it readable: the earlier of two conflicting
    uses of a `unique` value, which the use map records beside each
    use; the first of two `else` branches; and the declaration that
    already bound an extern implementation, which the FFI's claimed
    names record and which is often in another file, so that the note
    is where carrying the file in a location pays. Which of these
    deserve one is this session's reading of where one location is not
    enough; the rest carry one place. What has no position names the
    file alone: a contradiction reaching the driver rather than the
    form that would have placed it, and a runtime error, the
    post-erasure code carrying no positions and an extracted program
    having none to carry. A string literal is placed at its opening
    quote, its line its own rather than the line it closes on, and an
    unterminated one is reported there, so that a position is always
    the start of the token it names.

    The two implementations place a message differently in one
    respect: the reference carries a location per form, while `slc`
    records one in its environment for each form it descends into, so
    where a check runs after a sub-elaboration has returned `slc`
    names an enclosing form. The directives match on text alone, so
    `self/bootstrap.sh` compares where each side puts its first
    message on every error test and prints how many agree on file,
    line and column, on file and line alone, and on neither, so the
    number cannot quietly grow.

195. **Which binders the shadowing warning covers, and which of its
    two messages each earns.** Section 19 makes every name shadowable
    and the checker warns at every binder that hides a name already in
    scope; the spec says nothing further, so what follows is this
    session's. `Env.bind` is the one place every entry is minted, but
    it is reached twice for one binder -- reading a stored telescope
    binds its entries again -- so `bind` takes two things and not one:
    `~at`, the position the source wrote the binder at, which the entry
    keeps and a later message points at, and `~written`, whether this
    site is that writing, which is what decides the warning. A
    telescope carries the position for its own entries
    (`Term.entry`'s `loc`), so a parameter bound again inside its body
    keeps its declaration's position and does not warn a second time;
    it is no part of the type, `Term.blank` clearing it so that
    telescopes compare without it. The sites that write a binder are
    the declaration telescope entries, `let` binders, the names
    `def-lvl`, `def-fns` and `def-adts` introduce, a pattern's fields,
    and the binders a `unique` destructure, `cell-match` and an `else`
    add; everything the elaborator mints for itself carries
    `Reader.nowhere` and is silent. An entry with no position is then a
    built-in and nothing else -- a special form, an annotation token or
    one of the opaque types -- which is what lets the message say so
    rather than point nowhere. `slc` models all of it, its `Entry` and
    `EInfo` carrying the same position, so its messages agree with the
    reference's on the column as well as the line (`self/README.md`).

    `tests/shadow_warn.sl` and `tests/shadow_builtin_warn.sl` take a
    binder of each kind through the warning, and
    `tests/shadow_false_capture.sl`'s subject is a declaration hidden by
    a later one.

## `dump-context`

The owner asked for a special form that, applied, errors out and dumps
what would help the programmer -- the variables in scope with their
canonicalized types and `is` rules, their declared multiplicities and,
for a unique one, whether it is consumed or shared yet, the at table,
the goal, and whatever else is useful. Every shape below is the
session's, made without the owner.

196. **What `dump-context` is and what it reports.** `(dump-context)`,
    or `(dump-context e ...)`, is refused as an error: its first line is
    the `path:line:col: error:` header every refusal has, and the report
    follows as lines indented two spaces, an entry's details four, so
    that a test names any line of it with `; error:` directives as it
    names any refusal (`tests/dump_context*.sl`). It stands in three
    positions, each of which the reference hooks separately: as an
    expression, where the telescope the position expects is the goal; as
    a statement, in a body or at the top level, where there is no goal
    and the report says so; and as a type, in a signature or a `let`
    binder, where the goal is a type. It is listed among the statements
    (`Special.statements`) so that a top-level `(dump-context)` reads as
    one, and handled before the "is a statement, not an expression"
    refusal so that it also reads as an expression.

    The report, top to bottom, all of it through `Env.show` so that a
    term is canonical and each atom named as any message names it:
    the goal, as the expected telescope under the position's
    multiplicities with any `at`, a `_` still open numbered `__?1` and
    placed by the usual note, and, for a goal whose type's head has an
    opened `Matchable`, that type's constructors with their types;
    the position's multiplicity; whether the enclosing position is
    erased (nothing there counts as a use); whether this is run position;
    the current level and the enclosing function's subterm arguments in
    order, or that this is the top level; whether this is inside an
    extern function's model. Then every entry in scope that the
    program's own files bound, newest first, one line each: its name, a fetch
    form or `__1`, as MANUAL.md says, its canonical type, its multiplicity, `Settled` or `Hypothetical`, a
    kind read off its type (function, constructor, type constructor,
    level, proof, cell, `Matchable`, type, value), which subterm
    parameter it is, whether it is anonymous, the elaborator's own
    binder for a head or an argument, or shadowed by a newer binder of
    its name, and where it was bound (`Env.entry`'s position, ASSUMPTIONS
    195; a built-in or a minted entry says so). Under it: its `is` rule,
    canonical, except an alias of an anonymous entry, which a let
    forwarding a call's result has and which names nothing a reader can
    use; its value where it is a non-erased `Settled` that the final's
    printer can spell (a function or a `Matchable` adds
    nothing to its kind); and for a `unique` binder whether it is live, shared or
    consumed on this path and where, and whether the enclosing `def-fns`
    closes over it.
    Then the at-database as its classes of two or more members a reader
    can name (an entry in scope, a literal by its spelling, or
    `vacant-slot`), one of them an entry the program bound, the opened objects, and the
    numerals a rule has been minted on, as `unary` mints them, since a
    literal is otherwise opaque (DESIGN.md section 45).

    An argument is a term in section 9's grammar, elaborated as a type
    argument is: a variable is shown as its entry, the prelude's
    included, and any other term by what it canonicalizes to and its
    type, so `(dump-context (Cons A hd tl))` asks what a term means where
    the form stands. With any argument the scope listing is left out.

    In `Env.namer`, which `Env.show` and `Env.show_tele` share, an entry
    that is a location's representative is named by its own binder inside
    `slot-of` even where its `is` rule aliases it elsewhere, since a
    `slot-of` argument is read by binder and not through the rule
    (section 35). A message about an entry's own rule names nothing by
    that entry (`show ~except`), or `(let ((many ys)) (share xs))` would
    report `ys is ys`. Whether either misnames something in a message no
    test pins is not checked.

    `slc` carries the form too (`self/README.md`), built the same way
    from its own environment; the messages `slc` writes after the report
    are its usual cascade, the reference stopping at the first error.

    Not decided here, and open for the owner: whether the report should
    also list the prelude's entries on request as a whole rather than one
    by one; and whether the branch-forced facts of an enclosing match
    should be shown apart from the entries' rules, where they appear only
    as `xs is (Cons A hd tl)` on the scrutinee's own line.

197. **How `slc` budgets a `let-match` rewritten to a `match` (DESIGN.md
    section 52).** `slc` gets there through its budget of sugar
    expansions (111): the rewritten `match` is a raw of the elaborator's
    own making, so elaborating it spends one unit, and a body can nest
    such `let-match`es arbitrarily deep. The top level starts the budget
    at the size of the form being elaborated, its count of atoms and
    lists; the session's reading is that no chain of expansions can
    outrun it, each one being spent on a distinct `let-match` in that
    form. The zero case stays an internal error.

## Confining file requests (section 27)

The `ConfinePaths` request, the `--confine-read` and `--confine-write` flags and the fence model are as
MANUAL.md describes them; the choices below are the session's.

198. **What the fence admits, and when.** Each file request resolves
     its path the way the session understands the
     kernel's lookup to go (`Driver_core.resolve`): relative to the
     working directory, following symlinks with `lstat` and `readlink`,
     taking `..` physically, and stopping at the first component that
     cannot be looked up, since the kernel's lookup, as the session
     reads it, cannot get past that component either. `MkDir`,
     `DeleteFile` and `DeleteDir` do not follow a symlink in last position, as their
     syscalls do not, so a symlink at a writable path that points out of
     the fence can be deleted; a trailing `/`, `.` or `..` makes the last
     component followed after all, erring towards refusing. Under `--interpret` slc performs `ConfinePaths` once
     every source is read, with `/` writable when no flag is given, so its own
     reading of its sources is never fenced; a directory the program
     cannot be confined to is reported with slc's `slc: ` prefix there,
     and without it by the reference and by a compiled program. The
     fence belongs to the process rather than to one final, so a
     `ConfinePaths` in one file's `Program` final holds for the finals after it, as it must under `slc --interpret`, which performs them all
     inside one run of its own driver. The check is made before the request and not
     atomically with it, so it is not expected to hold against another
     process changing the directory tree in between, and a hard link
     already inside the fence reaches whatever it links to. When the
     working directory cannot be read, a relative path answers `Fail` with that
     error even unconfined, the one case where the check can change what
     an unconfined program sees.

199. **Counting output against `--confine-output-bytes`.** The choices
     below are the session's; MANUAL.md has the rest. An entry counts as created
     when `Sys.file_exists` is false for its path just before the
     request, which follows symlinks, so a write through a dangling
     symlink is charged for the entry it makes; like the fence (198) the
     check is not atomic with the request. A request that passes the
     check is charged whether or not it then succeeds. The crash exits
     with code 1, the code the driver already exits with when it cannot
     confine itself at startup. Under `--interpret` a flag value that is
     not a number is reported with slc's `slc: ` prefix, as a fence is
     in 198.

## Slots and `at` (DESIGN.md sections 35 to 41), literals and macros

Choices this session made where DESIGN.md does not decide, each a
reading that may be mistaken.

200. **How a slot sits in the fact table.** An entry's automatic slot
     (section 35) is held on the entry (`Env.entry`'s `slot`), not in
     the scope's list of ids. The closed spelling of `(slot-of x)` is a
     term node, `Term.SlotOf`, over a variable or a `Bound`, which is
     what a telescope can hold for one of its own binders (section 35);
     `Env.canon` resolves `(slot-of x)` to `x`'s binder's slot, so after
     canonicalization a slot is an atom. A binder written `at`, a `let`
     binder, a temporary, a cell binder and the rest of section 36's
     writers get a rule on their own slot equating it with the
     target's, minted by forcing. A `res`'s `place` is a slot term,
     `None` only where no binder stands behind the result yet, as far as
     this session traced: a call's return without `at`, a constructor
     application that is not a newtype's, a fresh or copied cell.

202. **What is passed and what is read (section 36).** A match's `at`
     annotation entries, and a `cell-match`'s, are projected away from
     every branch; the match's code gains that projection only when an
     entry is `at`. A result that is not a variable is bound to an
     anonymous entry before the entries after it are checked, so that a
     later entry's `at` can name the slot it sits in (section 15,
     section 36's return at an earlier return).

207. **At-functions and at-matches (sections 39, 40).** Erasing to
     nothing is checked on the code after `Elab.normalize`, with `at`
     entries projected away. A match annotated `_` inside an
     at-function is not an at-match and keeps its code, which the body
     check then covers.

209. **`array-pluck` and `array-unpluck` (section 44).** `array-pluck`'s
     one store, of `(Uninit A (slot-of hd))` into the slot already
     holding `hd`, is written full-at, so the model stores nothing, as
     the FFI's implementation does. The lemma from `SetNth` to `Nth`
     that a caller of `array-unpluck` needs is not in the prelude;
     `std/list.sl` has it as `setnth-nth`, and
     `tests/array_unpluck.sl` proves its own.

211. **Which arguments are bound first (sections 15, 35).** An argument
     bound first because a later entry of the signature names its
     parameter's slot, by `(slot-of p)` or `at p`, is found by
     `Elab.slot_named_params`; the entry is erased when the argument
     is, and its slot is the slot the signature then speaks of. A
     parameter's meta solved from a written variable is placed at that
     variable's slot when the argument is read (`Elab.check_args`,
     `check-args-go`), since the solution a reader sees is canonical and
     does not say which variable was written
     (`tests/slot_of_param_type_ruled.sl`). The `at` check of
     section 36 waits for the call's metas to settle at its closing
     paren, rather than running as each argument is read. A solved meta
     inside `slot-of` resolves to that slot (`Env.metaless`), so no
     `slot-of` over a term survives canonicalization. `dump-context`'s
     slot listing includes erased entries.

212. **Literals outside every scope (sections 5, 18, 45).** Both compilers
    intern a literal where it is first met, from an expression's literal case,
    `numeral-of` and the `intern-*` primitives, with no pass over a
    form ahead of elaborating it. The reference keeps one program-wide
    table (`Env.literal_rows`) from a literal's value to the entries it
    minted, with their values and the Peano ladder, reset with the FFI
    tables; the ids come from a separate half of the id space, the
    negatives, so that the evaluator and the extractor find a literal's
    value by its id alone (`Value.literal_values`, emitted once as
    `l<N>`) and a reference to a literal stays a `CVar`, which section
    15's "not rebound" relies on. The reference drops an inner env
    wholesale on leaving a body or branch, so a scope that meets a
    literal without its entries has them entered again under the same
    ids (`Env.enter`), the closed-telescope builders carry the literals
    their scratch env met into the env that continues (`Env.carry`), and
    diagnostics that walk the literals walk those present in the env
    (`Env.present_literals`), the only ones its terms can mention.
    `slc` has an explicit exit, `env-discard`, which keeps entries,
    store and the key map and enters the declaration facts of the
    literals interned inside into the restored table (`table-reenter`,
    at an id below the table's bound where the position is free), oldest
    first since a character's rule names its code's numeral, so nothing
    is entered again at resolution there. In
    both, a branch may still force a rule onto a literal's id, which the
    scoped table holds and drops with the branch. The introduction order
    of section 5 is a field of the entry: in the reference the entry's
    own id, negative for a literal's; in `slc` a `Maybe Nat`, `None` for
    a literal's. `prove-predates` names the level by its own name when
    it has one and canonically otherwise, since the inferred form's
    level is often the anonymous atom a named `let` canonicalizes to;
    a literal in a name position is refused as "is a literal, not a
    name". `self/bootstrap.sh` checks that the two compilers agree on
    every test.

213. **Macro expansion, where DESIGN.md section 62 is silent.** A
    position a macro gives that names a file other than the one being
    read is covered by no `;! suppress` region in `slc`, which keeps the
    regions of the current file alone; the reference reads the regions
    of the file the position names. `slc`'s elaborator takes a `fuel`
    parameter ahead of its `sugar` budget: an expansion spends one unit
    and elaborates its output with `sugar` reset to the output's size,
    and the run's count of 10000, kept in the environment, is read as
    firing before any path's fuel runs out. A `let-match` in a body has
    its branches spliced once, before it is told apart as a statement or
    a match, in both compilers.

215a. **Handles, where DESIGN.md section 64 is silent.** A handle to a
    literal enters the literal's entries where it is spliced, as the
    literal would, and is refused where a literal is. A
    `delegate`-bodied function that `slc` holds as its callee's value is
    minted at its own entry, not its callee's. A handle's value is the
    id of the entry its `Settled` was minted at, with the multiplicity
    (and the value, as item 216 has it), and `slc` also carries the text
    a message shows it by: a literal's spelling, else the entry's name,
    else `_`. A spliced handle is read wherever a name is read as a
    reference, the heads of special forms and macros included, and an
    erased one dispatches neither; where a binder is read, the message
    is "a handle to `k` is not a name". The reference holds a handle as
    a syntax node of its own, `slc` as a third kind of name, refused by
    the two functions that read binders.

216. **`settled-mult`, `settled-value` and the `intern-` forms, where
    DESIGN.md sections 64 and 65 are silent.** How an `MMany` handle
    carries its value differs between the compilers, and is meant not
    to be observable. The reference holds the value in the handle
    itself, through the reader's tree as well, the `Handle` node of
    `lib/ffi_core.ml` carrying it as an `Obj.t`. `slc`'s handle holds no
    value; its compile-time interpreter reads it by the handle's id from
    the entries of the heap it threads (below). This session's reading
    is that the two agree because nothing seems to mutate a `many` value
    in place (DESIGN.md section 13). `settled-mult` is given the
    prelude's three `Mult` constructors as hidden arguments after its
    handle, so that its evaluation needs no scope. The `intern-` forms
    mint into the program store, and the handle they return splices as
    any handle to a literal does (item 215a). In the reference the
    literal table is program-wide already. In `slc` the macro world
    carries the `Env`, and the evaluator threads a `Heap`, the store
    together with the entries and finals that hold its addresses, in
    place of the bare store, so that an `intern-` form mints into the
    one store the expansion runs against. A spliced handle to a
    character literal enters its code's numeral as well, which the
    character's rule names.

217. **`settled-type` and `settled-eq`, where DESIGN.md sections 64 and
    65 are silent.** `settled-type` of a `MintedType` handle is a
    `MintedIs` handle to the built-in `Type` entry, on this session's
    reading that the type of a type is `Type`, which `(Univ)`
    canonicalizes to as well. It reads the minted type as the fact table
    holds it at the innermost run position. A `MintedType` handle holds
    no value; an extracted program, from either compiler, holds a handle
    as its id, its reading, its multiplicity and its value, the value
    being `()` for a handle that is not `MMany`. Spliced where an
    expression or a type is read, a `MintedType` handle binds an
    anonymous erased entry whose `is` rule is that type and whose type
    is `Type`, and refers to it; where a name is read, it is refused as
    "a handle to `_` is not a name", a `MintedType` handle written raw
    showing as `_`. The message about a handle used at the wrong
    multiplicity shows the term the handle stands for, canonically, in
    both compilers. The literals whose declaration facts `settled-eq`
    enters differ between the compilers and are meant not to be
    observable, a literal's declaration facts rewriting only its own
    entries: the reference enters those of the literals the terms and
    types mention, and of those their facts mention in turn; `slc`
    enters every literal interned so far, into its trusted table
    widened first to the current id bound, which is why its `TrustThen`
    carries that bound at `many`. `slc` passes `settled-eq` the
    prelude's `None` and `(Some (JMRefl))` as hidden arguments after
    its handles, as `settled-mult` gets the `Mult` constructors.

218. **Literals as handles, where DESIGN.md sections 63 to 65 are
    silent.** The conversion of a top-level form's literals into
    handles runs on the forms read from the source alone: the forms a
    macro returns are not walked again, holding no literal node of their
    own. A literal that cannot be interned, for want of the prelude, is
    refused at its own position. Only a `MintedIs` handle at `MMany` to
    a literal's entry counts as that literal, so an `MErased` one made
    by `settled-erase` is refused as a handle where a literal would be.
    `slc` keeps each literal's node in its row of the literal table, and
    reads a handle to a literal back as that node where its elaborator
    tells literals apart by syntax; the reference recognizes the handle
    where it reads a literal instead. The view of `Raw` meets no literal
    node on this session's reading, and fails if it does.

219. **`read-file` and `ReadFileIn`, where DESIGN.md section 65 is
    silent.** A refusal names the path as the macro wrote it and the
    directory as given, not their resolved forms: `../dune: outside the
    directory ../tests`, `missing.txt: No such file or directory`,
    `elsewhere.sl: not a source file or a name given to
    --comptime-unconfine`, `x.sl: no directory ../no-such-dir` for a
    directory that does not exist, and, for `NoPos`, `no position to
    read relative to`, so that a test's expected output does not depend
    on where it runs. A source's directory is the text of its name before
    the last `/`, or `/` where that `/` comes first, or `.` where there is
    none, in both compilers. Both read through the request
    `ReadFileIn dir path`, which `lib/driver_core.ml` performs, checking
    a running program's own fence after the directory. The reference
    keeps each source as its name and the directory it is read from, since `test/runtest.ml` names a test
    `tests/x.sl` and reads it from `../tests`, and each name
    `--comptime-unconfine` gives with the directory derived from it;
    `slc` keeps the names and derives the directories. `slc`'s macro state is indexed by the slot of
    the elaborator's world, which it holds as a `Placed` field (DESIGN.md
    section 66), and `env-expand` unplaces that field and uses
    `placed-slot` after an expansion, so that the world comes back `at` the
    one that went in.

226. **Which calls a message names, where DESIGN.md section 62 is
    silent.** A call's notes read ``in the expansion of `m` here``, `m` as
    the call's head is written, innermost first; a line's call notes
    follow its notes on `__` numbers, and a call already named in the
    message is not named again. A form belongs to the last call that
    returned it: one a call passes through is that call's, whatever call
    returned it before; the statements after a returned `let-match` with
    branches keep the expansion they belong to when DESIGN.md section 52
    moves them into it. A position the elaborators keep for a later
    message, a binder's, a `_` argument's or a unique use's, keeps the
    calls it was met under; the positions in notes on `__` numbers do
    not. The messages about a list as a whole are those about the number
    of arguments of an application, of entries of a `values` or of
    binders of a `let`, a `match` or `let-match` missing a branch, a body
    without a final expression, and a type not of newtype shape; they
    name each call spliced into the list as ``the expansion of `m` here
    gave N forms``, `no forms` and `1 form` for those counts. A call
    spliced into a function's telescope is not named at the function's
    calls. The reference keeps the current expansion in a variable it
    restores on leaving the item that set it; `slc` keeps it in the
    position its environment is at and sets it back after each item.

## The world (section 42)

Choices both implementations make about the world where DESIGN.md is
silent.

214. **`world-do` is a node of its own.**
     `world-do` is a node of the post-erasure code of its own (`CWorldDo`
     in both compilers), evaluated by the driver's `perform` whether or
     not extern implementations run, and extracted to a call of it. A
     request that would take the program's output past its limit stops
     the program with exit code 1 from inside `world-do`. Under
     `--no-prelude` the name `world-do` stays bound, as every special
     form's is, and a use of it is refused for want of the prelude's
     `Request`. The reference's driver takes its `Measure` reading when it
     begins running the final `Program`, before the first step, with no
     compaction.

215b. **How `Measure` orders its own allocation.** The answer to
     `(Measure (Start))` holds the reading, so it cannot be built
     before the reading is taken. The reference's driver builds a
     throwaway answer first, counts the minor words that took, compacts
     the heap, takes the reading, and adds that count to `minor-words`;
     the answer it returns is built after the reading. This relies on
     the second build allocating as many words as the first, which holds
     on the session's reading because both hold the same number of
     `Nat`s and every figure is a small integer; no other figure is
     corrected. Both builds go through one closure hidden from the
     optimizer by `Sys.opaque_identity`, its argument hidden too, so
     that inlining cannot compile them differently, as flambda at `-O3`
     on OCaml 5.5.1 appears to otherwise. `(Measure (Stop))` reads
     `minor-words` as the driver enters `perform`, before the request is
     decoded, and the rest of the figures after it. `slc --interpret`
     passes the constructor through to its own driver and copies the
     answer into its compile-time store after the reading in both
     modes.

220. **Which number a table answers for a slot it holds twice, where
     DESIGN.md section 69 is silent.** A `Slots` can hold one slot more
     than once, built so through `MkSlots` or interned twice after a
     miss. Both compilers answer the number given most recently: the
     reference's table keeps every number in its hash buckets and finds
     the newest first, and slc's `BSlots` keeps one number per heap
     position, overwritten when the position is added again. Either
     answer satisfies the `NthLast` proof the result carries, on the
     session's reading.

221. **An extern type with one constructor, where DESIGN.md section 42
     says nothing of its tag.** `Slots` is the first extern type with a
     single constructor, so it is untagged (section 33), and the FFI's
     shape check in both compilers, which had required every extern
     type's shape to be tagged, now accepts an untagged one of one
     constructor. Extraction and slc's output still lay its view out as
     a one-constructor variant, which the session reads as representing
     it the same way.

222. **The result type of an extern function, read in slc from its first
     stored return.** slc finds the plain type an extern implementation
     builds, whose shape it checks, by reading one return of the model.
     It read the first return, which for `slots-intern` is the erased
     list; it now reads the first return that is neither erased nor
     written `at`, which for every earlier extern is the same return.
     The reference checks such types by name and reads no return.

## The `goal` and `qed` forms and `--goal`

225. **The goal is shown as the scope where it is set spells it.** The
     note on the goal points at the `goal` form, so its keyword, multiplicity and
     type are written as a message about that place writes them, even
     when a later binder shadows a name the type mentions.

