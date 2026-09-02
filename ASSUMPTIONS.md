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
   other than whitespace, parens and `;`. Digit-only atoms and `#\c`
   atoms are numeral and character literals (items 51-52); there are no
   string literals (SR 10).
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
   neither be matched on nor count as empty (SR 6). On top of that a
   source prelude (`lib/prelude.sl`, section 41) defines `Nat`, `False`,
   `Lt`, `Double`, `Pow2`, `Dec`, `U8`, `Bin`, `Numeral`, `Char`,
   `String`, their functions, and the levels `nat-lvl`, `pow-lvl`,
   `mod-lvl`, `u8-lvl`, `bin-lvl`, `str-lvl`, all as ordinary,
   shadowable entries, and since item 58 also `Unit`, `Maybe`,
   `Result`, `List` and `IO`; a user function calling `nat-add` proves
   `(prove-predates nat-lvl L)`. The examples still define their own
   `List`, shadowing the prelude's (SR 12).
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
    constructor name. A union newtype's other non-phantom constructors
    build the token. Marking changes nothing at runtime here: an
    unmarked type of newtype shape is represented as its field too, it
    just gets no `coercible-wrap`.
35. **An absurd function's code raises** if ever reached; a match whose
    real branches are all absurd or phantom likewise compiles to code
    that raises.

## Not implemented

36. Macros (`Macro`, `Raw`, the expansion limit). `lib/kernel_input.ml`
    is untouched and unused (SR 28). The `--repl` flag reads one form
    at a time and prints every expression's value, which goes beyond
    section 16's one-expression file; it is a convenience only.

## Extern types and the FFI (section 41)

42. **The FFI is a fixed OCaml table** (`lib/ffi.ml`) keyed by name:
    an `extern`-marked type or function looks its implementation up by
    its declared name at elaboration and fails if there is none, so a
    second `extern` declaration of a name already bound in the program
    is a hard error (settled by the owner). Section 41 leaves the
    source-level declaration open; this is the prototype's stand-in.
    The prelude itself is `lib/prelude.sl`, embedded into the binary by
    a dune rule so the interpreter needs no path to it at runtime.
43. **Extern payloads.** Values of an extern type are zarith integers
    (`Nat`, `U8`, `Bin`) or byte-string slices (`String`, item 48)
    carrying their type's runtime record; an extern type's
    implementation is a pair construct/destruct over constructor
    indices, so matching, `comptime-match` and printing all go through
    destruct and see the model's constructors. `U8`'s destruct yields
    its `Nat` field as a `Nat` integer, the erased proof field taking no
    slot. An untagged extern value prints as its fields, the way a
    transparent value does, so a `U8` prints the same with and without
    the FFI.
44. **`--no-extern` strips every implementation** and runs the models
    instead; `dune test` runs every test both ways and requires the
    same outcome, which is how section 41's invariant is checked. The
    prelude is re-elaborated per mode.
45. **`Newtype` has no ambiguity case**: `(Newtype T)` carries nothing
    but `T`, so `newtype-of` and `coercible-wrap` take the first one
    found in scope. `coercible-wrap` still requires the named
    constructor to have exactly one `many` field, the only check left
    after trusting the mark.
46. **The prelude's proofs are erased fields and erased functions**:
    `Lt`, `Double` and `Pow2` carry their sub-proofs at `erased`, and
    the lemmas `lt-pos` and `double-pos` are `erased` functions, so no
    proof is ever built at runtime; `lt-dec` returns a `Dec` whose
    proof field is erased. A choice of the session, not the owner's.

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

## Strings, literals, and the driver (sections 16 and 41)

Written by a session working autonomously overnight at the owner's
request ("make reasonable guesses when necessary and append them to the
assumption file"). The owner's direction in chat was: a `String ->
String` final expression run over stdin, strings held as slices of an
ASCII byte array with a `trim` that copies, no extra erased arguments on
that function for now, numerals as an opaque `Nat` related by a prelude
relation to a non-opaque binary spelling computed by a prelude function,
`Char` as a newtype over `U8`, and a form retrieving the relation.
Everything below that goes further is a guess, and DESIGN.md sections 16
and 41 still record the consumer of the top-level value and numeric
literals as open.

47. **The driver runs a final value as a program when its type is an
    `Fn`, at any level, from one `many (String)` parameter, `subterm` or
    not, to one `many (String)` return** (`lib/program.ml`): stdin is read whole into a
    `String`, the function applied, and the result written to stdout
    verbatim, with no newline added. Any other final value is printed
    as before, so the existing tests are unchanged. A `; stdin: text`
    directive in a test supplies the input, its lines joined by
    newlines with no trailing one.

48. **`String` is an extern enum modelled as a cons list of `Char`**
    (`SNil`, `SCons`), not marked `newtype`. The FFI holds a value as a
    slice of an OCaml string (offset and length); destructing an
    `SCons` yields the byte and the tail slice over the same buffer, so
    matching is structural and copies nothing, and same-level recursion
    over a string is discharged by an ordinary `subterm` proof.
    Constructing an `SCons` copies. `trim` is extern with the identity
    as its model: its whole content is the copy that lets the rest of a
    shared buffer be collected. `str-append` is plain source at
    `str-lvl`. The alternative reading of "slice", an ADT holding a
    buffer, a start and a length with erased bounds proofs, was not
    taken: section 5 forbids a length function in a type, so every bound
    would be a relation, and iteration would need a `Nat` fuel rather
    than structural recursion.

49. **`Char` is a source `newtype` over `U8`**, not extern, so a `Char`
    at runtime is the `U8`'s integer and the slice's destruct hands the
    byte back directly. Any byte is a `Char`; section 28's ASCII rule is
    about the language's syntax, not its data.

50. **`Bin` is bijective base 2**: `(BZ)`, `(B1 b)` meaning 2b+1 and
    `(B2 b)` meaning 2b+2, least significant digit outermost, so every
    number has exactly one spelling. Uniqueness is what lets the FFI's
    destruct of a zarith integer agree with the model on the head
    constructor; a plain bit list has trailing zeros and would break
    section 41's invariant. `Numeral : ((Bin) b) ((Nat) n) -> Type`
    has one constructor per digit, each carrying an erased sub-proof and
    an erased `Double` from the prelude; `bin-to-nat` is extern (the
    identity on zarith) over a structural model returning the number
    and the proof, in `pow2`'s shape. Coq's `positive`/`N` pair was the
    alternative. All names are the session's.

51. **A numeral is a digit-only atom and never a name** (`Env.bind`
    refuses one; leading zeros are rejected outright). It is sugar for
    `(let (many _) (erased _) (bin-to-nat <spelling>))` hoisted to just
    before the top-level form that first mentions it, run in run
    position, and interned per program by value, so every occurrence is
    one entry: the `Nat` is opaque, a call's result with no `is` rule,
    and the erased `Numeral` proof relates it to the spelling. The
    hoisted statements are elaborated in the prelude's own scope
    (`Env.prelude`, `Elab.hoist`), so user shadowing of `let` or
    `bin-to-nat` cannot reach them, and the born entries are not in the
    scope list at all; resolution goes through `Env.literals`. Sound
    because the statement depends on nothing but the prelude and the top
    level calls freely (section 24). Consequence to note: a literal is
    never unary-known. Using `3` where a `(Vec A n)` index is needed
    means unfolding its `Numeral` proof by erased matches
    (`tests/numeral.sl`, six nested matches), reasoning relationally, or
    indexing by `Bin` instead; `(Vec A 3)` is not `(Vec A (Succ (Succ
    (Succ (Zero)))))`.

52. **Character literals** are `#\c` for a printable ASCII `c`,
    `#\space`, `#\newline`, `#\tab` and `#\xHH`; Scheme's spelling was
    chosen over `'c'` to leave the quote free for a future `Raw`. One is
    sugar for its code's numeral followed by section 41's reflection
    route, `(let (many %d) (lt-dec n u8-modulus))`,
    `(comptime-match %d (Yes %a %b %p))` and
    `(let (many _) (MkChar (MkU8 n %p)))`, hoisted and interned the
    same way, the `%`-names living only in the discarded frame. The
    state-inheriting `let` makes the literal `is (MkChar (MkU8 n p))`,
    transparent down to its opaque `Nat` (`tests/char.sl`), so no
    separate relation for characters is needed.

53. **`(numeral-of e)`** takes any expression that canonicalizes to a
    literal's value entry, a numeral itself or a variable a match or
    `comptime-match` has forced equal to one, and yields that literal's
    erased `Numeral` proof; a character literal's entry yields its
    code's proof. It reads `Env.literals` rather than searching the
    scope, unlike `coercible-of`. The owner suggested `nat-of`; the
    session renamed it because the form yields a proof, not a number.

54. **Resource limits under `--no-extern`.** Stripped, `bin-to-nat`'s
    model runs `double` in unary, and `Value.show` prints a `Nat` in
    unary, so a numeral around a million overflows the interpreter's
    stack in either mode when printed and in the stripped mode when
    merely computed. Section 41's invariant holds up to resources; the
    tests keep their numerals small.

55. **Location-free errors** (the literal-as-name check lives in
    `Env.bind`, which has no line) are reported at the enclosing
    top-level form's line.

## IO programs (section 16)

Asked for by the owner in chat: an ADT read by the driver, "quasi
monad", efficient, able to read a whole file by name, write a whole
string to a file, write to stdout or stderr with a flush, read a line
from stdin, read the command-line arguments and exit with a code, kept
alongside the `String -> String` form as an optional alternative. The
shape below is the session's.

56. **`IO` is a source enum in the prelude, indexed by a level**:
    `(IO L)`. Each constructor carries what happens next, either the
    next `(IO L)` value outright (`WriteOut`, `WriteErr`, whose effects
    have no answer) or a continuation `(Fn L (many answer) -> (many
    (IO L) next))` the driver applies to the request's answer
    (`ReadLine` with `(Maybe (String))`, `ReadFile` with `(Result
    (String))`, `WriteFile` with `(Result (Unit))`, `GetArgs` with
    `(List (String))`); `Exit` carries a `U8`. The driver
    (`Program.run_io`) loops: destruct, perform, apply, repeat, flushing
    after every write. No step recurses, so an unbounded interaction is
    the driver's loop over a total function that returns a node holding
    itself as the continuation, which is why nothing coinductive is
    needed and why there is no `bind`: composing two `IO` values would
    need a lambda and a recursion the termination discipline cannot
    admit. Not extern, since the FFI never sees it; the driver reads it
    through the prelude's constructors.

57. **The level index is load-bearing.** A continuation's `Fn` type
    names the level its function was defined at, and `subterm` marks
    are part of an `Fn` type, so a recursive helper cannot itself be a
    continuation and a same-level wrapper cannot call it. The pattern
    the tests use (`tests/io_file_args.sl`): the helper sits at a level
    below the IO level, is defined after that level and its functions
    exist, and references those functions only as values, while a
    continuation at the IO level calls the helper with a `Predates`
    proof. A cost of the design, recorded rather than smoothed over.

58. **`Unit`, `Maybe`, `Result` and `List` join the prelude**, `List`
    exactly as section 31 defines it, so a program that defines its own
    (every `; needs: list` test) shadows the prelude's; that changes
    item 4's remark that `List` is not built in. `Result`'s failure
    carries a `String` message, the operating system's for a file that
    cannot be read or written.

59. **Program arguments** are what follows `--` on the interpreter's
    command line; `; args: a b` supplies them to a test, `; stderr:
    text` lines are what it must write to stderr and `; exit: n` the
    code it must exit with (0 when absent). `ReadLine` strips the
    newline and answers `None` at end of input; the whole-stdin
    `String -> String` form is unchanged.

60. **String literals** `"..."` were added for the IO tests' paths and
    messages: the reader accepts `\n`, `\t`, `\"` and `\\`, and a literal
    is sugar for its characters consed up with `SCons`, each a
    character literal hoisted first, so it is `is`-transparent like a
    character literal (`tests/string_literal.sl`). Interned by content.
    The hoisted `let` builds the value by consing, quadratic under the
    FFI, which only matters for very long literals.

## OCaml extraction (extract.ml)

Written by a session working autonomously at the owner's request, in
chat: extraction "in the sense of Coq's extraction", with compile-time
computation embedded in the extracted OCaml as its result rather than
recomputed, since compile-time calculation is meant as a performance
construct (the owner's words, paraphrased). Everything below is that
session's reading; the representation choices in particular are
Claude's and may be wrong, though `dune test` checks them on every test
in both modes.

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
    are the values captured at closure time, embedded the same way, and
    closures that reach one another through their environments land in
    one `let rec` group, so mutual recursion survives. A constant met
    inside such a group is named and placed before the group when it is
    closure-free, and written inline in the body when it holds a
    closure, since that closure joins the open group and a name placed
    before the group could not see it; `tests/io_closure_in_data.sl`
    reaches this through a factory parameter, the only way to, since a
    top-level constant a closure mentions is already named while its
    factory's body is written. A top-level `def-fns` function met as a value refers to
    its `let rec` name. The final expression's value is embedded too,
    being computed at elaboration like any run-position expression; so
    a printed final value is printed from data, a `String -> String`
    program is its `main` closure applied to stdin, and an `IO` program
    is its first request, whose continuations are closures.
62. **Every extracted value is an `Obj.t`**, with `Obj.repr`/`Obj.obj`
    at every construction, application and pattern, the way Coq's
    extraction reaches for `Obj.magic`. A typed extraction was not
    attempted: dependent indices, existential erased fields, first-class
    `Matchable`s and level polymorphism have no direct OCaml types, and
    section 38's zero-cost `coerce` between distinct types would need
    the same escape anyway. The runtime shape is section 38's: an ADT is
    an OCaml type, a variant when the interpreter tags it (every
    constructor listed, phantom ones included, with one `Obj.t` per
    `many` field) and otherwise an abbreviation for its one non-phantom
    constructor's field tuple (`unit`, `Obj.t`, or `Obj.t * ...`; a
    union, whose constructors may differ in arity, is `Obj.t`); a value
    of such a type is that tuple, one field bare and none `()`, exactly
    as `Value.tuple` has it, so `coerce` is the identity and a newtype
    is its field. An extern type under the FFI is `Z.t` or
    `Ffi_core.slice`. Several return values are an OCaml tuple boxed as
    one `Obj.t`; a function with no `many` parameter takes `()`. Names
    are `v<id>_<name>`, `C<id>_<name>`, `t<n>_<name>` and
    `cl<n>_<name>`, the id being the entry's, so shadowed names stay
    distinct; the source names come from a table `Env.bind` fills
    (`Env.names`).
63. **Each type gets a construct/destruct pair** (`con_n`, `des_n`),
    over constructor index and `Obj.t` field list, mirroring
    `Value.construct`/`destruct`: for a variant an OCaml constructor
    application and match, for an untagged type the tuple, for an
    extern type the pair `lib/ffi_core.ml` returns. A first-class
    constructor value is a descriptor record `{ ix; cname; con; des }`
    over that pair. So that the extractor can tell a constructor
    application from a call, the elaborator now marks one with the call
    kind `Value.Ctor` in the post-erasure code (the interpreter ignores
    the mark, dispatching on the value as before). A match whose
    constructors are statically known compiles to an OCaml `match` (or a
    `let` on an untagged type); one through first-class constructors
    (`tests/first_class.sl`) destructs through the first branch's
    descriptor and compares indices, as `Eval` does. Unmatched
    constructors fall through to `absurd ()`, unreachable by the
    elaborator's checks.
64. **The FFI is shared by embedding.** `lib/ffi_core.ml` holds the
    implementations over raw zarith integers and slices, generic in the
    value type through injection/projection arguments; `ffi.ml`
    instantiates them with `Value` constructors and a dune rule embeds
    the file's text into the interpreter (`Ffi_core_source`), which the
    extractor pastes into every output as `module Ffi_core`, instantiated
    with `Obj.repr`/`Obj.obj`. An extern function extracts to a wrapper
    around `Ffi_core.<name with - as _>` of the same arity; under
    `--no-extern` the extern types are ordinary variants and the extern
    functions' compiled models are extracted instead, so section 41's
    invariant is checked on the extracted programs too. `Value.payload`'s
    `Slice` now carries `Ffi_core.slice`. An embedded extern integer is
    `Z.of_string` of its decimal spelling; an embedded string is a
    literal. Without the FFI a large embedded numeral is that many
    nested constructor applications, which the OCaml compiler may refuse
    at some depth, a limit in the spirit of item 54.
65. **The driver is `program.ml` transliterated** over descriptors of the
    prelude's constructors, dispatching `IO` requests by constructor
    name as `run_io` does, flushing after every write, taking the
    program's arguments after `--`, and exiting with the `U8` counted in
    unary through destruct as `Program.u8` does. Under the FFI stdin is
    turned into a slice directly, as `Ffi.str` does; without it, into a
    cons list. An `absurd` reached at runtime prints `runtime error:
    absurd code reached` to stderr and exits 1, without the file name
    `bin/main.ml` would print. Every final expression of every file on
    the command line is consumed in order, as the interpreter would;
    `--extract` stops the interpreter from running the final values
    itself (elaboration still evaluates them, the language being pure).
66. **A printed final value goes through a generated printer**, since
    an extracted value does not know its constructor names: for the
    final expression's type, each constructor's return type is unified
    with it (as entering a match branch does) to find the `many` fields'
    types, and one printer per type is emitted, following `Value.show`:
    constructor and fields for a tagged value, the bare fields for an
    untagged one. Printing the interpreter's own rendering as a string
    literal would have been simpler and exact, but the printer applied to
    the embedded data is what checks the embedding. Limits, honestly: a
    closure prints as `<function ?>` unless the final value is itself a
    closure (`tests/absurd.sl`), since OCaml closures carry no name; a
    field whose type stays unknown (an existential) prints `?`; an
    untagged union whose index is not forced prints through its first
    candidate constructor. No test hits these.
67. **Testing.** For every test that runs (71 of 118; those expecting an
    error need no extraction) and each extern mode, `test/runtest.ml`
    extracts the elaborated program, drops the final expressions of the
    `needs:` files from the trace (the interpreter runner discards their
    output too), compiles with `ocamlfind ocamlopt -package zarith
    -linkpkg` into `_build/default/test/extract/`, runs the binary with
    the test's stdin and arguments, and requires the directives' stdout,
    stderr and exit code. A missing `ocamlfind` fails those tests rather
    than skipping them. The suite takes about thirty seconds. Every
    test passes in both modes. What that shows, precisely: since final
    values are embedded, a test printing a value checks the embedding of
    data and closures and the printer, while only the `String ->
    String` and `IO` tests run extracted function bodies (the others'
    bodies are compiled by OCaml but never called). An earlier revision
    of the extractor, in this branch's history, recomputed every
    constant and passed the same suite, which is the evidence the code
    generator has for the remaining bodies.
