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
2. **`_` as a binder name** mints an anonymous entry, wherever a binder
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
    not only a `def-lvl`-minted one; only `prove-predates` insists on the
    mint marker, after canonicalizing the level. Its subject stays the
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
    about the function found in scope, so an anonymous proof minted later
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
    canonical when minted with re-canonicalization on every new rule (SR
    21); occurs checks on the canonical form keep the rules acyclic.
29. **Facts minted inside a `let`'s right-hand side persist past it** unless
    they mention entries that went out of scope; only match branches
    restore the fact table on exit. The design's "a fact ends with the
    scope it was minted in" is not enforced for right-hand sides. The
    facts in question come from `comptime-match` verifications in a
    run-position right-hand side, which are unconditionally true, so
    this looked harmless.
30. **Nested definitions mint `Dyn`**, as section 34 says: a
    `def-adts`, `def-lvl` or delegate proof inside a body mints `Dyn`
    entries, and the body's code binds each nested constructor's value.
    In run position the same mints are `Const`, and the values of
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

36. Macros (`Macro`, `Raw`, the expansion limit). The `--repl` flag reads one form
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
45. **`Newtype` has no ambiguity case**: `(Newtype C)` carries nothing
    but `C`, so `newtype-of` and `coercible-wrap` take the first one
    found in scope; the mark having named `C` is what makes `C` the
    wrapper, the only check left after trusting the mark.
46. **The prelude's proofs are erased fields and erased functions**:
    `Lt`, `Double` and `Pow2` carry their sub-proofs at `erased`, and
    the lemmas `lt-pos` and `double-pos` are `erased` functions, so no
    proof is ever built at runtime; `lt-dec` returns a `Dec` whose
    proof field is erased. A choice of the session, not the owner's.

## Sugar (SUGAR.md)

37. All four forms are implemented as SUGAR.md describes them: `_` as
    a `def-fns` level mints an anonymous level; `_` as a match
    annotation reuses the telescope of the enclosing function body or
    match branch, and is an error elsewhere; `(predates _)` proves
    `Predates` between the callee's level, which must canonicalize to a
    variable, and the current level; `(subterm _)` proves `Subterm`
    between the annotated argument and the enclosing subterm parameter
    at the same subterm index. All naive, as SUGAR.md says.
    The telescope `_` reuses from a function body is the return
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
    against any value and minted `F`'s erased fields as `Const` tokens
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
    older. Constructors and type constructors are `rigid` (minted so in
    the prelude and by `def-adts`), and two distinct rigid atoms
    unifying is §18's second contradiction. The prior orientation went
    purely by entry id, so a `def-adts`-minted constructor whose id
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
    phantom branch counts as unreachable only under a `many` scrutinee; under
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
    `bin-to-nat` cannot reach them, and the minted entries are not in the
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
    state-forwarding `let` makes the literal `is (MkChar (MkU8 n p))`,
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
    The index does not confine a program to one level, though:
    `tests/io_lift.sl` embeds values from two levels in a program at a
    third by coercion, at no runtime cost, and `tests/io_lift_runtime.sl`
    does the same by rewrapping each continuation; neither is in the
    prelude, their usefulness being an open question.

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
    captured values are named per value (`tests/io_factory_twice.sl`,
    which caught the id-keyed version giving both closures the last
    value). A top-level `def-fns` function met as a value refers to
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
    cons list. An `absurd` reached at runtime prints `<file>: runtime
    error: absurd code reached` to stderr and exits 1, the file being
    the one whose final expression is running, as `bin/main.ml` prints
    it (`-` for stdin; the test runner passes no file). Every final
    expression of every file on the command line is consumed in order,
    as the interpreter would;
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
67. **Testing.** For every test that runs (80 of 127; those expecting an
    error need no extraction) and each extern mode, `test/runtest.ml`
    extracts the elaborated program, drops the final expressions of the
    `needs:` files from the trace (the interpreter runner discards their
    output too), compiles with `ocamlfind ocamlopt -package zarith
    -linkpkg` into `_build/default/test/extract/`, runs the binary with
    the test's stdin and arguments, and requires the directives' stdout,
    stderr and exit code. A missing `ocamlfind` fails those tests rather
    than skipping them. The suite takes about thirty seconds. Every
    test passes in both modes. What that shows, precisely: since final
    values are embedded, a test printing a plain value checks the
    embedding of data and closures and the printer, while the `String
    -> String`, `IO` and final-function tests (item 68; the
    `tests/thunk_*.sl` files cover tagged, untagged, union, extern,
    first-class and nested types, coerce, factory closures and shared
    data) run extracted function bodies over embedded constants.
68. **A final function from no arguments is applied and its result
    printed** (the owner's decision, in chat, so that a program can ask
    for its final value to be computed by code): the driver treats a
    final value of type `(Fn L -> (many T v))`, no parameters and
    exactly one `many` return, as such a request, both in the
    interpreter and extracted, where it is the form whose code runs at
    startup. A function with erased returns besides the one `many`
    return, or with erased parameters, is not accepted as this form;
    whether it should be is open. `Value.show` prints the result as it
    would any value, so a function from no arguments can no longer be
    printed as `<function name>`.

## A second soundness review

69. **Two `def-lvl` levels may unify, and that is left as it was.** A
    session asked to look for soundness issues probed the checker with a
    type indexed by a level, `(Foo : ((Level) L) -> Type)` with one
    constructor returning `(Foo P)`. Matching a `(Foo Q)` against it
    unifies `Q` with `P`, both being ordinary non-rigid entries, and
    inside the branch a `Q`-level body may call an `R`-level function
    minted after `Q` under the proof `(Predates R P)`. The branch is uninhabited,
    `(Foo Q)` having no values at any multiplicity, and no run or proof
    of `False` was found to follow. The session first made level-mint
    entries rigid so that the branch was refuted, then reverted that:
    it was a semantic change the owner had not approved, and it closed
    nothing reachable. (A rationale the session offered in between, that
    refuting on two levels differing would break section 23 because the
    stripped program may represent `Level` as `Unit`, was wrong: the
    stripped program keeps `P` and `Q` as distinct entries, and
    canonicalization compares entries, not runtime bytes.) Whether
    `def-lvl` levels should be rigid is open: for it, two mints are
    distinct constants, so the refutation is true and it forces the
    honest `(absurd C)`; against it, section 18 states the atom rule
    for every non-constructor atom and item 40 extended rigidity to
    constructors only. The load bearing part is elsewhere:
    `prove-predates` demands strict mint order and the three axioms
    keep a proof's subject older than its level, so no `(Predates Z Z)`
    could be built, which is what keeps a diagonal `(MkBar K) : (Bar K
    K)` forcing two level parameters equal from licensing a same-level
    call that could ever run. Open for the owner: whether that
    irreflexivity deserves a stated invariant.
    The same session tried, and the checker rejected: a Curry-style
    negative type whose stored function is applied to the value holding
    it; a function at an older level, defined later, calling a newer
    level; a forged erased proof field under `coercible-ctor`; and
    deriving `False` from a user relation's phantom constructor. An
    erased data field may change under `coercible-ctor` (a `(MkBox
    (Zero) n)` to a `(MkBox (Succ (Zero)) n)`), which the session read as
    harmless, the field carrying nothing at runtime and its replacement
    being typed.

## Three fixes from a bug-hunting session

A session asked to look for bugs, soundness ones especially, reported
its findings in chat; the owner picked three to fix and settled how the
first of them should be fixed. Items 70-72 record the changes and item
73 the one finding left open at the time, settled by the owner in a
later session.

70. **A `ValCtor`'s return is a type-constructor application.** The
    owner's decision, in chat: the former may not be invoked with a bare
    return type. `def-adts` already required each constructor's return
    to be an application of the type constructor it is declared under
    (section 12), but the first-class former (section 29) accepted a
    return of any type-sorted expression, a bare type variable included,
    as in `(ValCtor (many (Nat) n) -> A)` for a parameter `A`. Such a
    type has no `Matchable` to be found, and `coercible-ctor` over a
    constructor of one crashed the elaborator on an assertion rather
    than reporting an error. `elab_valctor` now checks that the return
    canonicalizes to an application whose head is a type constructor,
    which is where both spellings pass.

71. **A `tail` or `delegate` mark applies to a call and nothing else.**
    The marks set the calling convention of the call they wrap, so a
    mark on a constructor application, a `values` or a `match` had no
    effect at all and was silently accepted, `(tail (Succ n))` among
    them; only a later `coercible-of` revealed that `def-fns` had
    minted no proof. Both forms now reject anything whose compiled code
    is not the marked call. This looks like plugging an implementation
    gap rather than a design choice: section 9 describes both marks as
    claims about a call.

72. **A `let` that returns exactly what it binds is replaced by its
    right-hand side.** Section 9 counts a call as `tail` when its
    returns are bound by a `let` and repackaged in a `values` in the
    same order, and requires a hard compile error where the compiler
    cannot honor a mark. The check honored that reading, but the code
    did not: the `let` persisted into the compiled body, so the call ran
    with the `let`'s continuation still on the stack, in the
    interpreter and in the extracted OCaml alike. A recursion of that
    shape 200000 deep overflowed an 8MB stack in both, while the same
    recursion written as a direct `(tail ...)` ran in constant space.
    `check_marks` already normalized the code to read the marks through
    renaming `let`s; it now also drops a `let` whose body returns
    exactly its binders, and returns the normalized code as the
    function's body, so both readings agree. Believed
    semantics-preserving, the two forms producing the same values in the
    same order, and applied to every compiled body rather than only to
    marked ones, which keeps one path instead of two. The depth check
    above was run by hand: `tests/tail_values.sl` covers the form at a
    depth the test suite can also extract and compile, since embedding a
    Peano numeral that large in the extracted OCaml (section 41's
    stripped mode) is not something extraction handles quickly.

73. **Unifying a free variable with a telescope binder refutes the
    branch.** The guard meant to catch the clash did not: `has_dangling`
    started its fold at the depth being compared and counted a `Bound k`
    as dangling only when `k >= d`, so it flagged only an index escaping
    the whole pair of terms, which `refine` never produces, and never
    one bound by the telescope under comparison; unification recorded
    the rule instead. A type indexed by a function type is enough to
    reach it:

    ```scheme
    (def-lvl L)
    (def-adts
      (Tag : (Type A) -> Type
        enum
        (many MkTag : -> (Tag (Fn L (many (Nat) x) -> (many x is y))))))
    (def-lvl M)
    (def-fns M $ many probe : (erased (Nat) k)
        (many (Tag (Fn L (many (Nat) x) -> (many k is y))) t) -> (many (Nat) r)
      (match many t (((Nat) r))
        ((MkTag) (Zero))))
    ```

    `MkTag`'s index is the type of functions returning their own
    argument, the scrutinee's the type of functions returning the outer
    `k`, so entering the branch equated `k` with `x`, a binder of the
    `Fn` telescope. The branch was accepted as live; a body of `k` there
    reported `erased value #0 : (Nat) used in a non-erased position`,
    printing the dangling index the fact table held, and `(absurd
    MkTag)` was rejected as not refuted. A call such as `(probe (Zero)
    (MkTag))` was separately and correctly refused, both sides being
    closed there, so what was reachable was the wrong fact, not a proof
    of anything false.

    The owner's decision, in a later session: the clash refutes the
    branch, section 18's third way for a forced unification to fail. The
    guard now asks whether the term is closed, the same fold from depth
    zero, and a hit raises the contradiction that a `Bound` against a
    constructor already raised through the structural mismatch, which
    left `unify` with no use for a depth at all. The reasoning put to
    the owner, who agreed: a rule maps a variable to a closed term and
    canonicalizing a closed term keeps it closed, so no rule could make
    the two types identical under section 5, and refuting the
    free-variable case is the universal closure of what the closed case
    already did for each particular `k`; coercion does not reach the
    branch either, `coercible-ctor` retyping a value only to the
    constructor's return at other closed field values. Believed sound
    under section 5's identity, and by the same reading it holds for a
    unit-like index type, which is where the owner's Lean demo marks the
    boundary, since whether a binder occurrence and a closed term may be
    identified is a property of the indexed type rather than a
    structural fact about binders:

    ```lean
    -- Structure: gets definitional eta, so `b` and `MyUnit.mk` are defeq.
    structure SUnit where
    inductive SBox : SUnit → Type | mk : (u : SUnit) → SBox u

    example : ((b : SUnit) → SBox b) = ((b : SUnit) → SBox {}) := rfl  -- ✓

    -- Inductive: no eta. `b` is a variable, `IUnit.tt` is a constructor.
    inductive IUnit | tt
    inductive IBox : IUnit → Type | mk : (u : IUnit) → IBox u

    example : ((b : IUnit) → IBox b) = ((b : IUnit) → IBox .tt) := rfl  -- ✗ fails
    ```

    Under eta the two families agree, so refuting on the clash alone
    would refute something true there; section 5 states no eta rule, so
    here they are distinct types that no value shares. This session did
    not run the Lean; it is recorded as the owner wrote it. Should an eta
    rule ever be wanted, one place it could live is `canon`,
    eta-normalizing binder occurrences at such a type before comparison,
    which would turn the equation into a solvable `k` against `(MkU)` and
    leave the refutation as is; not designed. Section 42 records the
    owner's wider open question, a rewriting engine without the atom
    requirement, which could revisit the decision.
    `tests/binder_clash.sl` and `tests/binder_clash_bad.sl` cover the
    dismissed and the written branch.

## Three fixes from a second bug-hunting session

A session asked to look for bugs, soundness ones especially, probed the
checker and the compiled-code path. Items 74-76 record what it changed.
As elsewhere in this file, each is the implementation's reading offered
as a candidate question, not a settled decision; item 75 in particular
changes which programs are accepted and wants the owner's word. Where a
claim could be checked by compiling (CLAUDE.md rule 2) it was.

74. **A renaming `let` that is resolved away is substituted into nested
    function bodies too.** Item 72 has `check_marks` normalize every
    compiled body, replacing a `let` that only renames by its right-hand
    side. The substitution was applied through the body's own shape but
    not into the bodies of a nested `def-fns`: `Value.map_code`, which
    the normalizer walked with, deliberately does not descend into them,
    which is what keeps item 71's `tail`/`delegate` marks judged per
    function (commit "Judge tail and delegate marks per function"). A
    nested function closing over such a binder was then left referencing
    an id that nothing bound any more -- the interpreter raised `unbound
    at runtime` and the extracted OCaml named a variable that does not
    exist. Reached by a nested `def-fns` whose body mentions a binder of
    an enclosing `(let (many k) n)`, or of a `let` whose right-hand side
    is a `values` of plain variables. The normalizer now rewrites nested
    bodies as well; the mark scoping is untouched. Believed
    semantics-preserving, the binder and its right-hand side denoting the
    same value. `tests/nested_capture.sl`.

75. **A call's same-level test reads both levels canonically.** Section
    9 splits a call by whether the callee's level is the current one,
    and section 5's identity is canonicalize-then-compare. The test
    canonicalized the callee's level but compared it against the current
    level's bare variable, while the `Predates` check on the next line
    canonicalizes both sides. So a fact equating the enclosing function's
    own level with an older one -- which a match branch can force where a
    constructor's return names that older level, ASSUMPTIONS 69's
    situation -- made the function's *same-level self-call* read as a
    lower-level call, dischargeable by the ordinary `Predates` proof
    between the two levels and needing no `Subterm` decrease at all. That
    is unrestricted same-level recursion, which is exactly
    `tests/lt_subterm.sl`'s `loop`: the checker accepted an `erased`
    function whose one branch is that self-call and whose declared return
    is `(erased (False) f)`, so a caller able to reach it would bind a
    `False` token and section 10 would be gone. The session
    did not find a way to run one, agreeing with item 69: the branch
    forcing the equation is headed by a constructor whose return puts one
    variable in two index positions, so its values are diagonal, and
    `coercible-ctor` retargets an index only through an erased field,
    which is exactly the case where no equation is forced. So what was
    reachable appears to be an accepted call rather than a live loop.
    Both sides are now read canonically, which makes the call same-level
    and demands the `(subterm p)` it cannot supply
    (`tests/level_alias_bad.sl`). Open for the owner: this is the one
    change here that alters which programs are accepted, and the
    alternative -- reading the current level literally, so that the
    branch keeps its recursion -- is the behavior that was there before.

76. **`numeral-of` on a string literal is an error.** Item 51's literals
    table holds a value entry and a proof entry per literal; a string
    literal (item 60) has no `Numeral` proof, and the table stored its
    value entry in both slots. `(numeral-of "ab")` therefore yielded the
    string itself -- a `many` value of type `(String)`, where item 53 has
    the form yield an erased proof. Nothing false follows, the value
    being honestly typed, but the form did not do what it says. It is now
    an error (`tests/numeral_of_string_bad.sl`). Whether a string literal
    should instead relate to something -- a length, or its characters'
    numerals -- is open; nothing in DESIGN.md asks for it.

77. **An erased `def-fns` leaves nothing in the post-erasure code.** A
    `def-fns` under a function body or match branch compiled to a
    `CLetRec` binding every function of the block, an `erased` one
    included, whose own body is already nothing -- item 32's rule applied
    to the block's functions but not to the block itself. Section 20 has
    an erased function only ever held or called at multiplicity `erased`,
    so nothing at runtime can reach the closure and the leftover binding was
    unreachable code; it also stood in the way of section 9's `delegate`, whose check
    reads the post-erasure AST and wants the body to reduce to the marked
    call alone, so an erased proof helper defined inside a delegating
    function made the mark a hard error (a `tail` mark was unaffected,
    its check descending through the binding). The emitted `CLetRec` now
    carries only the block's `many` functions and is dropped when none
    remain, mirroring the guard `def-adts` already had for the empty
    case. Believed conservative, the dropped closures having no
    reachable use. The owner asked for the same reading to be applied to
    a nested `def-adts`'s *phantom* constructors, erased entries by
    section 12 and equally unreachable, so the `CLet` that statement
    emits now carries only the non-phantom ones and is dropped when none
    remain. A nested `def-adts` declaring a non-phantom constructor still
    binds a real value and so still blocks a `delegate`, which reads as
    right: section 9 wants the body to reduce to the marked call alone,
    and that binding does not reduce away. `tests/delegate_erased_inner.sl`
    covers both statements inside a delegating body.

78. **A form that fetches an object by naming something reads the name
    through its alias.** Section 9's state-forwarding `let` makes a
    binder an alias of the entry it names, and section 5's identity is
    canonicalize-then-compare, so `(let (erased N) Nat)` should leave `N`
    usable wherever `Nat` was; `ctor_var` already resolved a constructor
    that way (`tests/ctor_alias.sl`). The two forms that fetch an object
    from ambient scope did not. `matchable-of` looked for a `Matchable`
    naming the alias entry itself rather than the type constructor it
    resolves to, and `coercible-of` for a `Coercible` about the alias
    rather than about the function `def-fns` minted the proof for, so
    each reported its object missing on a renamed name. Both now resolve
    the name first, through the one helper `ctor_var` uses, which is also
    what makes `matchables` and `newtype_of` compare two canonical ids
    rather than one of each. `tests/matchable_of.sl`,
    `tests/delegate_erased_inner.sl`. Believed a correctness fix: by
    section 9 an alias and its target are one entry's contents, and
    nothing else in the checker tells them apart.

    The sweep behind this item, offered as a record rather than a claim
    of completeness: every term comparison in `lib/` either canonicalizes
    both sides (`check_type`, `check_equal`, `unify`, `Env.type_of` and
    everything reading through it, `expect_proof`, `numeral-of`,
    `Program.final`, `Extract.show`) or is fed canonical terms by
    construction (`marker` and `newtype_of` over a canonicalized
    `Matchable`; `is_strict_subterm` under `prove_subterm`, which
    canonicalizes both arguments first and relies on `canon` being deep;
    the rigid prelude ids `expect_proof` and `def-fns`'s level check
    compare against). `Term.equal` and `Term.occurs` do no
    canonicalizing of their own by design, the caller owning that.
    Comparisons of runtime code and values -- `check_marks` matching a
    `delegate`'s argument ids against the function's parameters,
    `Eval`'s constructor indices, `Extract`'s physical-identity sharing
    -- are not term comparisons and canonicalization does not apply.
    Two places read a named entry deliberately *without* resolving it,
    and were left alone: `comptime-match` wants the named entry's own
    state, multiplicity and stored value, which section 3 puts on the
    entry while the fact table holds only its type and `is` -- and
    resolving would as a rule leave nothing to read, since a run-position
    `let`'s binder canonicalizes to the expression it bound rather than
    to any variable (checked by patching the form to resolve, which fails
    on the ordinary `(comptime-match two (Succ one))`); an alias reaches
    the value through section 9's state forwarding instead, and an
    erased alias of a non-erased `Const` is refused, which is section
    34's requirement read on the name actually written,
    and `prove-predates` resolves only when the named variable is younger
    than the level, which is item 13's rule about mint order rather than
    about identity.

## Two checker gaps and a strictness from a third bug-hunting session

A session asked to look for soundness mistakes and to tidy the code
probed the checker again. Items 79-81 record what it changed; each is
the session's reading, offered as a candidate question rather than a
settled decision, and was checked by compiling and by the test suite
(CLAUDE.md rule 2). Neither gap appeared to reach a proof of anything
false: both were programs the checker accepted and the interpreter then
failed on.

79. **A non-erased match names non-erased constructors.** A `many` match
    on a tagged type compiles to a dispatch that compares the value's
    discriminant against each real branch's constructor at runtime, and
    a first-class constructor variable bound `erased` (a parameter, say)
    has no runtime value to compare against: the interpreter raised
    `unbound at runtime` on an otherwise well-typed program that passed
    its constructors erased beside a `Matchable` naming them `many`
    (`tests/erased_ctor_dispatch_bad.sl`). The pattern's constructor is
    now required to be non-erased in a real branch of a `many` match,
    which reads as section 20's rule -- an erased name in a non-erased
    position -- applied to the pattern; under an `erased` scrutinee, or
    in a refuted or phantom branch, nothing is dispatched on and the
    constructor may be erased as before. Whether the design would rather
    have such a match dispatch on the constructor's index in the
    `Matchable`, which needs no runtime constructor at all, is open;
    the extractor would then need a shape for the value that names no
    constructor either.

80. **A `ValCtor`'s return is headed by a type constructor in scope, not
    by the constructor's own field.** Item 70 requires the return to
    canonicalize to a type-constructor application, and a telescope
    binder of type `(TyCtor -> Type)` passed that test: the type
    `(ValCtor (erased (TyCtor -> Type) T) -> (T))` was accepted, and a
    `coercible-ctor` over a variable of it crashed the elaborator on the
    assertion that reads a constructor's type constructor
    (`tests/valctor_field_return_bad.sl`). No `def-adts` can declare
    such a constructor, section 12 fixing every constructor's return to
    the type it is declared under, so the type has no inhabitant and no
    `Matchable` could describe it; the former now rejects it, extending
    item 70's check to the head being a free type constructor. Read as
    the same decision applied once more, not a new one. "Free" is meant
    narrowly, the owner having asked: only the constructor's *own*
    telescope binders are refused, so a return may name a type
    constructor from any enclosing former -- a `Fn`'s parameter, or a
    field of an outer `ValCtor` -- which is how a function returning a
    type constructor beside a value constructor for it is written
    (`tests/ctor_former_nesting.sl`, `tests/gmap.sl`).

81. **An empty type may have several identical `Matchable`s in scope.**
    Section 19 makes several `Matchable`s for one type an error only
    when they disagree, and `find_matchable` reads it that way, but the
    emptiness test behind `absurd` demanded exactly one, so an absurd
    function taking `(erased (Matchable enum False) m)` as a parameter
    was told `(False)` is not an empty type. The test now goes through
    the same lookup as a match does (`tests/absurd_dup_matchable.sl`).
    A correctness fix by the session's reading of section 19.

82. **Head dispatch reads the head's type as well as its value**
    (settled by the owner; section 4 now says so). Section 38's
    `coerce` through a newtype wrapping `(Special)` produced a `Const`
    whose stored value was a `Special` variant, `(%let)`, while its
    type was the newtype's, and the dispatch, which read only the
    stored value, ran it as `let`. A special-form head must now also
    have type `(Special)`; such a value heads no form and elaborating
    it as an application fails on its type (`tests/special_newtype_bad.sl`).

## A match reads its Matchable, not its constructors

The owner's decisions, in chat, after item 79 reported that a non-erased
match on first-class constructors passed at `erased` crashed the
interpreter: a `Matchable` in scope is enough to match on a type, so the
constructors need no multiplicity of their own; the elaborator should
stamp what the `Matchable` says into the match; phantom constructors
take no discriminant; and a non-erased match needs a non-erased
`Matchable`, which is what carries an extern type's construction and
matching (§41). DESIGN.md §§17, 20 and 38 now say all four; items 83-85
record how the prototype reads them, and item 79's restriction is gone.

83. **What a match compiles to.** The post-erasure form of a match is
    its scrutinee, one branch per real constructor keyed by that
    constructor's discriminant, and a *shape* saying how the scrutinee
    comes apart: through the FFI's destructor where it holds the type
    (§41), off the tag where the type carries one, or as the value's
    own fields where it carries neither -- the case the elaborator has
    already checked leaves a single real branch (§12). All of it is
    settled at elaboration from the `Matchable`'s *type*, which fixes
    the enum/union tag, the constructor order and each constructor's
    phantom marker, together with the shape `def-adts` recorded for a
    named type. Nothing reads a constructor value at runtime any more,
    so a branch may name a constructor that is `erased` where it stands
    (`tests/erased_ctor_dispatch.sl`, the program item 79 refused). A
    fourth shape, a `Matchable` held in a variable, is the only one
    read when the code runs, and only because its type does not say
    whether the FFI implements the type.

84. **A match carries no `Matchable` it would not read** (the owner's
    decision, in chat). A `Matchable` entry is minted `many` and its
    value carries the type's runtime shape, but a match whose
    `Matchable` entry is `Const` (§34) -- minted by a `def-adts` in run
    position, or forwarded from one -- takes that shape and mentions no
    `Matchable` at all, so a non-extern type's match is a tag read or a
    field read with nothing dynamic in front of it, in the interpreter
    and in the extracted OCaml alike. Only a `Dyn` `Matchable` -- a
    first-class parameter (`tests/gmap.sl`, `tests/first_class.sl`,
    `tests/thunk_matchable.sl`, whose parameters are now `many`), or
    one a `def-adts` inside a body minted (item 88) -- is read at
    runtime, and the extraction emits a `Matchable` value for a type
    only where one is really held.
    The erasure demand, by contrast, is a rule about the source rather
    than about what the implementation manages to stamp: a match whose
    position and whose scrutinee are both non-erased needs a non-erased
    `Matchable` (`tests/erased_matchable_bad.sl`). It bites only where
    the shape is not stamped, a minted `Matchable` being `many` already,
    and those are exactly the cases no elaborator could prove
    non-extern. An erased scrutinee leaves a single real branch and no
    dispatch, and an erased position compiles to nothing, so neither
    asks for anything (`tests/erased_matchable_ok.sl`).

    Which `Matchable` a match reads therefore matters, and consistent
    ones for a type are interchangeable (§19), so the lookup prefers one
    whose shape the elaborator can see -- the one `def-adts` minted,
    read through an alias as ASSUMPTIONS 78 has the other fetching forms
    do -- over one it cannot, rather than taking the newest in scope.
    Without that, a `Matchable` parameter whose type names a concrete
    type shadowed that type's own, and a match on a `(List (Nat))`
    compiled to a runtime read and demanded the parameter be non-erased,
    though the declaration had already settled everything about it
    (`tests/known_matchable.sl`). Reading a first-class `Matchable`
    remains the only case that defers anything, and it defers exactly
    one thing: an extern type's destructor, the tag or its absence being
    settled by the `Matchable`'s type either way.

85. **Phantom constructors take no discriminant.** A constructor's
    discriminant is its position among the type's non-phantom
    constructors, so declaring a phantom constructor between two others
    no longer shifts the second one's tag. Nothing observable changed in
    the prototype -- no extern type has a phantom constructor, and the
    FFI's own destructors already numbered the model's constructors from
    zero -- but the two numberings had no reason to agree, and the
    stamped discriminants make the choice load-bearing. The extracted
    OCaml follows: a phantom constructor is no longer a variant of its
    type, and a value is never headed by one (§20's rule 2).

## A cleanup session's reading of the Matchable pick, and one open gap

A session asked to look for bugs and to tidy the code after items
83-85 landed found one spurious rejection and one gap it did not close.
Both are the session's reading, checked by compiling and by the test
suite (CLAUDE.md rule 2), not settled decisions.

86. **The Matchable pick reads aliases through and prefers a non-erased
    one.** Item 84's preference for a `Matchable` whose ADT the
    elaborator can see was applied to the entry as found in scope, so an
    erased `let` alias of a type's own `Matchable`, being newer, was
    picked ahead of the `def-adts` one, and a `many` match on the type
    was refused as reading an erased `Matchable`
    (`tests/matchable_alias_erased.sl`); likewise an erased first-class
    `Matchable` parameter bound after a `many` one of the same type
    shadowed it (`tests/matchable_prefers_many.sl`). The pick now reads
    each candidate through its alias rule, as ASSUMPTIONS 78's fetching
    forms do, and ranks the ADT the elaborator can see first, a
    non-erased `Matchable` second, an erased one last, still refusing
    inconsistent candidates as before. Read as §19's interchangeability
    of consistent `Matchable`s, not a new rule: the change can only turn
    a refusal into an acceptance, and only where a `Matchable` that
    would have served was already in scope.

87. **Forced unification consults the Matchables in scope** (settled by
    the owner; §§18, 19 now say so). The engine knew constructor
    disjointness only through rigidity (item 40), which `def-adts`
    confers on the names it mints and nothing confers on a
    `ValCtor`-typed parameter, so with `C` and `D` both parameters
    listed by one `(Matchable ... (many C) (many D))` and of equal
    arity, unifying `(C k)` against a `(D n)` pattern succeeded by
    aliasing `C` to `D` inside the branch, and `(absurd D)` was refused
    as "not refuted": an `erased` or union match over first-class
    constructors could not be written unless the arities differed. Two
    atoms one `Matchable` in scope lists are now §18's second
    contradiction (`tests/first_class_disjoint.sl`,
    `tests/first_class_disjoint_bad.sl`). No unsoundness was found
    before, the extra branch being unreachable and its facts ending
    with it; the change refuses a present branch the type already
    excludes and accepts the absurd one.

88. **The elaborator keeps no record of a type beyond the scope**
    (settled by the owner; §17 now says so). Items 83-84 had stamped
    the `def-adts`-minted shape into a match through a global table
    from `Matchable` entry to ADT record, filled by `def-adts` and read
    back by the match. The owner's reading, which the session checked
    against every use: the tag, the discriminants, the phantom markers
    and the field arities are all in the `Matchable`'s type and the
    constructors' `ValCtor` types, so the only thing a `Matchable`'s
    *value* can carry is an `extern` type's FFI wrapper (§41), and that
    value has the home every value has -- the entry's `Const` state in
    run position, a runtime binding in a body (§34). The table is gone;
    the `Matchable` minted inside a body is `Dyn` like the
    constructors beside it, bound by the same code, and a match on it
    reads it when the code runs, as a match on a parameter does. In the
    prototype the value also names the type for the extractor, which
    emits that type's destructor for it; the interpreter reads only the
    wrapper. Two smaller tables went the same way: `Special`'s
    variant-to-form map is a value the prelude builds, and the
    `def-adts` code binds no phantom constructor at all, a phantom
    entry holding only §3's token. What remains global is the id
    supply, the extractor's inputs (`Env.trace` and the id-to-name map
    it prints with), the FFI's claim tables and the `--no-extern` flag.

    One consequence for `delegate`: the `Matchable` a nested `def-adts`
    now binds would stand between a delegating body and its call, so
    the tail-check's normalizer, which already folds a renaming `let`
    away, also drops a `let` whose right-hand side is values embedded
    by elaboration -- literals in the post-erasure code, the entries
    they bind staying `Dyn` as §34 has every binding in a body -- when
    the rest of the body mentions none of its binders. That keeps item 77's guarantee for a phantom-only
    `def-adts` (`tests/delegate_erased_inner.sl`) but reads more widely
    than item 77 did: a nested `def-adts` whose constructors the body
    never uses no longer blocks a `delegate` either
    (`tests/delegate_inner_adts.sl`). Settled by the owner: this is the
    behaviour wanted, dropping a binding nothing reads changing no
    program's meaning.

89. **Nothing but a signature or a `Matchable` tells two atoms apart**
    (the owner's proposal, in chat, implemented here; an earlier form of
    this item, which kept identity-based distinctness for declared type
    constructors, was the session's own invention and is withdrawn).
    Item 40's `rigid` marker is gone from the scope entry altogether.
    Forced unification of two atoms now does three things: it refuses
    the pair where one `Matchable` in scope lists both (item 87), it
    makes the newer an alias of the older, and it then unifies what the
    two must share -- their signatures, where both are type or value
    constructors, and the `Matchable`s they head, where both are type
    constructors heading one -- so that a constructor list of a
    different length, a phantom marker that differs, or a field of
    another type refutes the branch. A declared name has no
    distinctness of its own: `Nat` and `Bool` are told apart by their
    `Matchable`s, `Succ` carrying a field `False` does not; two types of
    identical shape are not told apart at all, and an opaque type with
    no `Matchable`, `Level` say, unifies with any type constructor of
    its signature. The session's reading is that every such branch is
    unreachable and its facts hypothetical, so nothing false follows,
    and that what is lost is only an `(absurd C)` the checker can no
    longer grant. The suite is unchanged. §18's second failure mode and
    §19 now say this, in wording the owner confirmed (CLAUDE.md rule
    12).

## A compiler written in the language (self/)

Written by a session working autonomously at the owner's request, in
chat: name the language SL for now, self-host it, write in SL a program
compiling SL to OCaml that can interpret the compile-time `Const` part,
and use the existing OCaml interpreter and extractor to get there.
`self/README.md` describes the result; items 90-92 record what it
assumed and the one change it made to `lib/`. As elsewhere here, each
is the session's reading, checked by `self/bootstrap.sh` rather than
by the owner.

90. **`lt-dec` and `Dec` are extern.** The FFI table gains an
    implementation of the prelude's `lt-dec` (integer comparison) and
    of `Dec`, held as its constructor index alone since both
    constructors' fields are erased (`Ffi_core.indexed`); the source
    models and the `Dec`-consuming prelude functions are unchanged, and
    `dune test` still checks every test with the implementations
    stripped. The reason is speed inside the compiler: without it,
    comparing two characters or two small numbers is a walk down both
    numerals, and the compiler compares characters at every name
    lookup. This is the same kind of entry as `nat-add`'s (item 42),
    so the session read it as an implementation matter rather than a
    decision for the owner; the mark on `lt-dec` in `lib/prelude.sl`
    is nonetheless the owner's to keep or revert.

91. **The compiler checks its input.** A first version trusted it; at
    the owner's request ("make it not trusting") the session ported
    every check of `lib/elab.ml` and `lib/env.ml`: the three
    contradictions of forced unification (section 18), identity of
    types and values, erasure by position, the call-site proofs against
    the current level and enclosing subterm parameters, branch
    refutation and the one-real-branch rule, `comptime-match`
    verification, the tail and delegate marks, newtype shape, extern
    claims, and the reader's and literals' errors, with the reference's
    message texts. `self/bootstrap.sh` requires every error test to be
    refused with its text. Two readings of the session, not the
    owner's: an error does not stop elaboration, so a program may be
    refused with more than one message where the reference gives its
    first; and a message's line is that of the innermost form whose
    elaboration was in progress, where the reference may name a
    sub-form (a pattern, a field name), which on the tests and the
    session's own multi-line cases gave the same line. It is still not
    a second arbiter
    for section 10's consistency question, since it runs on the same
    reading of the design and trusts its own interpreter as `lib/`
    trusts its (KERNEL.md).

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
    only the test comparison speaks to, one test at a time. The session
    did not add these checks to `dune test`: running the compiler under
    the reference *interpreter* takes seconds per file and the stripped
    mode of item 44 would run its fuel counters in unary.

93. **Canonicalization terminates by construction, on an append-only
    list of rules.** At the owner's direction the session replaced the
    compiler's canonicalization fuel with a structural argument. The
    environment holds its rewrite rules in the order they were appended,
    and every appended rule's right-hand side is canonical at that
    moment. The session's reading is that a canonical term mentions only
    variables that are rule-free then, so any rule they later carry was
    appended later, and a chase from a rule only ever needs the rules
    after it. `canon` takes that suffix as its first `subterm` parameter
    and the term as its second; the lookup walks the suffix and returns
    the tail after the rule together with the `Subterm` proof, so the
    checker accepts the chase as a lexicographic decrease. A first
    version left completeness, that the rule is in the suffix, to that
    reading; item 94 proves it.

94. **The fact table, canonicalization and unification carry erased
    proofs.** Again at the owner's direction, and after the owner set
    aside a stamped version with a runtime comparison, a fully verified
    map, and an eager-substitution design, the session made the
    invariant of item 93 a proof rather than a reading. The fact table
    is a trie `Facts n` whose index counts its rule-free entries, with
    sums as the relations `Plus` and `Plus3` since a type may not call a
    function; `In` is the path to a rule-free entry and `RuledIn` to a
    ruled one. The environment's table carries, erased, the order
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
    once the variable is ruled out. What remains informal, both by the
    session's reading: a fresh id never lands on an occupied position of
    the table, which `bind` reports as an internal error if it ever did,
    and the reference's own termination, which no proof here touches.
    The verified table and the proofs together are about 1,100 lines in
    `self/core.sl`, most of it erased; they cost elaboration time only,
    and the bootstrap ran no slower.

95. **The emitter recurses on the closure it emits.** Its fuel is gone:
    every function of the emitting block takes the closure being emitted
    as its first `subterm` parameter and the piece of code as its
    second, with an erased `Subterm` proof that the piece lies inside
    the closure. A constant met in the code is then a subterm of the
    closure through that proof, a captured variable's value is a
    subterm of the closure's environment (the map lookup returns the
    proof with the value), and a closure met inside a value is a subterm
    of the value, so each descent is a lexicographic decrease the
    elaborator checks. A run-position group is emitted under a closure
    built around it, which captures nothing. While doing this the
    session found that the compiler's own elaborator had defined
    functions named `prove-subterm` and `prove-predates`, which shadowed
    the special forms of the same names in the files after it; they are
    now `mint-subterm` and `mint-predates`. The session's reading is that
    a name bound by a program shadowing a special form is what the
    design intends, and only the choice of names was at fault.

96. **The elaborator recurses on the raw it elaborates; no fuel remains
    outside the interpreter and the generated printer.** Every function
    of the elaborating block takes as its first `subterm` parameter the
    raw, or list of raws, it elaborates. The structures a function parses
    from that raw before elaborating it are indexed by the raw and carry
    erased `Subterm` proofs for the raws they hold: telescope entries
    (`SrcEntry root`, with `Sub root` for the raws before and after an
    arrow and `Within b a` for a suffix, which may be the list itself),
    function and type headers (`Headers fns`, one per raw of the list),
    branch parts, a let's binders, a constructor's signature and a call's
    decrease annotation. A descent into one of those raws is then a
    checked decrease at the first position, and a loop over such a
    structure a decrease at a later position with the raw held fixed.
    Where a function hands its whole raw to another (a type former to
    the TyCtor or ValCtor reader, a telescope reader to the loop over
    its parsed entries) a `Steps` value decreases instead: its type
    states how many hops it must pay for, `(Steps (Succ (Succ (Zero))))`
    for a type former, so the zero case is refuted by the constructor's
    index rather than reported, and each descent supplies a fresh budget
    of a size the code's shape fixes. The session's reading is that this
    is not a fuel in the sense of the earlier items: no path reports
    exhaustion, and the checker rejects a budget too small for the hops
    below it. Three smaller fuels went at the same time: the numeral
    spelling counts up in `Bin` from zero and the decimal printer counts
    up a digit list, both linear in the number (a numeral in the
    millions costs that many steps, which the session judged acceptable
    for the sources and tests at hand), and the reader closes `$` frames
    by recursion on the frames below the one closed. The restructuring
    merged the wrapper hops (`elab-expr` with `elab-form` and the
    special-form dispatch, `elab-term` with `elab-term1` and `elab-type`
    under a flag, the statement pair) and moved `comptime-match`, the
    field lookup and the malformed-form error out of the block. The
    session expects behaviour to differ only on malformed input: a
    function or type header, or a constructor, with no signature after
    its name is reported and then skipped rather than elaborated as an
    empty signature, so the errors following the first can differ from
    before; the bootstrap's error tests all still find their message,
    and its programs and fixpoint are unchanged.
