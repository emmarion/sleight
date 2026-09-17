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
   `Eq`, `Add`, `Lt`, `Double`, `Pow2`, `Mod`, `Dec`, `Cmp`, `U8`,
   `U8Add`, `Bin`, `Numeral`, `Char`, `String`, `Append`, their
   functions, and the levels `nat-lvl`, `u8-lvl`, `char-lvl` and
   `str-lvl`, the tests' names for them, every other level being
   anonymous (item 118), all as ordinary, shadowable entries, and since item 58 also `Unit`, `Maybe`,
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
21. **Match branches**: each constructor of the `Matchable` has at most
    one branch, in any order, and one left unlisted must be refuted or
    stood for by an `else` (SR 17, settled by the owner; §12 now says
    so). A present branch whose forced unification contradicts is an
    error telling the programmer to write `(absurd C)`; an `(absurd C)`
    whose unification succeeds is an error.
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
    this looked harmless. Superseded by item 138: the right-hand side's
    entries now stay in scope, so no fact outlives an entry it mentions.
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
    `Add`, `Lt`, `Double`, `Pow2`, `Mod`, `U8Add` and `Append` carry
    their sub-proofs at `erased`, and the lemmas (`double-pos`,
    `add-succ-right`, `mod-succ-lt`, ...) are `erased` functions, so no
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
    shared buffer be collected, and since item 118 its return is
    declared `(many s is t)`, so the checker sees the identity it
    models. `str-append` is plain source at
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

53. **`(numeral-of lit)`** takes a numeral or character literal
    itself, not an expression canonicalizing to one, and yields that
    literal's erased `Numeral` proof; a character literal yields its
    code's proof, and a string literal is an error, having none. It
    resolves the literal by its own spelling through `Env.literals`
    rather than searching the scope, unlike `coercible-of`. Resolving
    by spelling rather than by canonicalized value is what keeps the
    form usable inside a branch that has equated two literals: each
    still fetches its own proof, so the two spellings for one `Nat`
    refute the branch (`tests/numeral_of_branch.sl`) instead of one
    literal's proof standing in for the other's. The owner suggested
    `nat-of`; the session renamed it because the form yields a proof,
    not a number.

54. **Resource limits under `--no-extern`.** Stripped, `bin-to-nat`'s
    model runs `add` in unary, and `Value.show` prints a `Nat` in
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
    have no answer -- superseded by item 146, which makes these carry a
    nullary function too) or a continuation `(Fn L (many answer) -> (many
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
    descriptor and compares indices, as `Eval` does. A statically known
    match extracts against a phantom-index copy of its variant: the
    constructors that can reach it (its real branches and those its
    `else` stands for, recorded as the code's `live` set) are indexed
    `yes` and the rest `no`, and the scrutinee is coerced to the `yes`
    instance, so OCaml's exhaustiveness checker accepts the match
    without the refuted arms and emits no default; an `else` stays as
    `_` under that type. The interpreter still raises on a reached
    absurd, extraction being the path that trusts the checker (the
    owner's reading: interpretation is the checked path, extraction is
    opted into for speed). The first-class and extern paths keep their
    `absurd ()` guards, matching on an index no type narrows. The copy
    keeps every constructor at its arity, which is what keeps its
    representation the base type's; this session saw a copy that
    changed a constant constructor's arity renumber the ones after it.
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

90. **`lt-dec` and `Dec` are extern** (superseded by item 120: the
    extern is `nat-cmp` over `Cmp` now). The FFI table gains an
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

97. **A fresh id is provably absent from the fact table.** The table is
    now indexed by a bound as well as by its facts, `Table n f c`, and
    carries an erased `Above` proof that every key it holds is at most
    `c` (at each node, the key its path spells is, when the node holds
    an entry); the environment keeps its id counter as that bound, so
    the table's type is `Table nfree ffacts fresh`. Binding takes the
    successor of the counter with a `BinLt` proof (`bin-succ-lt`), and
    `table-insert` refutes the position being taken: a taken position
    yields a `Taken` proof (the insertion now returns one instead of a
    bare `IKept`), `Above` turns it into `BinLe x fresh`, and the strict
    order refutes that, so the "internal: a fresh entry's position was
    taken" error of item 94 is gone. `BinLt` and `BinLe` are the order
    on ids digit by digit, with reflexivity, transitivity in its four
    mixed forms, irreflexivity and a three-way decision with proofs.
    The bound moves only up: ruling out preserves the keys (`above-out`),
    inserting the fresh id keeps them at most the new counter
    (`above-ins`), the id supply's other client weakens the table to
    the new counter (`env-fresh-id`), and leaving a body keeps the outer
    table with the inner counter by comparing the two and weakening
    towards the larger, which is the inner one in every run but is
    decided rather than assumed. Unification threads the bound through
    its outcomes (`Outcome n c`) so that setting the table back into the
    environment sets the counter it was read with. The session's reading
    is that this closes the informal claim of item 94; the reference's
    own termination remains the one thing no proof here touches. In the
    same session the elaborator's lockstep lists went: the ids bound for
    a `def-fns` or `def-adts` are indexed by the headers they came from
    (`Bound fns hs`, `Tids adts hs`), headers hold their parameter and
    return telescopes rather than a type to take apart, string literals
    are interned by their own function so no name classifies as a
    string, the wrapping constructor's field is found by the search that
    checks it is the only one, and a run-position group's closures are
    the pairs closing produced. What the session left as they were, all
    reachable only after an error was already recorded or by the
    interpreter's own failure: `bind-let` and `first-res` on a result
    list whose length a reported count error already disagreed with,
    `spread` on values the interpreter failed to produce, and the
    interpreter's dynamic checks, which belong with its fuel. Still
    informal by the session's reading: the `comptime-match` contradiction after a value was verified, and
    the places that read an id out of a term expected to be a variable
    and default to id zero otherwise. Of those last, the session made
    the prelude-name lookups (`Nat`, `Numeral`, `Bin`'s digits, `Lt`,
    `MkChar`, `Char`, `String`) report an unbound name rather than
    default, since they are reachable by running slc without the
    prelude; the reader of a Matchable's constructor slot stays as it is,
    because the reference (`lib/env.ml`'s `unify`) treats those slots as
    ordinary variables, ruling one out against another when two
    Matchables disagree, so holding ids there instead of terms would
    change what unification does; the session's reading is that a slot
    holding anything but a variable is an invariant of well-formed terms
    of the same kind as `infer`'s.

98. **A proof's arguments are read by arity, not by position.** Reading a
    proof of `Predates`, `Subterm` or `Coercible` (`expect-proof3`,
    `expect-proof4`) now takes the relation's argument count apart and
    reports "expected a ... proof" on any other shape, where before the
    head was checked and the arguments fetched by index with a placeholder
    for a missing one; `nth-term` remains only for a call's arguments,
    reached after an arity error was already reported. The session also
    weighed intrinsically typed terms for the remaining well-formedness
    invariants and set them aside: the reference (`lib/env.ml`) adds a
    rule with no type check and makes the types agree by a second
    unification, as `refine` does, so between the two the rewritten terms
    are ill-typed from an intrinsic view, and slc must keep that order to
    accept and refuse the same programs. The reference accepts the
    inductive-inductive shape such terms would need (a type of types whose
    constructors embed terms indexed by those types) and refuses a type
    indexed by itself, both checked by compiling; the obstacle is the
    metatheory, not the declaration.

## `let-match`, and reasoning about literals through their spelling

The owner asked for a single-branch statement form of `match`, named it,
and confirmed §16's wording. What follows is how the session built it and
what it assumed while doing so.

99. **`let-match` reads no value, so it is not confined to run
    position** (`Elab.elab_let_match`). It requires the scrutinee's
    `Matchable` to list exactly one constructor and refuses a phantom
    one; the fields bind at `under smult` their declared multiplicities,
    which is §20's existing rule for a match's branch fields, so an
    erased scrutinee yields only erased fields. The refinement goes
    through the same `refine` an ordinary `match` branch uses, so nothing
    is asserted that a branch would not already have established — the
    form appears to change where the refinement reaches, not what it is.
100. **Its code depends on the scrutinee's erasure and on run position.**
    An erased scrutinee emits nothing, matching `elab_match`'s existing
    rule that one real branch under an erased scrutinee compiles to that
    branch's body. In run position with a `many` scrutinee it runs the
    scrutinee and binds the fields `Const`, as `comptime-match` does,
    emitting nothing. Only outside run position does it emit a
    one-branch `CMatch` wrapping the rest of the enclosing expression.
    So a `let-match` at top level never costs the code after it its run
    position, which was the session's worry about the form and appears
    not to arise.
101. **§27 numbers it `5a`** rather than renumbering the entries after
    it, at the owner's direction, in wording the owner confirmed
    (CLAUDE.md rule 12), and §20's erasure list names the form in its
    own bullet, in wording the owner confirmed.
102. **The `Numeral` lemmas are tests, not prelude additions**
    (`tests/numeral_distinct.sl`, `tests/numeral_succ.sl`). Each defines
    its own `Eq`, since the prelude has none and what belongs in the
    prelude is the owner's call. The session's reading is that these
    lemmas make disjointness and the successor step derivable rather
    than asserted — every fact reaching the table arrives through an
    ordinary checked call — but whether that is worth the lemmas'
    weight, and whether they should move into `lib/prelude.sl`, is not
    decided.

103. **The prelude carries `Eq`, `BinSucc` and seven erased lemmas**
    (`lib/prelude.sl`): `double-fn` and `double-inj` for the two
    directions of `Double`, `double-parity` for the even/odd clash,
    `numeral-zero`, `numeral-fn` and `numeral-inj` for `Numeral`, and
    `numeral-succ` over `BinSucc`. `Eq` is homogeneous and polymorphic,
    `(Eq : (Type A) (A x) (A y) -> Type)` with one `Refl`; the two tests
    that define their own shadow it without trouble. Elaborating the
    prelude went from about 45ms to about 95ms, which the session judged
    acceptable but did not put to the owner.
104. **`unary` and `distinct` elaborate to prelude calls, in the
    prelude's scope** (`Elab.elab_unary`, `Elab.elab_distinct`,
    `Elab.in_prelude`), so user shadowing cannot reach the generated
    forms, as with a literal's own expansion (51). The level context
    stays the caller's, so the generated call carries `(predates _)`
    inside a function body and nothing at top level (§24). `unary`
    hoists every literal on the walk, which is why `Elab.hoist` moved
    into the elaborator's recursive group. Its ceiling is 4096 steps,
    a number the session chose and the owner has not confirmed.
105. **Whether §27 should list a sugar form is open.** `unary` and
    `distinct` are registered as `Special` variants like any other form,
    but they carry no meaning of their own and are recorded in SUGAR.md,
    which is what that file is for. §27 says it lists every special
    form; the two readings are not reconciled here.

106. **`unary` mints one rule, not one per step.** At the owner's
    direction `(unary a b)` relates `a` to `b` under `a - b` successors
    and says nothing about the literals between them, which stay opaque
    (`tests/numeral_succ.sl` unaries `5` against `3` and then `4`
    against `3` without conflict). The session's first reading walked
    the range minting a rule per literal, which made every intermediate
    transparent as a side effect nobody asked for. The fold costs
    `a - b` erased calls in the generated term and one rule of that many
    nodes; using a literal as a `Vec`'s length now wants a `unary` per
    literal down to zero, which is the caller's choice rather than the
    form's.
107. **The prelude's character operations** (`lib/prelude.sl`):
    `char-cmp`, and it is `nat-cmp`. `Cmp` is parametric in the carrier
    and its strict order, `(Cmp T R a b)` with `R` a two-place type
    constructor over `T`, and every field is erased, so a value is only
    its tag and two instances differ by a coercion. `char-cmp`'s
    arguments coerce down through `Char`'s and `U8`'s newtype wrappers
    to their codes, the call to `nat-cmp` is a `delegate` (§38), and the
    `Coercible` carrying the result back up is built by an erased match
    over the three constructors — erased, so §12 puts no one-real-branch
    limit on it and it leaves no code, which is what lets the delegate
    mark stand. `tests/char_ops.sl` coerces `char-cmp` to `nat-cmp`'s
    own type and runs it on `Nat`s. `CEq` repeats its index rather than
    carrying an `Eq`, at the owner's direction, so matching it forces
    the two sides together the way `Refl` does; the branch still wants
    `pa` and `pb` identified before two `Char`s coincide, which is why
    `lt-unique` is now in the prelude at `dbl-lvl`.

    `char-to-nat` and `nat-to-char` were written and then removed at the
    owner's direction: converting is trivial through `U8`, which is
    itself trivial given an `Lt`, so the prelude need not choose what a
    `Nat` out of range becomes (`tests/char_convert.sl` writes both
    directions out).

108. **"Mint" in these notes means a fact or entry reaching the tables,
    not a claim about who checked it.** For `unary` and `distinct`
    nothing is asserted: the elaborator writes down terms — a `Bin`
    spelling, a `BinSucc` witness, a call — and the refinement reaches
    §18's table through the same `refine` an ordinary match branch uses.
    A wrong term does not typecheck, which the session checked by
    handing `numeral-succ` a witness and then a spelling that lie; both
    are rejected. What is not checked, here as everywhere a numeral is
    involved, is that a literal's runtime `Nat` is the number its source
    spelled, which rests on `bin-to-nat`'s extern (§41's invariant, and
    KERNEL.md's note on facts).

109. **`nat-to-u8` is gone** (`lib/prelude.sl`, `lib/ffi.ml`,
    `lib/ffi_core.ml`), removed at the owner's direction: a wrapping
    narrowing hands back a `U8` whose value bears no stated relation to
    its input, so what it returns is opaque exactly where a caller
    wanted to know. Nothing replaced it, and nothing needed to. A
    literal takes §41's reflection route at top level and is referenced
    from a body as an ordinary value, which is what the eight tests
    using it for an exit code now do. A computed `Nat` is narrowed where
    it is used, by binding it and matching `lt-dec` — §5 keeps a call
    out of the `Dec` index, so the binding is not optional — with the
    caller saying what out of range means instead of the prelude
    wrapping silently (`tests/io_closure_in_data.sl`,
    `tests/io_factory_twice.sl`). `u8-add` still wraps, which is
    modular arithmetic rather than a narrowing and was not touched.
    §41 says this, in wording the owner confirmed (CLAUDE.md rule 12).

110. **`U8` is marked `newtype`, and needs no extern.** `MkU8` carries
    an erased bound proof beside its one `many` field, which §12's
    newtype rule permits, so §38 requires the value to be that field
    alone — which is what the FFI's `bounded` was doing by hand:
    construct was the identity on the integer and destruct handed it
    back. With the mark, the ordinary untagged one-field path does the
    same, so `U8`'s `extern`, `Ffi_core.bounded`, its `Ffi.types` entry
    and its `Extract` entry are all gone, and `u8-add`'s result and the
    `String` FFI's per-character value are built at `"Nat"`, a `U8`
    being a `Nat` at runtime. `u8-to-nat` went too, having been the
    extern form of `coercible-wrap MkU8`.

    §41 says this in its prose, its code block and its list of externs,
    in wording the owner confirmed (CLAUDE.md rule 12).

## The compiler in `self/` after `let-match`, `unary` and `distinct`

A session merged the changes of items 99-110 into `self/` at the owner's
request ("update the self hosted SL on SL to match"). What follows is
how it read them into the compiler; `self/bootstrap.sh` is the check, and
none of it is design.

111. **`unary` and `distinct` are expanded where the form is reached, on
    a budget.** `elab-unary` and `elab-distinct` make the reference's
    checks in its order, with its messages, then write the same source
    text by the same fold and elaborate it in the prelude's scope (a
    `prelude` field the `Env` gained, set by `self/main.sl` after the
    first file, which is the prelude), with `(predates _)` when a level
    is in force and nothing at top level, as `lib/elab.ml` does (104).
    The compiler's elaborator recurses on the raw it elaborates (96),
    and a raw of its own making is no decrease; so every function of
    the elaborator's group took a `Nat` budget of expansions as a new
    first `subterm` parameter, passed unchanged on every existing call
    and decreased on the one call that elaborates a generated form,
    which the checker accepts as the lexicographic decrease it already
    accepted for `canon` (93). The top level starts the budget at one,
    since a generated form contains no sugar; the zero case is reported
    as an internal error, as no proof here says a generated form
    contains none. A first version instead expanded the sugar by a pass
    over the top-level form, reading heads by name; the owner asked for
    the reference's behaviour, under which a function shadowing
    `distinct` or a `let` aliasing `unary` resolves as any other head
    does, and the session checked both against the reference. The
    session's reading is that the derivation reaching `refine` (108) is
    the reference's own. `let-match` is ported as the reference has it,
    with `SMatch` as the statement code of a one-branch match wrapping
    the rest.
112. **A `U8` is its `Nat` inside the compiler too.** With `U8` a newtype
    (110) the compiler's value model dropped its `PU8` payload: a
    character literal's value, the `String` FFI's per-character value
    and `u8-add`'s result are all `Nat`s, as `lib/ffi.ml` now builds
    them. The compile-time interpreter's `u8-add` rebuilds two `U8`s
    from its `Nat` arguments by `lt-dec` and calls the prelude's own,
    reporting an error value if an argument is not below the modulus,
    which a typed program's cannot be. `char-of-code`, which the
    compiler uses to turn a code from the FFI into a `Char`, takes the
    same route and maps a code the modulus does not bound to the
    character with code 0; the reference's `Char.chr` would raise there
    instead, and no program reaching either is typed. The compiler's
    own exit codes are built as the tests' are, by reflection at top
    level (109).

113. **A call with no decrease annotation gets one inferred** (SUGAR.md
    3; `Elab.elab_call`, `elab-call` in `self/elab.sl`). Inside a
    function body a call carrying neither `(predates p)` nor
    `(subterm p)` is elaborated as if it carried `(predates _)` when the
    callee's level and the current level differ canonically (75), and
    otherwise `(subterm _)` at the first `subterm` position whose
    argument differs canonically from the enclosing counterpart. The
    check itself did not change: the same minters build the proof and
    the same comparisons read it. What changed is which programs are
    refused, and how. A bare call is no longer "needs a (subterm p)
    annotation"; it is refused only where the inferred proof fails, with
    that failure's message: `prove-predates`'s where the callee's level
    is later or was not minted by `def-lvl`, "is not a strict subterm
    of" where the chosen argument does not decrease, and "same-level
    call to f decreases no subterm argument" where every position
    agrees. `tests/no_predates.sl` and `tests/no_subterm.sl` expect
    those messages now, `tests/level_alias_bad.sl` the last of them, and
    `tests/bare_call.sl` shows both inferred kinds and a two-position
    lexicographic decrease without annotations. The generated prelude
    calls of 104 and 111 carry no annotation any more. That the first
    differing position is the only one an annotation could succeed at,
    and so that bare calls accept exactly what `_` accepted, is the
    session's reading, not the owner's; the tests are the evidence.

## A match's results are out of scope for its own branches

A session asked to fix and test a program the owner sent — a `match`
whose `else` fetched a `Matchable` from ambient scope, and an `absurd`
function that then returned a level as a proof of `(False)` — found the
program accepted and changed one thing in the reference and the same
thing in `self/`. Item 114 records it. The reasoning is the session's
and may be wrong (CLAUDE.md rule 1); the two new tests are what was
checked by running (rule 2).

114. **A `match`'s result entries are opened after its branches**
    (`Elab.elab_match`; `elab-match` in `self/elab.sl`). A match's
    annotation is a telescope, and the entries it opens stand for what
    the match produces. They were bound before the branches were
    elaborated, so the branches ran in a scope that already held them.
    Their names are dropped (`~names:(anon ann_tele)`), so nothing
    reaches them by name; but the lookups that go by type scan
    `env.scope` regardless — `find_matchable` and `matchable-of` for a
    `Matchable` heading a type constructor (§19), `newtype-of` for a
    `Newtype` naming a constructor (§38), `coercible-of` for an
    anonymous `Coercible` about a function (§9). A branch could
    therefore satisfy the annotation by fetching the entry the
    annotation had just minted, and `check_results` then compared that
    entry with itself. Two consequences the session could run:
    `(match erased (Zero) (((Matchable enum Level) m)) (else
    (matchable-of Level)))` bound an erased `Matchable` for `Level`
    listing no constructors, which is what `check_empty` reads as
    `(Level)` being an empty type, so an `absurd` body (§37) was
    accepted for a `def-lvl` level and `(False)` followed
    (`tests/match_result_matchable_bad.sl`, the owner's program); and
    the same shape through `newtype-of` minted a `Newtype` for a
    constructor whose `def-adts` entry carries no `newtype` mark, after
    which `coerce` handed a tagged `(MkBox (Succ (Zero)))` to a
    position of type `(Nat)` and it printed as one
    (`tests/match_result_newtype_bad.sl`). The results are now opened
    after the branches, the coverage check and the `else`, which is the
    only change; the annotation telescope, the check of each branch's
    results against it, and the results the match returns are as they
    were, and all 219 prior tests still pass. DESIGN.md does not appear
    to say either way. That a branch may not read what the match it
    belongs to produces looks to the session like plugging a
    circularity rather than a design choice, but it is recorded here in
    case the owner reads §12's annotation as binding for the branches;
    the entries are still anonymous, so the question is only about the
    type-directed lookups.

## `_` for an erased argument

The owner proposed `_` for an erased argument of a type constructor, a
value constructor or a function call, solved by unification against an
expectation and the other arguments, naive and left to right, with every
expression's type settled when the elaborator leaves it (SUGAR.md 6
records the proposal). Items 115 and 116 are the implementing session's
reading and choices, not the owner's; `tests/wild_*.sl` are the evidence.

115. **A `_` argument is a meta, solved by `Env.unify` in its solving
    mode** (`Elab.check_args`, `Env.bind ~meta`, `Env.unify ~force`;
    `check-args`, `bind-as` and `unify` in `self/`). A meta is a scope
    entry with the `meta` flag that `bind` leaves out of `env.scope`
    (and, in `self/`, out of the objects list), so nothing reaches it by
    name and none of the type-directed lookups of item 114 can fetch it;
    it prints as `_`. `unify` without `~force` binds only metas — a meta
    against a meta binds the newer, a meta against a term binds the meta
    after the occurs and dangling-binder checks of §18 — and requires the
    two sides identical otherwise; `refine` and the extractor's printer
    pass `~force:true` and are as they were, and `check`/`check_sg` now
    go through the solving unifier, which on meta-free terms is the
    identity check they were. `check_args` mints one meta per parameter,
    at the parameter's type over the metas before it (an `is`-entry's
    meta is solved by its rule at once); an argument written `_` is
    refused unless erased where it stands (`under pos e.mult`) and
    otherwise left to its meta; any other argument is elaborated with
    the parameter's instantiated signature as its expectation, checked
    against it, and bound to its meta. Where some argument is `_`, the
    application's result over the metas — `(C metas)` for a constructor,
    the return telescope instantiated for a call — is unified with the
    expected telescope before any argument is read, as a transaction
    (a failure leaves the environment as it was); at the closing paren,
    if a `_` is still open, the same unification is run again reporting
    the mismatch (`type mismatch: expected (Maybe (Nat)), got (List
    _)`), and a `_` still open after that is refused (`argument 1 is _
    and cannot be inferred`). The solutions replace the metas in the
    argument terms (`Env.metaless`), so no meta outlives the
    application that minted it. The expectation is the telescope
    `elab_expr` already carried for §2's `_` annotation — a function
    body's return telescope, a match's annotation — now handed down
    through `values` (entrywise, instantiated with the entries before),
    `tail`, `delegate` and every argument position; a `_` annotation
    refuses an expectation with a meta in it (`tests/wild_match_ann_bad.sl`).
    A `let` whose binders all carry a type or an `is` clause (the
    owner's addition) elaborates them as a telescope, `Elab.elab_tele`
    over the binder forms and `elab-src-entries` over the parsed
    binders in `self/`, and hands it to the right-hand side as its
    expectation; the check of each binder against its value is as it
    was (`tests/wild_let.sl`). Consequences the session chose without
    the owner: `(f _ (Nil _))` is refused, the inner application closing
    before anything settles the outer `_` (`tests/wild_nested_bad.sl`);
    an untyped binder hands nothing down, so `(let (many xs) (Nil _))`
    and a `(Nil _)` scrutinee are refused; a type constructor
    application's `_` is
    solved only through an `is` expectation, so `(many (List _) xs)` in
    a signature is refused (`tests/wild_type_bad.sl`); §3's decrease
    annotation is inferred after the arguments are solved, as the
    proposal asks, which is the order `elab_call` already had. All prior
    tests pass unchanged, and no error message of a prior test changed.

116. **`self/*.sl` writes `_` wherever slc accepts it, and `$` for a
    last argument on one line.** A script tried every erased argument
    of a known constructor or function as `_` (4052 of them, patterns,
    signatures and `let` binders left alone) and kept the 3225 that
    slc accepts, reverting the rest by the line slc reported: 459 KB
    became 447 KB, 2.5% fewer bytes, most of it in `core.sl`'s
    proof-carrying code, where a lemma's erased indices are read off
    the proof after them, and in `elab.sl`'s `(Nil _)`, `(None _)`,
    `(Cons _ x xs)` and `(list-length _ xs)`. What stayed written is
    what the reading of 115 cannot solve: a `(Nil (T))` as a `let`'s
    right-hand side or a scrutinee, an erased index no later argument or
    expectation mentions, and a `_` under a still-open `_`. A second
    script then rewrote each subform that is the last item of its parent
    and sits on one line, `(f a (g b c))`, as `(f a $ g b c)` (DESIGN.md
    §2), where the parent is headed by a name rather than a
    multiplicity, a type former, `match`, `def-fns` or `def-adts`, and
    the subform by a name: 4211 sites, byte-neutral (`(`+`)` and `$ `
    are two characters each), 18% fewer closing parens overall. Both
    rewrites are syntactic and meaning-preserving by construction, the
    first because a solved `_` is canonically what was written, the
    second by §2's definition of `$`; `self/bootstrap.sh` is the check,
    and the compiled compiler is byte-for-byte the fixpoint it was.
    Multi-line last items (a body's final `match`, a `let`'s right-hand
    side over several lines: 1339 sites) were left as they are, a `$` at
    the start of a continuation line being a style the owner has not
    written, and are the remaining `$` savings if wanted. With typed
    `let` binders an expectation (115), a third script moved the
    annotation of every `let`-bound `match` onto the binders and wrote
    `_` for it — 151 of 164, the rest having an `is` entry, an anonymous
    binder a later type mentions, or a statement before the match — for
    another 930 bytes; the erased arguments that pass had left written
    were tried again under the new expectations, and one more is solved.
    Under 117's boundary rule both passes ran once more: 116 erased
    arguments and 45 `many` ones in erased positions became `_`, all in
    core.sl's proof code, about 300 bytes. What stays written is, by a
    check of each remaining site one at a time, almost entirely erased
    *proof* arguments -- evidence such as an `Ord`, a `Fr` or a `Subterm`
    that nothing else mentions, which no unification in any order could
    supply -- and a few data-typed indices the batch script had dropped
    along with a failing neighbour, which a final one-at-a-time pass
    over the data-typed leftovers picked up (nine erased, and 27 of 31
    `many` ones in erased positions). The four data-typed sites still
    written are two shapes: a `(Succ (Zero))` under an untyped erased
    `let` that only the bound proof's later use fixes, and a pair of
    occurrences of one index in a call that determine each other and
    nothing else mentions, so one of the two must be written.

117. **Pure terms stay open; boundaries settle** (`Elab.check_args
    ~boundary`, `Elab.settle`, `Env.bind`; `check-args`, `settle`,
    `bind-as` in `self/`). The owner's second round on SUGAR.md 6: the
    invariant is that no fact in the table mentions an unsolved meta,
    and the forms are sorted by it. A constructor or type constructor
    application, in an expression or in §5's grammar, is no boundary:
    `check_args` runs without its closing checks there, the term and
    type it returns may hold open metas, and `elab_expr` substitutes the
    solved ones into every result it returns (`Env.metaless`). A call is
    a boundary for its arguments, as before. Everything that records a
    fact settles first: a `let`'s values before they are bound, a
    `match`'s scrutinee, the results of a body (`check_results`), the
    arguments of the special forms (`elab_erased`, the `coerce` value,
    `coercible-*` terms and proofs, `level-of`, `prove-subterm`), the
    final expression in run position, and `let-match`'s scrutinee.
    `Env.bind` enforces the invariant as a backstop: a type or rule with
    an open meta is refused with "cannot infer the _ in ...", so any
    form that let one leak is caught where it leaks; the one exception,
    `~holes`, is a telescope under construction. A match annotation is
    elaborated with holes allowed, unified with the expected telescope
    (`solve_tele ~strict`) when there is one of the same length, and
    settled before the branches, so `(((List _) r))` and `((_ r))` are
    written forms of §2's `_`; a bare `_` in a type is a meta of type
    `Type` (`elab_term`, which now threads the environment for this).
    A typed `let`'s binders are likewise elaborated with holes and each
    value is checked against its binder's entry of that telescope rather
    than a second elaboration of the clause (`bind_one`; `bind-let`),
    so `(let (many (List _) xs) ...)` is solved by the right-hand side.
    In `self/` the two telescopes keep their metas' facts through
    `env-restore` rather than `env-discard`. Consequences: `(f _ (Nil _)
    xs)` is accepted, `(len _ (Nil _))` still refused at the call's paren
    (`tests/wild_open.sl`, `tests/wild_open_bad.sl`); a `_` in a
    signature is refused where its entry is bound
    (`tests/wild_sig_bad.sl`); an unsolved `_` at a let reads "cannot
    infer the _ in (Nil _)" now (`tests/wild_ambiguous_bad.sl`);
    `tests/wild_partial_ann.sl` and `tests/wild_partial_ann_bad.sl` are
    the annotation. Whether a meta solved inside a match branch may
    escape it was raised and left out at the owner's request.

## A proof-carrying prelude

Asked for by the owner in chat: the prelude's primitives should return
proofs of their specifications, CPDT-style, since a function that returns
a bare value is opaque to every later type (section 5 keeps calls out of
types, so a returned relation is the only channel). The owner decided
that the FFI adder returns an `Add` proof with a plain adder as a
`delegate` over it, that `double` is derived from it, that `trim` is
transparent, that `str-append` gets a relation, that `u8-add` gets the
specification sketched to them, and that levels should be used
judiciously with `_`. The names and the shapes below are the session's.

118. **Primitives return their relations; the old names are forgetful
     wrappers.** `add`, extern, returns `(erased (Add a b c) p)` beside
     the sum; `nat-mod`, extern over a structural model, returns the
     residue with `(Lt r c)` and `(Mod s c r)`, given `(Lt (Zero) c)`;
     `add-u8` is plain source over the two and returns a `U8Add`
     relating the three `U8`s' fields through `Add` and `Mod`;
     `append` returns an `Append`. `nat-add`, `u8-add` and `str-append`
     keep their names and one-value signatures as `delegate` wrappers
     (so `coercible-of` relates each to its primitive), chosen so that
     no test or `self/` call site changes; `u8-add` is therefore no
     longer extern and the FFI's `u8_add` is gone, `nat_mod` (`Z.rem`)
     taking its place. `double` is `(add a a)` with the erased lemma
     `add-diag-double`, so the modulus is eight FFI additions rather
     than unary doubling; `Double` stays as the relation the `Numeral`
     lemmas invert. `Add` is Coq's (`AddZero : Add (Zero) b b`,
     recursion on the first argument; the owner's choice over a
     second-argument variant that needed fewer lemmas), and
     `add-zero-right`, `add-succ-right` (Coq's `plus_n_O`, `plus_n_Sm`)
     and the inversion `add-succ-right-inv` are the lemmas the `Mod`
     step and `add-diag-double` need. `Mod s c r` is `ModLt` (already below `c`) or
     `ModSub` (one more `c` subtracted), with `mod-succ-lt` and
     `mod-succ-wrap` the two cases of the successor step decided by
     `nat-cmp`, whose `CEq` forces `c is (Succ r)`; `lt-asym` refutes
     the third. `mod-add`, `succ-mod`'s old form and `lt-pos` are gone.
     `trim`'s return is `(many s is t)`. `tests/prelude_proofs.sl` is the
     evidence.
119. **Levels in the prelude are anonymous** (`_`, SUGAR.md 1) and its
     calls bare (SUGAR.md 3), except `nat-lvl`, `u8-lvl`, `char-lvl`
     and `str-lvl`, which tests prove `Predates` against; the functions
     the tests reach through them (`nat-add`, `double`, `lt-dec`,
     `nat-cmp`; `u8-add`; `char-cmp`; `trim`, `str-append`) sit at
     those. Two things the session learned writing the lemmas, recorded
     as its reading: a lemma cannot recurse on a proof another lemma's
     call produced, since that is not a subterm of anything, so
     `add-diag-double` recurses on the `Nat` instead; and two lemmas at
     one level can only call each other under section 9's positional
     subterm discipline, so each lemma is its own `def-fns _` and calls
     the ones above it with an inferred `Predates`.
120. **`nat-cmp` is the extern comparison; `lt-dec` is derived from it
     and `Dec` is plain source** (the owner's decision, replacing item
     90). `Cmp` took `Dec`'s place as a tag-only extern type at first,
     since the FFI had to construct the result; since item 123 it is
     plain source and the FFI builds it through its constructor.
     `nat-cmp` sits at an anonymous level below `nat-lvl` so that
     `lt-dec`, which tests reach through `nat-lvl`, can call it; the
     lemmas are `lt-succ` (`Lt a (Succ a)`) for the `CEq` case and
     `lt-weaken` (`Lt x y -> Lt x (Succ y)`) for `CGt`. `Dec` is kept
     because the character-literal sugar (item 52) and the tests name
     it; whether it stays is a separate question. The one test that
     named `nat-cmp`'s level in a type, `tests/char_ops.sl`, now
     infers it. The extern set is `add`, `nat-cmp`, `nat-mod`,
     `bin-to-nat`, `trim`.
123. **An extern over a plain ADT takes that type's constructor or
     destructor; nothing is extern for the FFI's convenience.** The
     owner asked why `Cmp` was extern; the only reason was that
     `ffi.ml`'s implementations could build values of registered extern
     types alone. Now `Ffi.note` records every declared type by name
     (first declaration winning, so the prelude's), `Ffi_core.nat_cmp
     ~con` builds its `Cmp` through the interpreter's `construct`, the
     extracted code's `con_N`, or slc's runtime `Tag`, and
     `Ffi_core.indexed` is gone; `Cmp` is an ordinary tagged type, so
     its `Matchable` and `coerce`s between its instances go the ordinary
     way. This is the mirror of `flatten`'s `~des` (item 122), and the
     extractor's special case is now one table over both names, still
     by name since a post-erasure `fn` no longer has types. slc's
     compile-time interpreter runs `nat-cmp`'s model instead of an
     extern, since building a `Cmp` there would want the prelude's
     constructor descriptors, which its extern table does not have; the
     extracted programs and slc's emitter still use `ext_nat_cmp`, so
     only the comptime of a compiled program compares in unary, at most
     256 steps per character literal. The extern types are `Nat`, `Bin`
     and `String`.

## The compiler's libraries carry evidence

Asked for by the owner in chat, after a survey of `self/`: its proofs
were all termination-driven, and its library layer returned `Bool`s and
`Maybe`s that discarded what the checker could have used. The owner chose
the first three of the session's proposals — deciders return evidence,
lookups return evidence, lists carry specs — and left moving the
libraries into the prelude aside. Shapes and names below are the
session's.

121. **Deciders decide into the prelude's `Cmp`; lookups return
     `Hit`/`Miss` with proofs.** `bin-cmp` (formerly `core.sl`'s
     `bin-cmp-dec`, moved to `base.sl` with `BinLt`, `BinLe`, `le-refl`
     and `lt-le`) returns `(Cmp (Bin) BinLt a b)`, and `str-cmp` returns
     `(Cmp (String) StrLt a b)` over a new lexicographic `StrLt`, built
     on the prelude's `char-cmp`; `nat-cmp` and `char-cmp` are the
     prelude's. Every direct `(match (X-eq a b) ((BTrue) ..) ((BFalse) ..))`
     in `self/` became `(match (X-cmp a b) ((CEq ..) ..) (else ..))`, so
     the equal branch runs with `b is a` forced (58 sites, rewritten
     mechanically); `nat-eq`, `bin-eq`, `str-eq`, `char-eq`, `nat-lt`
     and `bin-lt` remain as `Bool` wrappers for the `and`/`or` chains,
     and `base.sl`'s `Ord` is gone. `idmap-get` returns `(Lookup V k m)`:
     `Hit` carries the value and a `MapsTo` proof, `Miss` an `Absent`
     proof; `mapsto-subterm` derives the subterm proof the emitter's
     recursion needs, replacing `MapHit` and `idmap-get-sub`. `nm-get`
     likewise returns `NLookup` over `NMapsTo`/`NAbsent`, through
     `nm-kid`'s `KidLookup` over `KidIs`/`NoKid`, the latter carrying
     `CharLt` evidence for each kid passed over. `list-nth` returns
     `NthLookup` (`Nth` or `OutOfRange`), `length` returns a `Length`
     proof with `list-length` its `delegate` wrapper, and `list-append`
     returns a `Concat` proof (its two sites bind it). `core.sl`'s own
     `Eq`, `Cmp` and `Plus` are gone in favour of the prelude's `Eq`,
     `Cmp` and `Add`, with `plus-zero-right` and `plus-succ-right` now
     the prelude's `add-zero-right` and `add-succ-right`. Not done: a
     `Vec` where a length is statically known — the one candidate,
     `check-args-go`'s arity mismatch branches, reports a count error
     that `check-arity` has already recorded rather than being
     unreachable, so replacing it with a refuted branch would change the
     messages; `list-mem-*` and `index-of-bin` still return `Bool` and
     `Maybe`, an absence proof for them wanting a `Bin` inequality the
     `Neq` in `core.sl` provides only after `base.sl`; and the fact
     table's `In`/`RuledIn`/`Taken` family, which resembles `MapsTo`,
     was left alone. `self/bootstrap.sh` is the evidence.

## `Rope`, and strings built in one pass

Asked for by the owner in chat: a prelude tree for string appends,
without length caching for now, and an FFI function flattening it to
one `String`, since `WriteFile` takes the whole file as one; the session
had noted that an `SCons` copies its tail, so building a string by
`append` is quadratic even under the FFI. Shapes are the session's.

122. **`Rope` is a prelude enum (`REmpty`, `RStr`, `RCat`, `RChar`) and
     `flatten` an extern over a structural model**, returning the
     string with `(Flat r s)`, a relation whose `RCat` case carries the
     two halves' `Flat`s and the prelude's `Append`; `append` is extern
     too now, a blit over its unchanged model. The FFI flattens in two
     passes, leaves then one buffer, walking the tree with an explicit
     stack (`Ffi_core.flatten ~des ~slice ~str`, parametric in how a
     value is taken apart so the interpreter, the extractor and slc's
     runtime share it). It is the first extern taking a plain ADT: the
     interpreter hands it `VCtor`s, slc's runtime its `Tag`s, and the
     extractor special-cases the name to pass the `Rope` type's
     destructor (`Extract.fn`). slc's `base.sl` drops its own `Rope` for
     the prelude's, `rope-str` delegates to `flatten`, `rope-io` is gone
     and `main.sl` writes its output as one string. `RChar`, a character leaf (the owner's
     question, the session's yes), is what anything built character by
     character uses: slc's tokenizer accumulates a word or a string
     literal as a rope of `RChar`s and flattens it once, where it used to
     cons each character onto a copied string and then reverse it, and
     `base.sl`'s `nat-str`, `bin-str`, `sanitize` and `ocaml-escape`
     build ropes the same way; `str-of-chars` and `str-rev-onto` are
     gone. The owner's alternative, an extern splitting a string at a
     position so tokens would be slices of the file, was set aside as
     needing a new FFI for the same linear cost. slc's compile-time
     interpreter turns a `Rope` value back into a prelude `Rope` and
     calls the prelude's `flatten` (`value-rope`, `eval.sl`), so its
     comptime path is the FFI's too; a first version joined the pieces
     with `str-append`, quadratic on a left-deep rope, which the owner
     caught. `tests/rope.sl` is
     the evidence, in both modes and extracted. Not done: length
     caching, which would want a `Length`-style proof beside the cached
     field; and `IO` still takes `String`s, the driver never seeing a
     `Rope`.

## Lockstep evidence

124. **Lists the elaborator walks together carry a `Lockstep` proof, and
     generated forms are built as raws.** At the owner's direction, from
     a review of where the compiler reports internal errors that a type
     could refute. `base.sl` gains `Lockstep A B xs ys`, that two lists
     have one length entry by entry, with `lockstep-trans` and
     `list-fit`, which cuts or pads a list to another's length and
     returns the proof. `open-tele`, `src-mults` and `spread` return the
     proof beside the list they build, and `elab-expr` mints one at its
     tail, where the count of results against the expectation was
     already decided: the results are fitted to the expectation with a
     `no-res` placeholder, the count error is reported exactly as
     before, and the proof is a fourth return that `elab-body` threads
     through. `first-res` and `erased-term` take the proof and refute
     the empty list, `bind-let` takes proofs for its results and values
     (composed from the binders' by `lockstep-trans`) and refutes both
     empty cases, `erased-in-many` walks under the proof, and
     `check-args-go` takes the proof relating the telescope to its
     metas, so the "internal: a parameter without its meta" error and
     the placeholders of `first-res` and `bind-let` are gone.
     `elab-body`'s `absurd` flag went with it: its two absurd sites apply
     `check-empty` to the returned results themselves, which the
     session reads as the same environment the flag acted on. `unary`
     and `distinct` build their generated forms as `Raw` values
     (`gen-of`, `bin-raw`) instead of text read back by the reader, so
     the "internal: a generated form does not read" error is gone by
     construction; the forms are the same s-expressions as before, at
     line 1 as the reader gave them. Not done: the sugar budget's zero
     case (111) stays reported. The session first thought a
     sugar-freeness relation on the generated raw could refute it, but
     the sugar forms are dispatched by resolving a head in the prelude's
     scope, not by its spelling, so such a proof would have to speak
     about that scope. The session's reading, not a proof, is that the
     case is unreachable anyway: both forms check their arguments are
     literals before spending the budget, no expression in a generated
     form has exactly two literal arguments, and the one statement's
     arguments are not literals. Also left: `bind-let`'s `tele`, whose
     empty case silently stops checking rather than reporting.
     `self/bootstrap.sh` is the evidence.

## Code indexed by its erasures

125. **Post-erasure code is indexed by the erasures of the values it
     produces.** At the owner's direction, the next item of the same
     review. `Code` in `core.sl` is `Code ms`, `ms` the list of
     multiplicities the expression was elaborated at: `many-one` for a
     variable or a constant, and for a function body, a let's right-hand
     side, a match's branches and the whole of `elab-expr`'s result the
     expectation they were checked against. The evaluator returns
     `Vals ms`, a value at each many position and nothing at an erased
     one. The lists a node holds in step with its index, a `values`'
     codes and a let's non-erased ids, carry an erased `Picked` proof
     that they sit at the many positions, so the evaluator binds a
     let's ids to its values, reads the one value of a scrutinee, a
     callee or a `values` entry, and spreads a run-position let's
     values over its binders without a dynamic check: `first-value`,
     the interpreter's "expected one value" and its "arity mismatch"
     for a let, and `spread`'s placeholder for a let are gone. What
     stays dynamic is fitted once at a boundary: the values a closure
     returns are cut or padded to the call's index by `vals-fit`, a
     closure's arity being a runtime property, and a constructor's
     fields and a closure's parameters still bind by count. A node that
     has to make values on its own, an erased position, an application,
     a match, `absurd` and an error, holds its list as data for that.
     The elaborator's dispatch returns `AnyCode`, code at whatever index
     its case has, and `fit-code` decides that index against the
     expectation at `elab-expr`'s tail, where the count was already
     reported, with `CError` at the expectation as the placeholder when
     they differ; a call's projection of many results onto an
     expectation with fewer takes a decided `Lockstep` and builds both
     `Picked` proofs. The normalizer's dropping of a `let` whose body
     returns its ids needed care: the right-hand side's index differs
     from the body's in erased entries, as `nat-add`'s `delegate` over
     `add` shows, so `returns-same` decides that the two lists agree on
     their many entries, returning a `ManySame` proof, and `recast`
     rebuilds the code at the body's index, which changes only the
     lists the nodes hold; for that, `CLet` and `MkFunc` carry their
     erasures as data. The emitter reads the same lists as before, and
     the extracted OCaml still builds and takes apart tuples by arity.
     The session's reading is that no message changed: every placeholder
     sits behind an error already recorded. `self/bootstrap.sh` is the
     evidence.

     Item 150 has since removed `Vals` itself: the evaluator returns the
     many values as a plain list with the index beside it as an erased
     `Picked`, because the two conversions at a call boundary described
     above -- `vals-fit` on the way out, the strip to a list on the way
     in -- were what kept the interpreter from reaching a call in tail
     position by a tail call. The `Picked` proofs on a node's lists, and
     everything else this item records, stand; `vals-fit` survives only
     where arity is genuinely dynamic and nothing recurses after it.

## Types travel with their terms

126. **The elaborator never reads a type off a term after the fact.**
     At the owner's direction, in place of the depth-indexed `Term`
     that had been the review's fourth item. An extrinsic scopedness
     proof beside each closed term was the plan, but a stored type's
     natural home is the fact table, whose `In` family indexes on the
     type a node holds, so the proof would have reached the proof
     family after all. Instead the one consumer that needed closedness,
     `infer`, is gone. `elab-term` returns the type it computes beside
     the term: a variable's from the table, a constructor application's
     by instantiating the constructor's return, a type former's `Type`.
     `check-args` returns the arguments' types beside their terms. An
     `is` entry's `SgIs` carries the type computed when the clause was
     elaborated, instantiated, abstracted and freed of metas along with
     its term but neither canonicalized nor unified, since it is read
     only when the entry is bound, where the table canonicalizes on
     read. The application result entry a `_` is solved against takes
     its type from the head's constructor, `ARApp` carrying the return.
     The proof helpers take the `Res` a proof came from. The session's
     reading is that every type this hands over is the one `infer`
     computed, a variable's being `type-of` and a constructor
     application's the same instantiation, so no message changes.
     `FrSIs` and the guard for an `is` entry gain the type as an erased
     index; nothing else in the proof family moved. The "dangling
     binder" case is not refuted but absent: no function reads a type
     off a term any more. `dangling` itself stays, deciding section
     18's third contradiction and whether a `_` may be solved against
     an `is` entry. `self/bootstrap.sh` is the evidence.

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
     in it, both `many` since the interpreter walks them; `VEnv ctx`
     holds one list of values per frame with an erased `Lockstep` to
     the frame's ids, so `venv-get` is total and the interpreter's
     "unbound at runtime" is gone, as are its `IdMap` and the id-keyed
     binding of a `let`'s values (`vals-frame` picks them from the
     `Picked` proof). `Func gids ctx` and `Group gids ctx` bind a
     body over its parameters, its group and the scope the group was
     defined in, and a `Closure` packs those; `Bound` in `elab.sl`
     carries the group's ids as an index so `define-fns` returns the
     group's `Lockstep` by construction. A Const entry's value is
     embedded with its entry (`CConst id v`, section 34's wording), so
     the top level binds no frame, a top-level closure captures
     nothing, and run position is the empty context: `elab-let`,
     `elab-let-match` and `elab-def-fns` run code or mint a top-level
     group only under a match on the context being `Nil`, where
     `run-code` takes `Code (Nil) ms`; the environment's run-position
     flag stays for minting states. For that to hold, every branch
     body sits under a frame, the `else` body under an empty one, and
     a match with no runtime discriminant, an erased scrutinee or an
     untagged type, is a `CMatch` with the new `ShNone` shape rather
     than its branch's bare body; the normalizer drops it when its one
     branch binds nothing. `StmtCode ctx ctx2` says what frame a
     statement pushes, and `elab-stmt` returns the context after it.
     The normalizer's substitution is a `Ren from ctx`, a frame of
     atoms (a variable with its place, or a constant) per frame of
     the source, weakened under each binder (`ren-weaken`), so a let
     whose right-hand side is atoms, variables or Const entries, is
     substituted away rather than resolved through an id map. A value
     elaboration embeds, a `matchable-of` or a nested `def-adts`'s
     binding, is `CValue`, which is no atom, so lib/elab.ml's three
     cases are kept exactly: a let of such values that nothing mentions
     is dropped by `strengthen`, which rebuilds the body one frame
     shorter and fails where a variable sits in that frame, deciding
     "mentions" by construction; any other let stays. A first version
     substituted every constant, which the owner questioned; the
     session then found the reference keeps a mentioned one and
     matched it, checked on probes the tests do not cover. A `projection` builds the places of
     its bound ids from `at-ins` before referring to them. The group
     frame holds the `many` functions of a `def-fns`; an erased one is
     checked and leaves nothing behind, as item 77 has it, `Bound`
     skipping it so the frame's ids and the group's `Lockstep` are by
     construction, and an empty group binds nothing (a first version
     bound erased members too, which the owner caught). What stays dynamic: the elaborator decides a
     variable's place with `mem-dec` when it emits it, and a `Dyn`
     entry it cannot place is an internal error at elaboration, so the
     invariant that the scope's non-erased entries are the context's
     is not yet in the types; a closure's arity and a branch's fields
     are still fitted to their frame by count (`bind-frame`), the
     second rung. The emitter reads a captured value by name through
     `venv-find`, which returns its place in the environment as the
     subterm the emitter's measure needs. `self/bootstrap.sh` is the
     evidence: the tests match and are refused as before, and the
     fixpoint holds.

## The FFI's names decided once

128. **An extern mark is decided into an enum where it is read, and
     the compiler dispatches on the enum from then on.** At the owner's
     direction, the second item of the same ladder. `core.sl` declares
     `Extern`, one constructor per implementation the FFI has with its
     arity as the type's index, `ExtType` for the three types it holds,
     and `SomeExtern` packing an `Extern` with its arity; `extern-of`
     and `ext-type-of` are the only functions that compare a name to
     the FFI's, called once by `elab-headers` and `define-adts` at the
     `extern` mark, where `claim-extern` reports the unknown name as
     before. `Func`, `Header`, `Adt` and `Ctor` carry the enum in place
     of the name, so the interpreter's `apply-extern` is one match on
     it, `ext-construct` one on the type, and the emitter recovers the
     runtime's `ext_` and `con_`/`des_` names through `ext-name` and
     `ext-type-name`; the `or` chains `is-extern-fn` and
     `is-extern-type`, the string chain of `apply-extern` with its
     unreachable `nat-cmp` arm, and `arg-at` are gone, `nat-cmp`'s
     running as its model at compile time being `apply-extern`'s `None`
     for `ExNatCmp` (item 120). What stays dynamic, since the second
     rung was set aside: the arguments reach an extern as a list the
     elaborator counted against the model's telescope, and
     `apply-extern` takes its one or two from that list, an absent one
     being the error value it was; the arity in the type is read back
     by `ext-arity`, whose return `is` the index, and the owner asked
     for the check at the mark: a model whose `many` parameters do not
     number the implementation's arity is refused with "the extern
     implementation of NAME takes N arguments, its model M", and the
     owner then had the reference refuse it too: `Ffi.arities` lists
     each implementation's arity, `Ffi.check_arity` compares it with
     the model's `many` parameters before the claim, and
     `tests/extern_arity_bad.sl` carries the message. `self/bootstrap.sh`
     is the evidence.

## Code built at the expectation

129. **Every case of the expression elaborator builds its code at the
     expectation.** At the owner's direction, the fourth rung of the
     same ladder. `elab-expr` returns `Code ctx expect` from each
     case rather than code at whatever shape the case had, so `AnyCode`,
     `fit-code` and the `mults-eq` decision at its tail are gone. A
     case producing one value, a variable, a constructor application, a
     `coerce`, a `matchable-of`, hands its `Code ctx (Cons pos Nil)` to
     `single`, which reads the expectation's shape and, under a proof
     `PosOf expect pos` that `pos-of` now returns beside the position,
     has the two shapes identical rather than compared; an expectation
     of another count gets a placeholder, its count being reported at
     the expression's end as before. A special form producing one
     value elaborates its argument at the position rather than at the
     expectation's first entry, which differ only where the count error
     has already been reported. A call whose returns lockstep with the
     expectation is always projected onto it, `needs-projection` being
     gone: the normalizer already turns a projection that repackages
     the call's returns in order back into the call, so a body's code
     is as before, and only run-position code carries the let. A
     `distinct` returns no code, its value being erased. The session's
     reading is that no message changes; `self/bootstrap.sh` is the
     evidence.

## A held Matchable over an untagged type

130. **`slc` read the discriminant of a held untagged Matchable.** A
     `many` match through a first-class `Matchable` of a union, or of
     an enum with one non-phantom constructor, compiled to a branch
     pattern carrying the constructor's discriminant, while the
     runtime's untagged `Mat` answers `0` for every value, so a real
     branch on any constructor but the first reached `absurd`
     (`tests/held_union.sl`; the reference and the compile-time
     interpreter both ignore the discriminant there, as
     `lib/extract.ml`'s `Held` case does). The emitter now writes `_`
     for the discriminant when the held shape carries no tag. The
     session's reading is that this is the only site that read it;
     the test is the evidence.

## The compile-time interpreter's values live in a store

Proposed by the session after measuring that `self/emit.sl` copied a
value at each reference and a function's group at each closure
reference, with the `is-top`/`func-top` shortcuts as its only sharing
(without them the self-compilation was 202 MB of OCaml), and agreed by
the owner in chat, who chose Nat addresses over Bin ones, weakening as
a coerce, and dropped a list of addresses the first version kept in the
heap. Everything below is the session's reading of that agreement and
of what the code does; `self/bootstrap.sh` is the evidence, and the
bootstrap runs in the same time as before (about four minutes here).

131. **A value is an address into a size-indexed store; a block holds
     section 38's representation with every address in it below its
     own.** `self/heap.sl` declares `Addr bound`, a Nat below the bound
     carried at runtime as its bijective spelling (the prelude's `Bin`,
     related by `Numeral`), and `Heap B size`, a Braun tree of blocks
     sized by its count: the LSB-first trie on the spelling, in which
     address 2k+1 is the one-child and 2k+2 the two-child of address k,
     so the spelling is the path and the size fixes the shape. `alloc`
     and `deref` are total by the size alone, the session's reading
     being that the lemmas over the prelude's `Double` and `Numeral`
     (`half-lt-one`, `half-lt-two`, `double-lt-inv`, `double-le-inv`,
     `numeral-step`) carry the arithmetic; the Bin appears nowhere but
     as the spelling, since the FFI's Nat has no digits. Widening the
     bound of an address, or of any holder of addresses (a list, a
     `Maybe`, an `IdMap`, the interpreter's frames, the environment's
     entries and finals), is a `coerce` whose proof an erased function
     builds by recursion, so it extracts to the identity; `Addr` needs
     no `newtype` mark for that (section 38's `coercible-ctor` with the
     erased bound differing). `core.sl`'s `Block a` is a tag with
     fields, a tuple of fields, a host payload, a held constructor, a
     Matchable, a group over the frames it closed, a closure as a group
     block's address and member index, the token, or an error; its
     addresses are `Addr a`, `a` its own address, which is what makes
     the emitter's walk a single pass in address order and lets every
     walker over values (the printer for section 15's message, the
     Rope read back for `flatten`) recurse on an erased bound that a
     field's smaller number refines, with no fuel that can run out.
     `eval` keeps its fuel; every step returns the grown store with an
     erased `Lt hs (Succ hs2)` by which the frames, the Const entries and
     the values in hand are widened. A group frame in the interpreter's
     environment holds the group block's address, and reading a member
     allocates its closure block, so `apply` re-closes nothing. Code
     holds no address: `CConst id` names the entry and is resolved
     through the entries when the code runs, and a value elaboration
     embeds (`CValue`) is a closed block allocated when reached. The
     environment carries the store with its size existential; since
     two reads of it cannot be typed as one size, every run-position
     statement that stores an address is one session in `eval.sl` or
     `core.sl` that reads the store out, runs or allocates, widens the
     entries and finals, sets the states and puts the store back
     (`env-run-let`, `env-run-final`, `env-close-group`,
     `env-set-fields`, `env-run-fields`, `set-state-closed`), and the
     elaborator itself never holds an address; `bind` takes no state,
     `bind-closed`/`bind-token`/`bind-erased` allocate afterwards, and an
     erased Const is a fresh token block. The environment's `values`
     map and the `Trace` are gone: the emitter marks what every Const
     entry and every final reaches, walking the addresses newest first
     (a block's addresses being below it, one pass suffices), then
     writes each marked block oldest first as `let a<path> = ...`, a
     group block as its members' `let rec` packed in a tuple that
     `member` projects from, and a Const in code as the name of its
     address; the addresses are enumerated from the counter at emission
     (`heap-addrs`), the heap keeping no list. `alloc` always allocates,
     as the reference's physical identity does; interning was set aside
     for now. What stays dynamic: a `BFn`'s member index against the
     group block found at its address (an error block on a miss), and
     that every `CConst` the code names has a Const entry when it runs
     and is emitted. Measured with an instrumented reference before the
     switch: slc's own sources allocate about 20k blocks at compile
     time, the largest test about 7k. Two printer issues surfaced by
     the switch, since a plain final now prints through the generated
     printer rather than from its text: its memo keyed types exactly and
     looped on a dependent type minting a fresh index per level, now
     keyed as `lib/extract.ml` does with a wildcard for variables minted
     during printing (`OpWild`); and a closure-valued plain final prints
     `<function NAME>` as the reference interpreter does.
132. **`sub`, `mul`, `div` and `divmod` are extern over `Nat`** (the owner asked
     for the low-hanging Nat arithmetic; the shapes below are the
     session's, chosen to mirror `add` and `nat-mod`, and open to
     change). `mul` is structural on its first argument and returns an
     erased `Mul a b c` beside the product, `Mul` being a new relation
     in the shape of `Add` (`MulZero`, `MulSucc` through an `Add` of
     the partial product and `b`). `sub` is exact, not truncating: it
     takes an erased `Lt b (Succ a)` as `nat-mod` takes its positivity
     proof, and returns the difference with an erased `Add b c a`, so
     no new relation is needed; a truncating subtraction is left to be
     written over `lt-dec` where wanted. `div` takes the same
     positivity proof as `nat-mod` and returns the quotient with, all
     erased, `m`, `r`, `Mul q c m`, `Add m r s` and `Lt r c`, which is
     the session's reading of what characterises the quotient; the
     model is a wrapper dropping the remainder of `divmod`, itself
     extern over the same model shape as `nat-mod` and `succ-mod`
     (`succ-div` steps the remainder against `c` with `nat-cmp`) and
     returning the quotient and the remainder both `many`, with the
     erased characterisation once. The reference FFI returns the pair
     as two values and the extracted body is `Obj.repr` of zarith's
     pair, which is the tuple a two-value `let` takes apart; the
     self-hosted interpreter's `apply-extern` now returns its
     addresses as a list over an existentially sized store, as
     `apply` does, so that `divmod` can allocate two payloads. `nat-mod` and its `Mod`
     relation stay as they were; whether `Mod` should be restated
     through `Mul` and `Add` is open. `nat-mul` is a `delegate` at
     `nat-lvl` as `nat-add` is. The implementations are zarith's
     `sub`, `mul`, `div` and `div_rem`; the interpreter of `self/eval.sl` runs
     the models, deciding the proofs with `lt-dec` and returning an
     error block where `sub` would go negative or `div` or `divmod` by zero, as it
     does for `nat-mod`. `tests/nat_arith.sl` runs each once at
     elaboration and once inside a thunk, so the extracted program
     exercises the implementations.
     The prelude also gains the lemmas `slc` needs to recurse on a
     quotient: `lt-trans`, `lt-le-trans` (moved from `self/heap.sl`),
     `add-le-left`, `add-lt-left`, `mul-lt`, `divmod-lt` (the quotient
     of a positive dividend by a divisor above one is below the
     dividend) and `lt-subterm`, which turns `Lt a b` on `Nat` into the
     `Subterm` the checker's decrease wants, by deciding `a` against
     the predecessor of `b` with `nat-cmp` in an erased position and
     chaining `prove-subterm` through `subterm-trans`. `slc` then uses
     the externs (the owner's request): `nat-sub` is `sub` under
     `lt-dec`, `nat-times` is gone for `nat-mul`, and `nat-str` and
     `bin-of-nat`, which counted up to the value one step at a time,
     divide by ten and by two under `divmod-lt` and `lt-subterm`, so
     a numeral's cost no longer grows with its value (measured: a
     literal of thirty million compiled in the time of a literal of
     three, where the count-up took seconds).
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
     extracted through its view as before; `--no-templates` strips them
     all, the test runner extracts every FFI-mode test both ways, `slc`
     takes the same flag as its first argument and `self/bootstrap.sh`
     compiles a subset without them. Held constructors and Matchables
     still go through the view (`tests/thunk_extern_first_class.sl`).
     The file is embedded in the interpreter by a dune rule and in `slc`
     through `header.sl`, one text parsed by both, though only the
     reference checks it. Measured in the session's scratchpad: the
     Ackermann benchmark 58 ms through the views, 35 ms through the
     templates, 24 ms hand-written on zarith; a million-iteration tail
     loop over `Nat` 21 ms to 6 ms; and the pinned `slc` self-compile
     32.8 s to 32.0 s, its time being in the String copying (item 132's
     profile), which no template touches.
     The `Bin` template tests parity and halves through `Obj.is_int` on
     the small-integer case, since zarith's `is_odd` is a C call with no
     fast path where `pred` and `shift_right` have one, and a zero test
     is physical equality with `Z.zero`, sound because zarith keeps
     every value that fits an `int` as an immediate (`z.mli`'s first
     lines); a walk over sixty million `Bin` digits went from 0.37 s to
     0.19 s with the parity fast path.
134. **The driver converts a `String` held as the FFI's slice to and from
     the host's string directly** (the owner's request, after a
     performance audit). `Driver_core.make` takes optional `of_host`
     and `to_host`; `lib/program.ml` supplies them when `String` is the
     FFI's slice, `lib/extract.ml` emits them when `String` extracts as
     an extern, and `self/emit.sl` always does, `slc`'s `String` being
     the slice; without them `of_string` and `to_string` fold over
     `scons` and `un_str` as before, which is what `--no-extern` gets.
     The folds consed a read file one `SCons` at a time, and under the
     FFI each `SCons` copies its tail, so a `ReadFile` of n bytes copied
     about n^2/2 bytes, every copy going to the major heap: measured on
     a pinned self-compile, 32.4 s to 3.8 s wall with 21 s of system
     time (heap compactions) gone, and a program echoing a 240 KB file
     from 17 s extracted and 565 s interpreted to milliseconds. What
     remains of the self-compile is elaboration (fact-table lookups,
     structural `bin-cmp`, the rules list); the session's audit report
     lists it.
135. **`Half` is an extern type over a `Nat`, and `nat-halve` the identity
     into it** (the owner's suggestion, during a probe of whether `slc`'s
     ids could be `Nat`s with the bijective spelling erased). `Half n`
     has the constructors `HZ`, `H1 m` and `H2 m` for n = 0, 2m+1 and
     2m+2, `m` at `many` with an erased `Double m d` fixing the index;
     `nat-halve` models it structurally and the FFI holds a `Half` as
     the `Nat` itself, matched and built through `Bin`'s views and
     templates (`lib/ffi.ml`, `lib/ffi_templates.txt`), so a trie keyed
     by a `Nat` can walk its digits at the cost `Bin`'s template has.
     `slc` carries it as `ExtHalf` with a `PHalf` payload in its
     compile-time interpreter. The probe (a `Nat`-keyed twin of
     `base.sl`'s `IdMap` with the same evidence, kept in the session's
     scratchpad, not the repo) type-checked with the spelling hidden and
     ran 200k inserts and lookups in the time of the `Bin`-keyed map;
     as an extern *function* returning a plain block it had been about
     20% slower. Whether ids become `Nat`s is not decided; nothing in
     `slc` uses `Half` yet.
136. **`Bin` is a plain type, and `slc`'s ids are `Nat`s** (the owner's
     decision: every use of `Bin` erased in `slc`, the conversion through
     `Half`). The prelude's `Bin` and `bin-to-nat` lose their `extern`
     marks, so the FFI holds no `Bin`: its views, its templates and
     `bin-to-nat`'s identity go, `Half` keeps the halving view under
     its own name (`half_view`, `half_of`), and `lib/literal.ml` spells
     a numeral through it. In `slc` an id is a `Nat`: `nat-cmp` compares,
     `Succ` mints, `nat-eq-dec` decides equality with `Neq` as the
     order either way, and every trie (`base.sl`'s `IdMap`, `heap.sl`'s
     store, `core.sl`'s fact table) walks the id's halves by
     `nat-halve`. The evidence is restated the way the probe of item
     135 did it: where a constructor's index was `(B1 k)` it is
     `(Succ d)` with an erased `Double k d` field beside `k`, `(B2 k)`
     is `(Succ (Succ d))`, `(BZ)` is `(Zero)`, `Numeral` fields drop
     since the key is the number, and `BinLt`/`BinLe`/`Neq`'s digit
     lemmas become the prelude's `Lt`. A branch the digits refuted by
     shape is refuted by `double-parity`, and two keys under one digit
     meet through `double-inj`/`double-fn`. The `Bin` type still spells
     numerals into their `Numeral` proofs in `elab.sl`, as a plain
     enum. Measured on the compiler's own sources with the machine
     idle: the previous `slc` 3.9 s, this one 3.1 s; the emitted OCaml
     names ids in decimal (`v1234_length`) and the self-compile's
     output shrinks from 1.02 MB to 0.74 MB. Gate: dune test 253
     passed; bootstrap 175 matched, 103 refused, fixpoint reached.
137. **Four string externs: `str-cmp`, `str-length`, `str-split` and
     `nat-str`** (the owner's decision, with the caller supplying
     `str-split`'s bound). `str-cmp` decides `StrLt`, the lexicographic
     order by character code that was `slc`'s, into `Cmp` as `nat-cmp`
     does, its model the structural comparison; `str-length` returns
     the length with a `StrLength s n` relation; `str-split` takes the
     string, a count `k`, and erased `StrLength s len` and
     `Lt k (Succ len)`, returning the first `k` characters and the rest
     with `Append a b s` and `StrLength a k`; `nat-str` spells in
     decimal, its model the division by ten `slc` had, with the digit
     characters built by reflection since the prelude uses no literals.
     The implementations are a byte comparison of the two slices, the
     slice's stored length, two sub-slices, and `Z.to_string`. `slc`
     drops its own copies, and its tokenizer cuts a word out of the
     source with `str-split`, carrying `Add k rl len` (characters taken
     plus remaining) so `add-le-left` gives the bound, where it used to
     accumulate a rope of characters; a string literal still does, for
     its escapes. Measured on the compiler's own sources with the
     machine idle: no change (3.15 s before, 3.2 s after, within the
     noise), as the audit expected of these. Gate: dune test 253
     passed; bootstrap 175 matched, 103 refused, fixpoint reached.


## Opening a `Matchable` or `Newtype` (DESIGN.md section 19)

Implemented from proposals/matchable-newtype-opening.md, since folded into DESIGN.md section 19, as the owner settled it in chat, on this
branch afresh rather than by merging `claude/matchables-proposal-ekulyk`,
whose implementation predates the `_` metas and the evidence-carrying
`self/`. The owner decided the points marked so; everything else is the
session's reading, with the tests as the evidence.

138. **A `let`'s right-hand side statements are statements of the
     enclosing expression** (the owner's decision in chat, proposed by
     the session while placing an open's extent). Everything a
     right-hand side binds enters the expression after the `let`,
     anonymously: the entries keep their ids in scope with their names
     dropped (`Env.hide`; in `self/`, `env-hide` keeps the inner
     objects and clears the added entries' names), so no fact, and no
     open record, outlives an entry it mentions, which is what item 29
     had excused. A `many` binder there stays `many`, the owner's rule,
     which the code composition makes honest: the statements before the
     right-hand side's final expression wrap the `let`'s own binding
     (`Elab.elab_stmts`; in `self/`, `elab-stmts` and the `SSeq` code a
     `let` returns), so their code is emitted whether or not the `let`'s
     binders are erased, and only the final expression is the position
     section 20 calls the right-hand side. Run position is unchanged,
     nested statements having run first (section 16).
     `tests/let_nested_scope.sl` still refuses the name; the entry's
     survival is what `tests/open_adt_let.sl` reads.

139. **Nothing consults a `Matchable` or a `Newtype` until it is opened**
     (`Env.opens`, `Elab.open_adt`, `Env.merge_opens`; in `self/`, the
     `Env`'s `opens`, `open-adt` and `merge-opens`). The environment
     carries the opened entries beside the fact table, and they share
     its fate: a match branch's are discarded with the branch, a `let`
     right-hand side's kept (item 138). The invariant, the owner's
     choice over the proposal's merge-at-open: at most one opened
     `Matchable` names a given type constructor or value constructor,
     and at most one opened `Newtype` a given constructor, canonically;
     two that would name one thing are unified, forcing, and the
     better-ranked entry kept, the older on a tie, until no two name one
     thing, and a contradiction anywhere in that cascade is the
     forcing's. The invariant is restored after every forcing, a branch
     entered (`Elab.refine`), a `let-match` or `comptime-match` as much
     as an open, rather than inside the unifier, which the session
     reads as equivalent for what is accepted (every equation is
     canonicalized before its atoms are compared, and an opened
     Matchable's constructor list is read canonically) and which keeps
     `self/`'s unifier and its termination evidence untouched; the
     unifier's own check that two aliased type constructors head one
     Matchable is subsumed. `(open-adt mult e)` is a statement, the
     owner's shape: an anonymous `let` of `e` at the written
     multiplicity, checked as a `let` binder is, run at once in run
     position so the entry is `Const` and bound by code otherwise, then
     the open of that binder, whose constructors must be distinct after
     canonicalization (`tests/open_adt_bad.sl`) and which then merges
     with whatever open names one of them or its type constructor
     (`tests/open_adt_unify.sl`, `tests/open_adt_clash_bad.sl`,
     `tests/open_adt_expr.sl`, `tests/matchable_prefers_many.sl`,
     `tests/known_matchable.sl`, `tests/open_adt_mult_bad.sl`,
     `tests/open_adt_not_bad.sl`). A match that dispatches at runtime
     reads its Matchable's value, stamped in where the entry is `Const`
     with its ADT and read from the entry's binding otherwise, so it
     requires the opened entry to be *readable*: `Const` with the ADT,
     or non-erased and still bound (`Env.readable`; in `self/`,
     `readable` reads the objects list, which `env-hide` keeps).
     Readability is judged at the match, not the open: a `many`
     parameter opened at `erased` serves no such match
     (`tests/open_adt_erased_bad.sl`), while an open inside a `let`'s
     right-hand side does, its entry staying bound (item 138,
     `tests/open_adt_let.sl`). `(open-absurd e ann)` is an expression
     of its annotation's size, `_` reusing the enclosing telescope as a
     match's does (`Elab.result_tele`, shared with `match`); it takes
     `e` at `erased`, the owner's choice, requires the same open to
     contradict, records and mints nothing, and compiles to the absurd
     code (`tests/open_absurd.sl`, `tests/open_absurd_clash.sl`,
     `tests/open_absurd_bad.sl`). Every read of a `Matchable` goes
     through the opened list: `match`, `let-match`, `comptime-match`,
     the emptiness check, `matchable-of`, `newtype-of`, `coercible-wrap`
     and section 18's disjointness rule, so an unopened first-class
     `TyCtor` unifies with any other (`tests/open_tyctor.sl`,
     `tests/unopened_matchable_bad.sl`,
     `tests/unopened_newtype_bad.sl`, `tests/open_adt_branch_bad.sl`).
     `def-adts` and the built-in `Special` open what they mint. Section
     19's ambiguity error is gone, two opened Matchables for one type
     being one. The keywords are the owner's: `open-adt` names the
     minting site, one form opening both objects, and `open-absurd`
     carries the token that marks a contradiction elsewhere. The
     first-class tests gained an `(open-adt m)` at their parameter's
     multiplicity, and "has no Matchable in scope" became "has no
     Matchable open", likewise for a Newtype.

140. **A `Newtype` is recorded, not asserted, and has no contradicting
     form** (the owner's choice, from the proposal's unsettled list).
     `open-adt` on a `Newtype` merges it with an opened one naming the
     same canonical constructor and checks nothing else; `open-absurd`
     on one is refused as undecided
     (`tests/open_absurd_newtype_bad.sl`). Still open, as the proposal
     lists it: whether an opened `Newtype` for `C` beside an opened
     `Matchable` marking `C` phantom is a contradiction. `coercible-of`
     keeps its fetch from ambient scope for now, the owner's decision,
     recorded as a TBD in DESIGN.md section 38.

141. **`coercible-ctor` no longer refuses a phantom constructor**, so it
     reads no `Matchable` and needs none opened
     (`tests/coercible_ctor_phantom.sl`). The owner's decision, on the
     session's reading that the check was redundant: a `coerce` cashes a
     proof only for a non-erased source canonicalizing to `(C ...)`,
     and the checker never lets a phantom constructor head a non-erased
     value, a phantom application in a non-erased position being
     refused and a phantom branch under a `many` scrutinee checked with
     everything erased, where a `coerce` yields an erased value, which
     a phantom constructor may head. `coercible-wrap` is the contrast:
     its source is the field, from which it manufactures a `C`-headed
     value, so its `Newtype` stays load-bearing. Section 38's "the same
     non-phantom constructor on both sides" then describes what a usable
     proof relates rather than what the form checks.

142. **`let-match` applies `match`'s readability check.** A `let-match`
     at `many` outside run position compiles to a one-branch dispatch
     that reads its Matchable at runtime, and before the opening it did
     so through an erased first-class Matchable, which elaborated and
     then failed when run (`tests/let_match_erased_bad.sl`, found by
     the session that wrote the other branch). Both forms now refuse an
     opened entry that is not readable (item 139) with one message, "is
     erased or out of scope". In run position a `let-match` destructs
     through the constructor's `Const` value and reads no Matchable, so
     it is not checked there. That `let-match` is a match for this
     purpose is the owner's.

## More IO requests (section 16)

Asked for by the owner in chat, as a batch to prepare and then add:
environment variables in Java's two shapes, appending to a file,
reading what is left of stdin, listing a directory in Java's shape,
the working directory, and one query for what a path holds. The owner
then asked for `MkDir` and the two deletes as well, after the session
reported that without them a test had no way to build a directory to
list. The owner chose the general `Pair`, sorted listings, the `world`
for the environment and the working directory, single-level `MkDir`,
deletion that reports `Unchanged` rather than failing on an absent
path, and the `unix` dependency; the shapes below are the session's.

143. **Ten more requests join `IO`**, each in item 56's shape: `GetEnv`
     answering `(Maybe (String))` and `GetEnvs` `(List (Pair (String)
     (String)))`, `AppendFile` and `ReadRemaining`, `ListDir` answering
     `(Result (List (String)))`, `GetCwd`, `Stat` answering `(Result
     (EntryKind))`, and `MkDir`, `DeleteFile` and `DeleteDir` answering
     `(Result (Change))`. Three prelude types come with them. `Pair` is
     general rather than an environment-specific record, the owner's
     choice over a two-field `EnvVar`. `EntryKind` (`IsFile`, `IsDir`,
     `IsOther`, `Missing`) makes absence an ordinary answer and keeps
     `Fail` for a path the driver could not read at all, on the reading
     that a program checking whether something is there is not handling
     an error. `Change` (`Changed`, `Unchanged`) is shared by the three
     requests that ask for a state rather than an action, so that one
     answer says both that the request was met and whether this call is
     what met it; the session's argument for it, which the owner took,
     is that `mkdir` is atomic, so collapsing the two into a plain
     success would throw away the only race-free way to learn which
     caller created a directory, while failing on an existing one (as
     POSIX and Java 6 both do) would make the ordinary case awkward.
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
     `WriteFile` already were. The harness runs an extracted program
     under `env -i` with the same variables, so the interpreter's world
     and the compiled program's agree on what a program reads; the
     working directory is the real one in both, which is why
     `tests/io_stat.sl` asks `Stat` what `GetCwd` named rather than
     printing it. `ReadRemaining` reuses the world's stdin field, which
     is renamed `read_rest`: for `bin/main.ml` and for an extracted
     program the field was already `In_channel.input_all stdin`, which
     is what the channel has left, while the test world returned the
     whole input however much `read_line` had taken, so the test world
     now drains its pending lines instead. The session checked the two
     against each other across trailing newlines and blank lines before
     relying on it.

145. **The driver uses `unix` rather than `Sys` alone.** The owner
     first chose the stdlib, to avoid the dependency, at the price of
     `IsOther`, since `Sys.is_regular_file` arrived only in OCaml 5.1.
     Implementing it turned up a second price the choice had not been
     weighed against: `Sys.file_exists` answers false for a path whose
     parent denies access exactly as for an absent one, so `Stat` would
     have reported a denied path as `Missing` and its `Result` would
     have had no reachable `Fail` at all. On that the owner took the
     dependency. The classification now reads the errno: `ENOENT` is
     `Missing` for `Stat` and `Unchanged` for the deletes, `EEXIST` on
     a directory is `Unchanged` for `MkDir`, and anything else is a
     `Fail` carrying the message. `MkDir` is the one that still asks a
     second question, whether what is in the way is a directory, so its
     `Unchanged` is the one answer here that a concurrent change could
     in principle turn into the wrong report; `Changed` never can, being
     the syscall's own success. Extracted programs, the bootstrap and
     the benchmark compile with `-package zarith,unix`.

## Every request but Exit carries a function (section 16)

Asked for by the owner in chat: every `IO` entry except `Exit` should be
a function, possibly nullary, and an entry that does nothing should join
them, named `Step` unless a better name turned up. The owner proposed
the in-language helper that thunks a value rather than an anonymous
function form, and accepted the extra verbosity at the call sites; the
rest below is the session's.

146. **`WriteOut` and `WriteErr` carry `(Fn L -> (many (IO L) next))`**
     rather than the next `(IO L)` outright, superseding that part of
     item 56, and `Step` joins them with the same field and no effect of
     its own. Every constructor but `Exit` then reads as one signature —
     arguments, an answer type, and a continuation from the answer to
     the next request — with `WriteOut`'s answer type empty rather than
     absent. The driver gains `apply0` beside `apply`; a nullary SL
     function extracts to an OCaml `unit -> _` (`lib/extract.ml`'s
     `params`), so both back-ends apply one directly.

     What the change buys beyond uniformity is that a loop no longer
     needs a request that answers. Before, `(WriteOut L t next)` wanted
     `next` already built, so a self-referential one would have had to
     call itself: a same-level call with no decrease, which the checker
     refuses. Passing a function instead defers the next request to the
     driver, so an output-only loop is writable, as is a silent one
     through `Step` (`tests/io_step.sl`). The termination discipline
     does not move: the continuation is a closure at the IO level, which
     comes after the looping function's own level, so no SL function may
     call it, and the unbounded iteration is still the driver's (item
     56). One consequence is worth naming: a program may now diverge
     with nothing observable, where before it had to read or write to
     keep going. That is not new unsoundness, the driver's loop having
     been unbounded from the start, but it is a new observable
     behaviour.

     The uniformity is less than it looks for a walk over `IO` written
     in SL. Nothing here abstracts over a telescope, so a nullary
     continuation and a unary one are different types, and
     `tests/io_lift.sl` needs `lift-fn0` beside `lift-fn`: the walk goes
     from three shapes to two, not to one. What does collapse is the
     driver's side and the reading of the type.

147. **`thunk` is a prelude function rather than a form**: it takes a
     value and returns a nullary function holding it, at any type and
     any level, so a call site writes `(thunk (predates p) _ _ e)` where
     a bare `e` used to sit. The owner preferred this to an anonymous
     function expression, which would have been the larger language
     change. It is general rather than IO-specific, nothing about it
     being particular to `IO`; its body is the captured value alone, so
     the closure it returns needs no `Predates` proof of its own, and
     `def-fns` accepts the erased level parameter as the level to define
     at, which the session checked before relying on it.

     Reaching `thunk` at a level `L` needs `Predates thunk-lvl L`, which
     a caller holding `L` only as an existential cannot mint for itself,
     `prove-predates` wanting a level minted by `def-lvl` with the other
     in scope (section 8). That is section 31's factory rule rather than
     a limit on `thunk`: the relation is established where the level is
     minted, so a function that mints a level and hands it back returns
     the relation with it, as `lift2` in `tests/io_lift.sl` now returns
     `Predates thunk-lvl B` beside `B` and its coercions. A session
     first recorded this as `thunk` being unreachable at such a level,
     with a named nullary function in its place; the owner doubted it,
     and the doubt was right.

## The emitters' walks over the store (sections 16, 34)

148. **The emitters walk the compile-time store in tail position.**
     `slc` refused three of the `mini/` end-to-end tests
     (`mini_dependent`, `mini_recursion`, `mini_axioms`) with an OCaml
     stack overflow under the default 8MB limit, which HANDOFF and
     TOOLING-WISHLIST 15 had placed in the compile-time interpreter.
     Backtraces at the overflow put it in the emitter instead, reached
     after `main.sl`'s `compile` has run every file and found no error:
     `emit-blocks` (`self/emit.sl`) and `addrs-from` (`self/heap.sl`)
     each stepped once per address the store holds, the recursive call
     sitting inside a `Cons` or an `rcat`, so the stack held a frame per
     compile-time allocation — 157418, 162987 and 665800 blocks for the
     three, against 44797 for `mini_elab`, which passed. Both take an
     accumulator now and are marked `tail`, so the elaborator checks the
     property rather than it holding by accident; `heap-addrs` hands its
     addresses back newest first, the order `mark-pass` already wanted,
     and `emit-program` reverses once for the two passes wanting them
     oldest first. Believed semantics-preserving — the accumulated rope
     should flatten to the same string and the reversed list hold the
     same addresses — with the evidence being that all 193 test
     programs' emitted OCaml is byte-identical to what the old code
     produced with the stack raised, `slc`'s own output differing only
     as its own sources changed. The three then compile under the
     default limit, and the largest one's requirement falls from between
     32MB and 64MB to about 256KB.

     `lib/extract.ml`'s sharing table was the same shape of fault.
     `Hashtbl.hash` reads a bounded prefix, so every suffix of a long
     self-similar value shares one bucket, and `Hashtbl.find_all`'s scan
     of that bucket is not in tail position; the bucket is now a list
     scanned by `List.find_opt`, which is, and extracting a 20000-deep
     list needs 2MB rather than 4MB with unchanged output. Two things
     there are untouched and open, neither of them failing anything
     today: `value`/`plain` still recurses once per node of the value it
     walks, which an accumulator cannot fix and an explicit worklist
     could, at the cost of reordering the `shared_N` definitions it
     emits; and the lookup is linear in its bucket, so extracting such a
     value is quadratic in its depth (measured at about 2.6s, 8s, 46s
     and 237s for 5000, 10000, 20000 and 40000 elements). A deeper hash
     would not help the second, the suffixes of such a value differing
     only in length.

149. **Forcing a rule onto an atom then unifies the atom's type with its
     term's.** The owner's decision, in chat, for the minimal language
     (`mini/unify.sl`'s `UAssign`), after a session found that without
     it an atom of a former's type could be given a term of another type
     and a later telescope had no type for an `is` entry mentioning it
     (`tests/mini_untyped_rule.sl`; that program is also refused by
     item 80, restored to `mini/` at the same time). Whenever forcing
     gives an atom a rule, the atom's type is then unified with the type
     of the term it now rewrites to, as the next equation; an atom
     aliased to another is the case of this that item 89's signature
     check already covered, and the type equation a branch entry forces
     (section 18) follows from the scrutinee's, so `mini/`'s `Refine`
     forces the one. `lib/` and `self/` still assign with no type check,
     and unify signatures only where both atoms' types are formers
     (item 89); whether they should follow, and whether under item 80 the
     added equation can ever change an outcome, are open, in the
     session's reading.

150. **The compile-time interpreter reaches a call in tail position by a
     tail call.** At the owner's request, who asked that `slc`'s
     compile-time evaluation not grow the stack, or at the least that
     interpreting a tail call be a tail call. It was neither: a
     `tail`-marked countdown of 60000 steps run at elaboration
     overflowed the default 8MB stack, which is the standing exception
     HANDOFF and `self/README` record. Reading the emitted OCaml showed
     `eval`'s `CLet`, `CLetRec` and `CMatch` already reaching their
     continuations by a tail call, the normalizer (item 125) having
     dropped the `let` that bound them; the only two that did not were
     the two that converted between representations. `eval` returned
     `Vals ms` and `apply` a plain list, so `CApp` fitted `apply`'s
     result to the call's index afterwards and `apply` stripped
     `eval`'s result to a list afterwards, and each conversion held a
     host frame per interpreted call.

     Both now carry the same values. `eval` and `apply` return the list
     of many results together with an erased `Picked` reading it back
     against the index, so what was a conversion is a proof rather than
     data and `Vals` is gone from `core.sl`. Where a call's index and
     the member's declared returns differ -- they differ in erased
     entries, as item 125 records for the normalizer -- `apply` decides
     `ManySame` before the body runs, by a new `mults-same` whose
     recursion is lexicographic on the two lists, and `picked-same`,
     which `core.sl` already had, carries the proof across afterwards;
     being erased, it does not disturb the tail call. A new
     `picked-lockstep` derives the `Lockstep` a `let` needs from the two
     `Picked`s, in place of `vals-frame`; `vals-one` refutes the empty
     list from its `Picked` rather than from the shape of `Vals`; and
     `eval-picked` builds its `Picked` as it walks. `vals-fit` survives
     only where arity is genuinely a runtime property and no recursion
     follows it: an extern's results, a constructor's one value.

     A tail call in interpreted code now costs no host stack. 400000
     compile-time iterations run in a 256KB stack where 60000 overflowed
     8MB, and what bounds them is the interpreter's fuel (`eval-fuel`,
     1000000, two per interpreted call), which reports "out of fuel" as
     a value at about 500000 calls rather than killing the process; the
     session did not change that constant. A non-tail call in
     interpreted code still holds host frames, as it must without the
     heap-allocated continuation TOOLING-WISHLIST 15 once wanted;
     measured, it reaches about four times the depth it did, the removed
     conversions being part of what each frame held. `self/bootstrap.sh`
     is the evidence that nothing else changed: 201 programs match the
     interpreter, 114 are refused with the expected message, and `slc`
     reaches its own fixpoint. `tests/comptime_tail.sl` is the guard,
     and it discriminates: the `slc` from before this item refuses it
     with a stack overflow. Its 131071 iterations decrease an *erased*
     `Nat` tied to a non-erased binary counter by the prelude's
     `Numeral`, which is what keeps the loop from building a unary
     `Nat`; a first draft counted a `Nat` down instead and wanted 80MB
     under `--no-extern` against 7MB with the FFI, where this one costs
     7MB either way. The owner suggested that shape. The `bench/` samples are unchanged within
     noise, with `comptime_garbage`'s minor words down about 4% and its
     resident size from 11MB to 9MB.

     Two things this did not touch, neither of them new. `lib/eval.ml`
     needed nothing, and reading it afterwards is what shows this item
     to be `slc` catching up rather than breaking new ground: its `eval`
     and `apply` both hand back a plain `value list`, so `CLet`,
     `CLetRec`, a match branch, `CApp`'s `apply` and `apply`'s own
     `eval` are already OCaml tail calls, and the reference runs four
     million compile-time tail-recursive steps in a 256KB stack. The
     `Vals` index of item 125 is what had put a conversion on either
     side of `slc`'s call boundary; the reference never had one.
     (An earlier draft of this item said the reference grew its stack
     too, at about twice `slc`'s old depth. That was the same
     misattribution TOOLING-WISHLIST 15 records: the program measured
     returned a 200000-deep `Nat`, and the overflow was
     `Ffi_core.nat_view` unfolding it into unary Peano form to print
     it, with `eval` nowhere in the backtrace.) And `self/eval.sl`'s
     `apply-extern`
     returns `None` for `ExNatCmp` and `ExStrCmp`, the two externs whose
     result is a `Cmp` rather than a payload (item 123), so `slc` runs
     their source models at compile time; `nat-cmp`'s recurses once per
     unit of the smaller argument, with the recursive call in a match
     scrutinee, so `(nat-cmp 200000 200000)` alone overflows `slc`'s
     stack where the reference answers at once. That is a non-tail
     recursion in the model being interpreted rather than in the
     interpreter, and this item leaves it as it was; whether
     `apply-extern` should build a `Cmp`, as `lib/ffi.ml` does through
     the type's constructor, is open.
