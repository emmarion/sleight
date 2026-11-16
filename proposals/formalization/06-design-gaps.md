# 06. Where DESIGN.md is silent or gives a choice

A Claude session's findings, written overnight at the owner's request.
Each item is a place where a formal specification would have to say
something that DESIGN.md does not say, or where DESIGN.md's text gives
an implementation a choice. Each ends in a question. None is answered
here. Quotes are DESIGN.md's, with section and line numbers, and this
session checked each against the file.

`evidence/A5-design-audit.md` is the full audit by a sub-agent: every
sentence of DESIGN.md that bears on the run or on acceptance, 22
questions, 14 pairs of passages that pull against each other, and the
searches behind each claim of silence. Its author checked its 425
quotations by script. The items below are the ones this session judges
most formative, with the audit's item in brackets. The audit found
none of them listed in DECISIONS.md, which is empty, and only two
touched by OPEN.md (items 14 and 36B there).

Items keep their numbers; a removed item leaves a gap.

## G1. Acceptance can turn on the answer of a compile-time `slot-eq` [C3]

§67, lines 3044 to 3046: "`ESome` proves that `a` and `b` hold one
word (§38). `ENone` proves nothing, so an implementation may always
answer it, and which one a call answers may differ between runs."

§28, lines 1208 to 1210: "`(comptime-match m x (C f1 ... fn))`
asserts, at elaboration time, that `x` is a `Settled`, non-erased
value headed by `C`. It is an error otherwise."

`slot-eq` runs in run position, and its result can be the scrutinee of
a `comptime-match`. `spikes/gaps/slot-eq-asserts-some.sl` is:

```scheme
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(let ((many z)) (MkBox 5))
(let ((many r)) (slot-eq (slot-of z) (slot-of z)))
(comptime-match many r (ESome _ e))
7
```

The reference implementation, with and without `--no-extern`, and
`slc --interpret` all accept it and print `7`. All three reject
`slot-eq-asserts-none.sl`, the same file asserting `(ENone _)`, with
"`comptime-match`: expected `ENone`, got `(ESome _ _)`". An
implementation that always answered `ENone`, which §67 allows, would
do the opposite on both files. So, on the text as it stands, whether
these two sources are accepted is not a function of the source.

Consequences for the theorems of 01: "never both" (T4) cannot hold of
the full language as stated, and a specification of acceptance has to
say where the answer comes from (02, R6).

Question: should a `slot-eq` that runs at compile time be pinned (for
instance, to answer `ESome` exactly when the words are one word), or
may acceptance depend on its answer?

## G2. The order of evaluation among siblings [C2, D2, D10]

02, section 2.3, quotes the text. No sentence fixes the order among
the arguments of one call, between a head and its arguments inside a
body, among the entries of one `values`, or among the items of a
`cell-write` or `cell-alloc`. That the statements of a body run in the
order written is presupposed by §61 and not stated. §15's placement of
argument temporaries has two readings (02). §29, lines 1241 to 1242,
cites §15 for "the elaborator's own binders for its head, arguments
and scrutinee", and §15 gives binders to arguments only.

The order matters to what a user sees. 02, section 2.7, reports
accepted programs whose output depends on it, through what is written
before a failure and through the answer to a `Measure` request; that
the same form runs in one order inside a function body and in another
at the top level, in both implementations; and one accepted program,
`spikes/order/cell-write-operand.sl`, for which the reference prints
"measured BEFORE the build" and slc prints "measured AFTER the build".

Question: decision D4.

## G3. Whether words are part of what the language means [C1, D8]

§33, lines 1459 to 1460, introduces the representation as "a
requirement on the implementation". §35 to §38 and §67 treat words as
things a program holds, compares, and proves facts about: `(slot-of x)`
"takes the multiplicity of its position" and "Its word is the word of
`x`" (§35, lines 1574 to 1575); `ESome` "proves that `a` and `b` hold
one word" (§67, line 3044).

Question: is the representation of §33 part of the specification's
run (decision D3), and if so, which of the points G4 to G6 does the
specification fix?

## G4. What a function value's word is, and when a closure is made [C10]

§29, lines 1247 to 1248: "a function's value is its compiled code".
§32, line 1327: "A function defined by `def-fns` is a closure over its
scope." §33, lines 1488 to 1489: "The pointer of a `delegate`-bodied
function is its callee's pointer (§19)." §39, lines 1864 to 1865: "an
at-function compiles to a function that does nothing and returns no
word."

`(slot-of f)` is the word of `f`, and `slot-eq` compares words. OPEN.md
36B already notes, of `fn-same`, that "two closures at one word can
differ in what they capture or pass erased".

Question: when a `def-fns` inside a body runs twice, are its functions
one word or two? Is the word of a function with nothing to capture the
same each time?

## G5. Addresses: fresh, shared, reused [C9, D12]

§36, lines 1696 to 1698: "Neither does canonical equality: two
separately built cells with equal contents are `is`-equal and are two
blocks." §37, lines 1736 to 1738, puts a `cell-alloc` of a fieldless
constructor "at that tag slot, or at `vacant-slot`", so two such cells
are one word and no block; the first sentence must be about cells with
a non-erased field, and does not say so. §36, lines 1701 to 1702:
"address equality does not change when contents do." No sentence says
whether an address is ever reused, or whether two values built
separately at `many` with equal contents may be one block.

Question: is every allocation of a block fresh in the run and never
reused, so that an implementation may not share equal immutable
blocks? The handoff's proposal B says so and has no reply yet.

## G6. Details of the representation [C18, D3, D4]

- §33, lines 1464 to 1465: "A value is the tuple of its constructor's
  non-erased fields; a single field is stored bare." Lines 1481 to
  1483: the newtype representation is "forbidden for a type that is
  not marked: an unmarked type of newtype shape is a block (§37)".
  Read alone, the first says what the second forbids.
- §33, lines 1470 to 1475, gives the word of a value with no
  non-erased field as a position word "when its type is tagged", which
  does not exclude an `extern` type; §35, lines 1591 to 1592, gives a
  tag slot only to a type "not marked `extern` or `newtype`".
- §33, line 1475: "an unspecified word otherwise". §45, lines 2236 to
  2237, leaves to the implementation "How a `Nat`, `Char` or `String`
  is held at runtime". `slot-eq` can be asked of such words.
- §42, lines 1933 to 1935, makes `Special` "an enum with one `many`
  nullary constructor per special form" and gives the constructors no
  order. A program can observe the order. `spikes/gaps/` has three
  four-line files: one asserts that `let` is at tag slot 0 and is
  accepted by both implementations; one asserts the same of `match`
  and is rejected by both; one asserts that `match` is at tag slot 26
  and is accepted by both, and rejected by the reference under
  `--no-extern`.

Question: which of these does the specification fix, and to what?

## G7. A crash during a compile-time run [C4, D7, D13]

§31, lines 1320 to 1323: "A real run may crash where the host cannot
represent what is asked of it. A crash produces no value, never a
different one. How a crash is reported is not specified; it need not
be a runtime error." §72, lines 3153 to 3156, of `native-compute`: "It
may crash where the evaluator would not, and the other way round
(§31). A program that cannot be compiled is an error at the form, and
a run that crashes is an error at its argument."

So a crash in a `native-compute` run is an error of the program, and
whether it happens depends on the host. For an ordinary compile-time
run the text does not say whether a crash rejects the program. The
word "fuel" does not occur in DESIGN.md.

Question: is a source whose compile-time run crashes rejected, or is
there no verdict for it? Decision D1 is the same question for a run
that is merely long.

## G8. A run that would take a branch with no code [C14]

01, section 1.5. DESIGN.md says such a path is not reached (§21, line
894: a phantom branch "can never run"; §25, lines 1063 to 1064: an
absurd function "compiles to no code"; §59, line 2632: "the pointer is
never followed") and does not say what a run does there. The proposal
R7 of 02 is that the run relation derives no result for such a path,
and that a compile-time run that reaches one is a rejection, with a
positive relation saying that it did.

Question: confirm, or name an outcome. For a compile-time run that
reaches such a path, is the source rejected, or is there no verdict?

## G9. The order of elaboration [C11]

The order in which the elaborator reaches sibling forms can be
observed: through the number `gensym` returns (§65, lines 2928 to
2929: "counting from 1 over the whole run"), which is a `many` `Nat`
in the macro's hands; through the expansion count against its limit
(§62); through which of two errors is reported (§15, line 626:
"whichever one the elaborator meets first"); and, in run position,
through the order of the run (§27). The text gives the order in
pieces: §6, line 236, "The head is elaborated first"; §50, lines 2321
to 2322, an argument is checked against "its parameter, given the
arguments before it".

Both implementations today expand macro calls written directly as
arguments before a macro call nested inside an earlier argument: with
a macro `tick` that expands to the number `gensym` gave it,
`(add3 (tick) (nat-add (tick) 0) (tick))` receives 7, 9, and 8 in the
order written (`evidence/A2-reference-run.md`, section 3.6).

Question: is elaboration in the order written, everywhere, and is that
part of the language?

## G10. What "accepted" means, and what it depends on [C5, B0, B1]

DESIGN.md does not define a program's being accepted: the audit found
"reject" nowhere and "accept" only of single forms. The formal
specification has to introduce the predicate. Besides the text of the
program's files, the audit lists these as inputs to it, each with its
quote: six flags (`--no-prelude`, `--no-extern`, `--fn-same`, `--goal`,
`--warnings-as-errors`, `--comptime-unconfine`); the other files on
the command line and their order (§27, line 1163); the prelude's text;
file names, lines, and columns, which a macro receives as a `Pos`
(§62) and can compute on; the files `read-file` reaches (§65); the
FFI's table of names (§42, lines 1956 to 1958); the host (§42: "native
integers of at least 63 bits, which the FFI checks"); and the order of
`Special`'s constructors (G6).

Question: what is the input of the theorem "every program's source
code is either accepted or rejected": the files' bytes with a fixed
prelude and fixed flags, or more? S5 of 03 proposes that everything on
this list is a parameter of the top-level judgment.

## G11. The prelude as part of the specification [C7]

§42, line 1966: "`lib/prelude.sl` is the reference for what it
defines." Lines 1990 to 1991: "`lib/prelude.sl` is the reference for
the requests and their answers." The prelude was written by sessions.
It uses two declaration forms that DESIGN.md does not mention:
`def-prim`, 21 times, and `def-opaque`, 4 times
(`grep -c` on both files). `unary` and `prove-literal-lt`, which §45
and §49 describe, are macros defined there.

Question: is the prelude's text inside the formal specification, with
`def-prim` and `def-opaque` given rules, or does the specification
cover the language under `--no-prelude` plus a stated interface?

## G12. Where the input starts [C8]

§4, lines 156 to 157: "Pragmas are read from source text alone.
Nothing a macro returns is a pragma, and no parser from text to `Raw`
may process one." §63, lines 2779 to 2780: "each top-level form of the
source has its literals interned and replaced by such handles just
before it is elaborated." So the prelude's `Raw` cannot be the
specification's input as it stands: a literal is in a `Raw` only as a
handle to an entry that elaboration has already made, and pragmas are
outside it. Starting at bytes needs lexical details that §1, §4, and
§45 leave open. `evidence/S4-reader-spec.md`, section 12, lists
sixteen, each with its quote and with what each implementation does.
Five of them:

- **Which characters are whitespace.** §1, lines 41 to 42: "An atom is
  any run of characters other than whitespace, parentheses and `;`."
  The set is not given. The two implementations differ: a form feed, a
  vertical tab, a zero byte, and byte 0x1f are part of an atom for the
  reference and end an atom for slc. This session re-ran the probe:
  `spikes/reader/diff/probe.sh '(show-args a\fb)'` shows one atom
  under the reference and two under slc.
- **What a token is.** §1 and §45 use the word and do not define it.
  Both implementations read `"a"b` as two items and `a"b"` as one
  name.
- **What tree reading produces.** §63, lines 2779 to 2781, makes `Raw`
  hold handles where the source had literals, so the tree between
  reading and interning is not `Raw`, and DESIGN.md gives it no name.
- **Positions.** §42, lines 1997 to 1998, gives a `Pos` "a line and a
  column (`Nat`)" and does not say whether they count from 0 or 1, or
  in what unit. A macro receives a `Pos` and can compute on it (G10).
- **When a file's text is read.** DESIGN.md does not say. Both
  implementations read a whole file before elaborating any of its
  forms, and take the files of one command line one at a time. So a
  missing `)` at the end of a file rejects it before its first form
  runs, and the same mistake in a second file comes after the first
  file's forms have run (re-run by this session).

Question: decision D7; and what the language says on each of the five
points.

## G13. Stripped code and post-erasure code [C13]

The evaluator runs code whose erased positions are "stripped" (§27,
line 1181). The `tail`, `delegate`, and at-function checks read "the
post-erasure code", where coercions, placings, renaming `let`s, and
`at` entries are gone as well (§19, lines 822 to 824; §36, lines 1647
to 1651; §39, lines 1836 to 1841). The text does not say these are one
thing.

Question: are they one object in the specification, or two with a
stated map between them?

## G14. Models or implementations, and "the same values" [C6, C22, D14]

§42, lines 1951 to 1955, requires that "running the models instead of
the implementations must give a program the same values". It does not
say how values are compared: as words, as what is printed, or up to a
relation on heaps. Some programs are accepted in one mode and not in
the other (G6's last probe; §33, lines 1454 to 1457, refuses
`coercible-tag` "under `--no-extern`"), so the requirement can apply
only to programs accepted in both, which the text does not say.

Question: which mode is the theorem about, and how are two runs'
values compared? Decision D6.

## G15. Top level and run position [C19, D1]

§20, lines 850 to 852, makes the top level "anywhere outside a
function body, including the match branches of a top-level statement".
§27, lines 1178 to 1179, makes run position "under no function body
and no match branch". §27, line 1187, then says "A file's top level is
run position". A branch of a top-level `match` is at the top level by
§20 and not in run position by §27.

Question: confirm that the specification needs both notions, with such
a branch calling freely and not running when elaborated.

## G16. The sugar the header calls provisional [C20, B5]

Line 31: "Sugar, provisional: §46 to §53." The audit finds §6, §18,
§21, §25, §27, §29, and §39 citing §51 to §53 for things they use.

Question: is §46 to §53 in the formal specification from the start,
in part, or later?

## G17. What an error does [C12]

The text gives errors one form at a time and does not say whether the
first error ends elaboration, so that no later run-position form
runs. §62's "At most 10000 expansions run in one run" does not say
that the next expansion is an error, or whether the prelude's own
expansions count. `dump-context` "stops elaboration with a report of
the context" (§54, lines 2427 to 2428), which is neither acceptance
nor an error on the text.

Question: does the first error end elaboration? Is a program that
reaches `dump-context`, or the expansion limit, rejected?

## G18. `Imm` when the models run [C17, D9]

§44, lines 2061 to 2063: "`(Imm A v)` says that `v` is an immediate
however it is built [...]. `ImmNat` gives it for a `Nat` below
`u62-modulus`". Under `--no-extern` a `Nat` above zero is a `Succ`
value with a non-erased field, which §33's uniform representation
makes a pointer to a block.

Question: is an immediate a notion of the specification's run, and
does `ImmNat` hold in the mode the specification describes?

## G19. The driver [C16]

§27 says what the driver does with a final value, and §42 defers the
requests and their answers to the prelude. With several files the
text does not say which final values the driver acts on (§27, lines
1161 to 1164, with §1, lines 39 to 40: a file's top level "has size
one", and "A file that ends in a statement produces nothing").

Question: is the driver's loop inside the theorem that the output's
run matches the specification's run (T6 of 01)?

## Two notes that are not about DESIGN.md

- MINIMAL.md and `mini/` speak of forcing's "three contradictions";
  DESIGN.md §7, line 310, has "exactly four cases". A3 notes that
  `mini/` groups two of the four as one.
- OPEN.md has a heading "Argument temporaries" (line 128) with no item
  under it.
