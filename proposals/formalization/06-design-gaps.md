# 06. Where DESIGN.md is silent or gives a choice

A Claude session's findings, written overnight at the owner's request.
Each item is a place where a formal specification would have to say
something that DESIGN.md does not, or where DESIGN.md's text gives an
implementation a choice. Each is put as a question. None is answered
here. Quotes are DESIGN.md's, with section and line numbers.
`evidence/A5-design-audit.md` is a longer audit by a sub-agent, with
the searches behind each "silent".

Items keep their numbers; a removed item leaves a gap.

## G1. Acceptance can turn on the answer of a compile-time `slot-eq`

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

## G2. The order of evaluation among siblings

02, section 2.3, quotes the text and lists what it leaves open: the
order of sibling argument temporaries, of the entries of a `values`,
and of the items of a cell form, inside a function body; whether a
body runs in the order run position has; and whether §15's binding
covers a head and a scrutinee, as §29, lines 1241 to 1242, says in
passing ("the elaborator's own binders for its head, arguments and
scrutinee (§15)").

Question: decision D4.

## G3. What a function value's word is, and when a closure is made

§29, lines 1247 to 1248: "a function's value is its compiled code".
§32, line 1327: "A function defined by `def-fns` is a closure over its
scope." §33, lines 1488 to 1489: "The pointer of a `delegate`-bodied
function is its callee's pointer (§19)." §39, lines 1864 to 1865: "an
at-function compiles to a function that does nothing and returns no
word."

`(slot-of f)` is the word of `f` (§35, line 1575: "Its word is the
word of `x`"), and `slot-eq` compares words. OPEN.md 36B already notes
that "two closures at one word can differ in what they capture or pass
erased".

Question: when a `def-fns` inside a body runs twice, are its functions
one word or two? Is the word of a function with nothing to capture the
same each time?

## G4. Whether equal blocks built separately may share an address

§36, lines 1697 to 1698: "two separately built cells with equal
contents are `is`-equal and are two blocks." This is said of cells.
For values built by constructor application at `many` the text does
not say whether an implementation may share them, and `slot-eq` could
tell.

Question: is every allocation fresh in the run, so that sharing equal
immutable blocks is not allowed to an implementation?

## G5. Which words are unspecified

§33, lines 1470 to 1475, gives the word of a value with no non-erased
field in two cases and says "an unspecified word otherwise". §45,
lines 2236 to 2237, leaves to the implementation "How a `Nat`, `Char`
or `String` is held at runtime".

Question: may the run relation leave these words undetermined, with
`slot-eq` on them answering either way, or should it fix them?

## G6. A crash during a compile-time run

§31, lines 1320 to 1323: "A real run may crash where the host cannot
represent what is asked of it. A crash produces no value, never a
different one. How a crash is reported is not specified; it need not
be a runtime error." §72, lines 3153 to 3156, of `native-compute`: "It
may crash where the evaluator would not, and the other way round
(§31). A program that cannot be compiled is an error at the form, and
a run that crashes is an error at its argument."

So a crash in a `native-compute` run is an error of the program, and
whether it happens depends on the host. For an ordinary compile-time
run the text does not say whether a crash is a rejection or no verdict
at all.

Question: is a source whose compile-time run crashes rejected, or is
there no verdict for it?

## G7. The order of macro expansion and of interning

§65, line 2928: "`gensym` mints a number, counting from 1 over the
whole run". The number is a `many` `Nat` in the macro's hands, so what
a macro returns can depend on how many expansions came before. §7,
line 303: "of two literals the one interned first is the older", and
the older of two atoms is the one kept when they are unified. Both
make the result of elaboration depend on the order in which the
elaborator visits a form's parts. The text gives that order in pieces
(§6, line 236: "The head is elaborated first"; §63, lines 2779 to
2780: literals are interned per top-level form "just before it is
elaborated"), and not as one rule.

Question: is elaboration order the order written, everywhere?

## G8. A run that would take a branch with no code

01, section 1.5. DESIGN.md says such code does not exist (§25, lines
1063 to 1064: an absurd function "compiles to no code"; §59, line
2632: "the pointer is never followed") and does not say what a run
does if it gets there. The proposal R7 of 02 is that the relation has
no rule.

Question: confirm, or name an outcome.
