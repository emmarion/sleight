# A5. DESIGN.md audit for a formal specification of Sleight

Scope: what DESIGN.md fixes, and what it leaves unsaid, about the run (Part A) and about accepting or
rejecting a program (Part B); the gaps as questions for the owner (Part C); passages that pull against each
other (Part D). Audited file, `[RAN]` `wc -l`, `md5sum`, and `git log -1 -- DESIGN.md`: `/home/user/sleight/DESIGN.md`,
3156 lines, md5 `6c39fcd4d034e1c703bc80ad8c19cf75`, last changed by commit `734d51b`.

## Contents

- Findings first (ten findings, and a check of the handoff's statements about DESIGN.md)
- Part A. The run: A1 when code runs; A2 evaluation order; A3 memory; A4 nondeterminism and the environment;
  A5 the impossible paths; A6 erasure
- Part B. Accept or reject: B0 no definition of acceptance; B1 what acceptance depends on; B2 choices left to
  an implementation; B3 "never both accepted and rejected"; B4 where a program starts; B5 provisional and
  delegated parts
- Part C. Twenty-two gaps as questions for the owner (C1 to C22), each checked against OPEN.md and DECISIONS.md
- Part D. Fourteen internal tensions (D1 to D14)
- Appendix S (searches), Appendix R (two experiments), Verification of this report
- Things I am least sure of

## How to read this report

- **Tags.** Every claim carries one of the brief's five tags: a quotation tag, `[RAN]`, `[READ file:lines]`,
  `[INFERENCE]`, or `[UNKNOWN]`. A section or table that opens by declaring its items `[INFERENCE]` tags all of them.

- **Quotations.** Every quotation of a file is a blockquote line: the tag `[QUOTE`, the file, a colon, the
  first and last line (`a-b`), the section as `§N`, a closing `]`, and then the text. The text is
  copied exactly; a line break in the source is written as one space; Markdown markup of the source is kept.
  `§N` is the DESIGN.md section, or `§intro` for the lines before §1. Short phrases quoted inside prose carry
  their line numbers as `L1234` or `L1234-1236`; with no file named, they are lines of DESIGN.md.

- **Checked by machine.** `[RAN]` `python3 proto/A5/verify_quotes.py` on this file checks, for each quotation
  line, that the text occurs in the cited file, that it starts on the first cited line and ends on the last,
  and that the section number is the section holding those lines. `[RAN]` `python3 proto/A5/verify_inline.py`
  checks that each phrase between double quotes in prose occurs verbatim in a source file and that a line
  reference in the same paragraph overlaps an occurrence. The results are at the end of the report.

- **Silence.** A claim that DESIGN.md is silent cites the searches that support it; Appendix S lists every
  search with its output. A search can show that words are absent, not that an idea is absent, so each such
  claim also rests on my having read every line of DESIGN.md once, in order.

- **What I read.** All of DESIGN.md, OPEN.md, DECISIONS.md, CLAUDE.md, the brief, and the handoff. From
  MANUAL.md, only the passages on flags that I quote (it describes the implementations and the sessions wrote
  it). From `lib/prelude.sl`, only the lines I quote or cite with `[READ]`; DESIGN.md names that file "the
  reference for what it defines" (L1966). I did not open ASSUMPTIONS.md, SOUNDNESS.md, `lean/`, `mini/`, `self/`,
  or the OCaml sources, and nothing here rests on them.

- **Implementations.** Two small experiments (Appendix R) show what the two implementations do. They are
  marked as implementation behaviour wherever they are used, and no gap is filled from them.

## Findings first

Each finding is `[INFERENCE]` resting on the quotes and searches in the section it names.

1. **Acceptance is decided by running code, and the text lets one of that code's inputs differ between runs.**
   A run-position form runs as soon as it is elaborated; `comptime-match` makes it an error for a
   compile-time value to be headed by a constructor other than the one asserted; and §67 lets `slot-eq` answer
   `ENone` whatever its arguments and `ESome` when they hold one word, "and which one a call
   answers may differ between runs" (L3045-3046). So, on the text, one source can be accepted in one run and
   rejected in another. Both implementations accept the construction (Appendix R, run R1). The handoff's "never
   both accepted and rejected" (handoff L41) can hold only relative to fixed `slot-eq` answers, or under a further
   decision. (B3, C3)

2. **No sentence fixes the order of evaluation among the sibling sub-expressions of one form.** Not for the
   arguments of a call, not for a head against its arguments inside a body, not for the entries of a `values`,
   and not for the items of a `cell-write` or `cell-alloc`. The text fixes: eagerness; run-position statements in the
   order written, with the forms inside a form before it; the head first in run position; and §15's argument temporaries.
   §15's "placed just before the statement or final form that contains the call" (L658) has two readings; on
   one of them an argument nested in a later `values` entry is bound before the whole `values`, as the handoff
   said. §15 presents the rule as one about scope; §39 relies on it for the evaluation of a skipped call's
   arguments. That statements inside a body run in the order written is presupposed (§61) and not stated. (A2, C2)

3. **The text requires a machine of words and blocks, and frames it as "a requirement on the implementation" (L1460).**
   A3.2 lists 21 things a heap-machine model must have according to the text (one word per value; immediates
   and pointers to blocks; tags; position words; `cell-alloc`, `cell-write`, and invocation as allocation,
   store, and copy; an address that survives a store; word identity that `slot-eq` can report). A3.3 lists 12
   things the text leaves open, among them: what a function value's word is; whether equal blocks may share an
   address (the one sentence, §36 L1696-1698, says two separately built cells "are two blocks"); whether an
   address is ever reused (no sentence); what "fresh" (L1735) promises; what the immediates are. (A3, C1, C9, C10)

4. **A crash is a third outcome.** §31 lets any real run crash and says "How a crash is reported is not
   specified" (L1322). Only §72 makes a crash an error, for `native-compute`. DESIGN.md does not say that a crash
   of the evaluator at compile time rejects the program; MANUAL.md says the implementations refuse it. The
   word "fuel" does not occur in DESIGN.md. (A4, B1.4, C4)

5. **DESIGN.md does not define what it is for a program to be accepted, and acceptance has inputs besides the
   files.** It names six flags; it defers to `lib/prelude.sl` as "the reference for what it defines" (L1966), and that
   file declares 21 primitives with a form, `def-prim`, that DESIGN.md never mentions; acceptance can also
   depend on other files, file names and positions (through macros), the file system (`read-file`), the FFI
   table, the host, which warnings exist, and the order of `Special`'s constructors, which DESIGN.md does not
   give and which a program can observe (Appendix R, run R2). (B0, B1, B2, C5, C7)

6. **On the impossible paths the text says only that they are not reached.** A phantom branch "can never run" (L894);
   an `absurd` function "compiles to no code" (L1064) and its "pointer is never followed" (L2632); an all-refuted match
   "produces its declared result" (L1070). Nothing says what a run does there. (A5, C14)

7. **Erased code has two descriptions that the text does not identify.** The evaluator runs code with erased
   positions "stripped" (L1181); the `tail`, `delegate`, and at-function checks read "the post-erasure code" (L822), which
   also lacks coercions, placings, renaming `let`s, and `at` entries. (A6, C13)

8. **A spec cannot start at the prelude's `Raw` as it stands.** A literal is in a `Raw` only as a handle to an
   interned entry, made "just before" each top-level form "is elaborated" (L2779-2780), and pragmas are outside
   `Raw`. Starting at bytes needs lexical details the text omits. (B4, C8)

9. **Fourteen internal tensions** (Part D). The ones that most affect a formalization: the top level is wider
   than run position, yet §27 says "A file's top level is run position" (L1187; D1); §29 cites §15 for head and
   scrutinee binders that §15 does not give (D2); "a single field is stored bare" (L1465) against "an unmarked type of
   newtype shape is a block" (L1482-1483; D3); the word of a fieldless value of a tagged extern type (D4); `ImmNat` when the
   models run (D9).

10. **The sections the header calls "Sugar, provisional" (L31; §46 to §53) are load-bearing.** §6, §18, §21, §25, §27,
    §29, and §39 cite §51 to §53 for things they use. (B5, C20)

**The handoff's statements about DESIGN.md that I checked.** "DESIGN.md does not state the order among the
sub-expressions of one form" (handoff L34): confirmed (A2.2). The §15 reading it reports: confirmed as
reading R1 (A2.3). Its caution that DESIGN.md "describes the run in terms of words, blocks, slots, and stores
(§31, §33, §35 to §38, §67)" (handoff L52): confirmed for §33 and §35 to §38 and §67; §31 itself speaks only of "a
machine with unlimited stack and heap" (L1319-1320) and has none of those four words. Its quotation of §21 on a
missing branch (handoff L26) matches DESIGN.md L925-926.

# Part A. The run (dynamic semantics)

## A1. When code runs at all

### A1.1 The occasions on which code runs, and who runs it

`[INFERENCE]` (a summary of the quotes in A1.2 to A1.6; each row cites its lines) DESIGN.md names five
occasions on which code runs and three executors. It gives one sentence of semantics for all of them (§31, quoted in A1.6).

| Occasion | Executor, in the text's words | Where stated |
|---|---|---|
| A form in run position | "the evaluator" | §27 L1178-1184, §29 L1298-1302 |
| A macro call being expanded, anywhere, types included | not named ("runs the macro's function") | §7 L277-280, §9 L419-421, §27 L1188-1192, §62 L2737-2741 |
| `native-compute` in run position | "compiled code" | §72 L3149-3156 |
| The final value of the top level, when a `Program` | "the driver" | §27 L1165-1168, §42 L1976-1980 |
| The final value, when an `Fn` of one of two forms | "compiled code" (said of the second form in §27, and of "a final `Fn`" in §72) | §27 L1168-1176, §72 L3149-3152 |

### A1.2 Files, the top level, and the final value

> [QUOTE DESIGN.md:39-40 §1] A file is a sequence of statements, optionally followed by one expression (§27).

> [QUOTE DESIGN.md:1926-1927 §42] **Built-ins.** Before any file is read, the scope holds the following, all erased unless stated otherwise:

> [QUOTE DESIGN.md:1963-1966 §42] **The source prelude** `lib/prelude.sl` is elaborated before a program's files. Its names are ordinary and may be shadowed. Its proofs are erased fields and erased functions, so none is built at runtime. `lib/prelude.sl` is the reference for what it defines.

> [QUOTE DESIGN.md:1161-1162 §27] **The top level.** A file's top level is an expression and so has size one.

> [QUOTE DESIGN.md:1162-1163 §27] `goal` and `qed` (§71) do not change this, but `--goal open` and `--goal proved` turn off the driver described here.

> [QUOTE DESIGN.md:1163 §27] Several files on one command line share one scope, in order.

> [QUOTE DESIGN.md:1163-1165 §27] A file that ends in a statement produces nothing. Otherwise the type of the final value decides what the driver does with it.

> [QUOTE DESIGN.md:1165-1168 §27] A `Program` value (§42) is run: the driver consumes it at `unique` and applies each step's continuation once. Any other final value is used at `many`, so a `unique` one is written `(share x)` (§16).

> [QUOTE DESIGN.md:1168-1176 §27] A final value of `Fn` type must have one of two forms, at any level `L`. `(Fn L (many (String) x) -> (many (String) y))`, with the prelude's `String`, is applied to all of standard input, and its result is written to standard output. `(Fn L -> (many T y))`, for any type `T`, is applied and its result is printed (§45); this is how a program asks for its final value to be computed by compiled code. A final value of `Fn` type in neither form, or of `UniqueFn` type, is an error. Any other value is printed (§45).

> [QUOTE DESIGN.md:2228-2232 §45] Any other value prints by its type. A tagged enum names its constructor. A type with exactly one non-phantom constructor names it. A union with more than one prints `_`. So does an erased field, a cell, a slot, a function, an opaque proof, and a value whose type has no readable `Matchable` (§8).

> [QUOTE DESIGN.md:850-852 §20] At the file's top level, which means anywhere outside a function body, including the match branches of a top-level statement, any constructor and any function may be called with no `Predates` or `Subterm` proof.

> [QUOTE DESIGN.md:854-855 §20] The top level is above every function level, and no function body can call into it.

### A1.3 Run position: compile-time runs by the evaluator

> [QUOTE DESIGN.md:1178-1184 §27] **Run position.** A form is in run position when it is under no function body and no match branch. Such a form runs as soon as it has been elaborated, before the code after it is checked: it is elaborated, its erased positions are stripped, the evaluator runs the code, and its results become `Settled` with the resulting values (§29). Its code is then those values, so the form around it does not run it again.

> [QUOTE DESIGN.md:1184-1185 §27] A form in an erased position runs nothing, and its results are `Settled` with the token of §5.

> [QUOTE DESIGN.md:1185-1187 §27] This nests: the forms inside a form run before it does, and the statements of a `let`'s right-hand side complete before the enclosing `let` does.

> [QUOTE DESIGN.md:1187-1188 §27] A file's top level is run position, so calls there need no proofs (§20).

> [QUOTE DESIGN.md:1188-1192 §27] Elaborating code under a function body or a match branch never runs it; such code runs at compile time only when called from run position, or when it is part of a macro's implementation, the function the macro holds, which runs each time a call of that macro is expanded (§19).

> [QUOTE DESIGN.md:1192-1194 §27] The binders of a run-position statement declare their multiplicities (§19), which is what allows the statement to be stripped and run before the code after it is elaborated.

> [QUOTE DESIGN.md:277-280 §7] Code runs at compile time only where a run-position form runs, together with every function it calls, and where a call of a macro is expanded, which runs the macro's function (§27, §29, §62).

> [QUOTE DESIGN.md:280-281 §7] A run-position form's match branches are gated like any other.

> [QUOTE DESIGN.md:283-284 §7] Compile-time effects in unreachable code still happen.

> [QUOTE DESIGN.md:419-421 §9] The elaborated form of a type never contains a function call, and elaborating a type calls none: the only code that runs is a macro's expansion (§62).

> [QUOTE DESIGN.md:1198-1204 §28] Inside a function body or a match branch, the result of a call, the result of a match, a constructor application and a `coerce` (§33) are `Hypothetical`, even when their arguments are `Settled`: nothing is folded through them there, and every binding there is `Hypothetical`. Everywhere else, in run position (§27), each of them runs as soon as it is elaborated and its results are `Settled` (§29), as are the binders of the statements there.

> [QUOTE DESIGN.md:1208-1210 §28] `(comptime-match m x (C f1 ... fn))` asserts, at elaboration time, that `x` is a `Settled`, non-erased value headed by `C`. It is an error otherwise.

> [QUOTE DESIGN.md:1210-1213 §28] `x` is a size-one expression taken at `m`. Since the form is in run position, `x` runs as soon as it is elaborated (§27), and the stored value of its `Settled` result is read.

> [QUOTE DESIGN.md:1239-1244 §29] **A form in run position** (§27, §20). Every entry it creates and leaves in scope is `Settled` once the form has run: its results, the elaborator's own binders for its head, arguments and scrutinee (§15), the binders and fields of a statement, and the automatic slot (§35) of each, which holds the word of its entry, or the token where the entry is erased.

> [QUOTE DESIGN.md:1244-1246 §29] A `let` is elaborated, stripped of its erased positions, and run by the evaluator; its binders take the resulting values at their declared multiplicities (§19).

> [QUOTE DESIGN.md:1246-1249 §29] A `def-lvl`, `def-fns`, `def-unique` or `def-adts` involves no evaluation: a function's value is its compiled code, a `Level` is an erased token, and a `Matchable` is the FFI's wrapper for an `extern` type and nothing otherwise (§24).

> [QUOTE DESIGN.md:1273-1277 §29] **Inspection requires `Settled` and non-erased.** A stored value is read in three places: head dispatch (§6), the discriminant read of `comptime-match`, and the running of a run-position form that refers to the entry, where the value is embedded in the code that is run.

> [QUOTE DESIGN.md:1287-1291 §29] Selecting a match branch from a value would be evaluation, so inside a body the results of a match stay `Hypothetical` even when the scrutinee is `Settled` (§28). In run position the match itself runs (§27), which hands the branching to the evaluator.

> [QUOTE DESIGN.md:1298-1302 §29] **The round trip.** Checking a run-position form is a dialogue. The elaborator checks the form and produces code with the erased positions removed. The evaluator runs that code. The resulting values come back to be stored (§5) and embedded as constants. Round trips nest: a form in run position runs before the form that contains it.

> [QUOTE DESIGN.md:1305-1309 §29] Every fact derived from a stored value, that is, a `comptime-match` and everything that follows from the fields it binds, relies on the evaluator having evaluated correctly. A stored value that `native-compute` produced relies on its compiled run in the same way (§72).

> [QUOTE DESIGN.md:1355-1356 §32] A top-level binder, which is a `Settled` (§29), may be `unique` under the same rules, since run-position statements are sequential.

> [QUOTE DESIGN.md:601-603 §14] Erasure is decided from the text of one unit alone, a function body against its signature or a run-position statement against its binders, before that unit is compiled or run.

`[INFERENCE]` The compile-time store is one mutable heap that persists across run-position forms. This
rests on three quotes: a `Settled` entry's automatic slot "holds the word of its entry" (§29 L1242-1244,
above); a top-level binder may be `unique` "since run-position statements are sequential" (§32 L1355-1356,
above); and §64 says a read of an `MUnique` handle could happen "possibly after the value was consumed and
mutated in place" (L2848-2850, quoted in A3.1 group 9). I did not find a sentence that states it directly.

### A1.4 Macro expansion

> [QUOTE DESIGN.md:2737-2741 §62] A list whose head dispatches as a macro is a macro call (§6, §19). The function is applied to a macro world (§65), the position of the call's opening `(` or `$`, and the call's arguments as `Raw` (§63), unexpanded and unresolved; the head is not passed. The forms it returns replace the call.

> [QUOTE DESIGN.md:2752-2753 §62] At most 10000 expansions run in one run, every file on the command line included.

> [QUOTE DESIGN.md:2882-2887 §65] The macro world is the elaborator's program store: the run-position entries with their values and facts, the literal table, the gensym counter and the expansion count. It is threaded sequentially through all of elaboration, carried out of every scope where uses are carried, and passed along rather than joined. Only the expander supplies a `MacroWorld`, to a macro's function.

> [QUOTE DESIGN.md:281-283 §7] Special-form dispatch and macro expansion are decided at compile time anywhere, so they read the table as it stood at the innermost enclosing run position (§6, §65).

### A1.5 The driver, `Program`, and goals

> [QUOTE DESIGN.md:1972-1974 §42] **`Program` and `Request`.** `(Program L)` is an enum indexed by a level, read by the driver (§27). `Exit` carries a `U8` exit code. `Continue` carries a continuation

> [QUOTE DESIGN.md:1976-1980 §42] which the driver applies to the world, the one value of `World`, which only the driver supplies; the `Program` it returns is the next step. A world is taken `at vacant-slot`, so the driver passes it no word (§36). So a `Program` is unique throughout, and each continuation is applied once.

> [QUOTE DESIGN.md:1980-1981 §42] `(Request A)` is an enum indexed by the type of its answer, and the special form `world-do` performs one:

> [QUOTE DESIGN.md:1988-1991 §42] Its arguments are checked as a call's are, and `A` may be `_` (§50). It names the prelude's `Request`, so, like literals, it is unavailable under `--no-prelude`. `lib/prelude.sl` is the reference for the requests and their answers.

> [QUOTE DESIGN.md:1993-1996 §42] The driver flushes after every write. It never recurses, so an unbounded interaction is the driver's loop over total functions. MANUAL.md describes `ConfinePaths`, `ConfineOutputBytes` and the command-line flags that stand in for them.

> [QUOTE DESIGN.md:1361-1363 §32] The driver consumes a program's final `Program` value at unique (§27) and applies each continuation once.

> [QUOTE DESIGN.md:3130 §71] `(qed e)` discharges the goal: `e` is checked against `T` at `m`, as a body's final expression checks against its return telescope (§26), and runs as any form in run position does (§27).

> [QUOTE DESIGN.md:3132 §71] Under `open` and `proved`, the driver is off: a final expression runs as any form in run position does, and nothing is printed, applied or written after elaboration.

### A1.6 The one sentence of semantics, and `native-compute`

> [QUOTE DESIGN.md:1319-1323 §31] Evaluation is eager. The semantics is that of a machine with unlimited stack and heap. A real run may crash where the host cannot represent what is asked of it. A crash produces no value, never a different one. How a crash is reported is not specified; it need not be a runtime error.

> [QUOTE DESIGN.md:3138-3140 §72] `(native-compute f1 … fn)` is an expression confined to run position (§27), with one or more arguments and each of its results in a `many` position.

> [QUOTE DESIGN.md:3149-3156 §72] The form means `(values (f1) … (fn))`, and each result is `Settled` as its call's would be (§29). It is how a program asks for run-position calls to be run by compiled code rather than by the evaluator, as a final `Fn` is (§27). The compiled run hands back only the constructor, so its erased fields take the tokens of §5. It may crash where the evaluator would not, and the other way round (§31). A program that cannot be compiled is an error at the form, and a run that crashes is an error at its argument.

### A1.7 What A1's text leaves unsaid

1. `[INFERENCE]` **The machine is not defined.** §31 says "The semantics is that of a machine" (L1319) and gives it no
   states, steps, or observations. `[RAN]` `python3 proto/A5/search.py DESIGN.md 'small-step|big-step|operational|denotation' 'observ'`
   gives 0 matches for each; `'machine'` occurs on L17, L1319, and L1970 only (the listing is in Appendix S, search S7).

2. `[INFERENCE]` **Which executor runs a `Program`'s continuations, and a `String -> String` final, is not said.**
   "compiled code" is said of the `(Fn L -> (many T y))` form (§27 L1172-1174) and of "a final `Fn`" (§72
   L3150-3152). For a `Program` the text says only that "the driver" (L1166) applies the continuations. `[RAN]` the
   word `compiled` occurs on L603, L1174, L1248, L1308, L3151, L3152, and L3155 only (Appendix S, search S8).

3. `[INFERENCE]` **Several files: which final value the driver handles is not said.** §27 says files "share one
   scope, in order" (L1163) and speaks of "the final value" (L1165) of one file. `[RAN]` `search.py DESIGN.md 'last file'` gives
   0 matches; `'final value'` matches only L1165, L1167, L1168, and L1174 (twice), all in the paragraph quoted in A1.2.

4. `[INFERENCE]` **The exit code's effect is not said.** The only sentence is "`Exit` carries a `U8` exit code"
   (§42 L1973). `[RAN]` `search.py DESIGN.md 'exit (code|status)'` gives that one match.

5. `[INFERENCE]` **What happens to the rest of a run after an error is not said.** The text says of warnings
   that they "do not stop elaboration" (§4 L161) and of `dump-context` that it "stops elaboration" (§54
   L2427); I found no such sentence for an error. `[RAN]` `search.py DESIGN.md 'first error' 'abort'` gives 0
   matches each; `grep -n -i '\bstops\?\b' DESIGN.md` gives L16, L161, L1627, and L2427 only. (See B2 and C12.)

6. `[INFERENCE]` **The top level and run position are two different sets of places**, yet §27 says "A file's top
   level is run position" (L1187). See D1.

## A2. Evaluation order

### A2.1 Every sentence I found that orders things

**(a) The shape of an expression, and which way names flow.** These are stated as scope rules.

> [QUOTE DESIGN.md:1105-1108 §27] An expression is a series of **statements** followed by a final form. The final form is either a `values`, each entry of which is a size-one expression, or a single form of any size: a call, a match, a `coerce` or a `tail`-marked call.

> [QUOTE DESIGN.md:1108-1111 §27] A `values` with one entry may be written as just that entry, so `x` and `(Cons A hd tl)` are size-one expressions equal to `(values x)` and `(values (Cons A hd tl))`. `(values)` has size zero.

> [QUOTE DESIGN.md:1113-1116 §27] Every form binds names within its own sub-expressions. A **statement** also binds outward: its names, and the facts it creates, enter the expression that contains it, are visible to the rest of that expression, and are gone when it ends. A statement produces no values.

> [QUOTE DESIGN.md:92-93 §3] `let` sees backwards only: a binding never sees itself or anything declared after it.

> [QUOTE DESIGN.md:1084-1087 §26] `values` introduces several values and `let` takes them apart, with one binder per value: `(let ((many q) (many r)) (divmod n d))`. The items of a `let` are its binders, bracketed, then any statements, then the final expression.

> [QUOTE DESIGN.md:1124-1132 §27] The right-hand side of a `let` is itself an expression, so the statements before its final expression are statements of the expression that contains the `let`. Their names are visible only within the right-hand side, but their entries, facts and opened objects (§8) enter the expression after the `let`, anonymously, at the multiplicities they were declared with. Those statements run, or their code is emitted, whether or not the `let`'s own binders are erased. Only the final expression is the position that §14 calls the right-hand side.

> [QUOTE DESIGN.md:347-349 §8] `(open-adt m e)` is a statement (§27). It is an anonymous `let` of `e` at multiplicity `m`, checked like a `let` binder (§19), followed by the open of that binder.

**(b) Run position: the compile-time order.** These are stated about the run.

> [QUOTE DESIGN.md:1179-1180 §27] Such a form runs as soon as it has been elaborated, before the code after it is checked:

> [QUOTE DESIGN.md:1185-1187 §27] This nests: the forms inside a form run before it does, and the statements of a `let`'s right-hand side complete before the enclosing `let` does.

> [QUOTE DESIGN.md:1301-1302 §29] Round trips nest: a form in run position runs before the form that contains it.

> [QUOTE DESIGN.md:1355-1356 §32] A top-level binder, which is a `Settled` (§29), may be `unique` under the same rules, since run-position statements are sequential.

> [QUOTE DESIGN.md:1163 §27] Several files on one command line share one scope, in order.

> [QUOTE DESIGN.md:1963-1964 §42] **The source prelude** `lib/prelude.sl` is elaborated before a program's files.

**(c) The order of elaboration.** In run position the run follows elaboration ((b) above), so these bear on the run there.

> [QUOTE DESIGN.md:236 §6] The head is elaborated first.

> [QUOTE DESIGN.md:240-243 §6] A head that is a form is `Settled` in run position, since it runs as soon as it is elaborated (§29); inside a body it is `Settled` only when it forwards a `Settled` entry, as `(share n)` does (§16).

> [QUOTE DESIGN.md:246-247 §6] A head that is not dispatched is elaborated only once, and is the callee of item 2.

> [QUOTE DESIGN.md:2319-2322 §50] These positions are: a function body (its returns), a match branch (its annotation), a `let` whose binders all carry a type or `is` clause, and an argument (its parameter, given the arguments before it).

> [QUOTE DESIGN.md:1655-1656 §36] Its slot must equal the target's slot, instantiated with the earlier arguments, and it is not passed.

> [QUOTE DESIGN.md:2340-2343 §50] Boundaries settle from the inside out: everything within one boundary is solved together, and a boundary nested inside it closes first, using only what is known at that point. A match's annotation is settled before its branches, so no meta crosses into a branch.

> [QUOTE DESIGN.md:1854-1857 §39] The proof is created when the header that claims `at` is elaborated, before the bodies of the block, so a call within the block to a function so marked, including the function's own recursive call, is skipped.

> [QUOTE DESIGN.md:1334-1337 §32] each such binder that the body uses at unique is consumed by the definition itself, where the `def-unique` is elaborated, not at each call, and once modulo match branches as in §15.

> [QUOTE DESIGN.md:2777-2780 §63] A literal reaches it as an `MMany` handle (§64) to its interned entry (§45): each top-level form of the source has its literals interned and replaced by such handles just before it is elaborated.

> [QUOTE DESIGN.md:302-303 §7] A literal's entry (§45) is older than every other entry, and of two literals the one interned first is the older.

> [QUOTE DESIGN.md:2884-2886 §65] It is threaded sequentially through all of elaboration, carried out of every scope where uses are carried, and passed along rather than joined.

> [QUOTE DESIGN.md:2928-2930 §65] `gensym` mints a number, counting from 1 over the whole run, every file included, and returns it with a `Gensym` witness for it and the text `s`.

> [QUOTE DESIGN.md:624-626 §15] A use at unique together with any other non-erased use of the same binder is an error, reported at whichever one the elaborator meets first.

**(d) Argument temporaries (§15) and the sentences that refer to them.**

> [QUOTE DESIGN.md:620-621 §15] Each binder is checked by the uses it has on each path through the code. The order of the uses does not matter.

> [QUOTE DESIGN.md:655-661 §15] Every argument to a constructor, a function or a cell behaves as if it were first bound to an anonymous variable. An argument that is already a variable is not rebound. That binding is a statement (§27) placed just before the statement or final form that contains the call, so its entry stays in scope, anonymously, for the rest of the expression around it, as the entries of a `let`'s right-hand-side statements do.

> [QUOTE DESIGN.md:1239-1244 §29] **A form in run position** (§27, §20). Every entry it creates and leaves in scope is `Settled` once the form has run: its results, the elaborator's own binders for its head, arguments and scrutinee (§15), the binders and fields of a statement, and the automatic slot (§35) of each, which holds the word of its entry, or the token where the entry is erased.

> [QUOTE DESIGN.md:1652-1654 §36] At a call, the argument for a parameter written `at` is elaborated at the parameter's multiplicity and its uses count like any argument's. If it is not a variable, it is bound first.

> [QUOTE DESIGN.md:1843-1844 §39] Calling an at-function skips its runtime; its arguments are still evaluated, as §15 binds them.

> [QUOTE DESIGN.md:1875-1878 §39] Only the head is erased: the call stays in its non-erased position, so each argument for a non-erased parameter must be non-erased (§14, rule 2), and its arguments are still evaluated, as for any skipped call.

> [QUOTE DESIGN.md:1895-1898 §40] The match skips its runtime: its scrutinee is evaluated as for any match, but the match itself, its dispatch and its branches, compiles to no code, and the consumer reads its `at` entries back from their targets (§36).

**(e) Remarks and checks that presuppose an order inside a body.**

> [QUOTE DESIGN.md:1319 §31] Evaluation is eager.

> [QUOTE DESIGN.md:2717-2719 §61] The write stores `h` before the call: left to the invocation, that store would follow the call and the `tail` claim would fail. Per element: one allocation, two stores, constant stack.

> [QUOTE DESIGN.md:824-827 §19] The call is in tail position if it is the final expression of the body, or if its results are bound by a `let` and returned in order by a final `values`, with or without coercions and placings.

> [QUOTE DESIGN.md:1708-1709 §36] The caller's own promise is verified as always, by what follows the call, which the check requires to be erased.

> [QUOTE DESIGN.md:1754-1755 §37] This is a physical store into memory that the cell's eventual invocation re-creates; it does no usage accounting of its own.

**(f) Forms defined by another form's order.**

> [QUOTE DESIGN.md:3149 §72] The form means `(values (f1) … (fn))`

> [QUOTE DESIGN.md:1166-1167 §27] the driver consumes it at `unique` and applies each step's continuation once.

### A2.2 Does DESIGN.md fix the order among the sibling sub-expressions of one form?

**Answer: no sentence does.** `[RAN]` The searches below treat a line break as a space
(`python3 proto/A5/search.py /home/user/sleight/DESIGN.md PATTERN ...`); full output is in Appendix S, search S1.
In the table, `\|` is an escaped `|` (alternation).

| Pattern (case-insensitive regex) | Matches | What they are |
|---|---|---|
| `left to right` | 1 (L699) | the lexicographic termination order of `subterm` arguments (§17) |
| `right to left` | 0 | |
| `evaluation order` | 0 | |
| `order (written\|of evaluation\|in which)` | 0 | |
| `evaluated (first\|before\|after\|last)` | 0 | |
| `(first\|before\|after) evaluat` | 0 | |
| `in (that\|the same\|this\|source\|written\|textual\|declaration\|declared) order` | 3 (L221, L1032, L1507) | subterm parameters, a `Matchable`'s constructors, the `tail` check's `values` |
| `sequential` | 2 (L1356, L2884) | run-position statements; the macro world |
| `eager` | 1 (L1319) | §31 |

`[RAN]` `grep -n -i 'order' DESIGN.md` gives 24 lines (L198, L221, L370, L621, L631, L698, L735, L737, L749,
L750, L767, L826, L837, L985, L1031, L1032, L1163, L1420, L1507, L1833, L2185, L2193, L2485, L2951). I read each.
None speaks of the order in which the arguments of a call, a head and its arguments, the entries of a
`values`, or the items of a `cell-write` or `cell-alloc` are evaluated. L621 is "The order of the uses does
not matter" (use checking). L826, L837, and L1507 are about values or arguments passed "in order" for the
`tail` and `delegate` checks. L1163 is files "in order".

Per kind of sibling:

1. **The arguments of one call.** `[INFERENCE]` Not fixed. §15 (L655-661) gives each non-variable argument a
   binding "placed just before the statement or final form that contains the call"; it does not say in what
   order two such bindings of one call stand (A2.3 case ii). §50 L2321-2322 ("given the arguments before it") and
   §36 L1655-1656 ("instantiated with the earlier arguments") show that the check of an argument may use the
   arguments written before it; neither is a sentence about evaluation.

2. **Head versus arguments.** `[INFERENCE]` In run position the head runs first: "The head is elaborated first"
   (§6 L236) and a head that is a form "runs as soon as it is elaborated" there (§6 L240-242). Inside a body
   nothing is said. §15 names "Every argument to a constructor, a function or a cell" (L655), and not the head; §29
   L1241-1242 speaks of "the elaborator's own binders for its head, arguments and scrutinee (§15)" (see D2).

3. **The entries of one `values`.** `[INFERENCE]` Not fixed. The only sentences about a `values` are that each
   entry is "a size-one expression" (§27 L1106-1107) and "a size-one location" (§26 L1081-1082). §72 defines
   `native-compute` as "`(values (f1) … (fn))`" (L3149), so its calls inherit the gap.

4. **The items of a `cell-write` or `cell-alloc`.** `[INFERENCE]` Not fixed. Each item is "a `(Slot)` expression
   at many, or `_`" (§37 L1739-1740 and L1749-1750, quoted in A3.1 group 5). The items are not arguments "to a constructor, a
   function or a cell" (§15 L655), so §15's sentence does not literally cover them, and no other sentence orders them.

5. **The statements of one expression inside a function body.** `[INFERENCE]` Presupposed, not stated. For run
   position the text says it ((b) above). For a body, the nearest sentences are "An expression is a series of
   **statements** followed by a final form" (§27 L1105), "Evaluation is eager" (§31 L1319), and the remark in
   §61 that "The write stores `h` before the call" (L2717), which holds only if the statements of `append-into` run in
   the order written. `[RAN]` `search.py DESIGN.md 'order (written|of evaluation|in which)' '\bone after'` gives 0 matches each.

The handoff reports the same conclusion:

> [QUOTE handoff.md:34] DESIGN.md does not state the order among the sub-expressions of one form.

### A2.3 What §15's "placed just before the statement or final form that contains the call" implies

Everything in this subsection is `[INFERENCE]` from §15 L655-661, §27 L1105-1111, and §3 L92-93, all quoted
in A2.1. Below, *the call* is the application whose argument is being bound (§15 says "the call", L658, although its
sentence also covers a constructor and a cell). Two readings of "the statement or final form that contains
the call" (L658) are possible, and the text does not choose:

- **Reading R1 (the series reading).** The binding joins the statement series of the enclosing expression of
  §27: it goes just before the innermost §27 statement, or the §27 final form, in which the call occurs. This
  reading fits the stated consequence, "so its entry stays in scope, anonymously, for the rest of the expression
  around it, as the entries of a `let`'s right-hand-side statements do" (L659-661).

- **Reading R2 (the entry reading).** §27 calls each entry of a `values` "a size-one expression" (L1106-1107) and says a
  lone entry equals `(values entry)` (L1108-1110). So an entry that is a call is itself an expression whose final form is that
  call, and the binding goes just before the entry, inside the `values`. Against R2: DESIGN.md gives no syntax
  by which a `values` entry holds a statement. The places where I found a statement series are a file (§1
  L39-40), a function body, a branch body, a `cell-match` body, and a `let`'s right-hand side (§52 L2380-2383
  names the last four together).

A second ambiguity: when the call is in the final expression of a `let`'s right-hand side that has statements
of its own, both a statement (the `let`) and a final form (that of the right-hand side) contain the call.
Placing the binding before the `let` statement could put it before a right-hand-side statement that binds one
of its variables, so I read the phrase as naming the innermost of the two.

| Case | R1 | R2 |
|---|---|---|
| (i) `(values (f (g a)) (h b))` as a final form | `t := (g a)` is a statement before the whole `values`; then `(values (f t) (h b))`. So `(g a)` precedes both `(f t)` and `(h b)`. The order of `(f t)` and `(h b)` is not given. | `t := (g a)` sits with the first entry. Nothing orders the first entry against `(h b)`. |
| (i') `(values (h b) (f (g a)))` | `t := (g a)` is a statement before the whole `values`, so `(g a)` precedes `(h b)`, which is written before it. This is the handoff's observation. | `(g a)` is bound with the second entry. Nothing orders the entries. |
| (ii) `(f (g a) (h b))` as a final form | `t1 := (g a)` and `t2 := (h b)` both go just before the final form, which is the call itself (reading *contains* as *is*). Their order relative to each other is not given; neither mentions the other, so §3 does not force one. | The same. |
| (iii) `(f (g (h a)))` | `t2 := (h a)`, then `t1 := (g t2)`, then `(f t1)`. The order is forced: `t1`'s right-hand side mentions `t2`, and a `let` sees backwards only (§3 L92-93). | The same. |
| (iii') `(f (g (h a)) (k b))` | `t2`, then `t1`, as in (iii); where `t3 := (k b)` stands among them is not given. | The same. |
| (iv) an argument that is a variable, `(f x (g a))` | `x` is not rebound (§15 L656-657): no statement, and nothing is evaluated for it. Only `t := (g a)` is bound. | The same. |

> [QUOTE handoff.md:34] On one reading of §15, an argument nested inside a later entry of a `values` is bound before the whole `values`

Further points, each `[INFERENCE]`:

- §15's sentence covers arguments "to a constructor, a function or a cell" (L655). It does not name: the head of a
  call; the scrutinee of a `match`, `let-match`, `comptime-match`, or `cell-match`; an entry of a `values`; the
  operand of `coerce` or `share`; the cell and the items of `cell-write`; the items of `cell-alloc`; the
  argument of `qed`. For `world-do` the text says "Its arguments are checked as a call's are" (§42 L1988), and
  for the handle and macro-world forms that they are "primitives, apart from the two special forms that end
  this section, checked as calls" (§65 L2890-2891).

- In run position the placement is moot for the run: each sub-form "runs as soon as it has been elaborated"
  (§27 L1179-1180), so the run order of siblings there is the order in which the elaborator reaches them, and
  only the head's place in that order is stated (§6 L236). Under R1, an elaborator that takes the entries of a
  top-level `(values (h b) (f (g a)))` in written order runs `(h b)` before `(g a)`, while §15 places the
  binding of `(g a)` before the whole `values`. See D10.

### A2.4 Is §15's sentence presented as a statement about run-time order?

- `[INFERENCE]` Not by §15 itself. The section is titled "Uses of unique binders" (L618). The sentence says "behaves as
  if" (L655), and the consequence it draws is about scope: "so its entry stays in scope, anonymously, for the rest of
  the expression around it" (L659-660).

- `[INFERENCE]` Other sections lean on it for evaluation. §39 says a skipped call's "arguments are still
  evaluated, as §15 binds them" (L1843-1844), and §36 says of an `at` argument: "If it is not a variable, it is
  bound first" (L1654). §29 says these binders become `Settled` "once the form has run" (L1239-1244).

- `[INFERENCE]` §15 calls the binding "a statement (§27)" (L657), and §27 says of a `let`'s right-hand-side statements
  that they "run, or their code is emitted, whether or not the `let`'s own binders are erased" (L1129-1130). So a
  reader can take the placement as the order of the run, on two conditions the text does not state: that
  statements inside a body run in the order written (A2.2 item 5), and one of R1 or R2.

### A2.5 Orders that remain open on the text alone

Each line is `[INFERENCE]` from the quotes and searches above.

1. Among the argument temporaries of one call, constructor application, or cell invocation.

2. Between a call's head, when it is a form, and its argument temporaries, inside a body. (In run position: head first.)

3. Among the entries of one `values`, and so among the calls of one `native-compute`. The quotation after this
   list shows that MANUAL.md, which is not the specification, describes the implementations as running those
   calls at once.

4. Between an earlier `values` entry and the temporary of an argument nested in a later entry (R1: the
   temporary first; R2: not given).

5. Among the items of a `cell-write` or `cell-alloc`, and between them and the cell operand.

6. Among the statements of a body: written order is presupposed (§61), not stated.

7. In run position, among sibling sub-forms other than the head: the order is the elaborator's, which the text
   does not give.

8. Whether the scrutinee and the head get temporaries placed as arguments do (§29 L1241-1242 says they have binders, citing §15; §15 does not mention them).

> [QUOTE MANUAL.md:199-200] runs it once per argument, as many runs at once as `Exec` with a `max-parallel` of `None` allows

`[INFERENCE]` What could make a sibling order observable, on the text: which of two crashes happens (§31 L1321: "A
crash produces no value, never a different one"); the answers of `slot-eq`, which the text leaves free anyway
(§67); the `tail` check, which is static (§61's remark); and, at compile time, the gensym counter and the
expansion count when the siblings contain macro calls (A2.1 (c)). I did not find a construct in DESIGN.md
whose value depends on sibling order otherwise, and I did not prove there is none.

**OPEN.md and DECISIONS.md.** `[RAN]` `grep -n -i 'order\|evaluat' OPEN.md` gives eight lines, none about
evaluation order: L11 ("subterm order"), L38 to L40 (item 4, on trusting the evaluator), L46 ("the whole order
of §17"), L53 (item 9, "Compile-time evaluation inside a body"), L134 ("an order relation on `Bin`"), and L189
(item 33, on introduction order). The same grep on DECISIONS.md gives nothing. OPEN.md has a heading with no item under it:

> [QUOTE OPEN.md:128] ## Argument temporaries

`[RAN]` `git log --oneline -S'Argument temporaries' -- OPEN.md` names only the first commit of this history
(`a24c23e`), and `git show a24c23e:OPEN.md` shows the heading already empty there. DECISIONS.md holds no entry:

> [QUOTE DECISIONS.md:22-24] ## Proposals, not approved None at present.

## A3. Memory

### A3.1 Every statement I found about words, blocks, tags, slots, cells, stores, copies, and addresses

**Group 1. Words and the uniform representation.**

> [QUOTE DESIGN.md:1367-1369 §33] A `coerce` reinterprets one value as another value with the same runtime representation, at no runtime cost, on the strength of an erased proof that the two are coercible (§60).

> [QUOTE DESIGN.md:1459-1465 §33] **Representation.** Coercion is free only if the representations coincide, so the following is a requirement on the implementation. Values have a uniform representation: every value is one word, either an immediate or a pointer to a block, whatever its type. So a `Cons` block holds a `(Meters)` and a `(Nat)` in the same way, and the field of a wrapper may be existentially typed. A value is the tuple of its constructor's non-erased fields; a single field is stored bare.

> [QUOTE DESIGN.md:1465-1468 §33] A value carries a tag only when its type is an enum with more than one non-phantom constructor. A block's tag counts only the constructors with fields. A phantom constructor takes no discriminant.

> [QUOTE DESIGN.md:1478-1483 §33] A union never carries a tag. A newtype value built by a wrapping constructor is represented exactly as that constructor's one non-erased field, with no tag and no wrapper. That representation is mandatory for a type marked `newtype` and forbidden for a type that is not marked: an unmarked type of newtype shape is a block (§37).

> [QUOTE DESIGN.md:1483-1488 §33] A word is never read as the field of a constructor that did not build it: a non-erased match on a union has a single real branch unless it is an at-match, whose `at` entries every real branch must justify (§40), and unwrapping requires the value to canonicalize to the application of the wrapping constructor. Erased fields occupy no space.

> [QUOTE DESIGN.md:867-870 §21] A type marked `newtype` must have **newtype shape**: every non-phantom constructor holds exactly one non-erased field, and there is at least one non-phantom constructor, and exactly one if the type is an enum. A value of such a type is represented as that field (§33).

> [QUOTE DESIGN.md:858-859 §21] **Two kinds of data type.** An `enum` has a non-erased discriminant. A `union` has an erased discriminant.

> [QUOTE DESIGN.md:930-935 §21] Otherwise: when the discriminant is non-erased, that is, a `many` or `unique` match on an enum, there is a runtime tag to dispatch on. When the discriminant is erased, that is, an `erased` match or a match on a union in any mode, at most one branch may be **real**.

> [QUOTE DESIGN.md:1049-1052 §24] And it is what a match reads: its type gives the tag, each branch's discriminant and the marks, so the constructors named in a match may be erased; its value is read only for an extern type.

**Group 2. Values with no non-erased field: position words, `vacant-slot`, hollow types, tag slots.**

> [QUOTE DESIGN.md:1468-1470 §33] A type is **hollow** when it is not marked `extern`, carries no tag, and none of its non-phantom constructors has a non-erased field.

> [QUOTE DESIGN.md:1470-1478 §33] A value with no non-erased field is the word of the `Nat` of its position among the fieldless non-phantom constructors when its type is tagged, the word of `vacant-slot` (§35) when its type is untagged and not marked `extern`, however the value was built, and an unspecified word otherwise. In the first two cases this is the word of its constructor's tag slot (§35). `vacant-slot`'s word is that of `Nat` 0. With externs on, the extern `Nat`'s FFI must meet this for these numbers.

> [QUOTE DESIGN.md:1586-1589 §35] `vacant-slot`, the built-in `many` constant of type `(Slot)` (§42), is its own slot. That makes a cell type that names it the type of a fresh cell. Its runtime word is what `cell-alloc` puts in a vacant slot, and the word of every value of a hollow type (§33).

> [QUOTE DESIGN.md:1591-1597 §35] A non-phantom constructor `C` with no non-erased field, of a type not marked `extern` or `newtype`, has a tag slot when an opened `Matchable` lists it. That slot is a built-in slot per position among the fieldless non-phantom constructors for a tagged type, and `vacant-slot` for an untagged one. Tag slot 0 is `vacant-slot`, and each tag slot is its own slot. With the prelude, `(slot-of 0)` is `vacant-slot`; with externs too, `(slot-of k)` is tag slot `k`.

> [QUOTE DESIGN.md:1599-1602 §35] `(slot-tag x)` is a statement (§27). It forces, outward, `(slot-of x)` to equal a tag slot. That is `C`'s slot when `x` canonicalizes to `(C ...)`, or `x` is a cell of type `(Cell C ...)`. It is `vacant-slot` when `x` is any value of a hollow type.

**Group 3. Slots.**

> [QUOTE DESIGN.md:1547-1553 §35] Every entry of the scope environment (§5), including erased entries, is created together with an anonymous entry of type `(Slot)` at the entry's own erasure. This is the entry's **automatic slot**. It is not in the scope's list of names, and its own slot is itself. An erased variable has no word, so its slot has no word behind it, and §14 keeps the slot out of non-erased positions as it keeps the variable.

> [QUOTE DESIGN.md:1556-1562 §35] A forwarding `let` binder (§19) is at its source's slot, whatever its erasure. Whether two variables are at one slot is decided by the ordinary canonicalization of the fact table: an entry's slot is an atom, a rule may equate it with another atom, and two slots are equal exactly when their canonical atoms are equal. A slot fact is created by forcing (§7) and ends with its scope.

> [QUOTE DESIGN.md:1574-1576 §35] As an expression it takes the multiplicity of its position, including `unique`. Its word is the word of `x`, and the result is at `x`, so a `let` of it is at the same slot as `x`.

> [QUOTE DESIGN.md:1800-1805 §38] `Slot` is an opaque nullary type with no constructors and no `Matchable` (§8). It is not erased by kind: a `(Slot)` binder is `many`, `unique` or `erased` as declared. At runtime, the value of a slot is a word, either a pointer or an immediate. A slot is inert: it may be stored in a field or a list like any other value, and a unique copy of its word aliases nothing that matters (§13).

> [QUOTE DESIGN.md:1805-1808 §38] A signature that speaks of a slot abstracts over it as a `(Slot)` parameter; for example, `(erased (Slot) s) (unique (Cell Pair2 s s) u)` says that the two slots hold one thing.

> [QUOTE DESIGN.md:1808-1811 §38] Two slots are equal exactly when they canonicalize to one atom (§35). Nothing relies on two slots being distinct. A slot says nothing about contents: the content of a slot is not a subterm of the slot, and only `is` speaks about contents.

> [QUOTE DESIGN.md:1242-1244 §29] the binders and fields of a statement, and the automatic slot (§35) of each, which holds the word of its entry, or the token where the entry is erased.

**Group 4. `at`: one word under two names.**

> [QUOTE DESIGN.md:1616-1619 §36] The parameters and return entries of a function, and the entries of the annotation of a `match` or `cell-match`, may add `at v`. Several names may share one `at`: `(many (Nat) r at x)`, `(unique a is r at a)`. The value is at the same location as `v`.

> [QUOTE DESIGN.md:1634-1637 §36] The slot of the entry (§35) is `(slot-of v)`, always, even when `v` is itself a `(Slot)`. An erased entry may be `at` any variable. A `many` or `unique` entry may only be `at` a `many` or `unique` variable, because its word is its target's word and an erased target has none.

> [QUOTE DESIGN.md:1642-1645 §36] **In a value constructor.** To keep a field's word at a slot, declare the field with a `Placed` type indexed by that slot (§42). After a destructure, `(placed-slot s T v p)` on the field's binder `p` proves that its slot is `s`.

> [QUOTE DESIGN.md:1647-1652 §36] **What reaches runtime.** The runtime signature of a function consists of its non-erased entries that have no written `at`. An entry written `at`, whether a parameter, a return or an annotation entry, is omitted after erasure: its word is the word of whatever it is `at`. Which entries reach runtime is read from the signature as written, never from what an `at` canonicalizes to.

> [QUOTE DESIGN.md:1657-1668 §36] Inside the body, the parameter is a rename of its target's word. An `at` return is absent from the physical values of a call. A `let` binds it like any return, and the elaborator supplies its word from a non-erased entry in the same slot: the caller's own binder for the argument the promise names, which the caller still holds whether or not the call consumed it, or, where the promise names an earlier return, that return's own entry (§19), whose word the call returned whatever the `let` binds it at. The `at` entries of a match are likewise produced by no branch and read back by the consumer. The promise of an `at` return is verified where the function or branch returns, by the canonical identity of the slots.

> [QUOTE DESIGN.md:1672-1676 §36] A function that may fail can still promise its result at its argument. It returns an erased `(Type T)`, a `(unique T v at a)` and a non-erased outcome whose type is indexed by `T`. Matching the outcome forces `T` to the intended type on success and to the argument's own type on failure, and the one word is at `a` either way.

> [QUOTE DESIGN.md:1678-1695 §36] **Writers.** Besides the declaration sites, facts equating slots (§35) are created by: the cell binder and `else` binder of a destructure (equated with the scrutinee, §23); a destructure of a newtype (its non-erased field with the scrutinee) and an application of a newtype constructor (the value with its non-erased argument, §37); a cell invocation (the value with its cell) and a `cell-write` on a `unique` cell (the result with its input); `coerce` and `share` (the result with the source); a forwarding `let` (§19); a `let` of `(slot-of x)` (with `x`); the `at` return and `at` parameter of a call and the `at` entry of a match (with their targets); the delegate annotation (`g` with `f`, §41); an application of a constructor that has a tag slot or is of a hollow type, and a `cell-alloc` of one, where an opened `Matchable` lists the constructor (the value or cell with its tag slot, or with `vacant-slot`, §35); `slot-self` and `slot-tag` (§35); and a forcing unification (§7) whenever the types it unifies mention slots, including `Cell` types and types indexed by `(Slot)`, since a slot is an atom of the fact table.

> [QUOTE DESIGN.md:1695-1702 §36] A forced rule between two ordinary atoms, `x is y`, says nothing about slots. Neither does canonical equality: two separately built cells with equal contents are `is`-equal and are two blocks. A non-forcing check, such as an argument against a parameter, only asks whether the two slots already coincide. A slot fact ends with the scope that created it, like any fact. A slot may belong to consumed entries; address equality does not change when contents do.

**Group 5. Cells: obtaining, writing, invoking, reading out.**

> [QUOTE DESIGN.md:975-976 §23] `(match unique x ann branches)` consumes `x` and binds the fields of each branch according to the `unique` column of §22.

> [QUOTE DESIGN.md:978-981 §23] When the type's constructors have cells (§37), a pattern may add one binder after the fields: `((C f1 ... fn u) body)` as well as `((C f1 ... fn) body)`. The extra binder names the cell the constructor occupied.

> [QUOTE DESIGN.md:983-986 §23] Its type is `(Cell C (slot-of g1) ... (slot-of gk))`, with one slot per field whose label is non-erased, in order, `gi` being that field's binder, and it is at `x` (§36).

> [QUOTE DESIGN.md:986-990 §23] A branch passes a `unique` cell out of the match by returning it into an entry of the match's annotation marked `at x`. A cell at `unique` may produce its value at `unique`; a cell at `many` produces its value only at `many` (§37).

> [QUOTE DESIGN.md:1006-1010 §23] A value can be read without giving up its uniqueness: destructure it at `unique`, then in each branch reinvoke the same constructor with every store skipped (§37). That erases to reading the tag and nothing else. At `many` the same reinvocation costs nothing and gives the value back at `many`.

> [QUOTE DESIGN.md:1713-1717 §37] A value constructor `C` of a type that is not `extern`, and that is phantom or of a type not marked `newtype`, has a cell type `(Cell C s1 ... sn)`. This is a type former (§9) with one `(Slot)` (§38) per non-erased field of `C`. A constructor with no non-erased field has an empty cell.

> [QUOTE DESIGN.md:1729-1732 §37] **Newtypes.** A newtype's non-phantom constructors have no cell. Its representation is the word of its non-erased field (§33). A destructure of a newtype puts the field it binds at the scrutinee, and an application of its constructor is at its non-erased argument.

> [QUOTE DESIGN.md:1734-1744 §37] **Obtaining a cell.** `(cell-alloc C)` is an expression that yields a fresh cell at unique, at no slot, with every slot `vacant-slot` (§35). When `C` has a tag slot, or the opened `Matchable` that lists `C` is that of a hollow type, the cell is instead at that tag slot, or at `vacant-slot` (§35, §36). `(cell-alloc (C i1 ... in))` lists every non-erased field; each item is a `(Slot)` expression at many, or `_` for `vacant-slot`. A partial list is not allowed. A destructure in any mode yields, through its cell binder (§23), the cell the constructor occupied, at the scrutinee, with each slot `(slot-of g)` for the binder `g` of a field whose label is non-erased.

> [QUOTE DESIGN.md:1746-1760 §37] **Writing.** `(cell-write m u (C i1 ... in))` is an expression. `m`, `erased`, `many` or `unique`, is the multiplicity the cell is taken at, and must match the form's position (§14); the items are one per non-erased field. Each item is a `(Slot)` expression at many, or `_` to leave that slot alone. `C` must be the cell's own constructor, canonically. The index of the new type for each written slot is the value of that item. At `unique` the form takes `u` at unique and yields the same cell under the new type, at `u`. This is a physical store into memory that the cell's eventual invocation re-creates; it does no usage accounting of its own. At `many` the form uses `u` at many and copies: the result is a fresh block holding the old words with the written slots replaced, at unique and at nothing. So a write whose items are all `_` copies a shared block into a unique cell. At `erased` the form uses nothing and yields the same cell under the new type, at `u`, as at `unique` (§14).

> [QUOTE DESIGN.md:1762-1774 §37] **Invocation.** A head of `Cell` type can be applied in item 2 of §6. `(u a1 ... an)` is a constructor application that creates `(C a1 ... an)` at `u`. It uses each argument at the multiplicity of its field, as `(C a1 ... an)` would, including erased arguments, which have no slot and are written as in any constructor application. The type of the value is the return type of `C`, instantiated. The cell is taken at the multiplicity of the invocation's own position (§14), whatever expression `u` is. At `unique` the invocation consumes `u` and creates its value at `u`; `(share (u a1 ... an))` is how a `many` value is built in place. At `many` it uses `u` at many and produces its value at `many`: at the cell when every store is skipped (below), and otherwise as a fresh copy at nothing. In an erased position nothing is used (§14).

> [QUOTE DESIGN.md:1776-1780 §37] An `(at)` written immediately before an argument, in the way `(subterm p)` is written before its argument (§56), asserts that the slot already holds that argument, that is, that the variable's slot is the slot in the cell's type, and the store is skipped. If the assertion is false, that is a hard error, as for `tail`.

> [QUOTE DESIGN.md:1781-1783 §37] `(at m (u a1 ... an))`, which wraps the invocation as `tail` wraps a call, asserts the same of every non-erased argument and performs nothing.

> [QUOTE DESIGN.md:1785-1789 §37] Only the stores are skipped. An invocation with every store skipped still uses each argument at its field's multiplicity and `u` at its position's, consuming unique ones, and still creates its value at `u` and its `is` fact in the fact table.

> [QUOTE DESIGN.md:1791-1796 §37] `(imm o n)` before an argument, or before a `cell-write` item, marks a store whose old and new words are both immediates. `o` and `n` are erased proofs `(Imm (Slot) s)` (§44) for the slot overwritten and the slot written. It is refused where nothing is stored: before `_`, before an erased argument, after another mark, in a `cell-alloc`, and inside `(at m (u ...))`.

> [QUOTE DESIGN.md:1813 §38] `cell-match` reads the words of a cell out.

> [QUOTE DESIGN.md:1817-1821 §38] In both modes the `si` are fresh `many` binders of type `(Slot)`, one per non-erased field, and one forced unification of `(Cell C s1 ... sn)` against the type of `u` gives them their rules, in the same way that entering a branch unifies the type of a scrutinee (§7).

> [QUOTE DESIGN.md:1825-1827 §38] The form decides nothing about a slot: each `si` is whatever the type of `u` said. The words are for writing into another cell.

**Group 6. Sole reference, sharing, and in-place update.**

> [QUOTE DESIGN.md:14-16 §intro] a `unique` binder is the only reference to its value, so the value can be updated in place rather than copied (§13, §15)

> [QUOTE DESIGN.md:510-516 §13] Where a value can be mutated in place, either through the cell a destructure hands back (§37) or by an extern's own in-place operation (§43), a `unique` binder on that value is the only reference to it. Where nothing can mutate the value, the sole-reference property is neither promised nor needed, and a `unique` binder may alias a live `many` one (§34).

> [QUOTE DESIGN.md:665-667 §16] A `unique` value is born unique in three ways: a constructor application in a unique position, a cell invocation (§37), or `def-unique` (§32).

> [QUOTE DESIGN.md:960-961 §22] A unique-labelled field under a `many` scrutinee comes out `many`: a shared block shares everything it owns.

**Group 7. Forms that yield the word they were given.**

> [QUOTE DESIGN.md:678-681 §16] Either way, the result of `(share e)` is the result of `e`, at `many`: it has the type of `e`, it `is` whatever `e` is, so a binder of it forwards the type and facts of `e`, and it is at the location of `e` (§36).

> [QUOTE DESIGN.md:1396 §33] The result is at `a` (§36).

> [QUOTE DESIGN.md:3016 §66] A `(Placed s T v)` holds `v` and is represented as the word of `v`.

> [QUOTE DESIGN.md:3021-3023 §66] A call of `place-at`, `place-at-many`, `unplace-at` or `unplace-at-many` is a **placing**. It erases to a renaming of its argument, as a `coerce` does (§33).

**Group 8. Extern types, arrays, and immediates.**

> [QUOTE DESIGN.md:1941-1946 §42] The declaration is then a *model*. For a type, its constructors and `Matchable` say what its values are and how they are taken apart, and the FFI supplies the representation together with construction and matching over it. For a function, the body says what it computes, and the FFI supplies an implementation whose non-erased arity is the model's.

> [QUOTE DESIGN.md:1946-1947 §42] An extern type is a type like any other: its values are non-erased and one word (§33).

> [QUOTE DESIGN.md:1978-1979 §42] A world is taken `at vacant-slot`, so the driver passes it no word (§36).

> [QUOTE DESIGN.md:2004-2008 §43] A `unique` value of an extern type may be mutated in place by the FFI. The FFI author has one constraint beyond those of §42: an `at` return promised by an extern function's signature must be honoured physically, and the model's body is checked against the promise like any body.

> [QUOTE DESIGN.md:2008-2011 §43] Inside the body of an extern function, no type counts as marked `extern` for the `at` rules of §36 or the cells of §37, so a model is written with the placement of §37 over the cells of its own type.

> [QUOTE DESIGN.md:2011-2016 §43] The shape check of §42 compares the non-erased arities of the model's constructors with the implementation's. Outside the body of an extern function, there is no `Cell` for the constructor of an extern type, and so no `cell-alloc`, `cell-write`, `cell-match` or invocation on one. The in-place operations of an extern type are its own functions, such as `array-swap` in §44.

> [QUOTE DESIGN.md:2020-2022 §44] The prelude's array API is indexed by the list of the array's elements. Elements are owned, and uninitialised slots go through a union newtype in the manner of Rust's `MaybeUninit`.

> [QUOTE DESIGN.md:2054-2056 §44] A `(MaybeUninit A)` is one word: the word of `A` under `Init`, and the word of its slot under `Vacant` and `Stale`. So an `(Array (MaybeUninit A) xs)` is the same memory as the `(Array A ys)` it becomes.

> [QUOTE DESIGN.md:2059-2061 §44] Since the field of `Copy` is `many`, an element of an `(Array (Copy A) xs)` is read in place.

> [QUOTE DESIGN.md:2061-2066 §44] `(Imm A v)` says that `v` is an immediate however it is built, and the `-imm` operations take it as evidence. `ImmNat` gives it for a `Nat` below `u62-modulus`, and `ImmCoerce` carries it across a `Coercible` (§33). For a `(Slot)` it says that the slot holds an immediate: `ImmVacant` gives it for `vacant-slot`, and `ImmPlaced` gives it for the slot `s` of a `(Placed s A v)` (§66) from an `Imm` of `v`.

> [QUOTE DESIGN.md:2144-2147 §44] `array-pluck` leaves the plucked element's word in the array under its `Plucked` leftover, at the slot of the value returned. So the value may be mutated in place and put back with `array-unpluck`, an `extern at` function (§39) whose call costs nothing.

> [QUOTE DESIGN.md:2149-2152 §44] Until it is put back, the array may keep the plucked value alive. Constructing an `ACons` copies its tail, and taking an array apart through the model's `ACons` view is O(n).

> [QUOTE DESIGN.md:2236-2240 §45] **Left to the implementation.** How a `Nat`, `Char` or `String` is held at runtime, and whether a literal's entries are produced by elaborating statements or created directly to the same effect. The requirement of §42 applies: stripping the extern implementations must leave every literal meaning the same value.

> [QUOTE DESIGN.md:2771-2774 §63] `Raw` is `extern` so that its representation is the reader's own syntax tree: a macro's arguments and output pass without copying, which would let nested expansions cost exponentially more than the macros' own work.

**Group 9. Function values, and stored values.**

> [QUOTE DESIGN.md:1327-1329 §32] A function defined by `def-fns` is a closure over its scope. It may mention a `unique` binder of that scope only erased or degraded, that is, through a `(share x)` written in the body or earlier.

> [QUOTE DESIGN.md:1247-1249 §29] a function's value is its compiled code, a `Level` is an erased token, and a `Matchable` is the FFI's wrapper for an `extern` type and nothing otherwise (§24).

> [QUOTE DESIGN.md:1488-1489 §33] The pointer of a `delegate`-bodied function is its callee's pointer (§19).

> [QUOTE DESIGN.md:2689 §60] `(coerce inc-noted ig)` is then the pointer of `inc` itself.

> [QUOTE DESIGN.md:2631-2632 §59] The function compiles to no code, and holding it at `many` is fine: the pointer is never followed.

> [QUOTE DESIGN.md:1864-1867 §39] Whatever its body, an at-function compiles to a function that does nothing and returns no word. So a first-class call that reaches it without an opened proof runs without crashing, and the caller reconstructs the `at` returns as it would anyway.

> [QUOTE DESIGN.md:3119-3124 §70] `(fn-same f g)` takes two values at `many` whose types canonicalize to one `Fn` or `UniqueFn` type (§11, §32), the same for both, and whose slots are already equal (§36). It yields an `(ErasedOr (Eq F f g))` at `vacant-slot` (§36), `F` the type of `f`: `EONonErased` wherever it runs, and `EOErased` where it is reached only erased (§14). It compiles to nothing, is refused in an erased position, and requires the prelude.

> [QUOTE DESIGN.md:185-187 §5] For an erased entry the stored value is a token that records that the value exists; it is not data;

> [QUOTE DESIGN.md:2846-2852 §64] There is none for an `MErased` handle, which would only rename its own erased index, and none for an `MUnique` handle, whose read would happen outside the elaborator's use accounting, possibly after the value was consumed and mutated in place. These four read a handle anywhere, not only during an expansion, and an `MMany` handle carries its value into an extracted program.

**Group 10. Asking whether two words are one.**

> [QUOTE DESIGN.md:3044-3046 §67] `ESome` proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs. `slot-eq` requires the prelude.

> [QUOTE DESIGN.md:3057-3062 §68] `(cell-same u1 u2)` takes two cells at `many` whose constructors one opened `enum` `Matchable` lists and whose slots are already equal (§36). It yields an `(ErasedOr (JMEq T1 u1 T2 u2))` at `vacant-slot` (§36), `Ti` the type of `ui`: `EONonErased` wherever it runs, and `EOErased` where it is reached only erased (§14). It compiles to nothing, is refused in an erased position, and requires the prelude.

> [QUOTE DESIGN.md:3066-3068 §69] A `Slots` is a table of placed values (§66), each numbered by when it was added and found by its slot. It targets finding a slot in O(1), where a search with `slot-eq` (§67) is O(n).

> [QUOTE DESIGN.md:3111-3113 §69] The models search with `slot-eq`, so §42's exception for `slot-eq` covers what the implementations answer. How an implementation finds a slot is left to it.

**Group 11. Consumption, the machine, and the worked example.**

> [QUOTE DESIGN.md:626-628 §15] An erased mention is never a use and is allowed anywhere, before or after the binder is consumed: a proof or a type may name a consumed value.

> [QUOTE DESIGN.md:647-648 §15] a **use at unique**, in a non-erased position at `unique`; this consumes the binder;

> [QUOTE DESIGN.md:1319-1320 §31] The semantics is that of a machine with unlimited stack and heap.

> [QUOTE DESIGN.md:1895-1898 §40] The match skips its runtime: its scrutinee is evaluated as for any match, but the match itself, its dispatch and its branches, compiles to no code, and the consumer reads its `at` entries back from their targets (§36).

> [QUOTE DESIGN.md:2694-2697 §61] `append` copies `xs` onto `ys` in destination-passing style, over the prelude's `List` (§55), whose fields are both `many`. The helper takes a vacant cell and the head that belongs in it, and promises its result at the cell:

> [QUOTE DESIGN.md:2717-2719 §61] The write stores `h` before the call: left to the invocation, that store would follow the call and the `tail` claim would fail. Per element: one allocation, two stores, constant stack.

### A3.2 What a heap-machine model must have, according to the text

Each item is `[INFERENCE]` from the lines it cites (all quoted in A3.1), unless it restates a quote directly.

1. **Words.** Every non-erased value is one word, and a word is an immediate or a pointer to a block (§33 L1461-1462; §38 L1802-1803; §42 L1946-1947).

2. **Nothing for erased things.** An erased variable "has no word" (§35 L1551), "Erased fields occupy no space" (§33 L1488), and an erased entry's stored value "is not data" (§5 L185-187).

3. **Blocks.** A block holds the non-erased fields of the constructor that built it (§33 L1464-1465). It carries a tag only when its type is an enum with more than one non-phantom constructor, and the tag "counts only the constructors with fields" (L1465-1468). A union's block has no tag (L1478).

4. **Words of fieldless values.** For a tagged type, the word of the `Nat` of the constructor's position among the fieldless non-phantom constructors. For an untagged type not marked `extern`, the word of `vacant-slot`, which is that of `Nat` 0 (§33 L1470-1477).

5. **Newtypes.** A newtype value is its field's word, with no block of its own (§33 L1478-1481; §37 L1729-1732).

6. **Word identity is askable.** `slot-eq`'s `ESome` "proves that `a` and `b` hold one word" (§67 L3044). So the model needs a notion of two words being one word.

7. **An address survives a store.** "address equality does not change when contents do" (§36 L1701-1702).

8. **`cell-alloc`.** For a constructor with a non-erased field it yields a "fresh cell", each slot holding `vacant-slot`'s word or the word of the item written for it (§37 L1734-1740; §35 L1588). For a constructor with a tag slot, or of a hollow type, the cell is that tag slot's word or `vacant-slot`'s (§37 L1736-1738).

9. **`cell-write`.** At `unique`: "a physical store into memory", and the result is the same cell (§37 L1752-1755). At `many`: "a fresh block holding the old words with the written slots replaced" (L1755-1758).

10. **Invocation.** At `unique` it stores each argument whose store is not skipped and "creates its value at `u`" (§37 L1769-1771, L1776-1780). With every store skipped it "performs nothing" (L1781-1783). At `many` it yields the cell's own word when every store is skipped, and otherwise "a fresh copy" (L1771-1773).

11. **A cell's block already has its constructor's tag, where the type is tagged.** A fully skipped invocation "performs nothing" yet yields a `C` value (L1781-1789), and "`C` must be the cell's own constructor" for a write (L1750-1751). I found no sentence that says when the tag is written.

12. **A destructure's cell is the scrutinee's own word.** The cell binder "names the cell the constructor occupied" (§23 L980-981) and is "at the scrutinee" (§37 L1741-1742), with slot `i` holding the word of field `i` ("each slot `(slot-of g)`", L1743-1744).

13. **`cell-match` reads a cell's slot words out as `(Slot)` values** (§38 L1813, L1825-1827).

14. **Same-word forms.** `coerce` (§33 L1367-1369, L1396), `share` (§16 L678-681), a placing (§66 L3016, L3021-3023), `slot-of` (§35 L1575), and a forwarding `let` (§35 L1556-1557) yield the word they were given.

15. **`at` entries are not passed.** Their word is read from the target (§36 L1647-1668). An at-function "does nothing and returns no word" (§39 L1864-1865). An at-match "compiles to no code" (§40 L1895-1898).

16. **In-place mutation by the FFI.** "A `unique` value of an extern type may be mutated in place by the FFI" (§43 L2004), and an extern's `at` return "must be honoured physically" (L2005-2007).

17. **A `delegate`-bodied function and its callee are one pointer** (§33 L1488-1489; §60 L2689).

18. **The world has no word.** It is taken `at vacant-slot` (§42 L1978-1979). §65 says the same of a macro world: "A function that takes a macro world takes it `at vacant-slot` and returns it `at` its parameter" (L2889-2890).

19. **Sole reference where mutation is possible.** §13 L510-513 states it as a property of a `unique` binder. A machine model must be able to state it (reachability of a block from live words); the text does not say how it is established.

20. **A slot word carries no right to read through it.** "A slot is inert" (§38 L1803-1805).

21. **One heap across run-position forms.** A `Settled` entry's slot "holds the word of its entry" (§29 L1242-1244), and a consumed `Settled` may have been "mutated in place" (§64 L2848-2850). See A1.3.

### A3.3 What the text leaves open

1. **Whether §33's representation is part of the language or only of an implementation.** `[INFERENCE]` §33
   introduces it as "a requirement on the implementation" (L1459-1460), while §35 to §38 and §67 state facts
   about words in the language's own terms. See C1 and D8.

2. **What a function value's word is.** `[INFERENCE]` The text calls a function "a closure over its scope"
   (§32 L1327), says its value "is its compiled code" (§29 L1247-1248), and speaks of "the pointer" of a
   function three times (§33 L1488-1489, §59 L2632, §60 L2689). It does not say whether that pointer is to a
   block, what the block holds, or whether two evaluations of one nested `def-fns` give one word or two.
   `[RAN]` `search.py DESIGN.md 'closure'` gives 2 matches (L1325, the heading, and L1327); `grep -n -i 'pointer'`
   gives L1462, L1488, L1489, L1803, L2632, and L2689 only. OPEN.md 36B records the doubt for `fn-same`:

> [QUOTE OPEN.md:203-206] two closures at one word can differ in what they capture or pass erased. Examples are two `delegate`s to one target with different erased arguments, or a closed inner function that extraction allocates once.

3. **Whether two separately built blocks with equal contents may share an address.** The one sentence is in §36:

> [QUOTE DESIGN.md:1696-1698 §36] Neither does canonical equality: two separately built cells with equal contents are `is`-equal and are two blocks.

   `[INFERENCE]` It says "cells" (L1697), it stands in a paragraph about which facts equate slots, and "separately
   built" (L1697) is not defined. Whether it binds an implementation for two `many` constructor applications with
   equal arguments, for a compile-time value "embedded as constants" (§29 L1301), or for a literal, of which
   "every occurrence of `"ab"` is one entry" (§45 L2189-2190), is not said. `[RAN]` `search.py DESIGN.md 'hash-?cons'
   '\bshar(e|ed|ing) (a|one|the same) (block|address|word)'` gives 0 matches each; `grep -n -i 'address'` gives L1701 only.

4. **What "fresh" guarantees.** `[INFERENCE]` The text says "fresh cell" (L1735), "fresh block" (L1756), and
   "fresh copy" (L1773) and does not define the word. It also says "Nothing relies on two slots being
   distinct" (§38 L1809-1810). That a fresh block is not reachable from any other live word follows from §13's
   sole-reference sentence for a `unique` result, as an inference, and from nothing I found for a `many` one.

5. **Whether an address is ever reused.** `[RAN]` `search.py DESIGN.md 'garbage' 'reclaim' 'dealloc' '\bfreed?\b'`
   gives 0 matches for the first three, and for the fourth L433 ("free references") and L1459 ("Coercion is
   free"). `'reus'` matches only the telescope reuse of §26 and §47 (L1098, L2251, L2258, L2259) and "reusing
   `inc`" in §60 (L2677). The nearest
   sentence is "the array may keep the plucked value alive" (§44 L2150). §31 gives the machine an "unlimited"
   (L1319) heap. `[INFERENCE]` If an address could be reused while a `(Slot)` word naming the old block is still held,
   `slot-eq` could answer `ESome` for an old entry and a new one; the text does not discuss it.

6. **What the immediates are.** `[INFERENCE]` The text gives instances only: position words and `vacant-slot`'s
   word (§33), "a `Nat` below `u62-modulus`" through `ImmNat`, and what `ImmCoerce`, `ImmVacant`, and `ImmPlaced`
   carry (§44 L2061-2066). It does not say what run-time effect an `(imm o n)` mark has: the only sentence is
   that it "marks a store whose old and new words are both immediates" (§37 L1791-1792). See D9 for the
   models.

7. **What "an unspecified word" covers.** `[INFERENCE]` By the sentence's case split (§33 L1470-1475), the
   third case is a value with no non-erased field whose type is untagged and marked `extern`. Whether the
   first case, "when its type is tagged", includes a type marked `extern` is not said. See D4.

8. **How `Nat`, `Char`, `String`, and every extern type are held.** §45 leaves the first three "to the
   implementation" (L2236-2238); for an extern type "the FFI supplies the representation" (§42 L1942-1944).

9. **The layout of a block.** `[INFERENCE]` The order of the fields in a block, where the tag is kept, and how
   the constructors "with fields" (L1468) are numbered are not said. "a single field is stored bare" (§33 L1465) reads
   against "an unmarked type of newtype shape is a block" (L1482-1483). See D3.

10. **The words of `Special` values.** `[INFERENCE]` `Special` is "an enum with one `many` nullary constructor
    per special form, with its `Matchable` opened" (§42 L1933-1934), so its values are position words by §33
    and have tag slots by §35. DESIGN.md gives the constructors no order; §54 lists them "grouped as §27 groups
    them" (L2400-2401). `[RAN]` Both implementations put `let` at tag slot 0, and a program can depend on it
    (Appendix R, run R2). This is implementation behaviour, not the language.

11. **The stack.** `[INFERENCE]` §31 gives the machine an "unlimited stack" (L1319-1320), §19 lets a program assert that a
    call "compiles to a tail call" (L819-820), and §61 counts "constant stack" (L2719). Nothing else about a stack is said.

12. **The words of a `Matchable`, a handle, and a `Level`.** `[INFERENCE]` A `Matchable` is `many` data whose
    value is "the FFI's wrapper for an `extern` type and nothing otherwise" (§29 L1248-1249); what word "nothing"
    is, is not said. A handle `(Settled m T t)` is "not erased by kind" (§64 L2816-2817) and its word is not
    described. A `Level` is "an erased token" (§29 L1248).

## A4. Nondeterminism and dependence on the environment in the run

### A4.1 The sentences

**`slot-eq`.**

> [QUOTE DESIGN.md:3044-3046 §67] `ESome` proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs. `slot-eq` requires the prelude.

> [QUOTE DESIGN.md:3111-3113 §69] The models search with `slot-eq`, so §42's exception for `slot-eq` covers what the implementations answer. How an implementation finds a slot is left to it.

**Crashes.**

> [QUOTE DESIGN.md:1319-1323 §31] Evaluation is eager. The semantics is that of a machine with unlimited stack and heap. A real run may crash where the host cannot represent what is asked of it. A crash produces no value, never a different one. How a crash is reported is not specified; it need not be a runtime error.

**Extern implementations against their models.**

> [QUOTE DESIGN.md:1951-1955 §42] An `extern` implementation must agree with its model: except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31).

> [QUOTE DESIGN.md:1956-1959 §42] The prototype's FFI is a fixed table keyed by the declared name. An `extern` declaration of a name the table lacks, or of a name already claimed, is an error. `--no-extern` runs the models instead, and `dune test` runs every test both ways.

> [QUOTE DESIGN.md:1968-1971 §42] **`U62`.** Its operations take `Nat`s with erased proofs that the operands and results are below `u62-modulus`, so the FFI runs each as one machine operation. This relies on the host having native integers of at least 63 bits, which the FFI checks.

> [QUOTE DESIGN.md:2139-2142 §44] `array-length-dec` and `bytes-length-dec`, and their `-many` forms, also decide whether the length is below `array-limit`, 2^54, or `bytes-limit`, 2^57. The FFI always answers `Yes`, since it cannot build anything longer (§31). An erased array or byte string may be longer.

> [QUOTE DESIGN.md:2236-2240 §45] **Left to the implementation.** How a `Nat`, `Char` or `String` is held at runtime, and whether a literal's entries are produced by elaborating statements or created directly to the same effect. The requirement of §42 applies: stripping the extern implementations must leave every literal meaning the same value.

**`native-compute`, and facts that rest on a run.**

> [QUOTE DESIGN.md:3153-3156 §72] It may crash where the evaluator would not, and the other way round (§31). A program that cannot be compiled is an error at the form, and a run that crashes is an error at its argument.

> [QUOTE DESIGN.md:1305-1309 §29] Every fact derived from a stored value, that is, a `comptime-match` and everything that follows from the fields it binds, relies on the evaluator having evaluated correctly. A stored value that `native-compute` produced relies on its compiled run in the same way (§72).

> [QUOTE DESIGN.md:2209-2212 §45] `(prove-literal-lt a b)` mints `(Lt a b)` after deciding it with `lt-dec`. Its arguments are `Settled` `many` constants of type `Nat` or `Char`, a character standing for its code; like a `comptime-match`, it relies on the evaluator (§29).

**`read-file` (compile time, inside a macro).**

> [QUOTE DESIGN.md:2960-2966 §65] `read-file` reads a file relative to a source file or to a name `--comptime-unconfine` adds, one per occurrence, without reading or checking it. `here` must name one of these, spelled as the command line names it; standard input is not one. `path` is resolved against that name's directory and must land, through any symlinks, inside that directory or below it. Otherwise, for `NoPos`, and where the read fails, it answers `Fail`. The fence (MANUAL.md) does not apply to it.

**Requests answered by the world, and standard input (the driver's run).**

> [QUOTE DESIGN.md:1980-1981 §42] `(Request A)` is an enum indexed by the type of its answer, and the special form `world-do` performs one:

> [QUOTE DESIGN.md:1990-1991 §42] `lib/prelude.sl` is the reference for the requests and their answers.

> [QUOTE DESIGN.md:1170-1172 §27] `(Fn L (many (String) x) -> (many (String) y))`, with the prelude's `String`, is applied to all of standard input, and its result is written to standard output.

### A4.2 Reading

1. `[INFERENCE]` **`slot-eq` is the only construct that the text says may answer differently between runs.** Its
   constraint is one-sided: `ESome` only when the two "hold one word" (L3044); `ENone` always allowed (L3045).
   `[RAN]` `search.py DESIGN.md 'nondetermin' 'non-determin' 'between runs' 'may always'` gives 0, 0, 1 (L3046),
   and 1 (L3045) matches.

2. `[INFERENCE]` **A crash is permitted in any real run and is neither a value nor, on the text, an error.**
   §31 leaves its reporting "not specified" (L1322). §72 alone turns a crash into an error, for the compiled
   run of `native-compute` (L3155-3156). For a crash of the evaluator during a run-position form, DESIGN.md
   says nothing more. MANUAL.md, which the sessions wrote and which describes the implementations, says:

> [QUOTE MANUAL.md:162-164] A run-position form whose evaluation crashes is refused, the reference naming the file alone, as for any runtime error, and slc the form.

3. `[INFERENCE]` **The agreement between models and implementations is stated for "values" and excludes
   `slot-eq`, cost, and crashes** (§42 L1951-1955). The text does not say which values are compared (the final
   value, what is printed, every stored value). `[RAN]` `search.py DESIGN.md 'the same values?'` gives L1954,
   L2234, and L2240 only.

4. `[INFERENCE]` **DESIGN.md does not list the requests or their answers**; it points to `lib/prelude.sl`
   (L1990-1991) and, for `ConfinePaths` and `ConfineOutputBytes`, to MANUAL.md (L1995-1996, quoted in A1.5). So
   the dynamic semantics of the driver's interaction with the world is not in DESIGN.md. `[RAN]`
   `grep -n 'Request' DESIGN.md` gives L1972, L1980, L1984, and L1989 only.

5. `[INFERENCE]` **Environment the run can depend on, by the quotes above:** the answers of `slot-eq`; whether
   and where the host crashes; whether the implementations or the models run (`--no-extern`); the host's
   integer width; the file system as `read-file` sees it, symlinks included; the world's answers to requests;
   standard input; for `native-compute`, whether the program "cannot be compiled" (L3154-3155).

6. `[INFERENCE]` **Not nondeterministic, but global:** the gensym counter, the expansion count, and literal
   interning order are each a function of the order of elaboration over "the whole run, every file included"
   (§65 L2928-2929; §62 L2752-2753; §7 L302-303, all quoted in A1.4 and A2.1 (c)).

## A5. The impossible paths at run time

### A5.1 The sentences

> [QUOTE DESIGN.md:893-897 §21] A branch on a phantom constructor under a `many` or `unique` scrutinee can never run, because no non-erased value is headed by a phantom constructor (§14, rule 2). Everything in scope in such a branch is erased, including the branch's fields, whatever their declarations say, and so is the branch's result.

> [QUOTE DESIGN.md:594-596 §14] Phantom constructors, `erased` functions and type constructors enter scope erased, so by rule 2 none of them can produce a non-erased result.

> [QUOTE DESIGN.md:911-914 §21] **absurd, automatic**: `(absurd C)`, for a constructor that is refuted by the facts in force (§7). It has no fields and no body. It is optional: an unlisted constructor that is refuted needs no branch. It is an error if `C` is not refuted.

> [QUOTE DESIGN.md:915-917 §21] **absurd, by proof**: `(absurd (C f1 ... fn) body)`, a branch that refutes the facts in force (§51) or produces a value of an empty type (§25) instead of the match's result.

> [QUOTE DESIGN.md:924-926 §21] Each constructor has at most one branch. A present branch whose forced unification contradicts is an error. A constructor with no branch must either be refuted or be covered by the `else`.

> [QUOTE DESIGN.md:558-559 §14] the body of an absurd-by-proof branch and the body of an `absurd` function (§21, §25);

> [QUOTE DESIGN.md:1058-1064 §25] Its body does not produce its declared returns. Instead it produces one value of a type with no constructors, such as `False`, which the type's opened `Matchable` (§8) shows to be empty, or it refutes the facts in force (§51). This is the function-level counterpart of the absurd-by-proof branch of §21, and uses the same token (§59). Its body is an erased position (§14), and it compiles to no code.

> [QUOTE DESIGN.md:1066-1070 §25] A contradiction that lives in the fact table rather than in a value, for example two constructors of one opened `Matchable` equated, is used by `open-absurd` (§8), which produces the declared result directly with no empty type in between. When a scrutinee is available, a match whose branches are all refuted produces its declared result (§21).

> [QUOTE DESIGN.md:355-360 §8] `(open-absurd e ann)` is an expression. Its size and result types are given by `ann`, a return telescope like a `match`'s, or `_` for the enclosing one (§26). It takes `e` at `erased`, records nothing, adds nothing, and requires the open to *fail*: it uses a contradiction between the facts in force and the `Matchable`, in the same way an absurd branch uses one with a pattern (§21).

> [QUOTE DESIGN.md:2630-2632 §59] The body is `f`, a `(False)`, where the signature promises `(many A a)`; `absurd` accepts that. The function compiles to no code, and holding it at `many` is fine: the pointer is never followed.

> [QUOTE DESIGN.md:1438-1440 §33] because the source of a non-erased `coerce` is never phantom-headed at run time: no value at run time is headed by a phantom constructor (§14).

> [QUOTE DESIGN.md:1493-1494 §33] Wherever it runs, a non-erased `coerce` produces neither a value headed by a phantom constructor nor an erased function (§14).

> [QUOTE DESIGN.md:1483-1484 §33] A word is never read as the field of a constructor that did not build it:

> [QUOTE DESIGN.md:1668-1670 §36] An absurd body (§21, §25) produces no declared returns, so the promise of its function or branch has nothing to apply to.

> [QUOTE DESIGN.md:1846-1848 §39] The body of an `absurd` at-function is a refutation (§25) and is not checked for erasing.

> [QUOTE DESIGN.md:1499-1502 §33] A proof about a container, for example a proof that every element of a list is wrapped, is built by recursion in an `erased` function that returns the proof (§14). Such a function is checked for termination like any other (§17) and never runs.

### A5.2 Does the text say what a run does if such a path were reached?

`[INFERENCE]` **No. It says only that the path is not reached.** The statements are of three kinds: the path
"can never run" (L894), "the pointer is never followed" (L2632), and "no value at run time is headed by a
phantom constructor" (L1440); the code is absent ("compiles to no code", L1064 and L2631; "It has no fields
and no body", L912); or the form "produces its declared result" (L1068-1070) with no account of how. `[RAN]`
`search.py DESIGN.md 'undefined' 'stuck' 'cannot (run|be reached|happen)' 'unreachable'` gives 0, 0, 0, and 1
match; the one is L283, "Compile-time effects in unreachable code still happen", which is about elaboration.
`'never (run|runs|ran|followed|read|reached)'` gives L289, L894, L1189, L1483, L1502, L2632, and L2674; `'no code'`
gives L1064, L1897, and L2631.

`[INFERENCE]` Two consequences for a formal run. First, a machine needs some treatment of a dispatching
match whose scrutinee's constructor has no code (a refuted constructor with no branch, an `(absurd C)`
branch), of a call through the pointer of an `absurd` function, and of an `open-absurd` or an all-refuted
match in a non-erased position; DESIGN.md supplies none, and the word *never* in these sentences is a claim of the
kind OPEN.md item 1 leaves open. Second, the body of an absurd-by-proof branch and of an `absurd` function
is an erased position (L558-559), so nothing in it runs even if it is reached.

> [QUOTE OPEN.md:9-11] 1. Consistency. Is the language sound with `Type : Type` and no positivity restriction (§10)? Termination is carried by the level and subterm order (§17), and types never compute (§9).

## A6. Erasure and the run

### A6.1 Which positions are erased, and that it is decided before the run

> [QUOTE DESIGN.md:541 §14] These are the **erased positions**:

> [QUOTE DESIGN.md:543-553 §14] - an argument for a parameter or field declared erased; - any argument of a type constructor (§21); - a type or `is` expression (§9, §12); - the final expression of the right-hand side of a `let` with no non-erased binder; - an entry of the `values` that ends a `let`'s right-hand side, when the entry's binder is `erased`; - the body of a function with no non-erased return entry; - an entry of the `values` that ends a function body, when the entry's return entry is `erased`; - the scrutinee of an `erased` match;

> [QUOTE DESIGN.md:554-561 §14] - the proof argument of a `coerce`; every argument of a `coercible-*` form, of `prove-subterm`, of `prove-predates` and of the three axioms; and the proof inside `(subterm p)` and `(predates p)` (§18, §19, §33); - the body of an absurd-by-proof branch and the body of an `absurd` function (§21, §25); - the head of a call written `(at erased (f ...))` (§39); - every sub-expression of an erased expression.

> [QUOTE DESIGN.md:563-567 §14] The branch of a phantom constructor under a non-erased scrutinee is erased throughout (§21). So is the body of an `erased` function: it is checked with every return entry `erased`, whatever its signature says, so such a function can only be held or called at `erased`. Every other position is non-erased.

> [QUOTE DESIGN.md:578-579 §14] A statement's position is that of the expression it belongs to (§27),

> [QUOTE DESIGN.md:601-603 §14] Erasure is decided from the text of one unit alone, a function body against its signature or a run-position statement against its binders, before that unit is compiled or run.

### A6.2 Stripped code: what the evaluator runs

> [QUOTE DESIGN.md:1180-1183 §27] it is elaborated, its erased positions are stripped, the evaluator runs the code, and its results become `Settled` with the resulting values (§29).

> [QUOTE DESIGN.md:1184-1185 §27] A form in an erased position runs nothing, and its results are `Settled` with the token of §5.

> [QUOTE DESIGN.md:1244-1246 §29] A `let` is elaborated, stripped of its erased positions, and run by the evaluator; its binders take the resulting values at their declared multiplicities (§19).

> [QUOTE DESIGN.md:1278-1282 §29] An erased `Settled` holds only the token of §5; its value was never computed, because the erased positions are stripped before the evaluator runs. An erased `Settled` may still be referred to from the erased positions of a statement, because those positions are stripped, not read.

> [QUOTE DESIGN.md:1299-1300 §29] The elaborator checks the form and produces code with the erased positions removed.

> [QUOTE DESIGN.md:3152-3153 §72] The compiled run hands back only the constructor, so its erased fields take the tokens of §5.

### A6.3 Post-erasure code: what the `tail`, `delegate`, and at-function checks read

> [QUOTE DESIGN.md:821-824 §19] Tail position is judged on the post-erasure code, where erased positions, types, coercions and placings are gone and every `let` that only renames has been resolved away (§33, §42).

> [QUOTE DESIGN.md:833-837 §19] **`delegate`.** `(delegate (f ...))` is `tail` plus the same pass-through requirement on the arguments: in the post-erasure code the marked function's body is nothing but the call, and the non-erased parameters without a written `at` (§36) are passed straight through, in order.

> [QUOTE DESIGN.md:1504-1506 §33] **Tail and delegate.** A `coerce` erases to a renaming, so the `tail` and `delegate` checks of §19 see through it, as they see through a placing (§42).

> [QUOTE DESIGN.md:1704-1706 §36] **Tail and delegate.** The `tail` and `delegate` checks (§19) read the post-erasure code with `at` entries omitted, just as they read coerces as renamings.

> [QUOTE DESIGN.md:1647-1650 §36] **What reaches runtime.** The runtime signature of a function consists of its non-erased entries that have no written `at`. An entry written `at`, whether a parameter, a return or an annotation entry, is omitted after erasure: its word is the word of whatever it is `at`.

> [QUOTE DESIGN.md:3021-3023 §66] A call of `place-at`, `place-at-many`, `unplace-at` or `unplace-at-many` is a **placing**. It erases to a renaming of its argument, as a `coerce` does (§33).

> [QUOTE DESIGN.md:1006-1008 §23] A value can be read without giving up its uniqueness: destructure it at `unique`, then in each branch reinvoke the same constructor with every store skipped (§37). That erases to reading the tag and nothing else.

> [QUOTE DESIGN.md:2674-2675 §60] In `unwrap-all` the call is in an erased position and never runs; `(coerce ms p)` is the only runtime content, and it erases to nothing.

> [QUOTE DESIGN.md:2155-2156 §44] The `coerce` is written where it is used: a wrapper function would extract to a call, while the inline `coerce` extracts to nothing.

### A6.4 What still runs, or still happens, where something is erased

> [QUOTE DESIGN.md:1129-1132 §27] Those statements run, or their code is emitted, whether or not the `let`'s own binders are erased. Only the final expression is the position that §14 calls the right-hand side.

> [QUOTE DESIGN.md:1843-1844 §39] Calling an at-function skips its runtime; its arguments are still evaluated, as §15 binds them.

> [QUOTE DESIGN.md:1873-1878 §39] In `(at erased (f ...))` the head is an erased position (§14), so it may be erased: the call is skipped, and no word of the head is read. Only the head is erased: the call stays in its non-erased position, so each argument for a non-erased parameter must be non-erased (§14, rule 2), and its arguments are still evaluated, as for any skipped call.

> [QUOTE DESIGN.md:1895-1898 §40] The match skips its runtime: its scrutinee is evaluated as for any match, but the match itself, its dispatch and its branches, compiles to no code, and the consumer reads its `at` entries back from their targets (§36).

> [QUOTE DESIGN.md:170-172 §4] `compile-error` may stand anywhere a form may; `compile-warn` is a statement. Either fires wherever it is elaborated, erased code included.

> [QUOTE DESIGN.md:283-284 §7] Compile-time effects in unreachable code still happen.

> [QUOTE DESIGN.md:419-421 §9] The elaborated form of a type never contains a function call, and elaborating a type calls none: the only code that runs is a macro's expansion (§62).

### A6.5 Forms that skip or have no run-time content

> [QUOTE DESIGN.md:1835-1841 §39] Its body must **erase to nothing**: after erasure, with `at` entries omitted, the post-erasure code holds no call that is not skipped, no constructor application, no allocation, no store and no copy. Renames, constants, loads from a block, a `values`, a match whose every branch erases to nothing (including its dispatch), a nested definition whose remainder erases, and absurd code all count as nothing.

> [QUOTE DESIGN.md:1860-1865 §39] A non-erased call is skipped exactly when an opened `AtFn` proof names the callee's canonical atom. A skipped call still carries and checks its `predates` or `subterm` proof (§19), and may not be marked `tail`, `notail` or `delegate`. Whatever its body, an at-function compiles to a function that does nothing and returns no word.

> [QUOTE DESIGN.md:610-616 §14] A form whose only claim or effect is about the run is refused in an erased position: `tail`, `notail` and `delegate` (§19), the `at` wrapper around a call (§39), `share` (§16), `cell-match` (§38), `cell-same` (§68) and `fn-same` (§70); and an `erased` function may not be marked `at` (§39).

> [QUOTE DESIGN.md:1759-1760 §37] At `erased` the form uses nothing and yields the same cell under the new type, at `u`, as at `unique` (§14).

> [QUOTE DESIGN.md:1773-1774 §37] In an erased position nothing is used (§14).

> [QUOTE DESIGN.md:2986 §65] In an erased position the form mints nothing.

> [QUOTE DESIGN.md:3060-3062 §68] `EONonErased` wherever it runs, and `EOErased` where it is reached only erased (§14). It compiles to nothing, is refused in an erased position, and requires the prelude.

> [QUOTE DESIGN.md:1964-1965 §42] Its proofs are erased fields and erased functions, so none is built at runtime.

> [QUOTE DESIGN.md:2088-2090 §44] Each is `extern` with a source model in `lib/prelude.sl`; the FFI's implementation drops the arguments the model does not use:

### A6.6 Reading

1. `[INFERENCE]` **The stripped code is not defined beyond its name.** The evaluator runs code "with the erased
   positions removed" (§29 L1299-1300). The text does not give the stripped form of each construct. For
   example, an `erased` match in a non-erased position has "at most one" real branch (§21 L934-935, quoted in
   A3.1 group 1); that its stripped form is that branch's body with no dispatch is my inference, and a match
   with no real branch falls under A5.

2. `[INFERENCE]` **Two descriptions of erased code exist and the text does not identify them.** The evaluator
   runs code with erased positions "stripped" (§27, §29). The `tail`, `delegate`, and at-function checks read
   "the post-erasure code", from which "erased positions, types, coercions and placings are gone", every
   renaming `let` is "resolved away" (§19 L822-824), and `at` entries are omitted (§36 L1705). §44 and §64 also
   speak of what a form will "extract to" (L2156) and of "an extracted program" (L2851-2852), and §27 of code
   that "is emitted" (L1130). `[RAN]` `search.py DESIGN.md 'post-erasure' 'stripp?(ed|ing)' 'extracts? to|extracted' 'emitted'`
   gives 4 (L822, L834, L1705, L1836), 7 (L1181, L1194, L1244, L1280, L1282, L1294, L2239), 3 (L2156 twice, L2851),
   and 1 (L1130) matches. No sentence says the stripped code is the post-erasure code.

3. `[INFERENCE]` **What still runs where a binder or result is erased:** the statements of a `let`'s right-hand
   side (L1129-1130); the arguments of a skipped call (L1843-1844, L1877-1878); the scrutinee of an at-match
   (L1895-1896); macro expansions, in erased code and in types (L419-421); and `compile-error` and
   `compile-warn`, which fire at elaboration (L171-172).

4. `[INFERENCE]` **`coerce`, `share`, and a placing are renamings in the run** (§33 L1504, §66 L3022-3023; for
   `share`, §16 L678-681 says its result "is the result of `e`"). A formal run can therefore treat them as the
   identity on words, on the text.

5. `[INFERENCE]` **A skipped call is decided statically, by an opened proof** (L1860-1862), and an at-function
   also "compiles to a function that does nothing" (L1864-1865), so a call that reaches it without the proof
   has the same result. The text therefore describes two routes to the same outcome, and in neither does the
   at-function's body run.

# Part B. Accept or reject (static semantics as a decision)

## B0. DESIGN.md has no definition of a program being accepted

`[INFERENCE]` The text gives errors one case at a time and never says what it is for a program to be
accepted, nor what an error does to the rest of the run. `[RAN]` `search.py DESIGN.md 'reject'` gives 0
matches. `'accept'` occurs on seven lines (L776, L802, L2332, L2333, L2345, L2363, L2631), each about one form.
`'is an error'` gives 43 matches and `'is refused|are refused|refuses|refused'` gives 17. The only
run-level outcomes the text names are these:

> [QUOTE DESIGN.md:161-163 §4] Warnings go to standard error and do not stop elaboration. `--warnings-as-errors` makes a run that warns fail; a silenced warning does not count (MANUAL.md).

> [QUOTE DESIGN.md:3132 §71] Standard output holds one line: `--goal open: PASS` or `--goal proved: PASS` when the requirement is met, and the same with `FAIL` when it is not.

> [QUOTE DESIGN.md:2427-2428 §54] `dump-context`: stops elaboration with a report of the context (MANUAL.md). Also usable as an expression and as a type.

`[INFERENCE]` So the predicate the owner's theorem is about has to be introduced by the formal spec. The
natural candidate, the elaboration of the prelude and of every file reaching its end with no error, is my
wording and not DESIGN.md's. Because a run-position form "runs as soon as it has been elaborated, before the
code after it is checked" (§27 L1179-1180), that predicate is defined by an elaboration that runs code; it is
not a typing judgment on the source alone. §29 says so directly:

> [QUOTE DESIGN.md:1298 §29] **The round trip.** Checking a run-position form is a dialogue.

## B1. What acceptance depends on besides the source text of the program's files

### B1.1 Command-line flags

`[RAN]` `grep -o -n -- '--[a-z][a-z-]*' DESIGN.md | awk -F: '{print $2}' | sort | uniq -c` lists every flag
DESIGN.md names: `--comptime-unconfine` (1), `--fn-same` (1), `--goal` (5), `--no-extern` (2), `--no-prelude` (5),
and `--warnings-as-errors` (1).

**`--no-prelude`.**

> [QUOTE DESIGN.md:1936 §42] `--no-prelude` starts from these alone.

> [QUOTE DESIGN.md:792-793 §19] Macros rest on the prelude's types, so under `--no-prelude` there are none.

> [QUOTE DESIGN.md:1938-1941 §42] **The `extern` mark.** A `def-adts` entry or a `def-fns` or `def-unique` function may be marked `extern` (§54) only in the source prelude, or anywhere in a program run with `--no-prelude`. Marking one `extern` anywhere else is an error.

> [QUOTE DESIGN.md:1989-1990 §42] It names the prelude's `Request`, so, like literals, it is unavailable under `--no-prelude`.

> [QUOTE DESIGN.md:3018-3019 §66] It rests on the prelude's `Eq`, so under `--no-prelude` there is none.

**`--no-extern`.**

> [QUOTE DESIGN.md:1958-1959 §42] `--no-extern` runs the models instead, and `dune test` runs every test both ways.

> [QUOTE DESIGN.md:1454-1457 §33] It is refused for a phantom `C`, a `C` with a non-erased field, a `C` no opened `Matchable` lists, a `union` or `extern` `Matchable`, under `--no-extern`, and without the prelude.

> [QUOTE DESIGN.md:1596-1597 §35] With the prelude, `(slot-of 0)` is `vacant-slot`; with externs too, `(slot-of k)` is tag slot `k`.

`[INFERENCE]` The last two quotes make acceptance itself differ between a run with externs and one without:
a `coercible-tag`, or a fact that `(slot-of k)` is tag slot `k` for `k` above 0, is available in one and not
the other. Compile-time runs also differ: the models run in place of the implementations (A4.1). `[RAN]` The
reference accepts `special_slot_match26.sl` and rejects it under `--no-extern` (Appendix R, run R2).

**`--fn-same`, `--goal`, `--warnings-as-errors`, `--comptime-unconfine`.**

> [QUOTE DESIGN.md:3125-3126 §70] It is available only under `--fn-same` (MANUAL.md); without the flag it is an error.

> [QUOTE DESIGN.md:3132 §71] `--goal` (MANUAL.md) is `none`, `open` or `proved`. Under `none`, the default, a goal requires nothing and the driver is as §27 describes.

> [QUOTE DESIGN.md:3132 §71] `open` requires a goal and no `qed`. `proved` requires a goal and a `qed`.

> [QUOTE DESIGN.md:2960-2962 §65] `read-file` reads a file relative to a source file or to a name `--comptime-unconfine` adds, one per occurrence, without reading or checking it.

**Flags that only MANUAL.md names.** `[RAN]` `search.py DESIGN.md 'fuel'` gives 0 matches. MANUAL.md, written by
the sessions, describes flags that change what its implementations accept; three examples:

> [QUOTE MANUAL.md:154] `--eval-fuel n` bounds the evaluator.

> [QUOTE MANUAL.md:205-206] `--no-native` compiles nothing: each argument is called by the evaluator, as in `(values (f1) … (fn))`, and slc takes the same flag.

> [QUOTE MANUAL.md:266-267] `--warn-unused` adds the unused-binder warnings of WARNINGS.md 10, for the prelude and every file named; slc takes it too.

### B1.2 Other source text: the prelude, other files, and files inside files

> [QUOTE DESIGN.md:1963-1966 §42] **The source prelude** `lib/prelude.sl` is elaborated before a program's files. Its names are ordinary and may be shadowed. Its proofs are erased fields and erased functions, so none is built at runtime. `lib/prelude.sl` is the reference for what it defines.

> [QUOTE DESIGN.md:1163 §27] Several files on one command line share one scope, in order.

> [QUOTE DESIGN.md:3130 §71] `(goal m T)` sets the **goal** of a unit, the files on one command line.

> [QUOTE DESIGN.md:149-154 §4] `;! file "name"` ends the file being read and starts one named `name`. Each file a source holds this way means what it would as a separate file of the unit (§27), its lines counted from 1 after the pragma, except that its name grants nothing to `read-file` (§65). Its one argument is a non-empty string literal; anything else is an error. A position rebuilt from a `Pos` belongs to the place the `Pos` names.

`[INFERENCE]` DESIGN.md makes `lib/prelude.sl` part of the definition by reference ("the reference for what it
defines", L1966; "the reference for the requests and their answers", L1990-1991) without reproducing it. The
brief notes that the sessions wrote that file.

`[RAN]` The prelude uses a declaration form that DESIGN.md does not describe: `grep -c 'def-prim' lib/prelude.sl`
gives 21, and `grep -c 'def-prim' DESIGN.md` gives 0. DESIGN.md calls the forms so declared "primitives" (L2827,
L2890) and does not say how one is declared. An example from the prelude:

> [QUOTE lib/prelude.sl:2060] (def-prim $ (many slot-eq : (many (Slot) a) (many (Slot) b) -> (many (ErasedMaybe (Eq (Slot) a b)) r)))

`[READ lib/prelude.sl:2480, 2524, 2554, 2571]` `unary` and `prove-literal-lt` are bound in the prelude to `MkMacro`
values built from two prelude functions. I read those four lines and not the functions' bodies. `[RAN]`
`grep -n 'prove-literal-lt\|unary' DESIGN.md` gives L2208, L2209, L2283, L2285, L2288, L2290, and L2291 only, so
neither name is in the registry of §54 (L2398 to L2499); their meaning is given by §45 and §49 and by that code.

### B1.3 The file system, file names, and positions

> [QUOTE DESIGN.md:2962-2966 §65] `here` must name one of these, spelled as the command line names it; standard input is not one. `path` is resolved against that name's directory and must land, through any symlinks, inside that directory or below it. Otherwise, for `NoPos`, and where the read fails, it answers `Fail`. The fence (MANUAL.md) does not apply to it.

> [QUOTE DESIGN.md:1997-1998 §42] **Positions.** `Pos`: `NoPos`, or `MkPos` of a file (`String`), a line and a column (`Nat`).

`[INFERENCE]` A macro's function receives "the position of the call's opening `(` or `$`" (§62 L2738-2739) as a
`Pos` value, an ordinary `many` argument it can compute on. So the forms a macro returns, and with them
acceptance, can depend on a file's name as the command line spells it and on the line and column of a call.
The contents of any file `read-file` reaches are a further input.

### B1.4 What compile-time runs depend on

`[INFERENCE]` Each item below is an input to acceptance because a compile-time run's result can be asserted
by `comptime-match` (§28 L1208-1210) or can steer a macro's output (§62 L2740-2741).

1. **The answers of `slot-eq`** (§67 L3044-3046). See B3.

2. **Whether the evaluator crashes** (§31 L1320-1323). DESIGN.md does not say whether a crash during a
   run-position form is an error. `[RAN]` `search.py DESIGN.md 'fuel' 'time ?out'` gives 0 matches each.

3. **Whether the models or the implementations run** (§42 L1951-1955), since they need not agree "through
   `slot-eq`" and "either may crash where the other does not".

4. **`native-compute`**: whether the program "cannot be compiled", and whether the compiled run crashes (§72 L3153-3156).

5. **The host**: "native integers of at least 63 bits, which the FFI checks" (§42 L1970-1971).

### B1.5 Counters and limits over the whole run

> [QUOTE DESIGN.md:2752-2753 §62] At most 10000 expansions run in one run, every file on the command line included.

> [QUOTE DESIGN.md:2928-2932 §65] `gensym` mints a number, counting from 1 over the whole run, every file included, and returns it with a `Gensym` witness for it and the text `s`. Nothing else makes a witness, so a gensym cannot be forged: building an `SGen` at `many` needs one. `gensym-unique` is an axiom, resting on the counter minting each number once, with one text.

> [QUOTE DESIGN.md:2187-2190 §45] **Interning.** A literal is interned once per program, by what it denotes: a numeral by its number, a character by its code, a string by its characters. So `#\a` and `#\x61` are one entry, and every occurrence of `"ab"` is one entry.

> [QUOTE DESIGN.md:302-303 §7] A literal's entry (§45) is older than every other entry, and of two literals the one interned first is the older.

> [QUOTE DESIGN.md:2285-2287 §49] `(unary a b)` expands to a statement that creates one rule, `a is (Succ ... b)`, with as many successors as separate the two, at most 1024; `b` must not exceed `a`.

1. `[INFERENCE]` **The expansion limit.** The sentence does not say that the 10001st expansion is an error,
   and does not say whether expansions made while the prelude is elaborated count ("every file on the command
   line included", L2753; the prelude is not on the command line).

2. `[INFERENCE]` **The gensym counter.** `gensym` returns its number as `(many (Nat) n)` (§65 L2894-2895), which a
   macro can compute on. The number a call gets depends on how many `gensym` calls ran before it, so on the
   order of expansion, so on the order of elaboration, which the text gives only in part (A2.1 (c)).

3. `[UNKNOWN]` **Interning order.** The older of two unified atoms is the one kept ("the newer becomes an alias of
   the older", §7 L300-301), and which literal is older depends on which was "interned first" (L303). I could not
   determine whether this can change accept or reject, as opposed to the wording of a message.

### B1.6 Constants an implementation chooses

1. `[INFERENCE]` **The order of `Special`'s constructors.** `(slot-tag x)` forces `(slot-of x)` to the tag slot
   of `x`'s constructor (§35 L1599-1601), a tag slot is "per position among the fieldless non-phantom
   constructors" (L1593-1594), "Tag slot 0 is `vacant-slot`" (L1595), and DESIGN.md gives `Special`'s constructors
   no order (§42 L1933-1935; §54 L2400-2401). `[RAN]` A four-line program that asserts `let` is at tag slot 0 is
   accepted by both implementations, and the same program for `match` is rejected by both (Appendix R, run R2).

2. `[INFERENCE]` **The FFI table.** "An `extern` declaration of a name the table lacks, or of a name already
   claimed, is an error" (§42 L1957-1958). The table is not in DESIGN.md. This reaches a user program only
   under `--no-prelude` (L1939-1940).

3. `[INFERENCE]` **Which warnings exist**, under `--warnings-as-errors`. DESIGN.md defines the user's warnings
   (§4) and names two others ("A region that silences nothing produces a warning", L145; "the prelude warns at
   each", L3115). The compilers' own warnings are specified elsewhere:

> [QUOTE CLAUDE.md:110] 16. **Compiler warnings are documented in WARNINGS.md.**

## B2. Places where the text gives the implementation a choice

Each row is `[INFERENCE]` about the effect; the quoted words are at the lines given.

| # | The text | Lines | Can it change accept or reject, or only the report? |
|---|---|---|---|
| 1 | "reported at whichever one the elaborator meets first" | §15 L626 | The report only: both uses are errors. It shows the text treats the elaborator's order as unspecified. |
| 2 | "How a crash is reported is not specified; it need not be a runtime error." | §31 L1322-1323 | Accept or reject, when the crash is at compile time (B1.4 item 2). |
| 3 | "an implementation may always answer it, and which one a call answers may differ between runs" | §67 L3045-3046 | Accept or reject (B3). |
| 4 | "How an implementation finds a slot is left to it." | §69 L3112-3113 | Accept or reject, through the same channel as row 3, when a `Slots` is used at compile time. |
| 5 | "an unspecified word otherwise" | §33 L1475 | Only through `slot-eq` on such a word. |
| 6 | "**Left to the implementation.** How a `Nat`, `Char` or `String` is held at runtime" | §45 L2236-2237 | Only through `slot-eq` on such words. |
| 7 | "A program that cannot be compiled is an error at the form" | §72 L3154-3155 | Accept or reject: what can be compiled is not defined. |
| 8 | "This is its meaning; warnings and error messages may also use where and how it is written." | §8 L409-410 | The report only. |
| 9 | "The prototype's FFI is a fixed table keyed by the declared name." | §42 L1956 | Accept or reject under `--no-prelude` (B1.6 item 2). |
| 10 | The order of elaboration among sibling forms: no sentence | A2.2 | The report (row 1), and accept or reject through the gensym counter and the expansion count (B1.5). |
| 11 | The order of `Special`'s constructors: no sentence | B1.6 item 1 | Accept or reject. |
| 12 | What happens at the expansion limit: "At most 10000 expansions run in one run" | §62 L2752-2753 | Not said to be an error. |
| 13 | `dump-context` "stops elaboration with a report of the context (MANUAL.md)" | §54 L2427-2428 | Neither accepted nor an error, on the text. |

`[RAN]` `search.py DESIGN.md 'unspecified|not specified' 'left to'` gives L1322 and L1475 for the first pattern, and
L699, L2236, L2717, and L3113 for the second (L699 and L2717 are "left to right" and "left to the invocation").

## B3. Is "never both accepted and rejected" compatible with the text?

**Not as a statement about source text alone.** `[INFERENCE]` The quotes below combine into a source text and
two runs, both permitted by DESIGN.md, one of which accepts it and one of which reports an error.

> [QUOTE DESIGN.md:3040-3041 §67] slot-eq : (many (Slot) a) (many (Slot) b) -> (many (ErasedMaybe (Eq (Slot) a b)) r)

> [QUOTE DESIGN.md:1574-1575 §35] As an expression it takes the multiplicity of its position, including `unique`.

> [QUOTE DESIGN.md:1202-1204 §28] Everywhere else, in run position (§27), each of them runs as soon as it is elaborated and its results are `Settled` (§29), as are the binders of the statements there.

> [QUOTE DESIGN.md:1208-1210 §28] `(comptime-match m x (C f1 ... fn))` asserts, at elaboration time, that `x` is a `Settled`, non-erased value headed by `C`. It is an error otherwise.

> [QUOTE DESIGN.md:1215-1217 §28] The type must be an enum, not a union. `C` must not be phantom, and must be listed by the opened `Matchable` of `x`'s type.

> [QUOTE DESIGN.md:3044-3046 §67] `ESome` proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs. `slot-eq` requires the prelude.

> [QUOTE lib/prelude.sl:1263-1266] (def-adts $ (ErasedMaybe : (Type A) -> Type) enum (many ENone : (erased Type A) -> (ErasedMaybe A)) (many ESome : (erased Type A) (erased A a) -> (ErasedMaybe A)))

The steps, each `[INFERENCE]`:

1. `slot-eq` is listed among the expressions of §54 (L2453) and no sentence confines it away from run position.
   `[RAN]` `search.py DESIGN.md 'slot-eq'` gives 8 matches (L1952, L2453, L3037, L3040, L3046, L3068, and L3111 twice);
   none restricts where it may be called.

2. `(slot-of x)` in a `many` position is a `(Slot)` value, so `(slot-eq (slot-of x) (slot-of x))` is a call a
   program can write in run position, where it runs and its result is `Settled`.

3. `ErasedMaybe` is an enum whose two constructors are `many` (the prelude lines above; DESIGN.md uses the type
   and does not declare it), so `comptime-match` may assert either constructor of that result.

4. A run in which the call answers `ESome` accepts `(comptime-match many r (ESome a e))`; a run in which it
   answers `ENone`, which "an implementation may always" do (§67 L3045), makes the same form "an error" (§28 L1209).

`[RAN]` Both implementations accept the construction and so let a `slot-eq` answer reach acceptance
(Appendix R, run R1): `sloteq_some.sl` is accepted and `sloteq_none.sl` is rejected by the reference, with and
without `--no-extern`, and by `slc --interpret`. An implementation that always answered `ENone` would do the
reverse, within the letter of §67. This is implementation behaviour; it shows only that nothing in either
checker forbids the construction.

Other routes for the same flow, each `[INFERENCE]`:

- A macro's function may call `slot-eq` and return different forms for different answers (§62 L2740-2741: "The
  forms it returns replace the call").

- A `Slots` table used at compile time: "§42's exception for `slot-eq` covers what the implementations answer"
  (§69 L3111-3112).

- A crash: §42 lets a model and its implementation each "crash where the other does not" (L1954-1955), and §72
  makes a crashed compiled run "an error at its argument" (L3155-3156) where the evaluator might not crash.

- `read-file`: the file read may differ between two runs of one source text.

`[INFERENCE]` **What would make the theorem true.** The statement can hold only relative to everything in B1
being fixed, including one answer for each compile-time `slot-eq` call. The ways I can see to fix it are a
decision for the owner (C3): the spec's compile-time `slot-eq` always answers `ENone` (permitted by "may
always answer it", §67 L3045, but then both implementations disagree with the spec on `sloteq_some.sl`); the spec's
acceptance takes the answers as a parameter, and the theorem is stated for each choice of answers; or
acceptance is defined over all permitted runs. The nondeterminism does not threaten soundness as §67 states
it, since "`ENone` proves nothing" (L3044-3045).

**OPEN.md.** Items 3 and 4 are near this and do not ask it:

> [QUOTE OPEN.md:34-37] 3. Slot equality. What must the soundness claim for slots (§35) be, and does it hold? In particular, a user type indexed by `(Slot)` can make a forcing merge two slots in a branch that is not refuted. The owner believes it is sound.

> [QUOTE OPEN.md:38-41] 4. Facts from stored values. A `comptime-match` trusts the evaluator (§29). Should a reference evaluator inside the checker arbitrate runs that produce facts, so that a wrong evaluation cannot produce a `(False)` token through an erased field?

## B4. Where a program starts: bytes, tokens, or `Raw`

### B4.1 What the text fixes about reading

> [QUOTE DESIGN.md:39-48 §1] The syntax is s-expressions. A file is a sequence of statements, optionally followed by one expression (§27). A `;` starts a comment that runs to the end of the line. A `;!` starts a pragma (§4). An atom is any run of characters other than whitespace, parentheses and `;`. A token that begins with `"` is a string literal. Atoms made only of digits, and atoms of the form `#\c`, are numeral and character literals (§45). A token `#"..."` is a raw name: the string's bytes, read as a string literal (§45), whatever they are. It is always a name, so `#"_"`, `#"45"` and `#""` are names, and `#"let"` is `let`. Names are compared byte for byte, so they are case-sensitive.

> [QUOTE DESIGN.md:55-58 §1] A name written without `#"` may not begin with `__`; such a name is written raw. Those spellings are reserved for the compilers' messages, which write a name that does not read back plain as a raw name.

> [QUOTE DESIGN.md:60 §1] Every built-in name and built-in syntax is ASCII.

> [QUOTE DESIGN.md:66-70 §2] `$` opens a list form exactly as `(` does, but it does not consume the `)` that ends it. The form reads items until the terminator of the enclosing form, and leaves that terminator for the enclosing form to consume. If there is no enclosing form, the missing `)` is an error. Only a bare `$` token is special; `foo$bar` is an ordinary atom.

> [QUOTE DESIGN.md:128-131 §4] A pragma line `;! warn NAME message` names a type constructor, a value constructor or a function, meaning an entry of `Fn` or `UniqueFn` type, that is in scope, resolved through its aliases, and gives a message.

> [QUOTE DESIGN.md:137-138 §4] A `;! warn` must be written between top-level forms.

> [QUOTE DESIGN.md:142-144 §4] `;! suppress warn NAME` silences these warnings for `NAME` until the matching `;! restore warn NAME`, or to the end of the file if there is none. The pair may appear at any nesting depth.

> [QUOTE DESIGN.md:156-159 §4] Pragmas are read from source text alone. Nothing a macro returns is a pragma, and no parser from text to `Raw` may process one. Any other word after `;!` is an error.

> [QUOTE DESIGN.md:2165-2174 §45] **Syntax.** A numeral is an atom made only of digits, with no leading zero: `0` or `42`. A numeral written plain is never a name, and a binder written as a plain numeral is an error; `#"42"` is a name (§1). A character literal is `#\c` for a single byte `c` that the word syntax admits, or `#\space`, `#\newline`, `#\tab` or `#\xHH`, where `HH` is two hexadecimal digits. `#\(`, `#\)` and `#\;` must be written in the hex form. A string literal is `"..."`, starting at the start of a token, with the escapes `\n`, `\t`, `\"`, `\\` and `\xHH`, where `HH` is two hexadecimal digits giving one byte. Any other byte, including a newline, stands for itself.

> [QUOTE DESIGN.md:2771-2775 §63] `Raw` is `extern` so that its representation is the reader's own syntax tree: a macro's arguments and output pass without copying, which would let nested expansions cost exponentially more than the macros' own work. `RawWild` is a `_`; a raw name `#"_"` is a `RawSymbol` (§1).

> [QUOTE DESIGN.md:2777-2783 §63] A name in the source reaches a macro as `(RawSymbol p (SName s))`. A literal reaches it as an `MMany` handle (§64) to its interned entry (§45): each top-level form of the source has its literals interned and replaced by such handles just before it is elaborated. So `Raw` has no literal constructor, and a macro builds a literal by interning it (§65). A handle to a literal is treated as the literal wherever a refusal is worded, and is shown as the literal.

### B4.2 Reading

1. `[INFERENCE]` **The text starts at characters and bytes.** A file is characters (L42) whose names "are compared
   byte for byte" (L47-48), and pragmas "are read from source text alone" (L156). A spec that must give every
   source text an outcome (handoff, owner's item 3) has to start there, or state separately that reading is
   total.

2. `[INFERENCE]` **`Raw` cannot be the start as it stands.** `Raw` "has no literal constructor" (L2780-2781): a
   literal is in a `Raw` only as a handle to an interned entry, and interning happens "just before" each
   top-level form "is elaborated" (L2779-2780), against the literal table that the macro world carries (§65
   L2882-2884, quoted in A1.4). So a `Raw` value with a literal in it exists only relative to an elaboration
   state. Pragmas are also outside `Raw` (L156-157). A spec that starts after reading needs a syntax tree of its
   own with literals, and a separate account of pragmas.

3. `[INFERENCE]` **Reading and elaboration interleave by top-level form** (L2779-2780). The text does not say
   whether a file is read whole before any of its forms is elaborated, so it does not say whether a reading
   error late in a file leaves earlier run-position forms run. That does not change accept or reject.

4. `[INFERENCE]` **Lexical details the text leaves unsaid**, each needed by a spec that starts at bytes:
   which bytes are whitespace (`[RAN]` `search.py DESIGN.md 'whitespace'` gives L42 only); what an atom made only
   of digits with a leading zero is (L2165-2166 excludes it from numerals and says no more); where on a line a
   `;!` may begin, and where a pragma's message ends ("A pragma line", L128); what a `"` inside an atom does
   ("starting at the start of a token", L2171); what a `#` atom that is neither `#\c` nor `#"..."` is; how line
   and column are counted for `Pos` (the only sentence is "its lines counted from 1 after the pragma", L151),
   which matters because a macro can compute on them (B1.3).

## B5. Parts DESIGN.md itself marks as provisional, or leaves to an implementation or another file

`[RAN]` `search.py DESIGN.md 'provisional' 'for now' 'relaxed' 'prototype' 'in flux' 'tentative' 'today' 'currently' 'not yet' 'at present'`
gives one match each for the first five (L31, L779, L1206, L1956, L507) and 0 for the rest.

**Marked provisional or likely to change.**

> [QUOTE DESIGN.md:31 §intro] - Sugar, provisional: §46 to §53.

> [QUOTE DESIGN.md:505-507 §13] There is no default: wherever the multiplicity is a choice, it is written, which cuts down on mistakes while the design is in flux.

> [QUOTE DESIGN.md:776-779 §19] If a type or `is` clause is written, it is checked for identity against the inferred one (§9); a mismatch is an error. This is deliberately strict for now.

> [QUOTE DESIGN.md:1204-1206 §28] A definition that is wanted as `Settled` is therefore written in run position (see `xs` in §57). This may be relaxed if it proves heavy.

> [QUOTE DESIGN.md:1956 §42] The prototype's FFI is a fixed table keyed by the declared name.

`[INFERENCE]` §46 to §53 are: `_` as a level (§46), `_` as a match annotation (§47), inferred decrease
annotations (§48), `unary` (§49), `_` for an inferred argument with its metas (§50), refuting in an absurd
body (§51), `let-match` with branches (§52), and fetch forms in a type (§53). §51 to §53 are cited by
non-provisional sections as the definition of something they use: §21 L916 and §25 L1061 cite §51; §27 L1154
cites §52; §6 L229, §18 L732, §29 L1251, and §39 L1859 cite §53. So the header's "provisional" (L31) covers
material the core sections depend on.

**Left to an implementation, or not specified.**

> [QUOTE DESIGN.md:1322-1323 §31] How a crash is reported is not specified; it need not be a runtime error.

> [QUOTE DESIGN.md:1475 §33] built, and an unspecified word otherwise.

> [QUOTE DESIGN.md:2236-2238 §45] **Left to the implementation.** How a `Nat`, `Char` or `String` is held at runtime, and whether a literal's entries are produced by elaborating statements or created directly to the same effect.

> [QUOTE DESIGN.md:3112-3113 §69] How an implementation finds a slot is left to it.

> [QUOTE DESIGN.md:18-19 §intro] This is an aim for the language, not for the implementations, whose own speed, and the speed of the code they produce, are not aims.

**Defined by pointing at another file.** `[RAN]` `grep -n 'MANUAL' DESIGN.md` gives L4, L163, L1120, L1995, L2428,
L2966, L3125, and L3132; `grep -n 'lib/prelude.sl' DESIGN.md` gives L1963, L1966, L1990, and L2089;
`grep -n 'tests/' DESIGN.md` gives L1227, L2512, L2632, L2690, L2721, and L3034.

> [QUOTE DESIGN.md:3-6 §intro] This file is the specification of Sleight, the language. OPEN.md lists the open questions. MANUAL.md describes the implementations and their command lines; README.md introduces the repository. EXAMPLES.md indexes the tests. The code and the other files cite sections of this file by number.

> [QUOTE DESIGN.md:1966 §42] `lib/prelude.sl` is the reference for what it defines.

> [QUOTE DESIGN.md:1119-1120 §27] `slot-tag` and `open-at-fn` (§35, §39), `dump-context` (MANUAL.md), `compile-error` and `compile-warn` (§4), and `goal` and `qed` (§71).

> [QUOTE DESIGN.md:1995-1996 §42] MANUAL.md describes `ConfinePaths`, `ConfineOutputBytes` and the command-line flags that stand in for them.

**Present only under a flag.**

> [QUOTE DESIGN.md:3125-3126 §70] It is available only under `--fn-same` (MANUAL.md); without the flag it is an error.

> [QUOTE OPEN.md:199] 36B. Should `fn-same` (§70) be available without `--fn-same`, or at all?

`[INFERENCE]` **Parts a formal spec has to decide whether to include**, from the above: the sugar of §46 to §53
(of which §51 to §53 are load-bearing); the whole prelude, with its `def-prim` declarations, requests, and
macros (`unary`, `prove-literal-lt`); the FFI table and the `--no-extern` mode; `fn-same`; `native-compute`;
`dump-context`; the warnings; the flags of MANUAL.md; and the printing of §45, which is the driver's output.

# Part C. Gaps and ambiguities a formal spec would have to resolve

Each item is a question for the owner, ordered by how much its answer would shape the formalization. Each
item's statement of the gap is `[INFERENCE]` from the quotes under it. The line headed **OPEN.md** says whether the question is
already listed there; each such line rests on a `[RAN]` `grep -n -i` of OPEN.md with the pattern shown.
DECISIONS.md lists nothing at all, so no item is recorded there:

> [QUOTE DECISIONS.md:14-16] ## Decided None at present.

> [QUOTE DECISIONS.md:18-20] ## Approved rules awaiting wording None at present.

> [QUOTE DECISIONS.md:22-24] ## Proposals, not approved None at present.

> [QUOTE DECISIONS.md:26-28] ## Pending edits None at present.

## C1. Is the spec's run the machine of words and blocks?

**Question.** Is the representation of §33 (one word per value, immediates and pointers to blocks, tags) part
of what the language means, so that the spec's run is a machine over words and blocks, or is it only "a
requirement on the implementation" (L1460) beside a more abstract meaning? If the first, which of A3.3's open points
does the spec fix?

> [QUOTE DESIGN.md:1459-1460 §33] Coercion is free only if the representations coincide, so the following is a requirement on the implementation.

> [QUOTE DESIGN.md:1319-1320 §31] The semantics is that of a machine with unlimited stack and heap.

> [QUOTE DESIGN.md:3044 §67] `ESome` proves that `a` and `b` hold one word (§38).

The slot rules state facts about words in the language's own terms (A3.1 groups 3 to 5 and 10), so a spec
that lacks words cannot say what `ESome` proves. See D8. The handoff records the owner's suspicion and that
it is unconfirmed:

> [QUOTE handoff.md:24] The owner suspects the spec's run should be a mutating heap machine from the start.

**OPEN.md:** not asked. Item 3 (quoted in B3) asks what the soundness claim for slots must be. Pattern
`machine\|heap`: no line.

## C2. Evaluation order

**Question.** (a) Is the order among the sibling sub-expressions of one form fixed, or may a run take any
order? (b) If fixed, which order, and does the head come first inside a body as it does in run position?
(c) Is §15's placement of argument temporaries a statement about the run, and under which reading (A2.3: R1
puts a temporary before the whole `values`, R2 beside its entry)? (d) Do the head and the scrutinee get
temporaries as arguments do? (e) Do the statements of a body run in the order written? (f) Does the answer go
into DESIGN.md or stay a choice of the formal spec?

> [QUOTE DESIGN.md:655-661 §15] Every argument to a constructor, a function or a cell behaves as if it were first bound to an anonymous variable. An argument that is already a variable is not rebound. That binding is a statement (§27) placed just before the statement or final form that contains the call, so its entry stays in scope, anonymously, for the rest of the expression around it, as the entries of a `let`'s right-hand-side statements do.

> [QUOTE DESIGN.md:1319 §31] Evaluation is eager.

> [QUOTE DESIGN.md:236 §6] The head is elaborated first.

The searches that support the claim that no sentence fixes the order are in A2.2.

**OPEN.md:** not asked. It has an empty heading "Argument temporaries" (OPEN.md L128, quoted in A2.5). Pattern
`order\|evaluat`: eight lines, none about evaluation order (listed in A2.5).

## C3. `slot-eq` at compile time, and "never both accepted and rejected"

**Question.** May a compile-time run's `slot-eq` answer reach acceptance, as both implementations allow
(Appendix R, run R1)? If so, which statement does the owner want: acceptance relative to a given assignment of
answers; a spec whose compile-time `slot-eq` always answers `ENone`; or acceptance over all permitted runs? If
not, what forbids it?

> [QUOTE DESIGN.md:3044-3046 §67] `ESome` proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs. `slot-eq` requires the prelude.

> [QUOTE DESIGN.md:1208-1210 §28] `(comptime-match m x (C f1 ... fn))` asserts, at elaboration time, that `x` is a `Settled`, non-erased value headed by `C`. It is an error otherwise.

The derivation is in B3.

**OPEN.md:** not asked. Items 3 and 4 are near (both quoted in B3). Pattern `deterministic\|determin\|between runs`: no line.

## C4. A crash at compile time

**Question.** When a run-position form's run crashes, is the program rejected, or is that a third outcome
that the accept-or-reject theorem sets aside (for example by speaking of the
machine "with unlimited stack and heap", L1319-1320, which does not crash)? The same for a crash inside a macro's function.

> [QUOTE DESIGN.md:1320-1323 §31] A real run may crash where the host cannot represent what is asked of it. A crash produces no value, never a different one. How a crash is reported is not specified; it need not be a runtime error.

> [QUOTE DESIGN.md:3155-3156 §72] a run that crashes is an error at its argument.

MANUAL.md's sentence that the implementations refuse such a form is quoted in A4.2 item 2; it is not DESIGN.md.

**OPEN.md:** not asked. Pattern `crash`: no line.

## C5. What a program is, and what being accepted means

**Question.** What is the input of the accept-or-reject theorem: the bytes of the files alone, or those with
the flags, the prelude's text, the files `read-file` can reach, and the file names? And is being accepted the
elaboration of the prelude and every file ending with no error, with `--warnings-as-errors` and `--goal` as
separate predicates on top?

> [QUOTE DESIGN.md:1163 §27] Several files on one command line share one scope, in order.

> [QUOTE DESIGN.md:1963-1964 §42] **The source prelude** `lib/prelude.sl` is elaborated before a program's files.

> [QUOTE DESIGN.md:161 §4] Warnings go to standard error and do not stop elaboration.

B0 gives the searches showing that the text defines neither word; B1 lists the inputs.

**OPEN.md:** not asked. Pattern `accept\|reject`: four lines of OPEN.md (L65, L77, L112, L143), each about one form.

## C6. Models or implementations of the extern functions

**Question.** Does the spec's run execute the prelude's models of the extern types and functions, or a
description of the FFI's implementations? Is "An `extern` implementation must agree with its model" (L1951-1952) then a
hypothesis of the compiler's theorem, and how is its `slot-eq` exception stated?

> [QUOTE DESIGN.md:1951-1955 §42] An `extern` implementation must agree with its model: except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31).

> [QUOTE DESIGN.md:1941-1944 §42] For a type, its constructors and `Matchable` say what its values are and how they are taken apart, and the FFI supplies the representation together with construction and matching over it.

**OPEN.md:** listed in part, as item 14.

> [QUOTE OPEN.md:67-70] 14. A source-level way to declare extern types and functions, in place of the prototype's fixed table (§42). What should guarantee that an implementation agrees with its model, beyond the requirement stated there?

## C7. Is `lib/prelude.sl` part of the specification?

**Question.** DESIGN.md defers to the prelude for what it defines and for the requests and their answers. Is
the prelude's text then inside the formal spec (with its `def-prim` declarations, which DESIGN.md does not
describe, its macros such as `unary` and `prove-literal-lt`, and its requests), or does the spec cover the
language under `--no-prelude` plus a stated interface?

> [QUOTE DESIGN.md:1966 §42] `lib/prelude.sl` is the reference for what it defines.

> [QUOTE DESIGN.md:1990-1991 §42] `lib/prelude.sl` is the reference for the requests and their answers.

> [QUOTE lib/prelude.sl:1401] (def-prim $ (many place-at : (erased Type T) (unique T x) -> (unique (Placed (slot-of x) T x) p at x)))

The `def-prim` counts are in B1.2.

**OPEN.md:** not asked. Pattern `prelude`: four lines of OPEN.md (L96, L135, L141, L145), none on this.

## C8. Where the spec's input starts

**Question.** Does the spec start at bytes, as the handoff's "every program's source code" suggests, or at a syntax tree? If
at bytes, the lexical points of B4.2 item 4 need answers. If at a tree, it cannot be the prelude's `Raw` as it
stands, because a literal is in a `Raw` only as a handle to an interned entry (B4.2 item 2), and pragmas are
outside `Raw`.

> [QUOTE DESIGN.md:2779-2782 §63] each top-level form of the source has its literals interned and replaced by such handles just before it is elaborated. So `Raw` has no literal constructor, and a macro builds a literal by interning it (§65).

> [QUOTE DESIGN.md:156-157 §4] Pragmas are read from source text alone. Nothing a macro returns is a pragma, and no parser from text to `Raw` may process one.

**OPEN.md:** not asked. Pattern `reader\|lexical\|whitespace\|\bbyte`: no line.

## C9. Addresses: fresh, shared, reused

**Question.** In the spec's machine, (a) what does a "fresh" block (§37 L1756) promise; (b) may two blocks built
separately with equal contents be one block when both are `many`; (c) is an address ever reused; (d) does a
block keep one address for the whole run? The handoff's proposal B answers (a), (c), and (d) one way and is
unapproved:

> [QUOTE handoff.md:36] a step that allocates may take any address never taken before; a block keeps its address for the rest of the run whatever is written into it;

> [QUOTE DESIGN.md:1696-1698 §36] Neither does canonical equality: two separately built cells with equal contents are `is`-equal and are two blocks.

> [QUOTE DESIGN.md:1701-1702 §36] address equality does not change when contents do.

> [QUOTE DESIGN.md:1809-1810 §38] Nothing relies on two slots being distinct.

**OPEN.md:** not asked. Item 3 is near. Pattern `fresh\|address\|reuse\|garbage`: four lines of OPEN.md (L89, L119, L122, L125), none on this.

## C10. Function values

**Question.** What word is a function value: a pointer to a block that holds what the function closes over,
or something else? When are two function values one word (two evaluations of one nested `def-fns`; a
`delegate`-bodied function and its callee)? What does `fn-same` then conclude?

> [QUOTE DESIGN.md:1327 §32] A function defined by `def-fns` is a closure over its scope.

> [QUOTE DESIGN.md:1247-1248 §29] a function's value is its compiled code,

> [QUOTE DESIGN.md:1488-1489 §33] The pointer of a `delegate`-bodied function is its callee's pointer (§19).

**OPEN.md:** listed for `fn-same`, as item 36B (quoted in A3.3 item 2 and B5). The general question is not asked.

## C11. The order of elaboration

**Question.** Is the order in which the elaborator reaches sibling forms part of the language? It is
observable: through the numbers `gensym` returns, the expansion count against its limit, which literal is
interned first, which of two errors is reported, and, in run position, the order of the run.

> [QUOTE DESIGN.md:624-626 §15] A use at unique together with any other non-erased use of the same binder is an error, reported at whichever one the elaborator meets first.

> [QUOTE DESIGN.md:2928-2929 §65] `gensym` mints a number, counting from 1 over the whole run, every file included,

**OPEN.md:** not asked. Pattern `elaborat`: no line.

## C12. What an error does, and the outcomes that are neither

**Question.** (a) Does the first error end elaboration, so that no later run-position form runs? (b) Is a
program that reaches `dump-context` rejected? (c) Is the 10001st expansion an error, and do the prelude's own
expansions count? (d) If the spec's rejection is a positive relation, as the handoff proposes, must it say
which error is reported, or only that there is one?

> [QUOTE handoff.md:40] rejected ones carry a derivation of a positive `Fails` relation;

> [QUOTE DESIGN.md:2427 §54] `dump-context`: stops elaboration with a report of the context

> [QUOTE DESIGN.md:2752-2753 §62] At most 10000 expansions run in one run, every file on the command line included.

**OPEN.md:** (c) is near item 8; the rest is not asked.

> [QUOTE OPEN.md:49] 8. Macros. Open: macro termination beyond a global expansion limit,

## C13. Stripped code and post-erasure code

**Question.** Is the code the evaluator runs (erased positions "stripped", L1181) the same as the "post-erasure
code" (L822) that the `tail`, `delegate`, and at-function checks read (coercions, placings, renaming `let`s, and `at`
entries also gone)? And what is the stripped form of each construct, for example of an `erased` match with one
real branch?

> [QUOTE DESIGN.md:1299-1300 §29] The elaborator checks the form and produces code with the erased positions removed.

> [QUOTE DESIGN.md:821-824 §19] Tail position is judged on the post-erasure code, where erased positions, types, coercions and placings are gone and every `let` that only renames has been resolved away (§33, §42).

The handoff says the owner's concern about running stripped code goes away with a mutable heap, and that the
session's combined reading is unconfirmed:

> [QUOTE handoff.md:24] The session reads these together as: the spec's run is a mutating heap machine on code with its erased positions removed. The owner has not yet confirmed that reading.

**OPEN.md:** near item 2, which asks whether the collapsed program would "run to the same values".

> [QUOTE OPEN.md:17-18] 2. Erasure conservativity. Take any program that compiles and collapse `unique` to `many`:

## C14. The impossible paths

**Question.** What does the spec's machine do at a dispatching match whose scrutinee's constructor has no
code, at a call through an `absurd` function's pointer, and at an `open-absurd` or an all-refuted match in a
non-erased position: has it no rule there, so that agreement with the spec is vacuous on such runs, or is their
absence a hypothesis of the theorem?

> [QUOTE DESIGN.md:893-895 §21] A branch on a phantom constructor under a `many` or `unique` scrutinee can never run, because no non-erased value is headed by a phantom constructor (§14, rule 2).

> [QUOTE DESIGN.md:2631-2632 §59] The function compiles to no code, and holding it at `many` is fine: the pointer is never followed.

**OPEN.md:** near item 1 (quoted in A5.2). The handoff's owner item 1 says no consistency theorem is expected:

> [QUOTE handoff.md:19] No `no_false` theorem is expected: for consistency, proving properties about the language runs into a diagonalization argument.

## C15. Termination of compile-time runs

**Question.** DESIGN.md calls the language's functions "total" (L1994) and rests termination on levels; it does not
prove it. Does the theorem assume that every compile-time run halts (the handoff's hypothesis H), and is the
expansion limit the only bound on macros?

> [QUOTE handoff.md:22] under a hypothesis H that every accepted compile-time form's spec run halts, `compile` is a total function to accepted-or-rejected.

> [QUOTE DESIGN.md:1993-1994 §42] It never recurses, so an unbounded interaction is the driver's loop over total functions.

> [QUOTE DESIGN.md:696-699 §17] Termination rests on levels. A function's parameters may be marked `subterm`; the marks are part of its signature. Every call decreases a lexicographic order whose first component is the level, followed by the `subterm`-marked arguments from left to right.

**OPEN.md:** items 1 and 8 are near. Pattern `terminat\|halt\|fuel`: two lines of OPEN.md (L10, L49).

## C16. The driver

**Question.** (a) With several files, which final values does the driver act on? (b) Does the evaluator or
compiled code apply a `Program`'s continuations and a `String -> String` final? (c) Where are the requests and
their answers specified, and what does `Exit`'s code do? (d) Is the driver's run inside the theorem "the
output's run matches the spec's run"?

> [QUOTE DESIGN.md:1163-1165 §27] A file that ends in a statement produces nothing. Otherwise the type of the final value decides what the driver does with it.

> [QUOTE DESIGN.md:1973 §42] `Exit` carries a `U8` exit code.

**OPEN.md:** not asked. Pattern `driver\|Program\|exit`: four lines of OPEN.md (L17, L33, L161, L180), none on the driver.

## C17. Immediates and `imm`

**Question.** Is an immediate a notion of the spec's machine? Does an `(imm o n)` mark change anything in the
run, or is it a checked claim with no effect? Does `ImmNat` hold when the models run (D9)?

> [QUOTE DESIGN.md:1791-1792 §37] `(imm o n)` before an argument, or before a `cell-write` item, marks a store whose old and new words are both immediates.

> [QUOTE DESIGN.md:2061-2063 §44] `(Imm A v)` says that `v` is an immediate however it is built, and the `-imm` operations take it as evidence. `ImmNat` gives it for a `Nat` below `u62-modulus`,

**OPEN.md:** not asked. Pattern `\bimm\b\|immediate`: no line.

## C18. Details of the representation

**Question.** (a) What does "a single field is stored bare" (L1465) mean beside "an unmarked type of newtype shape is
a block" (L1482-1483; D3)? (b) Is a fieldless value of a tagged `extern` type a position word (D4)? (c) What does "an
unspecified word" (L1475) cover, and may `slot-eq` be asked of it? (d) What is the order of `Special`'s constructors?
(e) What is the layout of a block?

> [QUOTE DESIGN.md:1464-1465 §33] A value is the tuple of its constructor's non-erased fields; a single field is stored bare.

> [QUOTE DESIGN.md:1474-1475 §33] however the value was built, and an unspecified word otherwise.

**OPEN.md:** not asked. Pattern `represent\|\bword`: four lines of OPEN.md (L26, L46, L75, L203), none on these.

## C19. Top level, run position, and the binders of §29

**Question.** Is code in a match branch of a top-level statement at the top level (§20) and not in run
position (§27), and does the spec need both notions (D1)? Do a call's head and a match's scrutinee have
binders that become `Settled`, as §29 says, when §15 gives them none (D2)?

> [QUOTE DESIGN.md:850-852 §20] At the file's top level, which means anywhere outside a function body, including the match branches of a top-level statement, any constructor and any function may be called with no `Predates` or `Subterm` proof.

> [QUOTE DESIGN.md:1178-1179 §27] **Run position.** A form is in run position when it is under no function body and no match branch.

**OPEN.md:** not asked. Pattern `top level\|run position`: no line.

## C20. Which provisional, flag-gated, and delegated parts are in the spec

**Question.** Does the formal spec include: the sugar of §46 to §53, which the header calls provisional and
which §6, §18, §21, §25, §27, §29, and §39 rely on; `fn-same`; the `--no-extern` mode; the compilers' warnings
(needed only if `--warnings-as-errors` is in scope); and `dump-context`?

> [QUOTE DESIGN.md:31 §intro] - Sugar, provisional: §46 to §53.

**OPEN.md:** only `fn-same` is asked (item 36B). Pattern `provisional\|sugar`: one line of OPEN.md (L102, about a shadowing sugar).

## C21. `native-compute`

**Question.** `native-compute` makes acceptance depend on whether a toolchain can compile the program and on
whether a compiled run crashes. Is it in the spec, and if so is it specified by its meaning, "`(values (f1) … (fn))`" (L3149), alone?

> [QUOTE DESIGN.md:3153-3156 §72] It may crash where the evaluator would not, and the other way round (§31). A program that cannot be compiled is an error at the form, and a run that crashes is an error at its argument.

**OPEN.md:** not asked. Pattern `native-compute`: no line.

## C22. What it is for two runs to give "the same values"

**Question.** The requirement on externs and the handoff's proposed theorem targets ("compile-time values
match the spec's run; the output's run matches the spec's run") both compare values across runs. Compared
how: as words, as what is printed, or up to a relation on heaps? Position words, `slot-eq` answers, and the
representations of `Nat`, `Char`, and `String` may differ between the runs being compared.

> [QUOTE DESIGN.md:1953-1954 §42] running the models instead of the implementations must give a program the same values, though not the same cost,

**OPEN.md:** not asked as such; item 2 uses "run to the same values" (OPEN.md L23-24) without defining it.

# Part D. Internal tensions

Each item quotes two or more passages that pull against each other on the points of Parts A and B. Each
reading is `[INFERENCE]`. I found none of them listed in OPEN.md (`[RAN]` the greps of Appendix S, search S14)
or in DECISIONS.md, which has no entries; OPEN.md items 3 and 14 are near D8 and D14.

## D1. The top level is wider than run position, yet "A file's top level is run position"

> [QUOTE DESIGN.md:850-852 §20] At the file's top level, which means anywhere outside a function body, including the match branches of a top-level statement, any constructor and any function may be called with no `Predates` or `Subterm` proof.

> [QUOTE DESIGN.md:1178-1179 §27] **Run position.** A form is in run position when it is under no function body and no match branch.

> [QUOTE DESIGN.md:1187-1188 §27] A file's top level is run position, so calls there need no proofs (§20).

> [QUOTE DESIGN.md:280-281 §7] A run-position form's match branches are gated like any other.

Code in a branch of a top-level `match` is at the top level by §20 (it calls freely) and is not in run position
by §27 (it is under a match branch, so it does not run when elaborated and its results are `Hypothetical`).
The third quote identifies the two. A formal spec needs both notions and a rule for such a branch.

## D2. §29 cites §15 for binders that §15 does not give

> [QUOTE DESIGN.md:655-656 §15] Every argument to a constructor, a function or a cell behaves as if it were first bound to an anonymous variable.

> [QUOTE DESIGN.md:1240-1242 §29] its results, the elaborator's own binders for its head, arguments and scrutinee (§15),

§15 gives a binder to arguments only. §29 speaks of binders for a head and a scrutinee and cites §15. Whether
a head that is a form and a scrutinee that is a form are bound before the statement or final form that
contains them, as arguments are, is therefore unsettled (C2 (d), C19).

## D3. "a single field is stored bare" against "an unmarked type of newtype shape is a block"

> [QUOTE DESIGN.md:1464-1465 §33] A value is the tuple of its constructor's non-erased fields; a single field is stored bare.

> [QUOTE DESIGN.md:1480-1483 §33] That representation is mandatory for a type marked `newtype` and forbidden for a type that is not marked: an unmarked type of newtype shape is a block (§37).

Read alone, the first says a constructor with one non-erased field is represented as that field. The second
forbids exactly that for a type not marked `newtype`. The first may mean something narrower (for example that
a block of one field holds the field's word with nothing around it); the text does not say.

## D4. The word of a fieldless value of a tagged `extern` type

> [QUOTE DESIGN.md:1470-1476 §33] A value with no non-erased field is the word of the `Nat` of its position among the fieldless non-phantom constructors when its type is tagged, the word of `vacant-slot` (§35) when its type is untagged and not marked `extern`, however the value was built, and an unspecified word otherwise. In the first two cases this is the word of its constructor's tag slot (§35).

> [QUOTE DESIGN.md:1591-1593 §35] A non-phantom constructor `C` with no non-erased field, of a type not marked `extern` or `newtype`, has a tag slot when an opened `Matchable` lists it.

> [QUOTE DESIGN.md:1941-1944 §42] For a type, its constructors and `Matchable` say what its values are and how they are taken apart, and the FFI supplies the representation together with construction and matching over it.

The first case of §33's sentence, "when its type is tagged" (L1472), does not exclude a type marked `extern`, and the
sentence then says the word "is the word of its constructor's tag slot (§35)" (L1476). §35 gives a tag slot only to a
type "not marked `extern` or `newtype`" (L1591-1592), and §42 says the FFI supplies an extern type's representation.
`coercible-tag` sides with §35 and §42: it is refused for an `extern` `Matchable` (§33 L1454-1457, quoted in B1.1).
Example in point: the prelude's `String` is described as an "extern enum of `SNil` and `SCons`" (§45 L2184-2185);
whether `SNil` is the word of `Nat` 0 is decided differently by the first quote and by the other two.

## D5. The size of a file's top level

> [QUOTE DESIGN.md:1161-1162 §27] **The top level.** A file's top level is an expression and so has size one.

> [QUOTE DESIGN.md:1163-1164 §27] A file that ends in a statement produces nothing.

> [QUOTE DESIGN.md:39-40 §1] A file is a sequence of statements, optionally followed by one expression (§27).

> [QUOTE DESIGN.md:1116 §27] A statement produces no values.

A file that ends in a statement has no final form, so by the second and fourth quotes it produces no value,
which is size zero and not the size one of the first quote. With several files (L1163) the text does not say
whether each file is its own expression or the unit is one.

## D6. "the one statement confined to run position"

> [QUOTE DESIGN.md:1219-1220 §28] This is the one statement confined to run position (§27).

> [QUOTE DESIGN.md:1120-1121 §27] All of them except `comptime-match`, `goal` and `qed` may appear at the top level or inside a body.

> [QUOTE DESIGN.md:3130 §71] `goal` and `qed` are each allowed only as a bare top-level form of a file, at most once per unit.

§27 lists `goal` and `qed` among the statements (L1120) and confines them more tightly than `comptime-match`.
So `comptime-match` is not the one confined statement. A small point; a spec's grammar of statements has to
pick one account.

## D7. When a run-position result becomes `Settled`

> [QUOTE DESIGN.md:229-232 §6] The binders of a statement in run position (§27) are `Settled` in the code after it, and so is the result of every form in run position, from the moment the form is elaborated (§29).

> [QUOTE DESIGN.md:758-760 §19] Inside a body those entries are `Hypothetical`; in run position they are `Settled` from the moment the form has run (§29).

> [QUOTE DESIGN.md:1239-1240 §29] **A form in run position** (§27, §20). Every entry it creates and leaves in scope is `Settled` once the form has run:

> [QUOTE DESIGN.md:1386-1388 §33] `d` is `Hypothetical` inside a body (§28) and `Settled` in run position, from the moment the `coerce` has run (§29).

The wordings "from the moment the form is elaborated" (L232) and "once the form has run" (L1240) coincide only if the run always
completes at once. They differ when the run crashes (C4): after elaboration and before a completed run there
is no value to store. The second wording is the one that stays true if a run can crash.

## D8. The representation is "a requirement on the implementation", and words are facts of the language

> [QUOTE DESIGN.md:1459-1460 §33] Coercion is free only if the representations coincide, so the following is a requirement on the implementation.

> [QUOTE DESIGN.md:1575-1576 §35] Its word is the word of `x`, and the result is at `x`, so a `let` of it is at the same slot as `x`.

> [QUOTE DESIGN.md:1802-1803 §38] At runtime, the value of a slot is a word, either a pointer or an immediate.

> [QUOTE DESIGN.md:3044 §67] `ESome` proves that `a` and `b` hold one word (§38).

§33 frames words and blocks as what an implementation must do for `coerce` to be free. §35 to §38 and §67
make words something a program holds (`(slot-of x)` at `many`), compares (`slot-eq`), and proves things about
(`Eq (Slot) a b`). The second use needs words in the language's meaning, not only in an implementation. This
is C1.

## D9. `Imm` for a `Nat`, and the models

> [QUOTE DESIGN.md:2061-2063 §44] `(Imm A v)` says that `v` is an immediate however it is built, and the `-imm` operations take it as evidence. `ImmNat` gives it for a `Nat` below `u62-modulus`,

> [QUOTE DESIGN.md:2236-2237 §45] **Left to the implementation.** How a `Nat`, `Char` or `String` is held at runtime,

> [QUOTE DESIGN.md:1477-1478 §33] With externs on, the extern `Nat`'s FFI must meet this for these numbers.

> [QUOTE DESIGN.md:1461-1462 §33] Values have a uniform representation: every value is one word, either an immediate or a pointer to a block, whatever its type.

> [QUOTE lib/prelude.sl:10-13] (def-adts $ (Nat : -> Type) enum extern (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))

> [QUOTE lib/prelude.sl:1448] (many ImmNat : (erased (Nat) n) (erased (Lt n u62-modulus) p) -> (Imm (Nat) n))

`ImmNat` is an ordinary constructor of the prelude, with no condition on externs (`[READ lib/prelude.sl:1444-1456]`,
the whole `Imm` declaration). When the models run (`--no-extern`), a `Nat` above zero is a `Succ` value with one
non-erased field, which the uniform representation makes a pointer to a block, if the model's constructors are
then the representation; DESIGN.md does not say what the representation of an extern type is in that mode. So
under the models `(Imm (Nat) 1)` can be built and, on that reading, is false. DESIGN.md gives an `imm` mark no
run-time effect (A3.3 item 6), so no wrong result follows from the text; a spec that models immediates has to
decide (C17). `[UNKNOWN]` I did not check what either implementation does with `imm` under `--no-extern`.

## D10. §15's placement against "runs as soon as it has been elaborated", in run position

> [QUOTE DESIGN.md:657-658 §15] That binding is a statement (§27) placed just before the statement or final form that contains the call,

> [QUOTE DESIGN.md:1179-1180 §27] Such a form runs as soon as it has been elaborated, before the code after it is checked:

> [QUOTE DESIGN.md:1185-1186 §27] This nests: the forms inside a form run before it does,

This tension is conditional. Under reading R1 of A2.3, the argument `(g a)` in a top-level
`(values (h b) (f (g a)))` is bound by a statement before the whole `values`, so before `(h b)`. Under §27 each
sub-form runs when the elaborator reaches it. If the elaborator takes the entries in written order, `(h b)`
runs first. The text fixes neither R1 nor the elaborator's order, so it does not contradict itself; a spec
that fixes both must make them agree.

## D11. "the only reference to its value": stated without condition, then with one

> [QUOTE DESIGN.md:14-16 §intro] a `unique` binder is the only reference to its value, so the value can be updated in place rather than copied (§13, §15)

> [QUOTE DESIGN.md:513-516 §13] Where nothing can mutate the value, the sole-reference property is neither promised nor needed, and a `unique` binder may alias a live `many` one (§34).

The introduction states sole reference of every `unique` binder. §13 promises it only "Where a value can be
mutated in place" (L510-511). A theorem that `unique` means sole reference has to be the conditional one. The
handoff records the owner asking about that property; it is the session's claim there, not an owner decision.

## D12. Separately built cells "are two blocks", and empty cells

> [QUOTE DESIGN.md:1696-1698 §36] Neither does canonical equality: two separately built cells with equal contents are `is`-equal and are two blocks.

> [QUOTE DESIGN.md:1736-1738 §37] When `C` has a tag slot, or the opened `Matchable` that lists `C` is that of a hollow type, the cell is instead at that tag slot, or at `vacant-slot` (§35, §36).

Two `cell-alloc`s of one fieldless constructor are both at its tag slot, so they are one word and no block. The
first sentence must then be about cells that have a non-erased field; it does not say so.

## D13. `native-compute` "means" a `values`, yet a crash is treated differently

> [QUOTE DESIGN.md:3149 §72] The form means `(values (f1) … (fn))`

> [QUOTE DESIGN.md:3155-3156 §72] a run that crashes is an error at its argument.

> [QUOTE DESIGN.md:1322-1323 §31] How a crash is reported is not specified; it need not be a runtime error.

A crash in the compiled run of `native-compute` is an error by §72. A crash of the evaluator running the
`values` that the form "means" (L3149) has no specified report by §31. So the two are the same in value and may differ
in whether the program is rejected (C4, C21).

## D14. "the same values" under the two extern modes, and acceptance that differs between them

> [QUOTE DESIGN.md:1953-1954 §42] running the models instead of the implementations must give a program the same values, though not the same cost,

> [QUOTE DESIGN.md:1596-1597 §35] With the prelude, `(slot-of 0)` is `vacant-slot`; with externs too, `(slot-of k)` is tag slot `k`.

The requirement compares two runs of "a program" (L1953-1954). By the second quote, and by `coercible-tag` being refused
"under `--no-extern`" (§33 L1456-1457), some programs are accepted in one mode and not the other. The
requirement can then apply only to programs accepted in both, which the text does not say. `[RAN]` Appendix R,
run R2, shows one program that the reference accepts with externs and rejects under `--no-extern`. A compiler
theorem has to name the mode it is about (C6).

# Appendix S. The searches behind every claim of silence

`search.py FILE PATTERN...` (in `proto/A5/`) is a case-insensitive regex search that treats a line break as a
space, so a phrase split over two lines is found; a space in a pattern matches any run of whitespace. It
prints the line on which each match starts. `grep` lines are ordinary line-based greps. Everything below is
`[RAN]`; the working directory is `/home/user/sleight` for `grep` and `proto/A5` for `search.py`. Context is cut at 118 columns.

### S1. Evaluation order (A2.2)

```text
$ search.py DESIGN.md 'left to right' 'right to left' 'evaluation order' 'order (written|of evaluation|in which)' 'evaluated (first|before|after|last)' '(first|before|after) evaluat' 'in (that|the same|this|source|written|textual|declaration|declared) order' 'sequential' 'eager' '\bone after'
=== /left to right/ : 1 match(es)
  L699: ..., followed by the `subterm`-marked arguments from left to right. An ADT may have no constructors at all (`F
=== /right to left/ : 0 match(es)
=== /evaluation order/ : 0 match(es)
=== /order (written|of evaluation|in which)/ : 0 match(es)
=== /evaluated (first|before|after|last)/ : 0 match(es)
=== /(first|before|after) evaluat/ : 0 match(es)
=== /in (that|the same|this|source|written|textual|declaration|declared) order/ : 3 match(es)
  L221: ...enclosing function's `subterm`-marked parameters, in declaration order (§19). ## 6. Head dispatch Macros a
  L1032: ... constructor. The `Ci` are its value constructors in declared order, each with its multiplicity `ei`, whic
  L1507: ...are bound by a `let` and repackaged in a `values` in the same order, with or without coercions and placing
=== /sequential/ : 2 match(es)
  L1356: ...the same rules, since run-position statements are sequential. When the elaborator must read a `Settled` as
  L2884: ...m counter and the expansion count. It is threaded sequentially through all of elaboration, carried out of 
=== /eager/ : 1 match(es)
  L1319: ...(§14). ## 31. Evaluation strategy Evaluation is eager. The semantics is that of a machine with unlimited 
=== /\bone after/ : 0 match(es)
```

### S2. Every line with 'order' (A2.2)

```text
$ grep -n -i 'order' DESIGN.md | cut -c1-110
198:- an **introduction order**, which orders `Predates` (§18) and decides
221:function's `subterm`-marked parameters, in declaration order (§19).
370:be unified become one. The entry kept is, in order of preference, a
621:code. The order of the uses does not matter. On one path a `unique`
631:branch, in the order unused, then used at many, then used at unique.
698:lexicographic order whose first component is the level, followed by
735:from one (§19). `x` must have an introduction order (§5) earlier than
737:forwarding from a literal has an order of its own.
749:introduction order (§5), except that a binder forwarding from a
750:literal's entry (§45), which has none, keeps an introduction order of
767:introduction order.
826:returned in order by a final `values`, with or without coercions and
837:order. The function names its callee on its header line, as in
985:one slot per field whose label is non-erased, in order, `gi` being that
1031:either order, or neither. `T` is the type constructor. The `Ci` are its
1032:value constructors in declared order, each with its multiplicity `ei`,
1163:proved` turn off the driver described here. Several files on one command line share one scope, in order. 
1420:   are the telescope of `C`, in order, so exactly one of them, `f`, is
1507:`let` and repackaged in a `values` in the same order, with or without
1833:marks `absurd`, `extern` and `at` come before the name, in any order.
2185:and `SCons` over `Char`: its characters consed up, in order.
2193:and have no introduction order (§18). They refer to the prelude's
2485:- `subterm` marks a parameter as part of the lexicographic order (§17,
2951:literal's entry, it is outside every scope and has no introduction order
```

### S3. Every line with 'evaluat' (A2)

```text
$ grep -n -i 'evaluat' DESIGN.md | cut -c1-110
1181:elaborated, its erased positions are stripped, the evaluator runs the
1245:   erased positions, and run by the evaluator; its binders take the
1247:   `def-adts` involves no evaluation: a function's value is its
1280:positions are stripped before the evaluator runs. An erased `Settled` may
1284:**The checker never evaluates.** The checker computes only what the
1288:value would be evaluation, so inside a body the results of a match
1291:the evaluator. The inspection sites are checks, not forwarding: by the
1295:evaluation boundary: no erasure demand and no branch-hypothetical
1300:positions removed. The evaluator runs that code. The resulting values
1307:relies on the evaluator having evaluated correctly. A stored value
1317:## 31. Evaluation strategy
1319:Evaluation is eager. The semantics is that of a machine with unlimited
1844:arguments are still evaluated, as §15 binds them. A
1878:arguments are still evaluated, as for any skipped call. A skipped call
1895:(§39). The match skips its runtime: its scrutinee is evaluated as for
2212:it relies on the evaluator (§29). A character literal is
3151:calls to be run by compiled code rather than by the evaluator, as a final
3153:erased fields take the tokens of §5. It may crash where the evaluator
```

### S4. Addresses, sharing, reuse, function words (A3.3)

```text
$ search.py DESIGN.md 'hash-?cons' '\bshar(e|ed|ing) (a|one|the same) (block|address|word)' 'garbage' 'reclaim' 'dealloc' '\bfreed?\b' 'reus' 'closure'
=== /hash-?cons/ : 0 match(es)
=== /\bshar(e|ed|ing) (a|one|the same) (block|address|word)/ : 0 match(es)
=== /garbage/ : 0 match(es)
=== /reclaim/ : 0 match(es)
=== /dealloc/ : 0 match(es)
=== /\bfreed?\b/ : 2 match(es)
  L433: ...26, §3). Bound occurrences are de Bruijn indices; free references are entries of §5. Pattern matching ass
  L1459: ...out the prelude. **Representation.** Coercion is free only if the representations coincide, so the followi
=== /reus/ : 5 match(es)
  L1098: ... of the branches mention branch-forced facts. `_` reuses the telescope the position expects (§47). `(at (
  L2251: ...ay be written in place of the annotation (§26) to reuse it. Those positions are: the final expression of 
  L2258: ...`, `notail`, `delegate` and the `at` wrapper. The reused telescope may not contain a `_` that is still to 
  L2259: ...s still to be inferred (§50). `(open-absurd e _)` reuses the telescope in the same way (§8). ## 48. `_` 
  L2677: ...t, and it erases to nothing. A `delegate` proof, reusing `inc` from §57 at level `I`: ```scheme (let ((er
=== /closure/ : 2 match(es)
  L1325: ...pecified; it need not be a runtime error. ## 32. Closures, `def-unique`, and the top level A function defi
  L1327: ...e top level A function defined by `def-fns` is a closure over its scope. It may mention a `unique` binder 
$ grep -n -i 'address' DESIGN.md | cut -c1-110
1701:may belong to consumed entries; address equality does not change when
$ grep -n -i 'pointer' DESIGN.md | cut -c1-110
1462:an immediate or a pointer to a block, whatever its type. So a `Cons`
1488:constructor. Erased fields occupy no space. The pointer of a
1489:`delegate`-bodied function is its callee's pointer (§19). An extern
1803:slot is a word, either a pointer or an immediate. A slot is inert: it
2632:at `many` is fine: the pointer is never followed. `tests/absurd.sl` is
2689:`(coerce inc-noted ig)` is then the pointer of `inc` itself.
$ grep -n -i 'fresh' DESIGN.md | cut -c1-110
294:constructor applied to its fresh fields, and equates the scrutinee's
297:through matching non-atom arguments. A fresh atom, or an atom with no
728:`(def-lvl L)` creates a fresh, erased `Level` with the level-mint
764:run position it is minted afresh, with its own type as its minted
991:`(else x2 body)`. Then `x2` is a fresh binder at the scrutinee's
1142:fresh fields and without the facts learned while checking any other
1587:its own slot. That makes a cell type that names it the type of a fresh
1735:fresh cell at unique, at no slot, with every slot `vacant-slot` (§35).
1756:`many` the form uses `u` at many and copies: the result is a fresh
1773:otherwise as a fresh copy at nothing. In an erased position nothing is used
1818:modes the `si` are fresh `many` binders of type `(Slot)`, one per
1822:`u2` is optional. It is the cell given back, a fresh `unique` binder
2313:binder type or annotation entry. Each such `_` is a fresh unification
2396:fresh proof at each use, and it may not appear in a type.
2407:- `def-lvl`: creates a fresh `Level` (§18).
2944:`mint-settled` and `mint-settled-erased` mint a fresh anonymous `Settled`
2983:Otherwise it answers `Some` with a handle to a fresh anonymous `Settled`
```

### S5. Impossible paths (A5.2)

```text
$ search.py DESIGN.md 'undefined' 'stuck' 'cannot (run|be reached|happen)' 'unreachable' 'never (run|runs|ran|followed|read|reached)' 'no code'
=== /undefined/ : 0 match(es)
=== /stuck/ : 0 match(es)
=== /cannot (run|be reached|happen)/ : 0 match(es)
=== /unreachable/ : 1 match(es)
  L283: ...able is therefore enough. Compile-time effects in unreachable code still happen. A fact verified by a `comp
=== /never (run|runs|ran|followed|read|reached)/ : 7 match(es)
  L289: ...n, both sides are canonicalized. Canonicalization never reads a `Settled` entry's stored value. It is drive
  L894: ...structor under a `many` or `unique` scrutinee can never run, because no non-erased value is headed by a pha
  L1189: ...ting code under a function body or a match branch never runs it; such code runs at compile time only when 
  L1483: ...type of newtype shape is a block (§37). A word is never read as the field of a constructor that did not b
  L1502: ... checked for termination like any other (§17) and never runs. **Tail and delegate.** A `coerce` erases to
  L2632: ... and holding it at `many` is fine: the pointer is never followed. `tests/absurd.sl` is this program. ## 60
  L2674: ...unwrap-all` the call is in an erased position and never runs; `(coerce ms p)` is the only runtime content,
=== /no code/ : 3 match(es)
  L1064: ...y is an erased position (§14), and it compiles to no code. A contradiction that lives in the fact table r
  L1897: ...tself, its dispatch and its branches, compiles to no code, and the consumer reads its `at` entries back fr
  L2631: ...; `absurd` accepts that. The function compiles to no code, and holding it at `many` is fine: the pointer i
```

### S6. Words for erased code (A6.6)

```text
$ search.py DESIGN.md 'post-erasure' 'stripp?(ed|ing)' 'extracts? to|extracted' 'emitted'
=== /post-erasure/ : 4 match(es)
  L822: ...onour is an error. Tail position is judged on the post-erasure code, where erased positions, types, coercio
  L834: ...pass-through requirement on the arguments: in the post-erasure code the marked function's body is nothing b
  L1705: ...* The `tail` and `delegate` checks (§19) read the post-erasure code with `at` entries omitted, just as th
  L1836: ...**: after erasure, with `at` entries omitted, the post-erasure code holds no call that is not skipped, no 
=== /stripp?(ed|ing)/ : 7 match(es)
  L1181: ...ecked: it is elaborated, its erased positions are stripped, the evaluator runs the code, and its results b
  L1194: ...s (§19), which is what allows the statement to be stripped and run before the code after it is elaborated
  L1244: ...where the entry is erased. A `let` is elaborated, stripped of its erased positions, and run by the evaluat
  L1280: ... never computed, because the erased positions are stripped before the evaluator runs. An erased `Settled` 
  L1282: ...tions of a statement, because those positions are stripped, not read. **The checker never evaluates.** The
  L1294: ...ackwards into code that has already been checked, stripped and run. Nothing crosses an evaluation boundary
  L2239: ... the same effect. The requirement of §42 applies: stripping the extern implementations must leave every l
=== /extracts? to|extracted/ : 3 match(es)
  L2156: ...ritten where it is used: a wrapper function would extract to a call, while the inline `coerce` extracts to
  L2156: ...ould extract to a call, while the inline `coerce` extracts to nothing. ## 45. Literals Numerals, character
  L2851: ..., and an `MMany` handle carries its value into an extracted program. Only built-in forms create handles, s
=== /emitted/ : 1 match(es)
  L1130: ...ared with. Those statements run, or their code is emitted, whether or not the `let`'s own binders are eras
```

### S7. The machine (A1.7 item 1)

```text
$ search.py DESIGN.md 'small-step|big-step|operational|denotation' 'observ' 'machine'
=== /small-step|big-step|operational|denotation/ : 0 match(es)
=== /observ/ : 0 match(es)
=== /machine/ : 3 match(es)
  L17: ...untime part from being shaped to compile to tight machine code. This is an aim for the language, not for the
  L1319: ... Evaluation is eager. The semantics is that of a machine with unlimited stack and heap. A real run may cra
  L1970: ...elow `u62-modulus`, so the FFI runs each as one machine operation. This relies on the host having native i
```

### S8. Executors, the driver, and what follows an error (A1.7 items 2 to 5)

```text
$ grep -n -i 'compiled' DESIGN.md | cut -c1-110
603:before that unit is compiled or run.
1174:for its final value to be computed by compiled code. A final value of
1248:   compiled code, a `Level` is an erased token, and a `Matchable` is
1308:that `native-compute` produced relies on its compiled run in the same
3151:calls to be run by compiled code rather than by the evaluator, as a final
3152:`Fn` is (§27). The compiled run hands back only the constructor, so its
3155:compiled is an error at the form, and a run that crashes is an error at
$ search.py DESIGN.md 'last file' 'final value' 'exit (code|status)' 'first error' 'abort'
=== /last file/ : 0 match(es)
=== /final value/ : 5 match(es)
  L1165: ...ement produces nothing. Otherwise the type of the final value decides what the driver does with it. A `Pro
  L1167: ... applies each step's continuation once. Any other final value is used at `many`, so a `unique` one is writ
  L1168: ...so a `unique` one is written `(share x)` (§16). A final value of `Fn` type must have one of two forms, at
  L1174: ...printed (§45); this is how a program asks for its final value to be computed by compiled code. A final va
  L1174: ...ts final value to be computed by compiled code. A final value of `Fn` type in neither form, or of `UniqueF
=== /exit (code|status)/ : 1 match(es)
  L1973: ..., read by the driver (§27). `Exit` carries a `U8` exit code. `Continue` carries a continuation `(unique (
=== /first error/ : 0 match(es)
=== /abort/ : 0 match(es)
$ grep -n -i '\bstops\?\b' DESIGN.md | cut -c1-110
16:rather than copied (§13, §15), and nothing in the language stops a
161:Warnings go to standard error and do not stop elaboration.
1627:telescope does not stop the search outward. A constructor's telescope
2427:- `dump-context`: stops elaboration with a report of the context
```

### S9. Nondeterminism and the world (A4.2)

```text
$ search.py DESIGN.md 'nondetermin' 'non-determin' 'between runs' 'may always' 'the same values?'
=== /nondetermin/ : 0 match(es)
=== /non-determin/ : 0 match(es)
=== /between runs/ : 1 match(es)
  L3046: ...nswer it, and which one a call answers may differ between runs. `slot-eq` requires the prelude. ## 68. `ce
=== /may always/ : 1 match(es)
  L3045: ...38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may d
=== /the same values?/ : 3 match(es)
  L1954: ...nstead of the implementations must give a program the same values, though not the same cost, and either ma
  L2234: ...printed literal back gives a literal that denotes the same value. **Left to the implementation.** How a `N
  L2240: ... implementations must leave every literal meaning the same value. ## 46. `_` as a `def-fns` level `_` writ
$ grep -n 'Request' DESIGN.md | cut -c1-110
1972:- **`Program` and `Request`.** `(Program L)` is an enum indexed by a
1980:  applied once. `(Request A)` is an enum indexed by the type of its
1984:  (world-do A w req) : (erased Type A) (unique (World) w at vacant-slot) (unique (Request A) req) ->
1989:  (§50). It names the prelude's `Request`, so, like literals, it is
```

### S10. Acceptance, flags, fuel (B0, B1)

```text
$ search.py DESIGN.md 'reject' 'fuel' 'time ?out'
=== /reject/ : 0 match(es)
=== /fuel/ : 0 match(es)
=== /time ?out/ : 0 match(es)
$ grep -n -i 'accept' DESIGN.md | cut -c1-110
776:unique value (§16), and an `erased` binder accepts anything. If a type
802:  itself, which `predates-subterm` can produce, is not accepted here.
2332:solve. So `(f _ (Nil _) xs)` is accepted, while `(len _ (Nil _))` is
2333:refused at the `)` of the call. A `_` in a signature is accepted when
2345:not accepted as an entry of a `values` or as the scrutinee of a
2363:  accepted when `(match erased e _)` with no branches would refute. So
2631:`absurd` accepts that. The function compiles to no code, and holding it
$ search.py DESIGN.md 'is an error' 'is refused|are refused|refuses|refused' | grep '^==='
=== /is an error/ : 43 match(es)
=== /is refused|are refused|refuses|refused/ : 17 match(es)
$ grep -o -n -- '--[a-z][a-z-]*' DESIGN.md | awk -F: '{print $2}' | sort | uniq -c
      1 --comptime-unconfine
      1 --fn-same
      5 --goal
      2 --no-extern
      5 --no-prelude
      1 --warnings-as-errors
$ grep -c 'def-prim' lib/prelude.sl; grep -c 'def-prim' DESIGN.md
21
0
$ grep -n -i 'primitive' DESIGN.md | cut -c1-110
2022:in the manner of Rust's `MaybeUninit`. There is one extern primitive
2827:is. The other forms on handles are primitives:
2890:and returns it `at` its parameter. The forms below are primitives, apart from the two
```

### S11. Provisional, unspecified, and delegated parts (B2, B5)

```text
$ search.py DESIGN.md 'provisional' 'for now' 'relaxed' 'prototype' 'in flux' 'tentative' 'today' 'currently' 'not yet' 'at present' 'unspecified|not specified' 'left to'
=== /provisional/ : 1 match(es)
  L31: ...elude, the FFI and literals: §42 to §45. - Sugar, provisional: §46 to §53. - The special-form registry: 
=== /for now/ : 1 match(es)
  L779: ...mismatch is an error. This is deliberately strict for now. A `let` binder may not be written `at` (§36). *
=== /relaxed/ : 1 match(es)
  L1206: ...en in run position (see `xs` in §57). This may be relaxed if it proves heavy. `(comptime-match m x (C f1 
=== /prototype/ : 1 match(es)
  L1956: ...her may crash where the other does not (§31). The prototype's FFI is a fixed table keyed by the declared 
=== /in flux/ : 1 match(es)
  L507: ..., which cuts down on mistakes while the design is in flux. `unique` may be declared on function parameters 
=== /tentative/ : 0 match(es)
=== /today/ : 0 match(es)
=== /currently/ : 0 match(es)
=== /not yet/ : 0 match(es)
=== /at present/ : 0 match(es)
=== /unspecified|not specified/ : 2 match(es)
  L1322: ...never a different one. How a crash is reported is not specified; it need not be a runtime error. ## 32. Cl
  L1475: ...ked `extern`, however the value was built, and an unspecified word otherwise. In the first two cases this 
=== /left to/ : 4 match(es)
  L699: ..., followed by the `subterm`-marked arguments from left to right. An ADT may have no constructors at all (`F
  L2236: ...k gives a literal that denotes the same value. **Left to the implementation.** How a `Nat`, `Char` or `Str
  L2717: ...l ys)) ``` The write stores `h` before the call: left to the invocation, that store would follow the call 
  L3113: ...ons answer. How an implementation finds a slot is left to it. Taking a `Slots` apart through `MkSlots`, or
$ grep -n 'MANUAL' DESIGN.md | cut -c1-60
4:questions. MANUAL.md describes the implementations and the
163:does not count (MANUAL.md).
1120:(MANUAL.md), `compile-error` and `compile-warn` (§4), 
1995:  MANUAL.md describes `ConfinePaths`, `ConfineOutputByt
2428:  (MANUAL.md). Also usable as an expression and as a ty
2966:answers `Fail`. The fence (MANUAL.md) does not apply to
3125:It is available only under `--fn-same` (MANUAL.md); wit
3132:`--goal` (MANUAL.md) is `none`, `open` or `proved`. Und
$ grep -n 'lib/prelude.sl' DESIGN.md | cut -c1-60
1963:**The source prelude** `lib/prelude.sl` is elaborated b
1966:`lib/prelude.sl` is the reference for what it defines.
1990:  unavailable under `--no-prelude`. `lib/prelude.sl` is
2089:`lib/prelude.sl`; the FFI's implementation drops the ar
$ grep -n 'tests/' DESIGN.md | cut -c1-60
1227:`tests/u8.sl` does for the bound of a `U8`.
2512:The prelude declares `List` exactly like this (§42). `
2632:at `many` is fine: the pointer is never followed. `test
2690:`tests/coerce.sl` is this program.
2721:`tests/cell_append.sl` is this program.
3034:the result is at `a` (`tests/placed_thread.sl`). A cons
```

### S12. Reading (B4.2)

```text
$ search.py DESIGN.md 'whitespace' 'leading zero' 'ascii|utf|unicode'
=== /whitespace/ : 1 match(es)
  L42: ...(§4). An atom is any run of characters other than whitespace, parentheses and `;`. A token that begins with
=== /leading zero/ : 1 match(es)
  L2165: ...A numeral is an atom made only of digits, with no leading zero: `0` or `42`. A numeral written plain is ne
=== /ascii|utf|unicode/ : 1 match(es)
  L60: ...name. Every built-in name and built-in syntax is ASCII. The multiplicities are written as the words `erased`
```

### S13. slot-eq (B3)

```text
$ search.py DESIGN.md 'slot-eq' 'ErasedMaybe'
=== /slot-eq/ : 8 match(es)
  L1952: ...tation must agree with its model: except through `slot-eq` (§67), running the models instead of the imple
  L2453: ...ny`, `unplace-at` and `unplace-at-many` (§66), `slot-eq` (§67), `cell-same` (§68), `fn-same` (§70) and
  L3037: ...t a slot is declared the same way (§36). ## 67. `slot-eq` ```scheme slot-eq : (many (Slot) a) (many (Slot
  L3040: ... the same way (§36). ## 67. `slot-eq` ```scheme slot-eq : (many (Slot) a) (many (Slot) b) -> (many (Erase
  L3046: ...hich one a call answers may differ between runs. `slot-eq` requires the prelude. ## 68. `cell-same` ```sch
  L3068: ...gets finding a slot in O(1), where a search with `slot-eq` (§67) is O(n). ```scheme (def-adts $ (NthLast 
  L3111: ...unique l is l2 at l) ``` The models search with `slot-eq`, so §42's exception for `slot-eq` covers what t
  L3111: ...ls search with `slot-eq`, so §42's exception for `slot-eq` covers what the implementations answer. How an
=== /ErasedMaybe/ : 3 match(es)
  L2793: ...q : (many (Symbol) x) (many (Symbol) y) -> (many (ErasedMaybe (Eq (Symbol) x y)) r) ``` `symbol-eq` is ord
  L2904: ...mb B b) q) -> (unique mw is mw2 at mw) (many (ErasedMaybe (JMEq A a B b)) r) intern-nat : (unique (MacroWo
  L3041: ...q : (many (Slot) a) (many (Slot) b) -> (many (ErasedMaybe (Eq (Slot) a b)) r) ``` `ESome` proves that `a` 
```

### S14. OPEN.md and DECISIONS.md (A2.5, Part C)

```text
$ grep -n -i 'order\|evaluat' OPEN.md | cut -c1-100
11:   and subterm order (§17), and types never compute (§9). The owner
38:4. Facts from stored values. A `comptime-match` trusts the evaluator
39:   (§29). Should a reference evaluator inside the checker arbitrate
40:   runs that produce facts, so that a wrong evaluation cannot produce a
46:   represents the whole order of §17 as a nested disjunction, so that a
53:9. Compile-time evaluation inside a body: a `comptime` form, and a
134:    idea is an order relation on `Bin` and a lemma, appended to the end
189:    (§65) have an introduction order (§5, §18), as the
$ grep -n -i 'machine\|heap' OPEN.md | cut -c1-100
$ grep -n -i 'deterministic\|determin\|between runs' OPEN.md | cut -c1-100
$ grep -n -i 'crash' OPEN.md | cut -c1-100
$ grep -n -i 'accept\|reject' OPEN.md | cut -c1-100
65:13. Should `_` be accepted as an entry of a `values`, or as the
77:    combination: an unmarked `(Matchable enum T ...)` does not accept an
112:36A. Should `_` be accepted as an at-match's annotation (§40, §47)?
143:    `pow2-fn`) and the checker accepted it; that proof's unfolding
$ grep -n -i 'prelude' OPEN.md | cut -c1-100
96:    them in stages, deleting them if that works out, with the prelude
135:    of `lib/prelude.sl`, from that relation and the two literals'
141:    prelude? A session sketched that `Eq` from `u8-modulus-pow2` and
145:    opaque, and it is not known whether the prelude can hold a literal.
$ grep -n -i 'reader\|lexical\|whitespace\|\bbyte' OPEN.md | cut -c1-100
$ grep -n -i 'fresh\|address\|reuse\|garbage' OPEN.md | cut -c1-100
89:    given back as a fresh binder `is` and `at` it, so that neither is
119:    Two forms have been considered. One is `(at _)`, which would reuse
122:    when the telescope it reuses is that of an at-match's branch or
125:    and whether it stops where a fresh telescope is supplied, as at an
$ grep -n -i 'elaborat' OPEN.md | cut -c1-100
$ grep -n -i 'terminat\|halt\|fuel' OPEN.md | cut -c1-100
10:   positivity restriction (§10)? Termination is carried by the level
49:8. Macros. Open: macro termination beyond a global expansion limit,
$ grep -n -i 'driver\|Program\|exit' OPEN.md | cut -c1-100
17:2. Erasure conservativity. Take any program that compiles and collapse
33:   and `open-absurd` of the original program survives.
161:    program. A use as the head of a form does count. slc reads
180:    recommendation, if followed, changes the program: writing `_` makes
$ grep -n -i '\bimm\b\|immediate' OPEN.md | cut -c1-100
$ grep -n -i 'represent\|\bword' OPEN.md | cut -c1-100
26:   representation, and replace each `coerce` by the value its proof
46:   represents the whole order of §17 as a nested disjunction, so that a
75:    (§24)? The marks are written words, so a `Matchable` parameter fixes
203:    two closures at one word can differ in what they capture or pass
$ grep -n -i 'top level\|run position' OPEN.md | cut -c1-100
$ grep -n -i 'provisional\|sugar' OPEN.md | cut -c1-100
102:23. Should a shadowing sugar replace rebinding under the same name,
$ grep -n -i 'native-compute' OPEN.md | cut -c1-100
$ grep -n -i 'order\|evaluat' DECISIONS.md
(no output)
$ git log --oneline -S'Argument temporaries' -- OPEN.md
a24c23e slc: find a self-slotted constant's word through the canonical slot
$ git show a24c23e:OPEN.md | grep -n -A2 'Argument temporaries'
139:## Argument temporaries
140-
141-## Literal proofs
```

# Appendix R. Two experiments on the implementations

These runs show what the two implementations do. They are not statements about the language. Binaries:
`main.exe` is `/home/user/sleight/_build/default/bin/main.exe` (the OCaml reference); `slc` is
`/home/user/sleight/_build/release/slc`. The programs are in `proto/A5/`. Everything in this appendix is `[RAN]`.

### R1. A `slot-eq` answer reaches acceptance (used in B3, C3)

```text
$ cat sloteq_some.sl
(let ((many x)) (Cons (Nat) 1 $ Nil (Nat)))
(let ((many r)) (slot-eq (slot-of x) (slot-of x)))
(comptime-match many r (ESome a e))
7
$ cat sloteq_none.sl
(let ((many x)) (Cons (Nat) 1 $ Nil (Nat)))
(let ((many r)) (slot-eq (slot-of x) (slot-of x)))
(comptime-match many r (ENone a))
7
$ main.exe sloteq_some.sl
7
(exit 0)
$ main.exe --no-extern sloteq_some.sl
7
(exit 0)
$ slc --interpret sloteq_some.sl
7
(exit 0)
$ main.exe sloteq_none.sl
sloteq_none.sl:3:1: error: `comptime-match`: expected `ENone`, got `(ESome _ _)`
(exit 1)
$ main.exe --no-extern sloteq_none.sl
sloteq_none.sl:3:1: error: `comptime-match`: expected `ENone`, got `(ESome _ _)`
(exit 1)
$ slc --interpret sloteq_none.sl
sloteq_none.sl:3:1: error: `comptime-match`: expected `ENone`, got `(ESome _ _)`
(exit 1)
```

Reading, `[INFERENCE]`: both implementations answer `ESome` for `(slot-eq (slot-of x) (slot-of x))` at compile
time and let `comptime-match` assert it. §67 permits an implementation to answer `ENone` instead; such an
implementation would accept `sloteq_none.sl` and reject `sloteq_some.sl`.

### R2. The position of a `Special` constructor reaches acceptance (used in A3.3 item 10, B1.6, D14)

```text
$ cat special_slot0.sl
(let ((many x)) let)
(slot-tag x)
(let ((erased (Eq (Slot) (slot-of x) (slot-of 0)) e)) (Refl (Slot) (slot-of x)))
1
$ cat special_slot_match.sl
(let ((many x)) match)
(slot-tag x)
(let ((erased (Eq (Slot) (slot-of x) (slot-of 0)) e)) (Refl (Slot) (slot-of x)))
1
$ main.exe special_slot0.sl
1
(exit 0)
$ slc --interpret special_slot0.sl
1
(exit 0)
$ main.exe special_slot_match.sl
special_slot_match.sl:3:7: error: type mismatch: expected `(Eq (Slot) (slot-of x) vacant-slot)`, got `(Eq (Slot) (slot-of x) (slot-of x))`
(exit 1)
$ slc --interpret special_slot_match.sl
special_slot_match.sl:3:1: error: type mismatch: expected `(Eq (Slot) (slot-of x) vacant-slot)`, got `(Eq (Slot) (slot-of x) (slot-of x))`
(exit 1)
$ cat special_slot_match26.sl
(let ((many x)) match)
(slot-tag x)
(let ((erased (Eq (Slot) (slot-of x) (slot-of 26)) e)) (Refl (Slot) (slot-of x)))
1
$ main.exe special_slot_match26.sl
1
(exit 0)
$ main.exe --no-extern special_slot_match26.sl
special_slot_match26.sl:3:7: error: type mismatch: expected `(Eq (Slot) (slot-of x) (slot-of 26))`, got `(Eq (Slot) (slot-of x) (slot-of x))`
(exit 1)
$ slc --interpret special_slot_match26.sl
1
(exit 0)
```

A loop over `k` from 0 to 130 with the reference, replacing `match` by another special form and `26` by `k` in
`special_slot_match26.sl`, found the first accepted `k` for four forms:

```text
match: accepted at k=26
def-lvl: accepted at k=1
values: accepted at k=32
def-fns: accepted at k=2
```

Reading, `[INFERENCE]`: in both implementations a `Special` value is a position word (`let` at 0, `match` at 26),
and a program's acceptance can depend on that position. DESIGN.md gives `Special`'s constructors no order
(B1.6 item 1). The positions are not the listing order of §54 either: counting the names of §54 in the order
listed (L2405-2441: sixteen statements, six type formers, then `match` and `values`), `match` would be at 22 and
`values` at 23, and the reference has them at 26 and 32. The third run of `special_slot_match26.sl` also shows acceptance changing with `--no-extern`, as
§35 L1596-1597 says it should ("with externs too, `(slot-of k)` is tag slot `k`").

Not tried, `[UNKNOWN]`: the same loop under `slc`; any experiment on evaluation order; any experiment on `imm`
under `--no-extern`.

# Verification of this report

Everything in this section is `[RAN]`, from the directory `proto/A5/` of the scratchpad, on the assembled report.

```text
$ python3 verify_quotes.py ../../reports/A5-design-audit.md | tail -1
checked 425 quotes, 0 problems
$ python3 verify_inline.py ../../reports/A5-design-audit.md | tail -1
checked 260 inline phrases, 0 problems
$ python3 verify_inline.py ../../reports/A5-design-audit.md | grep -c 'no ref'
12
$ python3 verify_inline.py ../../reports/A5-design-audit.md | grep -c 'note: only in'
18
```

- `verify_quotes.py` checks every quotation line: the text occurs in the cited file; it starts on the first
  cited line and ends on the last; and, for DESIGN.md, the section tag is the section that holds those lines.
  Before use I gave it seven test lines, six of them wrong in one way each (wrong word, start line one early,
  end line one late, wrong section, missing section, three dots in place of the source's ellipsis character);
  it rejected exactly those six.
- `verify_inline.py` checks every phrase between double quotes in prose and tables, outside code fences and
  quotation lines: the phrase occurs verbatim in DESIGN.md, OPEN.md, DECISIONS.md, MANUAL.md, CLAUDE.md,
  `lib/prelude.sl`, the handoff, or the brief; and, when it occurs in DESIGN.md and its paragraph carries line
  references, one of them overlaps an occurrence. Its remaining notes are of two kinds, listed in the output
  above by count: phrases in headings, which carry no line reference there and are followed by their quotation
  lines; and phrases that occur only in the handoff or OPEN.md, which is where I quote them from.
- Not checked by machine: a line reference that stands without quoted words; the sentences I wrote about what
  a search's matches are; and the reasoning tagged `[INFERENCE]`.

# Things I am least sure of

1. **Completeness of the collections in Part A.** `[INFERENCE]` I read all 3156 lines once, in order, and then collected
   by section and by search. Sentences that constrain the run only indirectly may be missing from Part A, in
   particular among the array signatures of §44, the primitives of §64 and §65, and the worked examples.

2. **The two readings of §15 (A2.3).** `[INFERENCE]` R1 and R2 are my constructions from an ambiguous phrase.
   There may be a third reading, and the owner may intend something the text does not say. The same holds for
   my choice of the innermost one where a `let` and its right-hand side's final form both contain the call.

3. **That sibling order is observable only through crashes, `slot-eq`, the `tail` check, and the compile-time
   counters (end of A2.5).** `[INFERENCE]` I did not prove it, and I ran no experiment on evaluation order.

4. **D3, D4, and D9 as tensions.** `[INFERENCE]` Each rests on reading a sentence literally. "a single field is
   stored bare" (L1465) may have an intended meaning that removes D3. "when its type is tagged" (L1472) may be meant to exclude
   extern types, which would remove D4. D9 assumes that under `--no-extern` an extern type's values are
   represented by the model's constructors, which DESIGN.md does not say; I did not test `imm` under `--no-extern`.

5. **A1.3's inference of one heap across run-position forms.** `[INFERENCE]` It combines three sentences; no
   sentence states it. Run R1 is consistent with it for the implementations.

6. **Interning order (B1.5 item 3).** `[UNKNOWN]` I could not determine whether it can change accept or reject.

7. **The order of `Special`'s constructors as a gap (B1.6, R2).** `[INFERENCE]` It rests on my not finding an order
   in §42 or §54. The reference's positions (`let` 0, `def-lvl` 1, `def-fns` 2, `match` 26, `values` 32) do not
   follow §54's listing order past the first three, by my count of §54's names (Appendix R, run R2); I counted
   by hand and tried only five forms.

8. **Line references that stand without a quoted phrase.** The quotation lines and the phrases in double quotes
   were checked by machine. A bare reference such as `(§42 L1933-1935)` with no quoted words beside it was
   checked by hand only.

9. **What the other documents say.** I did not open ASSUMPTIONS.md, SOUNDNESS.md, the Lean model, `mini/`, or
   either implementation's source, by design. Some of the gaps in Part C may be answered there by a session's
   choice; such an answer would not be the owner's (CLAUDE.md rule 14).

10. **History.** `[RAN]` I looked at git history for one thing only, the empty OPEN.md heading "Argument
    temporaries". Whether a question on evaluation order or on argument temporaries was ever listed and removed
    before this history's first commit, I do not know.

11. **Part C's order.** The ranking by how much each answer would shape the formalization is my judgment.
