# A8. The ASSUMPTIONS.md backlog: what a formal specification would be forced to settle

Agent A8. This is an inventory, not a design exercise. Nothing inside `/home/user/sleight` was created, changed, or deleted.

**State read.** Branch `claude/sleight-formalization-compiler-8m362f`. HEAD was `269833c` when I began and `6f15f88` when I finished; the commit between them is titled `proposals/formalization: order and gap probes, and four more reports`. [RAN] `git diff --stat 269833c 6f15f88 -- ASSUMPTIONS.md DESIGN.md OPEN.md BUGS.md SPEC-REVIEW.md lib/prelude.sl CLAUDE.md WARNINGS.md` printed nothing, and `git status --short` for the same files printed nothing, so the text I read is the committed text at both commits. [RAN] `wc -l ASSUMPTIONS.md DESIGN.md` gave `2310 ASSUMPTIONS.md` and `3156 DESIGN.md`.

**How to read the tags.**

- `[QUOTE file:lines]` is followed by text copied from those lines, between “ and ”. Wrapped source lines are joined with single spaces and nothing else is altered. A script checked every quote in this report against the cited lines (section 6).
- Every class, area, label, and question in sections 1 and 2 is `[INFERENCE]`: my judgement from reading the item at the lines the row cites, `[READ ASSUMPTIONS.md:lines]`. The judgement can be checked by reading those lines. I did not check what either implementation does, except in the three probes marked `[RAN]`.
- Nothing in ASSUMPTIONS.md is treated here as the owner's decision or as the language's definition. Where an item says the owner decided something, this report says that the item says so, and no more.

## 0. Headline findings

1. **Size.** [RAN] `grep -cE '^[0-9]+[A-Za-z]?\. ' ASSUMPTIONS.md` gave `133`. The file has 133 numbered items under 132 distinct numbers (the number 215 is used twice, as `215a` at line 2104 and `215b` at line 2242). The highest number is 229. 97 of the numbers 1 to 229 are unused (section 6 lists them).
2. **How much forces a decision.** [INFERENCE] By content, 56 of the 133 items record a choice that can change whether a program is accepted, what it does when it runs, or both: 29 ACCEPT, 14 RUN, and 13 BOTH (section 1). The other 77 are messages only (9), implementation-internal (63), or already stated by DESIGN.md (5).
3. **The 56 reduce to about 30 questions.** [INFERENCE] Thirty of the 56 fall under four shared questions, defined in section 2: P1, whether the prelude's text and the FFI table are part of the specification (12 items); W1, whether the answers to requests are specified or left to an environment (8); T1, the exact post-erasure normal form that `tail`, `delegate`, and the erase-to-nothing check of §39 are judged on (6); and E1, evaluation order and the order in which the driver consumes final values (4). The other 26 stand alone.
4. **Twenty-one items present their headline choice as the owner's** (class OWNER-CLAIM, section 4). [INFERENCE] Seven of them have content that can change acceptance or runs and that I did not find settled in DESIGN.md, so a formal specification would still need an answer for each: 88, 136, 144, 145, 156, 168, and 172. Twelve more items attribute one or two points to the owner, and thirteen section preambles attribute requests, choices, or decisions to the owner. CLAUDE.md says of such entries: [QUOTE CLAUDE.md:90-93] “An entry there saying the owner decided something is a contradiction in terms.”
5. **Item 168 is partly contradicted by DESIGN.md and by both implementations.** Its sentence [QUOTE ASSUMPTIONS.md:1587-1589] “no at fact is inferred just because nullary values share an immediate representation” disagrees with DESIGN.md §35 and §36 as they stand, and a probe [RAN] (section 5, C1) shows the reference and slc both infer such a fact. Its sentence [QUOTE ASSUMPTIONS.md:1589-1590] “The source language is pure and specifies no observable evaluation order.” has no counterpart in DESIGN.md: [RAN] `grep -n -i 'pure' DESIGN.md` printed nothing (exit 1).
6. **Other places where an item and DESIGN.md read differently** are listed in section 5: when literals are interned (212 against §63), how many ways forcing fails (91 against §7), terms as trees or as entries (19 against §5, by the item's own account), when §8's invariant is restored (139 against §7), reached absurd code (35 against §25), `Imm` under `--no-extern` (228 against §44), and five smaller ones.
7. **No item says it is superseded.** [RAN] `grep -n -i 'supersed\|obsolete' ASSUMPTIONS.md` printed nothing (exit 1). [INFERENCE] Only 5 items are stale because DESIGN.md now states them (32, 57, 69, 113, and 138; quotes in section 2.6).
8. **Budgets and fuel (goal 3).** Six items record a bound in slc that DESIGN.md does not name: 111, 170, 188, 197, 213, and 229 (section 3.16). [RAN] `grep -n -i 'fuel\|budget' DESIGN.md` printed nothing (exit 1). The one elaboration bound DESIGN.md names is [QUOTE DESIGN.md:2752-2753 §62] “At most 10000 expansions run in one run, every file on the command line included.”

## 1. Summary tables

All counts are computed by a script from the list in section 2, so they agree with it by construction. Every figure is `[INFERENCE]` (it counts my classifications).

### 1.1 Count per class

"Primary class" follows the task's definitions, with OWNER-CLAIM split out of STALE. Because an OWNER-CLAIM item still records a behaviour, the third column counts each such item under the class its content would have. Section 6 gives the rule I used to tell an OWNER-CLAIM item from an item that merely mentions the owner.

| Class | Items by primary class | Items when each OWNER-CLAIM item is counted by its content | Of the content count, prelude text (P1) |
|---|---|---|---|
| ACCEPT | 25 | 29 | 3 |
| RUN | 12 | 14 | 0 |
| BOTH | 12 | 13 | 9 |
| MESSAGE | 7 | 9 |  |
| IMPL | 51 | 63 |  |
| STALE (DESIGN.md states it today) | 5 | 5 |  |
| STALE / OWNER-CLAIM (headline choice attributed to the owner) | 21 | (folded into the rows above) |  |
| UNSURE | 0 | 0 |  |
| **Total** | **133** | **133** | **12** |
| ACCEPT + RUN + BOTH | 49 | 56 | 12 |

Two reading aids:

- **Prelude text.** Twelve of the 56 record what `lib/prelude.sl` declares (names, signatures, and models). A program's acceptance and results do depend on them, so the conservative rule files them under ACCEPT or BOTH, but they pose one question between them (P1), not twelve.
- **Warnings.** The MESSAGE class assumes the default mode. [QUOTE DESIGN.md:161-163 §4] “`--warnings-as-errors` makes a run that warns fail; a silenced warning does not count (MANUAL.md).” [INFERENCE] Under that flag, the three warning items (155, 193, and 195) and the warning half of 213 also decide whether a run fails.

### 1.2 Count per DESIGN.md area

Areas are those of DESIGN.md's own table of contents [READ DESIGN.md:21-35]. An item is filed under the area of the section it mainly touches. Two cautions: "termination" (§17 to §20) holds `tail` and `delegate`, which DESIGN.md specifies in §19, and six of its seven items (all but item 75) are about those checks, not about termination; "other" holds items with no DESIGN.md subject (extraction, slc's internals, tests, and tooling).

| DESIGN.md area | ACCEPT | RUN | BOTH | MESSAGE | IMPL | STALE | OWNER-CLAIM | Total | ACCEPT + RUN + BOTH by content |
|---|---|---|---|---|---|---|---|---|---|
| syntax | 0 | 0 | 0 | 2 | 0 | 0 | 1 | 3 | 0 |
| scope and facts | 2 | 0 | 0 | 1 | 3 | 2 | 2 | 10 | 2 |
| types | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 1 | 0 |
| multiplicities and erasure | 1 | 0 | 0 | 0 | 1 | 0 | 3 | 5 | 3 |
| termination | 4 | 0 | 0 | 0 | 2 | 0 | 1 | 7 | 5 |
| data types and matching | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 3 | 2 |
| expressions, statements, and compile time | 1 | 2 | 0 | 1 | 2 | 1 | 1 | 8 | 4 |
| coercion | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| slots, `at`, and cells | 4 | 1 | 1 | 0 | 3 | 0 | 0 | 9 | 6 |
| prelude, FFI, and literals | 5 | 6 | 11 | 0 | 13 | 1 | 5 | 41 | 25 |
| sugar | 2 | 0 | 0 | 0 | 2 | 1 | 0 | 5 | 2 |
| macros | 5 | 1 | 0 | 1 | 0 | 0 | 0 | 7 | 6 |
| goals | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 1 | 0 |
| other | 0 | 0 | 0 | 0 | 24 | 0 | 8 | 32 | 0 |
| **Total** | **25** | **12** | **12** | **7** | **51** | **5** | **21** | **133** | **56** |

### 1.3 The 56 by shared question

| Shared question | Items | Count |
|---|---|---|
| P1 | 107, 118, 119, 120, 122, 123, 132, 135, 136, 137, 147, 209 | 12 |
| W1 | 59, 143, 144, 145, 198, 199, 214, 215b | 8 |
| T1 | 77, 88, 164, 174, 189, 207 | 6 |
| E1 | 65, 168, 188, 211 | 4 |
| (stands alone) | 5, 14, 19, 33, 35, 75, 114, 115, 117, 139, 154, 156, 157, 158, 165, 167, 172, 202, 212, 213, 215a, 216, 217, 218, 219, 220 | 26 |
| **Total** | | **56** |

## 2. The full classified list

One row per item, grouped by class and ordered by number within a class (the file's own order differs in two places: 123 precedes 121, and 214 and 215b follow 226). "Lines" are the item's lines in ASSUMPTIONS.md. Questions are phrased to be neutral: they state what the formal specification would have to say, not what it should say, and they do not judge the session's choice. A fragment in straight quotes in a Note cell is copied from the item's own lines; the generator checks each one.

### Shared questions

Four questions recur. A row that begins with one of these tags falls under it.

- **P1, the prelude and the FFI table.** Is the text of `lib/prelude.sl`, with the FFI table's names, arities, and shapes, part of the specification's initial environment; and does the specification's run use the prelude's models or the FFI's implementations? DESIGN.md delegates the content: [QUOTE DESIGN.md:1966 §42] “`lib/prelude.sl` is the reference for what it defines.” It constrains the two against each other: [QUOTE DESIGN.md:1952-1955 §42] “implementation must agree with its model: except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31).” The handoff lists the second half as not worked out: [QUOTE handoff.md:36] “whether the spec runs the prelude's models of extern types and functions or the FFI implementations”. [INFERENCE] If the specification takes the prelude's text as given, the twelve P1 items need no separate decisions; if it restates the prelude, each is a choice.
- **W1, requests and the world.** Does the specification say what each request answers, or is its run parameterized over an environment that answers them? DESIGN.md delegates here too: [QUOTE DESIGN.md:1990-1991 §42] “`lib/prelude.sl` is the reference for the requests and their answers.” and [QUOTE DESIGN.md:1995-1996 §42] “MANUAL.md describes `ConfinePaths`, `ConfineOutputBytes` and the command-line flags that stand in for them.” DESIGN.md names no individual request: [RAN] `grep -c 'ReadLine\|GetArgs\|ListDir\|Measure\|ReadRemaining\|GetEnv\|AppendFile\|MkDir' DESIGN.md` gave `0`.
- **T1, the post-erasure normal form.** What exactly is the post-erasure code, and its normal form, on which `tail`, `notail`, `delegate`, and the erase-to-nothing check of §39 are judged? DESIGN.md gives the criterion in prose: [QUOTE DESIGN.md:821-827 §19] “Tail position is judged on the post-erasure code, where erased positions, types, coercions and placings are gone and every `let` that only renames has been resolved away (§33, §42).” BUGS.md, which sessions wrote and whose entries I did not reproduce, reports the two compilers disagreeing at its edges: [QUOTE BUGS.md:98-102] “**The two compilers disagree on a `let` of a constant before a `delegate` call.**” and [QUOTE BUGS.md:112] “**`slc` refuses a `tail` call returned beside an `at` entry.**”
- **E1, order.** Does the specification fix an evaluation order among the sub-expressions of one form, and an order and a time at which the driver consumes the final values of several files? [QUOTE DESIGN.md:1319-1323 §31] “Evaluation is eager.” [RAN] `grep -n -i 'left to right\|evaluation order\|order of evaluation' DESIGN.md` printed one line, 699, which is about the lexicographic order of `subterm` arguments (§17). The handoff records a previous session's finding to the same effect: [QUOTE handoff.md:34] “DESIGN.md does not state the order among the sub-expressions of one form.” DESIGN.md does fix some order: see section 3.3.

### 2.1 ACCEPT (25 items)

| No. | Lines | Area | Label | Question the formal specification would have to answer | DESIGN.md | Note |
|---|---|---|---|---|---|---|
| 14 | 21-23 | data types and matching | Scope within one `def-adts` group | Within one `def-adts` group, which of the group's types may a type constructor's own telescope mention, and which may a value constructor's? | §21, §27, §54 |  |
| 19 | 27-34 | scope and facts | Applications kept as trees, not entries | Is every constructor application an entry of its own with an `is` rule (§5), or a tree, and is any difference observable (age, automatic slot, and aliasing)? | §5, §7, §9, §35 | The item says the two "should agree"; its first half (result entries) is now in §19. |
| 75 | 342-369 | termination | Same-level test reads levels canonically | Is a call's split into same-level and lower-level judged on the canonical forms of the callee's level and the current level, including where a branch-forced fact aliases the current level to an older one? | §7, §17, §19, §48 | The item itself says it "alters which programs are accepted". §48 states the canonical reading for an inferred annotation. |
| 77 | 371-387 | termination | Erased nested definitions leave no code | T1: what does the post-erasure code that `tail`, `delegate`, and at-function checks read contain for a nested `erased` function or the phantom constructors of a nested `def-adts`? | §14, §19, §39 |  |
| 114 | 696-722 | expressions, statements, and compile time | Result entries opened after the form | When do the entries standing for the results of a `match`, `cell-match`, or call enter scope relative to the form's branches, body, and arguments, and can `delegate-of` and `at-fn-of` find them? | §21, §26, §28, §33, §39, §53 |  |
| 115 | 730-756 | sugar | Metas solved by ordered unification | Within one boundary, in what order are the constraints that solve metas applied (the expected telescope before the arguments, arguments left to right, and the newer of two metas bound), and does acceptance depend on it? | §47, §50 |  |
| 117 | 779-798 | sugar | Open metas in terms; boundaries settle | Where exactly is an unsolved meta refused, and how does a match annotation or typed `let` with `_` entries take its expectation (for example, only when the two telescopes have one length)? | §47, §50 |  |
| 119 | 821-829 | prelude, FFI, and literals | Prelude levels anonymous, calls bare | P1: is each prelude lemma at an anonymous level (`_`), with bare calls, as described here? | §42, §46, §48 |  |
| 123 | 835-842 | prelude, FFI, and literals | No type extern for FFI's convenience | P1: which prelude types carry the `extern` mark (here: none for the FFI's convenience, so `Cmp` is plain)? | §33, §37, §42 |  |
| 139 | 1263-1290 | scope and facts | `Matchable` invariant restored after forcing | Is §8's invariant (at most one opened `Matchable` names a constructor) restored inside a forcing, at each atom-to-atom unification, or after the forcing completes, and are the two the same for what is accepted? | §7, §8 | The headline and the ranking of entries are now §8's; this residue is the item's. |
| 157 | 1530-1536 | slots, `at`, and cells | Locations kept apart from `is` rules | Are slots atoms of the one fact table, canonicalized like any other (§35), or a separate partition that only listed operations merge, and do the two give the same slot equalities? | §7, §35, §36 |  |
| 158 | 1538-1539 | multiplicities and erasure | Phantom and absurd bodies skip checks | In the branch of a phantom constructor under a non-erased scrutinee, or in an absurd body, which checks on uses and multiplicities are skipped? | §14, §15, §21, §25 | The usage half is §15's; what "multiplicity-promotion" names is not established. |
| 164 | 1566-1573 | slots, `at`, and cells | Word availability for `at`; `let` normalization | From which entry is the word of an `at` return read back, must one be available at run time, and on what normal form of nested `let`s is tail position judged (T1 in part)? | §19, §36 |  |
| 165 | 1575-1576 | prelude, FFI, and literals | Extern-model context is lexical | Does the body of an extern function, in the sense of §42 and §43, include the bodies of functions nested in it? | §37, §42, §43 |  |
| 167 | 1581-1584 | prelude, FFI, and literals | Extern `Array`: in place, no cell binder | Under `--no-extern`, does a type marked `extern` still count as extern for the cell rules (§37, §43), so that a pattern on it has no cell binder? | §37, §42, §43, §44 |  |
| 174 | 1634-1640 | termination | slc normalizer drops unused constant bindings | T1: does the normal form that `tail` and `delegate` are judged on drop unused erased or constant bindings and one-value wrappers? | §19, §35, §36 |  |
| 189 | 1729-1742 | termination | Let-bound match floated only under atoms | T1: is a `match` whose results a `let` binds and the body's final `values` returns in tail position, and under which continuations? | §19, §36 |  |
| 202 | 2020-2026 | slots, `at`, and cells | `at` entries projected; results bound first | When a body or branch returns several results, is a result that is not a variable bound to an entry before the later results are checked, so that a later return's `at` can name its slot? | §15, §26, §36 |  |
| 207 | 2028-2032 | slots, `at`, and cells | Erase-to-nothing check; `_`-annotated match | T1: on what normal form is erasing to nothing (§39) judged, and is a `_`-annotated match inside an at-function or at-match branch an at-match or an ordinary match the body check must cover? | §39, §40, §47 | OPEN.md 36A cites this item. |
| 212 | 2058-2090 | prelude, FFI, and literals | Literal table; when literals are interned | When are a literal's entries created relative to the elaboration of the form that contains it, and how does `prove-predates` read a level given without a name? | §5, §18, §45, §63 | Its first sentence appears to differ from §63 (section 5). |
| 213 | 2092-2102 | macros | Expansion: suppress regions, fuel, and `let-match` splicing | Are the macro calls among a `let-match`'s branches expanded once, before the form is classified as a statement or a `match` (§52), and which file's `;! suppress` regions cover a form whose position a macro supplied? | §4, §52, §62 |  |
| 215a | 2104-2117 | macros | Handles: splicing, literals, and delegate entries | Where may a spliced handle stand (a reference; a head that dispatches a special form or a macro), what does a handle to a literal enter where it is spliced, and which entry does a handle to a `delegate`-bodied function name? | §6, §63, §64 |  |
| 217 | 2141-2165 | macros | `settled-type` of a type handle; `settled-eq` | What is `settled-type` of a handle that already reads a minted type, what does such a handle denote when spliced as an expression, a type, or a name, and against which facts is a minted type read? | §64, §65 |  |
| 218 | 2167-2179 | macros | Which handles count as literals | Which handles count as a literal where a form requires or refuses one, and are the forms a macro returns searched for literals? | §45, §63, §64 |  |
| 219 | 2181-2201 | macros | `read-file`: directories and refusal texts | How is a source name's directory derived for `read-file`, and what text does a `Fail` answer carry (a macro can read it)? | §65 |  |

### 2.2 RUN (12 items)

| No. | Lines | Area | Label | Question the formal specification would have to answer | DESIGN.md | Note |
|---|---|---|---|---|---|---|
| 33 | 43-47 | coercion | Run-time value of a first-class constructor | What is the run-time word of an unapplied value constructor, and what do applying it and matching through a held constructor read at run time? | §24, §33, §67 | Its second half (a match reads the `Matchable`'s type) is now in §24. |
| 35 | 48-50 | data types and matching | Reached absurd code raises | What does the run do at the body of an `absurd` function, or at a match none of whose branches is real: no step, or a crash? | §21, §25, §31, §59 |  |
| 59 | 125-129 | prelude, FFI, and literals | Program arguments; what `ReadLine` answers | W1: where do a program's arguments come from, and what does `ReadLine` answer (is the newline kept; what at end of input)? | §27, §42 |  |
| 65 | 245-255 | expressions, statements, and compile time | Driver: every file's final, in order | E1: when several files each end in a final value, in what order, and when relative to elaborating the later files, is each consumed; what does reaching absurd code do? | §27, §31 | BUGS.md 19 records that the two compilers differ on the timing. |
| 154 | 1463-1502 | prelude, FFI, and literals | Literal printing keyed to prelude's types | Is §45's literal printing keyed to the prelude's own `Nat`, `Char`, and `String` entries rather than to names, and what does a `Char` or `String` whose code is not a byte print as? | §28, §45 |  |
| 188 | 1686-1727 | expressions, statements, and compile time | `slc --interpret`: finals, fuel, and error blocks | E1, W1: may a run stop with an error after a bounded number of steps (fuel), and is that a crash in §31's sense; in what order are several files' finals performed; what does a `world-do` reached with no world do? | §27, §31, §42 |  |
| 198 | 1964-1987 | prelude, FFI, and literals | What the path fence admits | W1: how does a confined file request resolve its path (symlinks, `..`, and the last component), and does a `ConfinePaths` in one file's final hold for the finals after it? | §27, §42 |  |
| 199 | 1989-1999 | prelude, FFI, and literals | Counting output against the byte limit | W1: what counts against `ConfineOutputBytes` (what is a created entry; is a failed request charged), and what does exceeding it do? | §31, §42 |  |
| 214 | 2230-2240 | prelude, FFI, and literals | `world-do` node; output limit; `Measure` start | W1: what does a request that would exceed the output limit do, from where does a `Measure` reading count, and is `world-do` performed the same way whether or not extern implementations run? | §31, §42 |  |
| 215b | 2242-2259 | prelude, FFI, and literals | How `Measure` orders its own allocation | W1: are the figures a `Measure` request answers specified at all, or may they be any value of the answer's type? | §42 |  |
| 216 | 2119-2139 | macros | How an `MMany` handle carries its value | Does an `MMany` handle carry the value its entry had when the handle was minted, or does `settled-value` read the entry's stored value when it runs, and can the two differ? | §13, §64, §65 |  |
| 220 | 2261-2269 | slots, `at`, and cells | `Slots`: answer for a slot held twice | When a `Slots` table holds one slot more than once, which number do `slots-find` and `slots-intern` answer? | §42, §67, §69 |  |

### 2.3 BOTH (12 items)

| No. | Lines | Area | Label | Question the formal specification would have to answer | DESIGN.md | Note |
|---|---|---|---|---|---|---|
| 5 | 14-17 | prelude, FFI, and literals | `Special` constructors named with a `%` prefix | What are `Special`'s constructors called, as distinct from the form names bound to them; are those names in scope, and how does a `Special` value print? | §19, §42, §45, §54 |  |
| 107 | 633-651 | prelude, FFI, and literals | Prelude character operations; `CEq`'s shape | P1: are `char-cmp`, the shape of `CEq`, and the absence of `char-to-nat` and `nat-to-char` part of the specification's initial environment? | §42, §45 |  |
| 118 | 808-820 | prelude, FFI, and literals | Prelude primitives return their relations | P1: are `nat-mod`, `double`, `Mod`, and the lemmas named here, as shaped here, part of the initial environment? | §42 |  |
| 120 | 830-834 | prelude, FFI, and literals | `lt-dec`'s model; `Dec` and `Cmp` plain | P1: are `lt-dec`'s model and evidence, and plain (non-extern) `Dec` and `Cmp`, part of the initial environment? | §42, §45, §49 |  |
| 122 | 881-901 | prelude, FFI, and literals | `Rope`, `flatten`, and `RChar` in prelude | P1: are `Rope`, `flatten`, `append`, and `RChar`, as shaped here, part of the initial environment? | §42 |  |
| 132 | 1134-1164 | prelude, FFI, and literals | `sub`, `mul`, `div`, and `divmod` extern | P1: are `sub`, `mul`, `div`, and `divmod`, with these signatures and models, part of the initial environment? | §42 |  |
| 135 | 1213-1221 | prelude, FFI, and literals | `Half` extern over `Nat`; `nat-halve` | P1: is `Half`, an extern type held as its `Nat`, with `nat-halve`, part of the initial environment? | §42 |  |
| 137 | 1236-1245 | prelude, FFI, and literals | Four string externs in the prelude | P1: are `str-cmp`, `str-length`, `str-split`, and `nat-str`, with these signatures and models, part of the initial environment? | §42 |  |
| 143 | 1303-1324 | prelude, FFI, and literals | Ten more `Request` constructors, their answers | W1: which requests exist, and what does the driver answer for each (`ListDir` sorted and without `.` and `..`, `AppendFile` creating the file, `Missing` versus `Fail`, and `Changed` versus `Unchanged`)? | §27, §42 | The types are prelude text (P1); the behaviours are the driver's. |
| 147 | 1363-1374 | prelude, FFI, and literals | `thunk` is a prelude function | P1: is `thunk` a prelude function (not a form), with the level discipline described here? | §27, §42, §57 |  |
| 209 | 2034-2040 | prelude, FFI, and literals | `array-pluck`'s model; missing `SetNth` lemma | P1: are `array-pluck`'s model (its one store written full-at) and the absence of a `SetNth`-to-`Nth` lemma part of the initial environment? | §44 |  |
| 211 | 2042-2056 | slots, `at`, and cells | Which arguments are bound first | E1: which arguments of a call are bound to an anonymous entry before the call, what slot does a parameter take when its argument is a written variable, when is the `at` check made relative to meta solving, and does the binding order fix an evaluation order? | §15, §35, §36, §50 |  |

Item 5 was probed, because its class hinges on whether the `%` names are visible. [RAN] in `proto/A8/t/`, with `/home/user/sleight/_build/default/bin/main.exe`: `special1.sl`, which is `(let ((many x)) let)` then `x`, printed `(%let)`; `special2.sl`, which is `(%let)`, printed `(%let)`; and `special3.sl`, which adds `(comptime-match many x (%let))` and ends in `(Zero)`, printed `0`. Each exited 0. So the prefixed names are in scope for a program and appear in a printed final value.

### 2.4 MESSAGE (7 items)

| No. | Lines | Area | Label | DESIGN.md | Note |
|---|---|---|---|---|---|
| 31 | 35-36 | types | `Type` printed as `(Univ)` in messages | §10 | The comparison itself is §10's; only the printing is the item's. |
| 155 | 1504-1517 | syntax | Warnings as their own channel | §4 |  |
| 193 | 1767-1794 | syntax | Indentation warning: text and timing | §4 |  |
| 195 | 1837-1866 | scope and facts | Shadowing warning: binders and messages | §5, §19 |  |
| 196 | 1877-1947 | expressions, statements, and compile time | What `dump-context` reports | §27, §54 | §54 makes the form always stop elaboration, so only its report is at stake. |
| 225 | 2290-2293 | goals | Goal shown as spelled where set | §71 |  |
| 226 | 2203-2223 | macros | Which macro calls a message names | §62 |  |

### 2.5 IMPL (51 items)

A note marks the items that sit near the line: a part of the item touches a rule that DESIGN.md states, or the item records a budget.

| No. | Lines | Area | Label | DESIGN.md | Note |
|---|---|---|---|---|---|
| 36 | 54-60 | other | `--repl` convenience mode |  | Tooling; the item says it "goes beyond section 27's one-expression file". |
| 42 | 64-66 | prelude, FFI, and literals | FFI table file; prelude embedded in binary |  |  |
| 43 | 67-72 | prelude, FFI, and literals | Reference's representation of extern values |  |  |
| 44 | 73 | other | Test runner elaborates prelude per mode |  |  |
| 48 | 77-81 | prelude, FFI, and literals | `String` held as an OCaml slice | §45 | §45 leaves the run-time holding of a `String` to the implementation. |
| 51 | 83-90 | prelude, FFI, and literals | Numeral entries minted directly | §45 | §45 leaves this to the implementation. |
| 54 | 92-100 | prelude, FFI, and literals | Stack limits under `--no-extern` | §31 |  |
| 60 | 131-138 | prelude, FFI, and literals | String literals bound directly | §45 | Its last sentence (a string does not intern its characters' numerals) only changes which literal entries exist and their ages. |
| 61 | 151-187 | other | Extraction embeds values, extracts functions | §27, §29 |  |
| 62 | 188-209 | other | Extracted values are `Obj.t`; wide shapes | §33 |  |
| 63 | 210-228 | other | Extraction of matches; reached absurd code | §21 | Same question as item 35 for reached absurd code. |
| 64 | 229-244 | other | FFI shared by embedding |  |  |
| 66 | 256-265 | other | Generated printer in extracted programs | §45 |  |
| 67 | 266-280 | other | Extraction test harness |  |  |
| 72 | 307-317 | termination | Renaming `let` replaced in compiled code | §19 | The check's half (tail position seen through a `let` that returns its binders) is now in §19. T1-related. |
| 74 | 328-340 | termination | Renaming-`let` substitution reaches nested bodies | §19 | A compiler fix; T1-related. |
| 83 | 394-409 | data types and matching | How the prototype compiles a match | §8, §24, §42 |  |
| 92 | 457-470 | other | What the bootstrap fixpoint shows |  |  |
| 95 | 510-523 | other | slc emitter's recursion measure |  |  |
| 96 | 525-553 | other | slc elaborator's recursion measure; `Steps` |  |  |
| 97 | 555-601 | scope and facts | slc proves fresh ids absent |  |  |
| 98 | 603-618 | scope and facts | slc reads proofs by arity | §7 | Records that forcing adds a rule before the types are unified, so terms are ill-typed in between (see section 3). |
| 100 | 624-632 | expressions, statements, and compile time | `let-match` code by erasure and position | §27, §29, §52 | The semantic half (fields `Settled` in run position) is §29's. |
| 111 | 658-669 | sugar | slc budget for generated forms | §52 | Fuel-like: the zero case is "reported as an internal error". |
| 112 | 670-679 | prelude, FFI, and literals | `U8` is its `Nat` inside slc |  |  |
| 116 | 758-777 | other | Style of `self/*.sl`: `_` and `$` |  |  |
| 121 | 851-872 | other | `self/` deciders and lookups return evidence |  |  |
| 131 | 1108-1133 | other | slc compile-time store of blocks | §33 |  |
| 148 | 1378-1389 | other | Extractor sharing-table bucket scan |  |  |
| 151 | 1429-1443 | prelude, FFI, and literals | slc builds extern results from models' types | §42 |  |
| 152 | 1444-1454 | prelude, FFI, and literals | FFI tables: one record per extern |  | The order of two refusals is a message matter. |
| 153 | 1455-1461 | other | Test directive `; externs: only` | §42 | The item calls it "a hole in section 42's requirement" (section 5). |
| 162 | 1541-1560 | other | Extracted variants with mutable fields | §33, §37 |  |
| 163 | 1562-1564 | other | Extractor emits captured blocks identity-first | §36, §38 |  |
| 166 | 1578-1579 | prelude, FFI, and literals | FFI boundary: `Cmp` results, `Rope` view |  |  |
| 169 | 1595-1601 | other | slc: multiplicity versus physical result shape | §35 |  |
| 170 | 1603-1616 | other | slc heap: stores with override maps | §31, §37 | Fuel-like: the diagnostic printer "bounds recursive traversal at depth 100000". |
| 173 | 1629-1632 | other | Extracted unions as one-constructor variants | §33 |  |
| 175 | 1642-1648 | other | Extractor buffers fills for cyclic captures |  |  |
| 181 | 1663-1664 | other | slc `ExprDemand` and `DemandBridge` |  |  |
| 184 | 1666-1669 | prelude, FFI, and literals | Whether print/read-back becomes a test | §45 |  |
| 187 | 1676-1684 | expressions, statements, and compile time | A run may update an embedded `Settled` | §27, §32 |  |
| 190 | 1744-1749 | multiplicities and erasure | Variable arguments and heads not rebound | §15, §29 | The argument half is §15's. |
| 191 | 1751-1756 | other | slc rules list is erased |  |  |
| 192 | 1758-1765 | scope and facts | Newtype lookup through the opens index | §8 |  |
| 197 | 1949-1957 | sugar | slc budget for rewritten `let-match` | §52 | Fuel-like: "The zero case stays an internal error." |
| 200 | 2006-2018 | slots, `at`, and cells | How the reference stores slots | §35, §36 |  |
| 221 | 2271-2278 | prelude, FFI, and literals | One-constructor extern type is untagged | §33, §42, §69 | §69 itself declares `Slots` as an `extern` enum with one constructor. |
| 222 | 2280-2286 | prelude, FFI, and literals | slc reads extern result type from model |  |  |
| 228 | 2298-2302 | slots, `at`, and cells | `imm` stores under `--no-extern` | §37, §44 | Records that `ImmNat` holds "of the extern representation only" (section 5). |
| 229 | 2304-2310 | slots, `at`, and cells | slc spends fuel on `imm` proofs | §37, §62 | Fuel-like: at zero it "would report" the macro-expansion limit. |

### 2.6 STALE: DESIGN.md states it today (5 items)

| No. | Lines | Area | Label | DESIGN.md | Note |
|---|---|---|---|---|---|
| 32 | 40-42 | scope and facts | Token values for erased `Settled` entries | §5, §27, §28, §29 | Stated by §5, §27, §28, and §29 (quotes below the table). |
| 57 | 110-123 | prelude, FFI, and literals | `Program`'s level index: a usage pattern | §42 | An observation on §42's `(Program L)`; records no choice. |
| 69 | 284-301 | scope and facts | Two `def-lvl` levels may unify | §7, §18, §33 | A soundness observation; records no choice. The behaviour follows from §7 (quote below the table). Pairs with item 75. |
| 113 | 681-687 | sugar | Inferred decrease annotation on bare calls | §48 | §48 states the rule; what is left is a claim the item calls "the session's reading, not the owner's". |
| 138 | 1253-1261 | expressions, statements, and compile time | `let` right-hand-side statements' scope | §27 | Stated by §27 (quote below the table). |

The DESIGN.md text that settles each:

- **32.** [QUOTE DESIGN.md:185-187 §5] “For an erased entry the stored value is a token that records that the value exists; it is not data;” [QUOTE DESIGN.md:1184-1187 §27] “A form in an erased position runs nothing, and its results are `Settled` with the token of §5.” [QUOTE DESIGN.md:1222-1224 §28] “erased fields take the tokens of §5, since the stored value does not contain them.” [QUOTE DESIGN.md:1246-1249 §29] “a `Level` is an erased token”
- **57.** [QUOTE DESIGN.md:1972-1973 §42] “`(Program L)` is an enum indexed by a level, read by the driver (§27).” [INFERENCE] The item comments on what that index costs a program's author; it records no choice of its own.
- **69.** [QUOTE DESIGN.md:297-302 §7] “A fresh atom, or an atom with no conflicting fact, always unifies.” [QUOTE DESIGN.md:310 §7] “Forcing fails, and so refutes the branch, in exactly four cases:” [INFERENCE] Two levels made by `def-lvl` are atoms and fall under none of the four cases, so that they unify follows from §7; the item is a soundness observation about that consequence. This rests on my reading of §7's four cases at lines 312 to 328.
- **113.** [QUOTE DESIGN.md:2272-2277 §48] “The elaborator then supplies one: `(predates _)` when the callee's level and the current level do not canonicalize to the same level, and otherwise `(subterm _)` before the first `subterm`-marked argument that does not canonicalize to the same term as its counterpart among the enclosing function's `subterm` arguments (§5, §19).”
- **138.** [QUOTE DESIGN.md:1124-1128 §27] “The right-hand side of a `let` is itself an expression, so the statements before its final expression are statements of the expression that contains the `let`.”

### 2.7 STALE / OWNER-CLAIM (21 items)

The quoted phrases are in section 4.1. "By content" is the class the item would have if the attribution were set aside.

| No. | Lines | By content | Area | Label | Question, where the content is ACCEPT, RUN, or BOTH | DESIGN.md | Note |
|---|---|---|---|---|---|---|---|
| 88 | 415-428 | ACCEPT | termination | Tail and delegate checks drop unread constants | T1: does the post-erasure code that `tail` and `delegate` are judged on omit a `let` of constants (literals, a nested `def-adts`'s constructors and `Matchable`) that nothing reads? | §19, §33, §36 | BUGS.md 20 records the two compilers disagreeing on a `let` of a constant before a `delegate` call. |
| 91 | 440-455 | MESSAGE | other | slc ports every check; errors accumulate |  |  | The session's own part: an error does not stop elaboration, so slc may give several messages. |
| 93 | 472-484 | IMPL | scope and facts | slc canonicalization terminates without fuel |  | §7 |  |
| 94 | 486-508 | IMPL | scope and facts | slc fact table carries erased proofs |  | §7 |  |
| 124 | 905-926 | IMPL | other | slc `Lockstep` proofs and `Syn` values |  |  |  |
| 125 | 930-962 | IMPL | other | slc code indexed by erasures |  |  |  |
| 126 | 966-990 | IMPL | other | slc never infers a type afterwards |  |  |  |
| 127 | 994-1053 | IMPL | other | slc code indexed by frames |  | §19, §27 | Also describes slc's normalizer keeping the reference's three cases for a `let` of constants (T1-related). |
| 128 | 1057-1078 | IMPL | prelude, FFI, and literals | slc decides extern marks into an enum |  | §42, §43 | The arity check at the mark is §42's and §43's. |
| 129 | 1082-1099 | IMPL | other | slc builds code at the expectation |  |  |  |
| 133 | 1165-1200 | IMPL | other | Extern types extracted through templates |  |  |  |
| 134 | 1201-1212 | IMPL | prelude, FFI, and literals | Driver converts FFI strings directly |  |  |  |
| 136 | 1222-1235 | ACCEPT (P1) | prelude, FFI, and literals | `Bin` plain; slc ids are `Nat`s | P1: is `Bin` a plain (non-extern) type? | §42, §45 |  |
| 144 | 1326-1339 | RUN | prelude, FFI, and literals | Environment requests through the driver's world | W1: where do `GetEnv`, `GetEnvs`, and `GetCwd` take their answers from, and what does `ReadRemaining` answer after earlier `ReadLine`s? | §42 |  |
| 145 | 1341-1355 | RUN | prelude, FFI, and literals | Driver uses `unix`; errno classification | W1: what do `Stat`, `MkDir`, `DeleteFile`, and `DeleteDir` answer for an absent path, an existing directory, and a path the host denies? | §42 |  |
| 150 | 1391-1424 | IMPL | other | slc interprets tail calls as tail calls |  | §31 |  |
| 156 | 1519-1528 | ACCEPT | multiplicities and erasure | Uses counted against the written binder | Are uses of a `unique` binder counted against the binder as written or against the canonical value it `is`, and which statements of an erased or unreachable body count as uses? | §14, §15, §16, §27 |  |
| 168 | 1586-1593 | BOTH | expressions, statements, and compile time | Language called pure; evaluation order unobservable | E1: does the specification fix an evaluation order among the sub-expressions of one form, and can any order be observed; when are two values that share an immediate word at one slot? | §15, §27, §31, §35, §36, §67 |  |
| 172 | 1618-1627 | ACCEPT | multiplicities and erasure | Computed head elaborated at a demand | At what multiplicity is a head that is itself a form elaborated, when its type (a `Cell`, a `UniqueFn`, or an `Fn`) decides how the application uses it? | §6, §15, §32, §37 |  |
| 180 | 1650-1661 | IMPL | multiplicities and erasure | Follow-up: typing separate from multiplicity checking |  |  | A plan for the elaborators' structure, not a language rule (see section 3). |
| 194 | 1796-1835 | MESSAGE | syntax | Messages carry file, line, and column |  | §4 |  |

### 2.8 UNSURE (0 items)

None. The items I was least able to place are named in section 7, each with what I would need to know.

### 2.9 Index by item number

For lookup. OWNER-CLAIM items show their class by content in parentheses; `P1` marks prelude text.

5 BOTH; 14 ACCEPT; 19 ACCEPT; 31 MESSAGE; 32 STALE; 33 RUN; 35 RUN; 36 IMPL; 42 IMPL; 43 IMPL; 44 IMPL; 48 IMPL; 51 IMPL; 54 IMPL; 57 STALE; 59 RUN; 60 IMPL; 61 IMPL; 62 IMPL; 63 IMPL; 64 IMPL; 65 RUN; 66 IMPL; 67 IMPL; 69 STALE; 72 IMPL; 74 IMPL; 75 ACCEPT; 77 ACCEPT; 83 IMPL; 88 OWNER-CLAIM (ACCEPT); 91 OWNER-CLAIM (MESSAGE); 92 IMPL; 93 OWNER-CLAIM (IMPL); 94 OWNER-CLAIM (IMPL); 95 IMPL; 96 IMPL; 97 IMPL; 98 IMPL; 100 IMPL; 107 BOTH P1; 111 IMPL; 112 IMPL; 113 STALE; 114 ACCEPT; 115 ACCEPT; 116 IMPL; 117 ACCEPT; 118 BOTH P1; 119 ACCEPT P1; 120 BOTH P1; 121 IMPL; 122 BOTH P1; 123 ACCEPT P1; 124 OWNER-CLAIM (IMPL); 125 OWNER-CLAIM (IMPL); 126 OWNER-CLAIM (IMPL); 127 OWNER-CLAIM (IMPL); 128 OWNER-CLAIM (IMPL); 129 OWNER-CLAIM (IMPL); 131 IMPL; 132 BOTH P1; 133 OWNER-CLAIM (IMPL); 134 OWNER-CLAIM (IMPL); 135 BOTH P1; 136 OWNER-CLAIM (ACCEPT) P1; 137 BOTH P1; 138 STALE; 139 ACCEPT; 143 BOTH; 144 OWNER-CLAIM (RUN); 145 OWNER-CLAIM (RUN); 147 BOTH P1; 148 IMPL; 150 OWNER-CLAIM (IMPL); 151 IMPL; 152 IMPL; 153 IMPL; 154 RUN; 155 MESSAGE; 156 OWNER-CLAIM (ACCEPT); 157 ACCEPT; 158 ACCEPT; 162 IMPL; 163 IMPL; 164 ACCEPT; 165 ACCEPT; 166 IMPL; 167 ACCEPT; 168 OWNER-CLAIM (BOTH); 169 IMPL; 170 IMPL; 172 OWNER-CLAIM (ACCEPT); 173 IMPL; 174 ACCEPT; 175 IMPL; 180 OWNER-CLAIM (IMPL); 181 IMPL; 184 IMPL; 187 IMPL; 188 RUN; 189 ACCEPT; 190 IMPL; 191 IMPL; 192 IMPL; 193 MESSAGE; 194 OWNER-CLAIM (MESSAGE); 195 MESSAGE; 196 MESSAGE; 197 IMPL; 198 RUN; 199 RUN; 200 IMPL; 202 ACCEPT; 207 ACCEPT; 209 BOTH P1; 211 BOTH; 212 ACCEPT; 213 ACCEPT; 214 RUN; 215a ACCEPT; 215b RUN; 216 RUN; 217 ACCEPT; 218 ACCEPT; 219 ACCEPT; 220 RUN; 221 IMPL; 222 IMPL; 225 MESSAGE; 226 MESSAGE; 228 IMPL; 229 IMPL.

## 3. The items most consequential for a formal specification

These fifteen (several are clusters, named by their lead item) would shape the relations themselves: what a term is, what the fact table holds, what the run is, and what a use is. The choice of fifteen, and each "why", is `[INFERENCE]`. Each paragraph says what the item records; none says the choice is right or wrong, and none is the owner's decision.

### 3.1 Item 19: is a term a tree or a graph of entries? (ACCEPT; §5, §7, §9, §35)

[QUOTE ASSUMPTIONS.md:27-34] “Grammar expressions are kept as trees rather than as anonymous entries with an `is` rule (section 5's picture); canonicalization should agree either way, but this is a representation choice, not the one section 5 draws.”

DESIGN.md draws the other picture: [QUOTE DESIGN.md:211-215 §5] “Every application of a type constructor or value constructor has an entry of its own, usually anonymous, whose `is` rule is that application. The reference graph of the fact table is therefore the whole structure of every term in §9's grammar. There is no separate term structure next to it.” [INFERENCE] A formal specification has to pick one representation for its static relations. Under §5's picture every application has an age (§7 orders atoms when it aliases them) and an automatic slot (§35); under the item's, it has neither. The item's "should agree" is a claim it does not support with a test or an argument. Whether slc also keeps trees is [UNKNOWN]; the item's file preamble speaks of the reference ([QUOTE ASSUMPTIONS.md:3-8] “A running log of the assumptions the prototype interpreter (`lib/`, `bin/`) makes where DESIGN.md is silent, ambiguous, or where the implementation takes a shortcut.”).

### 3.2 Item 98: forcing passes through ill-typed states (IMPL, with content that shapes the specification; §7)

[QUOTE ASSUMPTIONS.md:608-614] “The session also weighed intrinsically typed terms for the remaining well-formedness invariants and set them aside: the reference (`lib/env.ml`) adds a rule with no type check and makes the types agree by a second unification, as `refine` does, so between the two the rewritten terms are ill-typed from an intrinsic view, and slc must keep that order to accept and refuse the same programs.”

DESIGN.md states the order: [QUOTE DESIGN.md:297-302 §7] “Whenever an atom is unified with an expression, which may itself be an atom, the atom's type is then unified with the expression's type.” [INFERENCE] The item adds two things DESIGN.md does not say: that the order matters to which programs are accepted, and that it rules out terms that are well typed by construction. A specification of Sleight written in Sleight that wanted intrinsically typed terms would meet this; the item is filed IMPL only because it describes how slc is organised.

### 3.3 Item 168, with 65: the language called pure, with no observable evaluation order (OWNER-CLAIM; by content BOTH; E1)

[QUOTE ASSUMPTIONS.md:1586-1593] “The owner's clarification confirms that proof-indexed array get/set may use unsafe operations.” Then, in the same item: [QUOTE ASSUMPTIONS.md:1586-1593] “The source language is pure and specifies no observable evaluation order. Destructive updates implement that pure semantics; their execution order must not be observable in well-typed programs. The interpreter's traversal order is an implementation choice.” Item 65 leans on the same idea in passing: [QUOTE ASSUMPTIONS.md:252-255] “(elaboration still evaluates them, the language being pure)”.

Which of the item's sentences the "clarification" covers cannot be told from the text [UNKNOWN]; only the first names the owner. The handoff already warns about this item: [QUOTE handoff.md:50] “The session wrongly relied on item 168 for "the language is pure and order-free".”

What DESIGN.md says on the subject, as far as I found:

- It never uses the word: [RAN] `grep -n -i 'pure' DESIGN.md` printed nothing (exit 1).
- For forms in run position, it fixes the order between a form and what it contains: [QUOTE DESIGN.md:1184-1187 §27] “This nests: the forms inside a form run before it does, and the statements of a `let`'s right-hand side complete before the enclosing `let` does.”
- It places argument bindings before the form that contains the call: [QUOTE DESIGN.md:655-661 §15] “Every argument to a constructor, a function or a cell behaves as if it were first bound to an anonymous variable. An argument that is already a variable is not rebound. That binding is a statement (§27) placed just before the statement or final form that contains the call”
- It has one operation whose answer may vary: [QUOTE DESIGN.md:3044-3046 §67] “`ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs.”

[INFERENCE] This item decides the shape of the run relation: one machine with a fixed order, or a relation that admits every order. The handoff's proposal A, and the suspicion about a mutating heap machine that it reports the owner as holding, are about exactly this [READ handoff.md:24-25 and 34], so the item's sentence cannot be used as an answer.

### 3.4 Item 211, with 190 and 202: which arguments are bound first (BOTH; E1; §15, §35, §36, §50)

[QUOTE ASSUMPTIONS.md:2042-2056] “An argument bound first because a later entry of the signature names its parameter's slot, by `(slot-of p)` or `at p`, is found by `Elab.slot_named_params`; the entry is erased when the argument is, and its slot is the slot the signature then speaks of.” and [QUOTE ASSUMPTIONS.md:2042-2056] “The `at` check of section 36 waits for the call's metas to settle at its closing paren, rather than running as each argument is read.” Item 190 adds: [QUOTE ASSUMPTIONS.md:1744-1749] “Match scrutinees are bound, as the reference binds them.” Item 202 adds: [QUOTE ASSUMPTIONS.md:2020-2026] “A result that is not a variable is bound to an anonymous entry before the entries after it are checked, so that a later entry's `at` can name the slot it sits in”.

[INFERENCE] §15 (quoted in 3.3) says every argument behaves "as if" bound first; these items record that the implementations bind some and not others, and when. For the static relations this decides which entries and slots exist. If the binding statements are also what orders evaluation (E1), it decides which arguments run before the rest of the form.

### 3.5 Item 114: when a form's result entries enter scope, and how fetch forms find a proof (ACCEPT; §26, §28, §33, §39, §53)

[QUOTE ASSUMPTIONS.md:696-705] “but `delegate-of` and `at-fn-of` (§19, §39) find a proof by scanning `env.scope` for an anonymous entry of its type.” [QUOTE ASSUMPTIONS.md:706-709] “coercing `id` through it appears to put a `Nat` where a `Bool` is expected” [QUOTE ASSUMPTIONS.md:711-722] “The results are opened after everything the form elaborates: for a match, the branches, the coverage check and the `else`. DESIGN.md does not appear to say either way.”

[INFERENCE] The scope relation must say when the entries for a match's, a `cell-match`'s, or a call's results exist, and the relation for `delegate-of` and `at-fn-of` must say which entries they may find. The item reports that one ordering lets a branch fetch the proof its own annotation asks for.

### 3.6 Items 115 and 117: solving `_` is an algorithm with an order (ACCEPT; §47, §50)

[QUOTE ASSUMPTIONS.md:736-751] “Where some argument is `_`, the application's result over the metas — `(C metas)` for a constructor, the return telescope instantiated for a call — is unified with the expected telescope before any argument is read, as a transaction (a failure leaves the environment as it was); at the closing paren, if a `_` is still open, the same unification is run again reporting the mismatch.”

DESIGN.md describes the same thing without an order: [QUOTE DESIGN.md:2340-2342 §50] “Boundaries settle from the inside out: everything within one boundary is solved together, and a boundary nested inside it closes first, using only what is known at that point.” [INFERENCE] The specification must state the sugar either as a declarative condition ("solved together") or as this ordered procedure. If the two accept different programs, the difference is this item's.

### 3.7 Item 75, with 69: the current level under branch-forced facts (ACCEPT; §7, §17, §19, §48)

[QUOTE ASSUMPTIONS.md:342-346] “The test canonicalizes the callee's level and the current level alike, as the `Predates` check does.” The item says what it guards against: [QUOTE ASSUMPTIONS.md:354-357] “the checker would accept an `erased` function whose one branch is that self-call and whose declared return is `(erased (False) f)`, so a caller able to reach it would bind a `False` token and section 10 would be gone.” And it asks: [QUOTE ASSUMPTIONS.md:363-369] “Open for the owner: this is a reading that alters which programs are accepted, and the alternative is reading the current level literally, so that the branch keeps its recursion.”

[INFERENCE] The termination relation needs a definition of "same level" that says whether branch-forced facts count. §48 says "canonicalize" for an inferred annotation (quoted in section 2.6, item 113); for a written `(predates p)` I found no sentence either way.

### 3.8 Item 88, with 77, 164, 174, 189, and 207: the post-erasure normal form (T1; §19, §33, §36, §39)

[QUOTE ASSUMPTIONS.md:415-422] “The tail and delegate checks drop a `let` of embedded values that nothing reads.” [QUOTE ASSUMPTIONS.md:427-428] “Settled by the owner: this is the behaviour wanted, dropping a binding nothing reads changing no program's meaning.” [QUOTE ASSUMPTIONS.md:1729-1740] “any other continuation stays a `let` of the match, where a marked call is not in tail position unless the continuation returns the binders, which the normalizer folds.” [QUOTE ASSUMPTIONS.md:2028-2032] “Erasing to nothing is checked on the code after `Elab.normalize`, with `at` entries projected away.”

[INFERENCE] Whether `tail`, `notail`, `delegate`, an at-function, or an at-match is accepted is a judgement on code after erasure and normalization, so the specification needs that function exactly, case by case. These six items are six of its cases. BUGS.md, a sessions' log I did not reproduce, reports that the cases are where the compilers part: [QUOTE BUGS.md:106-109] “DESIGN.md §19 says a `delegate`-bodied function is nothing but the call once lets that only rename are resolved away, which seems not to settle a let of a constant.” Item 88's closing sentence presents its case as settled by the owner; DESIGN.md §19 does not state it.

### 3.9 Item 156, with 158: what a use is counted against (OWNER-CLAIM; by content ACCEPT; §14, §15, §16)

[QUOTE ASSUMPTIONS.md:1519-1528] “Uses are recorded against the binder as written, never its canonical value. In a computed `share` argument, the uses needed to compute that expression retain their own multiplicities. Erased and unreachable bodies contribute no usage, including statements preceding their results.”

[INFERENCE] The usage relation of §15 must say whether two binders that the fact table makes equal share one count. The item's opening sentence, which names the owner, is about the scope of an implementation task; these three sentences carry no attribution.

### 3.10 Items 172 and 180: typing and multiplicity checking, one pass or two (both OWNER-CLAIM; §6, §15, §32, §37)

[QUOTE ASSUMPTIONS.md:1618-1627] “The owner's approved narrow repair of the computed-head erased probe introduces a callable-head demand: elaborate the expression once in its actual context, taking unique demand for a Cell or UniqueFn and many for an ordinary callable.” [QUOTE ASSUMPTIONS.md:1650-1661] “Elaborate a whole function body into a typed representation that retains written labels, match modes, erased expressions, source locations, branch/refutation information and capture scopes. A later pass should calculate demands and validate uses, captures, returns and word availability before erasure and runtime-code construction.”

[INFERENCE] These record a dependency the specification will meet: how a head is used depends on its type, and its type is known only after it is elaborated. A specification can state typing and usage as two relations or as one; 180 describes the two-relation shape as work the implementations have not done. Both items attribute an approval to the owner that DESIGN.md does not record. What DESIGN.md does say about a head that is a form is [QUOTE DESIGN.md:246-247 §6] “A head that is not dispatched is elaborated only once, and is the callee of item 2.” A probe of the one acceptance question I could isolate found the reference following §37 ([QUOTE DESIGN.md:1767-1769 §37] “The cell is taken at the multiplicity of the invocation's own position (§14), whatever expression `u` is.”): [RAN] `proto/A8/t/cellhead1.sl`, whose body is `((cell-alloc Cons) _ h t)` in a `many` position, was refused with "`(cell-alloc Cons)`, a fresh cell and so unique, used at many without `share`"; `cellhead2.sl` and `cellhead3.sl`, with `share` around the invocation and around the head, each printed `(Cons _ 1 $ Nil _)`.

### 3.11 Item 139: when §8's invariant is restored (ACCEPT; §7, §8)

[QUOTE ASSUMPTIONS.md:1267-1270] “The invariant is restored after every forcing, a branch entered (`Elab.refine`), a `let-match` or `comptime-match` as much as an open, rather than inside the unifier, which the session reads as equivalent for what is accepted”

DESIGN.md puts it inside: [QUOTE DESIGN.md:297-302 §7] “When two atoms are unified, the newer becomes an alias of the older, and the opened `Matchable`s they head, if both are type constructors, are then unified as well (§8).” [INFERENCE] A forcing relation written from §7 merges at each step; a compiler that merges afterwards must be shown to agree with it. The item's "equivalent" is a reading, not a result.

### 3.12 Items 157, 169, and 200: are slots atoms of the one table? (ACCEPT, IMPL, IMPL; §7, §35, §36)

[QUOTE ASSUMPTIONS.md:1530-1536] “DESIGN.md section 36's locations are represented separately from ordinary value rules. Location terms retain the original binder when `is` canonicalization runs; only location equality and the listed location-producing operations merge that partition.” [QUOTE ASSUMPTIONS.md:2011-2012] “`Env.canon` resolves `(slot-of x)` to `x`'s binder's slot, so after canonicalization a slot is an atom.”

DESIGN.md: [QUOTE DESIGN.md:1558-1561 §35] “Whether two variables are at one slot is decided by the ordinary canonicalization of the fact table: an entry's slot is an atom, a rule may equate it with another atom, and two slots are equal exactly when their canonical atoms are equal.” [INFERENCE] The fact-table relation needs one account of slots. Items 157 and 200 may describe one design in two vocabularies, or two designs; I could not tell from the text [UNKNOWN].

### 3.13 Items 188, 65, and 187: the driver and the top-level run (RUN, RUN, IMPL; E1; §27, §31, §32, §42)

[QUOTE ASSUMPTIONS.md:251-253] “Every final expression of every file on the command line is consumed in order, as the interpreter would” [QUOTE ASSUMPTIONS.md:1695-1697] “at compile time a `Unit`, whose performer answers a `world-do` with an error block, there being no world to perform with” [QUOTE ASSUMPTIONS.md:1718-1723] “The evaluator's fuel is 1000000000, which the million-step tail loop of `tests/extern_tail.sl` needs under `--interpret`, where neither the reference nor the compiled program has a bound.”

BUGS.md records that the timing differs between the compilers: [QUOTE BUGS.md:83-87] “The reference runs a file's final value as soon as it reaches it, before reading the files after it on the command line; `slc`, compiled or under `--interpret`, elaborates every file first and runs the finals afterwards.” [INFERENCE] The top-level run relation is the driver's loop (§27, §42). It has to say when a non-last file's final value runs, and the agreement theorem has to say what a fuel-bounded run is allowed to do where the specification's run continues. Item 187 adds that a run can change, in place, a value that extraction would embed: [QUOTE ASSUMPTIONS.md:1676-1684] “the run updates that Settled's block in place”.

### 3.14 Item 143, with 59, 144, 145, 198, 199, 214, and 215b: requests and the world (W1; §27, §42)

[QUOTE ASSUMPTIONS.md:128-129] “`ReadLine` strips the newline and answers `None` at end of input.” [QUOTE ASSUMPTIONS.md:1319-1322] “`ListDir` sorts and omits `.` and `..`; `Sys.readdir` already omits them, and sorting is so that a test may compare its output byte for byte”

[INFERENCE] Requests are how a run is observed, so the run relation must either fix their answers or take them from an environment it is parameterized over. These eight items record driver behaviour that DESIGN.md does not state (W1, above). Much of it is attributed to the owner in items 144 and 145 and in the preamble at lines 1294 to 1301 (section 4), which is not the same as DESIGN.md stating it.

### 3.15 Item 216, with 212, 215a, 217, and 218: handles, literals, and the elaborator's store (RUN and ACCEPT; §45, §63, §64, §65)

[QUOTE ASSUMPTIONS.md:2119-2128] “How an `MMany` handle carries its value differs between the compilers, and is meant not to be observable.” [QUOTE ASSUMPTIONS.md:2119-2128] “This session's reading is that the two agree because nothing seems to mutate a `many` value in place (DESIGN.md section 13).” [QUOTE ASSUMPTIONS.md:2167-2175] “Only a `MintedIs` handle at `MMany` to a literal's entry counts as that literal, so an `MErased` one made by `settled-erase` is refused as a handle where a literal would be.”

[QUOTE DESIGN.md:2882-2884 §65] “The macro world is the elaborator's program store: the run-position entries with their values and facts, the literal table, the gensym counter and the expansion count.” [INFERENCE] So the specification's compile-time store has to say what a handle holds and when a literal's entries come into being. Item 216's equivalence rests on `many` values never being mutated in place, which leans on `unique` meaning sole reference. The handoff records, as a session's claim and not an owner decision, an exchange about [QUOTE handoff.md:28] “whether the project would not itself prove that the spec makes `unique` mean sole reference”; if that property is not proved, this equivalence cannot be assumed either.

### 3.16 Related, for goal 3: budgets and fuel recorded in the file

[RAN] `grep -n -i 'fuel\|budget' DESIGN.md` printed nothing (exit 1). The elaboration bound DESIGN.md does name is [QUOTE DESIGN.md:2752-2753 §62] “At most 10000 expansions run in one run, every file on the command line included.” The items that record other bounds, all in slc:

- **111 and 197**, a budget for forms the elaborator generates: [QUOTE ASSUMPTIONS.md:666-667] “the zero case is reported as an internal error.” [QUOTE ASSUMPTIONS.md:1953-1957] “the session's reading is that no chain of expansions can outrun it, each one being spent on a distinct `let-match` in that form. The zero case stays an internal error.”
- **213**, fuel ahead of that budget: [QUOTE ASSUMPTIONS.md:2096-2100] “the run's count of 10000, kept in the environment, is read as firing before any path's fuel runs out.”
- **229**, fuel spent on forms that are not macro calls: [QUOTE ASSUMPTIONS.md:2304-2310] “A run with fuel left at zero there would report "more than 10000 macro expansions".”
- **188**, the evaluator's fuel under `--interpret` (quoted in 3.13).
- **170**, a depth bound in a printer: [QUOTE ASSUMPTIONS.md:1615-1616] “The diagnostic printer reads current bodies and bounds recursive traversal at depth 100000.”
- **96** says of its own `Steps` budgets: [QUOTE ASSUMPTIONS.md:543-545] “The session's reading is that this is not a fuel: no path reports exhaustion, and the checker rejects a budget too small for the hops below it.”
- **93** records the opposite approach for canonicalization, attributed to the owner (section 4.1).

BUGS.md 18 lists fuel in slc's evaluator separately: [QUOTE BUGS.md:29-33] “running out becomes a `BError` ("out of fuel") rather than `REmpty` or `Nil`.”

### 3.17 Runners-up

[INFERENCE] Four more would shape a relation, each more narrowly. Item 35 (what the run does at absurd code: no step, or a crash). Item 33 (what word an unapplied constructor is; the handoff's proposal B leaves the same question open for functions [READ handoff.md:36]). Items 165 and 167 with 228 (how far the `extern` mark reaches, and what `--no-extern` changes in checking, not only in running). Item 170, an IMPL item, states what slc's heap proofs do not establish: [QUOTE ASSUMPTIONS.md:1603-1611] “They do not establish unchanged current contents across Stores, acyclicity, or preservation of source typing and uniqueness by updates.”

## 4. OWNER-CLAIM: every place the file attributes something to the owner

[RAN] `grep -c -i "owner" ASSUMPTIONS.md` gave `70`; `grep -n` lists the lines. I read each in its item. They fall into four groups; the grouping, and the "kind" column, are `[INFERENCE]`. Whether the owner said any of these things is [UNKNOWN] to me and is not claimed here; DESIGN.md is the only record this report treats as the owner's.

### 4.1 Items whose headline choice is attributed to the owner (21; class OWNER-CLAIM)

| No. | Kind | The phrase | By content |
|---|---|---|---|
| 88 | settled | [QUOTE ASSUMPTIONS.md:427-428] “Settled by the owner: this is the behaviour wanted, dropping a binding nothing reads changing no program's meaning.” | ACCEPT |
| 91 | request | [QUOTE ASSUMPTIONS.md:440-442] “At the owner's request ("make it not trusting") the compiler ports every check of `lib/elab.ml` and `lib/env.ml`” | MESSAGE |
| 93 | direction | [QUOTE ASSUMPTIONS.md:472-475] “At the owner's direction, the compiler's canonicalization terminates by a structural argument rather than by fuel.” | IMPL |
| 94 | direction | [QUOTE ASSUMPTIONS.md:486-489] “Again at the owner's direction, the owner having set aside a stamped version with a runtime comparison, a fully verified map, and an eager-substitution design” | IMPL |
| 124 | direction | [QUOTE ASSUMPTIONS.md:905-908] “At the owner's direction, from a review of where the compiler reports internal errors that a type could refute.” | IMPL |
| 125 | direction | [QUOTE ASSUMPTIONS.md:930-932] “At the owner's direction, the next item of the same review.” | IMPL |
| 126 | direction | [QUOTE ASSUMPTIONS.md:966-967] “At the owner's direction, in place of a depth-indexed `Term`.” | IMPL |
| 127 | direction | [QUOTE ASSUMPTIONS.md:994-1006] “At the owner's direction, the first rung of a ladder the session proposed after reading DESIGN.md with CPDT's dependent de Bruijn representation in mind (`member` and `hlist`); the owner set the second rung (arity-indexed application) aside as common-case special casing (CLAUDE.md 6), and the session withdrew the third (shape-indexed values) on the owner's question about branch refinement” | IMPL |
| 128 | direction, request | [QUOTE ASSUMPTIONS.md:1057-1059] “At the owner's direction, the second item of the same ladder.” [QUOTE ASSUMPTIONS.md:1075-1078] “The arity check at the mark is made in both compilers, at the owner's request” | IMPL |
| 129 | direction | [QUOTE ASSUMPTIONS.md:1082-1084] “At the owner's direction, the fourth rung of the same ladder.” | IMPL |
| 133 | decision | [QUOTE ASSUMPTIONS.md:1165-1168] “(the owner's decision, after this session proposed it, with the owner's hole discipline: every hole but a branch body is filled with a variable name)” | IMPL |
| 134 | request | [QUOTE ASSUMPTIONS.md:1201-1203] “(the owner's request, after a performance audit)” | IMPL |
| 136 | decision | [QUOTE ASSUMPTIONS.md:1222-1224] “(the owner's decision: every use of `Bin` erased in `slc`, the conversion through `Half`)” | ACCEPT (P1) |
| 144 | choice | [QUOTE ASSUMPTIONS.md:1326-1328] “as `GetArgs` does, the owner's choice” | RUN |
| 145 | choice | [QUOTE ASSUMPTIONS.md:1341-1342] “(the owner's choice)” | RUN |
| 150 | request, suggestion | [QUOTE ASSUMPTIONS.md:1391-1394] “At the owner's request, who asked that `slc`'s compile-time evaluation not grow the stack, or at the least that interpreting a tail call be a tail call.” [QUOTE ASSUMPTIONS.md:1417-1420] “the owner suggested that shape” | IMPL |
| 156 | permission, preference | [QUOTE ASSUMPTIONS.md:1519-1528] “The owner allows restructuring the self-hosted heap and staged restoration of erased proof invariants, while preferring the compiler to continue exemplifying checked correctness through dependent proofs.” | ACCEPT |
| 168 | clarification | [QUOTE ASSUMPTIONS.md:1586-1593] “The owner's clarification confirms that proof-indexed array get/set may use unsafe operations.” | BOTH |
| 172 | approval | [QUOTE ASSUMPTIONS.md:1618-1627] “The owner's approved narrow repair of the computed-head erased probe” | ACCEPT |
| 180 | approval, requirement | [QUOTE ASSUMPTIONS.md:1650-1661] “The owner approved finishing the narrow computed-head repair, while explicitly requiring this broader approach later.” | IMPL |
| 194 | request | [QUOTE ASSUMPTIONS.md:1796-1798] “The owner asked that they, and so `lib/reader.ml`'s `loc`, which is a file and a position” | MESSAGE |

[INFERENCE] In items 156 and 168 the attribution opens the item and the sentences after it carry none, so how much of each item it covers cannot be told from the text. In item 91 the item itself separates the two: [QUOTE ASSUMPTIONS.md:449-452] “A reading of the session, not the owner's: an error does not stop elaboration, so a program may be refused with more than one message where the reference gives its first.”

### 4.2 Items that attribute one or two points to the owner (12; classed by content)

| No. | Class | Kind | The phrase |
|---|---|---|---|
| 61 | IMPL | observation | [QUOTE ASSUMPTIONS.md:168-171] “(the owner's observation, checked against `Eval.close` and `elab_def_fns`)” |
| 63 | IMPL | reading | [QUOTE ASSUMPTIONS.md:219-222] “(the owner's reading: interpretation is the checked path, extraction is opted into for speed)” |
| 77 | ACCEPT | request | [QUOTE ASSUMPTIONS.md:382-385] “The owner asked for the same reading to be applied to a nested `def-adts`'s *phantom* constructors” |
| 107 | BOTH (P1) | direction, twice | [QUOTE ASSUMPTIONS.md:641-651] “`CEq` repeats its index rather than carrying an `Eq`, at the owner's direction” [QUOTE ASSUMPTIONS.md:641-651] “The prelude has no `char-to-nat` or `nat-to-char`, at the owner's direction” |
| 116 | IMPL | observation | [QUOTE ASSUMPTIONS.md:776-777] “a style the owner has not written” |
| 117 | ACCEPT | request | [QUOTE ASSUMPTIONS.md:797-798] “Whether a meta solved inside a match branch may escape it was raised and left out at the owner's request.” |
| 122 | BOTH (P1) | question | [QUOTE ASSUMPTIONS.md:891-893] “(the owner's question, the session's yes)” |
| 132 | BOTH (P1) | request; shapes disclaimed | [QUOTE ASSUMPTIONS.md:1134-1137] “(the owner asked for the low-hanging Nat arithmetic; the shapes below are the session's, chosen to mirror `add` and `nat-mod`, and open to change)” |
| 139 | ACCEPT | naming | [QUOTE ASSUMPTIONS.md:1288-1290] “The keywords are the owner's” |
| 143 | BOTH | choice, twice | [QUOTE ASSUMPTIONS.md:1306-1308] “the owner's choice over a two-field `EnvVar`” [QUOTE ASSUMPTIONS.md:1311-1314] “the session's argument for it, which the owner took” |
| 162 | IMPL | direction | [QUOTE ASSUMPTIONS.md:1546-1555] “at the owner's direction” |
| 184 | IMPL | a stated non-decision | [QUOTE ASSUMPTIONS.md:1666-1669] “Not decided, and left open by the owner” |

### 4.3 Section preambles that attribute something to the owner (13; not numbered items)

| Lines | Heading it sits under | Items in that section | The phrase |
|---|---|---|---|
| 104-108 | Programs (section 27) | 57, 59, 60 | [QUOTE ASSUMPTIONS.md:104-108] “Asked for by the owner in chat: an ADT read by the driver, "quasi monad", efficient, able to read a whole file by name, write a whole string to a file, write to stdout or stderr with a flush, read a line from stdin, read the command-line arguments and exit with a code, kept alongside the `String -> String` form as an optional alternative.” |
| 142-149 | OCaml extraction (extract.ml) | 61 to 67 | [QUOTE ASSUMPTIONS.md:142-149] “Written by a session working autonomously at the owner's request, in chat: extraction "in the sense of Coq's extraction", with compile-time computation embedded in the extracted OCaml as its result rather than recomputed, since compile-time calculation is meant as a performance construct (the owner's words, paraphrased).” |
| 304-305 | Fixes from a bug-hunting session | 72 | [QUOTE ASSUMPTIONS.md:304-305] “reported its findings in chat, and the owner picked which to fix.” |
| 432-438 | A compiler written in the language (self/) | 91 to 98 | [QUOTE ASSUMPTIONS.md:432-438] “Written by a session working autonomously at the owner's request, in chat: name the language SL for now, self-host it, write in SL a program compiling SL to OCaml that can interpret the compile-time `Settled` part, and use the existing OCaml interpreter and extractor to get there.” |
| 802-806 | A proof-carrying prelude | 118, 119, 120, 123 | [QUOTE ASSUMPTIONS.md:802-806] “The owner decided that the FFI adder returns an `Add` proof with a plain adder as a `delegate` over it, that `double` is derived from it, that `trim` is transparent, that `str-append` gets a relation, and that levels should be used judiciously with `_`. The names and the shapes below are the session's.” |
| 846-849 | The compiler's libraries carry evidence | 121 | [QUOTE ASSUMPTIONS.md:846-849] “The owner chose three of the session's proposals for `self/`'s library layer — deciders return evidence, lookups return evidence, lists carry specs — and left moving the libraries into the prelude aside.” |
| 876-879 | `Rope`, and strings built in one pass | 122 | [QUOTE ASSUMPTIONS.md:876-879] “The owner asked for `Rope` without length caching for now (DESIGN.md section 42 describes it)” |
| 1103-1106 | The compile-time interpreter's values live in a store | 131 to 137 | [QUOTE ASSUMPTIONS.md:1103-1106] “Proposed by the session and agreed by the owner in chat, who chose Nat addresses over Bin ones, weakening as a coerce, and no list of addresses kept in the heap.” |
| 1250-1251 | Opening a `Matchable` (DESIGN.md section 8) | 138, 139 | [QUOTE ASSUMPTIONS.md:1250-1251] “The owner decided the points marked so; everything else is the session's reading, with the tests as the evidence.” |
| 1294-1301 | More requests (section 27) | 143, 144, 145 | [QUOTE ASSUMPTIONS.md:1294-1301] “The owner chose the general `Pair`, sorted listings, the `world` for the environment and the working directory, single-level `MkDir`, deletion that reports `Unchanged` rather than failing on an absent path, and the `unix` dependency; the shapes below are the session's.” |
| 1359-1361 | `thunk` (section 27) | 147 | [QUOTE ASSUMPTIONS.md:1359-1361] “The owner proposed the in-language helper that thunks a value rather than an anonymous function form, and accepted the extra verbosity at the call sites; the rest below is the session's.” |
| 1673-1674 | slc's interpret mode (sections 27, 32) | 187 to 195 | [QUOTE ASSUMPTIONS.md:1673-1674] “The owner asked for an interpret option for `slc` in place of emitting OCaml. The shapes below are the session's, made without the owner.” |
| 1870-1875 | `dump-context` | 196, 197 | [QUOTE ASSUMPTIONS.md:1870-1875] “The owner asked for a special form that, applied, errors out and dumps what would help the programmer” |

[INFERENCE] The preamble at 1103 to 1106 is about item 131's subject (a store, addresses, and weakening); items 132 to 137 follow it under the same heading but are about other things.

### 4.4 Mentions that are not claims of a decision

For completeness, the remaining mentions say the opposite or ask a question, and need no flag: the file's own preamble ([QUOTE ASSUMPTIONS.md:3-8] “nothing here is a design decision.”); the preambles at 321 to 326, 391 to 392, 691 to 694, and 726 to 728; the disclaimers in items 91, 113, and 162 ("not the owner's"); and the questions put to the owner in items 75, 114, and 196.

## 5. Items that appear to contradict DESIGN.md as it stands today

Both texts are quoted in each case. "Appear" is meant: each entry is my reading of two texts, `[INFERENCE]`, and only C1 was probed. They are ordered by how much I think they matter to a formal specification.

**C1. Item 168 against §35 and §36: slot facts from a shared immediate word.**
[QUOTE ASSUMPTIONS.md:1586-1593] “Distinct logical location classes need not imply distinct physical words; no at fact is inferred just because nullary values share an immediate representation.”
[QUOTE DESIGN.md:1591-1596 §35] “A non-phantom constructor `C` with no non-erased field, of a type not marked `extern` or `newtype`, has a tag slot when an opened `Matchable` lists it. That slot is a built-in slot per position among the fieldless non-phantom constructors for a tagged type, and `vacant-slot` for an untagged one. Tag slot 0 is `vacant-slot`, and each tag slot is its own slot.”
[QUOTE DESIGN.md:1688-1691 §36] “an application of a constructor that has a tag slot or is of a hollow type, and a `cell-alloc` of one, where an opened `Matchable` lists the constructor (the value or cell with its tag slot, or with `vacant-slot`, §35);”
[RAN] `proto/A8/t/tagslot1.sl` declares two enums, `Color` with `Red` and `Green` and `YN` with `Yes` and `No`, and a function `g : (many (Color) x) (many (YN) y at x) -> (many (Nat) n)`, then calls `(g a b)` with `a` bound to `(Red)` and `b` to `(Yes)`. `/home/user/sleight/_build/default/bin/main.exe t/tagslot1.sl` printed `0` and exited 0; `/home/user/sleight/_build/release/slc --interpret t/tagslot1.sl` did the same. `tagslot2.sl` differs only in binding `b` to `(No)`; both refused it with ``error: argument 2, `y`, of `g` does not satisfy `at` `vacant-slot` `` and exit 1. So both implementations treat the first fieldless constructors of two unrelated types as at one slot, as §35 and §36 say, and the item's sentence no longer describes them.

**C2. Items 168 and 65 against DESIGN.md as a whole: "pure".** The item's sentences are quoted in section 3.3. DESIGN.md has no such statement ([RAN] `grep -n -i 'pure' DESIGN.md`, no output), and it describes mutation as real: [QUOTE DESIGN.md:1746-1755 §37] “This is a physical store into memory that the cell's eventual invocation re-creates; it does no usage accounting of its own.” It also fixes some order (section 3.3). This is an unsupported claim more than a contradiction; whether any order is observable is exactly question E1.

**C3. Item 212 against §63, and against item 218: when a literal is interned.**
[QUOTE ASSUMPTIONS.md:2058-2061] “Both compilers intern a literal where it is first met, from an expression's literal case, `numeral-of` and the `intern-*` primitives, with no pass over a form ahead of elaborating it.”
[QUOTE DESIGN.md:2778-2780 §63] “each top-level form of the source has its literals interned and replaced by such handles just before it is elaborated.”
[QUOTE ASSUMPTIONS.md:2167-2175] “The conversion of a top-level form's literals into handles runs on the forms read from the source alone”
Whether the difference can be observed is [UNKNOWN]. The time of interning is at least visible to the fact table: [QUOTE DESIGN.md:302-303 §7] “of two literals the one interned first is the older.”

**C4. Item 91 against §7: how many ways forcing fails.**
[QUOTE ASSUMPTIONS.md:442-443] “the three contradictions of forced unification (section 7)”
[QUOTE DESIGN.md:310 §7] “Forcing fails, and so refutes the branch, in exactly four cases:”
Item 126 uses the same count: [QUOTE ASSUMPTIONS.md:986-990] “deciding section 7's third contradiction”. The dangling-binder case it means is the third of §7's four [READ DESIGN.md:320-324].

**C5. Item 19 against §5: trees or entries.** Quoted in section 3.1. The item says of itself that its representation is [QUOTE ASSUMPTIONS.md:27-34] “not the one section 5 draws”, and claims the two agree.

**C6. Item 139 against §7 and §8: when two opened `Matchable`s are unified.** Quoted in section 3.11. DESIGN.md also says: [QUOTE DESIGN.md:364-366 §8] “`Matchable`s would name one thing, whether at an open or when a forcing (§7) equates two type constructors or two value constructors, they are unified by forcing.” The item restores the invariant after the forcing and reads that as equivalent.

**C7. Item 35 against §25 and §59: absurd code.**
[QUOTE ASSUMPTIONS.md:48-50] “**An absurd function's code raises** if ever reached; a match whose real branches are all absurd or phantom likewise compiles to code that raises.”
[QUOTE DESIGN.md:1063-1064 §25] “Its body is an erased position (§14), and it compiles to no code.”
[QUOTE DESIGN.md:2631-2632 §59] “The function compiles to no code, and holding it at `many` is fine: the pointer is never followed.”
This may be a difference of wording only: a stub that raises is one way to have "no code" for the body. For a run relation the question is real (section 3.17).

**C8. Item 228 against §44: what `Imm` asserts when the models run.**
[QUOTE ASSUMPTIONS.md:2298-2302] “so the session reads `ImmNat`, and every `Imm` built from it, as true of the extern representation only”
[QUOTE DESIGN.md:2061-2063 §44] “`(Imm A v)` says that `v` is an immediate however it is built, and the `-imm` operations take it as evidence. `ImmNat` gives it for a `Nat` below `u62-modulus`”
§44's sentence is not limited to the extern representation; the item says the claim fails for the model's `Nat`.

**C9. Item 213, slc's half, against §4: suppress regions for a position a macro supplies.**
[QUOTE ASSUMPTIONS.md:2092-2102] “A position a macro gives that names a file other than the one being read is covered by no `;! suppress` region in `slc`, which keeps the regions of the current file alone; the reference reads the regions of the file the position names.”
[QUOTE DESIGN.md:153-154 §4] “A position rebuilt from a `Pos` belongs to the place the `Pos` names.”
The reference's behaviour matches that sentence as I read it; slc's does not. The item records the two compilers differing.

**C10. Item 83 against §24: reading a held `Matchable`.**
[QUOTE ASSUMPTIONS.md:403-409] “The code appears to read a held `Matchable` whether or not its type carries the `extern` mark.”
[QUOTE DESIGN.md:1049-1052 §24] “its value is read only for an extern type.”
Probably unobservable, since §8 requires a dispatching match's `Matchable` to be readable whatever its marks [READ DESIGN.md:387-390].

**C11. Item 153 against §42: every test both ways.**
[QUOTE ASSUMPTIONS.md:1455-1459] “The session's reading is that this is a hole in section 42's requirement that `dune test` run every test both ways, and should stay rare.”
[QUOTE DESIGN.md:1958-1961 §42] “`--no-extern` runs the models instead, and `dune test` runs every test both ways.”
The item says so itself. It concerns the test suite, not the language.

**C12. Item 157 (and 169) against §35: where slot facts live.** Quoted in section 3.12. The two wordings differ, as the quotes there show; whether the behaviour differs is [UNKNOWN].

**C13. Item 36 against §27, by its own account.** [QUOTE ASSUMPTIONS.md:54-56] “prints every expression's value, which goes beyond section 27's one-expression file; it is a convenience only.” A tooling mode.

### Stale references inside items

These cite DESIGN.md for something it does not contain today. None changes a class.

| Where | What it says | Check |
|---|---|---|
| Preamble, 876-878 | [QUOTE ASSUMPTIONS.md:876-878] “(DESIGN.md section 42 describes it)”, of `Rope` | [RAN] `grep -n 'Rope' DESIGN.md` printed nothing (exit 1) |
| Item 132 | [QUOTE ASSUMPTIONS.md:1157-1158] “Beside the lemmas section 42 names” | [RAN] `grep -n 'lemma' DESIGN.md` printed nothing (exit 1) |
| Item 194 | [QUOTE ASSUMPTIONS.md:1805-1807] “section 12's phantom-constructor warning” | [RAN] `grep -n -i 'phantom' DESIGN.md \| grep -i warn` printed nothing (exit 1); [READ WARNINGS.md:77-82] has it as WARNINGS.md item 7 |
| Item 132 | [QUOTE ASSUMPTIONS.md:1144-1148] “returning the quotient and the remainder both `many`, with the erased characterisation once” | DESIGN.md's only `divmod` type is an example of notation with two parameters and two returns: [QUOTE DESIGN.md:103-106 §3] “(Fn L (subterm many (Nat) n) (many (Nat) d) -> (many (Nat) q) (many (Nat) r))”. [READ lib/prelude.sl:257-258] The prelude's `divmod` takes a third, erased parameter and returns four erased values besides. §3 does not say its example is the prelude's function. |

## 6. Method

**What I read, and how.**

- `brief-common.md`, `CLAUDE.md`, and `handoff.md` in full.
- [READ DESIGN.md:1-3156] in eight consecutive chunks: 1-400, 400-799, 800-1199, 1200-1599, 1600-1999, 2000-2399, 2399-2798, and 2798-3156.
- [READ OPEN.md:1-211], [READ SPEC-REVIEW.md:1-35], and [READ BUGS.md:1-139] in full.
- [READ ASSUMPTIONS.md:1-2310] in eight consecutive chunks, each overlapping the last by a line or more: 1-282, 282-619, 619-928, 928-1249, 1248-1519, 1519-1768, 1767-2006, and 2001-2310. I classified each chunk's items before reading the next, then revisited every ACCEPT, RUN, BOTH, STALE, and OWNER-CLAIM item against DESIGN.md.

**Counts.** [RAN] `grep -cE '^[0-9]+[A-Za-z]?\. ' ASSUMPTIONS.md` gave `133`. [RAN] `grep -nE '^\s+[0-9]+[A-Za-z]?\. ' ASSUMPTIONS.md` printed nothing, so no item is indented or nested. The items carry 132 distinct numbers: `215` appears twice, as `215a` (line 2104) and `215b` (line 2242). The highest number is 229. The file is not in numeric order in two places: item 123 (line 835) precedes item 121 (line 851), and items 214 (line 2230) and 215b (line 2242) follow item 226 (line 2203).

**Gaps.** 97 of the numbers 1 to 229 have no item: 1-4, 6-13, 15-18, 20-30, 34, 37-41, 45-47, 49-50, 52-53, 55-56, 58, 68, 70-71, 73, 76, 78-82, 84-87, 89-90, 99, 101-106, 108-110, 130, 140-142, 146, 149, 159-161, 171, 176-179, 182-183, 185-186, 201, 203-206, 208, 210, 223-224, 227.

**Rules I applied.**

- *Conservative filing.* Where an item plausibly affects acceptance or runs, it is not under IMPL, even when the item itself claims the difference cannot be observed (19, 139, 157, and 216 are filed this way).
- *Mixed items.* An item with a part DESIGN.md now states and a part it does not is filed by the part it does not, and the note says which part is DESIGN.md's (31, 33, 72, 75, 100, 139, 158, and 190).
- *OWNER-CLAIM.* An item is OWNER-CLAIM when the choice its title names is attributed to the owner (a decision, choice, approval, agreement, clarification, direction, permission, or request), or when the item opens with such an attribution and leaves unclear how much of the rest it covers. An item whose titled choice is the session's, with one clause attributed to the owner, is filed by content and listed in section 4.2. Item 132 is filed by content because its own parenthesis says the shapes are the session's and open to change.
- *Prelude text.* An item that records what `lib/prelude.sl` declares is filed ACCEPT or BOTH and tagged P1.
- *No judgement of the choices.* No row says whether a session's choice was right.

**Checks on this report.**

- The tables in sections 1 and 2 are generated by `proto/A8/build.py` from one list, `proto/A8/items.py`; the script asserts that the list has exactly the 133 item numbers found in the file, that every label has 3 to 8 words, and that every ACCEPT, RUN, or BOTH row (by class or by content) has a question.
- `proto/A8/checkquotes.py` takes every `[QUOTE file:lines]` in this report, joins the cited lines of the cited file with single spaces, and requires the quoted text to occur in them. [RAN] `python3 proto/A8/checkquotes.py reports/A8-assumptions-backlog.md` printed `166 quotes checked, 0 failures; 168 QUOTE tags; 1 curly-quoted spans without a tag`. The two tags beyond the quotes checked, and the one loose span, are this report's own descriptions of the tag syntax.
- Three probes ran the prebuilt binaries on files under `proto/A8/t/`: `special1` to `special3` (item 5), `tagslot1` and `tagslot2` (C1), and `cellhead1` to `cellhead4` (section 3.10). No `dune`, `git`, or bootstrap command that changes state was run.

**Items I was least sure about.** 19, 33, 69, 139, 157, 158, 164, 169, 172, 181, 212, and 216 for their class, and 91, 132, and 156 for whether they are OWNER-CLAIM. Section 7 says why for each.

## 7. Things I am least sure of

1. **Items filed conservatively that may be IMPL.** Items 19, 139, 157, and 216 each say the difference they record is not observable. I filed them ACCEPT or RUN because that claim is the item's own and is not checked. To move them I would need a proof or a failed search for a distinguishing program. Item 33 (the word of an unapplied constructor) is RUN only on the strength of `slot-eq` being able to compare words.
2. **Item 158.** I could not establish what "multiplicity-promotion checks" names. [RAN] `grep -rn -i 'promot' --include='*.ml' --include='*.sl' --include='*.md' . | grep -v '^./_build'` found it in ASSUMPTIONS.md only at line 1538; every other hit is about garbage-collection figures (`promoted-words` and the like) or an unrelated sentence under `agent/solutions/`. The item's usage half is §15's; if the other half is too, the item is STALE, not ACCEPT.
3. **Item 212.** Most of it describes how the two compilers keep the literal table. I filed it ACCEPT because literals are on the task's list for that class and two of its sentences plausibly reach acceptance (the time of interning, and how `prove-predates` reads an unnamed level). IMPL would be defensible. C3 is a difference between two texts; I did not find a program that shows it.
4. **The P1 group.** Whether twelve records of prelude content belong among the choices that change acceptance depends on a decision this report cannot make: whether the prelude's text is part of the specification. Section 1.1 gives the counts both ways.
5. **Where OWNER-CLAIM starts.** The rule in section 6 puts 21 items in the class and 12 beside it. Items 91, 132, and 156 are the closest calls: 91 opens with the owner's request and then disclaims one reading; 132 names a request and disclaims its shapes; 156 opens with a permission and then states three rules with no attribution.
6. **Item 69 as STALE.** It rests on my reading that §7's four failure cases do not cover two `def-lvl` levels. If the owner reads §7 otherwise, the item is ACCEPT and belongs with item 75.
7. **slc-side normalizer items.** I filed 174 under ACCEPT (T1) and left the similar passages of 127 under its OWNER-CLAIM class with content IMPL. Both describe slc keeping the reference's normal form; the split follows what each item's headline is about, and could be argued either way.
8. **Budgets.** Items 111, 197, and 229 are IMPL although a budget that runs out refuses a program. Item 197 reads that case as unreachable, and item 124 says the same of 111's; 229 does not say. If any is reachable, slc refuses a program the reference accepts, which is a defect in slc and not a question for the specification.
9. **The terse batch, items 156 to 181.** Most of these have no title and little context. My readings of 164, 169, 172, and 181 in particular may miss what the writing session meant. For 172, the probe in section 3.10 tested one reading only.
10. **Areas.** An item touching several sections is filed under one. The per-area counts in section 1.2 would shift by a few items under a different assignment, most visibly for `tail` and `delegate` (filed under §19's area, "termination").
11. **What I did not do.** I did not check any item's description of the implementations against the code, apart from the three probes. A row's class says what the recorded choice could change if the item describes the implementations correctly.
