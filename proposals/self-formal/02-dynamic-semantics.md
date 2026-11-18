# 02 — The spec's run: dynamic semantics as a heap machine

Written overnight by an agent exploring options for the owner. Everything
here is a proposal or a reading. Nothing in it is approved, and nothing
in it is the owner's decision unless it says so and cites the brief's
list of owner statements.

Sources are marked: **§n** quotes DESIGN.md; **file:line** is code;
**[compiled]** is a test run tonight, with the reference
(`_build/default/bin/main.exe`) unless it names slc or OCaml, files under
`proposals/self-formal/proto/dyn/` or a `proto/review*/` directory;
**(reading)** is my inference.

## 1. Summary

- DESIGN.md already places its compile-time run on stripped code: a
  run-position form "is elaborated, its erased positions are stripped,
  the evaluator runs the code" (§27), and §19, §36, and §39 speak of the
  post-erasure code at runtime. DESIGN.md defines no run on unstripped
  code; §35 says "An erased variable has no word". (reading) So a heap
  machine would run stripped code, and the stripped-mode concern (which
  owner statement 6 says goes away with a mutable heap) becomes a
  type-soundness obligation over stripped code with a heap typing. (Both
  interpreters do give an erased position a placeholder: slc's `CErased`
  evaluates to a `BToken` block, `self/elab-main.sl:173-176`, and the
  reference's to `VToken`, `lib/eval.ml:22`.)
- Proposal: a small-step machine whose words are `Imm n | Ptr a`, with
  `a` an abstract address that can only be compared. Blocks are mutable.
  The step function is total, and an explicit continuation stack holds
  the rest of the run. Proposal B's abstract addresses are enough, once
  immediates and the representation identities of §33, §35, and §41 are
  added. A prototype (`proto/dyn/machine.sl`) compiles and runs a total
  step looped by the `Program` driver with no fuel counter; as committed,
  its finite oracle tape bounds the run (2.6).
- Evaluation order: DESIGN.md fixes eagerness (§31) and run-position
  nesting (§27), and with §6 ("The head is elaborated first") the
  head-before-arguments order in run position (reading). §15's hoisting
  ("behaves as if ... bound ... placed just before the statement") fixes
  a timing only if "behaves as if" covers time, which DESIGN.md does not
  say; read that way it puts argument forms before a form head, against
  the run-position reading. DESIGN.md does not state the order of body
  statements in general (though §61 presumes written order in one
  case), of sibling arguments, or of `values` entries. Whether Proposal A
  conflicts with §15 depends on whether A applies before or after
  hoisting (2.2).
- (reading, unproved conjecture) In the abstract machine, order seems
  observable only through crashes, stuck states, and divergence (cost,
  which a program can read through the `Measure` request, becomes part
  of the world's answers once those are inputs, 2.3):
  world effects are totally ordered by the unique `World`, and mutation
  goes only through unique references. Recommendation: fix one order in the spec (no
  confluence proof needed), and leave order-independence as an optional
  later theorem.
- `slot-eq` is nondeterministic by §67, and its answers do vary between
  implementations and modes in practice (no run-to-run variation was
  seen): the reference interpreter and `slc --interpret` answer `ENone`
  where code compiled by either with externs answers `ESome`
  [compiled]; under the reference's `--no-extern` the compiled code
  also answers `ENone`. Recommendation: make the spec a deterministic
  function of the program, the world's answers, and an oracle tape of
  `slot-eq` bits; the compiler theorem says some oracle exists.
- Crash: "agrees or crashes" has no teeth. Recommendation: allow a crash
  only at named resource events, and make compile-time crash a
  deterministic function of an explicit depth bound.
- Externs: §35 gives literal tag slots only "with externs", and §33's
  extern-`Nat` requirement is stated only "With externs on", so acceptance
  depends on the extern mode by DESIGN.md's own text [compiled]. A spec
  that runs the `Nat` model must either give up the extern-only facts or
  choose a word for each tag slot (E1).
  Recommendation: make `Nat` a machine primitive (immediate words) and
  run every other extern's model.

## 2. Findings

### 2.1 What DESIGN.md says about the run

- §31: "Evaluation is eager. The semantics is that of a machine with
  unlimited stack and heap. A real run may crash where the host cannot
  represent what is asked of it. A crash produces no value, never a
  different one. How a crash is reported is not specified".
- Stripped code. §27: "it is elaborated, its erased positions are
  stripped, the evaluator runs the code, and its results become
  `Settled`". §29: "its value was never computed, because the erased
  positions are stripped before the evaluator runs". §36: "The runtime
  signature of a function consists of its non-erased entries that have
  no written `at`". §19: "Tail position is judged on the post-erasure
  code, where erased positions, types, coercions and placings are gone
  and every `let` that only renames has been resolved away".
- Representation, §33: "every value is one word, either an immediate or
  a pointer to a block, whatever its type"; "A value is the tuple of
  its constructor's non-erased fields; a single field is stored bare";
  "A value carries a tag only when its type is an enum with more than
  one non-phantom constructor"; a fieldless value "is the word of the
  `Nat` of its position among the fieldless non-phantom constructors
  when its type is tagged, the word of `vacant-slot` (§35) when its type
  is untagged and not marked `extern`, ..., and an unspecified word
  otherwise"; "`vacant-slot`'s word is that of `Nat` 0. With externs on,
  the extern `Nat`'s FFI must meet this for these numbers"; "The
  pointer of a `delegate`-bodied function is its callee's pointer".
  Newtypes are "represented exactly as that constructor's one non-erased
  field".
- Slots, §35/§38: "Its word is the word of `x`"; "At runtime, the value
  of a slot is a word, either a pointer or an immediate. A slot is
  inert"; "Nothing relies on two slots being distinct. A slot says
  nothing about contents". §36: "A slot may belong to consumed entries;
  address equality does not change when contents do." §35: "With the
  prelude, `(slot-of 0)` is `vacant-slot`; with externs too, `(slot-of
  k)` is tag slot `k`."
- `at`, §36: "An `at` return is absent from the physical values of a
  call. ... the elaborator supplies its word from a non-erased entry in
  the same slot: the caller's own binder for the argument the promise
  names, which the caller still holds whether or not the call consumed
  it".
- Cells, §37: `cell-alloc` gives "a fresh cell at unique, at no slot,
  with every slot `vacant-slot`". `cell-write` at `unique` "is a
  physical store into memory that the cell's eventual invocation
  re-creates"; at `many` "the result is a fresh block holding the old
  words with the written slots replaced". An invocation at `unique`
  "consumes `u` and creates its value at `u`"; at `many` its value is
  "at the cell when every store is skipped ... and otherwise as a fresh
  copy at nothing". With `(at)`, "the store is skipped", and `(at m (u
  ...))` "performs nothing".
- At-functions, §39: "Calling an at-function skips its runtime; its
  arguments are still evaluated, as §15 binds them"; "an at-function
  compiles to a function that does nothing and returns no word".
  At-matches, §40: "its scrutinee is evaluated as for any match, but the
  match itself ... compiles to no code".
- Externs, §42: "An `extern` implementation must agree with its model:
  except through `slot-eq` (§67), running the models instead of the
  implementations must give a program the same values, though not the
  same cost, and either may crash where the other does not (§31)." §43:
  "A `unique` value of an extern type may be mutated in place by the
  FFI." §69: "The models search with `slot-eq`, so §42's exception for
  `slot-eq` covers what the implementations answer."
- §13: "Where a value can be mutated in place ... a `unique` binder on
  that value is the only reference to it. Where nothing can mutate the
  value, the sole-reference property is neither promised nor needed".
- §66–§70: `Placed` "is represented as the word of `v`"; `slot-eq`:
  "`ESome` proves that `a` and `b` hold one word (§38). `ENone` proves
  nothing, so an implementation may always answer it, and which one a
  call answers may differ between runs"; `cell-same` and `fn-same`
  "compile to nothing".
- §72: native-compute "may crash where the evaluator would not, and the
  other way round (§31). ... a run that crashes is an error at its
  argument."
- §42 (Program): the driver "never recurses, so an unbounded interaction
  is the driver's loop over total functions"; a world "is taken `at
  vacant-slot`, so the driver passes it no word".

### 2.2 Evaluation order: what is fixed

Fixed by DESIGN.md:
1. Eager evaluation (§31).
2. §15: "Every argument to a constructor, a function or a cell behaves
   as if it were first bound to an anonymous variable. ... That binding
   is a statement (§27) placed just before the statement or final form
   that contains the call". §15 is about uses of unique binders, and its
   first paragraph says "The order of the uses does not matter". (reading)
   It fixes evaluation order only if "behaves as if" covers time and
   statements run in written order; DESIGN.md says neither in general.
   Eagerness alone already makes an argument run before its call.
3. §27, run position only: a run-position form "runs as soon as it has
   been elaborated, before the code after it is checked"; "the forms
   inside a form run before it does, and the statements of a `let`'s
   right-hand side complete before the enclosing `let` does".
   Run-position statements are sequential (§32: "since run-position
   statements are sequential"). §6 item 1: "The head is elaborated
   first" and "A head that is a form is `Settled` in run position, since
   it runs as soon as it is elaborated (§29)"; §28: in run position each
   call, match, constructor application, and `coerce` "runs as soon as it
   is elaborated". (reading) So in run position a head that is a form
   runs before the argument forms are elaborated, so before they run.
4. Skipped calls and at-matches still evaluate their arguments and
   scrutinee (§39, §40).
5. (reading) World requests are totally ordered by dataflow: `world-do`
   takes `(unique (World) w ...)` and gives back `w2` (§42), so only one
   world is ever usable. `MacroWorld` is threaded the same way (§65).
6. §61 presumes an order of body statements in one case: "The write
   stores `h` before the call: left to the invocation, that store would
   follow the call and the `tail` claim would fail." No dataflow orders
   that `cell-write` statement before the `let` of the call (`cell2` is
   used only in the final form), so (reading) §61 presumes written order
   there, or reads it off §19's tail-call requirement.

Not fixed in general (DESIGN.md does not say, as far as I found):
- The order of the statements of a function body at runtime, beyond
  §61's case. Otherwise only scoping and dataflow order them.
- The mutual order of several bindings hoisted by §15 before the same
  statement.
- Head against arguments outside run position. §15 names only
  arguments. §29 speaks of "the elaborator's own binders for its head,
  arguments and scrutinee (§15)", but §15 binds no head and no scrutinee
  (rough edge 2 in section 5 below).
- The order of the entries of a `values`, and of the stores of one
  invocation.

[compiled, `--extract`] `order2.sl`: in `(values (g (h n)) (h (g n)))`
the reference emits `(h n)`, then `(g n)`, and then the two outer calls
as OCaml `let x = g .. and y = h .. in`. The OCaml 4.14 manual
(ocaml.org/manual/4.14/expr.html) says such a `let` "evaluates expr1 …
exprn in some unspecified order", and that for an application "The
order in which the expressions expr, argument1, …, argumentn are
evaluated is not specified"; OCaml 4.14.1, as installed, evaluates
`let ... and` in written order, both `ocamlopt` and `ocamlc`
[compiled], while it evaluates application arguments and tuple
components right to left. In
`((pick) (h n))` the reference emits the head `(pick)` first, then
`(h n)`, then the application: it does not hoist the argument above a
form head. `order1.sl` emits `(g n)` then `(h n)` for `(f (g n) (h n))`.

(reading) Applied to source forms before hoisting, Proposal A ("within
one form, sub-expressions left to right, head first") gives `(h n)`,
`(g ..)`, `(g n)`, `(h ..)` for the `values`, while hoisting with
statements in written order gives `(h n)`, `(g n)`, `(g ..)`, `(h ..)`.
Applied after hoisting, A agrees with hoisting there. For `((pick) (h
n))`, A and the reference agree (head first), and a timing reading of
§15 would not. slc's interpreter evaluates a call's head before its
arguments (`self/elab-main.sl:178-182`), threading its world through
both.

[compiled] Two programs, each one `Program` step, observe a head form
against an argument form inside a body, with a world write on one side
and a stack overflow on the other. In `proto/dyn/head_crash_arg_write.sl`, the head
form overflows and the argument writes "argument ran"; in
`proto/dyn/head_write_arg_crash.sl`, the head form writes "head ran"
and returns a `UniqueFn` that closes over the world, and the argument
overflows. Under the reference (interpreted, and built natively and
with `--byte`), its `--no-extern` interpreter, `slc --interpret`, and
slc's native and `--byte` builds, the first prints nothing before
"Stack overflow" and the second prints "head ran" before it. In each,
`proto/dyn/crash_probe.sl` prints "before" and not "after": a write
before an overflow is shown, and nothing runs after the overflow. With
the overflow made harmless (depth 10 in place of 10^8), each prints its
write and exits 0. So in these two tests, one call shape each, every
implementation and mode tried runs the head form before the argument
form. The reference's `--no-extern --build` was not tried: it
overflows while extracting these files.

### 2.3 Is order observable in the abstract machine?

(reading; no proof) Candidate observers, assuming no crash:
- `world-do`: ordered by the unique world (2.2 item 5). Not affected by
  the order of independent pure work.
- In-place mutation (cells §37, FFI §43): only through a unique binder,
  which §13 says is "the only reference". Slot words are pointers but
  "inert" (§38): no read goes through them except `at` reconstruction,
  which reads back a live or just-consumed binder's word (§36). If
  §13's property holds as a heap invariant, a write cannot be seen by
  independent work.
- Allocation: if addresses are abstract (B), with no order or
  arithmetic, nothing in the language can tell allocation order apart.
  §45 prints "a cell, a slot, a function" as `_`.
- `slot-eq`: the *set* of allowed answers depends only on word
  identity, which dataflow fixes. A specific oracle tape consumed in
  step order would make the answers depend on order, so an
  order-independence statement has to quantify over oracles.
- Compile time: within one macro run, `gensym`, `read-file`, and the
  other §65 primitives are ordered by the unique `MacroWorld`. Which
  number a given `gensym` call gets also depends on the order in which
  the elaborator reaches macro calls. §65 threads the world "sequentially
  through all of elaboration", and §6 elaborates the head first, but I
  found no statement of the order in which a call's arguments are
  elaborated. Both implementations expand every macro call among an
  application's arguments before elaborating any argument, or a head
  that is a name (01, §3.6, `proto/review3/gensym_depth.sl`,
  `proto/review4/01_head_name_err.sl`). A gensym number can reach the output (`intern-nat`, §65),
  so elaboration order is observable; that is a question about the
  elaboration spec, separate from runtime evaluation order.
  `native-compute` results are constructors with no non-erased field
  (§72), so sharing plays no part.
- `Measure` (`lib/prelude.sl:1386`) answers wall and CPU time, words
  allocated, and GC counts (`MkUsage`, `lib/prelude.sl:1331-1335`),
  "totals since the Program began", so a program can observe cost, and
  through it the order of work between two requests. In a spec where the
  world's answers are inputs, this is absorbed by quantifying over
  answers, not by order-independence.
- Not covered: crashes, stuck states, and divergence. In a body whose
  statements are `(let ((unique w2) (many _)) (world-do _ w (WriteOut
  "x")))` and `(let ((erased xs) (unique a) (erased p)) (array-new _
  huge))`, with no dataflow between them, the order decides whether "x"
  is written before a crash. Within one `Program` step,
  divergence and reaching absurd code look possible only if erased proofs
  can be forged or §17's termination argument fails (unproved); across
  steps, an unbounded run is allowed (§42). No consistency theorem is
  expected (owner statement 1), so the spec must handle them. Cost also
  differs, which §42 allows between models and implementations.

Conjecture (needs proof, relies on §13 as a heap invariant): the set of
crash-free, stuck-free, terminating behaviours, meaning world traces and
final values up to renaming addresses, for given world answers and
quantified over `slot-eq` oracles, does not depend on evaluation order.

### 2.4 Implementations

- slc's interpreter runs post-erasure code: `Code` has `CErased` tokens
  (`self/core.sl:604-622`), and self/README.md calls it "a plain
  recursive interpreter over the post-erasure code". It is a big-step
  `eval` with a subterm `fuel` (`self/elab-main.sl:159`) that decreases
  per call nesting. MANUAL.md:154-166 describes `--eval-fuel` as a depth
  bound whose exhaustion "crashes with `out of fuel` (DESIGN.md section
  31)" and says "A run-position form whose evaluation crashes is
  refused".
- slc's store already models a heap whose blocks can be overwritten at
  a fixed address, with monotone addresses: `Store` keeps an erased
  allocation history plus a `writes` overlay (`self/heap.sl:64-69`).
  `store-write` returns a store whose overlay maps the same address to
  the new body, a functional update of a `many` map, not a physical one
  (`self/heap.sl:204-207`), and `store-read` prefers the overlay
  (`self/heap.sl:191-202`). A unique `cell-write` calls `hwrite` on the
  same address (`self/elab-main.sl:251-269`); a `many` one allocates a
  copy (`:271-288`).
- In slc every value is an address, immediates included: a `Nat` is a
  `BExt (PNat n)` block (`self/eval.sl:44-53`, `word-of-block`).
  `slot-eq` compares allocation positions (`self/eval.sl:804-809`), so
  two separately computed equal `Nat`s answer `ENone`. The reference
  interpreter uses OCaml `==` (`lib/eval.ml:61`).
- [compiled] `imm_eq.sl`: `slot-eq` of `(add 1 2)` and `3` answers
  `ENone` in the reference interpreter (with or without externs) and
  under `slc --interpret`, and `ESome` in the binary that either the
  reference or slc compiles (`--build`) with externs; under the
  reference's `--no-extern --build` it answers `ENone`. All are allowed
  by §67.
- `tests/slot_eq.sl` expects `ESome` (`1`) for a slot taken before an
  in-place `grow` and compared after it. The tests fix behaviour that
  §67 leaves free.
- mini/eval.sl is a pure, environment-based big-step relation `Eval`
  with no heap. As a relation it fixes no order: `EvApp` and `EvCall`
  just take a derivation for the head and an `EvalList` for the
  arguments (`mini/eval.sl:10-14`, `:28-29`). Its deriving function
  `eval` computes the head first, then the arguments left to right
  (`mini/eval.sl:60-74`, `:104-110`). Only that function takes fuel.

### 2.5 Externs and representation

[compiled] `tagslot.sl`: with `(def-fns ... (many id-at : (many (Four)
c) (many (Nat) n at c) -> ...) n)`, `(let ((many c)) (A3))`, and `(id-at
c 3)`:
- With externs it is accepted and prints `3`. The literal's slot is tag
  slot 3 (§35), so `n` is not passed: it is read back from `c`'s word.
- Under `--no-extern` it is refused ("does not satisfy `at`").

So static facts and acceptance depend on the extern mode, as DESIGN.md
says: §35 gives `(slot-of k)` = tag slot `k` only "with externs too",
and §33 refuses `coercible-tag` "under `--no-extern`". (reading) A spec
that ran the `Nat` model (a chain of `Succ` blocks) would have no single
"word of the `Nat` 3" for §33 to name unless it chose one, for example
the interned literal's block; DESIGN.md does not say, and I did not
check whether such a choice is consistent.

### 2.6 The prototype

`proto/dyn/machine.sl` (163 lines) is checked with the reference, with
and without `--no-extern`, and with `slc --interpret`, and prints `imm
1`, or `imm 0` with an all-false oracle. It has:
- `Word` (`WImm n | WPtr a`), with `a` a natural-number position in the
  heap list (`alloc` uses the heap's length, as in A2 below), compared
  only for equality; blocks overwritten at their position by a
  functional `set-nth`; and ANF code:
  variables, constructor allocation, `cell-alloc`, unique invocation
  (an in-place write), `slot-eq` reading an oracle bit, a closure, an
  application, `let`, and a field read.
- A total, non-recursive `step` (list helpers recurse structurally) over
  `Eval | Ret` configurations with a `FLet` continuation stack. Only `KLet`
  pushes a frame, so a call in tail position pushes none.
- A fuel-free run: each `Program` continuation performs one step
  (`drive`, `def-unique`), so the driver's loop (§42) is the only
  unbounded iteration.
- The oracle is a finite tape, and the run stops when the tape runs out,
  so as written the tape bounds the run as fuel would. A variant (made
  during review, not committed) in which `drive` takes the oracle as an
  `(Fn O (many (Nat) i) -> (many (Bool) b))` and a step counter, with no
  tape, also checks and prints `imm 1` [compiled], so the driver loop
  alone needs no bound. A like variant, with a fixed all-true oracle
  function and a step counter, is kept as
  `proto/review2/machine_fn_oracle.sl` and prints `imm 1`.

## 3. Options

### Q1. What the spec runs

- **R1 (recommended): post-erasure code, as DESIGN.md says.** The
  machine code is the output of elaboration: erased positions gone,
  `at` entries replaced by the renames the elaborator supplies (§36),
  skipped calls, skipped stores, at-matches, coerces, and placings as
  renames. Pros: matches §27 and §29, is close to what slc interprets
  (slc keeps `CErased` placeholders that evaluate to a token block), and
  no erased value needs a word. Cons: which calls are skipped is decided
  by the fact table ("skipped exactly when an opened `AtFn` proof names
  the callee's canonical atom", §39), so stripping is part of the
  elaboration spec's output, not a syntactic function of the source. A type-soundness
  theorem over stripped code needs a heap typing (cell slot contents,
  §13 uniqueness, `at` targets). SOUNDNESS.md argues safety in another
  way: in a "full semantics" in which "Every position runs, erased ones
  included" (part 3), with its (E) relating the stripped run to that one
  through (T) (part 7). A spec of R1 would take over that obligation or
  replace it by a direct proof over stripped code. Cost: the soundness
  proof is where most of the effort goes.
- **R2: full typed code, erased parts skipped by the machine.** The same
  machine, but it walks typed code and ignores erased nodes. Pros: one
  object for typing and running. Cons: just R1 with the strip inlined
  into every step; nothing gained.
- **R3: R1, but performing every skipped store and skipped call.**
  Pros: the run does not rely on `(at)` assertions being true. Cons:
  differs from §37 ("the store is skipped") and §39 ("Calling an
  at-function skips its runtime"); skipping is not part of §27's
  stripping of erased positions. Skipping is then a compiler
  optimization needing the heap invariant anyway.

### Q2. Machine state

Proposal (reading of §33, §35, §37, §41, §42, §66):
- Word = `Imm n` (n natural) | `Ptr a`, with `a` abstract (equality only,
  never reused).
- Block = constructor block (tag when tagged, the non-erased field
  words), closure block (code plus captured words), or a model block of
  an extern type.
- Heap = finite map from address to block, written in place.
- Configuration = code, environment of words, continuation stack, heap.
  The world is outside: a `world-do` step is a labelled event that the
  driver answers.

Values as words:

| value | word |
|---|---|
| tagged fieldless value at position k | `Imm k` |
| fieldless value of an untagged type not marked `extern` (hollow or not, §33: "however the value was built") | `Imm 0`, which is `vacant-slot` |
| a `Nat` | `Imm n` (Q6) |
| newtype, `Placed`, `share`, `coerce` result | the word of its field, value, or source |
| function (`def-fns` member) | `Ptr` to a closure |
| `delegate`-bodied function | its callee's word |
| at-function | `Ptr` to a no-op closure (§39: "a function that does nothing and returns no word") |
| absurd function | an unspecified word; §59: "the pointer is never followed" |
| unapplied constructor | a word for its constructor function (DESIGN.md does not say) |
| cell | `Ptr` to the block it will become; but at a tag slot's word when `C` has one or its type is hollow (§37), and at the scrutinee's word when bound by a destructure (§23) |
| slot | the word of its entry |
| `World`, `MacroWorld` | (reading) `Imm 0`, since each is taken `at vacant-slot` and "the driver passes it no word" (§42); their state is the driver's or the elaborator's, outside the heap |
| `Matchable` of a non-extern type | nothing (§29: "the FFI's wrapper for an `extern` type and nothing otherwise"); `Imm 0` is my choice |
| `Matchable` of an extern type | the FFI's wrapper (§29); under `--no-extern` DESIGN.md does not say |
| `Settled` handle | a block naming an entry; not compile-time only: "an `MMany` handle carries its value into an extracted program" (§64) |
| erased entries | no word |

- **A1 (recommended): this state, Proposal B's addresses plus `Imm n`.**
  Pros: (reading) every DESIGN.md requirement I found is met (2.1). §38's "Nothing
  relies on two slots being distinct" is consistent with addresses that
  are never reused, which a machine that never frees gives at no cost.
  GC reuse cannot be
  observed, since a slot word keeps its block alive (reading). Cons:
  equal immediates make `slot-eq` answer `ESome` across unrelated
  values; §67 allows that. Cost: low.
- **A2: natural-number addresses (slc's `ref-pos`).** Pros: concrete,
  as in slc today. Cons: a spec that exposed order or arithmetic would
  need a theorem that nothing uses it. Choosing A1 removes the question.
- **A3: everything boxed (slc's interpreter).** Pros: matches slc today.
  Cons: §33's identities (`vacant-slot` = `Nat` 0, tag slots) then hold
  only through a separate map from a block to its word, as slc's
  `word-of-block` does (`self/eval.sl:44-53`); `slot-eq` must then say
  whether it compares addresses (slc compares allocation positions) or
  words. slc so built does read `at` back through a tag slot:
  `slc --interpret tagslot.sl` prints `3` [compiled].

### Q3. Evaluation order

- **O1 (recommended): fix it.** Statements run in written order. Before
  a statement or final form, its §15 bindings run in order of
  appearance, inner before outer. Then the form itself runs: the head,
  then the arguments, which are variables by then, then `values`
  entries left to right, and a match's scrutinee before its branch.
  The spec is deterministic given the world's answers and the
  `slot-eq` oracle. Pros: no confluence proof, a total step function,
  and the compiler theorem is lock-step. Cons: compilers may not reorder
  without proof. The reference's `let ... and` for `values` meets it
  only through OCaml 4.14.1's observed, unpromised order. slc's emitter
  writes `order2.sl`'s `values` as nested `let ... in` in written
  order, and the head `(pick)` before the hoisted `(h n)`
  (`proto/review6/02_values_order_slc.sl`, slc's OCaml output read
  [compiled]). As stated, O1 puts the hoisted `(h n)` before the
  head `(pick)` in `((pick) (h n))`, which is the opposite of what the
  reference emits, of what every implementation tried does in the
  world-write tests (2.2), and of the run-position reading of §6 and
  §27; "a form head, then the §15 bindings" is the variant that matches
  all three. Needs DESIGN.md wording
  (rules 11, 12). Cost: low.
- **O2: fix only what DESIGN.md fixes; the spec is a relation over
  orders.** Pros: freedom for compilers. Cons: the compiler theorem
  needs order-independence (2.3), a diamond lemma over disjoint
  footprints. That rests on §13 as a heap invariant, which must itself
  be proved from the uniqueness rules (§15, §16, §22, §32, §34),
  including the inert slot words and `Stale` leftovers of §44. Cost:
  large, comparable to type soundness itself.
- **O3: O1 now, with order-independence stated as a later, optional
  theorem** that would license reordering compilers. Cost: O1's, plus
  O2's when wanted.

### Q4. `slot-eq` and other nondeterminism

- **N1 (recommended): oracle.** The spec run is a function of the
  program, the world's answers, and an oracle (step count → bit).
  `slot-eq` answers `ESome` only if the bit is set and the words are
  equal. Theorem: for each compiled run there is an oracle under which
  the spec run produces the same events and values. It covers the FFI
  `Slots` too (§69): an FFI answer is the model's linear search under
  some oracle, as long as the FFI says "found" only for an equal word
  (reading; not checked against the `Slots` models). The existence of
  an oracle also depends on E2 (Q6), or some other choice that makes
  equal `Nat`s one word: compiled code answers `ESome` for `(add 1 2)`
  against `3` (`imm_eq.sl`, 2.4), which a spec running the `Nat` model,
  with separately built `Succ` blocks, could not match (reading).
  Pros: deterministic, fits a `Program`-driven spec. Cons: the theorem
  is existential.
- **N2: relation.** `slot-eq` is a nondeterministic step, and the
  theorem is behaviour inclusion. Equivalent to N1 in strength; less
  natural in Sleight.
- **N3: always `ENone`.** Cons: `tests/slot_eq.sl` and the `Slots`
  implementations would disagree with the spec, so a compiler would have
  to answer `ENone` too. Not meaningful.
- **N4: truthful.** Cons: the reference interpreter and slc fail it
  (2.4). So does compiled code for big `Nat`s, which the extracted OCaml
  boxes as `Z.t` above `max_int`: [compiled]
  `proto/review5/02_big_nat_slot_eq.sl`, comparing two separately
  computed `Nat`s equal to 2^63, answers `ENone` when built by the
  reference or by slc, where the same program with small `Nat`s
  answers `ESome` when built by the reference.

### Q5. Crash

- **C1: CakeML-style.** The compiled behaviour equals the spec's, or is
  a prefix of it ending in a crash. Cost: low. Cons: a compiler that
  always crashes satisfies it.
- **C2 (recommended for runtime): crash only at named resource events.**
  Those are an allocation, a stack push, and an FFI primitive past its
  stated limit (`array-limit`, `bytes-limit`, the U62 host check of
  §42, §44). The trace is a prefix of the spec's, and the step at the
  crash is such an event. Also require that compiled code never aborts
  by itself except where the spec gets stuck (Q7). Cost: low to medium.
  Cons: any allocation may still crash.
- **C3: resource-indexed spec.** The spec takes a heap and depth bound
  (H, D) and crashes when live words exceed H or depth exceeds D.
  Theorem: on a host with at least c·H and c·D, compiled code does not
  crash where spec(H, D) does not. Pros: real teeth. Cons: needs a
  model of OCaml memory use; in practice an axiom per construct.
  Cost: high.
- **C4 (recommended for compile time): a deterministic bound.** The
  compile-time run is the spec machine with an explicit depth bound
  taken as compiler input, as `--eval-fuel` already is (MANUAL.md: the
  reference has no bound without the flag; slc's default is 1000000000).
  (reading) Accepting or rejecting would then be a function of (source,
  bound, flags, `read-file` oracle), once the order and the `slot-eq`
  answers are fixed (Q3, Q4),
  so owner statement 3 ("accepted or rejected") would hold per bound,
  provided the rest of elaboration terminates (SOUNDNESS.md part 6
  argues that canonicalization, unification, and meta solving do
  without (T), which it uses only for the runs; §62 bounds the
  expansions). A depth bound D bounds the steps of each run even
  without (T), by a count (reading; not machine-checked): there is no
  loop form and `let` does not recurse, so one activation evaluates each
  part of a body at most once and makes at most B calls, B the largest
  number of call sites in any body of the finite program; activations
  then form a tree of depth at most D and branching at most B. This
  needs D to count activations, a tail call included, as `--eval-fuel`
  does ("a tail call nesting inside the call it replaces", MANUAL.md).
  A bound on the depth of the continuation stack of Q2's machine would
  not do: there a tail call pushes no frame (2.6), so without (T) a
  self tail call could step forever at constant depth. The bound
  departs from §31's "unlimited stack and heap" for compile time and
  needs owner wording. A depth bound does not bound the heap, so a
  compile-time heap exhaustion stays host-dependent unless C3's heap
  bound is added. `native-compute` (§72) stays host-dependent: its
  answer is treated as an oracle, or excluded. Neither implementation
  is yet such a function of the bound in its message. Both can die of
  a host stack overflow before a large bound is spent: a run-position
  recursion 10^8 calls deep does so in both under
  `--eval-fuel 1000000000` (`proto/review7/02_deep_runpos.sl`). And
  slc's interpreter does not stop at an exhausted bound, since "out of
  fuel" is an error value and the code after it still runs
  (`self/elab-main.sl:185-187`, `CLet` at `:192-197`). Under
  `--eval-fuel 20`, `proto/review3/head_arg_order.sl`, whose head form
  alone exhausts the bound (`proto/review6/02_fuel_head_alone.sl`, the
  same with a small array, gives "out of fuel" on both), makes slc die
  of a stack overflow in its argument's run, where the reference stops
  with "out of fuel" [compiled]. That run is the final `main`'s, after
  elaboration. With the call in run position
  (`proto/review7/02_fuel_runpos.sl`), the reference refuses the file
  with "out of fuel", and slc again dies of the overflow, with no
  message naming the form [compiled]. 01 (decision 7)
  recommends the alternative: a spec machine that never crashes, and a
  third compiler outcome, `Crashed`.

### Q6. Externs

- **E1: run every model.** The FFI's agreement (§42) is a hypothesis per
  function. Cons: 2.5. DESIGN.md gives `(slot-of k)` = tag slot `k`
  only with externs. Either the spec elaborates without extern facts
  (then tagslot.sl is refused by the spec but accepted by the compiler),
  or it elaborates with them and runs the model, and must then choose a
  word for each tag slot (e.g. the interned literal's block), whose
  consistency is unchecked.
- **E2 (recommended): `Nat` is a machine primitive; all other models
  run.** `Nat` words are `Imm n` (unbounded in the abstract machine).
  Its extern operations are primitive steps whose results are proved, in
  the spec, equal to their models. The FFI agreement of the other
  externs (`String`, `Array`, `Bytes`, `Raw`, `Slots`, `Half`) is a
  hypothesis per function, with `slot-eq` under the oracle (N1). Pros:
  §33's "word of the `Nat` of its position" and §35's tag-slot literals
  get a meaning, and `ImmNat` is true in the spec. Cons: `Nat` is
  special in the spec.
- **E3: every extern primitive.** Cons: a large trusted base, and the
  models become documentation.

### Q7. Stuck states

Absurd code reached, or a malformed configuration.
- **S1 (recommended):** a defined `abort` outcome that compiled code must
  also produce. `self/runtime.ml:1` and `lib/eval.ml:66` already abort
  with "absurd code reached". A theorem that well-typed code never gets
  stuck except at `CAbsurd` is part of type soundness.
- **S2:** undefined behaviour after a stuck state. Cheaper, but
  promises nothing for programs whose erased proofs might be forged.

### Q8. Values computed at compile time, embedded in the output

- **V1:** agree as trees: the same constructors, ignoring sharing.
- **V2:** agree as heap graphs up to renaming addresses, so sharing is
  kept. self/README.md says slc keeps sharing ("Sharing is the
  store's").

I could not determine whether DESIGN.md needs V2 for correctness, and
not only for cost. Slot facts derived from a run-position `slot-eq`
(`ESome` gives `Eq (Slot) a b`) seem to need only equal *values* for
the `at` reading-back that follows, since both entries are `many`
(reading). Whatever the theorem compares, N1's "there is an oracle"
seems to need the spec itself to keep one block per `Settled` value: an
oracle can turn an `ESome` into `ENone` but not the reverse, and
`proto/review4/02_share_pair.sl`, a run-position `(MkPair _ _ a a)`
whose two fields a function compares with `slot-eq`, answers `ESome`
in the reference and slc, interpreted and built [compiled]. A spec
that stored `Settled` values as trees, copying `a` per field, could not
match it (reading). Recommendation: V1 for the theorem, V2 as an
option, with the spec's own store a heap (as 01's Σ is).

## 4. Decisions for the owner

1. **Does the spec run post-erasure code (R1)?** Recommended: yes. §27
   and §29 already say the evaluator runs stripped code at compile time,
   and §19, §36, and §39 describe runtime by post-erasure code, so this
   mostly confirms DESIGN.md; the open part is the formal spec's object
   and slc's `CErased` placeholders. (reading) A machine could give
   erased values placeholder words, as slc does, but §35 says "An erased
   variable has no word". Depends on it: the
   elaboration spec must output stripped code with its reading-back
   renames, and type soundness is stated over it.
2. **Machine state A1:** `Imm n | Ptr a` words, abstract, never-reused
   addresses compared only for equality, mutable blocks, explicit
   continuation, total step, `Program`-driven. Recommended: yes. (reading)
   It meets every requirement I found in §33, §35–§38, §41, and §66, and
   the driver loop needs no fuel (prototype, with the oracle as a
   function, 2.6). MINIMAL.md lists "Evaluation and typing are
   relations, not functions" under "Decided about the semantics" of the
   minimal language; a step function here would sit beside such a
   relation as its deriving function, as in mini/ (reading).
3. **Fix the evaluation order (O1/O3)?** Recommended: fix it in the
   spec. Sub-question: does §15's "behaves as if ... placed just before"
   fix timing? If so, it orders argument forms before a form head, which
   neither implementation does in the tests of 2.2 and which conflicts
   with a run-position reading of §6 and §27 (rough edge 10). Proposal A, applied after
   hoisting, is one candidate.
   This needs DESIGN.md wording. Leave order-independence as an
   optional later theorem. Depends on it: whether the compiler theorem
   is lock-step (cheap) or needs confluence (expensive).
4. **`slot-eq`: oracle (N1)?** Recommended: yes. It keeps the spec a
   function, and "there is an oracle" covers every implementation seen
   tonight, provided `Nat` words are immediates as E2 proposes (N1) and
   the spec's store shares `Settled` values (Q8).
5. **Crash: C2 at runtime, C4 at compile time?** Recommended: yes, with
   C3 as a later strengthening; 01's decision 7 is the alternative.
   The depth bound counts activations, tail calls included (C4).
   Depends on it: whether owner statement 3 can be stated per
   compile-time bound. Either way, `native-compute` needs its own
   clause.
6. **Externs: is `Nat` primitive (E2)?** Recommended: yes. Otherwise
   either the spec elaborates with `--no-extern` facts, and the compiler
   accepts programs (tagslot.sl) that the spec refuses, or the spec must
   choose a word for each tag slot under the `Nat` model (E1).
7. **Stuck: abort (S1)?** Recommended: yes. Compiled code already
   aborts. It gives the theorem content even though no consistency
   theorem is expected.
8. **Compile-time values: trees (V1) or graphs (V2)?** Recommended: V1
   for the theorem, V2 as an option, with the spec's own store a heap
   that keeps one block per `Settled` value, since N1's "there is an
   oracle" seems to need that (Q8, reading).

## 5. Rough edges in DESIGN.md (questions, not resolutions)

1. **Order of statements in a body at runtime.** Neither §27 nor §31
   says it. §27 says it only for run position ("This nests ...").
2. **The head and scrutinee in §15.** §15: "Every argument to a
   constructor, a function or a cell behaves as if it were first bound
   to an anonymous variable". §29: "the elaborator's own binders for its
   head, arguments and scrutinee (§15)". §15 says nothing of heads or
   scrutinees.
3. **Several hoisted bindings.** §15's "placed just before the statement
   or final form that contains the call" does not order several
   bindings placed before one statement.
4. **`Nat`'s word under models.** §33's "the word of the `Nat` of its
   position" presupposes that `Nat` k has one word. That holds for an
   immediate extern `Nat`, not obviously for the model's `Succ` blocks.
   §33 states the representation itself with no condition, and only the
   FFI's obligation to meet it "With externs on". §35's "with
   externs too, `(slot-of k)` is tag slot `k`" makes acceptance depend
   on the extern mode (tagslot.sl), apparently by design. So §42's
   "running the models instead of the implementations must give a
   program the same values" has nothing to compare for a program
   refused under the models.
5. **What a crash does to earlier effects.** §31's "A crash produces no
   value, never a different one" does not say what happens to effects
   already performed (the world trace), or where a crash may occur.
   MANUAL.md's "A run-position form whose evaluation crashes is
   refused", and §72's "a run that crashes is an error at its
   argument", make acceptance depend on the host.
6. **Reaching absurd code.** DESIGN.md does not say what happens when
   absurd code is reached at runtime. The reference interpreter
   (`lib/eval.ml:66`) and slc's OCaml runtime (`self/runtime.ml:1`)
   abort.
7. **What "the only reference" means.** §13's "the only reference to
   it" needs "reference" defined to exclude slot words (§38, "inert")
   and the `Stale` word an array keeps (§44: "Until it is put back, the
   array may keep the plucked value alive"). The reading-back of §36
   produces a reference from a consumed binder's word.
8. **"The same values" in §42.** It is not said whether values are
   compared as trees or with sharing (Q8).
9. **Tests fix free behaviour.** `tests/slot_eq.sl` expects `ESome`
   where §67 allows `ENone`. Not a contradiction, but the tests
   constrain implementations beyond the spec.
10. **§15's timing against §6 and §27.** If §15's "placed just before the
   statement or final form that contains the call" is read as timing, a
   call `((pick) (h n))` runs `(h n)` before the head `(pick)`. In run
   position, §6 ("The head is elaborated first") and §27 (a form "runs
   as soon as it has been elaborated") run `(pick)` first. The reference
   emits `(pick)` first, and both implementations run a head form first
   in the world-write tests (2.2).
11. **§61 presumes statement order.** §61's "The write stores `h` before
   the call" relies on a body statement running before a later one with
   no dataflow between them, which no general rule states (2.2 item 6).
12. **Elaboration order of a call's arguments.** §65 threads the macro
   world "sequentially through all of elaboration" and gensym numbers
   are observable, but DESIGN.md states only that the head is elaborated
   first (§6).

## 6. Unverified claims

- The order-independence conjecture (2.3) is unproved. So is the claim
  that §13's property, as a heap invariant, follows from the uniqueness
  rules.
- What OCaml versions other than 4.14.1 do with `let ... and`. The
  4.14 manual leaves it, and the order of application arguments,
  unspecified (checked, 2.2), and 4.14.1 was observed [compiled]:
  `let ... and` in written order, application arguments and tuples
  right to left.
- `lib/eval.ml:24` is `apply (eval1 env f) (List.map (eval1 env) args)`,
  and OCaml 4.14.1 evaluates application arguments right to left, so
  within one `CApp` the `List.map` runs first. This does not make the
  reference run arguments before a form head: the elaborator binds a
  head and argument that are not variables to anonymous entries in the
  order it elaborates them (`pending`, `lib/elab.ml:2268-2272`), so the
  `CApp` sees variables. [compiled] `proto/review3/head_arg_order.sl`,
  inside a function body, has a head form that recurses 50 deep and an
  argument form that crashes allocating a huge array: under
  `--eval-fuel 20` the reference reports "out of fuel", and without it
  the array crash, so the head runs first. slc's interpreter overflows
  its stack on that file either way, and since its "out of fuel" does
  not stop the run (C4), the overflow does not tell the two orders
  apart; nor does it on `proto/review3/00_arg_head_order.sl`, the same
  test with head and argument swapped. The world-write tests of 2.2 do
  tell them apart, and show the head form first in every
  implementation and mode tried; they cover one call shape each, not
  every call.
- That GC reuse of addresses is unobservable because a slot word keeps
  its block alive. This is a reading of OCaml's runtime, not checked.
- CakeML's top-level theorem allowing early termination on resource
  exhaustion, and its later space-cost work, are from memory.
- That V1 suffices for the soundness of slot facts derived at compile
  time (Q8).
- The first pass did not run slc. The second review ran
  `_build/release/slc` on every file under `proto/dyn/` and on
  `imm_eq.sl` under `--build`; the other claims about slc's internals
  are from reading its source.

## Review notes

Added by an adversarial review pass. Each item is an error found and the
change made above, then points left uncertain.

1. "A run on full code is not defined, because erased entries have no
   word (§35)" stated a cause DESIGN.md does not give. Now: DESIGN.md
   defines only a run on stripped code (§27, §29); §35's "An erased
   variable has no word" is quoted separately; slc's `CErased` evaluates
   to a token block (`self/elab-main.sl:173-176`).
2. "Proposal A conflicts with §15 [compiled]" was too strong, and a
   compile cannot establish what DESIGN.md says. Now conditional: it
   depends on whether §15's "behaves as if" fixes timing and whether A
   applies before or after hoisting. The extract shows the reference
   runs a form head before the hoisted argument, against a timing
   reading of §15.
3. "Head against arguments" was listed as unfixed. In run position §6
   ("The head is elaborated first") with §27 (a form "runs as soon as it
   has been elaborated") fixes head first (reading). Added; and noted
   that O1 as written puts the hoisted argument before the head, the
   opposite of the reference.
4. §61 was not cited. It presumes a body statement runs before a later
   one with no dataflow between them. Added as 2.2 item 6 and rough edge 11.
5. §15's "The order of the uses does not matter" was not mentioned;
   added to show §15 is about use-checking.
6. "Macro calls are elaborated in a fixed order" had no source. Replaced
   by what DESIGN.md states (§6 head first, §65 sequential threading);
   gensym numbers are observable via `intern-nat`. Rough edge 12.
7. Missed observer: the `Measure` request (`lib/prelude.sl:1386`) lets a
   program read time and GC counts. Added to 2.3 and the summary.
8. "Divergence ... possible only if erased proofs can be forged" ignored
   the unbounded driver loop (§42) and rests on §17's termination being
   sound. Now hedged and scoped to one step.
9. OCaml order was unverified. Compiled test: OCaml 4.14.1 (`ocamlopt`
   and `ocamlc`) evaluates `let ... and` in written order and
   application arguments and tuples right to left. The manual's
   "unspecified" stays from memory.
10. `self/elab-main.sl:174-176` was the wrong range for `CApp`; now
   178-182.
11. `store-write` does not update "in place"; it is a functional update
   of a `many` map at the same address.
12. mini/eval.sl: the relation fixes no order; only the deriving
   function computes head then arguments. Corrected with line cites.
13. Table: `Settled` handles are not compile-time only (§64: "an `MMany`
   handle carries its value into an extracted program"); a cell can be
   at a tag slot's word or a scrutinee's (§37, §23); §29's "nothing
   otherwise" is about non-extern types, not model mode. Fixed.
14. `imm_eq.sl`: compiled `ESome` holds only with externs; under
   `--no-extern --build` it answers `ENone` (re-run). Fixed.
15. Externs: §35 and §33 limit the tag-slot and `Nat`-word statements to
   "with externs" explicitly, so the mode dependence is DESIGN.md's own
   text, not a failure. E1 and decision 6 no longer claim the only
   alternative is refusal: a spec running the `Nat` model could choose a
   word per tag slot.
16. R3's conflict is with §37 and §39 (skipping), not §27 (stripping).
17. R1's "needs the elaborator's slot facts": §36 reads an `at` return's
   word from the binder the promise names; the fact-table dependence is
   §39's call skipping. Fixed.
18. Decision 2's "fuel-free (prototype)": the committed prototype's run
   is bounded by its 100-bit tape. A review variant with the oracle as a
   function and a step counter checked and printed `imm 1` (not
   committed). Fixed in 2.6 and decision 2.
19. C4 departs from §31's "unlimited stack and heap" at compile time and
   leaves heap exhaustion host-dependent; noted.

Re-run tonight: all five prototypes with and without `--no-extern`
(outputs as the file states; `tagslot.sl` refused under `--no-extern`
with "does not satisfy `at`"), `imm_eq.sl` under `--build` both ways,
and `--extract` of `order1.sl` and `order2.sl`.

Uncertain points:
- Whether §15's "behaves as if" is meant to fix timing; only the owner
  can say.
- Whether §61's ordering comes from written order or from §19's tail
  requirement.
- Whether choosing the interned literal's block as tag slot `k`'s word
  under the `Nat` model is consistent (E1).
- The summary is now longer than the brief's 15 lines.


## Second review notes

Added by a second, independent review. All five files under `proto/dyn/`
were rerun on the reference (with and without `--no-extern`) and on
`_build/release/slc --interpret`; `imm_eq.sl` under `--build` on both;
`order2.sl` under `--extract`; and the OCaml order test on 4.14.1. The
outputs quoted above reproduce. New tests are under `proto/review2/`.

1. 2.3's example `(f (world-do w (WriteOut "x")) (array-new _ huge))`
   could not be written: `world-do` takes its type first and returns two
   values (§42), and `array-new` three (§44), and an argument has size
   one (§27). Rewritten as two statements with no dataflow between
   them.
2. A3 claimed a boxed machine "loses §33's identities, so `at` reading
   back through a tag slot (2.5) has no meaning". slc's interpreter is
   boxed and runs `tagslot.sl`, printing `3`: it maps a block to its
   word (`word-of-block`, `self/eval.sl:43-52`). Restated as a cost,
   not an impossibility.
3. C4 said statement 3 "holds per bound". That needs the order and the
   `slot-eq` answers fixed and the rest of elaboration to terminate;
   hedged, with the reasoning that a depth bound seems to bound steps
   with no loop form (unproved). Decision 5 likewise.
4. C4 and decision 5 did not mention that 01's decision 7 recommends
   the opposite (a spec machine that never crashes, plus a `Crashed`
   compiler outcome). Cross-referenced.
5. slc was said not to have been run. `_build/release/slc` exists:
   `slc --interpret imm_eq.sl` answers `ENone` twice, and slc's
   `--build` binary answers `ESome` for the immediates, like the
   reference's. Summary, 2.4, and section 6 updated.
6. 2.2 item 3 rested head-first-in-run-position on §6's "The head is
   elaborated first" alone; §6 item 1 also says "A head that is a form
   is `Settled` in run position, since it runs as soon as it is
   elaborated", and §28 that each form there "runs as soon as it is
   elaborated". Quoted.
7. `Measure` also answers words allocated (`MkUsage`,
   `lib/prelude.sl:1331-1335`), not only time and GC counts. Added.
8. 2.6: "A call in tail position pushes no frame" was true but
   incomplete: no call pushes a frame; only `KLet` does. Reworded. The
   uncommitted fuel-free variant is now reproduced as
   `machine_fn_oracle.sl` (a fixed oracle function and a step counter),
   which prints `imm 1`.
9. "(§5 below)" in 2.2 read as DESIGN.md §5; now "rough edge 2 in
   section 5 below".
10. Rough edge 6's "Both implementations abort" had no citation; now
    `lib/eval.ml:66` and `self/runtime.ml:1`.
11. Oxford comma in R1.

During this review, a mistyped command (`main.exe --build imm_eq.sl`,
which takes `imm_eq.sl` as the output name) overwrote
`proto/dyn/imm_eq.sl` with a binary. It was restored from git HEAD,
whose text matches the file as printed just before.

Unsure, not changed:
- N1's "there is an oracle" holds only if a compiled `ESome` never
  meets two words the abstract machine keeps apart; a host that shared
  equal constant blocks would break it. `const_share.sl` (two
  run-position `(MkBox 5)`) answers `ENone` in the reference and slc,
  built and interpreted, so no such sharing was seen.
- The summary is still longer than the brief's 15 lines.

## Third review notes

Added by a third, independent review. All five files under `proto/dyn/`
were rerun on the reference (with and without `--no-extern`) and on
`_build/release/slc --interpret`; `imm_eq.sl` under `--build` on both,
and under the reference's `--no-extern --build`; `order1.sl` and
`order2.sl` under `--extract`; the OCaml order test on 4.14.1; and
`machine.sl` with an all-false tape and with a 3-bit tape (the latter
prints nothing, confirming that the tape bounds the run). The outputs
quoted above reproduce. New tests are under `proto/review3/`.

1. Section 6 listed "the reference interpreter evaluates arguments
   before the head" as a plausible unverified claim. Observably it does
   not: the elaborator binds a non-variable head and arguments to
   anonymous entries in elaboration order (`lib/elab.ml:2268-2272`), so
   `CApp` sees variables. `review3/head_arg_order.sl` (a head form 50
   calls deep, an argument that crashes allocating) gives "out of fuel"
   under `--eval-fuel 20`, so the head runs first. Rewritten.
2. C4 said SOUNDNESS.md part 6 argues the rest of elaboration
   terminates "from (T)"; part 6 uses (T) only for the runs. Fixed. C4
   also left "a depth bound seems to bound the steps of each run" as
   unproved; a short count (no loop form, branching at most the largest
   number of call sites in a body, depth at most D) gives it. Added,
   marked as reading.
3. The summary counted cost among the observers of order, while 2.3
   says `Measure` is absorbed once the world's answers are inputs.
   Aligned with 2.3.
4. The summary said a spec running the `Nat` model "must still choose a
   word for each tag slot"; E1 gives the alternative of dropping the
   extern-only facts. Fixed.
5. 2.6 described the prototype's words as if its addresses were
   abstract; `alloc` uses the heap list's length, so they are natural
   numbers (A2), compared only for equality, and a block is replaced by
   a functional `set-nth`. Stated.
6. A3 cited `self/eval.sl:43-52` (from the second review) while 2.4
   cited `:44-53`; `word-of-block` is at 44-53. Fixed in A3 (second
   review note 2 keeps the old range as history).
7. 2.4's ranges for slc's cell write and copy were off by up to three
   lines; now `self/elab-main.sl:251-269` and `:271-288`.
8. R1 did not mention SOUNDNESS.md's route, a "full semantics" in which
   erased positions run (part 3) with (E) relating the stripped run to
   it through (T) (part 7). Added to R1's cons.
9. Decision 2 recommends a total step function without noting that
   MINIMAL.md lists "Evaluation and typing are relations, not
   functions" under "Decided about the semantics". Noted, with mini/'s
   relation-plus-deriving-function pairing as the reading.
10. The summary named only slc's erased placeholder; the reference's
    `CErased` evaluates to `VToken` (`lib/eval.ml:22`). Added.
11. 2.3 now records the tested elaboration order of macro calls among
    arguments (01, §3.6).
12. Oxford commas in the summary, 2.2 item 3, 2.3, 2.5, and decision 1.

Unsure, not changed:
- slc's runtime order of a head form against an argument form was not
  observed: `slc --interpret` overflows its stack on
  `head_arg_order.sl` whatever the depth.
- The OCaml manual's wording on the order of `let ... and` is still from
  memory.
- The summary is still longer than the brief's 15 lines.

## Fourth review notes

Added by a fourth, independent review. All five files under `proto/dyn/`
were rerun on the reference (with and without `--no-extern`) and on
`_build/release/slc --interpret`; `imm_eq.sl` under `--build` on both
and under the reference's `--no-extern --build`; `order1.sl` and
`order2.sl` under `--extract`; `machine.sl` with an all-false tape;
`review2/machine_fn_oracle.sl`, `review2/const_share.sl` and
`review3/head_arg_order.sl`; and the OCaml order test on 4.14.1. The
outputs quoted reproduce. New tests are `proto/review4/02_*.sl` (and
01's `review4/01_head_name_err.sl`, cited in 2.3).

1. C4's count ("activations then form a tree of depth at most D") holds
   only if D counts activations, tail calls included, as `--eval-fuel`
   does (MANUAL.md: "a tail call nesting inside the call it replaces").
   The machine proposed in Q2 and 2.6 pushes no frame for a tail call,
   so a bound on its stack depth would not bound the steps without (T),
   which C4 claims to do without. Stated in C4 and decision 5.
2. C4 said acceptance would be a function of "(source, bound)"; the
   flags and the `read-file` oracle are inputs too (01, §3.4). Added.
3. The OCaml manual's wording was "from memory" in 2.2 and section 6.
   Checked against ocaml.org/manual/4.14/expr.html: `let ... and`
   "evaluates expr1 … exprn in some unspecified order", and the order of
   an application's head and arguments "is not specified". Quoted; the
   section 6 item now covers only other OCaml versions.
4. The summary said `slot-eq` is nondeterministic "in practice too";
   what was observed is variation between implementations and modes,
   not between runs. Reworded.
5. Q2's table gave `Imm 0` for an "untagged hollow value"; §33 gives
   `vacant-slot`'s word to every value with no non-erased field of an
   untagged type not marked `extern`, "however the value was built",
   which is wider than hollow types. Fixed.
6. Q8 did not note that N1's existence claim needs the spec's own store
   to share `Settled` values: `review4/02_share_pair.sl` (a run-position
   pair of one box, its fields compared by `slot-eq` in a function)
   answers `ESome` in the reference and slc, interpreted and built, and
   an oracle can only turn `ESome` into `ENone`. Added, as reading.
7. A1 said never-reused addresses are something "memory safety needs
   anyway"; it does not (reuse after a free can be safe). Reworded.
8. Decision 5's "Depends on it: whether … and `native-compute` needs
   its own clause" read as one dependency; split.

Unsure, not changed:
- Whether C4's tree count also needs care for a function value stored
  in data and called through it (each call site is still in some body,
  so B seems to cover it).
- slc's runtime order of a head form against an argument form is still
  unobserved (its interpreter overflows on `head_arg_order.sl`).
- The summary is still longer than the brief's 15 lines.

## Coordinator note

1. Decision 8 still read "V1 unless a reason for V2 turns up", which
   disagreed with Q8 as corrected by fourth review note 6. Restated to
   match Q8. Flagged by the fourth-round propagation check of
   00-summary.

## Fifth review notes

Added by a fifth, independent review. All five files under `proto/dyn/`
were rerun on the reference (with and without `--no-extern`) and on
`_build/release/slc --interpret`; `imm_eq.sl` under `--build` on both
and under the reference's `--no-extern --build`; `order1.sl` and
`order2.sl` under `--extract`; `machine.sl` with an all-false tape;
`review2/machine_fn_oracle.sl`, `review2/const_share.sl`,
`review3/head_arg_order.sl`, and `review4/02_share_pair.sl` (interpreted
and built, both implementations); and the OCaml order test on 4.14.1.
The OCaml 4.14 manual's three quoted sentences were checked against
ocaml.org/manual/4.14/expr.html. The outputs and quotes reproduce, and
the code citations were reopened. The new test is
`proto/review5/02_big_nat_slot_eq.sl`.

1. N1 and decision 4 said "there is an oracle" covers every
   implementation seen, without saying that this needs `Nat` words to
   be immediates (E2): built code answers `ESome` for `(add 1 2)`
   against `3` (`imm_eq.sl`), which a spec running the `Nat` model
   could not reproduce, since an oracle only turns `ESome` into
   `ENone`. Decision 4 also now names Q8's sharing condition. Added, as
   reading.
2. N4's claim about the host's big `Nat`s was a reading of the
   interpreter's `VWord`, not a test. `review5/02_big_nat_slot_eq.sl`
   compares two separately computed `Nat`s equal to 2^63: built by the
   reference or by slc it answers `ENone`; the same program with `Nat`s
   equal to 6 answers `ESome` when built by the reference. Now
   [compiled].
3. The [compiled] tag's description named only the reference and
   `proto/dyn/`, while several [compiled] claims use slc, OCaml, or
   `proto/review*/` files. Fixed.

Unsure, not changed:
- C4's count bounds the steps of Sleight code; under E2 a primitive
  step on a huge `Nat`, or an FFI primitive of another extern if the
  spec ever runs one, is one step whatever its host cost. That seems
  intended by the abstract machine, but it means the bound says nothing
  about host time.
- The summary is still longer than the brief's 15 lines.

## Round 6 review notes

Added by a sixth, independent review. All five files under `proto/dyn/`
were rerun on the reference (with and without `--no-extern`) and on
`_build/release/slc --interpret`; `imm_eq.sl`,
`review5/02_big_nat_slot_eq.sl` (and a copy with small `Nat`s), and
`review4/02_share_pair.sl` built by both; `order1.sl` and `order2.sl`
under `--extract`; `review2/machine_fn_oracle.sl`,
`review2/const_share.sl`, and `review3/head_arg_order.sl`; the OCaml
order test on 4.14.1; and the two OCaml manual sentences against
ocaml.org/manual/4.14/expr.html. The outputs and quotes reproduce, and
the code citations hold. New tests are `proto/review6/02_*.sl`.

1. Rough edge 4 said "§33 states the requirement only 'With externs
   on'". §33 states the representation (a fieldless value is "the word
   of the `Nat` of its position", `vacant-slot`'s word "that of `Nat`
   0") unconditionally; only the FFI's obligation is "With externs on".
   Fixed.
2. 2.3 called `native-compute` results "fieldless constructors". §72
   requires only that no non-phantom constructor has a non-erased
   field, and says "its erased fields take the tokens of §5". Fixed.
3. O1 said slc's emitter "would need checking". It was checked:
   `02_values_order_slc.sl` (`order2.sl` with a final function) makes
   slc emit the `values` as nested `let ... in` in written order, and
   the head `(pick)` before the hoisted `(h n)`. Fixed.
4. C4 recommends compile-time exhaustion as a deterministic function of
   a bound without noting that slc's interpreter does not stop at an
   exhausted bound: "out of fuel" is an error value and the code after
   it runs (`self/elab-main.sl:185-187`, `:192-197`). On
   `head_arg_order.sl` under `--eval-fuel 20`, whose head alone
   exhausts the bound (`02_fuel_head_alone.sl`), slc reports a stack
   overflow from the argument and the reference "out of fuel". Added.
5. Section 6 said slc's overflow on `head_arg_order.sl` "says nothing"
   without saying why; item 4 is the reason, and it applies equally to
   `review3/00_arg_head_order.sl`. Added. For the coordinator:
   00-summary (finding on runtime order) cites
   `00_arg_head_order.sl` for slc's interpreter running a head form
   first, which for this reason that test cannot show; this review's
   attempts to show it through `--eval-fuel` failed the same way.

Unsure, not changed:
- Whether slc's out-of-fuel-as-value is a bug against MANUAL.md's
  "crashes with `out of fuel`" or intended; not raised in BUGS.md here.
- slc's interpreter's order of a head form against an argument form
  remains unobserved.
- The summary is still longer than the brief's 15 lines.

## Round 7 coordinator notes

1. The Round 6 notes left slc's interpreter's order of a head form
   against an argument form unobserved. `proto/dyn/head_crash_arg_write.sl`
   and `proto/dyn/head_write_arg_crash.sl` observe it with a world write
   on one side and a stack overflow on the other; unlike "out of fuel",
   a stack overflow ends a run of slc's interpreter (`proto/dyn/crash_probe.sl`
   prints "before" and not "after"). Both show the head form first
   under the reference (interpreted and `--build`), `slc --interpret`,
   and slc's native and `--byte` builds; their controls, with the
   overflow made harmless, print the write and exit 0. Added to 2.2
   and section 6.
