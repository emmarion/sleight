# 02 — The spec's run: dynamic semantics as a heap machine

Written overnight by an agent exploring options for the owner. Everything
here is a proposal or a reading. Nothing in it is approved, and nothing
in it is the owner's decision unless it says so and cites the brief's
list of owner statements.

Sources are marked: **§n** quotes DESIGN.md; **file:line** is code;
**[compiled]** is a test run tonight with the reference
(`_build/default/bin/main.exe`), files under
`proposals/self-formal/proto/dyn/`; **(reading)** is my inference.

## 1. Summary

- DESIGN.md already places its compile-time run on stripped code: a
  run-position form "is elaborated, its erased positions are stripped,
  the evaluator runs the code" (§27), and §19, §36 and §39 speak of the
  post-erasure code at runtime. DESIGN.md defines no run on unstripped
  code; §35 says "An erased variable has no word". (reading) So a heap
  machine would run stripped code, and the stripped-mode concern (which
  owner statement 6 says goes away with a mutable heap) becomes a
  type-soundness obligation over stripped code with a heap typing. (slc's
  interpreter does give an erased position a placeholder: `CErased`
  evaluates to a `BToken` block, `self/elab-main.sl:173-176`.)
- Proposal: a small-step machine whose words are `Imm n | Ptr a`, with
  `a` an abstract address that can only be compared. Blocks are mutable.
  The step function is total, and an explicit continuation stack holds
  the rest of the run. Proposal B's abstract addresses are enough, once
  immediates and the representation identities of §33, §35 and §41 are
  added. A prototype (`proto/dyn/machine.sl`) compiles and runs a total
  step looped by the `Program` driver with no fuel.
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
  observable only through crashes, stuck states, divergence, and cost
  (which a program can itself read through the `Measure` request): world
  effects are
  totally ordered by the unique `World`, and mutation goes only through
  unique references. Recommendation: fix one order in the spec (no
  confluence proof needed), and leave order-independence as an optional
  later theorem.
- `slot-eq` is nondeterministic by §67, and in practice too: the
  reference interpreter answers `ENone` where compiled code with externs
  answers `ESome` [compiled]; under `--no-extern` the compiled code also
  answers `ENone`. Recommendation: make the spec a deterministic
  function of the program, the world's answers, and an oracle tape of
  `slot-eq` bits; the compiler theorem says some oracle exists.
- Crash: "agrees or crashes" has no teeth. Recommendation: allow a crash
  only at named resource events, and make compile-time crash a
  deterministic function of an explicit depth bound.
- Externs: §35 gives literal tag slots only "with externs", and §33's
  extern-`Nat` requirement is stated only "With externs on", so acceptance
  depends on the extern mode by DESIGN.md's own text [compiled]. A spec
  that runs the `Nat` model must still choose a word for each tag slot.
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
   statements are sequential"). (reading) With §6 item 1, "The head is
   elaborated first", a head that is a form runs, in run position, before
   the argument forms are elaborated, so before they run.
4. Skipped calls and at-matches still evaluate their arguments and
   scrutinee (§39, §40).
5. (reading) World requests are totally ordered by dataflow: `world-do`
   takes `(unique (World) w ...)` and gives back `w2` (§42), so only one
   world is ever usable. `MacroWorld` is threaded the same way (§65).

5b. §61 presumes an order of body statements in one case: "The write
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
  (§5 below).
- The order of the entries of a `values`, and of the stores of one
  invocation.

[compiled, `--extract`] `order2.sl`: in `(values (g (h n)) (h (g n)))`
the reference emits `(h n)`, then `(g n)`, and then the two outer calls
as OCaml `let x = g .. and y = h .. in`. The OCaml manual leaves the
order of `let ... and` unspecified (from memory; not checked against the
manual tonight); OCaml 4.14.1, as installed, evaluates it in written
order, both `ocamlopt` and `ocamlc` [compiled], while it evaluates
application arguments and tuple components right to left. In
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
- Compile time: within one macro run, `gensym`, `read-file` and the
  other §65 primitives are ordered by the unique `MacroWorld`. Which
  number a given `gensym` call gets also depends on the order in which
  the elaborator reaches macro calls. §65 threads the world "sequentially
  through all of elaboration", and §6 elaborates the head first, but I
  found no statement of the order in which a call's arguments are
  elaborated. A gensym number can reach the output (`intern-nat`, §65),
  so elaboration order is observable; that is a question about the
  elaboration spec, separate from runtime evaluation order.
  `native-compute` results are fieldless constructors (§72), so sharing
  plays no part.
- `Measure` (`lib/prelude.sl:1386`) answers wall and CPU time and GC
  counts "since the Program began", so a program can observe cost, and
  through it the order of work between two requests. In a spec where the
  world's answers are inputs, this is absorbed by quantifying over
  answers, not by order-independence.
- Not covered: crashes, stuck states, and divergence. In `(f
  (world-do w (WriteOut "x")) (array-new _ huge))`, the order decides
  whether "x" is written before a crash. Within one `Program` step,
  divergence and reaching absurd code look possible only if erased proofs
  can be forged or §17's termination argument fails (unproved); across
  steps, an unbounded run is allowed (§42). No consistency theorem is
  expected (owner statement 1), so the spec must handle them. Cost also
  differs, which §42 allows between models and implementations.

Conjecture (needs proof, relies on §13 as a heap invariant): the set of
crash-free, stuck-free behaviours, meaning world traces and final values
up to renaming addresses, does not depend on evaluation order.

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
  same address (`self/elab-main.sl:251-266`); a `many` one allocates a
  copy (`:270-287`).
- In slc every value is an address, immediates included: a `Nat` is a
  `BExt (PNat n)` block (`self/eval.sl:44-53`, `word-of-block`).
  `slot-eq` compares allocation positions (`self/eval.sl:804-809`), so
  two separately computed equal `Nat`s answer `ENone`. The reference
  interpreter uses OCaml `==` (`lib/eval.ml:61`).
- [compiled] `imm_eq.sl`: `slot-eq` of `(add 1 2)` and `3` answers
  `ENone` in the reference interpreter (with or without externs) and
  `ESome` in the compiled binary (`--build`) with externs; under
  `--no-extern --build` it answers `ENone`. All are allowed by §67.
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
c) (many (Nat) n at c) -> ...) n)`, `(let ((many c)) (A3))` and `(id-at
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
and without `--no-extern`, and prints `imm 1`, or `imm 0` with an
all-false oracle. It has:
- `Word` (`WImm n | WPtr a`), mutable `Block`s in a heap, and ANF code:
  variables, constructor allocation, `cell-alloc`, unique invocation
  (an in-place write), `slot-eq` reading an oracle bit, a closure, an
  application, `let`, and a field read.
- A total, non-recursive `step` (list helpers recurse structurally) over
  `Eval | Ret` configurations with a `FLet` continuation stack. A call
  in tail position pushes no frame.
- A fuel-free run: each `Program` continuation performs one step
  (`drive`, `def-unique`), so the driver's loop (§42) is the only
  unbounded iteration.
- The oracle is a finite tape, and the run stops when the tape runs out,
  so as written the tape bounds the run as fuel would. A variant (made
  during review, not committed) in which `drive` takes the oracle as an
  `(Fn O (many (Nat) i) -> (many (Bool) b))` and a step counter, with no
  tape, also checks and prints `imm 1` [compiled], so the driver loop
  alone needs no bound.

## 3. Options

### Q1. What the spec runs

- **R1 (recommended): post-erasure code, as DESIGN.md says.** The
  machine code is the output of elaboration: erased positions gone,
  `at` entries replaced by the renames the elaborator supplies (§36),
  skipped calls, skipped stores, at-matches, coerces and placings as
  renames. Pros: matches §27 and §29, is close to what slc interprets
  (slc keeps `CErased` placeholders that evaluate to a token block), and
  no erased value needs a word. Cons: which calls are skipped is decided
  by the fact table ("skipped exactly when an opened `AtFn` proof names
  the callee's canonical atom", §39), so stripping is part of the
  elaboration spec's output, not a syntactic function of the source. A type-soundness
  theorem over stripped code needs a heap typing (cell slot contents,
  §13 uniqueness, `at` targets). Cost: the soundness proof is where most
  of the effort goes.
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
| untagged hollow value | `Imm 0`, which is `vacant-slot` |
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
  are never reused, which memory safety needs anyway. GC reuse cannot be
  observed, since a slot word keeps its block alive (reading). Cons:
  equal immediates make `slot-eq` answer `ESome` across unrelated
  values; §67 allows that. Cost: low.
- **A2: natural-number addresses (slc's `ref-pos`).** Pros: concrete,
  as in slc today. Cons: a spec that exposed order or arithmetic would
  need a theorem that nothing uses it. Choosing A1 removes the question.
- **A3: everything boxed (slc's interpreter).** Pros: matches slc today.
  Cons: loses §33's identities (`vacant-slot` = `Nat` 0, tag slots), so
  `at` reading back through a tag slot (2.5) has no meaning.

### Q3. Evaluation order

- **O1 (recommended): fix it.** Statements run in written order. Before
  a statement or final form, its §15 bindings run in order of
  appearance, inner before outer. Then the form itself runs: the head,
  then the arguments, which are variables by then, then `values`
  entries left to right, and a match's scrutinee before its branch.
  The spec is deterministic given the world's answers and the
  `slot-eq` oracle. Pros: no confluence proof, a total step function,
  and the compiler theorem is lock-step. Cons: compilers may not reorder
  without proof. The reference's `let ... and` for `values` would not
  meet it; slc's emitter would need checking. Needs DESIGN.md wording
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
  some oracle, as long as the FFI says "found" only for an equal word.
  Pros: deterministic, fits a `Program`-driven spec. Cons: the theorem
  is existential.
- **N2: relation.** `slot-eq` is a nondeterministic step, and the
  theorem is behaviour inclusion. Equivalent to N1 in strength; less
  natural in Sleight.
- **N3: always `ENone`.** Cons: `tests/slot_eq.sl` and the `Slots`
  implementations would disagree with the spec, so a compiler would have
  to answer `ENone` too. Not meaningful.
- **N4: truthful.** Cons: the reference interpreter and slc fail it
  (2.4). The host's boxed big `Nat`s fail it too, which is my reading of
  `VWord` with `Z`.

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
  taken as compiler input, as `--eval-fuel` already is. Accepting or
  rejecting is then a function of (source, bound), so owner statement 3
  ("accepted or rejected") holds per bound. `native-compute` (§72)
  stays host-dependent: its answer is treated as an oracle, or excluded.

### Q6. Externs

- **E1: run every model.** The FFI's agreement (§42) is a hypothesis per
  function. Cons: 2.5. Under the `Nat` model, `(slot-of k)` = tag slot
  k is false, so programs accepted with externs have no meaning in the
  spec, unless the spec also elaborates without extern facts (then
  tagslot.sl is refused by the spec but accepted by the compiler).
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
(reading). Recommendation: V1 for the theorem, V2 as an option.

## 4. Decisions for the owner

1. **Does the spec run post-erasure code (R1)?** Recommended: yes. §27
   and §29 already say the evaluator runs stripped code, and a heap
   machine cannot run erased code (§35: no word). Depends on it: the
   elaboration spec must output stripped code with its reading-back
   renames, and type soundness is stated over it.
2. **Machine state A1:** `Imm n | Ptr a` words, abstract, never-reused
   addresses compared only for equality, mutable blocks, explicit
   continuation, total step, `Program`-driven. Recommended: yes. It meets
   every requirement found in §33, §35–§38, §41, and §66, and it is
   fuel-free (prototype).
3. **Fix the evaluation order (O1/O3)?** Recommended: fix it in the
   spec, in an order consistent with §15's hoisting (not Proposal A).
   This needs DESIGN.md wording. Leave order-independence as an
   optional later theorem. Depends on it: whether the compiler theorem
   is lock-step (cheap) or needs confluence (expensive).
4. **`slot-eq`: oracle (N1)?** Recommended: yes. It keeps the spec a
   function, and "there is an oracle" covers every implementation seen
   tonight.
5. **Crash: C2 at runtime, C4 at compile time?** Recommended: yes, with
   C3 as a later strengthening. Depends on it: owner statement 3 holds
   per compile-time bound, and `native-compute` needs its own clause.
6. **Externs: is `Nat` primitive (E2)?** Recommended: yes. Otherwise the
   spec must elaborate with `--no-extern` facts, and the compiler would
   accept programs (tagslot.sl) that the spec refuses.
7. **Stuck: abort (S1)?** Recommended: yes. Compiled code already
   aborts. It gives the theorem content even though no consistency
   theorem is expected.
8. **Compile-time values: trees (V1) or graphs (V2)?** Recommended: V1
   unless a reason for V2 turns up.

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
   immediate extern `Nat`, not for the model's `Succ` blocks. §35's
   "with externs too, `(slot-of k)` is tag slot `k`" makes acceptance
   depend on the extern mode (tagslot.sl). So §42's "running the models
   instead of the implementations must give a program the same values"
   cannot be applied to such a program as written.
5. **What a crash does to earlier effects.** §31's "A crash produces no
   value, never a different one" does not say what happens to effects
   already performed (the world trace), or where a crash may occur.
   MANUAL.md's "A run-position form whose evaluation crashes is
   refused", and §72's "a run that crashes is an error at its
   argument", make acceptance depend on the host.
6. **Reaching absurd code.** DESIGN.md does not say what happens when
   absurd code is reached at runtime. Both implementations abort.
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

## 6. Unverified claims

- The order-independence conjecture (2.3) is unproved. So is the claim
  that §13's property, as a heap invariant, follows from the uniqueness
  rules.
- That OCaml leaves the order of `let ... and` and of application
  arguments unspecified (from memory of the OCaml manual; I did not
  check it tonight).
- That the reference interpreter evaluates arguments before the head
  (`lib/eval.ml` relies on OCaml's order, which I did not check).
- That GC reuse of addresses is unobservable because a slot word keeps
  its block alive. This is a reading of OCaml's runtime, not checked.
- CakeML's top-level theorem allowing early termination on resource
  exhaustion, and its later space-cost work, are from memory.
- That V1 suffices for the soundness of slot facts derived at compile
  time (Q8).
- I did not build or run slc (`_build/self/slc` is absent). The claims
  about slc are from reading its source.
