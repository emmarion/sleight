# 06. Spike: a certified, fuel-free stepper for a heap language

Written overnight by a Claude agent as a proof-technique spike. It is a
proposal and an agent's reading; nothing in it is approved or decided.
Where it and DESIGN.md disagree, DESIGN.md is right.

Sources are marked: **§n** quotes DESIGN.md; **file:line** is code;
**[ran]** is a run tonight of the reference (`_build/default/bin/main.exe`,
commit d6644d9; the first review re-ran everything at ad07c35, the
second at 07692f2, the third at c236135, the fourth at e0aaf2c, the
fifth at fb2c533, the sixth at 10bd85d, and the seventh at 13ca61f,
with no change to `bin/`, `lib/`, `src/`, `self/`, or `std/` in
between) and, where said, of `_build/release/slc`. The
prototype is `proto/stepper/`. Every command line starts with the
repository's `std/list.sl`, then `spec.sl machine.sl`.

## 1. Summary

- A tiny language (registers, a heap of mutable blocks with allocate,
  read, and write-in-place, `if`, and `while`) has a big-step spec `Runs m c
  m2` (`spec.sl`). A total, non-recursive `step` over an explicit command
  stack and memory, driven one `Program` continuation per step, runs it
  with no fuel. The reference accepts `run.sl` and
  `complete.sl total_demo.sl` and runs them [ran]; so do `--no-extern`,
  `--build`, `slc --interpret`, and `slc --build` [ran].
- The theorem is the type of `advance`: its `Halted` result carries
  `(erased (Runs m0 c0 mf) d)`, for the `c0` and `m0` that the erased
  trace argument starts from, so a run started with `TNil` gets it for
  the original program and memory. This is partial correctness only. The
  spec is deterministic (`runs-fn`).
  Conversely, `Runs` implies a finite small-step run (`runs-star`), the
  small step is deterministic (`step-det`), and so `run-total` takes a
  `Runs m0 c0 mf` and returns the machine's result, proved equal to
  `mf`, or "stuck" (`complete.sl`). "Stuck" carries no evidence, so a
  `step` that always answered `SStuck` would pass every type here;
  nothing yet proves the machine is ever not stuck.
- The invariant built is first order: an erased trace of the steps
  taken, folded back at the halt by a non-recursive per-step lemma
  (`step-back`) over the spec lifted to stacks. A closure invariant
  ("the rest composed with the current focus gives the spec's run") also
  works at one fixed level if it takes an erased step counter, which
  each extension's call to the previous closure decreases
  (`ho_counter.sl`, added in review) [ran]. Without that counter it is
  refused at a fixed level. With its level packed in the state it can be
  built, but a stepper that extends it at a fresh level each step cannot
  apply it (§18); with a `Predates` to the stepper's level packed too, it
  can be applied but not extended at a fresh level [ran].
  Packing the level with its `Predates` proofs and the counter, and
  extending at that same packed level, is accepted
  (`proto/review4/06_packed_counter.sl`) [ran, fourth review].
- Missing: refuting "stuck" when a `Runs` derivation exists (that `step`
  finds every step `Step` allows), an in-place (unique) heap in the
  implementation, and abstract addresses. Determinism, the soundness
  glue, the result types, and `complete.sl` come to about 210 lines
  (`complete.sl`'s 52 include `finish` and `run-total`, which are code),
  against 90 lines of stepper code and 67 lines of spec (F5). Checking
  all of it adds about 0.1 s to the prelude's 0.3–0.4 s [ran].

## 2. Findings

### F1. The language and its spec (`spec.sl`)

`Val` is `VNum n | VPtr a`; `Mem` is `MkMem env heap`, registers as a
`(List (Val))` and the heap as a `(List (List (Val)))`, an address being
a position. `Op` has `OSet`, `OMov`, `OPred`, `OAdd`, `OAlloc`, `ORead`,
and `OWrite`; `Cmd` has `CSkip`, `COp`, `CSeq`, `CIf` (zero test), and
`CWhile`. The atomic semantics `RunOp m o m2` is stated with the
prelude's `Nth`, `SetNth`, `Repeat`, and `Add` (`lib/prelude.sl:1281-1302`,
`:33-36`) and one new relation, `Alloc` (append at the end, address =
old length). A write is `SetNth` on the block, then `SetNth` on the heap
at the same address, so an alias sees it: `run.sl` writes `100` through
register 5 (a copy of register 1, the list's head pointer), then copies
register 1 to register 2 and sums the list through register 2 [ran:
`114`].

`Runs` has five rules (`spec.sl:69-78`). `CIf` goes through a relation
`Pick m x c1 c2 c`, and `CWhile` unfolds: `ExWhile` derives `Runs m
(CWhile x b) m2` from `Runs m (CIf x (CSkip) (CSeq b (CWhile x b))) m2`.
Every premise of a rule is a field of the derivation, so all inductions
below are plain `subterm` recursion on derivations (§21: "Subterm
recursion (§17) may go through an erased field."), not on commands:
`ExWhile`'s premise is about a larger command. This holds for any rule
set whose premises are plain fields rather than function-typed ones; the
unfolding does not create it.

Determinism, `runs-fn : (Runs m c m1) (Runs m c m2) -> (Eq (Mem) m1 m2)`,
is accepted [ran]. It uses `runop-fn` and `pick-fn`, which use
`nth-fn`, `setnth-fn`, and `repeat-fn` from `std/list.sl`, `add-fn`
from `lib/prelude.sl:407`, and `alloc-fn` from `spec.sl`. A wrong final step in it is refused [ran].

### F2. The stepper and the soundness theorem (`machine.sl`)

- `Step k m k2 m2` is the small-step relation on a command stack; it has
  one rule per command, mirroring `Runs` (`machine.sl:11-21`).
- `RunsAll m k m2` lifts `Runs` to stacks (`RANil`, `RACons`).
- `step-back : (Step k m k2 m2) (RunsAll m2 k2 mf) -> (RunsAll m k mf)`
  is non-recursive: one case per `Step` rule, each one to four lines
  (`machine.sl:30-44`). This is the "reverse accumulation" lemma.
- `Trace k0 m0 k m`, with `TNil` and `TSnoc`, records the steps taken,
  newest outermost; `trace-back` folds `step-back` over it by `subterm`
  recursion (`machine.sl:46-50`).
- `step : (many (List (Cmd)) k) (many (Mem) m) -> (many (StepOut k m) r)`
  returns `SNext k2 m2 (erased (Step k m k2 m2))`, `SHalt` (indexed by
  the empty stack), or `SStuck`. It calls no function at its own level;
  the list helpers recurse structurally.
- `advance` takes the state and `(erased (Trace (c0 :: nil) m0 k m))`.
  On `SHalt` it applies `trace-back` to `RANil`, takes the one `RACons`
  apart, and returns `Halted mf (erased (Runs m0 c0 mf))`
  (`machine.sl:182-189`). So the type of `advance` is the soundness
  theorem: whatever the machine halts with, the spec relates the program
  to it. `c0` and `m0` are pinned by the trace's type: any trace a
  caller supplies is a chain of `Step` derivations from
  `(c0 :: nil, m0)` to the current state, the one for the start state
  being `TNil (c0 :: nil) m0` (`machine.sl:26`), and `Running` hands
  back a trace with the same `c0` and `m0` (`machine.sl:178`). It says
  nothing about a run that never halts or gets stuck.
- `run.sl`'s `drive` wraps `advance` in one `def-unique` continuation per
  step, as `proto/theorems/drive.sl` does. The driver is the only loop
  (§42: "It never recurses, so an unbounded interaction is the driver's
  loop over total functions."). Output [ran]: `halted after 151 steps;
  registers 0 #4 0 114 5 #4; heap [ 5 0 ] [ 4 #0 ] [ 3 #1 ] [ 2 #2 ] [
  100 #3 ]`. `drive`'s own type says nothing about `advance`'s
  outcome, so the driver and the text it prints are outside the theorem.

Checks that the theorem has teeth [ran, files in the session
scratchpad]: swapping `c1` and `c2` in `step`'s `CSeq` case is refused
at `SNext`, which tests `step` against `Step` rather than against the
spec. Inverting the loop test in both `Step` and `step`, so the machine
is consistent with itself but not with the spec, is refused in
`step-back` at `ExWhile`; swapping `c1` and `c2` in both is likewise
refused in `step-back` at `ExSeq` [ran, third review].

### F3. Completeness and termination (`complete.sl`)

- `Star` is the forward reflexive-transitive closure of `Step`;
  `star-trans` and `runs-star : (Runs m c m1) -> (Star (c :: k) m k m1)`
  are accepted. `runs-star`'s `CSeq` case makes two recursive calls on
  the two premises.
- `step-det` is accepted.
- `finish` iterates `advance` by recursion on an erased
  `(Star k m nil mf)`: `step-det` equates the machine's step with the
  derivation's first step, so the rest of the derivation, a subterm,
  starts from the machine's next state.
  When `advance` returns `Running`, the derivation's `StarRefl` case,
  which would make the stack empty, is refuted by the step `s` that
  `Running` carries (`(absurd (StarRefl _ _) s)`). This is the Bove–Capretta
  shape of 05 F4, here over the same `advance` the driver uses.
- `run-total : (many (Cmd) c0) (many (Mem) m0) (erased (Mem) mf)
  (erased (Runs m0 c0 mf) spec) -> (many (Agrees c0 m0 mf) a)`, where
  `AgreeHalted` carries `(many mf is r)`. With determinism, the machine's
  result is the spec's. `total_demo.sl` writes one derivation out at top
  level and prints `(AgreeHalted _ _ _ $ MkMem (Cons _ (VNum 7) $ Nil _)
  $ Nil _)` [ran, also `--no-extern` and `slc --interpret`]. As 05 F4
  says of this shape, a caller needs a `Runs` derivation from somewhere.
- `AgreeStuck` is still a possible result. Refuting it needs `step` to
  find every step that `Step` allows, not progress: the spec itself has
  stuck programs, such as `OPred` on a register holding `VNum 0` (no
  `RPred` applies), on which `run.sl`'s driver prints `stuck`
  (`proto/review6/06_pred_zero.sl`) [ran, sixth review]. The helpers
  return `NthNo`, `SetNo`, `OpNo`, and `PickNo` with no evidence, so
  nothing connects a failure to the derivation. I did not do this
  (§3 Q2). So as built, the types of `complete.sl` add only
  `star-trans`, `runs-star`, `step-det`, and that an `AgreeHalted`
  result is `mf`.
  "If this machine halts, it halts with `mf`" already follows from
  `advance`'s type and `runs-fn`. That `run-total` runs this machine,
  and halts or sticks within the derivation's step count, is read from
  its code (`finish` calls the real `advance` and recurses on the
  `Star`), not from a type: an `advance` that always answers `Ended`
  with `Stuck` and a `run-total` that always answers `AgreeStuck` have
  the same types (`proto/review3/06_vacuous.sl`, accepted) [ran, third
  review]. That `finish` stops at run time also rests on the erased
  `Star` being a real, finite derivation (second review notes, second
  uncertain point).

### F4. What the checker refused, and why

1. **A closure invariant at a fixed level, with no decreasing argument**
   (`ho_fixed_bad.sl`): the stepper takes `(erased (Fn L (erased (Mem) mf)
   (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv)`.
   Extending it after a step means a new closure at `L` calling `inv` at
   `L`: "same-level call to `inv` decreases no subterm argument". This
   matches 03 F4.1. It is the missing decrease that is refused, not the
   fixed level: giving the closure type a `(subterm erased (Nat) j)` and
   an `(erased (Eq (Nat) j n) e)`, with `n` the erased step count kept in
   the state, lets `inv2` at `L` match `e` against `Refl` and call `inv`
   on `n`, a subterm of `(Succ n)`. The stepper, at a level minted after
   `L`, applies it at a halt. `ho_counter.sl` is accepted by the
   reference, under `--no-extern`, and by `slc --interpret`, and halts a
   small loop with `Halted` [ran in review]. Its loop, `fin`, is a test
   driver bounded by a fuel of 1000, not a `Program` driver; the closure
   itself takes no fuel.
2. **A closure invariant at a packed level.** If the state packs
   `(erased (Level) L)` with `inv` at `L`, each step can `def-lvl` a fresh
   `L2` and build `inv2` at `L2` calling `inv`: accepted
   (`ho_exist_build.sl`). But the stepper cannot apply it at a halt:
   "`L` was not in scope when level `(level-of adv-ho)` was minted"
   (`ho_exist_use_bad.sl`). §17: "A function may call a function of a
   strictly lower level"; §18: for `(prove-predates x L)`, "`x` must have
   an introduction order (§5) earlier than `L`'s", and "`L` must be an
   entry created by `def-lvl`, or a `let` binder forwarding from one".
   §18 also says: "A level created later is strictly higher than one
   created earlier, so a function at a later level cannot be called from
   code at an earlier level." Packing a `Predates` from `L` to a level
   `S` minted first does not help: a function at `S` can then apply the
   closure, but a step cannot prove its fresh `L2` below `S`: "`L2` was
   not in scope when level `S` was minted"
   (`proto/review3/06_packed_predates_bad.sl`) [ran, third review].
   The `Predates` need not be packed: a function at `S` given a state
   built before `S` was minted, with a `Predates` from that state to `S`,
   gets one for the packed level through `prove-subterm` and
   `predates-subterm`, and applies the closure
   (`proto/review7/06_packed_subterm.sl`; reference, `--no-extern`, and
   `slc --interpret`) [ran, round 7]. As I read §18, a state a step builds
   can have no such `Predates`, so this does not help a stepper either.
   Inside a closure defined at a packed level, even a call to a lower-level
   function such as `step-back` needs a packed `Predates`: without one,
   "`L` is not a level minted by `def-lvl`" (§18: "`L` must be an entry
   created by `def-lvl`, or a `let` binder forwarding from one") [ran,
   fourth review]. Packing both `Predates` proofs and item 1's counter,
   and extending the closure at its own packed level rather than at a
   fresh one, is accepted, applied at a halt, and halts the same small
   loop (`proto/review4/06_packed_counter.sl`; reference, `--no-extern`,
   and `slc --interpret`) [ran, fourth review]; its loop is the same
   fuel-bounded test driver as item 1's. Here the packed level is `L0`,
   minted at the top level before the stepper's `S`, and as I read §18 a
   level with a `Predates` to `S` is an entry introduced before `S` or a
   part of a value that has such a `Predates` (as in
   `06_packed_subterm.sl`, whose level binder is introduced after `S`),
   so a step cannot mint it afresh, and this is item 1 with the level
   hidden; item 1's counter makes packing the level
   unnecessary. The trace of F2 is the same closure defunctionalized:
   `step-back` is the code of each closure, and `Trace` is the list of
   them.
3. **Numerals in an erased derivation** (`total_demo.sl`, first draft):
   `RSet ... 0 ...` was refused against `(SetNth ... (Zero) ...)`, with
   the note that `0` "is a numeral literal, opaque to the checker". §45:
   "`3` is not `(Succ (Succ (Succ (Zero))))`." A register index that
   proofs inspect has to be written `(Zero)` or `(Succ ...)`, or exposed
   with `unary` (§49). At run time `nth-p` matches literals as usual.
4. **Style warnings**: lopsided `match` and unmarked same-level calls;
   fixed by `let-match` and `notail`. `Exec` and `SCons` clashed with
   prelude names (warning only); renamed.

Apart from these, every definition was accepted as first written. Items
3 and 4 and that sentence are the author's report on drafts that were
not kept: the reviews reproduce item 3's refusal and item 4's
name-clash warnings on edited copies of today's files, and cannot check
the rest.

### F5. Where the effort went

Non-blank, non-comment lines:

| part | lines |
|---|---|
| spec: syntax, `Alloc`, `RunOp`, `Pick`, `Runs` | 67 |
| spec determinism (`alloc-fn`, `runop-fn`, `pick-fn`, `runs-fn`) | 83 |
| soundness glue (`RunsAll`, `Step`, `Trace`, `step-back`, `trace-back`) | 41 |
| evidence-carrying result types (`NthOut` … `Advance`) | 34 |
| stepper code (helpers, `run-op`, `pick`, `step`, `advance`) | 90 |
| completeness and termination (`complete.sl`) | 52 |
| driver, printing, example (`run.sl`) | 43 |

Inside the stepper code, the proof is mostly one extra constructor
argument per line (`(RAdd e e2 h x y z a b c g1 g2 ad s)`) and erased
pattern binders. The largest single proof is `runop-fn` (47 lines): one
`nth-fn`/`setnth-fn` chain per primitive, each `let-match`ing a `Refl`.
`step-back`, the lemma that carries the technique, is 15 lines.

What made it longer than it would be with calls in types (§9: "The
elaborated form of a type never contains a function call"): each partial
helper has its own result type carrying the relation (`NthOut`,
`SetOut`, `OpOut`, `PickOut`, `StepOut`). `(Nth A xs i)` cannot be passed
unsaturated (§17: "There is no currying, for functions or for
constructors."), but a result type indexed by the unapplied relation is
accepted: `proto/review6/06_generic_out.sl` gives `run-op`'s result as
`(Out2 (Mem) m (Op) o (Mem) RunOp)` [ran, sixth review]. Such a wrapper
serves only relations whose signature has the shape of its relation
parameter. `Nth`, whose `xs` and `x` have types that mention its first
entry, does not fit a non-dependent three-input wrapper
(`proto/review6/06_generic_out_nth_bad.sl`, refused at the relation
argument) [ran, sixth review], but it fits one written with its own
signature, which the prelude's `NthLast` also fits; a four-input wrapper
fits `Pick`, and one written with `SetNth`'s signature fits it
(`proto/review7/06_generic_out_more.sl`) [ran, round 7]. So wrappers
could replace each of `NthOut`, `SetOut`, `OpOut`, and `PickOut`, but
the four relations have four signature shapes, so here they would save
no types. Long positional constructor telescopes (`RWrite` has 15
fields) are the main readability cost; patterns are counted by hand.

### F6. Cost of checking and running

[ran, one machine, single runs; ranges are across the author's run and
the reviews]: the reference takes 0.29–0.44 s on a one-line file,
0.36–0.54 s on `std/list.sl spec.sl machine.sl complete.sl`;
`slc --interpret` 0.18–0.27 s and 0.23–0.36 s. The long runs are `run.sl`
with both loop bounds `5` replaced by `300` (7821 steps) and by `1000`
(26021 steps). 7821 steps take 1.0–1.5 s in the reference interpreter,
0.39–0.58 s under `slc --interpret`, and under 0.01 s compiled
(`--build`); 26021 steps take 8.5–12.1 s, 3.3–3.6 s, and 0.03–0.07 s. The growth is probably the
list heap, which every allocation, read, and write walks. Peak memory
of the interpreters stays 22–41 MB, consistent with the erased trace
not being built at run time, which erasure (§14, §27) already implies.

## 3. Options

### Q1. Shape of the erased invariant

1. **Erased trace plus a per-step backward lemma** (built). *Pro:* first
   order, accepted, and the per-rule lemma is local and non-recursive
   once the spec is lifted to stacks. *Con:* the erased trace is, as a
   proof term, as long as the run; being erased, it is not built at run
   time (§14; F6's memory figures are consistent with that). *Cost:* 41
   lines here.
2. **Closure invariant with a packed level.** *Con:* with no packed
   `Predates`, it cannot be applied by the stepper; with one, it cannot
   be extended at a fresh level (F4.2). With the `Predates` proofs and
   option 5's counter packed, it works, but, as I read §18 (F4.2), only
   at one level with a `Predates` to the stepper's, which a step cannot
   mint afresh, so it is option 5 with the level hidden.
3. **A first-order "derivation under construction"**: an erased context
   of `Runs` frames, filled as commands finish, so the halt reads off the
   derivation with no fold. *Pro:* no trace. *Con:* needs one frame type
   per spec rule with a pending premise, and a plug lemma per frame.
   *Untested.*
4. **Small-step as the spec.** Take `Step`/`Star` as the spec and drop
   `Runs`. *Pro:* soundness is immediate if the spec's closure is the
   snoc-list `Trace` itself (the trace is then the derivation); with the
   cons-list `Star` as the spec, it needs a `Trace`-to-`Star` lemma.
   *Con:* determinism and composition are then lemmas about `Star`.
   For runs that end on the empty stack I expect the two to agree here
   (`runs-star` one way; `trace-back` the other, `Trace` being `Star`
   read backwards, though no lemma converting a `Star` to a `Trace` is
   written, so that direction is not compiled), so this looks like a
   presentation choice.
5. **Closure invariant at a fixed level with an erased step counter**
   (F4.1, `ho_counter.sl`, added in review). *Pro:* no `Trace` type and
   no fold; the halt applies the closure to `RANil`. *Con:* a ghost
   counter and an `Eq` argument in the closure type; it still uses
   `step-back` and `RunsAll`. *Cost:* about the same as option 1 (an
   estimate from `ho_counter.sl`, which builds no full stepper).

### Q2. Total correctness ("never stuck")

1. **Positive failure evidence**: `NthNo` carries evidence that the
   index is out of range, for example a `NoNth` relation like the one in
   07's `proto/roundtrip/spec.sl` (neither `std/list.sl` nor the prelude
   has one), and each failure site in `run-op` and `pick` refutes the
   given step: a missing index with a lemma like 07's `nth-nonth`, a value
   of the wrong shape with `nth-fn` and a constructor clash, and the
   other relations with like lemmas. There are 26
   failure sites (24 `OpNo` in `run-op`, 2 `PickNo` in `pick`). This
   refutes `AgreeStuck` given a `Runs` derivation; it says nothing of a
   program with none. *Cost:* perhaps 60–80 lines.
2. **A well-formedness invariant** (register count, pointer validity,
   value shapes) carried in the state, under which failure sites are
   unreachable. This is type soundness of the object language. For this
   toy I expect it would also need a language change: `OPred` on
   `VNum 0` has no rule (F3), and which registers hold `0` is known only
   at run time.
   *Cost:* larger; it is the shape the full Sleight machine would need
   anyway.
3. **Accept "halted with the spec's result, or stuck"** (built).

### Q3. The implementation's heap

1. **`many` lists with functional update** (built). Simple; quadratic.
2. **The prelude's unique `Array`** (§44). Its API is indexed by the same
   `Nth`/`SetNth` relations this spec uses (`array-place`, `array-swap`),
   so the proofs could carry over. The machine state becomes unique and
   each `def-unique` continuation captures it. *Untested.*
3. **Abstract addresses** as 02 recommends (A1). Here an address is a
   position, which 02 recommends a spec of Sleight avoid (02's A2 cons:
   a spec exposing order or arithmetic "would need a theorem that
   nothing uses it"). *Untested.*

## 4. Decisions for the owner

1. **Is "spec as relation, stepper returns an erased derivation at halt,
   invariant as an erased trace" the pattern to scale up?** Recommended:
   yes, as a working hypothesis: it is first order, and by the author's
   report (F4) it compiled at first attempt apart from F4's items. A
   fixed-level closure with an erased counter (Q1.5) is an alternative
   the checker also accepts, so the choice between them looks like one
   of presentation. A certified stepper in the compiler-route proposals
   would use one of these two, or an untested shape such as Q1.3.
2. **Should the level rules allow a function to apply a closure whose
   level is packed in its argument?** I do not propose a change. As
   DESIGN.md stands (§17, §18, §19), a function that receives such a
   closure can apply it only with a `Predates` from the closure's level
   to its own. The reviews found three ways to have one: packed with the
   closure (F4.2); by `predates-subterm` from a `Predates` about the value
   that holds it (`proto/review7/06_packed_subterm.sl`; for 07's
   `Certified`, `proto/review7/07_cert_predates.sl`); and, for code whose
   level is minted after a top-level destructure of the value, proved
   directly (`proto/review6/07_cert_drive.sl`). The last two need the
   value built before the code's level is minted, which a stepper's
   states, arising at run time, are not; and, as I read §18, a closure at
   a level minted after the function's can never have one (F4.2). A
   closure at a fixed level with a decreasing erased argument works
   instead (F4.1), so certified steppers do not depend on this.
3. **Is "never stuck" a target for the formal spec's own machine?** If
   yes, Q2.2 (a typing invariant) is the route that also serves type
   soundness; Q2.1 is cheaper for a toy. They answer different
   questions: Q2.1 refutes "stuck" only when a `Runs` derivation exists,
   and Q2.2 for every well-formed state.
4. **Should the next spike use the unique `Array` heap and abstract
   addresses (Q3.2, Q3.3)?** Recommended: yes, before scaling, since 02
   recommends abstract addresses (its A1). Owner statement 6 of the
   brief (an earlier session's paraphrase) says the owner suspects the
   spec's run should be a mutating heap machine from the start; that
   concerns the spec, while Q3.2 concerns the implementation's heap.

## 5. Rough edges in DESIGN.md (questions, not resolutions)

1. §17, §18 with §24 item 2 ("a function, of `Fn` or `UniqueFn` type" is
   first-class data): a function stored in data whose level is packed
   beside it, as an erased `(Level)` field, can be held and extended,
   but, as far as the spike and its reviews found, code that receives the
   data can call it only with a `Predates` from the packed level to the
   code's own level: packed beside it, or derived by `predates-subterm`
   from a `Predates` about the data, which needs the data built before
   the code's level was minted (F4.2). For a level created after the
   code's, §18 says outright that it cannot be called ("a function at a
   later level cannot be called from code at an earlier level").
   Otherwise, as I read it, it follows from §18's rule for
   `prove-predates` ("`x` must have an introduction order (§5) earlier
   than `L`'s"), the packed level being a binder introduced after the
   code's level, with `predates-trans` and `predates-subterm` only
   chaining proofs that exist. So it is a consequence, not a gap;
   whether it is wanted for packed levels is decision 2. This did not
   block the spike: a fixed-level closure with a decreasing erased
   argument works (F4.1).
2. I found no contradiction in DESIGN.md while doing this spike.

## 6. Unverified claims

- That Q1.3 (a derivation context) would work, and its size.
- That no placement of levels lets a stepper apply a closure extended
  at a fresh level each step (F4.2); two packed shapes were tried
  (`ho_exist_use_bad.sl`, and `proto/review3/06_packed_predates_bad.sl`
  with a packed `Predates`). Two shapes that keep one level do work: the
  fixed-level counter of F4.1, and `proto/review4/06_packed_counter.sl`,
  which packs that level. A `Predates` about the state, passed beside
  it, serves a state built before the stepper's level
  (`proto/review7/06_packed_subterm.sl`) and, as I read §18, no state a
  step builds.
- The `--build` timings of F6 were not re-run by the first review; the
  second review got 0.00 s and 0.06 s, and the fifth 0.00 s and 0.07 s.
- The Q2.1 line estimate.
- That the prelude's `Array` API would carry these proofs over (Q3.2).
- That the technique scales to Sleight's own machine: rule count, frame
  kinds, `at`/cell reading-back, and the oracle of 02 were not modelled.
- Timings are single runs on one machine. `_build/release/slc` was used
  as found; its file is dated after the last change to `self/`
  (0bbc5e4), so it is probably built from the current source, but its
  build was not checked.

## Review notes

An adversarial review re-ran every claim at ad07c35 and edited this file.

Errors corrected:

1. Summary, F4.1, F4.2, Q1, decisions 1 and 2, and rough edge 1 said a
   closure invariant cannot be used because of levels and that the trace
   is "the only invariant shape" the level rules allow. False: a closure
   at one fixed level with an `(subterm erased (Nat) j)` step counter and
   an `Eq` pinning it is accepted and runs (`proto/stepper/ho_counter.sl`,
   added in review; reference, `--no-extern` and `slc --interpret`).
   `ho_fixed_bad.sl` is refused for the missing decrease, not for the
   fixed level. Added Q1.5. This may also bear on 03 F4.1's conclusion
   about fixed-level continuation closures (not checked there; 03 not
   edited).
2. The summary implied `run-total` establishes agreement; added that
   "stuck" carries no evidence, so a `step` that always answered
   `SStuck` would satisfy every type in the spike. What is proved:
   partial correctness of `advance` for the trace's `c0`, `m0`; spec
   determinism; and, given a `Runs` derivation, that iterating `advance`
   halts or sticks within its step count and a halt gives `mf`. Not
   proved: progress, or anything for programs with no `Runs` derivation.
3. Decision 4 called owner statement 6 a decision putting the heap "at
   the centre"; it is an earlier session's paraphrase of a suspicion.
   Reworded.
4. F5 table: `run.sl` has 43 non-blank, non-comment lines, not 44.
5. F6 inferred "the trace is not built" from memory use; reworded as
   consistent with what erasure (§14, §27) already implies.
6. F1's aliasing sentence: the sum is read through register 2, a copy
   of register 1's pointer; reworded.

Confirmed as written: every accept/refuse/output claim (reference,
`--no-extern`, `--build`, `slc --interpret`, `slc --build`); both bad
files refused with the quoted messages, at the closure call (11:17) and
the same-level call (8:5); the two teeth checks (swapped `CSeq`, refused
at `SNext`; inverted loop, refused at `ExWhile` in `step-back`); the
wrong `runs-fn` step refused; the numeral refusal and note of F4.3; the
7821/26021-step counts and interpreter timings (1.46 s / 0.58 s, 12.1 s /
3.6 s); the DESIGN.md quotes (§9, §17, §18, §21, §24, §42, §45); the
`lib/prelude.sl` and `std/list.sl` citations; the line counts other than
item 4; 26 failure sites (24 `OpNo` in `run-op`, 2 `PickNo` in `pick`).

Uncertain:

- Whether some other arrangement (for example a `Predates` proof packed
  with the level) would let a packed-level closure be applied; the
  review's reading of §18 says no, but only the shapes named in F4.2
  were compiled.
- The `--build` timings and "accepted as first written" were not
  re-checked.

## Second review notes

A second adversarial review read DESIGN.md in full and every file in
`proto/stepper/`, and re-ran at 07692f2 (no code change since d6644d9):
`run.sl`, `complete.sl total_demo.sl`, `ho_counter.sl`, and
`ho_exist_build.sl` under the reference, `--no-extern`, and
`slc --interpret`; `run.sl` under `--build` and `slc --build`; both
bad files; the two teeth checks, and the wrong `runs-fn` step; the
numeral refusal; the line counts; the 26 failure sites; the checking
times; and the 7821- and 26021-step runs, `--build` included. All
matched except as below. Errors found and changes made:

1. F1: the body still said the list is summed "from register 1",
   while first-review note 6 said it had been reworded to register 2.
   `run.sl` copies register 1 to register 2 and walks register 2. The
   body now says so.
2. F2 said "the only trace a caller can start with is `TNil`". A caller
   may pass any erased `Trace` whose type fits, for example one with a
   step already taken; the soundness claim holds for every such trace,
   since a `Trace` is a chain of `Step` derivations from
   `(c0 :: nil, m0)`. Reworded.
3. F2: added that `drive`'s type says nothing about `advance`'s
   outcome, so the driver and its printed text are outside the theorem
   (as 07 F7 says of its driver).
4. F2: `step-back`'s cases are one to four lines, not "two or three".
5. F3: "On the empty stack the derivation's `StarRefl` case is refuted"
   had it backwards: in the `Running` case, `StarRefl` would force the
   stack empty, and the step `s` refutes that. Reworded.
6. F6: the long-run program was not identified; it is `run.sl` with
   both loop bounds set to 300 and 1000 (the step counts reproduce
   exactly). "Every step walks" the heap was an overclaim: only
   allocation, read, and write do. The `--build` times were re-run
   (0.00 s and 0.06 s); §6 updated.
7. Q1.4: no lemma turns a `Star` into a `Trace`; added.
8. Q2.1: refuting failures needs lemmas beyond `nth-fn` (for example
   for `SetNth` and the value-shape tests); the 26-site count was
   confirmed by the first review and is now stated with its split, and
   dropped from §6.
9. Decision 1's "compiled at first attempt" is the author's report and
   F4 lists exceptions; hedged.
10. Oxford commas in several lists; header names the second review's
    commit and that the command lines take `std/list.sl` from the
    repository root.

The theorem's type was checked against the claims: `advance`'s
`Halted` carries `(erased (Runs m0 c0 mf) d)` for the trace's `c0`,
`m0`; `run.sl` starts it with `TNil` at `(prog :: nil, mem0)`;
`run-total`'s `AgreeHalted` carries `(many mf is r)`. Vacuous
implementations that pass every type: a `step` that answers `SStuck`
on any or all states. A `step` cannot answer `SHalt` on a non-empty
stack (its type is indexed by `Nil`), and every `SNext` carries a real
`Step`, which is deterministic.

Points I am unsure of:

- Whether some arrangement with a `Predates` packed beside the level
  would let F4.2's packed-level closure be applied. My reading: the
  stepper's level is minted first, and §18's `prove-predates` needs
  the lower level introduced earlier, so a level minted at each step
  cannot be proved below it, and `predates-trans` and
  `predates-subterm` only chain proofs that already exist. Not
  compiled.
- Every claim that an erased derivation is "real" rests on Sleight's
  erased logic having no closed proof of `False`; with §10's
  `Type : Type` and no positivity, nothing here shows that. The
  brief's owner statement 1 (an earlier session's paraphrase) says no
  consistency theorem is expected.
- "Accepted as first written" (F4) remains the author's report.

## Third review notes

A third adversarial review read DESIGN.md in full, every file in
`proto/stepper/`, and re-ran at c236135 (no code change since d6644d9):
`run.sl` under the reference, `--no-extern`, `--build`,
`slc --interpret`, and `slc --build`; `complete.sl total_demo.sl` under
the same five; `ho_counter.sl` and `ho_exist_build.sl` under the
reference, `--no-extern`, and `slc --interpret`; both bad files; both
teeth checks; a wrong `runs-fn` step; the numeral refusal; the line
counts; the 24 + 2 failure sites; and the 7821- and 26021-step runs
(1.39 s and 11.3 s reference, 0.53 s and 3.3 s slc, 0.06 s built, peak
22–41 MB). All matched, up to timing noise (the one-line file took
0.38 s, not 0.44 s). Errors found and changes made:

1. §5 rough edge 1 said DESIGN.md does not say whether calling a
   later-level closure from earlier code is meant to be impossible.
   §18 says it: "A level created later is strictly higher than one
   created earlier, so a function at a later level cannot be called
   from code at an earlier level." Reworded as a consequence, not a gap.
2. F4.2 rested on "my reading" and the second review's open point said
   a packed `Predates` was not compiled. It now is:
   `proto/review3/06_packed_predates_bad.sl` packs
   `(Predates (Level) L S)` with `S` minted first; a function at `S`
   applies the closure (accepted when the file stops there), and the
   step that mints `L2` is refused at `(prove-predates L2 S)` with
   "`L2` was not in scope when level `S` was minted". F4.2 quotes the
   §18 sentence and the result; §6 updated.
3. F1 said the `ExWhile` unfolding "makes every premise a strict
   subterm". Any rule's premises are fields of its derivation, so that
   holds whatever the rules are; the unfolding does not create it.
   Reworded; added that the recursion is on derivations, not commands.
4. Vacuity: besides a `step` that always answers `SStuck`, an `advance`
   that always answers `Ended` with `Stuck`, and a `run-total` that
   always answers `AgreeStuck`, have the theorems' types
   (`proto/review3/06_vacuous.sl`, accepted). Added to F3, which also
   now says the step-count bound comes from `finish`'s recursion, not
   from a type.
5. F2's first teeth check (swap in `step` only) tests `step` against
   `Step`, not against the spec; said so, and added the stronger check
   (swap in both `Step` and `step`), refused in `step-back` at `ExSeq`.
6. Decision 4's "since 02 recommends one" named nothing; it is 02's A1
   (abstract addresses). It also cited owner statement 6, which is about
   the spec's run, for Q3.2, which is about the implementation's heap;
   the mismatch is now stated.
7. Summary: "an erased step counter that each extension decreases" read
   as the counter decreasing over the run; it increases, and each
   extension's call to the previous closure decreases it. Reworded.
8. F4.1 said "the state holds" the closure; in `ho_fixed_bad.sl` it is
   the stepper's argument. F1 omitted `alloc-fn` from `runop-fn`'s
   lemmas. Oxford commas in F1, F2, and F4.1.

Points I am unsure of:

- Whether some arrangement other than the three compiled ones (no proof,
  a packed `Predates`, a fixed level with a counter) lets packed-level
  closures be applied, for example a state type parameterised by the
  stepper's level. My reading of §18 (`prove-predates` needs a level
  "created by `def-lvl`", not a parameter) says no; not compiled.
- Timings remain single runs; `_build/release/slc` was used as found.

## Fourth review notes

A fourth adversarial review read DESIGN.md in full, every file in
`proto/stepper/` and `proto/review3/06_*`, and re-ran at e0aaf2c (no code
change since d6644d9): `run.sl` under the reference, `--no-extern`,
`--build`, `slc --interpret`, and `slc --build`; `complete.sl
total_demo.sl` under the same five; `ho_counter.sl` under the reference,
`--no-extern`, and `slc --interpret`; `ho_exist_build.sl`; the three bad
files (messages and positions as quoted); `06_vacuous.sl`; all three
teeth checks (refused at `SNext` argument 5, at `ExSeq`, and at
`ExWhile`); a wrong `runs-fn` step; the numeral refusal; the F5 line
counts, the 47-line `runop-fn`, the 15-line `step-back`, and `RWrite`'s
15 fields; the 24 + 2 failure sites; the `lib/prelude.sl` and
`std/list.sl` citations; and the 7821-step run (1.33 s reference,
0.48 s slc, peak 22–32 MB). All matched. Errors found and changes made:

1. The summary, F4.2, Q1.2, decision 2, and §6 said a closure whose
   level is packed in the state "can be built but not applied" and is
   "not viable". With a `Predates` from its level to the stepper's
   packed too, the stepper applies it: `06_packed_predates_bad.sl` cut
   after its line 13 is accepted. What fails is extending it at a fresh
   level. And packing the level with both `Predates` proofs it needs
   plus F4.1's counter, extending at that same packed level, is
   accepted and halts a loop with `Halted`
   (`proto/review4/06_packed_counter.sl`, new; reference,
   `--no-extern`, and `slc --interpret`). Without the second `Predates`,
   the packed-level closure cannot even call `step-back`: "`L` is not a
   level minted by `def-lvl`". All five places now say this, and that
   this shape is F4.1's with the level hidden.
2. §5 rough edge 1 cited §18's "a function at a later level cannot be
   called from code at an earlier level" as saying outright that a
   packed-level closure cannot be called. A packed level need not have
   been created later; what refuses `ho_exist_use_bad.sl` is §18's
   introduction-order rule for `prove-predates`, the packed level being
   a binder introduced after the stepper's level ("`L` was not in scope
   when level `(level-of adv-ho)` was minted"). Reworded.
3. F3 said that as built "the completeness half proves only" a halt with
   `mf` within the step count. No type in `complete.sl` says that: the
   halt-with-`mf` part already follows from `advance`'s type and
   `runs-fn`, and the bound is read from the code. Rewritten to say
   which part is a type and which is read from the code, and that
   `finish` stopping at run time rests on the erased `Star` being real.
4. F1: "This holds for any rule set" overclaimed. A function-typed
   premise is a field, but recursion through it is not subterm
   recursion (§18: `prove-subterm` "treats a type former (production 4)
   as opaque"). Qualified to plain fields.
5. Q1.4 stated that `Star` and `Trace` runs "agree" when only one
   direction is compiled; now an expectation.
6. Decision 1 called Q1.5 "an accepted alternative", which reads as
   approved; it is accepted by the checker. "Everything ... depends on
   one of the two" ignored the untested Q1.3. Reworded.
7. Summary: "the reference accepts all of it" while three files are
   meant to be refused; it now names the files it runs.
8. Q1.1 cited F6's memory figures for what §14 implies; Q1.5's cost is
   now marked as an estimate. Timings in the summary and F6 now give
   the range across reviews (the one-line file took 0.38 s today).

Points I am unsure of:

- That no arrangement lets a stepper apply a closure that each step
  extends at a level minted during the run; my reading of §18 is that a
  level minted after the stepper's can never be proved below it, and
  `predates-trans` and `predates-subterm` only chain existing proofs.
- `06_packed_counter.sl` mints its packed level at the top level, before
  the stepper's; I did not try packing a level that is itself passed in
  from a caller.

## Fifth review notes

A fifth adversarial review read DESIGN.md in full, every file in
`proto/stepper/`, `proto/review3/06_*`, and `proto/review4/06_*`, and
re-ran at fb2c533 (no code change since d6644d9): `run.sl` under the
reference, `--no-extern`, `--build`, `slc --interpret`, and
`slc --build`; `complete.sl total_demo.sl` under the same five;
`ho_counter.sl` and `06_packed_counter.sl` under the reference,
`--no-extern`, and `slc --interpret` (both print `0`, the `Halted`
case); `ho_exist_build.sl`; the three bad files (messages and positions
as quoted); `06_packed_predates_bad.sl` cut after line 13 (accepted);
`06_packed_counter.sl` without `(predates pb)` ("`L` is not a level
minted by `def-lvl`"); `06_vacuous.sl`; all three teeth checks; a wrong
`runs-fn` step; the numeral refusal and its note; the prelude warning
for redeclaring `SCons` and `Exec` (F4.4); a `step` whose body is
`(SStuck _ _)`, with which `machine.sl`, `complete.sl`, and both demos
are accepted, and `total_demo.sl` and `run.sl` print `(AgreeStuck _ _ _)`
and `stuck`; the F5 line counts, the 47-line `runop-fn`, the 15-line
`step-back`, `RWrite`'s 15 fields, and the 24 + 2 failure sites; the
`lib/prelude.sl`, `std/list.sl`, and `machine.sl`/`spec.sl` line
citations; the DESIGN.md quotes; and the timings (one-line file
0.40 s, the four files 0.48–0.51 s, slc 0.24–0.27 s and 0.32 s; 7821
steps 1.37 s, 0.57 s, and 0.00 s built; 26021 steps 10.8 s, 3.43 s, and
0.07 s built; peak 22–41 MB). All matched except as below. Errors found
and changes made:

1. Q2.1 said `NthNo` would carry "a `NoNth` derivation" and failures
   would be refuted "with `nth-fn` or a like lemma". No `NoNth` exists
   in the stepper's files, `std/list.sl`, or the prelude (it is 07's,
   `proto/roundtrip/spec.sl:33`), and `nth-fn` (functionality) cannot
   refute a missing index; 07 needs `nth-nonth` for that. Reworded to
   name both kinds of lemma.
2. Q1.4 said that with `Step`/`Star` as the spec "the trace is the
   derivation". `Trace` is a snoc-list and `Star` a cons-list, and no
   conversion is written (as Q1.4 itself says). Now: immediate only if
   the spec's closure is `Trace` itself.
3. F4.2 stated as fact that "the packed level is then one minted before
   the stepper's". That holds for `06_packed_counter.sl` (`L0`); in
   general it is a reading of §18 (I did not try, for example, a level
   reached through `predates-subterm` on a field of an earlier value).
   Hedged, and the file's level named.
4. F4.1 and F4.2 said the closure shapes "halt a small loop" without
   saying that the loop in `ho_counter.sl` and `06_packed_counter.sl`,
   `fin`, takes a fuel of 1000. The closures take no fuel; the test
   driver does. Said so, since the spike's title is "fuel-free".
5. F6 gave single figures for the long runs where the reviews measured
   a spread (for example 10.8–12.1 s for 26021 steps); now ranges, and
   slc's short-run range is 0.24–0.27 s.
6. §6: the `--build` timings were re-run (0.00 s and 0.07 s), and
   `_build/release/slc` is dated after the last change to `self/`
   (0bbc5e4 on 2026-11-06; the binary is from 2026-11-17); still not a
   check of its build.

The theorem's type was checked against the claims again: `advance`
takes the trace at `(Cons c0 Nil, m0)` and its `Halted` carries
`(erased (Runs m0 c0 mf) d)`; `Running` needs a real `Step` from the
current state and so is determined by `step-det`, and is impossible on
the empty stack; `run-total`'s `AgreeHalted` carries `(many mf is r)`.
The vacuous implementations that pass are those already listed: a
`step` answering `SStuck` (compiled above), an `advance` answering
`Ended` with `Stuck`, and a `run-total` answering `AgreeStuck`.

Points I am unsure of:

- Whether a level reached by forcing a field of an erased value
  introduced before the stepper's level (so that `predates-subterm`
  gives it a `Predates` to that level) could serve as a packed level
  that each step changes. I expect such levels to be finitely many,
  since the value is finite, so it would not give an unbounded run;
  not compiled.
- The "Proof is about 210 lines" in §1 is F5's determinism, soundness
  glue, result types, and `complete.sl` rows (83 + 41 + 34 + 52);
  `complete.sl` includes `finish` and `run-total`, which are code.

## Round 6 review notes

A sixth adversarial review read DESIGN.md in full, every file in
`proto/stepper/`, `proto/review3/06_*`, and `proto/review4/06_*`, and
re-ran at 10bd85d (no code change since d6644d9): `run.sl` and
`complete.sl total_demo.sl` under the reference, `--no-extern`,
`--build`, `slc --interpret`, and `slc --build`; `ho_counter.sl` and
`06_packed_counter.sl` under the reference, `--no-extern`, and
`slc --interpret` (both `0`); `ho_exist_build.sl`; the three bad files
(messages and positions as quoted); `06_packed_predates_bad.sl` cut
after line 13 (accepted); `06_packed_counter.sl` without `(predates pb)`
(refused at 24:26 as quoted); `06_vacuous.sl`; the three teeth checks
(refused at `SNext` argument 5, `ExSeq` argument 6, and `ExWhile`
argument 5); a `step` whose body is `(SStuck _ _)` (`stuck` and
`(AgreeStuck _ _ _)`); the numeral refusal and its note; the F5 line
counts, `runop-fn`'s 47 lines, `step-back`'s 15, and the 24 + 2 failure
sites; the `lib/prelude.sl` and `std/list.sl` citations; the DESIGN.md
quotes; and the timings (one-line file 0.29–0.31 s, the four files
0.36–0.41 s, slc 0.18–0.25 s and 0.23–0.36 s; 7821 steps 1.01 s, 0.39 s,
and 0.00 s built; 26021 steps 8.51 s, 3.42 s, and 0.03 s built; peak
22–41 MB). All matched except as below. Errors found and changes made:

1. F3 and the summary said refuting `AgreeStuck` "needs progress". With
   a `Runs` derivation in hand it needs `step` to find every step that
   `Step` allows; progress would be "every well-formed state steps",
   which this spec does not have: `OPred` on a register holding `VNum 0`
   has no `RPred`, and `run.sl`'s driver rightly prints `stuck` on it
   (`proto/review6/06_pred_zero.sl`, new) [ran]. F3 and the summary now
   say so; Q2.1 says what it refutes; Q2.2 says that for this toy a
   typing invariant would also need a language change (my expectation);
   decision 3 says the two options answer different questions.
2. F5 said each partial helper "needs" its own result type and that no
   generic "value with proof" wrapper exists, since `(Nth A xs i)`
   cannot be passed unsaturated. A result type indexed by the unapplied
   relation is accepted for a relation with a non-dependent signature:
   `proto/review6/06_generic_out.sl` (new) wraps `run-op`'s result as
   `(Out2 (Mem) m (Op) o (Mem) RunOp)` and prints `(Found2 ... )` under
   the reference, `--no-extern`, and `slc --interpret`.
   `proto/review6/06_generic_out_nth_bad.sl` (new) shows `Nth`, whose
   signature is dependent, refused as a three-input wrapper's relation.
   Rewritten.
3. F3 said `step-det` makes "the rest of the derivation a subterm". It
   is a subterm in any case; what `step-det` gives is that it starts
   from the machine's next state, so the recursive call type-checks.
   Reworded.
4. The summary called 210 lines "proof"; they include `complete.sl`'s
   `finish` and `run-total`, which are code (fifth review's open point).
   Now says what the 210 lines are.
5. Decision 2 said a packed-level closure "can be built but not applied"
   without a packed `Predates`. That holds for a function that receives
   it; code whose level is minted after a top-level destructure of the
   value can apply it (`proto/review6/07_cert_drive.sl`, 07's
   `Certified`, accepted; `07_cert_fn_bad.sl`, a function given the same
   value, refused with "`L` was not in scope when level ... was
   minted"). Qualified; this does not help a stepper, whose states arise
   at run time.
6. F4.2 and Q1.2 said a level with a `Predates` to `S` is "minted"
   before `S`; §18 asks that `x` have an earlier introduction order,
   and a destructured level is introduced, not minted. Q1.2 also stated
   that reading as fact. Both now say "introduced" and Q1.2 is hedged.
7. F6 and the summary: today's timings fall below the stated ranges;
   the ranges now include them. Header names this review's commit.
8. Q3.3 said, unhedged, that a spec of Sleight "would not want"
   position addresses; that is 02's recommendation (its A1, with A2's
   cons quoted), not established. Now attributed.

Also checked: `ho_exist_build.sl`'s closure state can be returned, not
only built (a scratch variant returning it in a `HNext` is accepted), so
F4.2's "can def-lvl a fresh `L2` and build `inv2`" holds for a real
step.

Points I am unsure of:

- Whether `PickOut` fits a four-input wrapper as `OpOut` fits
  `Out2`; `Pick`'s signature is not dependent, but this was not
  compiled.
- That a typing invariant for this toy would need a language change
  (Q2.2); a semantic invariant tracking register contents might not,
  but would amount to running the program.

## Round 7 review notes

A seventh adversarial review read DESIGN.md in full, every file in
`proto/stepper/`, `proto/review3/06_*`, `proto/review4/06_*`, and
`proto/review6/06_*`, and the round-7 tests an interrupted reviewer
left, and re-ran at 13ca61f (no code change since d6644d9): `run.sl` and
`complete.sl total_demo.sl` under the reference, `--no-extern`,
`--build`, `slc --interpret`, and `slc --build`; `ho_counter.sl` and
`06_packed_counter.sl` under the reference, `--no-extern`, and
`slc --interpret` (both `0`); `ho_exist_build.sl`; the three bad files
(messages and positions as quoted); `06_packed_predates_bad.sl` cut
after line 13 (accepted); `06_packed_counter.sl` without `(predates pb)`
(refused at 24:26); `06_vacuous.sl`; `06_pred_zero.sl` (`stuck`);
`06_generic_out.sl` in three modes and `06_generic_out_nth_bad.sl`; the
three teeth checks (`SNext` argument 5, `ExWhile` argument 5, `ExSeq`
argument 6); a wrong `runs-fn` step; the numeral refusal and its note;
F4.4's name-clash warnings; the F5 line counts, `runop-fn`'s 47 lines,
`step-back`'s 15, `RWrite`'s 15 fields, and the 24 + 2 failure sites;
the `lib/prelude.sl`, `std/list.sl`, 02 A1/A2, 03 F4.1, and 05 F4
citations; the DESIGN.md quotes; and, with the one-minute load average
between 0.5 and 1.1, the timings (one-line file 0.42–0.44 s, the four
files 0.51–0.54 s, slc 0.25–0.27 s and 0.33–0.34 s; 7821 steps 1.45 s,
0.52 s, and 0.00 s built; 26021 steps 11.8 s, 3.50 s, and 0.06 s built;
peak 22–41 MB). All matched except as below. Errors found and changes
made:

1. F5 said a result type indexed by an unapplied relation is accepted
   "when the relation's signature is not dependent", that such a wrapper
   "is per input count", and that wrappers could not replace `NthOut` or
   `SetOut`. A wrapper whose relation parameter has `Nth`'s dependent
   signature serves `nth-p` and the prelude's `NthLast`, one with
   `SetNth`'s serves `set-p`, and a four-input one serves `pick`
   (`proto/review7/06_generic_out_more.sl`, left by the interrupted
   reviewer and extended here with `SetNth`; reference, `--no-extern`,
   and `slc --interpret`). Each wrapper serves one signature shape, and
   the four relations have four, so here wrappers would save no types.
   Rewritten; this also settles the round-6 open point on `PickOut`.
2. Decision 2 and §5 rough edge 1 said a packed-level closure cannot be
   applied by a function that receives it unless a `Predates` is packed
   with it. `proto/review7/06_packed_subterm.sl` (left by the
   interrupted reviewer; reference, `--no-extern`, and
   `slc --interpret`) gives a function at `S` a state built before `S`
   was minted and a `Predates` from the state to `S`; `prove-subterm`
   and `predates-subterm` give the packed level its `Predates`, and the
   closure is applied (`Halted`). This needs the state built before `S`,
   so it does not help a stepper either. F4.2, decision 2 (now listing
   the three ways the reviews found), rough edge 1, the summary (now "a
   stepper that extends it ... cannot apply it"), and §6 say so. It also
   bears on the fifth review's open point: a level reached through
   `predates-subterm` can be applied; whether it can change at each step
   is still not compiled.
3. F4.2 read §18 as making "any level with a `Predates` to `S`" one
   "introduced ... before `S`". In `06_packed_subterm.sl` the level is a
   binder introduced inside `use`, after `S`, and has one through
   `predates-subterm`. F4.2 and Q1.2 now give what the argument needs,
   that a step cannot mint such a level afresh, still as a reading.
4. F6 gave slc's four-file time as 0.23–0.33 s, while the sixth review
   measured up to 0.36 s and its note 7 says the ranges include its
   timings; this review got 0.33–0.34 s. Now 0.23–0.36 s, and the
   reference's four-file range takes in today's 0.54 s.
5. F4's items 3 and 4 are history on drafts that were not kept, but
   only "accepted as first written" was marked as the author's report.
   All three are now, with what the reviews reproduce on edited copies
   of today's files (item 3's refusal and item 4's name-clash warnings).
6. Header: names this review's commit.

Points I am unsure of:

- That no route gives each state a stepper builds a `Predates` to the
  stepper's level. My reading of §18 is that `prove-predates` needs the
  state introduced before the level, and `predates-trans` and
  `predates-subterm` only reach levels inside values that already have
  one; not compiled beyond the shapes F4.2 names.
- Whether decision 2's three ways to have the `Predates` are all; I
  found no other in §18 or §19, but did not prove there is none.
