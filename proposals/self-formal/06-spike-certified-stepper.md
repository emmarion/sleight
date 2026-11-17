# 06. Spike: a certified, fuel-free stepper for a heap language

Written overnight by a Claude agent as a proof-technique spike. It is a
proposal and an agent's reading; nothing in it is approved or decided.
Where it and DESIGN.md disagree, DESIGN.md is right.

Sources are marked: **§n** quotes DESIGN.md; **file:line** is code;
**[ran]** is a run tonight of the reference (`_build/default/bin/main.exe`,
commit d6644d9; the review re-ran everything at ad07c35) and, where said,
of `_build/release/slc`. The prototype is
`proto/stepper/`. Every command line starts with `std/list.sl spec.sl
machine.sl`.

## 1. Summary

- A tiny language (registers, a heap of mutable blocks with allocate,
  read and write-in-place, `if`, `while`) has a big-step spec `Runs m c
  m2` (`spec.sl`). A total, non-recursive `step` over an explicit command
  stack and memory, driven one `Program` continuation per step, runs it
  with no fuel. The reference accepts all of it and runs it [ran]; so do
  `--no-extern`, `--build`, `slc --interpret` and `slc --build` [ran].
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
  works at one fixed level if it takes an erased step counter that each
  extension decreases (`ho_counter.sl`, added in review) [ran]. Without
  that counter it is refused at a fixed level, and with its level packed
  in the state it can be built but not applied (§17, §18) [ran].
- Missing: refuting "stuck" (progress), an in-place (unique) heap in the
  implementation, and abstract addresses. Proof is about 210 lines
  against 90 lines of stepper code and 67 lines of spec. Checking all of
  it adds about 0.1 s to the prelude's 0.44 s [ran].

## 2. Findings

### F1. The language and its spec (`spec.sl`)

`Val` is `VNum n | VPtr a`; `Mem` is `MkMem env heap`, registers as a
`(List (Val))` and the heap as a `(List (List (Val)))`, an address being
a position. `Op` has `OSet`, `OMov`, `OPred`, `OAdd`, `OAlloc`, `ORead`
and `OWrite`; `Cmd` has `CSkip`, `COp`, `CSeq`, `CIf` (zero test) and
`CWhile`. The atomic semantics `RunOp m o m2` is stated with the
prelude's `Nth`, `SetNth`, `Repeat` and `Add` (`lib/prelude.sl:1281-1302`,
`:33-36`) and one new relation, `Alloc` (append at the end, address =
old length). A write is `SetNth` on the block, then `SetNth` on the heap
at the same address, so an alias sees it: `run.sl` writes `100` through
register 5 (a copy of the list's head pointer in register 1) and then
sums the list from register 1 [ran: `114`].

`Runs` has five rules (`spec.sl:69-78`). `CIf` goes through a relation
`Pick m x c1 c2 c`, and `CWhile` unfolds: `ExWhile` derives `Runs m
(CWhile x b) m2` from `Runs m (CIf x (CSkip) (CSeq b (CWhile x b))) m2`.
That makes every premise a strict subterm, so all inductions below are
plain `subterm` recursion on derivations (§21: "Subterm recursion (§17)
may go through an erased field.").

Determinism, `runs-fn : (Runs m c m1) (Runs m c m2) -> (Eq (Mem) m1 m2)`,
is accepted [ran]. It uses `runop-fn` and `pick-fn`, which use
`nth-fn`, `setnth-fn` and `repeat-fn` from `std/list.sl` and `add-fn`
from `lib/prelude.sl:407`. A wrong final step in it is refused [ran].

### F2. The stepper and the soundness theorem (`machine.sl`)

- `Step k m k2 m2` is the small-step relation on a command stack; it has
  one rule per command, mirroring `Runs` (`machine.sl:11-21`).
- `RunsAll m k m2` lifts `Runs` to stacks (`RANil`, `RACons`).
- `step-back : (Step k m k2 m2) (RunsAll m2 k2 mf) -> (RunsAll m k mf)`
  is non-recursive: one case per `Step` rule, each two or three lines
  (`machine.sl:30-44`). This is the "reverse accumulation" lemma.
- `Trace k0 m0 k m`, with `TNil` and `TSnoc`, records the steps taken,
  newest outermost; `trace-back` folds `step-back` over it by `subterm`
  recursion (`machine.sl:46-50`).
- `step : (many (List (Cmd)) k) (many (Mem) m) -> (many (StepOut k m) r)`
  returns `SNext k2 m2 (erased (Step k m k2 m2))`, `SHalt` (indexed by
  the empty stack) or `SStuck`. It calls no function at its own level;
  the list helpers recurse structurally.
- `advance` takes the state and `(erased (Trace (c0 :: nil) m0 k m))`.
  On `SHalt` it applies `trace-back` to `RANil`, takes the one `RACons`
  apart, and returns `Halted mf (erased (Runs m0 c0 mf))`
  (`machine.sl:182-189`). So the type of `advance` is the soundness
  theorem: whatever the machine halts with, the spec relates the program
  to it. `c0` and `m0` are pinned by the trace: the only trace a caller
  can start with is `TNil (c0 :: nil) m0` at state `(c0 :: nil, m0)`
  (`machine.sl:26`), and `Running` hands back a trace with the same
  `c0` and `m0` (`machine.sl:178`). It says nothing about a run that
  never halts or gets stuck.
- `run.sl`'s `drive` wraps `advance` in one `def-unique` continuation per
  step, as `proto/theorems/drive.sl` does. The driver is the only loop
  (§42: "It never recurses, so an unbounded interaction is the driver's
  loop over total functions."). Output [ran]: `halted after 151 steps;
  registers 0 #4 0 114 5 #4; heap [ 5 0 ] [ 4 #0 ] [ 3 #1 ] [ 2 #2 ] [
  100 #3 ]`.

Checks that the theorem has teeth [ran, files in the session
scratchpad]: swapping `c1` and `c2` in `step`'s `CSeq` case is refused
at `SNext`; inverting the loop test in both `Step` and `step`, so the
machine is consistent with itself but not with the spec, is refused in
`step-back` at `ExWhile`.

### F3. Completeness and termination (`complete.sl`)

- `Star` is the forward reflexive-transitive closure of `Step`;
  `star-trans` and `runs-star : (Runs m c m1) -> (Star (c :: k) m k m1)`
  are accepted. `runs-star`'s `CSeq` case makes two recursive calls on
  the two premises.
- `step-det` is accepted.
- `finish` iterates `advance` by recursion on an erased
  `(Star k m nil mf)`: `step-det` equates the machine's step with the
  derivation's first step, so the rest of the derivation is a subterm.
  On the empty stack the derivation's `StarRefl` case is refuted by the
  step itself (`(absurd (StarRefl _ _) s)`). This is the Bove–Capretta
  shape of 05 F4, here over the same `advance` the driver uses.
- `run-total : (many (Cmd) c0) (many (Mem) m0) (erased (Mem) mf)
  (erased (Runs m0 c0 mf) spec) -> (many (Agrees c0 m0 mf) a)`, where
  `AgreeHalted` carries `(many mf is r)`. With determinism, the machine's
  result is the spec's. `total_demo.sl` writes one derivation out at top
  level and prints `(AgreeHalted _ _ _ $ MkMem (Cons _ (VNum 7) $ Nil _)
  $ Nil _)` [ran, also `--no-extern` and `slc --interpret`]. As 05 F4
  says of this shape, a caller needs a `Runs` derivation from somewhere.
- `AgreeStuck` is still a possible result. Refuting it needs progress:
  the helpers return `NthNo`, `SetNo`, `OpNo` and `PickNo` with no
  evidence, so nothing connects a failure to the derivation. I did not
  do this (§3 Q2). So as built, the completeness half proves only "if
  this machine halts, it halts with `mf`, and it halts or sticks within
  the derivation's step count"; a machine that always sticks satisfies
  it too.

### F4. What the checker refused, and why

1. **A closure invariant at a fixed level, with no decreasing argument**
   (`ho_fixed_bad.sl`): the state holds `(erased (Fn L (erased (Mem) mf)
   (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv)`.
   Extending it after a step means a new closure at `L` calling `inv` at
   `L`: "same-level call to `inv` decreases no subterm argument". This
   matches 03 F4.1. It is the missing decrease that is refused, not the
   fixed level: giving the closure type a `(subterm erased (Nat) j)` and
   an `(erased (Eq (Nat) j n) e)`, with `n` the erased step count kept in
   the state, lets `inv2` at `L` match `e` against `Refl` and call `inv`
   on `n`, a subterm of `(Succ n)`. The stepper, at a level minted after
   `L`, applies it at a halt. `ho_counter.sl` is accepted by the
   reference, under `--no-extern` and by `slc --interpret`, and halts a
   small loop with `Halted` [ran in review].
2. **A closure invariant at a packed level.** If the state packs
   `(erased (Level) L)` with `inv` at `L`, each step can `def-lvl` a fresh
   `L2` and build `inv2` at `L2` calling `inv`: accepted
   (`ho_exist_build.sl`). But the stepper cannot apply it at a halt:
   "`L` was not in scope when level `(level-of adv-ho)` was minted"
   (`ho_exist_use_bad.sl`). §17: "A function may call a function of a
   strictly lower level"; §18: for `(prove-predates x L)`, "`x` must have
   an introduction order (§5) earlier than `L`'s", and "`L` must be an
   entry created by `def-lvl`, or a `let` binder forwarding from one".
   My reading: the packed `L` is bound inside the stepper's body, after
   the stepper's level, and a `Predates` proof packed beside it could not
   be renewed at each step for a freshly minted `L2`, so this shape
   cannot be applied by fixed-level code. Item 1's counter makes packing
   the level unnecessary. The trace of F2 is the same closure
   defunctionalized: `step-back` is the code of each closure, and
   `Trace` is the list of them.
3. **Numerals in an erased derivation** (`total_demo.sl`, first draft):
   `RSet ... 0 ...` was refused against `(SetNth ... (Zero) ...)`, with
   the note that `0` "is a numeral literal, opaque to the checker". §45:
   "`3` is not `(Succ (Succ (Succ (Zero))))`." A register index that
   proofs inspect has to be written `(Zero)` or `(Succ ...)`, or exposed
   with `unary` (§49). At run time `nth-p` matches literals as usual.
4. **Style warnings**: lopsided `match` and unmarked same-level calls;
   fixed by `let-match` and `notail`. `Exec` and `SCons` clashed with
   prelude names (warning only); renamed.

Apart from these, every definition was accepted as first written (the
author's report; the review cannot check it).

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
helper needs its own result type carrying the relation (`NthOut`,
`SetOut`, `OpOut`, `PickOut`, `StepOut`). I found no generic
"value with proof" wrapper, since `(Nth A xs i)` cannot be passed
unsaturated (§17: "There is no currying, for functions or for
constructors."). Long positional constructor telescopes (`RWrite` has 15
fields) are the main readability cost; patterns are counted by hand.

### F6. Cost of checking and running

[ran, one machine, single runs]: the reference takes 0.44 s on a
one-line file, 0.53 s on `std/list.sl spec.sl machine.sl complete.sl`;
`slc --interpret` 0.26 s and 0.33 s. Running 7821 steps takes 1.5 s in
the reference interpreter, 0.56 s under `slc --interpret`, and under
0.01 s compiled (`--build`); 26021 steps take 11.9 s, 3.6 s and 0.05 s.
The growth is probably the list heap, which every step walks. Peak
memory stays 22–41 MB, consistent with the erased trace not being built
at run time, which erasure (§14, §27) already implies.

## 3. Options

### Q1. Shape of the erased invariant

1. **Erased trace plus a per-step backward lemma** (built). *Pro:* first
   order, accepted, and the per-rule lemma is local and non-recursive
   once the spec is lifted to stacks. *Con:* the erased trace is, as a
   proof term, as long as the run; being erased, it is not built at run
   time [F6]. *Cost:* 41 lines here.
2. **Closure invariant with a packed level.** *Con:* cannot be applied
   by the stepper (F4.2). Not viable as far as I can see.
3. **A first-order "derivation under construction"**: an erased context
   of `Runs` frames, filled as commands finish, so the halt reads off the
   derivation with no fold. *Pro:* no trace. *Con:* needs one frame type
   per spec rule with a pending premise, and a plug lemma per frame.
   *Untested.*
4. **Small-step as the spec.** Take `Step`/`Star` as the spec and drop
   `Runs`. *Pro:* soundness is immediate (the trace is the derivation).
   *Con:* determinism and composition are then lemmas about `Star`.
   For runs that end on the empty stack the two agree here (`runs-star`
   one way; `trace-back` the other, `Trace` being `Star` read backwards),
   so this looks like a presentation choice.
5. **Closure invariant at a fixed level with an erased step counter**
   (F4.1, `ho_counter.sl`, added in review). *Pro:* no `Trace` type and
   no fold; the halt applies the closure to `RANil`. *Con:* a ghost
   counter and an `Eq` argument in the closure type; it still uses
   `step-back` and `RunsAll`. *Cost:* about the same as option 1.

### Q2. Total correctness ("never stuck")

1. **Positive failure evidence**: `NthNo` carries a `NoNth` derivation,
   and each failure site in `run-op` and `pick` refutes the given step
   with `nth-fn`. I count 26 failure sites. *Cost:* perhaps 60–80 lines.
2. **A well-formedness invariant** (register count, pointer validity,
   value shapes) carried in the state, under which failure sites are
   unreachable. This is type soundness of the object language. *Cost:*
   larger; it is the shape the full Sleight machine would need anyway.
3. **Accept "halted with the spec's result, or stuck"** (built).

### Q3. The implementation's heap

1. **`many` lists with functional update** (built). Simple; quadratic.
2. **The prelude's unique `Array`** (§44). Its API is indexed by the same
   `Nth`/`SetNth` relations this spec uses (`array-place`, `array-swap`),
   so the proofs could carry over. The machine state becomes unique and
   each `def-unique` continuation captures it. *Untested.*
3. **Abstract addresses** as 02 recommends (A1). Here an address is a
   position, which a spec of Sleight would not want. *Untested.*

## 4. Decisions for the owner

1. **Is "spec as relation, stepper returns an erased derivation at halt,
   invariant as an erased trace" the pattern to scale up?** Recommended:
   yes, as a working hypothesis: it is first order and compiled at first
   attempt. A fixed-level closure with an erased counter (Q1.5) is an
   accepted alternative, so the choice between them is one of
   presentation. Everything in the compiler-route proposals that relies
   on a certified stepper depends on one of the two.
2. **Should the level rules allow a function to apply a closure whose
   level is packed in its argument?** I do not propose a change. As
   DESIGN.md stands (§17, §18), such a closure can be built but not
   applied (F4.2). A closure at a fixed level with a decreasing erased
   argument works instead (F4.1), so certified steppers do not depend
   on this.
3. **Is "never stuck" a target for the formal spec's own machine?** If
   yes, Q2.2 (a typing invariant) is the route that also serves type
   soundness; Q2.1 is cheaper for a toy.
4. **Should the next spike use the unique `Array` heap and abstract
   addresses (Q3.2, Q3.3)?** Recommended: yes, before scaling, since 02
   recommends one, and owner statement 6 of the brief (an earlier
   session's paraphrase) says the owner suspects the spec's run should be
   a mutating heap machine from the start.

## 5. Rough edges in DESIGN.md (questions, not resolutions)

1. §17, §18 with §24 item 2 ("a function, of `Fn` or `UniqueFn` type" is
   first-class data): a function stored in data whose level is packed
   beside it, as an erased `(Level)` field, can be held and extended but,
   as far as the spike found, not called by code whose level was minted
   earlier (F4.2). §57 shows the factory pattern for one direction;
   DESIGN.md does not say whether the other direction is meant to be
   impossible. This did not block the spike: a fixed-level closure with a
   decreasing erased argument works (F4.1).
2. I found no contradiction in DESIGN.md while doing this spike.

## 6. Unverified claims

- That Q1.3 (a derivation context) would work, and its size.
- That no other placement of levels lets a stepper apply a packed-level
  closure (F4.2); the two shapes above were tried, plus the fixed-level
  counter of F4.1, which avoids packing.
- The `--build` timings of F6 were not re-run in review.
- The Q2.1 line estimate and the count of 26 failure sites.
- That the prelude's `Array` API would carry these proofs over (Q3.2).
- That the technique scales to Sleight's own machine: rule count, frame
  kinds, `at`/cell reading-back and the oracle of 02 were not modelled.
- Timings are single runs on one machine; `_build/release/slc` was used
  as found, without checking which commit it was built from.

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
