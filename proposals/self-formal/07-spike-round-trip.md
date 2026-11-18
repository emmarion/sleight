# 07. Spike: proving the §29 round trip with a suspendable checker

Written overnight by a Claude agent as a proof-technique spike. It is a
proposal and an agent's reading. Nothing in it is approved, and where it
and DESIGN.md disagree, DESIGN.md is right.

Tags: **[D]** DESIGN.md, quoted; **[C]** compiled or run. Unless marked
otherwise, files are under `proto/roundtrip/` and were run with
`_build/default/bin/main.exe` at commit 669b328 (no change to `bin/`,
`lib/`, `src/`, or `self/` since, up to ad07c35, 07692f2, c236135, e0aaf2c,
fb2c533, 10bd85d, 13ca61f, and 634e3ee), and also with slc
(`_build/release/slc`; `slc --interpret`, `slc --goal`).
**[A]** marks my own reading or proposal. The only owner items the body
mentions are the brief's statement 3, in decision 4, and the hypothesis
H of its statement 4, in §1; both are an earlier session's paraphrases.

## 1. Summary

- [C] A toy language with the round trip works end to end, with no fuel
  anywhere. It has top-level `Let t` (run at check time, giving a
  `Settled` value), `Assert i c` (a `comptime-match`: it reads entry i's
  stored value, checks the constructor, and exports a fact), and
  `Need i c` (a later check that consults only the facts, never the
  value). The spec has an inductive `Elab` with evaluation premises, a
  positive `Fails`, and a small-step `Step` relation. The checker emits
  "evaluate this" by moving into a `Waiting` state. Each `Program`
  step is one checker step: one machine step while `Waiting` (the step
  whose machine step halts also resumes the checker, or rejects if the
  run is stuck), and otherwise one statement, or the acceptance once no
  statement is left. The
  final `Verdict p` carries an erased `Elab [] p` or `Fails [] p`.
  Exclusivity (`Elab ∧ Fails → False`) is proved. Its proof uses
  determinism of evaluation (`step-det`, `runs-det`, `evals-det`) and
  of every lookup the rules use; with one extra, nondeterministic
  `Step` rule, some program has both derivations (F4).
- [C] Both the reference and slc accept the whole thing, run it, and
  report `--goal proved: PASS` for the packaged statement. Four
  deliberately wrong versions of single components are refused at the
  faulty proof term. Each is a standalone function, not wired into the
  checker: two have the signature of `check-assert` and `check-need`,
  and two stand for one case of `mstep` and one transition of `cstep`.
  Example: skipping the fact check in `Need` gives "expected
  `(Nth (Ent) es i (MkEnt v (KIs ct)))`, got `(Nth (Ent) es i (MkEnt v k))`".
- How the suspended state is represented (the spike's key question). A
  suspended checker records "I am deriving
  `Elab [] p0`, waiting on `Evals` of `t`" as two nested,
  defunctionalized derivation contexts. They are both erased fields of
  the `Waiting` state.
  - `Ctx p0 es p`: "a derivation for `es ⊢ p` plugs into one for
    `[] ⊢ p0`". Each frame holds the non-recursive premises already
    established.
  - `Reach (Ev t env []) m`: "a run from `m` extends to a run from the
    initial state".
  [A] One `Ctx` serves both `Elab` and `Fails`. That works because
  `Fails` mirrors `Elab`: each rule with a recursive premise has a
  "fails later" form with the same earlier premises.
- [C] A second implementation compiles too. It keeps the elaborator in
  direct style and replays from the start with a proof-carrying oracle
  of answers (the replay half of 03's option (e), without its inline
  bursts, and replaying the whole program rather than one form). It
  meets the same goal. Its price
  is a proof-producing decidable equality on requests, so that an
  answer can be used as a premise for the request at hand.
- [C] The packaged statement is only partial correctness plus
  exclusivity, and the exclusivity field is a lemma about the spec
  alone: it mentions no part of the implementation. A stepper that
  always returns `More` also passes the goal (`spin_vacuous.sl`), and
  the `why` string a `Rejected` carries is unconstrained. A
  `step` that calls itself is refused (a same-level self-call
  "decreases no subterm argument", §17, §48;
  `proto/review4/07_loop_step_bad.sl`). Completeness, or
  termination under H (the brief's statement 4: that every accepted
  compile-time form's spec run halts), is the main missing piece.

## 2. Findings

### F1. What DESIGN.md says about the round trip

- §27: a run-position form "runs as soon as it has been elaborated,
  before the code after it is checked: it is elaborated, its erased
  positions are stripped, the evaluator runs the code, and its results
  become `Settled` with the resulting values (§29)."
- §29: "Checking a run-position form is a dialogue. The elaborator
  checks the form and produces code with the erased positions removed.
  The evaluator runs that code. The resulting values come back to be
  stored (§5) and embedded as constants. Round trips nest". Also: "Every
  fact derived from a stored value, that is, a `comptime-match` and
  everything that follows from the fields it binds, relies on the
  evaluator having evaluated correctly."
- §29: "The checker never evaluates." "The engine of §7 reads no stored
  value." §7: "Canonicalization never reads a `Settled` entry's stored
  value." §7: "A fact verified by a `comptime-match` in run position
  holds afterwards".
- §28: `comptime-match` "asserts, at elaboration time, that `x` is a
  `Settled`, non-erased value headed by `C`. It is an error otherwise."
  "On a mismatch, the error prints the expected constructor and the
  actual value".

[A] The toy keeps these properties. `Let` is the only rule with an
evaluation premise. `Assert` reads a stored value (`Nth` plus `Head`)
and does not evaluate. `Need` reads only the fact. Program 1 below is
rejected even though its value is `Succ`-headed, because no `Assert`
exported the fact.

### F2. The toy (files and sizes) [C]

| file | lines | content |
|---|---|---|
| `spec.sl` | 178 | syntax (`Tm`, `Stmt`), machine states, `Step` (9 rules), `Runs`, `Reach`, `Vals`, `Evals`, `Sticks`, `Head`, `CNe`, `NotIs`, `Elab` (4 rules), `Fails` (8 rules), `Verdict`, `Turn` |
| `goal.sl` | 9 | the statement as a `goal` (below) |
| `det.sl` | 123 | determinism lemmas and `exclusive` |
| `impl.sl` | 151 | proof-producing lookups, the CEK `mstep` returning `(erased (Step s o))`, `reach-runs`, `Ctx` with `plug-elab`/`plug-fails`, `CState`, `cstep` |
| `replay.sl` | 127 | the replay variant: decidable equality with proofs, direct-style `elab-r`, `RState`, `rstep` |
| `drive.sl` | 61 | test programs and one generic `Program` driver for both variants |
| `proof.sl`, `proof_replay.sl` | 7 + 7 | `qed` for each variant |
| `*_bad.sl`, `spin_vacuous.sl` | 21 + 10 | refusal tests, and the vacuity check |

The statement (`goal.sl`), with the state type existentially packaged:

```scheme
(many MkCertified : (erased (TyCtor ((List $ Stmt) p) -> Type) S) (erased (Level) L)
   (many (Fn L (many (List $ Stmt) p) -> (many (S p) s)) init)
   (many (Fn L (erased (List $ Stmt) p) (many (S p) s) -> (many (Turn S p) t)) step)
   (erased (Fn L (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d)
      (erased (Fails (Nil (Ent)) p) f) -> (erased (False) no)) excl) -> (Certified))
```

`Turn S p` is `More (S p)` or `Fin (Verdict p)`. The statement mentions
only spec types, so both implementations prove the same goal.

Runs (`main.exe spec.sl det.sl impl.sl replay.sl drive.sl -- which how`,
where `how` 0 is the zipper and 1 is replay):

| which | program | zipper | replay |
|---|---|---|---|
| 0 | two lets (one reading the first's entry), asserts, and needs | accepted, 26 steps | accepted, 22 steps |
| 1 | `Let 3; Need 0 Succ` (no assert) | rejected: fact not known, 4 | same, 4 |
| 2 | `Let 0; Assert 0 Succ` | rejected: other constructor, 4 | same, 4 |
| 3 | stuck run `(App (Num 1) (Num 2))` | rejected: stuck, 6 | same, 7 |
| 4 | unbound variable in a run | rejected: stuck, 2 | same, 3 |
| 5 | `Assert 1 …` with one entry | rejected: no such entry, 4 | same, 4 |
| 6 | `Let omega` | runs until killed; 22 MB at 4 s and at 12 s | same |

`slc --interpret` gives the same outputs and step counts for programs 0
to 5 in both variants. Both checkers print `--goal proved: PASS` for
`spec.sl goal.sl det.sl impl.sl proof.sl`, for the replay set
`spec.sl goal.sl det.sl impl.sl replay.sl proof_replay.sl` (`replay.sl`
uses `impl.sl`'s lookups and `mstep`, and fails without it), and for
`spec.sl goal.sl det.sl spin_vacuous.sl`. The refusals are run as
`spec.sl impl.sl X_bad.sl`.

### F3. How the suspended state carries the partial derivation [C]

```scheme
(many Waiting : (erased (List $ Stmt) p0) (many (List $ Ent) es) (erased (Tm) t) (many (List $ Stmt) rest)
   (erased (Ctx p0 es (Cons (Stmt) (Let t) rest)) c)
   (erased (List $ Val) env) (erased (Vals es env) ve)
   (many (MSt) m) (erased (Reach (Ev t env (Nil (Frame))) m) r) -> (CState p0))
```

- Elaboration hole. `c : Ctx p0 es (Let t :: rest)` says that a
  derivation of `Elab es (Let t :: rest)` or `Fails es (Let t :: rest)`
  can be plugged to one for `[] ⊢ p0`. `Ctx` has `CTop` for the root
  and one constructor per (rule, recursive premise): `CLet`, `CAssert`,
  and `CNeed`. Each frame holds that rule's other premises, which are
  already established. `plug-elab` and `plug-fails` rebuild the root
  derivation. The frames' rules are applied, in erased code, only when
  the checker finishes, and that is the only use of the frames.
- Evaluation hole. `Reach init m` is the snoc-list of `Step … (Go …)`
  proofs so far. When the machine halts, `reach-runs r (RunHalt st)`
  gives `Runs init res`. If `res` is a value, the checker pushes
  `CLet c (MkEvals … runs)` and returns to `Checking`. If it is stuck,
  `plug-fails c (FLetStuck …)` gives the rejection.
- Every `CState p0` value is a valid partial derivation by construction,
  because its erased fields can be built only by the rules, provided
  the erased logic has no closed proof of `False`, which nothing here
  shows (second review notes). The theorem needs no separate invariant
  and no `init` state hypothesis.
- [A] The `Fails` rules mirror the `Elab` rules: `FLetRest`,
  `FAssertRest`, and `FNeedRest` carry the same earlier premises as
  `ElLet`, `ElAssert`, and `ElNeed`. That is why one `Ctx` plugs into
  both. Such a `Fails` fixes the order of premises: a rule "fails at
  premise k" only after premises 1 to k−1 hold. So a positive `Fails`
  in this shape takes a side on 01's decision 5 (order of
  elaboration). This is my reading.
- [A] Nesting. In the toy, a round trip occurs only at the top of the
  statement list, so `Ctx` is one spine. Under §29's "Round trips nest",
  a run can be requested while elaborating a sub-form at any depth. I
  expect the same construction would then give `Ctx` one frame per
  (rule, recursive premise position) of the whole `Elab` rule set,
  which is its derivative in the zipper sense, and a `Waiting` could
  then sit under any frame. I have not built this.

### F4. Where the proof effort went [C]

- The spec, at 178 lines, is larger than the checker logic.
- Determinism and exclusivity take 123 lines.
  - Generic list lemmas (`nth-det`, `nth-nonth`, `setnth-det`): about 25.
  - `vals-det`, `step-det`, `runs-det`, `head-det`, `evals-det`, and
    `evals-sticks`: about 60.
  - `exclusive`: about 35. It is induction on `Fails`, with a
    determinism lemma for each shared premise whose outputs a case must
    equate (`FNeedRest` needs none), and `nth-nonth` or `evals-sticks`
    where a premise of one derivation contradicts one of the other.
  - Exclusivity of `Let` needs `evals-det`, which needs `vals-det`,
    `runs-det`, and `step-det`, which in turn needs `nth-det` and
    `nth-nonth`. Without determinism of the evaluation relation, this
    proof does not go through at `FLetRest`/`ElLet`: two different
    values put the two derivations in different contexts. Exclusivity
    is then false for at least one nondeterministic variant [C, second
    review]: `proto/review2/07_nondet_spec.sl` is `spec.sl` plus a rule
    `SNumUp` letting `Num n` also step to `n + 1`, and with it
    `proto/review2/07_nondet_both.sl` builds both an `Elab` and a
    `Fails` for `Let (Num 0); Assert 0 CSucc` (`det.sl` is then refused
    at `step-det`). This matches 05's expectation that T3 "needs the
    spec to be deterministic".
- The proof-carrying checker. Each lookup returns its relation (`Find`
  carries `Nth` or `NoNth`, `head` returns `Head`, and `ctor-dec`
  returns `CSame` or a `CDiff` carrying `CNe`). The suspension machinery (`Ctx`, the two
  `plug` functions, `Reach`, and `reach-runs`) is about 45 lines.
- The evaluator proof is trivial here, because the spec's evaluation
  relation is the same machine as the implementation's `mstep`: `mstep`
  returns `(erased (Step s o))` per step, and `Reach` is a list. [A] If
  the spec's run were big-step, or a different machine (02's heap
  machine), a simulation between the two would be the largest single
  proof. I did not attempt it.
- The reference forced and refuted on its own every cross-constructor
  case whose indices clash. Examples are `let-match` on `Step`
  derivations whose indices differ, and `(match erased e _)` on
  `Eq (Out) (Halt …) (Go …)`. Cases whose indices do not clash needed a
  proof: `SVar` against `SVarNo` in `step-det` is refuted by `nth-nonth`
  (`det.sl:40`, `:44`). The
  author reports that most lemmas were accepted on the first compile;
  that history was not re-checked.

### F5. What the reference refused, and why [C]

- `det.sl`, first version. A bare `ne` as a final expression is
  refused; with today's `det.sl` edited back that way, the message is
  "expected `(False)`, got `(CNe c2 c2)`" at `FAssertHead` and
  "... got `(CNe c c)`" at `FNeedFact`. The fix is
  `(match erased ne _)`, a match whose every constructor is refuted,
  which "produces its declared result" (§25, §21). As I read §51, its
  refutation rule covers absurd bodies only, and `exclusive` is not
  `absurd`.
- `replay.sl`, first version. "`p0`, declared `erased`, used in a
  non-erased position." The draft was not kept; the message reproduces
  with `p0` passed for `src` at `replay.sl:116`. Replay re-elaborates
  the whole source, so its state must hold the source at runtime:
  `(many p0 is src)`. The zipper needs only the remaining statements at
  runtime.
- `drive.sl`. Calling the step parameter from `drive`'s body with a
  `Predates M P` gave "value mismatch: expected `PA`, got `P`", since
  the current level is `PA`. With no annotation the call is accepted:
  §48 builds `(predates _)`. Written out, either `(predates _)` or
  `(predates p)` with a `Predates M PA` draws the warning "unnecessary
  `(predates _)`; drop it" (re-checked).
- Intended refusals:
  - `need_bad.sl` skips the fact check (shown in §1).
  - `assert_bad.sl` skips the constructor check: "expected `(Head v ct)`,
    got `(Head v ct2)`".
  - `eval_bad.sl` makes a step drop the argument: the expected
    `(Go (Ev b env rest))` does not match `SCall`'s
    `(Go (Ev b (Cons (Val) v env) rest))`.
  - `settle_bad.sl` settles a `Let` to `0` without running it:
    `RunHalt` expected `(Step (Ev t env (Nil (Frame))) (Halt (RVal (VNum 0))))`.
- Warnings (fixed): "lopsided `match`" (flattened to `let-match`), and
  "same-level call … is unmarked; mark it `notail`". Not re-checked;
  the current files run with no warnings.

### F6. The replay variant [C]

`elab-r : es (subterm p) (List Answer) -> (RTurn es p)` is
direct-style structural recursion on the program, like `t1_toy.sl`.
`RTurn` is `RElab`, `RFails`, or `RAsk t env`. An `Answer` is
`MkAnswer t env r (erased (Runs (Ev t env []) r))`.
- At a `Let`, the elaborator pops the next answer. It must prove that
  the answer is for this request: `tm-eq` and `vals-eq` return
  `(ErasedMaybe (Eq …))`. On `ESome` it uses the stored `Runs` as the
  premise. A missing or mismatched answer gives `RAsk`.
- Every recursive call site re-wraps three outcomes, for example
  `RElab d → ElLet …`, `RFails f → FLetRest …`, and `RAsk` passed
  through. This is one more case per call site than t1_toy.
- `rstep` runs `elab-r` from the start on each `Replay`. On `RAsk` it
  runs the machine (with `Reach`) and appends the answer. [A] So the
  elaboration work is about (number of runs) × (program length), plus
  the equality checks: quadratic when the runs grow with the program.
  This is an estimate from the code, not a measurement.
- About 50 of its 127 lines are the decidable equality.
- [A] In full Sleight a request is roughly (stripped code, the store
  Σ), so this equality covers code and heap. The alternative is to
  index the oracle by derivation position, so that no comparison is
  needed. But then extending it needs the position of the hole, and
  that is the `Ctx` zipper again.

### F7. What the statement does not say [C]

`spin_vacuous.sl` is a stepper whose `step` always returns `More`. It
passes the same goal. So the theorem is: whatever verdict `step`
returns, from any state, is a correct one, and accept and reject cannot
both hold. It does not say that the loop reaches a verdict when the
spec has one. The reason string of `Rejected` is free text, so a
`step` may give any reason with a correct `Fails`. Nor does it cover
`drive.sl`: the driver, which reaches `cstep` and `rstep` through its
own wrappers `zipper` and `replay` rather than through a `Certified`
value, and the text it prints for each verdict, are outside the proved
statement. A function given only a `Certified` cannot, in the two
shapes tried and as I read §18, call its `init` or `step`: their level
`L` is packed, and the call is refused with "`L` was not in scope when
level `(level-of first-turn)` was minted"
(`proto/review6/07_cert_fn_bad.sl`), as 06 F4.2 found for packed-level
closures; and a `Predates` from the value to the function's level,
written out in the function, is refused too, the value being a
parameter introduced after that level ("`c` was not in scope when level
`F` was minted", `proto/review8/07_cert_fn_self_bad.sl`; reference,
`--no-extern`, and `slc --interpret`) [C, round 8]. Given also a
`Predates` from the value to the function's
level, which the top level proves for a value built before that level
is minted, the function calls both, through `prove-subterm` and
`predates-subterm` (`proto/review7/07_cert_predates.sl`; reference,
`--no-extern`, and `slc --interpret`) [C, round 7]. Destructured at the
top level before the driver's levels are minted, the same value drives
program 0 to "accepted after 26 Program steps"
(`proto/review6/07_cert_drive.sl`; reference, `--no-extern`, and
`slc --interpret`) [C, sixth review]. Program 6 has a diverging run, so
(by my reading, not proved) it has neither derivation, since `Evals`
and `Sticks` both need a finite `Runs` and `Step` is deterministic; the
loop runs at constant memory. That is consistent with "no verdict if
and only if a run that the checker reaches diverges" (a program rejected before a diverging
`Let` still gets a verdict). For the zipper, both directions can be
read from the code, though neither is proved: a `Waiting` state leaves
only on `Halt`, so a diverging run gives no verdict; and each other
step either ends with a verdict or handles one statement, so if every
run the checker reaches halts, a verdict comes after finitely many
steps. [A] The divergence comes from the toy's untyped object
language, which has no levels; whether a run-position form of full
Sleight can diverge at all bears on §17 ("Termination rests on
levels"), see §5 below.

## 3. Options

### Q1. Shape of the resumable certified checker

- **(a) Derivation zipper: a CPS or defunctionalized state machine.**
  - Design: the checker state is the elaboration context (`Ctx`) plus,
    while waiting, the evaluation context (`Reach`), both erased. It
    advances by one total step per `Program` step.
  - Pros:
    - No fuel and no replay: each statement is checked once (the toy's
      list lookups still cost O(entries) per statement).
    - One frame type covers acceptance and rejection.
    - The derivation is assembled once, at the end.
    - Compiled here.
  - Cons:
    - Every elaborator function that can reach a round trip becomes
      frames. [A] In full Sleight I expect that to be most of
      elaboration (nested run positions, §15's hoisted arguments, and
      macro expansion, which also runs code, §62).
  - Risk: frame count. There is one frame per (rule, recursive premise)
    pair, so it grows with the total number of recursive premises.
  - Cost [A]: high for slc; natural for a new kernel written this way.
- **(b) Direct style plus replay with a proof-carrying oracle.**
  - Design: as in F6.
  - Pros:
    - The elaborator stays recursive, which is how I read slc's main
      block to be written. Its compile-time runs are inline calls to
      `run-code`/`eval` with fuel (`self/elab-main.sl:159`, `443-462`).
    - Compiled here.
  - Cons:
    - It needs decidable equality with proofs on requests, which [A] I
      expect to cover heaps in full Sleight.
    - Work is about quadratic in the number of runs (F6, an estimate).
    - Σ effects (gensym, expansion count, macro-world updates) must
      come back from the oracle, or be replayed identically (03 Q1(e)).
    - Every call site re-wraps a third outcome.
  - Cost [A]: medium to high. My reading of the toy is that most of
    the cost would be intrinsic derivations everywhere, which (a)
    would need too. The toy is too small to establish this.
- **(c) Inline bursts with replay only on overflow (03's hybrid).**
  - Design: (b), but the machine runs inline for B steps, and only a
    run longer than B triggers `RAsk`.
  - Pros: replay is rare.
  - Cons [A]: inline bursts are bounded iteration. A burst that runs
    out must yield `RAsk`, so I expect the proof to be (b)'s.
  - Untested.

### Q2. What the spec's evaluation relation is

- **(a) A small-step machine relation that the implementation steps
  through.**
  - Pros: the evaluator side of the proof is a list of step proofs
    (F4).
  - Cons: the spec reads as a machine. [A] DESIGN.md's own wording is
    a machine too (§31: "The semantics is that of a machine with
    unlimited stack and heap"), though not a small-step relation.
- **(b) Big-step, or a different machine.**
  - Pros [A]: big-step may read closer to §27's "the evaluator runs the
    code".
  - Cons: it needs a simulation proof from the implementation's
    machine. [A] I expect that proof to dominate the effort.

### Q3. Completeness (the missing piece)

- **(a) Bove–Capretta on per-source evidence.**
  - Design: a runner that takes erased evidence H(p0), for example
    a step-indexed `Runs` for each `Let`. It recurses on the erased
    count, using `step-det` to relate the machine to the evidence.
  - Pros: internal (05 F4 compiles the pattern).
  - Cons: as 05 says, a caller needs the evidence.
- **(b) A step relation `CStep s o` returned by `cstep`.**
  - Design: completeness becomes "a derivation implies a finite
    `CStep` chain to `Fin`".
  - Pros: it states what the driver does.
  - Cons: it is a second relation mirroring the checker.
- **(c) Leave it meta.**

## 4. Decisions for the owner

1. **Which resumable shape: zipper (Q1a) or replay (Q1b)?**
   - Recommended: zipper for a new certified kernel, and replay only if
     slc itself is retrofitted.
   - Why: both compile. Replay keeps slc's direct style, but it adds
     request equality (on terms and environments in the toy, and [A]
     probably on heaps in full Sleight) and re-elaboration work about
     quadratic in the number of runs (F6, an estimate). The zipper
     removes both, at the cost of rewriting the elaborator into frames;
     its list lookups still cost O(entries) per statement (Q1a).
   - Depends on it: 04's compiler-route choice, and 03 decision 3.
2. **Is the spec's compile-time run a small-step relation over the same
   machine the compiler steps (Q2a)?**
   - Recommended: yes, if the owner wants the evaluator part of the
     proof to stay small.
   - Depends on it: 02's machine design, and the size of the T5 proof
     in 05.
3. **Should `Fails` mirror `Elab` premise by premise ("fails at premise
   k after 1..k−1 hold")?**
   - Recommended: yes. One context then serves both. Exclusivity is a
     plain induction with or without the mirror shape: 05's
     `proto/theorems/t1_toy.sl` has an order-free `FPlusR`, which needs
     no `Elab` of the left operand, and its `exclusive` is also a plain
     induction, on the source term with no determinism lemma, where the
     toy's is on `Fails` with determinism lemmas.
   - Consequence: the spec then fixes the order of premises, which is
     01's decision 5.
4. **Must the packaged theorem include completeness?**
   - Recommended: yes, relative to per-source evidence (Q3a). Without
     it, a stepper that never answers satisfies the statement (F7).
   - Context: the brief's owner statement 3 (an earlier session's
     paraphrase) is that every source should provably be accepted or
     rejected; the packaged statement here does not give that.
   - Depends on it: 05 decision 5.
5. **Is a compile-time run that goes wrong a rejection?** The toy has
   `FLetStuck`.
   - [A] In typed Sleight, a run that gets stuck should not happen if
     the language is sound, so the toy's rule is a stand-in, not a
     proposal for the full spec. The nearest question for full Sleight
     is 05 decision 4, about crashes (§31: "A real run may crash where
     the host cannot represent what is asked of it"), which is a
     different kind of failure from a stuck term.

## 5. Rough edges in DESIGN.md (questions, not resolved)

- §29 says "Round trips nest: a form in run position runs before the
  form that contains it", and §27 says such a form "runs as soon as it
  has been elaborated, before the code after it is checked", and "the
  forms inside a form run before it does". So an inner run comes after
  its own elaboration and before whatever is "after it". What I could
  not find is which sibling items of one form count as "after it",
  that is, the order in which a form's items are elaborated. §6 says
  "The head is elaborated first", and §15 places each argument's
  hoisted binding "just before the statement or final form that
  contains the call", but neither orders two arguments. §50's "an
  argument (its parameter, given the arguments before it)" fixes what an
  argument is checked against, not when it is elaborated or run. [A] A
  zipper or a positive `Fails` in the mirror shape needs that order
  (F3). This adds to the evidence for 01's decision 5.
- §28: "On a mismatch, the error prints the expected constructor and
  the actual value". If rejections carry their reason (01 decision 4),
  the `Fails` rule for a mismatch must carry the value. The toy's
  `FAssertHead` carries `v` and its head. Whether the printed text is
  part of the spec is open.
- DESIGN.md does not mention a diverging run-position form. §27 says
  the form "runs as soon as it has been elaborated, before the code
  after it is checked", and §17 says "Termination rests on levels"
  ("Every call decreases a lexicographic order"); §33 says an erased
  proof function "is checked for termination like any other (§17)";
  §20 says "no function body can call into" the top level; §42 calls an
  unbounded interaction "the driver's loop over total functions"; §62
  caps expansions ("At most 10000 expansions run in one run"). These
  suggest that functions are meant to halt, but I could not find text
  saying outright that every compile-time run halts, or what a checker
  that never returns means for acceptance. With no fuel, the toy simply
  never finishes, but its object language has no levels (F7). This is
  the gap that F7 and 05's T4 discuss.

## 6. Unverified claims

- That the zipper construction scales to nested round trips by taking
  one frame per (rule, recursive premise). It is not built.
- That replay in full Sleight needs equality on (code, heap) requests,
  and that indexing the oracle by position brings back the zipper. This
  is reasoning, not code.
- That a simulation proof would dominate under Q2(b).
- That Q3(a) is writable for this toy: plausible from 05's `bove.sl`,
  but not written.
- The timings and memory figures are single runs on one machine (the
  review re-measured about 22 MB resident at 4, 8, and 12 s for both
  variants).
- That program 6 has neither derivation, and that "most of
  elaboration" in full Sleight would become frames.
- The work estimates (no re-elaboration for the zipper, about
  quadratic for replay) are read off the code, not measured.
- That slc's elaborator is "direct-style" throughout. I read only
  `self/elab-main.sl:159` and `443-462`, and 03's description of the
  block.

## Review notes

An adversarial review re-ran every acceptance, refusal, and goal claim
with `_build/default/bin/main.exe` and `_build/release/slc`, read
DESIGN.md in full, read every file in `proto/roundtrip/`, and checked
the cited slc lines. Errors found and changes made:

1. Header: named the slc binary used and noted that HEAD (ad07c35)
   has no code change since 669b328. "No owner decision is cited" was
   replaced, since decision 4 now mentions the brief's statement 3.
2. §1, F5: the four `*_bad.sl` files are standalone wrong versions of
   one component each, not wrong whole checkers; said so. All four are
   refused at the stated proof term, with the quoted messages, by both
   checkers (re-checked).
3. §1: added that the `excl` field is a spec-only lemma (any `S`
   discharges it with `exclusive`), and that a `step` that itself
   loops is refused (compiled: "same-level call to `step-top`
   decreases no subterm argument"). So the only vacuity found is a
   `step` that returns `More` forever, on some or all programs.
4. §1, F6: the replay variant is not quite 03's option (e): it has no
   inline bursts and replays the whole program, not one form.
5. F2: slc agrees on programs 0 to 5 in both variants, not only 0, 1,
   2, 3, and 5. Gave the exact file sets; the replay set needs
   `impl.sl` (without it: "unbound name `vals`").
6. F3: `CTop` is the root, not a (rule, premise) frame; "the root rule
   is applied only when the checker finishes" was ambiguous and was
   reworded. The nesting paragraph is now hedged as an expectation.
7. F4: "exclusivity fails" without determinism was reasoning, not a
   compiled result; hedged. The 05 citation now quotes 05's words.
   "Accepted on the first compile" is marked as unre-checked history.
8. F5: re-running the `ne` refusal at `FAssertHead` gives
   `(CNe c2 c2)`, not `(CNe c c)` (the second review found that
   `(CNe c c)` is what the `FNeedFact` site gives). The citation §51 was replaced by §25 and §21: §51
   covers absurd bodies, and `exclusive` is not `absurd` (my reading).
   The `predates` warning was re-checked, and an explicit correct
   `(predates p)` draws it too.
9. F6, Q1(a), Q1(b), decision 1: "linear work" was wrong for the toy
   (each statement's list lookups and `vals` are O(entries)); replaced
   by "no re-elaboration". "Quadratic" for replay is marked as an
   estimate. "Equality on heaps", "most of elaboration becomes
   frames", "most of the cost is intrinsic derivations either way",
   and "the simulation would dominate" are now marked [A] readings.
10. Q1(a): "frame count grows with (rules × recursive premises)" read
    as a product; it is one frame per (rule, premise) pair, a sum.
11. F7: added that the driver and its printed text are outside the
    proved statement; spelled out which direction of "no verdict iff
    some run diverges" is evident; marked "program 6 has neither
    derivation" as reasoning; noted that the divergence comes from the
    toy's level-free object language.
12. Decision 5: a stuck run is not 05 decision 4's crash (§31); reworded.
13. §5, first rough edge: §27 does say an inner form "runs as soon as
    it has been elaborated, before the code after it is checked", and
    that "the forms inside a form run before it does". The gap is
    narrower: the order of a form's items. Quoted both.
14. §5, last rough edge: added §17's "Termination rests on levels" and
    §62's cap, and that DESIGN.md never mentions divergence (searched).

Checked and found accurate: the six programs' outputs and step counts
(reference and slc); the three `--goal proved: PASS` sets; constant
memory on program 6; line counts; rule counts (`Step` 9, `Elab` 4,
`Fails` 8); the `goal.sl` and `Waiting` excerpts; that `det.sl` needs
only `spec.sl`, so exclusivity is over spec relations; that `goal.sl`
mentions only spec types; the DESIGN.md quotes in F1 and §5; and
`self/elab-main.sl:159` (`eval` with a `subterm many (Nat) fuel`) and
`443-462` (`run-code` and the `env-run-*` functions passing
`(env-fuel e)`).

Uncertain points:

- Whether §17's levels, with §10's `Type : Type` and no positivity,
  really keep every run-position form from diverging. If they do, the
  toy's divergent program 6 has no full-Sleight counterpart, and the
  completeness gap becomes "the checker answers whenever the spec
  does", not "diverging runs". Not settled here.
- Whether the mirror-shaped `Fails` fixes more of the order of
  premises than 01 decision 5 would choose; not examined.
- Which slc binary the original author used; the review used
  `_build/release/slc`.

## Second review notes

A second adversarial review read DESIGN.md in full and every file in
`proto/roundtrip/`, and re-ran at 07692f2 (no code change since
669b328) all six programs in both variants under the reference and
`slc --interpret`, the three `--goal proved` sets under both checkers,
program 6's memory (22 MB, flat, both variants), the four refusals, the
looping-`step` refusal, the two `ne` refusals, the `p0` refusal, and
the three `predates` variants of `drive.sl`. All matched except as
below. Errors found and changes made:

1. §1 said each `Program` step "runs one machine step and the checker
   resumes". A `Program` step is one `cstep`: a machine step while
   `Waiting`, otherwise one statement or the resumption after a halt.
   Reworded.
2. §1 said the four wrong components each have "the correct
   component's signature". Only `assert_bad.sl` and `need_bad.sl` match
   an existing function's signature (`check-assert`, `check-need`);
   `eval_bad.sl` is one case of `mstep` and `settle_bad.sl` one
   transition of `cstep`. Reworded.
3. §1 said exclusivity "needs" determinism (a [C] bullet stating a
   reading). Now "its proof uses", plus a compiled counterexample: F4's
   [A] "I expect exclusivity could then be false" is now [C].
   `proto/review2/07_nondet_spec.sl` (`spec.sl` plus a rule `SNumUp`)
   with `proto/review2/07_nondet_both.sl` builds both derivations for
   `Let (Num 0); Assert 0 CSucc`, and prints `(MkBoth _ _ _)`;
   `det.sl` against that spec is refused at `step-det` (`det.sl:48`,
   missing branch for `SNumUp`).
4. Vacuity, §1 and F7: besides a `step` that returns `More` forever,
   the `why` string of `Rejected` is unconstrained, so a correct `Fails`
   can come with any reason text. Added. F7 also now says that
   `drive.sl` calls `cstep` and `rstep` directly, not through a
   `Certified` value.
5. F5: the bare-`ne` message depends on the site; `(CNe c c)` is the
   `FNeedFact` one. Added, and first-review note 8 qualified.
6. §5, first rough edge: §6 ("The head is elaborated first") and §15
   (hoisted argument bindings placed "just before the statement or
   final form that contains the call") fix part of the order; added
   that neither orders two arguments.
7. §5, last rough edge: §42's "the driver's loop over total functions"
   was missing; it, with §17, suggests that functions are meant to
   halt. Added; the gap is now "not said outright".
8. Header: Oxford comma; noted the second review's commit. §1:
   "`Eval` of `t`" named no relation; now `Evals`. F4: `ctor-dec`
   returns `CSame` or `CDiff` (which carries a `CNe`), not `CNe`.

Points I am unsure of:

- Every "by construction" claim (F3) rests on Sleight's erased logic
  having no closed proof of `False`; with §10's `Type : Type` and no
  positivity, nothing in DESIGN.md or this spike shows that. The
  brief's owner statement 1 (an earlier session's paraphrase) says no
  consistency theorem is expected.
- F5's "first version" histories (the bare `ne`, the erased `p0`) were
  reproduced by editing today's files, not from the original drafts.
- That the replay variant cannot loop on a mismatched head answer: it
  would ask again and append, never dropping the bad answer. I read
  the answers as always produced in request order, so it does not
  arise here; not proved.

## Third review notes

A third adversarial review read DESIGN.md in full and every file in
`proto/roundtrip/` and `proto/review2/07_*`, and re-ran at c236135 (no
code change since 669b328): programs 0 to 5 in both variants under the
reference and `slc --interpret` (outputs and step counts as in F2);
program 6 (22 MB, flat over 9 s, both variants); the three
`--goal proved: PASS` sets and the replay set without `impl.sl` (FAIL)
under both checkers; the four refusals under both; the looping-`step`
refusal; both bare-`ne` refusals; the three `predates` variants of
`drive.sl`; and `07_nondet_spec.sl` with `07_nondet_both.sl`
(`(MkBoth _ _ _)`) and with `det.sl` (refused at `det.sl:48`, missing
`SNumUp`). All matched. Errors found and changes made:

1. §1 said a `Program` step is a machine step, a statement, "or the
   resumption after a run halts", as if resumption were a step of its
   own. In the zipper the step whose machine step halts also resumes
   the checker (program 1 takes 4 steps: start the `Let`, `SNum`,
   `SRetNil` with the resumption, and the `Need`). Reworded.
2. F4 said the reference refuted "every cross-constructor case on its
   own". `step-det`'s `SVar`/`SVarNo` cases, whose indices do not clash,
   needed `nth-nonth` (`det.sl:40`, `:44`). Narrowed.
3. F7 said `drive.sl` calls `cstep` and `rstep` "directly"; it calls
   them through its wrappers `zipper` and `replay`, passed to a generic
   `drive` as its `step` parameter. Reworded.
4. Q2: "(b) reads closer to DESIGN.md's prose" and "(a) the spec reads
   as a machine" as a con, with no source. §31 says "The semantics is
   that of a machine with unlimited stack and heap". Both are now [A],
   with §31 quoted.
5. F7's "no verdict if and only if some run diverges" is false as
   worded: a program rejected before a diverging `Let` gets a verdict.
   Now "a run that the checker reaches".
6. F2 table: Oxford comma in program 0's description. Header: names the
   third review's commit.

The theorem's type was checked against the claims: `MkCertified` takes
an existential `S` and `L`, an `init`, a `step` from any `S p` to
`More (S p)` or `Fin (Verdict p)`, and `excl`, which mentions only
`spec.sl` relations and is discharged by `exclusive` whatever `S` is.
Since `Verdict p` carries an erased `Elab [] p` or `Fails [] p`, every
`Fin` is correct from any state, and `init` is constrained by nothing.
Vacuous implementations that pass: a `step` that answers `More` on any
or all states (`spin_vacuous.sl`), with any `init`; and any reason
string in `Rejected`. A `step` cannot loop by calling itself at its own
level (refused, "decreases no subterm argument").

Points I am unsure of:

- That nothing other than these two kinds of vacuity passes; I found no
  third, but did not prove there is none.
- The `p0` refusal of F5 was reproduced only as "`src`, declared
  `erased`, used in a non-erased position" (`src` made erased); the
  quoted `p0` wording is the author's.

## Fourth review notes

A fourth adversarial review read DESIGN.md in full, every file in
`proto/roundtrip/` and `proto/review2/07_*`, and re-ran at e0aaf2c (no
code change since 669b328): programs 0 to 5 in both variants under the
reference and `slc --interpret` (outputs, exit codes, and step counts as
in F2; program 0's 26 zipper steps are 6 statements, 19 machine steps,
and the acceptance, and its 22 replay steps are 3 replays and 19 machine
steps); program 6 (22 MB at 4 s and at 10 s, both variants); the three
`--goal proved: PASS` sets and the replay set without `impl.sl` (FAIL)
under both checkers; the four refusals under both, with the quoted
messages; a looping `step-top` (refused, now saved); both bare-`ne`
refusals; the three `predates` variants of `drive.sl`; `07_nondet_both.sl`
under the reference and `slc --interpret`, and `det.sl` against
`07_nondet_spec.sl` (refused at `det.sl:48`); the line and rule counts;
the `goal.sl` and `Waiting` excerpts; and `self/elab-main.sl:159` and
`443-462`. All matched. Errors found and changes made:

1. §1 said a `Program` step that is not a machine step is "one
   statement". The last step of an accepted program handles no
   statement: it is `cstep` on an empty list, giving `Accepted`
   (program 0: 6 + 19 + 1 = 26). Added.
2. §1 said "A `step` that itself never returns is refused". What was
   compiled is a `step` that calls itself; that no accepted `step` can
   fail to return is §17's intent, not something this test shows. Now
   "calls itself", with the test saved as
   `proto/review4/07_loop_step_bad.sl` (earlier reviews did not save
   it).
3. Decision 3 gave "exclusivity is a plain induction" as a reason for
   the mirror-shaped `Fails`. 05's `t1_toy.sl` has an order-free
   `Fails` (`FPlusR` needs no `Elab a`) and its `exclusive` is the same
   plain induction (re-run: accepted). Reworded, so the reason left is
   the shared context.
4. §1: "each rule has a 'fails later' form"; `ElNil` has none, having
   no premise. Now "each rule with a recursive premise".
5. §5, last rough edge: added §33 ("checked for termination like any
   other (§17)") and §20 ("no function body can call into" the top
   level) to the evidence; neither says outright that a compile-time
   run halts (searched `diverg`, `halts`, `infinite`, `loop`, and
   `terminat`: the only matches are §17, §18, §33, and §42, all
   quoted).
6. Header: "the only owner item mentioned" is statement 3, but the
   second review notes mention statement 1; now "the body mentions".

Points I am unsure of:

- That nothing other than the two vacuities found (a `step` answering
  `More` forever, and free reason text) passes the goal; I found no
  third.
- Whether a mirror-shaped `Fails` fixes an order the toy can observe:
  every premise in the toy depends on the one before it, so no two
  premises can fail independently. With independent premises and a
  diverging run (F7), the chosen order would decide whether a verdict
  exists; that is a reading, not compiled.

## Fifth review notes

A fifth adversarial review read DESIGN.md in full, every file in
`proto/roundtrip/`, `proto/review2/07_*`, and `proto/review4/07_*`, and
re-ran at fb2c533 (no code change since 669b328): programs 0 to 5 in
both variants under the reference and `slc --interpret` (outputs, exit
codes, and step counts as in F2, identical between the two); program 6
(22 MB at 4 s and at 10 s, both variants); the three
`--goal proved: PASS` sets and the replay set without `impl.sl`
("unbound name `vals`") under both checkers; the four refusals under
both, with the quoted messages; `07_loop_step_bad.sl` (refused, then
`--goal proved: FAIL`); both bare-`ne` refusals (`(CNe c2 c2)` at
`det.sl:107`, `(CNe c c)` at `:120`); the `p0` refusal; the three
`predates` variants of `drive.sl`; `07_nondet_both.sl` under both
checkers and `det.sl` against `07_nondet_spec.sl`; that the current
files run with no warnings; the line and rule counts, F4's sub-counts
(`det.sl:1-25`, `27-88`, `90-123`), and the `goal.sl` and `Waiting`
excerpts; `self/elab-main.sl:159` and `443-462`; and the cross-references
to 01 decisions 4 and 5, 03 decision 3 and Q1(e), and 05 F4, T5, and
decisions 4 and 5. All matched. Errors found and changes made:

1. F7 said that of "a diverging run gives no verdict" and its converse
   only the first is evident from the code. For the zipper the converse
   reads off the code as easily: every step that is not a machine step
   ends with a verdict or handles one statement, so if every run the
   checker reaches halts, a verdict comes in finitely many steps. Both
   are now given as read from the code, and neither as proved.
2. §5, first rough edge: §50's "an argument (its parameter, given the
   arguments before it)" is the nearest DESIGN.md comes to an argument
   order; it concerns what an argument is checked against. Added, so
   the "could not find" covers it.
3. Fourth review note 5 says a search for `terminat` and the like found
   only §17, §18, §33, and §42. It also matches the overview line
   "Termination: §17 to §20" (DESIGN.md line 25) and the word
   "terminator" in §2 and §3; neither changes the rough edge.
4. Fourth review notes, second unsure point: "every premise in the toy
   depends on the one before it, so no two premises can fail
   independently" is false for `ElNeed`, whose `Elab es rest` does not
   depend on its `Nth` fact premise. So the toy can observe the order:
   in `Let 3; Need 0 Succ; Let omega`, the mirror-shaped `FNeedFact`
   gives a `Fails` (both variants print "rejected: need: the fact is not
   known after 4 Program steps" on a scratch copy of `drive.sl`), while
   a `Need` rule that required the rest first would give no derivation,
   the rest's run diverging (reasoning; such a rule was not written).
5. Third review notes, second unsure point: the `p0` wording of F5 is
   now reproduced exactly, by passing `p0` for `src` at `replay.sl:116`:
   "`p0`, declared `erased`, used in a non-erased position".
6. Header: names this review's commit.

The theorem's type was checked against the claims again: `MkCertified`
packs `S`, `L`, an unconstrained `init`, a `step` whose `Fin` must carry
a `Verdict p` for the same erased `p`, and an `excl` that mentions only
`spec.sl` relations. Vacuous implementations that pass: a `step` that
answers `More` on some or all states, with any `init`, and any reason
string. I found no third.

Points I am unsure of:

- That the toy's `exclusive` and 05's `t1_toy.sl` one are "the same
  induction" (decision 3): both match on `Fails` and recurse on a
  sub-derivation, but `t1_toy.sl` recurses with `subterm` on the source
  term and needs no determinism lemma, having no state.
- Whether full Sleight's levels rule out a diverging run-position form
  (first review's open point); not examined here.

## Round 6 review notes

A sixth adversarial review read DESIGN.md in full, every file in
`proto/roundtrip/`, `proto/review2/07_*`, and `proto/review4/07_*`, and
re-ran at 10bd85d (no code change since 669b328): programs 0 to 5 in
both variants under the reference and `slc --interpret` (outputs, exit
codes, and step counts as in F2, identical between the two); program 6
(22 MB at 4 s and at 12 s, both variants); the three
`--goal proved: PASS` sets and the replay set without `impl.sl`
("unbound name `vals`") under both checkers; `spec.sl det.sl` alone
(accepted); the four refusals under both checkers, with the quoted
messages; `07_loop_step_bad.sl` (refused, then `--goal proved: FAIL`);
both bare-`ne` refusals (`(CNe c2 c2)` at `det.sl:107`, `(CNe c c)` at
`:120`); the three `predates` variants of `drive.sl` (the `Predates M P`
one refused with "value mismatch: expected `PA`, got `P`", the other two
accepted with the quoted warning); `07_nondet_both.sl` under both
checkers (`(MkBoth _ _ _)`) and `det.sl` against `07_nondet_spec.sl`
(refused at `det.sl:48`, missing `SNumUp`); that the current files run
with no warnings; the line and rule counts; the `goal.sl` and `Waiting`
excerpts; the DESIGN.md quotes in F1 and §5; and `self/elab-main.sl:159`
and `443-462`. All matched except as below. Errors found and changes
made:

1. Decision 3 said 05's `t1_toy.sl` exclusivity is "the same
   induction" as the toy's (the fifth review's open point). It is not:
   `t1_toy.sl`'s `exclusive` recurses with `subterm` on the source term
   and uses no determinism lemma; the toy's recurses on `Fails` and
   needs one per shared premise (`det.sl:90-123`). Both are plain
   inductions, which is all the decision needs. Reworded.
2. F7 did not say whether a `Certified` value can be driven at all. A
   function given one cannot call its `init` or `step`, since their
   level is the packed `L`: `proto/review6/07_cert_fn_bad.sl` (new) is
   refused with "`L` was not in scope when level `(level-of first-turn)`
   was minted". Destructured at the top level, before the driver's
   levels are minted, the same value drives program 0 to "accepted after
   26 Program steps" (`proto/review6/07_cert_drive.sl`, new; reference,
   `--no-extern`, and `slc --interpret`). Added to F7, since it bears on
   how the statement can be used.
3. Header: names this review's commit.

The theorem's type was checked against the claims again: `MkCertified`
packs `S`, `L`, an unconstrained `init`, a `step` that sees `p` only
erased and whose `Fin` must carry a `Verdict p` for that `p`, and an
`excl` that mentions only `spec.sl` relations (`det.sl` is accepted
against `spec.sl` alone). Vacuous implementations that pass: a `step`
answering `More` on some or all states, with any `init`, and any reason
string. I found no third.

Points I am unsure of:

- Whether 05's claim that T3 "needs the spec to be deterministic",
  which F4 cites, is meant generally; `t1_toy.sl`'s exclusivity needs no
  determinism lemma, its spec having no evaluation. F4's own claim, that
  this toy's proof uses determinism and fails for one nondeterministic
  variant, is compiled.
- Whether the top-level destructure of item 2 is how a certified checker
  in full Sleight would be packaged for its driver; that is a design
  question, not settled by this test.

## Round 7 review notes

A seventh adversarial review read DESIGN.md in full, every file in
`proto/roundtrip/`, `proto/review2/07_*`, `proto/review4/07_*`,
`proto/review6/07_*`, and `proto/review7/07_cert_predates.sl`, and
re-ran at 13ca61f (no code change since 669b328): programs 0 to 5 in
both variants under the reference and `slc --interpret` (outputs, exit
codes, and step counts as in F2, identical between the two); program 6
(22 MB at 4 s and at 12 s, both variants, still running at 12 s); the
three `--goal proved: PASS` sets and the replay set without `impl.sl`
(FAIL) under both checkers; `spec.sl det.sl` alone (accepted); the four
refusals under both checkers, with the quoted messages;
`07_loop_step_bad.sl` (FAIL under both); both bare-`ne` refusals; the
`p0` refusal; the three `predates` variants of `drive.sl`;
`07_nondet_both.sl` under both checkers (`(MkBoth _ _ _)`) and `det.sl`
against `07_nondet_spec.sl` (refused at `det.sl:48`);
`07_cert_fn_bad.sl` (refused as quoted) and `07_cert_drive.sl`
(reference, `--no-extern`, and `slc --interpret`); that the current
files run with no warnings; the line and rule counts and F4's
sub-counts; the `goal.sl` and `Waiting` excerpts; the DESIGN.md quotes
in F1 and §5, and searches of DESIGN.md for divergence and for an
argument order; `self/elab-main.sl:159` and `443-462`; and the
cross-references to 01 decisions 4 and 5, 03 decision 3 and Q1(e), 05
F4, T3, T5, and decisions 4 and 5, and `t1_toy.sl`. All matched except
as below. Errors found and changes made:

1. F7 said a function given a `Certified` "cannot call its `init` or
   `step` at all". Given also a `Predates` from the value to the
   function's level, proved at the top level for a value built before
   that level was minted, the function calls both through
   `prove-subterm` and `predates-subterm`
   (`proto/review7/07_cert_predates.sl`, left by an interrupted round-7
   reviewer; reference, `--no-extern`, and `slc --interpret`, each
   printing `0`, the `More` case). §19 refuses a `Predates` "about the
   function value itself"; the one derived here is about the packed
   level `L`. F7 now says "given only" and adds this; 06's decision 2
   cites it.
2. F4 said `exclusive` has "one determinism lemma per premise that two
   derivations share". `FNeedRest` shares its `Nth` premise and uses
   none, `FAssertRest` uses no `head-det` for the `Head` premise it
   shares, and three cases refute with `nth-nonth` or `evals-sticks`
   instead (`det.sl:90-123`). Reworded; decision 3's "on `Fails` with
   one" now says "with determinism lemmas".
3. §1 said the step whose machine step halts "also resumes the
   checker"; when the run is stuck, that step rejects instead (program
   3's sixth step). Added.
4. F5 gave `replay.sl`'s "first version" refusal without saying that
   the draft was not kept; it now says that, and that the message
   reproduces with `p0` passed for `src` at `replay.sl:116`.
5. Header: names this review's commit.

The theorem's type was checked against the claims again: `MkCertified`
packs `S`, `L`, an unconstrained `init`, a `step` whose `Fin` must carry
a `Verdict p` for the erased `p` it is given, and an `excl` that
mentions only `spec.sl` relations. Vacuous implementations that pass: a
`step` answering `More` on some or all states, with any `init`, and any
reason string. I found no third.

Points I am unsure of:

- The round-6 open point stands, now with two ways to reach a
  `Certified`'s `init` and `step`: a top-level destructure, which
  drives program 0 to its verdict, and a `Predates` passed beside the
  value, compiled only for one call of each. Which, if either, a
  certified checker in full Sleight would use for its driver is a
  design question.
- F3's "valid partial derivation by construction" still carries, only
  in the second review's notes, the caveat that it rests on the erased
  logic having no closed proof of `False`; I left the body as it is.

## Round 8 review notes

An eighth adversarial review read DESIGN.md in full, every file in
`proto/roundtrip/`, `proto/review2/07_*`, `proto/review4/07_*`,
`proto/review6/07_*`, and `proto/review7/07_cert_predates.sl`, and
re-ran at 634e3ee (no code change since 669b328): programs 0 to 5 in
both variants under the reference and `slc --interpret` (outputs, exit
codes, and step counts as in F2, identical between the two); program 6
(22 MB at 4 s and at 12 s, both variants); the three
`--goal proved: PASS` sets and the replay set without `impl.sl`
("unbound name `vals`") under both checkers; `spec.sl det.sl` alone
(accepted); the four refusals under both checkers, with the quoted
messages; `07_loop_step_bad.sl` (FAIL under both); both bare-`ne`
refusals (`det.sl:107` and `:120`); the `p0` refusal; the three
`predates` variants of `drive.sl`; `07_nondet_both.sl` under both
checkers (`(MkBoth _ _ _)`) and `det.sl` against `07_nondet_spec.sl`
(refused at `det.sl:48`); `07_cert_fn_bad.sl` (refused as quoted, slc
also at the `step` call), and `07_cert_drive.sl` and
`07_cert_predates.sl` under the reference, `--no-extern`, and
`slc --interpret`; that the current files run with no warnings; the
line and rule counts, F4's sub-counts, and the lemmas each case of
`exclusive` uses (`det.sl:90-123`); the `goal.sl` and `Waiting`
excerpts; the DESIGN.md quotes in F1 and §5, and a search of DESIGN.md
for divergence; `self/elab-main.sl:159` and `443-462`; and the
cross-references to 01 decisions 4 and 5, 03 decision 3 and Q1(e), 05
F4, T3, T5, and decisions 4 and 5, and `t1_toy.sl`. All matched except
as below. Errors found and changes made:

1. F7 said a function given only a `Certified` cannot call its `init` or
   `step`, on one refusal of the inferred `(predates _)`, which §48 says
   does not search. A written-out `(prove-predates c F)` in the function
   is refused too, "`c` was not in scope when level `F` was minted"
   (`proto/review8/07_cert_fn_self_bad.sl`, new; reference,
   `--no-extern`, and `slc --interpret`). F7 now cites it and says "in
   the two shapes tried and as I read §18".
2. §1 used "termination under H" without saying what H is. It is the
   hypothesis of the brief's statement 4, so the header's "The only
   owner item the body mentions is the brief's statement 3" was false.
   §1 now states H, and the header names both statements as an earlier
   session's paraphrases.
3. Decision 1 condensed F6 and Q1(b) to "about quadratic work", dropping
   that it is an estimate and that it is re-elaboration work, quadratic
   in the number of runs, and said the zipper "removes both", where
   Q1(a) keeps the toy's O(entries) lookups per statement. Now says so.
4. F3's "Every `CState p0` value is a valid partial derivation by
   construction" carried no condition in the body, which round 7 left
   open: it rests on the erased logic having no closed proof of `False`
   (second review notes). The body now says so.
5. Header: names this review's commit.

Points I am unsure of:

- F4's "about 45 lines" for the suspension machinery: `Ctx`, the two
  `plug` functions, `Reach`, and `reach-runs` come to 41 lines, 49 with
  `CState`; left as it is.
- Outside this file: 00-summary.md section 7 states "A function given
  only a `Certified` value cannot call its packed-level `step`" on the
  same single test that item 1 found too thin; left to its owner.
