# 07. Spike: proving the §29 round trip with a suspendable checker

Written overnight by a Claude agent as a proof-technique spike. It is a
proposal and an agent's reading. Nothing in it is approved, and where it
and DESIGN.md disagree, DESIGN.md is right.

Tags: **[D]** DESIGN.md, quoted; **[C]** compiled or run. Unless marked
otherwise, files are under `proto/roundtrip/` and were run with
`_build/default/bin/main.exe` at commit 669b328 (no change to `bin/`,
`lib/`, `src/` or `self/` since, up to ad07c35), and also with slc
(`_build/release/slc`; `slc --interpret`, `slc --goal`).
**[A]** marks my own reading or proposal. The only owner item mentioned
is the brief's statement 3, in decision 4, and it is an earlier
session's paraphrase.

## 1. Summary

- [C] A toy language with the round trip works end to end, with no fuel
  anywhere. It has top-level `Let t` (run at check time, giving a
  `Settled` value), `Assert i c` (a `comptime-match`: it reads entry i's
  stored value, checks the constructor, and exports a fact), and
  `Need i c` (a later check that consults only the facts, never the
  value). The spec has an inductive `Elab` with evaluation premises, a
  positive `Fails`, and a small-step `Step` relation. The checker emits
  "evaluate this" by moving into a `Waiting` state. Each `Program`
  step runs one machine step and the checker resumes, all driven by
  `Program`. The final `Verdict p` carries an erased `Elab [] p` or
  `Fails [] p`. Exclusivity (`Elab ∧ Fails → False`) is proved. It
  needs determinism of evaluation (`step-det`, `runs-det`,
  `evals-det`) and of every lookup the rules use.
- [C] Both the reference and slc accept the whole thing, run it, and
  report `--goal proved: PASS` for the packaged statement. Four
  deliberately wrong versions of single components (each a standalone
  function with the correct component's signature, not wired into the
  checker) are refused at the faulty proof term. Example: skipping the
  fact check in `Need` gives "expected
  `(Nth (Ent) es i (MkEnt v (KIs ct)))`, got `(Nth (Ent) es i (MkEnt v k))`".
- How the suspended state is represented (the spike's key question). A
  suspended checker records "I am deriving
  `Elab [] p0`, waiting on `Eval` of `t`" as two nested,
  defunctionalized derivation contexts. They are both erased fields of
  the `Waiting` state.
  - `Ctx p0 es p`: "a derivation for `es ⊢ p` plugs into one for
    `[] ⊢ p0`". Each frame holds the non-recursive premises already
    established.
  - `Reach (Ev t env []) m`: "a run from `m` extends to a run from the
    initial state".
  [A] One `Ctx` serves both `Elab` and `Fails`. That works because
  `Fails` mirrors `Elab`: each rule has a "fails later" form with the
  same earlier premises.
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
  always returns `More` also passes the goal (`spin_vacuous.sl`). A
  `step` that itself never returns is refused (a same-level self-call
  "decreases no subterm argument", §17, §48). Completeness, or
  termination under H, is the main missing piece.

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
| 0 | two lets, one reading the first's entry, asserts and needs | accepted, 26 steps | accepted, 22 steps |
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
  because its erased fields can be built only by the rules. The theorem
  needs no separate invariant and no `init` state hypothesis.
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
  - `exclusive`: about 35. It is induction on `Fails`, with one
    determinism lemma per premise that two derivations share.
  - Exclusivity of `Let` needs `evals-det`, which needs `vals-det`,
    `runs-det`, and `step-det`, which in turn needs `nth-det` and
    `nth-nonth`. [A] Without determinism of the evaluation relation,
    this proof does not go through at `FLetRest`/`ElLet`: two different
    values would put the two derivations in different contexts, and I
    expect exclusivity could then be false. This matches 05's
    expectation that T3 "needs the spec to be deterministic".
- The proof-carrying checker. Each lookup returns its relation (`Find`
  carries `Nth` or `NoNth`, `head` returns `Head`, and `ctor-dec`
  returns `CSame` or `CNe`). The suspension machinery (`Ctx`, the two
  `plug` functions, `Reach`, and `reach-runs`) is about 45 lines.
- The evaluator proof is trivial here, because the spec's evaluation
  relation is the same machine as the implementation's `mstep`: `mstep`
  returns `(erased (Step s o))` per step, and `Reach` is a list. [A] If
  the spec's run were big-step, or a different machine (02's heap
  machine), a simulation between the two would be the largest single
  proof. I did not attempt it.
- The reference forced and refuted every cross-constructor case on its
  own. Examples are `let-match` on `Step` derivations whose indices
  differ, and `(match erased e _)` on `Eq (Out) (Halt …) (Go …)`. The
  author reports that most lemmas were accepted on the first compile;
  that history was not re-checked.

### F5. What the reference refused, and why [C]

- `det.sl`, first version. A bare `ne` as a final expression is
  refused; with today's `det.sl` edited back that way, the message is
  "expected `(False)`, got `(CNe c2 c2)`". The fix is
  `(match erased ne _)`, a match whose every constructor is refuted,
  which "produces its declared result" (§25, §21). `exclusive` is not
  an `absurd` function, so §51's refutation rule is not what applies.
- `replay.sl`, first version. "`p0`, declared `erased`, used in a
  non-erased position." Replay re-elaborates the whole source, so its
  state must hold the source at runtime: `(many p0 is src)`. The zipper
  needs only the remaining statements at runtime.
- `drive.sl`. Calling the step parameter from `drive`'s body with a
  `Predates M P` gave "value mismatch: expected `PA`, got `P`", since
  the current level is `PA`. With no annotation the call is accepted:
  §48 builds `(predates _)`, and an explicit one draws "unnecessary
  `(predates _)`".
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
  "same-level call … is unmarked; mark it `notail`".

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
  runs the machine (with `Reach`) and appends the answer. The work is
  quadratic in the number of runs.
- About 50 of its 127 lines are the decidable equality.
- [A] In full Sleight a request is roughly (stripped code, the store
  Σ), so this equality covers code and heap. The alternative is to
  index the oracle by derivation position, so that no comparison is
  needed. But then extending it needs the position of the hole, and
  that is the `Ctx` zipper again.

### F7. What the statement does not say [C]

`spin_vacuous.sl` is a stepper whose `step` always returns `More`. It
passes the same goal. So the theorem is: whatever verdict the loop
reaches is a correct one, and accept and reject cannot both hold. It
does not say that the loop reaches a verdict when the spec has one.
Program 6 shows a diverging run that has neither derivation, and the
loop runs at constant memory. That is consistent with
"no verdict ⇔ some run diverges", but only the ⇐ direction is evident
from the code. Neither direction is proved.

## 3. Options

### Q1. Shape of the resumable certified checker

- **(a) Derivation zipper: a CPS or defunctionalized state machine.**
  - Design: the checker state is the elaboration context (`Ctx`) plus,
    while waiting, the evaluation context (`Reach`), both erased. It
    advances by one total step per `Program` step.
  - Pros:
    - No fuel, no replay, and linear work.
    - One frame type covers acceptance and rejection.
    - The derivation is assembled once, at the end.
    - Compiled here.
  - Cons:
    - Every elaborator function that can reach a round trip becomes
      frames. In full Sleight that is most of elaboration (nested run
      positions, §15's hoisted arguments, and macro expansion, which
      also runs code, §62).
  - Risk: frame count. It grows with (rules × recursive premises).
  - Cost: high for slc; natural for a new kernel written this way.
- **(b) Direct style plus replay with a proof-carrying oracle.**
  - Design: as in F6.
  - Pros:
    - The elaborator stays recursive, which is how slc's block is
      written. Its compile-time runs are inline calls to
      `run-code`/`eval` with fuel (`self/elab-main.sl:159`, `443-462`).
    - Compiled here.
  - Cons:
    - It needs decidable equality with proofs on requests, which means
      heaps in full Sleight.
    - Work is quadratic in the number of runs.
    - Σ effects (gensym, expansion count, macro-world updates) must
      come back from the oracle, or be replayed identically (03 Q1(e)).
    - Every call site re-wraps a third outcome.
  - Cost: medium to high. Most of the cost is intrinsic derivations
    everywhere, which (a) needs too.
- **(c) Inline bursts with replay only on overflow (03's hybrid).**
  - Design: (b), but the machine runs inline for B steps, and only a
    run longer than B triggers `RAsk`.
  - Pros: replay is rare.
  - Cons: inline bursts are bounded iteration. A burst that runs out
    must yield `RAsk`, so the proof is (b)'s.
  - Untested.

### Q2. What the spec's evaluation relation is

- **(a) A small-step machine relation that the implementation steps
  through.**
  - Pros: the evaluator side of the proof is a list of step proofs
    (F4).
  - Cons: the spec reads as a machine.
- **(b) Big-step, or a different machine.**
  - Pros: it reads closer to DESIGN.md's prose.
  - Cons: it needs a simulation proof from the implementation's
    machine. That proof would dominate the effort.

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
     request equality on heaps and quadratic work. The zipper removes
     both, at the cost of rewriting the elaborator into frames.
   - Depends on it: 04's compiler-route choice, and 03 decision 3.
2. **Is the spec's compile-time run a small-step relation over the same
   machine the compiler steps (Q2a)?**
   - Recommended: yes, if the owner wants the evaluator part of the
     proof to stay small.
   - Depends on it: 02's machine design, and the size of the T5 proof
     in 05.
3. **Should `Fails` mirror `Elab` premise by premise ("fails at premise
   k after 1..k−1 hold")?**
   - Recommended: yes. One context then serves both, and exclusivity is
     a plain induction.
   - Consequence: the spec then fixes the order of premises, which is
     01's decision 5.
4. **Must the packaged theorem include completeness?**
   - Recommended: yes, relative to per-source evidence (Q3a). Without
     it, a stepper that never answers satisfies the statement (F7).
   - Depends on it: 05 decision 5.
5. **Is a compile-time run that goes wrong a rejection?** The toy has
   `FLetStuck`.
   - [A] In typed Sleight, a run that goes wrong should not happen if
     the language is sound. So this is 05 decision 4 (crashes) in
     another form, and the toy's rule is a stand-in, not a proposal for
     the full spec.

## 5. Rough edges in DESIGN.md (questions, not resolved)

- §29 says the round trip "nest[s]" but does not say in what order the
  inner runs happen relative to the elaboration of their siblings. A
  zipper or a positive `Fails` needs that order (F3). This adds to the
  evidence for 01's decision 5.
- §28: "On a mismatch, the error prints the expected constructor and
  the actual value". If rejections carry their reason (01 decision 4),
  the `Fails` rule for a mismatch must carry the value. The toy's
  `FAssertHead` carries `v` and its head. Whether the printed text is
  part of the spec is open.
- §27 and §29 describe a diverging run-position form only implicitly:
  the form "runs as soon as it has been elaborated, before the code
  after it is checked". DESIGN.md does not say what a checker that
  never returns means for acceptance. With no fuel, the toy simply never
  finishes. This is the gap that F7 and 05's T4 discuss.

## 6. Unverified claims

- That the zipper construction scales to nested round trips by taking
  one frame per (rule, recursive premise). It is not built.
- That replay in full Sleight needs equality on (code, heap) requests,
  and that indexing the oracle by position brings back the zipper. This
  is reasoning, not code.
- That a simulation proof would dominate under Q2(b).
- That Q3(a) is writable for this toy: plausible from 05's `bove.sl`,
  but not written.
- The timings and memory figures are single runs on one machine.
- That slc's elaborator is "direct-style" throughout. I read only
  `self/elab-main.sl:159` and `443-462`, and 03's description of the
  block.
