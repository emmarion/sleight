# 05. The theorem statements, and what can and cannot be proved inside Sleight

Written by a Claude agent overnight, as one input to the owner's review.
Everything here is a proposal or an agent's reading. Nothing in it is
approved, and nothing here is a design decision (CLAUDE.md rules 1 and 11).

Sources are marked: **§n** quotes DESIGN.md; **file:line** is code;
**[proto]** is a test under `proto/theorems/`, compiled with the
reference (`_build/default/bin/main.exe`) at commit 164fcf1;
**[owner n]** is item n of the brief's "Owner decisions", which are an
earlier session's paraphrases, not the owner's words; everything
else is my own reading and is hedged as such. `bove_use.sl`, `fuel.sl`,
`model.sl`, `fuel_run.sl`, `halts_reflect.sl`, and
`proto/review3/05_halts_uniform.sl` need `bove.sl` (`fuel_run.sl` and
`halts_reflect.sl` also `fuel.sl`, and `halts_reflect.sl` also
`fuel_run.sl`) earlier on the same command line.

## 1. Summary

- Because §9 bars calls from types, "`compile src` = Accepted ⇒ …"
  cannot be written as a type. One workable form, which I recommend, is
  *intrinsic*: `compile` returns its verdict together with an erased spec
  derivation. The other is a graph relation that duplicates the
  function (F1). A toy checker in the intrinsic form, together with an exclusivity lemma, is
  accepted, and packaging it as `(goal many (Certified))` passes
  `--goal proved` [proto].
- T1 (acceptance soundness) and T2 (rejection soundness) are then the
  type of `compile`. T3 (exclusivity) needs the spec to be deterministic.
  As DESIGN.md stands it is not: `slot-eq` may answer either way
  (§67) and can decide acceptance at compile time [proto]. Crashes and
  `native-compute` add more choice, and `read-file` makes acceptance
  depend on the file system. My proposal is an
  oracle parameter, with T3 stated per oracle.
- In my reading, T4 (every source is accepted or rejected) cannot be an
  unconditional Sleight function if the compiler is faithful (T1 to
  T3, with crashes kept out of the oracle, §3 T3): if Sleight's functions terminate and its checking ends
  (SOUNDNESS.md's (T), (C), and (E), argued there, not proved, and read
  as §4.3 and 03 F6 read them), and its
  logic is sound, which the argument needs because T1 to T3 are stated
  by erased derivations, a diagonal argument rules out a total, sound, and complete compiler or
  run-function for Sleight source written in Sleight. The
  self-reference can come from `read-file` in a macro (03 F6, whose
  mechanism `proto/fuel/diagonal.sl` compiles, under the further
  premises of 09 §3.4), so no quine is needed. Gödel's second
  theorem may give a related limit, conditionally (§4.3, 09): if Sleight
  is consistent, a formalized provability relation `Prov` meets the
  derivability conditions and has a diagonal sentence, the usual
  derivation's internal steps go through despite level stratification,
  and the matching lemmas hold, then on my reasoning Sleight cannot prove
  uniform stripped-run safety, nor uniform (T) together with
  full-semantics safety. Of these conditions only the first, which is
  OPEN.md 1, has been worked on, and the internal steps have been tried
  only for an abstract relation in place of `Prov` (§4.3). Nothing builds
  a `Prov` that formalizes acceptance. Two fuel-free shapes compile: recursion on an
  erased `Halts` derivation, and a typed step machine driven by
  `Program` [proto]. A third shape, "honest fuel", whose out-of-fuel
  result carries a proof, also compiles [proto], but it uses fuel. The
  `Halts` shape is fuel-free but not callable in practice except under
  a proof: its caller must supply an erased `(Halts …)`, which takes
  either a termination proof (for that input, or for every input where
  the step's termination is provable, as for a toy step in
  `proto/review3/05_halts_uniform.sl`) or a fuel run that has already
  done the work (§4.3).
- Parameterizing the semantics works through erased `TyCtor`
  parameters and model records indexed by them [proto]. A signature
  cannot name a relation stored as a record's field, since a type has no
  projection (§9); inside a body, after a `let-match`, the field can be
  used in types [proto `project_in_body.sl`].
- The theorems mean something only if Sleight's logic is sound in a
  sense stronger than consistency, because the derivations are erased.
  A proved compiler can take the elaborator, the compile-time evaluator,
  and OPEN.md 4 out of the trust base. It cannot remove OPEN.md 1–3,
  the axioms' justification, or the checker that checks the proof.
- In my reading, "`unique` is the sole reference" is not needed for compiler
  correctness against a mutating heap-machine spec. It is what connects
  that heap machine to the tree reading of values that the fact table
  depends on.

## 2. Findings

### 2.1 What a theorem can be in Sleight

- **F1. No calls in types.** "The elaborated form of a type never
  contains a function call" (§9). Compiled: `(Eq (Nat) (f n) (Succ n))`
  is refused with "`f` … cannot be applied in a term, where only a type
  or value constructor can be applied (§9)"
  [proto `call_in_type_bad.sl`]. So, as far as I can see, a theorem
  about a function's output is stated in one of two ways. Either it is *intrinsic* (the function
  returns an erased proof about its result), or it is about an inductive
  *graph relation* written alongside the function, which duplicates it.
- **F2. Intrinsic certified checker works.** [proto `t1_toy.sl`] declares
  a toy `Src`, a positive `Elab` relation, and a positive `Fails` relation,
  plus `Verdict s` with `Accepted (erased (Elab s))` and
  `Rejected (erased (Fails s))`. The function
  `compile : (subterm many (Src) s) -> (many (Verdict s) r)` and the erased
  lemma `exclusive : … (Elab s) (Fails s) -> (False)` (it dispatches on
  the `Fails` derivation and recurses on the `subterm` source `s`) are
  accepted, and the program runs.
- **F3. A theorem as a goal.** §71: "`(goal m T)` sets the goal of a unit
  … A goal is one type, not a telescope; an existential … is packaged by
  an ADT (§21)." [proto `spec.sl` + `proof.sl`] packages
  `(many (Fn L (many (Src) s) -> (many (Verdict s) r)) c)` together with
  the erased exclusivity function into `Certified`.
  `--goal proved spec.sl proof.sl` prints `--goal proved: PASS`. Both
  functions had to be in one `def-fns` block, because the ADT fixes one
  level `L` for both fields. My first attempt, with two blocks, was refused.
  An ADT with a level per field accepts two blocks
  [`proto/review2/05_spec_two_levels.sl` with `05_tb_two_level.sl`,
  PASS; the same blocks against `spec.sl`, `05_tb_one_level.sl`, FAIL].
- **F4. Fuel-free recursion on an erased derivation (Bove–Capretta
  style).** §21: "Subterm recursion (§17) may go through an erased
  field." [proto `bove.sl`] defines
  `run : (many (Nat) s) (subterm erased (Halts R s) h) -> (many (Nat) k) (erased (RunsTo R s k) r)`.
  It is a `many` function that dispatches on `s`, takes `h` apart with
  `let-match erased`, and recurses with `(subterm sp)` on the erased
  sub-derivation. `R` is a relation parameter, and the step function and
  a determinism lemma are passed in through a §57-style factory. It is
  accepted. Instantiated with a toy step and a hand-built `Halts` at the
  top level [proto `bove_use.sl`], it prints `2`. The `Halts` there is a
  constructor term written out for one input. §20 frees the top level
  from decrease proofs only, not from supplying a typed erased argument,
  so a caller of `run` needs a `(Halts R s)` from somewhere. I found
  three sources: a term written out, an `erased` function that proves
  halting (for that input, or for every input: for the toy step,
  `proto/review3/05_halts_uniform.sl` proves `(Halts Dec s)` for every
  `s` and calls `run` from a `many` function with no further argument,
  printing `7`), or a `comptime-match` on the result of a
  fuel-bounded run (F5) whose finished case carries the run's
  derivation. The third compiles: [proto `halts_reflect.sl`] runs
  `fuel_run.sl`'s runner with fuel 10, `comptime-match`es `FDone`,
  turns its `RunsTo` into a `Halts`, and calls `run` with it (prints
  `3`); with fuel 2 the `comptime-match` is refused. By then the fuel run
  has computed the answer, so `run` adds nothing.
- **F5. Honest fuel.** [proto `fuel.sl`] declares a fuel-result type
  whose out-of-fuel constructor carries
  `(erased (Prefix R s f (Succ t)))`: the spec run has a non-final state
  after `f` steps. It also proves the lemma "a halting run of length `k`
  and a non-final prefix of length `n` give `(Lt n k)`", by induction on
  the prefix, given determinism. The lemma has to sit behind a factory:
  calling a function parameter needs a `Predates` that only a level
  minted after the parameter can have (§18, §57). The first attempt was
  refused with "`M` was not in scope when level … was minted".
  `fuel.sl` itself holds only the type and the lemma. The runner, a
  `subterm` recursion on the fuel that returns `FDone` with a `RunsTo`
  or `FOut` with a `Prefix`, is [proto `fuel_run.sl`] (added in review;
  accepted).
- **F6. A typed step machine driven by `Program`.** §27: "A `Program`
  value (§42) is run: the driver consumes it at `unique` and applies each
  step's continuation once." [proto `drive.sl`] defines a generic
  `drive`. It takes a step function
  `(Fn M (many S s) (erased (Inv s) i) -> (many (Out S Inv Good s) r))`
  whose `Done` carries `(erased (Good s))` and whose `Next` carries the
  next state and `(erased (Inv s2))`, and it wraps each step in a
  `def-unique` continuation at the program's level `P`. A countdown
  machine runs and exits 0. The step's level must be minted before `P`
  (refused otherwise, as `tests/io_step.sl` also arranges). The
  unbounded iteration belongs to the driver, which SOUNDNESS.md part 5
  leaves "outside the claim". The driver consumes only a file's final
  value, and only under `--goal none` (§27, §71). So only the later steps
  of the driven run itself hold its result as a value: no compile-time
  code and no `qed` can obtain it, and a theorem can speak only about the
  step function.
- **F7. Parameterization mechanisms.** A relation is an erased parameter
  of `TyCtor` type, as in the prelude's `Cmp` (`lib/prelude.sl:67`).
  [proto `model.sl`] defines `(Model R)`, an ADT indexed by the relation
  `R`, whose fields are a `many` step function at an erased level and an
  erased determinism lemma. A function generic over `(many (Model R) md)`
  unpacks it and is accepted. [proto `record.sl`] shows that an ADT with
  relation-valued *erased fields* is accepted, and a projected field can
  be applied in an erased expression. Inside a body, after the
  `let-match`, the field can also stand in a binder's type, and forcing
  ties it to a relation the record's index names
  [proto `project_in_body.sl`, added in review]. What F1 rules out is
  naming the field in a signature, since a type has no projection, so
  the form usable across signatures is "index the record by its
  relations". `(many Type T)` is accepted as a
  parameter declaration, with a warning, but no non-erased argument exists: `(f (Nat))`
  gives "type constructor `Nat` applied in a non-erased position"
  [proto `manytype_bad.sl`, `manytype2_bad.sl`], consistent with §21 "A
  value of type `Type` is erased." A `TyCtor` parameter has no opened
  `Matchable` of its own (§8). Generic code can still take apart a
  derivation of a parameter relation if it is also given the relation's
  constructors and an erased `Matchable` listing them, which it opens
  with `open-adt` [`proto/review2/05_generic_match.sl`, accepted]. That
  fixes the number and telescopes of the constructors in the interface.
  Without it, generic code can only use the lemmas the model supplies.
- **F8. The logic is anticlassical.** README.md "Logic and strength":
  "excluded middle at any level `L`, with `¬P` read as a level-`L`
  function, gives a function that returns `False`"
  (`tests/anticlassical.sl`, which refutes the schema over every
  `(erased Type P)`). So a proof cannot assume excluded middle in
  general. Whether the one instance "the spec run of `src` halts or it
  does not", for every `src`, is refutable or merely unprovable I have
  not determined; either way it is not available as a lemma.
- **F9. Claimed strength.** README.md: "the language as a whole computes
  exactly the multiply recursive functions, so its strength is about IΣ₂
  … with proof-theoretic ordinal ω^ω^ω". This is the author's assertion
  and I have not checked it.

### 2.2 Sources of nondeterminism in the spec (for T3)

- **§67** `slot-eq`: "`ENone` proves nothing, so an implementation may
  always answer it, and which one a call answers may differ between
  runs." [proto `sloteq_ct.sl`] runs `slot-eq` in run position and
  `comptime-match`es `ESome`. The reference accepts it, with and without
  `--no-extern`. An implementation that answered `ENone` would reject the
  same text. So *acceptance is not a function of the source* under
  DESIGN.md as written.
- **§31**: "A real run may crash where the host cannot represent what is
  asked of it." **§42**: implementation and model "either may crash where
  the other does not." **§72**: `native-compute` "may crash where the
  evaluator would not … a run that crashes is an error at its argument."
  So whether a program is rejected can depend on the host.
- **§65** `read-file`: answers depend on the file system and on
  `--comptime-unconfine`.
- **§65** `gensym` "mints a number, counting from 1 over the whole run".
  The numbers are observable, so determinism also needs the order of
  macro expansion fixed. I could not determine whether DESIGN.md fixes
  the order in which several macro calls within one form expand; §6
  says only that "The head is elaborated first." (The
  evaluation-order question in general belongs to other tracks.)

### 2.3 What SOUNDNESS.md already says about H

SOUNDNESS.md part 1 lists "(C) Checking terminates" and "(T) Totality
… In the *full semantics* …, every function activation returns, apart
from a crash" among "what is claimed", relative to the shipped prelude.
Part 6 adds "Run-position forms run total code by (T)", which applies
(T) form by form during checking, whereas part 1 states it only "about
any program the checker accepts" (03 F6). If (T) holds, read form by
form as part 6 reads it, and, for a spec whose run strips erased positions, as §27 does ("its
erased positions are stripped, the evaluator runs the code"), (E) too,
read as giving termination of the stripped run (09 §3.2), then
[owner 4]'s hypothesis H (every accepted compile-time form's spec run
halts) holds, apart from host I/O (`read-file`, `native-compute`; 03
F7) and except for `--no-prelude` programs with their own extern models
or `def-prim` signatures, which part 1 says the claims "do not cover". These are claims with an argument, not proofs: the note
calls itself "a sketch" outside `lean/`'s fragment, and says its
argument "rests on lemmas … that are not proved", among them the
preservation of (I1), which "this note does *not* prove". SOUNDNESS.md
does not mention H; on the readings above, H follows from what it
*claims and argues*, and is not established. Even if true, it
is not something Sleight can prove about itself for all programs in a
form a function can recurse on, if its logic is sound, on my reading of
§4.3 below. Part 7 also says of its argument for "(E)" (the stripped run
follows a run of the full semantics): "Without (T) this step fails".
That matters for T7.

## 3. Candidate theorem statements

Pseudo-Sleight below. `Core`, `Target`, `Oracle`, `Elab`, `Fails`,
`Emits`, `TRuns`, and `SpecAllows` are placeholders for the spec
tracks. The shapes have been compiled only in their toy form (F2–F6).

**T1 + T2 (intrinsic).** The verdict carries the oracle under which the
spec derivation holds:

```scheme
(def-adts $ (Verdict : ((String) src) -> Type)
  enum
  (many Accepted : (erased (String) src) (erased (Oracle) o) (erased (Core) c)
     (erased (Elab o src c) d) (many (Target) out) (erased (Emits c out) em) -> (Verdict src))
  (many Rejected : (erased (String) src) (erased (Oracle) o)
     (erased (Fails o src) f) (many (Diag) msg) -> (Verdict src)))
```

`Fails` should be a *positive* relation: a derivation that pinpoints
the failing step. It should not be `Elab → False`. With the negative
form, T2 would need the compiler to refute every possible derivation,
and anticlassicality (F8) gives no shortcut.

**T3 (exclusivity, per oracle).**
`(erased (Elab o src c) d) (erased (Fails o src) f) -> (erased (False) no)`.
In the toy this is a plain induction (F2). In general it needs
determinism of every sub-judgment once the oracle is fixed, including
the compile-time run relation
(`Runs o e v1 → Runs o e v2 → Eq v1 v2`). These are inductions on finite
derivations and need no termination, so I expect them to be provable
inside Sleight once the spec is deterministic given `o`. Across
different oracles, T3 is false (§2.2).

T3 matters for more than tidiness. If the spec's `Fails` held of every
source, a compiler that rejects everything would satisfy T1 and T2; T3
rules such a spec out, provided its `Elab` holds of some source. A spec
whose `Elab` holds of too few sources satisfies T3 all the same. T3 plus T4 give a weak completeness: if
`Elab o src c` holds and `compile` halts, it cannot reject *under `o`*.
It can still reject under another oracle it chose. If the oracle
records crash points, as §4.2 option 1 proposes, and a crash at
compile time counts as a rejection (decision 4), a compiler that always
picks "crash at once" rejects every source that runs any compile-time
code and satisfies T1 to T3, so the guard against a vacuous compiler is
lost. With the shipped prelude that is every source, since the
prelude's own run-position forms run code (`lib/prelude.sl:354` calls
`pow2`). §31 says "The semantics is
that of a machine with unlimited stack and heap" and treats a crash as
something "A real run may" do, which I read as saying that a crash is
not a behaviour of the spec. Completeness would then have to be stated
for the crash-free oracle, or crashes kept out of the oracle. This is
open (decision 3).

**T4 (totality).** Four forms:
- (a) meta-theorem only: it would follow from SOUNDNESS.md's claimed
  (T), (C), and (E) (argued there, not proved), read as covering every
  source, as §2.3 reads (T) and (E), plus the compiler proof;
- (b) Bove–Capretta (F4):
  `compile-h : (many (String) src) (subterm erased (Halts o src) h) -> (many (Verdict src) v)`.
  This is one reading of [owner 4(ii)] as a type, per source: uniform H
  would supply `Halts o src` for every `src`. Not callable in practice
  except under a proof, or after a fuel run (F4);
- (c) honest fuel (F5):
  `compile-fuel : (subterm many (Nat) f) (many (String) src) -> (many (FuelVerdict src f) v)`.
  Its `OutOfFuel` carries `(SpecPrefix o src f st)` and `(NotFinal st)`.
  This is one reading of [owner 4(i)] as a type: running out of fuel
  proves that the spec run has not finished after `f` steps (not that
  it diverges, which no single answer can show). Combined with the F5
  lemma, `Halts-in o src k` and `f ≥ k` rule out `OutOfFuel`;
- (d) step machine (F6): T1/T2 become "the step preserves `Inv`, and
  `Done` implies `Good`". Termination of the loop is meta, and under H
  it follows from a measure.

**T5 (compile-time agreement).** If the compiler's evaluator is the
spec's step function itself, an executable spec, then the values
embedded in `out` are those in `Elab`'s derivation by construction, and
T5 is part of T1. If the evaluator is separate, T5 is a lemma
`eval … -> (erased (Runs o e v))`.

**T6 (output agreement).** The meaningful direction for a
nondeterministic spec is *refinement*: every behaviour of the output is
one the spec allows. Sketch:

```scheme
refines : (erased (Target) out) (erased (Trace) tr) (erased (TRuns out tr) r) ->
    (erased (Oracle) o) (erased (SpecAllows o c tr) a)
```

DESIGN.md mentions no coinductive data, and SOUNDNESS.md part 3 reads
"Values are finite trees", so I take behaviours to be finite trace
prefixes. `SpecAllows`
must admit "prefix then crash" (§31). It must also say what happens
after the spec goes wrong; see T7. Forward simulation from the spec
plus a deterministic target gives backward simulation in the usual way
(the CompCert pattern, cited by name only and from memory). As I recall
it, that route needs the target to be deterministic and the spec
receptive, not the spec deterministic; here the target's `slot-eq`
answers would have to be expressible as an oracle the spec can choose.

**T7 (safety of the spec itself).** Two levels:
- *Full semantics* (erased code runs): progress and preservation of a
  typed state are an induction over finitely many steps. I expect them
  to be provable inside Sleight, because they need no termination.
  This is unverified.
- *Stripped run* (erased code removed; an earlier session read
  [owner 6] this way, and the brief marks that reading NOT confirmed):
  "never enters a refuted branch" needs every erased proof to *exist*
  in the full semantics. That is SOUNDNESS.md (E), whose argument there
  uses (T) ("Without (T) this step fails"). On my reading of §4.3,
  uniform (T) and full-semantics safety cannot both be proved inside
  Sleight if it is consistent, conditions (b) to (d) of §4.3 hold for
  a formalized `Prov`, and the matching lemmas of §4.3 hold (of these,
  only consistency has been worked on, and (d) only for an abstract
  relation, §4.3), and on my reasoning there uniform stripped-run safety
  alone would already give internal consistency. So, consistent with
  [owner 1]'s "no `no_false`", I expect T7 for the stripped run to stay
  a meta-theorem. T6 then either assumes
  "the spec run of `src` does not go wrong", as CompCert assumes a safe
  source, or defines going wrong as a behaviour after which anything is
  allowed. Either way it is not vacuous for accepted programs only if
  the meta-theorem holds.

## 4. Options

### 4.1 Theorem shape

1. **Intrinsic** (F2): the verdict carries erased derivations. *Pro:*
   compiles today, with no duplicate of the code. *Con:* the proof is
   interleaved with the compiler, which is bigger to read. *Risk:* low.
   *Cost:* the derivations must be threaded through every function.
2. **Graph relation** + extrinsic lemma: write `CompileRel src v` that
   mirrors `compile`, and prove `CompileRel src v → …`. *Pro:* separates
   the code from the proof. *Con:* by F1 the relation duplicates the
   compiler, and the link from function to relation is itself intrinsic.
   *Cost:* roughly double.
3. **Certificate output**: the derivations are `many`, so they are
   actually built, and a small independent checker checks them. *Pro:*
   moves trust from Sleight's logic and the proof checker onto the
   certificate checker (§5). *Con:* the certificate checker re-implements
   the spec relation, and certificates include whole compile-time runs.

### 4.2 Nondeterminism

1. **Oracle parameter** (recommended): `Elab o src c` with
   `o : Oracle`, which records `slot-eq` answers, crash points, file
   contents, and so on. The compiler records the answers it actually
   used as an erased log, and the verdict exists-quantifies `o`. *Pro:*
   T3 per oracle, determinism lemmas provable. *Con:* the oracle's shape
   must anticipate every source of choice, and an oracle that may choose
   crashes, or `ENone` from every `slot-eq`, lets a compiler reject
   more than it should while meeting T1 to T3 (§3 T3).
2. **Relational spec** with nondeterminism inside the rules. *Pro:*
   closest to DESIGN.md's prose. *Con:* T3 is false outright, and
   completeness has to be stated with `∃`.
3. **Remove the nondeterminism from the language**: for example, refuse
   `slot-eq` in run position, or make compile-time `slot-eq` exact. This
   is a language change for the owner, not something I propose here.

### 4.3 Totality (T4): what is and is not internally provable

My reading of the limits, hedged:

- **Diagonal.** Suppose `cr : (many (String) src) -> (many (Result (Nat)) r)`
  were a Sleight function (hence total, if SOUNDNESS.md (T) holds),
  sound, and complete for the spec's run of programs whose final value
  is, or computes, a `Nat`. A program Q containing its own text (a
  quine; strings make this routine) can end in a final value of type
  `(Fn L -> (many (Nat) y))` that computes `cr(Q)` and returns its value
  plus 1, or 0 on `Fail`. Defining it "involves no evaluation" (§29),
  so Q is accepted before `cr` runs, and the driver then applies it
  (§27). On 09 §3.2's reading of SOUNDNESS.md part 5, which does not
  mention the driver's call of a final value, (T) and (E) cover that
  call, and the spec run of Q halts with a `Nat`. Soundness and completeness then contradict each other. (With
  `cr(Q)` in run position instead, Q would be accepted only if that run
  ended, and (T), stated for accepted programs, could not be used to
  show that it does.) So, on that reading, and
  assuming soundness of the logic, the spec's determinism on Q, and the
  existence of quines (I have not written one), no internal total,
  sound, and complete compile-and-run
  for Sleight source exists. Without a quine, Q can do the same in a
  macro that reads its own file with `read-file` (03 F6, which carries
  (T) and (E) over to that possibly rejected Q through an accepted program with
  the call as its final value, on the same reading and under the
  further premises of 09 §3.4). Applied to
  `compile`, the argument needs T1 to T4 and the spec's determinism on
  Q (through T3), not T5: as in 03 F6, Q's macro expands to a
  `compile-error` exactly when `compile` accepts Q. T3 holds per oracle,
  so the oracle in `compile`'s verdict must govern the run of `compile`
  inside Q. That holds if `compile` calls no `slot-eq`; otherwise, as
  in 03 F6, the argument goes through its copy with every `slot-eq`
  answered `ENone`, which an oracle may always choose (§67) (my
  reasoning). It also needs crashes kept out of the oracle, as
  completeness does (§3 T3): if a compile-time crash counts as a
  rejection (decision 4), a `compile` that rejects Q under an oracle
  that crashes at once meets T1 to T4 on Q, and no contradiction
  follows. This is, as I understand it, the
  classical "no total self-interpreter on source text" barrier. Brown
  and Palsberg's typed self-interpreter for F_ω, cited by name, is to my
  understanding not subject to it because its input is a typed
  representation, not text. The argument is mine and has not been
  checked by anyone else.
- **Gödel.** On my reading, Gödel's second theorem would apply in this
  conditional form. Let `Prov` be a Sleight inductive relation on codes
  of units, formalizing acceptance under `--goal proved` (§71). Suppose
  (a) no unit proves `(goal erased (False))`; (b) whenever a unit proves
  T, one proves `(Prov ⌜T⌝)`; (c) Sleight proves D2 and D3 for
  `Prov`, and a diagonal sentence G with G ↔ ¬`(Prov ⌜G⌝)`, built from a
  relational substitution or by a macro that reads the unit's text (09
  §2.4); and (d) the internal steps of the usual derivation from these
  conditions, which compose implications between `Prov` statements, go
  through despite the level stratification of 09 §2.3. Then, by that
  derivation (cited from memory), no unit proves ¬`(Prov ⌜False⌝)`. If moreover Sleight proves
  that `(Prov ⌜False⌝)` yields an accepted program whose stripped run
  reaches absurd code, it cannot prove uniform stripped-run safety. The
  same goes for uniform (T) with full-semantics safety, given the
  matching lemma. (d) has been tried only in an abstract form (09
  §2.4 B): for a relation `P` on codes that formalizes nothing, with D2,
  D3, and the diagonal's D1 instance as hypotheses, and G taken to be
  ¬`(P ⌜G⌝)` itself, as a macro-built G would be (a relationally built
  G adds steps that were not tried), `proto/godel/g2_step.sl`, after
  `g2_defs.sl`, proves ⊢ Con → G for every such `P` and code, and `--goal proved` passes on both
  implementations; 09 §2.4 B places the last step, to ⊢ ⊥, at the top
  level. Nothing builds a `Prov` that formalizes acceptance, and (b),
  (c), and those lemmas have not been attempted (09 §2.4). As far as I recall, that derivation is intuitionistic, so
  anticlassicality (F8) does not obviously exempt Sleight. The claimed
  IΣ₂ strength (F9) would supply a base for G2 only if it means that
  Sleight interprets IΣ₂ with closure under deduction; README.md derives
  it from the functions Sleight computes, which does not give that, and
  it says nothing about (b) or (c) (09 §2.4).

  H, read uniformly over all programs, together with internal
  stripped-run type safety would imply internal consistency. Take a
  program with a `many` run-position form of type `(False)` that the
  checker accepts as a form. H, read as covering every such form, says
  its run halts with a value, preservation says the value has type
  `(False)`, and canonical forms say no such value exists.
  "Normalization implies consistency" is the general form of this. The
  same holds of uniform (T) and full-semantics safety. So, if Sleight is
  consistent and meets the conditions above, it cannot prove both
  halves of either pair. For the stripped run, H is not even needed (my
  reasoning): an erased proof `p` of `(False)` gives an accepted program
  whose final value is a `(Fn L -> (many (Nat) r))` with body
  `(lift p)`, `lift` an `absurd` function from an erased `(False)` to a
  `many` value. Defining it runs nothing (§29), so the program is
  accepted; the driver's stripped run drops `p` and enters `lift`'s
  body at once, against safety
  ([`proto/review5/05_stripped_absurd_final.sl`]: with `p` from an
  axiom under `--no-prelude`, `--extract` and `--build` accept it, and
  the reference, the built program, and `slc --interpret` stop with
  "absurd code reached"). With `(lift p)` in run position instead, the
  program is refused at that form
  ([`proto/review4/05_stripped_absurd.sl`]; `--extract` fails), so it
  says nothing about accepted programs. So uniform stripped-run safety
  alone would give internal consistency. In the full semantics `p` runs
  first, so this needs (T). The diagonal above rules out uniform H in one form
  without Gödel, under its premises and if the logic is sound: uniform H, in a form a function
  can recurse on (an erased `Halts` for every source, for a faithful
  step), would give `compile-h` a hypothesis-free caller (option 1
  below). Whether full-semantics safety alone is provable is my guess,
  not a result.
- **What I expect remains provable inside Sleight.** H for one
  particular program, either by an `erased` proof for that program or
  by a fuel run in run position whose finished result is
  `comptime-match`ed (F4, [proto `halts_reflect.sl`]); the latter is a
  run of the compiler with fuel, so it gains nothing over (c) below.
  Also anything conditional on H, safety properties of the full
  semantics, determinism, and exclusivity. None of this is verified
  beyond the toys.

Options:

1. **(b) Bove–Capretta.** *Pro:* no fuel inside `compile-h`, the
   hypothesis is erased and so free at run time, and it is one reading
   of [owner 4(ii)] as a type. *Con:* it is not callable in practice
   except under a proof. Its caller must supply `h : (Halts o src)`,
   and the only sources I found (F4) are a derivation written out, an
   `erased` halting proof (for that input, or for every input, which
   the next sentence rules out for a faithful compiler), or a fuel run whose result
   carries the derivation, which has then already computed the
   verdict. The diagonal above is exactly why, under its premises, no
   Sleight code can supply `h` for every `src`. So, as a way to *run* the compiler, it still
   needs fuel or a proof; its use is as a statement. If the logic were
   unsound, `h` could be fake and `compile-h` could diverge. *Cost:* low
   (F4).
2. **(c) Honest fuel.** *Pro:* runs anywhere; out-of-fuel is evidence,
   not silence; its finished result carries `RunsTo`, from which `Halts`
   follows ([proto `halts_reflect.sl`]). *Con:* it is fuel, which the
   brief lists among the owner's goals to minimize. A large constant
   makes it practically unbounded. *Cost:* low (F5, `fuel_run.sl`).
3. **(d) Step machine + `Program` loop** [owner 2]. *Pro:* no fuel; the
   divergence is the driver's, outside every function; T1/T2 as an
   invariant. *Con:* the whole compiler, including the compile-time
   evaluator, must be written as an explicit-state step (other tracks).
   Its verdict reaches only the driver and the run's own later steps,
   never compile-time code (F6), so it cannot serve where Sleight code
   needs the verdict, such as a `--goal proved` run.
   Internal T4 additionally needs (b) or (c) on the same step function,
   or a graph relation of it (F1). *Cost:* high, since this is the
   compiler's architecture.
4. **Resource budget in the language.** The spec rejects any compile
   whose compile-time runs exceed a bound. §62 already bounds expansions
   ("At most 10000 expansions run in one run"), though it does not say
   that going past the bound is a rejection (03 decision 5). *Pro:* T4
   becomes an unconditional Sleight function, and [owner 3] holds
   literally. *Con:* a language change with an arbitrary constant; a
   Q whose run exceeds the budget is rejected. Owner's call.

### 4.4 What "parameterized the semantics" could mean [owner 1]

1. **Fixed spec, fixed compiler.** The theorems are about one relation.
2. **Spec and compiler generic over a model record** (F7): relations as
   erased `TyCtor` indices, plus a `(Model R …)` record with `many`
   functions and erased laws. Candidates for the parameter are the
   extern models or FFI behaviour, the oracle of §4.2, the file system,
   and possibly the budget of §4.3 option 4. One proof covers
   `--extern` and `--no-extern` and every `slot-eq`. *Con:* generic code
   can match on a parameter relation only if the record also carries its
   constructors and `Matchable` (F7), and every helper that calls a
   parameter function needs a factory (F5).
3. **Also generic over the syntax**: the reader as a parameter
   satisfying a `Parses text raw` law, which would be [owner 1]'s "the
   syntax of the language, or both". *Pro:* separates reader correctness.
   *Con:* one more interface.
4. **Generic over the prelude.** This seems too wide to me: SOUNDNESS.md
   part 1 makes the prelude's models and `def-prim` signatures
   assumptions.

## 5. Trust base of the final theorem

| Item | Source | Can a proved compiler remove it? |
|---|---|---|
| Sleight's logic is sound (OPEN.md 1–3), in a sense stronger than consistency: an erased derivation in `Verdict` must correspond to one that exists, which is SOUNDNESS.md (T), (S), and (E) | §14, SOUNDNESS.md 1 | No. On my reading of §4.3, uniform stripped-run safety, which (S) with (E) includes, cannot be proved internally if Sleight is consistent and §4.3's conditions (b) to (d) and its lemma hold (unattempted, apart from (d) for an abstract relation). `lean/` covers a fragment. Option 4.1.3 moves it onto a certificate checker. |
| The checker that checks the proof: `lib/` (OCaml), or slc compiled to OCaml | MANUAL.md `--goal` | No. It can be mitigated by checking with both, or by a proved slc checking its own proof. That is a consistency check, not a proof; CakeML's in-logic bootstrap, cited by name, is the known pattern. |
| Axioms `predates-trans`, `subterm-trans`, `predates-subterm` (§18), `gensym-unique` (§65), `placed-slot`, `placed-eq` (§66) | §18, §65, §66 | Not from the logic. Their truth *in the spec* (SOUNDNESS.md (I2) and (I3), and the gensym counter) is a safety invariant that I expect to be provable inside Sleight. `placed-slot` and `placed-eq` are about slots, so I expect theirs to rest on OPEN.md 3 as well; SOUNDNESS.md part 4 assumes them true. Using them for the stripped run still needs (E). |
| Character literal bounds "asserted rather than decided" | §45 | Yes in principle: a lemma over the 256 codes, decided rather than asserted. |
| Facts from stored values: `comptime-match` (§28, §29), `prove-literal-lt` (§45), `unary` (§49), the handle primitives (§64, §65) | §29 "relies on the evaluator having evaluated correctly"; OPEN.md 4 | Yes, if the checker's evaluator *is* the proved one (T5). OPEN.md 4 then reduces to OPEN.md 1. A proof that avoids run-position reflection does not depend on them. |
| `native-compute` (§72) | §29, §72 | Only if T6 is proved for the compiled code and the OCaml toolchain is trusted. |
| Extern implementations agree with their models, except `slot-eq` (§42) | §42; SOUNDNESS.md 11 | Yes, for programs checked and compiled with models only (`--no-extern`). Not for primitives without a model (`slot-eq`, `world-do`, the `def-prim`s at `lib/prelude.sl:1401–2250`). |
| Prelude `def-prim`/`def-opaque` signatures and extern models | SOUNDNESS.md 1 | No: they are part of the spec. |
| The elaborator implementation (`lib/elab.ml`, `self/elab*.sl`) and slc's interpreter | `self/README.md` "What it does not do" | Yes. This is the point of the project. |
| The spec's faithfulness to DESIGN.md prose | — | No. It is irreducible. T3 plus completeness guard against a vacuous compiler and against a spec whose `Fails` overlaps its `Elab`, but not against a spec that accepts too little; in my reading that needs `Elab` derived for programs DESIGN.md presents as valid, such as its worked examples (§55 to §61). |
| The OCaml compiler, the runtime, zarith (`lib/ffi_core.ml` `small`), and the host | SOUNDNESS.md 11 | No, unless T6 is extended below OCaml (out of scope). |

## 6. `unique` as sole reference

§13: "Where a value can be mutated in place … a `unique` binder on that
value is the only reference to it." My reading of its role:

- **For compiler correctness (T6) against a mutating heap-machine spec,
  which [owner 6] suspects the spec should be, I do not think it is
  needed.** If the spec stores into the same block
  the compiled code stores into, any aliasing is reproduced step for
  step. The simulation relates heaps, not trees.
- **It is what makes the heap machine agree with the tree reading** that
  the fact table relies on. `is` facts are rules over terms (§7), which
  SOUNDNESS.md part 3 reads as immutable trees: beyond the cells of
  `lean/`'s fragment, for which "`machine_main` appears to prove it", it
  "assumes" that "a `unique` binder, a cell
  and an in-place update are read as an implementation of fresh
  immutable values" (OPEN.md 2's first step, OPEN.md 3). If a mutated
  block were still reachable through a `many` binder whose `is` fact
  names the old contents, (I1) "facts are true" would fail in the heap
  machine, and with it T5's facts from stored values and T7.
- **So, to the handoff's question.** Proving that "the spec makes
  `unique` mean sole reference" is a statement about the spec's
  reachable states. It is a safety invariant, so I expect it to be
  provable inside Sleight for the full semantics. If proved, what
  follows is that the heap machine and a pure tree semantics agree on
  values. That is what would justify reasoning with `is` facts about a
  run, and it is not something the compiler theorem itself uses. It
  does not settle (E) for the stripped run, which still needs (T).

## 7. Decisions for the owner

1. **Intrinsic theorem statements?** Recommended: yes (F1, F2), with
   graph relations only where a separate statement is wanted. The proof
   architecture of every compiler pass depends on this.
2. **`Fails` positive, with exclusivity as a separate lemma?**
   Recommended: yes (§3 T1+T2, T3). The spec tracks' rule set depends
   on it.
3. **How should nondeterminism enter the spec?** Recommended: an oracle
   parameter, and the verdict exists-quantifies it (§4.2.1). Needs:
   the list of choice sources (§2.2), and a rule that keeps a
   rejection-favouring oracle from making completeness vacuous (§3 T3),
   for example crashes outside the oracle.
4. **Is a crash during a compile-time run a rejection, or a third
   outcome?** §72 makes it an error for `native-compute`. DESIGN.md
   does not say for an evaluator crash at compile time. On my reading
   (§3 T3), §31 puts crashes outside "the semantics", so the question is whether [owner 3]'s
   theorem is about the spec, where on that reading no crash occurs, or
   also about an implementation, which "may crash". This is needed
   before [owner 3] can be stated.
5. **What form does T4 take?** I recommend a step machine (§4.3.3) for
   the running compiler, plus a Bove–Capretta or honest-fuel statement
   on the same step for internal "total under H", with uniform totality
   left as a meta-theorem. The Bove–Capretta statement is not a way to
   run anything without fuel or a proof (§4.3 option 1). The alternative is a compile-time budget in
   the language (§4.3.4). Depends on: decision 4 and the compiler
   architecture tracks.
6. **What does "parameterized" mean?** I recommend a model record
   covering extern models, the oracle, and the file system (§4.4.2),
   with the reader as a parameter if the syntax is to be separated.
7. **T6 and wrong behaviour.** Should T6 assume "the spec does not go
   wrong" (CompCert style), or treat going wrong as a behaviour after
   which anything is allowed? Either way, I expect stripped-run safety
   to stay meta (§3 T7).
8. **Which checker's PASS is the final trust root?** Options are
   `lib/`, slc, or both. This affects §5's second row.
9. **Should `unique`-sole-reference and full-semantics safety be proved
   inside Sleight**, as invariants (§6)? I think it is plausible and
   worth it, but it does not remove (E).

## 8. Rough edges and gaps in DESIGN.md (questions, not resolutions)

1. §67, "which one a call answers may differ between runs", together
   with `slot-eq` being usable in run position [proto `sloteq_ct.sl`]:
   acceptance of a fixed text can differ between conforming
   implementations. Is that intended, given [owner 3]?
2. §31, "A real run may crash where the host cannot represent what is
   asked of it": at compile time, outside `native-compute` (§72), is
   such a crash an error at the form, or neither acceptance nor
   rejection?
3. §29, "Every fact derived from a stored value … relies on the
   evaluator having evaluated correctly": in a formal spec, is "the
   evaluator" the spec's own run? If so, the reliance becomes reliance
   on the logic.
4. §45: the character literal's bound proof is "asserted rather than
   decided", so it is an axiom of the spec, unlike numerals, whose
   `Lt` facts go through `prove-literal-lt`.
5. §65, `gensym` "counting from 1 over the whole run": the numbers
   depend on expansion order. I could not find where DESIGN.md fixes the
   order of expansions within one form.
6. §62's "At most 10000 expansions run in one run" and §49's `unary`
   limit ("at most 1024") are the resource bounds in the spec that I
   found. Is either a precedent for a compile-time evaluation budget, or
   are they one-offs?

## 9. Unverified claims

- The diagonal argument (§4.3) assumes that the spec of a program whose
  compile-time code is total halts. Its quine form assumes that
  quines are writable in Sleight; I did not write one. Its macro form
  needs no quine, but rests on the premises of 03 F6 and 09 §3.4, and,
  applied to an intrinsic `compile`, also needs crashes kept out of the
  oracle (§4.3).
- r.e. appears to hold under the readings of 09 §2.2. Σ₁ statements and
  consistency of a coded system are expressible as goals (09 §2.3,
  compiled). D1 to D3 for a formalized `Prov`, the diagonal sentence,
  and any interpretation of HA, IΣ₁, or PRA are unattempted. Whether the
  derivation's internal steps go through (§4.3 (d)) was tried only for
  an abstract relation, with D2, D3, and the diagonal's D1 instance as
  hypotheses (09 §2.4 B, compiled); nothing builds a `Prov` that
  formalizes acceptance. The
  obvious translation of nested implications meets level
  stratification (09 §2.3, compiled); a PRA-style translation with
  first-order implications does not obviously meet it (09 §2.4).
  README.md's IΣ₂ claim is unchecked.
- That determinism lemmas, full-semantics progress and preservation,
  and the sole-reference invariant are provable inside Sleight at
  scale. Only the toy determinism and exclusivity (F2, F5) were
  compiled.
- That forward simulation plus a deterministic target gives refinement
  here, given `slot-eq` and the crash allowances.
- SOUNDNESS.md's (T), (C), and (E) themselves: H rests on (T) and (E)
  (§2.3), and T4 as a meta-theorem on all three (§3 T4).
- That the three sources of a `Halts` argument in F4 are the only ones.
- That uniform stripped-run safety alone, proved inside Sleight, would
  give internal consistency (§4.3). The program shape, with `(lift p)`
  in the final value, is compiled; the internal formalization of
  "accepted" and of the stripped run is not.
- That full-semantics safety is provable inside Sleight. (That uniform
  H, in a form a function can recurse on, is not provable rests on the
  diagonal and the logic's soundness, §4.3.)
- Whether a `many` function recursing on an erased `subterm` derivation
  (F4) is intended by DESIGN.md. §17 and §21 do not forbid it, the
  reference accepts it, and `tests/erased_subterm.sl` ("Subterm
  recursion through an erased argument (section 21)") is a `many`
  function recursing on an erased `subterm` `Nat`.

## Review notes

Added by an adversarial review agent. Every prototype was re-run with
`_build/default/bin/main.exe` (reference unchanged since 164fcf1); each
accepts or refuses as the text says, including `--goal proved: PASS`
for `spec.sl proof.sl`, `2` for `bove_use.sl`, `(ESome _ _)` for
`sloteq_ct.sl` with and without `--no-extern`, exit 0 for `drive.sl`,
and the refusal when `drive.sl`'s step level is minted after `P`.

Errors found and changed:

1. Summary called honest fuel one of "three fuel-free shapes" and
   "[proto, all three]". It uses fuel, and `fuel.sl` held only the
   result type and the bound lemma, not a runner. Reworded; added
   `proto/theorems/fuel_run.sl`, a runner that is accepted.
2. Bove–Capretta was presented as fuel-free and recommended without
   saying plainly that no one can call it without a proof. Added to the
   summary, F4, §3 T4(b), §4.3 option 1, and decision 5: a caller needs
   a `Halts`, which comes from a written-out derivation, a per-input
   halting proof, or a fuel run plus `comptime-match`
   (`proto/theorems/halts_reflect.sl`, added; prints `3` with fuel 10
   and is refused with fuel 2). In the last case the fuel run has
   already done the work.
3. §2.3 said that, by SOUNDNESS.md's argument, "H is *true*". SOUNDNESS.md
   lists (T) and (C) as "what is claimed", calls itself "a sketch"
   outside `lean/`'s fragment, and does not prove preservation of (I1).
   Reworded to "claimed and argued, not established". It also noted
   that a stripped-run H needs (E) as well as (T).
4. §2.3 and T7 said SOUNDNESS.md records that (E) "fails" without (T).
   The text is "Without (T) this step fails", about its argument.
   Quoted it exactly.
5. T7 called the stripped run "[owner 6]'s reading". The brief marks it
   an earlier session's reading, "NOT confirmed". Fixed, also in §6.
6. "This *is* [owner 4(ii)]" and "This is [owner 4(i)]" overclaimed:
   the brief says the owner agreed only in general, not to exact
   statements. Also `Halts o src` is per source, H is uniform, and
   out-of-fuel shows non-termination within `f` steps, not divergence.
   Reworded to "one reading of".
7. "Stripped run … needs (T), the part blocked internally" read as
   established. Hedged: on the Gödel reading only one half of each
   pair, uniform (T) or full safety, can be proved, and which half is a
   guess. §4.3's "every safety property … provable" and the trust table's
   "§4.3 bars proving it" were hedged the same way.
8. The summary and F7 said a relation projected from a record "cannot
   be used in a later type" / "is only an opaque atom". Inside a body,
   after `let-match`, it can stand in a binder's type and is tied to
   the index by forcing (`proto/theorems/project_in_body.sl`, added,
   accepted). What is ruled out is naming it in a signature.
9. F8 dropped README.md's qualifier "with `¬P` read as a level-`L`
   function" and concluded that "no theorem can begin 'either the spec
   run halts or it does not'". The test refutes the uniform schema;
   whether that one instance is refutable is not shown. Fixed.
10. F2 said `exclusive` is "by induction on the `Fails` derivation"; its
    `subterm` parameter is the source `s`. Fixed.
11. §3 T3 claimed that T3 plus T4 give completeness. With an oracle that
    can choose crashes (§4.2 option 1 includes "crash points"), a
    reject-everything compiler satisfies T1 to T3. Added this, with
    §31's "The semantics is that of a machine with unlimited stack and
    heap", to T3, §4.2, and decisions 3 and 4.
12. §8 item 6 said §62's limit is "the only resource bound in the spec";
    §49 bounds `unary` at "at most 1024". Fixed.
13. Added to F6 that the driver consumes only a final value under
    `--goal none` (§27, §71), so a driven compiler's verdict never
    becomes a Sleight value; and to the header that `bove.sl` must
    precede its dependents on the command line.

Uncertain points, not changed:

- The diagonal argument (§4.3) looks right to me, given (T), quines,
  and the logic's soundness, but I did not write a quine either.
- Whether Gödel II's conditions hold for Sleight's spec relation as an
  internal provability predicate is unchecked by author and reviewer.
- Whether the brief's owner items are faithful is outside this review;
  they are a session's paraphrases.
- I did not re-check the "first attempt was refused" claims in F3 and
  F5, only that the final versions behave as described.

## Second review notes

A second adversarial reviewer read DESIGN.md in full and SOUNDNESS.md
parts 1, 3, 5 to 7, and 9 to 11, and re-ran every prototype with the
reference (unchanged since 164fcf1, as are `self/` and `bin/`): each
accepts, refuses, or prints as stated, and `halts_reflect.sl` with
fuel 2 is refused at the `comptime-match` (`expected FDone, got FOut`).

Errors found and changed:

1. Summary, "if the compiler is faithful (T5)". The diagonal needs T1 to
   T4 and determinism through T3; T5 is not needed when Q branches on
   the verdict through `compile-error`, as 03 F6 does. §4.3 said T5 was
   needed; fixed there too.
2. §4.3 and section 9 treated a quine as a premise. 03 F6 gets the
   self-reference from `read-file` in a macro, with its mechanism
   compiled (`proto/fuel/diagonal.sl`). Added; the quine is now needed
   only for the run-position variant.
3. §4.3, "Which half is the provable one is my guess". The diagonal in
   the same section, and option 1 ("no Sleight code can supply `h` for
   every `src`"), already rule out uniform H in a recursable form if
   the logic is sound. Now says so; only full-semantics safety stays a
   guess. Section 9 updated.
4. F7 and §4.4.2, "generic code cannot take apart a derivation of a
   parameter relation". With the relation's constructors and an erased
   `Matchable` passed in, `open-adt` then `let-match` works
   (`proto/review2/05_generic_match.sl`, accepted). Narrowed.
5. F6 and §4.3 option 3, "no Sleight code, compile-time or otherwise,
   can obtain the result of a driven run" (from review note 13). The
   run's own later steps hold it, as `drive.sl`'s `Done` branch does
   with `g`. Now: no compile-time code and no `qed`.
6. Section 9, "I found no test or section that names the pattern" of a
   `many` function recursing on an erased `subterm`. `tests/erased_subterm.sl`
   is exactly that, citing §21. Fixed.
7. §3 T6, CompCert. As I recall it, the forward-to-backward flip needs
   a deterministic target and a receptive source, not a deterministic
   spec. Reworded, hedged as from memory.
8. §2.3, H from SOUNDNESS.md. Added host I/O and part 1's exclusion of
   `--no-prelude` programs with their own models or `def-prim`s.
9. Header, `halts_reflect.sl` also needs `fuel_run.sl` on the command
   line.
10. Summary, `read-file` called a source of "choice". It is a dependence
    on the file system, an input. Reworded.
11. Decision 4 stated "§31 puts crashes outside 'the semantics'" flatly;
    §3 T3 gives it as a reading. Hedged.
12. T6, "DESIGN.md has no coinductive data" cited SOUNDNESS.md for a
    DESIGN.md claim. DESIGN.md does not mention it; reworded.
13. F3, the one-block constraint is specific to `Certified`'s single
    level: an ADT with a level per field accepts two blocks
    (`proto/review2/05_spec_two_levels.sl` + `05_tb_two_level.sl`
    PASS; two blocks against `spec.sl`, `05_tb_one_level.sl`, FAIL).
    Added.

Confirmed: the §9, §21, §67, §71, and §72 quotes; SOUNDNESS.md's "(C)",
"(T)", "a sketch", "Without (T) this step fails", "Values are finite
trees", part 5's "outside the claim", and part 6's "Run-position forms
run total code by (T)"; README.md's anticlassicality and IΣ₂ text;
`self/README.md`'s "What it does not do"; `prelude.sl:67` and the
`def-prim` range (1401 to 2250). The Gödel step (uniform H plus
stripped-run safety gives consistency) holds as far as I can see,
since an erased `(False)` yields a `many` one through an `absurd`
function (`proto/review2/05_erased_to_many_false.sl`, accepted), so
inconsistency gives an accepted `many` run-position `(False)` form.

Unsure:
- Whether Gödel II's conditions hold for Sleight; unchecked by all
  three passes.
- The "first attempt was refused" claims in F3 and F5 beyond my
  two-block check.
- Whether the oracle can be shaped so that completeness is not vacuous
  (decision 3); not attempted.

## Third review notes

A third adversarial reviewer read DESIGN.md in full, SOUNDNESS.md parts
0 to 7, the brief, and OPEN.md items 1 to 4, and re-ran every prototype
and the cited `review2` files with the reference at c236135. Each
behaves as stated.

Errors found and changed:

1. Summary, the diagonal stated without its premise. §4.3 and 03 F6
   condition it on termination; the summary now names SOUNDNESS.md's
   (T), (C), and (E), since §27 strips erased positions before a run.
2. §3 T3, "A compiler that rejects everything satisfies T1 and T2".
   With a positive `Fails` (T1 + T2), `Rejected` must carry a `Fails`
   derivation, so a reject-everything compiler meets T2 only if the
   spec's `Fails` holds of every source. Reworded: T3 rules out such a
   spec.
3. §3 T3, the crash oracle. "Rejects everything" overclaimed: §29 says a
   `def-fns`, `def-adts`, or `def-lvl` "involves no evaluation", so a
   crash can reject only a source that runs compile-time code, and only
   if a compile-time crash counts as a rejection, which is decision 4.
   Both conditions added.
4. Summary, F4, and §4.3 option 1, the sources of a `Halts` argument.
   "A termination proof for that input" left out a proof for every
   input. `proto/review3/05_halts_uniform.sl` (new) proves
   `(Halts Dec s)` for every `s` by an erased function and calls `run`
   from a `many` function with no further argument; it prints `7`. For
   a faithful compiler the diagonal still rules that out, which option
   1 now says.
5. §2.3, "for a spec whose run strips erased positions". §27 says the
   run strips them; quoted.
6. §5 table, "the `def-prim`s at `lib/prelude.sl:1399–2250`". Line 1399
   is the `def-opaque` of `Placed`; the first `def-prim` is line 1401.
7. §6, "`is` facts treat values as immutable terms (§7)". §7 does not
   say so; the immutable reading is SOUNDNESS.md part 3's. Reattributed.
8. Header, a missing Oxford comma.

Confirmed: F5's "first attempt" refusal reproduces in a minimal form
(`proto/review3/05_det_param_bad.sl`: calling an erased `Fn M`
parameter gives "`M` was not in scope when level `(level-of use-det)`
was minted"); the `--goal proved` PASS and the one-level FAIL of F3;
`halts_reflect.sl` with fuel 2 refused at the `comptime-match`; the §9,
§21, §27, §31, §42, §65, §67, §71, and §72 quotes; OPEN.md 1 to 4 as
cited. The §4.3 diagonal (run-position and macro forms) and the step
"uniform H plus stripped-run safety gives internal consistency" hold as
far as I can check, under the premises stated. Gödel II does apply to
intuitionistic theories such as HA, and the CompCert flip does use a
receptive source and a determinate target, both from memory.

Unsure:
- Stripped-run safety alone, proved uniformly inside Sleight, may
  already give internal consistency: an inconsistency yields an
  accepted program whose stripped run calls an `absurd` function
  (`proto/review2/05_erased_to_many_false.sl`). That would need the run
  to reach the call, so H for the forms before it. I did not work this
  out, so T7 is unchanged.
- Whether Gödel II's conditions hold for Sleight; unchecked by all
  three passes.

## Fourth review notes

A fourth adversarial reviewer read the brief, CLAUDE.md, DESIGN.md in
full, SOUNDNESS.md parts 0 to 7 and 9, and OPEN.md 1 to 4, and re-ran
every `proto/theorems/` file (with `bove.sl`, `fuel.sl`, and
`fuel_run.sl` first where needed), `--goal proved spec.sl proof.sl`,
`sloteq_ct.sl` with and without `--no-extern`, and
`proto/review3/05_halts_uniform.sl`. Each behaves as stated.

Errors found and changed:

1. Header: `proto/review3/05_halts_uniform.sl` also needs `bove.sl`
   first; alone it fails with "unbound name `Halts`". Added.
2. Summary, the diagonal's premises. T1 to T3 are erased derivations,
   so the contradiction with a spec `Fails` derivation needs those
   derivations to be true, which is soundness of the logic, not only
   (T), (C), and (E). §4.3 says "assuming soundness of the logic"; the
   summary did not. Added.
3. §4.3, the diagonal applied to an intrinsic `compile`. T3 holds per
   oracle, and `compile` chooses the oracle in its verdict, so the
   argument needs that oracle to govern `compile`'s own run inside Q.
   Added that this holds without `slot-eq`, and otherwise goes through
   the `ENone` copy, as 03 F6 does.
4. §4.3, the Gödel paragraph, an underclaim (third review's unsure
   point). For the stripped run, H is not needed: an erased proof `p`
   of `(False)` gives an accepted program whose first run-position form
   `(lift p)` enters an `absurd` body at once, since stripping drops
   `p`. New `proto/review4/05_stripped_absurd.sl` (with `p` from a
   `def-prim` axiom under `--no-prelude`) is checked and then fails at
   that form with "absurd code reached" under the reference and `slc
   --interpret`. So uniform stripped-run safety alone would give
   internal consistency (my reasoning). Updated §4.3, T7, the summary,
   and section 9.
5. Summary, "Gödel's second theorem ... gives a related limit on
   proving H". Gödel limits H only together with stripped-run safety,
   and (item 4) limits that safety alone; the summary also omitted
   consistency as a condition. Reworded.
6. §4.3 option 1, "no Sleight code can supply `h` for every `src`" was
   unconditional. Now "under its premises".
7. §5 table, row 1: an erased derivation corresponding to one that
   exists needs (T) for it to finish and (S)'s preservation for its
   type, not "(T)+(E)" alone. Now (T), (S), and (E).

Confirmed: the §9, §21, §27, §31, §42, §65, §67, §71, and §72 quotes;
SOUNDNESS.md's "(C)", "(T)", "a sketch", "does *not* prove", "Without
(T) this step fails", and part 6's "Run-position forms run total code
by (T)"; README.md's anticlassicality and IΣ₂ text; `prelude.sl:67` and
the `def-prim` range 1401 to 2250; the run-position quine diagonal of
§4.3 (with completeness, cr(Q) = Ok v gives v = v + 1, and Fail gives
Ok 0); the Gödel step "uniform H plus stripped-run safety gives
internal consistency"; and T3's weak-completeness reading.

Unsure:
- Item 4 rests on formalizing "accepted" and the stripped run inside
  Sleight, which no one has tried.
- §4.3's quine form and 03 F6 both lean on SOUNDNESS.md's claims for a
  program that may be rejected; 03's fourth review notes say how that
  scope is read.
- Whether Gödel II's conditions hold for Sleight; unchecked by all four
  passes.

## Fifth review notes

A fifth adversarial reviewer read the brief, CLAUDE.md, DESIGN.md in
full, SOUNDNESS.md in full, OPEN.md 1 to 4, and README.md's "Logic and
strength", and re-ran every `proto/theorems/` file, `--goal proved
spec.sl proof.sl`, `sloteq_ct.sl` with and without `--no-extern`,
`proto/review3/05_halts_uniform.sl`,
`proto/review2/05_erased_to_many_false.sl`, and
`proto/review4/05_stripped_absurd.sl` under both implementations. Each
prints or refuses as the body says.

Errors found and changed:

1. §4.3, the stripped-run Gödel step (added by fourth review note 4).
   It said an erased proof `p` of `(False)` "gives an accepted program
   whose first run-position form is `(lift p)`". That program is not
   accepted: the run-position form runs during checking, so it is
   refused at that form (`proto/review4/05_stripped_absurd.sl`;
   `--extract` fails with "absurd code reached"), and a refused program
   says nothing about the safety of accepted ones. The step holds with
   `(lift p)` in the body of a final `(Fn L -> (many (Nat) r))` instead:
   `proto/review5/05_stripped_absurd_final.sl` (new) is accepted by
   `--extract` and `--build`, and the reference, the built program, and
   `slc --interpret` stop with "absurd code reached". §4.3 and section 9
   updated. The second review's "Confirmed" remark, "inconsistency gives
   an accepted `many` run-position `(False)` form", has the same flaw.
2. §4.3, the quine diagonal had Q "compute `cr(Q)` in run position" and
   then used (T), which SOUNDNESS.md states for accepted programs; such
   a Q is accepted only if that run ends (the fourth review's unsure
   point). With the call in Q's final value, Q is accepted before `cr`
   runs (§29) and the driver's call is covered. Rewritten; the macro
   form now points to 03 F6's matching detour. Section 9's "run-position
   form" is now "quine form".
3. §4.3, "H ... together with internal stripped-run type safety". "Take
   an accepted program with a `many` run-position form of type
   `(False)`" was self-defeating: if the program is accepted, that form
   already ran. It now takes a form the checker accepts, and H read as
   covering every such form, as [owner 4]'s "every accepted
   compile-time form" reads.
4. §2.3, "it is not something Sleight can prove about itself" had lost
   §4.3's qualifiers (for all programs, in a form a function can
   recurse on, if the logic is sound), as 03's summary had before its
   fourth review. Restored.
5. §3 T3, the crash oracle "rejects every source that runs any
   compile-time code". With the shipped prelude that is every source:
   its own run-position forms run code (`lib/prelude.sl:354` calls
   `pow2`). Added.
6. §2.2, the expansion order. Added §6's one statement on it, "The head
   is elaborated first."
7. F7, `(many Type T)` "is accepted": it is, with a warning that a
   `Type` is always erased (both `manytype` files). Added.

Confirmed: README.md:107-119 as quoted in F8 and F9 (the IΣ₂ sentence
says "anticlassicality aside"); OPEN.md 1 to 4 as used in §1 and §5;
SOUNDNESS.md's part 1 claims and scope, part 5's "outside the claim",
part 6, and part 7's "Without (T) this step fails"; `prelude.sl:67`,
`1337-1342`, and the `def-prim` range 1401 to 2250; DESIGN.md says
nothing of an evaluator crash at compile time (grep "crash": §31, §39,
§42, §72 only) and mentions no coinductive data. The step "uniform (T)
plus full-semantics safety gives internal consistency" holds with the
final-value program of item 1, and the T4(c) step from the F5 lemma
(`Lt f k` against `f ≥ k`) checks.

Unsure:
- Item 1's program takes `p` from a `def-prim` under `--no-prelude`,
  which SOUNDNESS.md part 1 excludes; it shows only the shape that an
  internal proof of `(False)` would give.
- Items 1 and 2 read SOUNDNESS.md part 5 as covering the driver's call
  of a final value.
- Whether Gödel II's conditions hold for Sleight; unchecked by all five
  passes.
- 00-summary's Gödel bullet repeats item 1's flaw ("so the program is
  refused") and needs propagating; not edited here.

## Coordinator notes

1. §1, §4.3's Gödel paragraph, T7, and §9 now state Gödel's second
   theorem in the conditional form of 09 §4, as corrected by 09's
   review: consistency, D1 for a formalized `Prov` ((b)), D2, D3, and a
   diagonal sentence ((c)), which may be built by a macro that reads the
   unit's text, and, for the safety limits, the lemma that
   `(Prov ⌜False⌝)` yields an accepted program whose stripped run
   reaches absurd code; none attempted. §4.3's IΣ₂ sentence now says
   that README.md derives that strength from the functions Sleight
   computes, which supplies no interpretation of arithmetic closed under
   deduction; 09's two suggested IΣ₂ sentences are merged into one.
   §4.3's "meets the theorem's conditions" is now "meets the conditions
   above". §9's Gödel item now lists what appears to hold, what is
   compiled, and what is unattempted (09 §2.2 to §2.4). The fifth
   review's unsure point "Whether Gödel II's conditions hold for
   Sleight" is answered only in part: they remain unattempted. From 09
   §2 and §4.

## Round 6 review notes

A sixth adversarial reviewer read the brief, CLAUDE.md, DESIGN.md in
full, SOUNDNESS.md parts 0 to 7, OPEN.md 1 to 4, README.md's "Logic
and strength", and 09 as it now stands, and re-ran every
`proto/theorems/` file (with `bove.sl`, `fuel.sl`, and `fuel_run.sl`
first where needed), `--goal proved spec.sl proof.sl`, the two
`review2` level files, `review3/05_halts_uniform.sl` (prints `7`),
`review3/05_det_param_bad.sl`, `review2/05_generic_match.sl`,
`review2/05_erased_to_many_false.sl`, `review4/05_stripped_absurd.sl`
(`--extract` fails), `review5/05_stripped_absurd_final.sl`
(`--extract` succeeds; the run stops with "absurd code reached"), and
the `proto/godel/` files 09 §2.3 cites, under the reference and, for
the goals, `slc`. Each behaves as stated.

Errors found and changed:

1. §4.3's Gödel paragraph, the summary, T7, and §9, taken over from 09
   §4. "Then, by the usual derivation from these conditions" claimed
   that consistency, D1, D2, D3, and a diagonal sentence suffice. That
   derivation also composes implications inside the theory (for
   instance ⊢ Con → G), which in Sleight means building functions under
   level stratification; 09 §2.4 A names "closure under logic" as the
   obstacle, and 09 §2.4 B finds it only "not obviously" blocked for
   `Prov`. Added it as condition (d), unattempted. 09 §4's suggested
   wording has the same gap.
2. Summary, "none of which has been attempted" followed a list whose
   first item is consistency, OPEN.md 1, on which SOUNDNESS.md and
   `lean/` work. Reworded; T7's "(all unattempted)" had the same flaw.
3. Summary, "and, since T1 to T3 are stated by erased derivations, its
   logic is sound" read as deriving soundness from the derivations.
   Reworded to say that the argument needs soundness because of them.
4. §4.3, the quine diagonal said flatly that (T) and (E) cover the
   driver's call of Q's final value. SOUNDNESS.md does not mention that
   call; 03 F6 and 09 §3.2 treat it as a reading. Hedged, also for the
   macro form.
5. §2.3, H from (T) and (E). (T) is stated "about any program the
   checker accepts" (part 1), while H concerns forms of every source;
   the step reads (T) form by form, as part 6 does. Also, (E) gives
   termination of the stripped run only on 09 §3.2's reading of
   "follows". Both added.
6. §5 table, row 1 still said "if Gödel II applies (unchecked)", the
   form the coordinator replaced elsewhere. Now names uniform
   stripped-run safety and §4.3's conditions.
7. F2, a missing Oxford comma.

Unsure:
- T4(b) and (c) mention the oracle `o` without binding it, and a fixed
  `o` would have to govern `compile`'s own `slot-eq` answers, as §4.3
  says for T3. Pseudo-Sleight, so unchanged.
- Whether condition (d) is better read as part of "Sleight proves D2
  and D3"; stated separately here because the usual statement of the
  conditions assumes a theory closed under logic.
