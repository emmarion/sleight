# 05. The theorem statements, and what can and cannot be proved inside Sleight

Written by a Claude agent overnight, as one input to the owner's review.
Everything here is a proposal or an agent's reading. Nothing in it is
approved, and nothing here is a design decision (CLAUDE.md rules 1 and 11).

Sources are marked: **§n** quotes DESIGN.md; **file:line** is code;
**[proto]** is a test under `proto/theorems/`, compiled with the
reference (`_build/default/bin/main.exe`) at commit 164fcf1;
**[owner n]** is item n of the brief's "Owner decisions"; everything
else is my own reading and is hedged as such.

## 1. Summary

- Because §9 bars calls from types, "`compile src` = Accepted ⇒ …"
  cannot be written as a type. The workable form is *intrinsic*:
  `compile` returns its verdict together with an erased spec derivation.
  A toy checker in that form, together with an exclusivity lemma, is
  accepted, and packaging it as `(goal many (Certified))` passes
  `--goal proved` [proto].
- T1 (acceptance soundness) and T2 (rejection soundness) are then the
  type of `compile`. T3 (exclusivity) needs the spec to be deterministic.
  As DESIGN.md stands it is not: `slot-eq` may answer either way
  (§67) and can decide acceptance at compile time [proto]. Crashes,
  `native-compute` and `read-file` add more choice. My proposal is an
  oracle parameter, with T3 stated per oracle.
- In my reading, T4 (every source is accepted or rejected) cannot be an
  unconditional Sleight function if the compiler is faithful (T5): a
  diagonal (quine) argument rules out a total, sound, and complete
  run-function for Sleight source written in Sleight. Gödel's second
  theorem gives a related limit on proving H. Three fuel-free shapes do
  compile: recursion on an erased `Halts` derivation, a typed step
  machine driven by `Program`, and "honest fuel", whose out-of-fuel
  result carries a proof [proto, all three].
- Parameterizing the semantics works through erased `TyCtor`
  parameters and model records indexed by them [proto]. A relation
  projected out of a record cannot be used in a later type.
- The theorems mean something only if Sleight's logic is sound in a
  sense stronger than consistency, because the derivations are erased.
  A proved compiler can take the elaborator, the compile-time evaluator,
  and OPEN.md 4 out of the trust base. It cannot remove OPEN.md 1–3,
  the axioms' justification, or the checker that checks the proof.
- "`unique` is the sole reference" is not needed for compiler
  correctness against a mutating heap-machine spec. It is what connects
  that heap machine to the tree reading of values that the fact table
  depends on.

## 2. Findings

### 2.1 What a theorem can be in Sleight

- **F1. No calls in types.** "The elaborated form of a type never
  contains a function call" (§9). Compiled: `(Eq (Nat) (f n) (Succ n))`
  is refused with "`f` … cannot be applied in a term, where only a type
  or value constructor can be applied (§9)"
  [proto `call_in_type_bad.sl`]. So a theorem about a function's output
  is stated in one of two ways. Either it is *intrinsic* (the function
  returns an erased proof about its result), or it is about an inductive
  *graph relation* written alongside the function, which duplicates it.
- **F2. Intrinsic certified checker works.** [proto `t1_toy.sl`] declares
  a toy `Src`, a positive `Elab` relation and a positive `Fails` relation,
  plus `Verdict s` with `Accepted (erased (Elab s))` and
  `Rejected (erased (Fails s))`. The function
  `compile : (subterm many (Src) s) -> (many (Verdict s) r)` and the erased
  lemma `exclusive : … (Elab s) (Fails s) -> (False)` (by induction on
  the `Fails` derivation) are accepted, and the program runs.
- **F3. A theorem as a goal.** §71: "`(goal m T)` sets the goal of a unit
  … A goal is one type, not a telescope; an existential … is packaged by
  an ADT (§21)." [proto `spec.sl` + `proof.sl`] packages
  `(many (Fn L (many (Src) s) -> (many (Verdict s) r)) c)` together with
  the erased exclusivity function into `Certified`.
  `--goal proved spec.sl proof.sl` prints `--goal proved: PASS`. Both
  functions had to be in one `def-fns` block, because the ADT fixes one
  level `L` for both fields. My first attempt, with two blocks, was refused.
- **F4. Fuel-free recursion on an erased derivation (Bove–Capretta
  style).** §21: "Subterm recursion (§17) may go through an erased
  field." [proto `bove.sl`] defines
  `run : (many (Nat) s) (subterm erased (Halts R s) h) -> (many (Nat) k) (erased (RunsTo R s k) r)`.
  It is a `many` function that dispatches on `s`, takes `h` apart with
  `let-match erased`, and recurses with `(subterm sp)` on the erased
  sub-derivation. `R` is a relation parameter, and the step function and
  a determinism lemma are passed in through a §57-style factory. It is
  accepted. Instantiated with a toy step and a hand-built `Halts` at the
  top level [proto `bove_use.sl`], it prints `2`.
- **F5. Honest fuel.** [proto `fuel.sl`] declares a fuel-result type
  whose out-of-fuel constructor carries
  `(erased (Prefix R s f (Succ t)))`: the spec run has a non-final state
  after `f` steps. It also proves the lemma "a halting run of length `k`
  and a non-final prefix of length `n` give `(Lt n k)`", by induction on
  the prefix, given determinism. The lemma has to sit behind a factory:
  calling a function parameter needs a `Predates` that only a level
  minted after the parameter can have (§18, §57). The first attempt was
  refused with "`M` was not in scope when level … was minted".
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
  leaves "outside the claim".
- **F7. Parameterization mechanisms.** A relation is an erased parameter
  of `TyCtor` type, as in the prelude's `Cmp` (`lib/prelude.sl:67`).
  [proto `model.sl`] defines `(Model R)`, an ADT indexed by the relation
  `R`, whose fields are a `many` step function at an erased level and an
  erased determinism lemma. A function generic over `(many (Model R) md)`
  unpacks it and is accepted. [proto `record.sl`] shows that an ADT with
  relation-valued *erased fields* is accepted, and a projected field can
  be applied in an erased expression. By F1, though, a relation obtained
  by projection is only an opaque atom in later types, so the usable form
  is "index the record by its relations". `(many Type T)` is accepted as a
  parameter declaration, but no non-erased argument exists: `(f (Nat))`
  gives "type constructor `Nat` applied in a non-erased position"
  [proto `manytype_bad.sl`, `manytype2_bad.sl`], consistent with §21 "A
  value of type `Type` is erased." A `TyCtor` parameter has no opened
  `Matchable` (§8), so generic code cannot take apart a derivation of a
  parameter relation. It can only use the lemmas the model supplies.
- **F8. The logic is anticlassical.** README.md "Logic and strength":
  "excluded middle at any level `L` … gives a function that returns
  `False`" (`tests/anticlassical.sl`). So no theorem can begin "either
  the spec run halts or it does not".
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
  the order in which several macro calls within one form expand. (The
  evaluation-order question in general belongs to other tracks.)

### 2.3 What SOUNDNESS.md already says about H

SOUNDNESS.md part 1 claims "(C) Checking terminates" and "(T) Totality
… every function activation returns, apart from a crash". Taken
together, these are what [owner 4]'s hypothesis H asserts: every
accepted compile-time form's run halts. So, by that note's (unproved,
outside `lean/`) argument, H is *true* about Sleight. It is just not
something Sleight can prove about itself (§4.3 below). Part 7 also
records that "(E)" (the stripped run follows the full one) "fails"
without (T). That matters for T7.

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

T3 matters for more than tidiness. A compiler that rejects everything
satisfies T1 and T2. T3 plus T4 give completeness: if `Elab o src c`
holds and `compile` halts, it cannot reject under `o`.

**T4 (totality).** Four forms:
- (a) meta-theorem only: it follows from SOUNDNESS.md (T) and (C) plus
  the compiler proof;
- (b) Bove–Capretta (F4):
  `compile-h : (many (String) src) (subterm erased (Halts o src) h) -> (many (Verdict src) v)`.
  This *is* [owner 4(ii)] as a type;
- (c) honest fuel (F5):
  `compile-fuel : (subterm many (Nat) f) (many (String) src) -> (many (FuelVerdict src f) v)`.
  Its `OutOfFuel` carries `(SpecPrefix o src f st)` and `(NotFinal st)`.
  This is [owner 4(i)] as a type: running out of fuel proves that the
  spec run is still going. Combined with the F5 lemma, `Halts-in o src k`
  and `f ≥ k` rule out `OutOfFuel`;
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

DESIGN.md has no coinductive data (SOUNDNESS.md part 3: "Values are
finite trees"), so behaviours are finite trace prefixes. `SpecAllows`
must admit "prefix then crash" (§31). It must also say what happens
after the spec goes wrong; see T7. Forward simulation from the spec
plus a deterministic target gives backward simulation in the usual way
(the CompCert pattern, cited by name only). That route needs the spec
to be deterministic given `o`, and the target's `slot-eq` answers to be
expressible as an oracle the spec can choose.

**T7 (safety of the spec itself).** Two levels:
- *Full semantics* (erased code runs): progress and preservation of a
  typed state are an induction over finitely many steps. I expect them
  to be provable inside Sleight, because they need no termination.
  This is unverified.
- *Stripped run* (erased code removed, which is [owner 6]'s reading):
  "never enters a refuted branch" needs every erased proof to *exist*
  in the full semantics. That is SOUNDNESS.md (E), which needs (T), the
  part blocked internally (§4.3). So, under [owner 1]'s "no `no_false`",
  T7 for the stripped run stays a meta-theorem. T6 then either assumes
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
   must anticipate every source of choice.
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
  is a `Nat`. A program Q containing its own text (a quine; strings make
  this routine) can compute `cr(Q)` in run position and return its value
  plus 1, or 0 on `Fail`. Q's own code is total, so the spec run of Q
  halts. Soundness and completeness then contradict each other. So,
  assuming soundness of the logic and the existence of quines (I have not
  written one), no internal total, sound, and complete compile-and-run
  for Sleight source exists. This is the classical "no total
  self-interpreter on source text" barrier. Brown and Palsberg's typed
  self-interpreter for F_ω, cited by name, escapes it only because its
  input is a typed representation, not text.
- **Gödel.** In the form for effectively axiomatized theories that
  satisfy the Hilbert–Bernays–Löb derivability conditions (cited by
  name), a consistent theory cannot prove its own consistency. Intuitionistic
  theories such as HA are covered, so anticlassicality (F8) does not
  obviously exempt Sleight. The claimed IΣ₂ strength (F9) appears to be
  more than such results usually need. I have not checked that Sleight
  meets the conditions.

  H, read uniformly over all programs, together with internal type
  safety would imply internal consistency. Take an accepted program with
  a run-position form of type `(False)`. H says its run halts with a
  value, preservation says the value has type `(False)`, and canonical
  forms say no such value exists. "Normalization implies consistency"
  is the general form of this. So, if Sleight is consistent, it cannot
  prove both uniform H and stripped-run safety.
- **What remains provable inside Sleight.** H for one particular program
  may be provable, for example by building `Halts` for slc's own
  source. So are anything conditional on H, every safety property of
  the full semantics, determinism, and exclusivity.

Options:

1. **(b) Bove–Capretta.** *Pro:* no fuel at all, the hypothesis is
   erased and so free at run time, and it states [owner 4(ii)] exactly.
   *Con:* someone must supply `h`; the top level cannot do so without a
   proof. If the logic were unsound, `h` could be fake and `compile-h`
   could diverge. *Cost:* low (F4).
2. **(c) Honest fuel.** *Pro:* runs anywhere; out-of-fuel is evidence,
   not silence. *Con:* it is fuel, which [owner] wants minimized. A large
   constant makes it practically unbounded. *Cost:* low (F5).
3. **(d) Step machine + `Program` loop** [owner 2]. *Pro:* no fuel; the
   divergence is the driver's, outside every function; T1/T2 as an
   invariant. *Con:* the whole compiler, including the compile-time
   evaluator, must be written as an explicit-state step (other tracks).
   Internal T4 additionally needs (b) or (c) on the same step function,
   or a graph relation of it (F1). *Cost:* high, since this is the
   compiler's architecture.
4. **Resource budget in the language.** The spec rejects any compile
   whose compile-time runs exceed a bound, as §62 already does for
   expansions ("At most 10000 expansions run in one run"). *Pro:* T4
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
   cannot match on parameter relations (F7), and every helper that calls
   a parameter function needs a factory (F5).
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
| Sleight's logic is sound (OPEN.md 1–3), in a sense stronger than consistency: an erased derivation in `Verdict` must correspond to one that exists, which is SOUNDNESS.md (T)+(E) | §14, SOUNDNESS.md 1 | No. §4.3 bars proving it internally. `lean/` covers a fragment. Option 4.1.3 moves it onto a certificate checker. |
| The checker that checks the proof: `lib/` (OCaml), or slc compiled to OCaml | MANUAL.md `--goal` | No. It can be mitigated by checking with both, or by a proved slc checking its own proof. That is a consistency check, not a proof; CakeML's in-logic bootstrap, cited by name, is the known pattern. |
| Axioms `predates-trans`, `subterm-trans`, `predates-subterm` (§18), `gensym-unique` (§65), `placed-slot`, `placed-eq` (§66) | §18, §65, §66 | Not from the logic. Their truth *in the spec* (SOUNDNESS.md (I2), (I3), and the gensym counter) are safety invariants that I expect to be provable inside Sleight. Using them for the stripped run still needs (E). |
| Character literal bounds "asserted rather than decided" | §45 | Yes in principle: a lemma over the 256 codes, decided rather than asserted. |
| Facts from stored values: `comptime-match` (§28, §29), `prove-literal-lt` (§45), `unary` (§49), the handle primitives (§64, §65) | §29 "relies on the evaluator having evaluated correctly"; OPEN.md 4 | Yes, if the checker's evaluator *is* the proved one (T5). OPEN.md 4 then reduces to OPEN.md 1. A proof that avoids run-position reflection does not depend on them. |
| `native-compute` (§72) | §29, §72 | Only if T6 is proved for the compiled code and the OCaml toolchain is trusted. |
| Extern implementations agree with their models, except `slot-eq` (§42) | §42; SOUNDNESS.md 11 | Yes, for programs checked and compiled with models only (`--no-extern`). Not for primitives without a model (`slot-eq`, `world-do`, the `def-prim`s at `lib/prelude.sl:1399–2250`). |
| Prelude `def-prim`/`def-opaque` signatures and extern models | SOUNDNESS.md 1 | No: they are part of the spec. |
| The elaborator implementation (`lib/elab.ml`, `self/elab*.sl`) and slc's interpreter | `self/README.md` "What it does not do" | Yes. This is the point of the project. |
| The spec's faithfulness to DESIGN.md prose | — | No. It is irreducible, but T3 plus completeness guard against a vacuous spec. |
| The OCaml compiler, the runtime, zarith (`lib/ffi_core.ml` `small`), and the host | SOUNDNESS.md 11 | No, unless T6 is extended below OCaml (out of scope). |

## 6. `unique` as sole reference

§13: "Where a value can be mutated in place … a `unique` binder on that
value is the only reference to it." My reading of its role:

- **For compiler correctness (T6) against a mutating heap-machine spec
  [owner 6], it is not needed.** If the spec stores into the same block
  the compiled code stores into, any aliasing is reproduced step for
  step. The simulation relates heaps, not trees.
- **It is what makes the heap machine agree with the tree reading** that
  the fact table relies on. `is` facts treat values as immutable terms
  (§7), and SOUNDNESS.md part 3 "assumes" that "a `unique` binder, a cell
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
   the list of choice sources (§2.2).
4. **Is a crash during a compile-time run a rejection, or a third
   outcome?** §72 makes it an error for `native-compute`. DESIGN.md
   does not say for an evaluator crash at compile time. This is needed
   before [owner 3] can be stated.
5. **What form does T4 take?** I recommend a step machine (§4.3.3) for
   the running compiler, plus a Bove–Capretta or honest-fuel statement
   on the same step for internal "total under H", with uniform totality
   left as a meta-theorem. The alternative is a compile-time budget in
   the language (§4.3.4). Depends on: decision 4 and the compiler
   architecture tracks.
6. **What does "parameterized" mean?** I recommend a model record
   covering extern models, the oracle, and the file system (§4.4.2),
   with the reader as a parameter if the syntax is to be separated.
7. **T6 and wrong behaviour.** Should T6 assume "the spec does not go
   wrong" (CompCert style), or treat going wrong as a behaviour after
   which anything is allowed? Either way, stripped-run safety stays
   meta (§3 T7).
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
6. §62's expansion limit is the only resource bound in the spec. Is it
   a precedent for a compile-time evaluation budget, or a one-off?

## 9. Unverified claims

- The diagonal argument (§4.3) assumes that quines are writable in
  Sleight, and that the spec of a program whose run-position code is
  total halts. I did not write a quine.
- That Sleight meets the conditions of Gödel's second theorem (r.e.
  checker, enough arithmetic, derivability conditions), and README.md's
  IΣ₂ claim.
- That determinism lemmas, full-semantics progress and preservation,
  and the sole-reference invariant are provable inside Sleight at
  scale. Only the toy determinism and exclusivity (F2, F5) were
  compiled.
- That forward simulation plus a deterministic target gives refinement
  here, given `slot-eq` and the crash allowances.
- SOUNDNESS.md's (T), (C), and (E) themselves, on which "H is true"
  rests.
- Whether a `many` function recursing on an erased `subterm` derivation
  (F4) is intended by DESIGN.md. §17 and §21 do not forbid it, and the
  reference accepts it, but I found no test or section that names the
  pattern.
