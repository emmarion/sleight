# 09. Gödel's second theorem, and SOUNDNESS.md part 5 for 03's detour

Written by a Claude agent overnight, as a follow-up to 03 and 05. It is
an agent's reading. Nothing in it is approved or decided, and where it
and DESIGN.md or SOUNDNESS.md disagree, those files are right. Standard
results are named from memory, without checked statements or page
references.

## 1. Summary

- **Q1, Gödel II.** On my reading, nothing found so far stops Gödel II
  from applying to Sleight. Nothing establishes that it does, either.
  The "theory" is the set of goal types that pass `--goal proved`
  (§71). That set is r.e. under conditions I list. It does not need
  checking to terminate. Types can state Σ₁ facts ("there is a
  derivation") and consistency of a coded system as goals, with no call
  in a type (compiled, `proto/godel/`). The missing step is the internal
  one: a Sleight relation `Prov` that formalizes acceptance and meets the
  derivability conditions D1 to D3, with D2 and D3 proved inside
  Sleight, and with the usual derivation's internal steps going through
  despite level stratification (§2.4 B). Nobody has built it. For an
  abstract relation `P` in place of `Prov`, given D2, D3, and the
  diagonal's D1 instance as hypotheses, with G taken to be ¬`P ⌜G⌝`
  itself, the derivation's internal steps compile (`g2_defs.sl` with
  `g2_step.sl`); reading G that way puts conditions on its code
  (§2.4 B). Its final step to ⊥ is accepted at the top level, but only
  with consistency postulated by a `def-prim` that gives an element of
  every type, for a relation that holds of every code
  (`review7/09_g2_final.sl`), which shows how the step elaborates and
  nothing more. So 03 and 05 may claim Gödel-based limits only
  conditionally on the missing step (§4 gives the wording they carry,
  revised there since). §9 does not force the diagonal sentence to be
  built from a relational `Sub`: a macro in a goal type can splice in
  the text of its own file (`r_self_goal.sl`, compiled).
- **What the cheap diagonal already gives.** 03's `read-file` diagonal
  gives two things without Gödel, under the premises of §3.4 and §2.5:
  no faithful, hypothesis-free, non-erased `compile`; and no uniform H
  in a form a function can recurse on. Separately, a Kleene-style
  argument (§2.4) would give an unprovable true non-halting statement,
  given r.e., Σ₁-completeness for a halting relation of a machine whose
  halting is undecidable, and consistency.
  Gödel II adds limits on Π-type statements: uniform safety,
  and (T) together with safety. It also needs only consistency, not
  soundness. Its price is the internal `Prov` step above.
- **The obvious arithmetic translation meets level stratification.**
  One route is to show that Sleight interprets HA or IΣ₁. Implication is
  level-stratified: a body cannot apply a closure whose level arrives
  packed in an argument or in a call's result (compiled). That blocks
  the translation of nested implications in its obvious form. It does
  not obviously block a rule-based, PRA-style translation whose
  implications are first-order (data to data): an induction function
  from packed premises to a packed conclusion compiles
  (`r_induction_rule.sl`). Whether that covers all of PRA is unchecked.
  The `Prov` route needs first-order implications too, apart from
  steps such as ⊢ Con → G, whose antecedent is itself a closure; like
  the induction function, that step compiles through a factory in the
  abstract form of §2.4 B.
- **Q2, 03's detour.** SOUNDNESS.md never mentions the driver's call of
  a final `Fn` value. Part 5 says only that "the driver's loop over a
  `Program` (§42) is outside the claim, each step being a total call".
  Part 5's measure argument does not depend on who calls the root
  activation, so I read it as covering that call, but that is a reading.
  `03_detour.sl` is accepted and prints `(BFalse)` under the reference,
  built by the reference, under `slc --interpret`, and built by slc. Its
  prefix is byte-identical to `diagonal.sl`'s text before `(diag)`, and
  its literal equals `diagonal.sl` (checked). Under the premises in §3.4
  the argument goes through.

## 2. Q1: does Gödel II apply?

### 2.1 What theory the checker defines

DESIGN.md §71: "`(goal m T)` sets the **goal** of a unit ... `(qed e)`
discharges the goal: `e` is checked against `T` at `m`". Under
`--goal proved`, "Standard output holds one line: `--goal open: PASS` or
`--goal proved: PASS` when the requirement is met".

My proposed reading: fix a vocabulary V (the shipped prelude plus fixed
definition files). A *sentence* is a type T in §9's grammar over V. T is
a *theorem*, written ⊢ T, when some files F make
`--goal proved V S_T F` pass, where S_T is a file holding
`(goal erased T)`. `erased` is the natural mode for propositions. A
`many` goal needs a run-time value as well. *Consistency* means that no
F makes `(goal erased (False))` pass, with the prelude's `False`
(`lib/prelude.sl:15`; DESIGN.md §59 declares one the same way; any type whose opened `Matchable` lists no constructors
would serve, §25).

Three things make this a theory *relative to* fixed choices, not one
fixed set (my reading):
- `read-file` (§65) reads files under the source directories, so a
  verdict depends on the file system. I count the files a unit may read
  as part of F.
- `slot-eq` may answer either way (§67), so "passes" must mean "some
  permitted run passes" or "every permitted run passes". 05 §2.2 lists
  this and other sources of choice (crashes, `native-compute`).
- Flags change the language (`--no-prelude` admits `def-prim` axioms,
  which SOUNDNESS.md part 1 excludes, though both implementations
  refuse it with `--goal proved`, MANUAL.md; `--fn-same`). I fix the
  default flags.

### 2.2 Is the theory recursively enumerable?

Under "some permitted run passes", ⊢ T is Σ₁: there exist files F and a
finite elaboration trace that accepts. That needs only that whether a
finite trace is an accepting trace of a given unit is decidable. It does
not need checking to terminate, on any unit. Under "every permitted run
passes", ⊢ T is Σ₁ too if the spec's elaboration is finitely branching
(`slot-eq` has two answers; the file system is fixed by F): a passing
unit then has a finite tree of runs, by König's lemma, and that tree is
the witness. DESIGN.md is prose, so that the check is decidable is my
reading of it. The implementations are evidence only for the inputs
run: each such run ended. The reference's evaluator has no fuel bound
unless `--eval-fuel` sets one, and slc's default is 1000000000
(MANUAL.md). A run that finishes is a finished run, if its evaluator is
faithful (SOUNDNESS.md part 11 lists the evaluator as trusted).

Decidability would need (C) for every source. SOUNDNESS.md part 1 states
(C) "about any program the checker accepts" (line 45). Read literally,
that is vacuous for deciding acceptance, as 03's fourth review notes
say. Part 6's argument read per run, "Run-position forms run total code
by (T)", would give termination of every elaboration, and so a meta-level
decision procedure. 03 F6 shows that no Sleight function decides it,
under 03's premises. Gödel II needs only r.e., so (C) does not matter
for Q1.

### 2.3 What types can state, given §9

§9: "The elaborated form of a type never contains a function call".
`proto/theorems/call_in_type_bad.sl` is refused. So every function
symbol of arithmetic must enter a statement as its graph, an inductive
relation, together with lemmas for totality and functionality. This is
the usual relational treatment of arithmetic. The prelude already does
it for addition and multiplication:
- `Add` (`lib/prelude.sl:33`) and `Mul` (`:225`) are the relations;
- `add` (`:173`) and `mul` (`:236`) return an erased `Add`/`Mul` proof;
- `add-fn` (`:407`) and `mul-fn` (`:413`) give functionality as `Eq`;
- `Eq`/`Refl` are at `:19-21`;
- `Nat` is a `def-adts` (`:10`), so §7 forcing gives `Succ` injective
  and `Zero ≠ Succ`.

So the relational translations of Robinson Q's axioms look provable to
me; each is a first-order `Fn` statement. I did not write them out.

Compiled (`proto/godel/`; reference and `slc --goal proved` both PASS):
- `sys.sl` defines codes `Fm` (`Bot`, `At n`, `Imp`), a Hilbert-style
  derivation relation `Deriv` (axiom K and modus ponens), and the graph
  `Ev` of the all-atoms-true valuation, which stands in for an `eval`
  that §9 cannot put in a type.
- `sys.sl sigma1.sl` proves the Σ₁ goal
  `(Deriv (Imp (At 2) (Imp (At 0) (Imp (At 1) (At 0)))))`, a statement
  that a derivation exists, by a closed term using MP.
- `sys.sl con.sl` proves the consistency goal `(Con)` for that system:
  an ADT packing a level and an erased `(Fn L (erased (Deriv (Bot)) d)
  -> (erased (False) no))`. The proof uses soundness for `Ev` by
  recursion on derivations, with first-order lemmas called across
  levels.

So "there is a derivation", "this program halts" (05's `bove.sl`
`Halts`), and "the coded system Σ proves no ⊥" can all be goal types.
Statements about Sleight itself would need Sleight's acceptance as such
an inductive relation. That is the project's spec, and it does not yet
exist.

**Implication is level-stratified** (compiled, reference and slc
agree):
- `hyp_fixed.sl` (accepted): a level-`L` function applies a hypothesis
  of type `(Fn M ...)` when `M` was minted before `L`.
- `hyp_packed_bad.sl` (refused, "`K` was not in scope when level
  `(level-of mp)` was minted"): a hypothesis whose level `K` arrives
  packed in an ADT cannot be applied in the body.
- `hyp_factory.sl` (accepted): after unpacking, a body can mint a fresh
  level and build a *new* packed closure that applies the hypothesis,
  the factory pattern of §57.
- `sys.sl top_mp.sl` (PASS): at the top level such a packed function
  applies freely (§20: "The top level is above every function level").

- `r_result_closure_bad.sl` (refused by both, "`K` was not in scope
  when level `L` was minted"): the same holds for a closure that a call
  inside the body returns, the innermost step of axiom S.
- `r_induction_rule.sl` (`--goal proved` PASS, both): `ind` takes a
  base case and a packed first-order step, P n to P (Succ n), and
  returns a packed ∀n. P n, by minting a level after unpacking the
  step, as `hyp_factory.sl` does.

So modus ponens works at the meta level (top-level application) and for
hypotheses of known lower level. It does not work inside a body for a
closure of unknown level, unless the conclusion is itself a packed
closure built by a factory. SOUNDNESS.md part 8 describes the same
refusal as what stops Curry's paradox.

### 2.4 How Gödel II could be met

Three routes. Each is my reading, with standard results named from
memory.

**A. Interpret arithmetic, then apply G2 to the induced theory.** Let
T_A = {φ : ⊢ ⟦φ⟧} for a translation ⟦·⟧ of arithmetic into goal types.
Suppose T_A is a consistent, r.e. theory that contains a base such as HA
(intuitionistic) or IΣ₁ (classical; I do not remember the weakest
intuitionistic base for which G2 is standard). Then G2 in Feferman's
form, for a Σ₁ presentation, gives T_A ⊬ Con_σ, hence ⊬ ⟦Con_σ⟧. Here σ
is the Σ₁ formula "some unit proving ⟦φ⟧ passes". The obstacle is
closure under logic. T_A must be closed under intuitionistic deduction,
including axioms whose hypotheses are implications. Two options fail:
- Fixed levels per formula. Each statement unit mints its own levels,
  so ⟦A⟧ differs between units unless one vocabulary mints them all.
  V has finitely many `def-lvl` forms, so formulas must share levels.
  A function at a level of V cannot call a unit's own lemmas, which are
  at later levels (§18: "a function at a later level cannot be called
  from code at an earlier level"). Also, validating every S-axiom
  instance (A→(B→C))→((A→B)→(A→C)) by direct closures seems to need
  level(A→C) above level(A→(B→C)) and level(B→C) for every B. If, so
  that a proof can apply its hypothesis, ⟦X→Y⟧ must sit above ⟦X⟧ when X
  is an implication, then the levels of B→C rise with B's nesting, and
  infinitely many distinct levels lie below level(A→C), against "a
  well-order of type ω" (SOUNDNESS.md part 3, line 115). Without that
  condition the formulas could share levels, and this argument does not
  apply. With shared levels, a same-level call needs a
  `subterm` decrease.
- Packed levels. Internal MP with a data consequent fails
  (`hyp_packed_bad.sl`), and so does the innermost step of axiom S
  (`r_result_closure_bad.sl`).
- A rule-based, PRA-style translation (my proposal, unchecked beyond
  one case). Translate only free-variable formulas with decidable
  matrices, as graph relations, with each theorem's universal closure
  packed. Implications are then between data. Induction becomes an
  internal function from packed premises to a packed conclusion, which
  compiles (`r_induction_rule.sl`). Composition of packed totality
  proofs is `hyp_factory.sl`'s `compose`. G2 holds for PRA and, as I
  recall, for its consistent r.e. extensions, with consistency a
  free-variable formula. Not checked: closure of T_A under all of PRA's
  rules, graphs for every primitive recursive function, and a
  primitive recursive check of acceptance traces for σ.

A cleverer translation for HA (level parameters, `Predates` carried in
data, factories) may exist. I did not find or rule one out. README.md,
in its paragraph that begins "The author asserts", says that "the
language as a whole computes exactly the multiply recursive functions,
so its strength is about IΣ₂ (anticlassicality aside), with
proof-theoretic ordinal ω^ω^ω". Read as a claim about computation,
which is how README.md derives it, it does not by itself supply ⟦·⟧
with the closure properties G2 needs. Read as Sleight interpreting
IΣ₂ with closure under deduction, it would supply route A's base; I
found nothing in README.md that argues that reading.

**B. Internal provability predicate on codes (Hilbert–Bernays–Löb).**
Define `Prov c` in Sleight as an inductive relation saying that a unit
with goal code c passes. That means formalizing §1 to §72 as a finitary
derivation system: run-position evaluation, macro expansion with its
10000 cap, and literal interning, with `read-file` and `slot-eq` as
inputs. G2
then needs:
- **D1 (meta):** if ⊢ T, then ⊢ `Prov ⌜T⌝`. A true `Prov` instance has
  a finite derivation, which can be written out or obtained by
  reflection (05's `halts_reflect.sl` pattern, which "relies on the
  evaluator", §29).
- **D2 (internal):** `Prov ⌜A→B⌝ → Prov ⌜A⌝ → Prov ⌜B⌝`, a lemma that
  units compose. §71's "at most once per unit" for `goal`/`qed`, global
  gensym and literal state (§65, §45), and shadowing (§19) make this a
  real lemma about the formalization, not a triviality.
- **D3 (internal):** `Prov ⌜A⌝ → Prov ⌜Prov ⌜A⌝⌝`, an instance of
  formalized Σ₁ completeness, for the Σ₁ relation `Prov`.
- **A diagonal sentence G** with ⊢ G → ¬`Prov ⌜G⌝` and the converse.
  §9 bars a substitution function in types, but its own words make an
  exception: "elaborating a type calls none: the only code that runs is
  a macro's expansion". So there are two constructions. Relationally,
  G := for every y with `Sub ⌜φ⌝ y`, ¬`Prov y`, which needs a proof that
  `Sub` is functional. Or, as 03's diagonal does, a macro reads the
  unit's text with `read-file` (§65) and expands to ¬`Prov` of that
  text; then G is ¬`Prov ⌜G⌝` after expansion, if codes are unit texts.
  `r_self_goal.sl` (`--goal proved` PASS, reference and slc, run after
  `std/macro.sl`, whose `fail-raw` and `str-raw` it calls) has a goal
  type that a macro expands to `(Prov "<the file's own text>")`; the
  unit's other file, `std/macro.sl`, is not in the code. That
  second form puts the burden on `Prov`'s formalization of macros and
  `read-file`, which route B needs anyway. A string literal is opaque to
  the checker (§45), so whether D2 and D3 can be proved about such codes
  is open.

Most internal implications here go from inductive derivations to
inductive derivations or to `False`, calling earlier, closed lemmas, as
`con.sl` does. Some do not: Con, ¬`Prov ⌜G⌝`, and G are themselves
closure types, so a step such as ⊢ Con → G takes a packed closure and
must build a new one by a factory, as `hyp_factory.sl` does, since a
body cannot apply a packed closure (`hyp_packed_bad.sl`). The final
step ("from ⊢ Con build ⊢ ⊥") applies closed proofs at the top level,
as `top_mp.sl` does. So the stratification of §2.3 does not obviously
block route B (my reasoning). Whether every internal step of the
derivation goes through is a condition of its own ((d) in §4), tried
so far only in an abstract form:
- [compiled] `g2_defs.sl` codes formulas as `Bot`, `Imp`, `Pv` (the
  object language's "provable"), and `Txt` (a string), and states, for
  an abstract relation `P` on codes (a `TyCtor` parameter) and a code
  `g`, D2, D3, and the D1 instance ⊢ `P (Imp g (Imp (Pv g) Bot))`,
  that is, `P` of the code of G → ¬`Pv` ⌜G⌝ with ⌜G⌝ = `g`, as
  hypotheses packed with their level (`Hbl`). With G read as ¬`P g`,
  so that ¬`P ⌜G⌝` → G holds by definition, its `con-to-g` proves,
  for every such `P` and `g`, a packed ¬`P g` from a packed
  ¬`P ⌜⊥⌝`: ⊢ Con → G, which `g2_step.sl` states as its goal
  (`--goal proved` PASS, reference and slc). The proof unpacks the
  hypotheses, mints a level, and defines the new closure there, as
  `hyp_factory.sl` does.
- [compiled] Applying the packed hypotheses in the body itself, to
  reach `False` from a proof of `P g`, is refused by both
  (`g2_direct_bad.sl`: "`K` was not in scope when level
  `(level-of g2-direct)` was minted"). With the hypotheses at levels
  minted before the function, the same body is accepted
  (`g2_fixed.sl`, PASS, both). So in the packed form the last step,
  from ⊢ Con to ⊢ ⊥ through D1 for G, is a top-level application, as in
  `top_mp.sl`, which is where G2's argument makes it.
  `review7/09_g2_final.sl`, run under `--no-prelude` after
  `review7/09_g2_pre.sl` and `g2_defs.sl`, takes that step at the top
  level and is accepted by both. It postulates ⊢ Con with a `def-prim`
  axiom, which SOUNDNESS.md part 1 excludes and which, as declared in
  `09_g2_pre.sl`, gives an element of every type, so the file shows how
  the step elaborates, not anything about Con; it proves the other
  hypotheses for a `P` that holds of every code, for which Con is
  false. The same step inside a function body is refused by both, as
  `g2_direct_bad.sl` is (`review8/09_g2_body_bad.sl`, run under
  `--no-prelude` after those three files: "`N2` was not in scope when
  level `(level-of fin)` was minted").
- Reading G as ¬`P g` needs `g` to be a code of the type ¬`P g`
  itself, so that D1 turns ⊢ G into ⊢ `P g` in the last step. In
  `g2_defs.sl`'s coding, ¬`Pv g` is `Imp (Pv g) Bot`, and no `g`
  equals a larger term that contains it: §7's occurs check refutes the
  equation (`review7/09_g2_cycle.sl`, accepted by both). So, on my
  reading, `g` has to be a code not built from the formula's
  structure, such as a `Txt` holding the source text that states G, as
  the macro-built diagonal of `r_self_goal.sl` splices in its own
  file's text. ¬`P g` then has two codes, and the D1 instance uses
  both: `g` as its antecedent, which `p : P g` must match, and
  `Imp (Pv g) Bot` as its consequent, which D2 splits. A coding that
  gives each formula one code and codes implications with `Imp` would
  need `g` = `Imp (Pv g) Bot` there, so, on my reading, a `Prov` that
  formalizes acceptance would have to meet D1 for a code that mixes a
  text code with structural ones, and D2 for such codes too; whether
  one can is not examined. For
  a relational diagonal, G ↔ ¬`Prov ⌜G⌝` is a theorem rather than a
  definition, and its two directions are further internal steps, not
  tried.
- This checks (d) for this derivation and this way of stating the
  hypotheses only. `P` formalizes nothing, and nothing here shows that
  D2, D3, or the D1 instance hold for a `Prov` that formalizes
  acceptance.

The usual G2 argument from D1 to D3 is intuitionistic, so
anticlassicality (README.md, `tests/anticlassical.sl`) is no exemption.
G2 fails for some very weak theories with suitably weak consistency
statements (Willard's self-verifying systems, from memory). So D3 is a
real premise, not a formality. The self-formalizations I recall do not
contradict G2 because they prove the consistency or normalization of a
weaker system inside the stronger one, as in Barras's Coq-in-Coq, from
memory.

**C. Normalization implies consistency (05 §4.3).** This is route B
plus a lemma. If ⊢ "every accepted program's stripped run is safe" for
the formalized semantics, then ⊢ ¬`Prov ⌜False⌝`. Given a proof `p` of
`(False)`, the program whose final `(Fn L -> (many (Nat) r))` has body
`(lift p)`, with `lift` a `many absurd` function from an erased
`(False)`, is accepted (§29: defining it "involves no evaluation").
Stripped, it reaches absurd code: `proto/review5/05_stripped_absurd_final.sl`,
under `--no-prelude` with `p` from a `def-prim` axiom, which SOUNDNESS.md
part 1 excludes, is accepted and stops with "absurd code reached" under
the reference and `slc --interpret`. It shows the program's shape, not
a `p` from a passing unit.
Internally that needs two lemmas about the formalization:
- `Prov ⌜False⌝` implies acceptance of that program;
- its formalized stripped run reaches absurd code.

Neither has been tried. With them and route B's D1 to D3, its
diagonal sentence, and its internal steps ((d) in §4), consistency
gives ⊬ uniform stripped-run safety. The same holds for (T) together
with full-semantics safety, since then `p` runs first. This is the form
in which type theories usually meet G2: "the system cannot prove its own
normalization". As I recall it, normalization implies consistency
already in weak arithmetic, so G2 forbids the internal normalization
proof.

**Kleene/Rosser-style diagonals without HBL.** As far as I know, these
give G1-type results: some sentence is undecided. They do not give
"consistency is unprovable". For Sleight, a Kleene-style G1 needs:
- r.e. (§2.2);
- a halting relation `Halts e` on codes e of a machine whose halting is
  undecidable, such as a Turing machine (Sleight's own functions return,
  by (T), so they cannot play that part);
- Σ₁-completeness for it (⊢ `Halts e` whenever e halts, by a written
  derivation);
- consistency, with ¬`Halts e` applicable to `Halts e` at the top
  level (§20), so that no e has both proved.

From these, some e diverges while ⊬ ¬`Halts e`. If every true
non-halting statement were provable, enumerating proofs would decide
halting. Σ₁-soundness (⊢ `Halts e` only if e halts) is not needed for
this; on my reading it would follow from SOUNDNESS.md's (T), (S), and
(E), which are argued there, not proved. Every proof of G2 I know needs
some internalized Σ₁ completeness, at least D3.

### 2.5 The cheap diagonal against Gödel II

| Claim | 03's diagonal (no Gödel) | What the Gödel route adds |
|---|---|---|
| No faithful, hypothesis-free, non-erased `compile : Src -> Verdict` (03 F6) | Gives it, under §3.4's premises | Nothing |
| Uniform H not provable in a form a function can recurse on (03 F6/F7, 05 §4.3) | Gives it, with soundness ((T), (S), (E)) and a faithful stepper | Needs only consistency, and also covers non-recursable forms (¬¬H, Π-forms), but only for H *with* safety (H alone does not give Con: a stripped run that reaches absurd code still "halts" in some sense) |
| Uniform stripped-run safety not provable (05 §4.3, T7) | Does not give it: a Π statement yields nothing to run | Gives it under route B's D1 to D3, diagonal, and internal steps ((d) in §4) and route C's two lemmas, or under a route A translation with the same lemmas; I know no other route |
| Uniform (T) + full-semantics safety not provable (05 T7) | Only in recursable form, with soundness | Every form, from consistency, under the same conditions |

## 3. Q2: SOUNDNESS.md and the detour

### 3.1 What SOUNDNESS.md says

- Part 1 (line 45): "The claim has four parts, about any program the
  checker accepts". (T): "In the *full semantics* of part 3 below, in
  which erased code runs too, every function activation returns, apart
  from a crash." (E): "The run the implementations perform, with erased
  positions stripped, follows a run of the full semantics".
- Part 3 describes "an eager semantics of the unerased program". It
  never mentions the driver.
- Part 5 begins: "Give each activation of a function, of `def-fns` or
  `def-unique`, erased ones included, the measure". It ends: "The top
  level is not a function and runs straight through (§20). Macro
  expansion is bounded (§62), and the driver's loop over a `Program`
  (§42) is outside the claim, each step being a total call."
- `grep driver` finds only line 195 (the answers to `world-do`) and line
  289. **No part mentions the driver's application of a final `Fn`
  value** (§27: "`(Fn L -> (many T y))`, for any type `T`, is applied
  and its result is printed"). The `Program` driver's steps are mentioned
  only to say that the loop is outside the claim and each step is a
  total call.
- "The checker" is not defined. Part 8 ("refused by both compilers. The
  messages are the checker's") suggests that it means the
  implementations' checking.

### 3.2 My reading

The driver's call of `run-q` is an activation of a `def-fns` function,
so it falls under part 5's first sentence. The measure argument
("Each activation therefore makes finitely many calls, each of which
finishes, by well-founded induction on μ") asks a decrease only of the
calls an activation makes, never of the root. The root here is called
with no proof, as a top-level call is (§20). The invariants (I1) to (I4)
of part 4 at that call are those in force at the end of elaboration. Part 5's
remark that each `Program` step is "a total call" can be read as
treating driver-made calls as covered, though the same sentence puts
the driver's loop "outside the claim". So I read (T) as covering the final-`Fn` call, and
(E) as covering its stripped run. Two things make this a reading, not a
quotation:
- part 3's full semantics does not say that it includes the driver;
- part 1's (T) speaks of activations "in the full semantics" of an
  accepted program.

For (E) to give *termination* of the stripped run, "follows" has to
mean an order-preserving correspondence with a finite full run. Part 7
("each state the stripped run reaches corresponds to a reachable state
of the full semantics") suggests that meaning without saying it.

### 3.3 Re-run (reference built at this checkout; `_build/release/slc`)

From `proto/review5/`:
- `main.exe ../../../../std/macro.sl 03_detour.sl` prints `(BFalse)`,
  exit 0. Every elaboration below also warns on standard error at line
  37, column 2, the `))` just after the string literal closes, that it
  is "dedented past indentation 2" (with a note pointing at line 18);
  that is a layout warning, not a refusal. The built programs print
  nothing on standard error.
- `--extract out.ml` writes the OCaml, exit 0. (`--extract` takes the
  next argument as its output path. Written as `--extract
  ../../../../std/macro.sl 03_detour.sl`, it took `std/macro.sl` as the
  output and failed with "unbound name `macro-fail`" before writing
  anything; `git status` shows the file unchanged.)
- `--build` builds a program that prints `(BFalse)`.
- `slc ... --interpret` prints `(BFalse)`.
- `slc ... --build` builds a program that prints `(BFalse)`.
- From `proto/fuel/`, `diagonal.sl` (969 bytes), run after
  `std/macro.sl` as `03_detour.sl` is, is accepted and prints its
  string; alone it is refused ("unbound name `macro-fail`").

A byte comparison (Python) shows two things:
- `03_detour.sl` up to `(def-fns _ $ (many run-q` equals `diagonal.sl`
  up to `(diag)`;
- the unescaped literal passed to `toy-compile` equals `diagonal.sl`.

So P is Q's prefix plus a final value that applies the function to Q's
text, as 03 says. `(BFalse)` is `toy-compile`'s "reject" on 969 bytes,
consistent with Q being accepted. Whether the *spec* accepts P cannot be
run. Both implementations accept it, and I found nothing in DESIGN.md
that refuses it:
- the macro is defined but not called;
- the run-position `let` applies a constructor;
- `run-q`'s body makes one bare lower-level call, given `(predates _)`
  by §48.

### 3.4 Does the argument go through?

Yes, on my reading, under these premises:

1. SOUNDNESS.md's (T) and (E) hold, which is argued there, not proved.
   They cover the driver's call of P's final value (§3.2), and (E)
   implies termination of the stripped run.
2. P is accepted in the sense part 1 means, and the spec elaborates
   Q's prefix as it elaborates P's. P and Q differ only after the
   prefix, and §27 runs forms before later code is checked. This also
   needs the prefix to make no compile-time `read-file` of its own file
   (true of `diagonal.sl`), and the `slot-eq` caveat of 03.
3. The spec's run of `compile` on equal arguments is deterministic. The
   closure and argument in Q's macro run equal those in P's driver run.
   The `read-file` result equals the literal as a `String` value (§45: a
   literal "means what it would mean with those values written out").
   It must also not matter that one run is the compile-time evaluator's
   and the other the driver's. §31 gives one semantics, "a machine with
   unlimited stack and heap"; that is my reading. It also sets crashes
   aside: §31 and §42 allow one run to crash where the other does not.
4. The rest of the macro run ends. In `diagonal.sl` this is by
   inspection: `diag-fn` (`diagonal.sl:8-15`), and `macro-fail`,
   `fail-raw`, and `str-raw` (`std/macro.sl:5-36`), are non-recursive and, apart from `compile`
   and each other, call only `read-file` and `intern-string`. Those
   must return; for `read-file` that is a host assumption (03 F7). This
   code cannot be given a P, as 03 F6 says, because `diag-fn` needs a
   `MacroWorld` that only the expander supplies (§65).
   Inspection replaces it here. For a real `compile`, the macro must
   also read every file of its unit and build `Src` from them, still by
   non-recursive code plus calls already covered.
5. `read-file` returns Q's text in Q's run. That is, "faithful" is
   relative to a fixed file system (§2.1).
6. After the macro returns, the rest of Q is accepted when the macro
   expands to nothing, and Q is rejected when it expands to
   `compile-error`. In `diagonal.sl` the rest is one string literal,
   and the expansion count stays far below §62's 10000.

Under 1 to 6, Q's spec run ends, and its verdict is the negation of
`compile`'s answer on Q, as 03 F6 says. Premise 1 is the weakest. If
"the checker" in part 1 means the implementations, P's acceptance is
established (§3.3), but premise 2 then adds that the spec agrees with
them on P.

## 4. Wording for 03 and 05

03 F6 and 05 (§1, §4.3, T7, and §9; 05's Coordinator note 1) carry this
wording, revised there by later reviews; where they differ, they are
the current text. 05 §4.3 adds a condition (d), included below.

**03 F6, after "(T) and (E) for P then say that this call of `compile`
returns, reading part 5 as counting the driver's call as one of the
activations it covers."** Add: "SOUNDNESS.md does not mention the
driver's call of a final `Fn` value. Part 5's measure argument asks no
decrease of a root activation, and its last sentence calls each
`Program` step 'a total call', though the same sentence puts the
driver's loop 'outside the claim'. So this is a reading, not a
quotation. The macro's other code cannot be given a P, since it needs a
`MacroWorld` (§65). In `diagonal.sl` it is non-recursive apart from that
call, and its termination is by inspection, given that `read-file` and
`intern-string` return (09 §3.4)."

**03 F6, "I make no claim about Gödel's theorems here."** Keep, and
add: "The diagonal above needs no Gödel. 09 §2.5 says what a Gödel route
would add."

**05 §1 Summary and §4.3, the Gödel paragraph.** Replace "In the form
for effectively axiomatized theories that satisfy the
Hilbert–Bernays–Löb derivability conditions ... I have not checked that
Sleight meets the conditions." with:

> On my reading, Gödel's second theorem would apply in this
> conditional form. Let `Prov` be a Sleight inductive relation on codes
> of units, formalizing acceptance under `--goal proved` (§71). Suppose
> (a) no unit proves `(goal erased (False))`; (b) whenever a unit proves
> T, one proves `(Prov ⌜T⌝)`; (c) Sleight proves D2 and D3 for
> `Prov`, and a diagonal sentence G with G ↔ ¬`(Prov ⌜G⌝)`, built from a
> relational substitution or by a macro that reads the unit's text (09
> §2.4); and (d) the internal steps of the usual derivation from these
> conditions, which compose implications between `Prov` statements, go
> through despite level stratification (09 §2.3, §2.4 B). Then, by that
> derivation (cited from memory), no unit proves ¬`(Prov ⌜False⌝)`. If moreover Sleight proves
> that `(Prov ⌜False⌝)` yields an accepted program whose stripped run
> reaches absurd code, it cannot prove uniform stripped-run safety. The
> same goes for uniform (T) with full-semantics safety, given the
> matching lemma. (d) has been tried only for an abstract relation `P`
> in place of `Prov`, with D2, D3, and the diagonal's D1 instance as
> hypotheses and G taken to be ¬`(P ⌜G⌝)` itself (09 §2.4 B); (b),
> (c), and those lemmas have not been attempted (09 §2.4). As far as I recall, that derivation is intuitionistic, so
> anticlassicality does not obviously exempt Sleight. README.md's IΣ₂
> remark is derived there from the functions Sleight computes; read
> that way, it does not supply an interpretation of arithmetic closed
> under deduction, and it says nothing about (b) or (c).

Also replace "The claimed IΣ₂ strength (F9) appears to be more than
such results usually need" with: "The claimed IΣ₂ strength (F9) would
supply a base for G2 only if it means that Sleight interprets IΣ₂ with
closure under deduction; README.md derives it from the functions
Sleight computes, which does not give that (09 §2.4)."

**05 T7.** Replace "if it is consistent and meets Gödel II's conditions
(unchecked)" with "if it is consistent, conditions (b) to (d) of
§4.3 hold for a formalized `Prov`, and the matching lemmas of §4.3 hold
(all unattempted)".

**05 §9.** Replace "That Sleight meets the conditions of Gödel's second
theorem (r.e. checker, enough arithmetic, derivability conditions)"
with: "r.e. appears to hold under the readings of 09 §2.2. Σ₁
statements and consistency of a coded system are expressible as goals
(09 §2.3, compiled). D1 to D3 for a formalized `Prov`, the diagonal
sentence, the derivation's internal steps under level stratification,
and any interpretation of HA, IΣ₁, or PRA are unattempted, except
that the internal steps were tried for an abstract relation `P` in
place of `Prov`, with D2, D3, and a D1 instance as hypotheses, and G
taken to be ¬`P ⌜G⌝` itself (09 §2.4 B).
The obvious translation of nested implications meets level
stratification (09 §2.3, compiled); a PRA-style translation with
first-order implications does not obviously meet it (09 §2.4)."

00-summary's Gödel item (key finding 20, in its §2) points to 09 for
the conditions.

## 5. Unverified

- That the spec's acceptance traces are decidable to check, and that
  its elaboration is finitely branching (§2.2). DESIGN.md is prose.
- The relational Q axioms: I cited the prelude lemmas but did not write
  the axioms out. I did not try HA, IΣ₁, or Σ₁ induction beyond the
  fixed-level shape of `hyp_fixed.sl`.
- The S-axiom remark in route A is reasoning; only its innermost step
  is compiled (`r_result_closure_bad.sl`). A cleverer translation is not
  ruled out.
- The PRA-style route: only the induction function is compiled
  (`r_induction_rule.sl`). G2 for consistent r.e. extensions of PRA is
  from memory.
- The macro-built diagonal: `r_self_goal.sl` shows only that a goal type
  can contain its own file's text, not the whole unit's, and not that
  D2 or D3 can be proved about such codes.
- Route B: no `Prov`, D2, D3, `Sub`, or G was built. The derivation's
  internal steps ((d) in §4) were tried only with D2, D3, and one D1
  instance as hypotheses about an abstract `P`, and with G read as
  ¬`P g`, which needs `g` to be a code of that type, such as the text
  of the file that states G, and D1 and D2 to hold for codes that mix
  such a code with structural ones (`g2_step.sl`, §2.4 B); its final
  step was accepted only with consistency postulated by a `def-prim`
  that gives an element of every type (`review7/09_g2_final.sl`). For a
  relational diagonal, the two directions of G ↔ ¬`Prov ⌜G⌝` were not
  tried.
  Whether D2 holds given §71's one goal per unit and the global gensym
  and literal state is open.
- Route C's two lemmas, and the claim that normalization implies
  consistency in weak arithmetic (from memory).
- The named results are from memory, unchecked: G2 for HA, Feferman's
  Σ₁-presentation condition, Willard's self-verifying systems, Barras's
  Coq-in-Coq, and the Kleene G1 argument.
- §3.2's reading of parts 1, 3, 5, and 7 for the driver's call. Whether
  (E)'s "follows" implies termination of the stripped run.
- §3.4 premise 2 (the spec accepts P as the implementations do) and
  premise 3 (the evaluator's run and the driver's run are one semantics).

## Review notes

An adversarial reviewer read the brief, CLAUDE.md, DESIGN.md in full,
SOUNDNESS.md in full, README.md's "Logic and strength", 03 F6 and F7
with their review notes, and 05 §4.3, T7, and §9 with theirs. It re-ran
`hyp_packed_bad.sl` (refused, the quoted message), `hyp_fixed.sl` and
`hyp_factory.sl` (accepted), and `--goal proved` on `sys.sl` with
`sigma1.sl`, `con.sl`, and `top_mp.sl` (PASS), all under the reference
and `_build/release/slc`; and `03_detour.sl` under the reference,
`--extract` (to a scratch path), `--build`, `slc --interpret`, and `slc
--build` (each prints `(BFalse)`, exit 0), and `diagonal.sl` under the
reference and `slc --interpret`. A byte comparison confirmed the prefix
match (909 bytes) and that the unescaped literal equals `diagonal.sl`
(969 bytes). `std/macro.sl` was unchanged afterwards.

Errors found and changed:

1. §2.2, the r.e. condition. "Finitely branching computable process"
   was both more and less than needed: "some run passes" needs only a
   decidable check of finite accepting traces, and finite branching is
   what makes "every run passes" Σ₁, through König's lemma, which was
   not covered. Rewritten.
2. §2.4 B and §4, "Since §9 bars a substitution function in types, G is
   built relationally". §9 itself lets a macro run while a type is
   elaborated, and a macro can read the unit's text (§65), as 03's
   diagonal does. `r_self_goal.sl` (new) has a goal type that expands
   to `Prov` of the file's own text; `--goal proved` passes under both
   implementations. Both constructions are now given, with the open
   point that string literals are opaque to the checker (§45).
3. Summary and §2.4 A, "The naive arithmetic route is blocked". The
   compiled refusals block nested implications whose proof must call a
   closure of unknown level. A rule-based, PRA-style translation with
   first-order implications avoids them in the one case tried:
   `r_induction_rule.sl` (new) turns a packed first-order step and a
   base case into a packed ∀n inside a function body, accepted by both.
   The heading and text now say the obvious translation meets
   stratification and the PRA-style one does not obviously; added as a
   third option under route A.
4. §2.3, only a hypothesis packed in an argument was compiled; the S
   axiom's innermost step uses a closure returned by a call in the same
   body. `r_result_closure_bad.sl` (new) is refused by both with "`K`
   was not in scope when level `L` was minted". Added.
5. §2.4 A, fixed levels. Added that V has finitely many `def-lvl` forms,
   so formulas must share levels, and that a function at a level of V
   cannot call a unit's later lemmas (§18, quoted).
6. §2.4 A and §4, README.md's IΣ₂ remark was described as concerning
   "the provably total functions", a phrase README.md does not use. It
   derives the strength from "computes exactly the multiply recursive
   functions" and also names an ordinal. Now quoted, attributed to the
   paragraph that begins "The author asserts", and the two readings
   separated. The suggested deletion of 05's IΣ₂ sentence became a
   replacement that keeps the conditional.
7. §2.4, Kleene G1. Σ₁-soundness was listed as a premise and said to
   "follow" from SOUNDNESS.md's claims, unhedged. The argument needs
   consistency (with top-level application of ¬`Halts e`), not
   Σ₁-soundness. Reworded and hedged.
8. §3.4 lacked a premise that the rest of Q is accepted when the macro
   expands to nothing and rejected when it expands to `compile-error`.
   Added as premise 6. Premise 3 now says that it sets crashes aside,
   which §31 and §42 allow in one run and not the other. Premise 4 now
   says that `diag-fn` also calls `compile` and the macro helpers.
9. §3.2, "treats driver-made calls as covered" was stated as what part
   5 does; the same sentence puts the driver's loop "outside the
   claim". Now a reading. §4's suggested 03 wording said "this reading
   seems sound"; changed to the same.
10. §4, suggested 05 wording. The T7 replacement dropped the lemma that
    `(Prov ⌜False⌝)` yields an accepted program reaching absurd code,
    without which (b) and (c) give only ⊬ consistency, an overclaim.
    Added. The §4.3 replacement now hedges the derivation from D1 to D3
    and its intuitionistic character as recalled, and the §9
    replacement says "appears to hold" for r.e.
11. §2.5, row 3 said the Gödel route is "the only route"; a route A
    translation with the same lemmas would also give it. Reworded.
12. §3.3 omitted the layout warning (line 37) that every run prints on
    standard error. Added.
13. §2.4 B, a four-item list whose last item read as two. Rephrased.

Confirmed: the DESIGN.md quotes (§9, §18, §20, §27, §29, §31, §45, §65,
§71); the SOUNDNESS.md quotes of parts 1, 3, 5, 7, and 8, verbatim,
including part 5's last sentence; `grep driver` hits lines 195 and 289
only; line 115's "a well-order of type ω"; the prelude line numbers for
`Nat`, `Eq`, `Add`, `Mul`, `add`, `mul`, `add-fn`, and `mul-fn`;
`std/macro.sl:5-36`; `call_in_type_bad.sl` is refused citing §9. The
route B outline (D1 to D3, the diagonal, then top-level application)
uses no internal application of a closure of unknown level: Con → G
can be built by a factory, as `hyp_factory.sl` does, since G is itself
a closure type (my reasoning).

Unsure:
- Whether G2 holds for consistent r.e. extensions of PRA stated as
  free-variable theories, and whether some version for theories that
  only interpret Q would weaken route A's base further (from memory,
  not checked).
- `tests/anticlassical.sl` refutes excluded middle as one function over
  every erased `Type P`. Whether a classical base such as IΣ₁ could
  still be interpreted instance by instance was not examined.
- Whether a macro-built G is compatible with D3, given that a string
  literal has no `is` rule (§45).

## Round 6 review notes

A sixth reviewer read the brief, CLAUDE.md, all of DESIGN.md, all of
SOUNDNESS.md, README.md's "The author asserts" paragraph, 03 F6, 05
§1, §2.2, §4.3, and T7 as they now stand, and 00-summary item 20. It
re-ran `hyp_fixed.sl`, `hyp_packed_bad.sl`, `hyp_factory.sl`, and
`r_result_closure_bad.sl` (as stated, both implementations); `--goal
proved` on `sys.sl` with `sigma1.sl`, `con.sl`, and `top_mp.sl`, and on
`r_induction_rule.sl` and `std/macro.sl r_self_goal.sl` (PASS, both);
`call_in_type_bad.sl` (refused, citing §9); `03_detour.sl` under the
reference, `--extract` to a scratch path, `--build`, `slc --interpret`,
and `slc --build` (each `(BFalse)`, exit 0); the `--extract` misuse on a
scratch copy of `std/macro.sl` ("unbound name `macro-fail`", copy
unchanged); `diagonal.sl` (969 bytes, both); the byte comparisons (909
bytes, literal equal); and `05_stripped_absurd_final.sl` under
`--no-prelude` ("absurd code reached", both).

1. Summary and §2.4 B said `r_self_goal.sl` splices "the unit's own
   text". It splices its own file's text; the unit also holds
   `std/macro.sl`, which it needs (it fails alone, "unbound name
   `str-raw`"). Both fixed.
2. Summary credited 03's diagonal with "a G1-style corollary". §2.4's
   Kleene argument uses r.e., Σ₁-completeness for a halting relation,
   and consistency, none of which 03's diagonal supplies; the other two
   items also rest on premises. Reworded.
3. §2.4's Kleene G1 lacked a condition: `Halts` must be about a machine
   whose halting is undecidable; Sleight's own functions return by (T).
   Added.
4. §2.2 said the reference "terminates on accepted inputs within its
   fuel". The reference has no fuel bound unless `--eval-fuel` sets one
   (MANUAL.md), and only the inputs run are evidence. Reworded.
5. §2.4 A inferred "infinitely many levels below one" from the S axiom.
   That needs the levels of B→C to be distinct, which holds only if an
   implication with an implication antecedent must sit above it. The
   condition is now stated.
6. §2.4 B said HBL-style route B "is how self-formalizations meet G2",
   then described proving a weaker system's consistency, a different
   thing. Reworded.
7. Route C cited `05_stripped_absurd_final.sl` without saying that it
   runs under `--no-prelude` with `p` from a `def-prim`, which
   SOUNDNESS.md part 1 excludes. Added, with what `lift` is.
8. §2.1 cited DESIGN.md §59 for "the prelude's `False`"; §59 is a worked
   example. Now `lib/prelude.sl:15`.
9. §3.2 named the invariants "(I1) to (I3)"; part 4 lists (I1) to (I4).
   Fixed.
10. §3.3 placed the layout warning "inside the string literal" and said
    every run warns. It is at 37:2, the `))` after the literal closes,
    and the built programs print nothing on standard error. Fixed.
11. §3.4 premise 4 put `diag-fn` in `std/macro.sl:5-36` (it is
    `diagonal.sl:8-15`) and quoted 03's "the same way", which 03 no
    longer says. Fixed.
12. §4 was headed "(not applied)" and said 00-summary's bullet "should
    then point to 09"; 03 F6, 05 (§1, §4.3, T7, §9), and 00-summary
    item 20 already carry it. Now stated in the present tense, with 03
    and 05 as the current text.
13. §4's conditional, and with it the summary, §2.4 B, §2.4 C, §2.5,
    and §5, omitted a condition, raised by the round-6 reviewer of 03
    and 05 and checked here: the usual G2 derivation builds implications
    inside Sleight, such as ⊢ Con → G, whose antecedent is itself a
    packed closure. §2.4 B said "every internal implication" goes
    between inductive derivations, which is false for those. Added as
    condition (d), matching 05 §4.3, and §2.4 B now says which steps
    need a factory.
14. D3 was called "formalized Σ₁ completeness of `Prov`", and the
    Kleene paragraph said "D3 or an instance of it"; D3 is an instance
    of formalized Σ₁ completeness. Reworded both.

Unsure:
- Whether a factory-built Con → G (item 13) really goes through: no G
  exists to try it on.
- 00-summary item 20 still says the diagonal sentence can splice "the
  unit's own text" and credits 03's diagonal with the G1-style
  statement (items 1 and 2); that file is not this reviewer's.

## Round 7 coordinator notes

1. Condition (d), the derivation's internal steps under level
   stratification, was untried. `proto/godel/g2_defs.sl`,
   `g2_step.sl`, `g2_direct_bad.sl`, and `g2_fixed.sl` try it for an
   abstract relation with D2, D3, and the diagonal's D1 instance as
   hypotheses: the packed ⊢ Con → G passes `--goal proved` on both
   implementations, the direct application of packed hypotheses is
   refused, and the fixed-level form passes. Added to §1, §2.4 B, §4's
   wording for 05, and §5.
2. After this round's review: §2.4 B said `09_g2_final.sl` postulates
   ⊢ Con. Its `def-prim`, as declared in `09_g2_pre.sl`, gives an
   element of every type, so the file shows only how the last step
   elaborates; said so.
3. After this round's review: §5 called the code G needs "a unit's
   text", where §2.4 B says the source text that states G, as a
   macro-built diagonal splices in its own file's text. §5 follows
   §2.4 B now.

## Round 7 review notes

A seventh reviewer read REVIEW.md, the brief, CLAUDE.md, all of
DESIGN.md, all of SOUNDNESS.md, README.md's "Logic and strength", 05's
Gödel paragraphs as they now stand, and 00-summary key finding 20. It
re-ran, on the reference and `_build/release/slc`: `--goal proved` on
`g2_defs.sl` with `g2_step.sl` and with `g2_fixed.sl` (PASS), and
`g2_direct_bad.sl` (refused with the quoted message; slc reports four
such errors, three naming `K` and one `KC`); `hyp_fixed.sl`,
`hyp_packed_bad.sl`, `hyp_factory.sl`, and `r_result_closure_bad.sl`
(as stated); `--goal proved` on `sys.sl` with `sigma1.sl`, `con.sl`,
and `top_mp.sl`, on `r_induction_rule.sl`, and on `std/macro.sl
r_self_goal.sl` (PASS); `call_in_type_bad.sl` (refused, citing §9);
`05_stripped_absurd_final.sl` under `--no-prelude` ("absurd code
reached", reference and `slc --interpret`); and `03_detour.sl` under
the reference and `slc --interpret` (`(BFalse)`), with the 909-byte
prefix comparison.

`con-to-g` was checked step by step against the usual derivation: from
the D1 instance and `p : P g`, `d2` gives `P (Imp (Pv g) Bot)`; `d3`
gives `P (Pv g)`; `d2` again gives `P Bot`; Con refutes it. That is
⊢ Prov⌜G⌝ → Prov⌜⊥⌝ and its contrapositive, so the function proves
⊢ Con → ¬`P g` from the packed D2, D3, and D1 instance; G enters only
through reading ¬`P g` as G, and through the code `g` in the D1
instance.

1. §1 said the internal steps "do go through ... with the final step
   to ⊥ at the top level". That step had not been compiled with these
   definitions, and the sentence dropped the reading of G that the
   result rests on (item 2). `review7/09_g2_final.sl`, run under
   `--no-prelude` after `review7/09_g2_pre.sl` and `g2_defs.sl`,
   applies `con-to-g` at the top level to a postulated Con and to
   proofs of D2, D3, and the D1 instance for a relation that holds of
   every code, unpacks the result, and reaches a `(False)`; both
   implementations accept it. The same last step in a function body is
   refused by both (`N2` was not in scope when its level was minted),
   and a wrong proof of `P g` is refused. `--goal proved` refuses
   `--no-prelude`, so the file is checked as a plain run. §1, §2.4 B,
   and §5 now say this.
2. §2.4 B read G as ¬`P g` "by definition" without saying what that
   takes: `g` must be a code of the type ¬`P g` itself. In
   `g2_defs.sl`'s coding that type's code is `Imp (Pv g) Bot`, which
   contains `g`, and §7's occurs check refutes any such equation
   (`review7/09_g2_cycle.sl`, an `absurd` function from
   `(Eq (Fm) g (Imp (Pv g) (Bot)))`, accepted by both; the same with
   `(Bot)` in place of the inner `g` is refused as not refuted). So `g`
   has to be a code such as a unit's text, as a macro-built diagonal
   gives; for a relational one, the two directions of G ↔ ¬`Prov ⌜G⌝`
   are further, untried steps. Added as a bullet; §1, §5, and §4's
   wording for 05 (§4.3 and §9) now carry the condition.
3. §2.4 B's description of `g2_defs.sl` left out the `Txt` constructor,
   and wrote the D1 instance as `P ⌜g → ¬Pv g⌝`, corner quotes around a
   term that already holds the code `g`. Now `Txt` is listed and the
   instance is `P (Imp g (Imp (Pv g) Bot))`, with what it codes.
4. In §2.4 B the inserted bullet list swallowed the paragraph after it
   (the intuitionistic G2 argument, Willard, and Barras), whose
   unindented lines continued the last bullet. Split off.
5. §4's last line placed 00-summary's Gödel item at "§3 item 20". It is
   key finding 20, in 00-summary's §2; §3 there is "Decisions for the
   owner". Fixed.
6. §2.1 named `--no-prelude`'s `def-prim` axioms as a way flags change
   the theory, without saying that both implementations refuse
   `--no-prelude` with `--goal proved` (MANUAL.md; checked: "--goal
   proved does not take --no-prelude", FAIL). Added.
7. The coordinator's note said that 05 still carries the earlier
   wording on (d) and that 00-summary and 00-glance call (d) untried.
   8ea3540 had already changed both summaries, and 05's own round-7
   review has since put the abstract (d) in its §1, §4.3, T7, and §9,
   with the reading of G in §4.3. Both clauses removed, and §1 now says
   that 05 revised §4's wording. An intermediate state of this review, which
   said that 05 did not yet carry it, was committed in passing.
8. §5 still said that `r_self_goal.sl` shows a goal type containing
   "the unit's own text"; round 6 corrected the phrase in §1 and §2.4 B
   only. The file splices its own file's text, and the unit also holds
   `std/macro.sl`. Fixed.

Unsure:

- Whether a text code can stand for ⌜G⌝ inside the structural code
  `Imp g (Imp (Pv g) Bot)` of D1's instance, and still meet D2 for a
  `Prov` that formalizes acceptance, was not examined.
- 00-glance's Gödel item still states the abstract (d) without the
  reading of G, and 00-summary key finding 20 says (d) "holds in one
  abstract form" and that the last step "is a top-level application",
  which is now compiled only with Con postulated; neither file is this
  reviewer's.

## Round 8 review notes

An eighth reviewer read REVIEW.md, the brief, CLAUDE.md, all of
DESIGN.md, all of SOUNDNESS.md, README.md's "Logic and strength", 05
§2.2 and §4.3's Gödel paragraph as they now stand, and 00-summary key
finding 20. It re-ran, on the reference and `_build/release/slc`:
`--goal proved` on `g2_defs.sl` with `g2_step.sl` and with
`g2_fixed.sl` (PASS); `g2_direct_bad.sl` (refused, the quoted message
first); `review7/09_g2_cycle.sl` (accepted) and round 7's control with
`(Bot)` for the inner `g` (refused, "not refuted"); `09_g2_final.sl`
under `--no-prelude` after `09_g2_pre.sl` and `g2_defs.sl` (accepted),
with round 7's variants that apply its closure to a proof of
`(Triv (Bot))` and pass a Con for `(Pv (Bot))` (refused, type
mismatch); `hyp_fixed.sl`, `hyp_packed_bad.sl`, `hyp_factory.sl`, and
`r_result_closure_bad.sl` (as stated); `--goal proved` on `sys.sl` with
`sigma1.sl`, `con.sl`, and `top_mp.sl`, on `r_induction_rule.sl`, and
on `std/macro.sl r_self_goal.sl` (PASS; `r_self_goal.sl` alone,
"unbound name `str-raw`"); `call_in_type_bad.sl` (refused, citing §9);
`05_stripped_absurd_final.sl` under `--no-prelude` ("absurd code
reached", reference and `slc --interpret`) and `--goal proved` with
`--no-prelude` (FAIL, both); `03_detour.sl` under the reference,
`--extract` to a scratch path, `--build`, `slc --interpret`, and `slc
--build` (each `(BFalse)`, exit 0, the layout warning at 37:2, the
built programs silent on standard error); and the byte comparisons
(909-byte prefix, 969-byte literal). `con-to-g` was checked again step
by step: with `p : P g`, `d2` on the D1 instance and `p` gives
`P (Imp (Pv g) Bot)`, `d3` gives `P (Pv g)`, `d2` on those gives
`P Bot`, and Con refutes it.

1. §1 said the final step to ⊥ compiles "with consistency
   postulated", without round 7's caveat, which coordinator note 2
   added to §2.4 B only: the `def-prim` gives an element of every type,
   and the relation holds of every code, so Con is false for it. §1
   and §5 now carry it (also raised by 03 and 05's round-8 reviewer).
2. §1's "conditionally on that step" now followed the sentence about
   the final step, which it does not mean; it means the missing
   internal `Prov` step. Fixed.
3. §1 ended its third item with "The `Prov` route also needs only
   first-order implications", against §2.4 B since round 6: ⊢ Con → G
   has a closure as its antecedent, and `con-to-g` takes and builds
   closures. Reworded.
4. §1's Kleene sentence dropped the condition, added to §2.4 in round
   6, that the halting relation be for a machine whose halting is
   undecidable. Added.
5. §1, §2.4 B, and §4's wording for 05 §4.3 and §9 wrote ¬`Prov ⌜G⌝`
   for the abstract relation `P` (raised by 03 and 05's round-8
   reviewer). Now ¬`P ⌜G⌝`, with `P` named in place of `Prov`.
6. §2.4 B said that `g2_step.sl` proves ⊢ Con → G. The proof is
   `con-to-g` in `g2_defs.sl`; `g2_step.sl` states it as its goal. §1
   cited `g2_step.sl` alone the same way. Both fixed. §1's "meets D1 to
   D3 inside Sleight" also now says that D2 and D3 are the ones proved
   inside Sleight, since D1 is meta-level (§2.4 B; §4's (b)).
7. (gap) §2.4 B said that reading G as ¬`P g` needs `g` to code ¬`P g`
   and stopped there. On this reviewer's reading it also takes D1's
   instance `P (Imp g (Imp (Pv g) Bot))` to code one formula two ways:
   its antecedent and consequent both stand for ¬`P g`, the first as
   `g`, which `p : P g` must match, the second as `Imp (Pv g) Bot`,
   which `d2` splits. A coding with one code per formula and `Imp` for
   implication would need `g` = `Imp (Pv g) Bot`, which
   `09_g2_cycle.sl` shows is refuted. So D1, and D2, would have to hold
   for codes that mix a text code with structural ones; unexamined.
   Added to §2.4 B and §5, hedged; 05 §4.3 now says the same. Also, "no
   `g` equals a term that contains `g`" is now "a larger term", since
   §7 makes `x` = `x` a no-op.
8. (untested) §2.4 B's "The same step inside a function body is
   refused by both" rested on a scratch file of round 7's. New
   `proto/review8/09_g2_body_bad.sl`, run under `--no-prelude` after
   `09_g2_pre.sl`, `g2_defs.sl`, and `09_g2_final.sl`, is refused by
   both with "`N2` was not in scope when level `(level-of fin)` was
   minted". Cited.
9. §3.3 said that `diagonal.sl` "is accepted"; alone it is refused
   ("unbound name `macro-fail`"), and it needs `std/macro.sl` first,
   as `03_detour.sl` does. Fixed.

Checked and unchanged: the DESIGN.md quotes of §9, §18, §20, §27,
§29, §31, §45, §62, §65, and §71; the SOUNDNESS.md quotes of parts 1,
3, 5, 6, and 7 and its lines 45, 115, 195, and 289; the README.md
quote; the prelude lines of §2.1 and §2.3; `diagonal.sl:8-15` and
`std/macro.sl:5-36`; MANUAL.md's refusal of `--no-prelude` with `--goal
proved`, its `--eval-fuel` defaults, and 05 §2.2's list; 03 F6's two
quoted sentences.

Unsure:

- Whether a `Prov` defined through a decoding of codes, so that
  `Prov c` depends only on the formula `c` decodes to, would meet D1
  for mixed codes was not examined; decoding a `Txt` would mean
  elaborating its text, macros and `read-file` included, inside the
  formalization.
- 00-summary key finding 20 says a text code "might be" a code of
  ¬`P g`, which item 7 leaves standing but narrows; its §6 already
  names D2 for mixed codes, not D1. Not this reviewer's file.
