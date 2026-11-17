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
  derivability conditions D1 to D3 inside Sleight. Nobody has built it.
  So 03 and 05 may claim Gödel-based limits only conditionally on that
  step (§4 below gives wording).
- **What the cheap diagonal already gives.** 03's `read-file` diagonal
  gives three things without Gödel: no faithful, hypothesis-free,
  non-erased `compile`; no uniform H in a form a function can recurse
  on; and, as a G1-style corollary, an unprovable true non-halting
  statement. Gödel II adds limits on Π-type statements: uniform safety,
  and (T) together with safety. It also needs only consistency, not
  soundness. Its price is the internal `Prov` step above.
- **The naive arithmetic route is blocked.** One route is to show that
  Sleight interprets HA or IΣ₁. Implication is level-stratified, which
  blocks that route in its obvious form: a body cannot apply a hypothesis
  whose level arrives packed in data (compiled). The `Prov` route needs
  only first-order implications, which work.
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
(DESIGN.md §59; any type whose opened `Matchable` lists no constructors
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
  which SOUNDNESS.md part 1 excludes; `--fn-same`). I fix the default
  flags.

### 2.2 Is the theory recursively enumerable?

Under "some permitted run passes", ⊢ T is Σ₁: there exist files F and a
finite elaboration trace that accepts. That needs only that the spec's
elaboration is a finitely branching computable process. It does not
need checking to terminate. DESIGN.md is prose, so "computable" is my
reading of it. The reference implementation is evidence (rule 2): it
implements the elaboration and terminates on accepted inputs within its
fuel. A run that finishes within fuel is a finished run, if its
evaluator is faithful (SOUNDNESS.md part 11 lists the evaluator as
trusted).

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

So modus ponens works at the meta level (top-level application) and for
hypotheses of known lower level. It does not work inside a body for a
hypothesis of unknown level. SOUNDNESS.md part 8 describes the same
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
  Also, validating every S-axiom instance
  (A→(B→C))→((A→B)→(A→C)) by direct closures seems to need level(A→C)
  above level(A→(B→C)) for every B. That means infinitely many levels
  below one, against "a well-order of type ω" (SOUNDNESS.md part 3,
  line 115), unless levels are shared, and then a same-level call needs
  a `subterm` decrease.
- Packed levels. Internal MP fails (`hyp_packed_bad.sl`).

A cleverer translation (level parameters, `Predates` carried in data,
factories) may exist. I did not find or rule one out. README.md's "its
strength is about IΣ₂" concerns the provably total functions ("computes
exactly the multiply recursive functions"). Even if it holds, it does
not by itself supply ⟦·⟧ with the closure properties G2 needs.

**B. Internal provability predicate on codes (Hilbert–Bernays–Löb).**
Define `Prov c` in Sleight as an inductive relation saying that a unit
with goal code c passes. That means formalizing §1 to §72 as a finitary
derivation system: run-position evaluation, macro expansion with its
10000 cap, literal interning, `read-file` and `slot-eq` as inputs. G2
then needs:
- **D1 (meta):** if ⊢ T, then ⊢ `Prov ⌜T⌝`. A true `Prov` instance has
  a finite derivation, which can be written out or obtained by
  reflection (05's `halts_reflect.sl` pattern, which "relies on the
  evaluator", §29).
- **D2 (internal):** `Prov ⌜A→B⌝ → Prov ⌜A⌝ → Prov ⌜B⌝`, a lemma that
  units compose. §71's "at most once per unit" for `goal`/`qed`, global
  gensym and literal state (§65, §45), and shadowing (§19) make this a
  real lemma about the formalization, not a triviality.
- **D3 (internal):** `Prov ⌜A⌝ → Prov ⌜Prov ⌜A⌝⌝`, formalized Σ₁
  completeness of `Prov`.
- **A diagonal sentence G** with ⊢ G → ¬`Prov ⌜G⌝` and the converse.
  Since §9 bars a substitution function in types, G is built
  relationally: G := for every y with `Sub ⌜φ⌝ y`, ¬`Prov y`. Building
  it needs a proof that `Sub` is functional.

Every internal implication here goes from inductive derivations to
inductive derivations or to `False`. It calls earlier, closed lemmas,
as `con.sl` does. The final step ("from ⊢ Con build ⊢ ⊥") applies
closed proofs at the top level, as `top_mp.sl` does. So the
stratification of §2.3 does not obviously block route B (my
reasoning). The usual G2 argument from D1 to D3 is intuitionistic, so
anticlassicality (README.md, `tests/anticlassical.sl`) is no exemption.
G2 fails for some very weak theories with suitably weak consistency
statements (Willard's self-verifying systems, from memory). So D3 is a
real premise, not a formality. As far as I can see, this route is how
self-formalizations meet G2: they prove consistency of a weaker system
inside the stronger one, as in Barras's Coq-in-Coq, from memory.

**C. Normalization implies consistency (05 §4.3).** This is route B
plus a lemma. If ⊢ "every accepted program's stripped run is safe" for
the formalized semantics, then ⊢ ¬`Prov ⌜False⌝`. Given a proof `p` of
`(False)`, the program whose final `(Fn L -> (many (Nat) r))` has body
`(lift p)` is accepted (§29: defining it "involves no evaluation").
Stripped, it reaches absurd code (`proto/review5/05_stripped_absurd_final.sl`).
Internally that needs two lemmas about the formalization:
- `Prov ⌜False⌝` implies acceptance of that program;
- its formalized stripped run reaches absurd code.

Neither has been tried. With them and route B's D1 to D3, consistency
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
- Σ₁-completeness for a halting relation (⊢ `Halts e` whenever e
  halts, by a written derivation);
- Σ₁-soundness (⊢ `Halts e` only if e halts; this follows from
  SOUNDNESS.md's (T), (S), and (E)).

From these, some e diverges while ⊬ ¬`Halts e`. If every true
non-halting statement were provable, enumerating proofs would decide
halting. Every proof of G2 I know needs some internalized Σ₁
completeness, D3 or an instance of it.

### 2.5 The cheap diagonal against Gödel II

| Claim | 03's diagonal (no Gödel) | What the Gödel route adds |
|---|---|---|
| No faithful, hypothesis-free, non-erased `compile : Src -> Verdict` (03 F6) | Gives it, under §3.4's premises | Nothing |
| Uniform H not provable in a form a function can recurse on (03 F6/F7, 05 §4.3) | Gives it, with soundness ((T), (S), (E)) and a faithful stepper | Needs only consistency, and also covers non-recursable forms (¬¬H, Π-forms), but only for H *with* safety (H alone does not give Con: a stripped run that reaches absurd code still "halts" in some sense) |
| Uniform stripped-run safety not provable (05 §4.3, T7) | Does not give it: a Π statement yields nothing to run | The only route, under route B's D1 to D3 and route C's two lemmas |
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
with no proof, as a top-level call is (§20). The invariants (I1) to (I3)
at that call are those in force at the end of elaboration. Part 5's
remark that each `Program` step is "a total call" treats driver-made
calls as covered. So I read (T) as covering the final-`Fn` call, and
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
  exit 0.
- `--extract out.ml` writes the OCaml, exit 0. (`--extract` takes the
  next argument as its output path. Written as `--extract
  ../../../../std/macro.sl 03_detour.sl`, it took `std/macro.sl` as the
  output and failed with "unbound name `macro-fail`" before writing
  anything; `git status` shows the file unchanged.)
- `--build` builds a program that prints `(BFalse)`.
- `slc ... --interpret` prints `(BFalse)`.
- `slc ... --build` builds a program that prints `(BFalse)`.
- From `proto/fuel/`, `diagonal.sl` (969 bytes) is accepted and prints
  its string.

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
   unlimited stack and heap"; that is my reading.
4. The rest of the macro run ends. In `diagonal.sl` this is by
   inspection: `diag-fn`, `macro-fail`, `fail-raw`, and `str-raw`
   (`std/macro.sl:5-36`) are non-recursive and call only `read-file`
   and `intern-string`. Those must return; for `read-file` that is a
   host assumption (03 F7). 03's "the same way" cannot be a P, because
   `diag-fn` needs a `MacroWorld` that only the expander supplies (§65).
   Inspection replaces it here. For a real `compile`, the macro must
   also read every file of its unit and build `Src` from them, still by
   non-recursive code plus calls already covered.
5. `read-file` returns Q's text in Q's run. That is, "faithful" is
   relative to a fixed file system (§2.1).

Under 1 to 5, Q's spec run ends, and its verdict is the negation of
`compile`'s answer on Q, as 03 F6 says. Premise 1 is the weakest. If
"the checker" in part 1 means the implementations, P's acceptance is
established (§3.3), but premise 2 then adds that the spec agrees with
them on P.

## 4. Suggested wording for 03 and 05 (not applied)

**03 F6, after "(T) and (E) for P then say that this call of `compile`
returns, reading part 5 as counting the driver's call as one of the
activations it covers."** Add: "SOUNDNESS.md does not mention the
driver's call of a final `Fn` value. Part 5's measure argument asks no
decrease of a root activation, and its last sentence calls each
`Program` step 'a total call', so this reading seems sound, but it is a
reading. The macro's other code cannot be given a P, since it needs a
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

> Gödel's second theorem would apply in this conditional form. Let
> `Prov` be a Sleight inductive relation on codes of units, formalizing
> acceptance under `--goal proved` (§71). Suppose (a) no unit proves
> `(goal erased (False))`; (b) whenever a unit proves T, one proves
> `(Prov ⌜T⌝)`; and (c) Sleight proves D2 and D3 for `Prov` and a
> diagonal sentence built relationally (§9 bars substitution in a type).
> Then no unit proves ¬`(Prov ⌜False⌝)`. If moreover Sleight proves
> that `(Prov ⌜False⌝)` yields an accepted program whose stripped run
> reaches absurd code, it cannot prove uniform stripped-run safety. The
> same goes for uniform (T) with full-semantics safety. None of (b),
> (c), or that lemma has been attempted (09 §2.4). Anticlassicality does
> not exempt Sleight, since the argument is intuitionistic. README.md's
> IΣ₂ remark concerns provably total functions and does not supply (c).

Also delete "The claimed IΣ₂ strength (F9) appears to be more than such
results usually need": strength in provably total functions is not what
G2's conditions ask.

**05 T7.** Replace "if it is consistent and meets Gödel II's conditions
(unchecked)" with "if it is consistent and conditions (b) and (c) of
§4.3 hold for a formalized `Prov` (unattempted)".

**05 §9.** Replace "That Sleight meets the conditions of Gödel's second
theorem (r.e. checker, enough arithmetic, derivability conditions)"
with: "r.e. holds under the readings of 09 §2.2. Σ₁ statements and
consistency of a coded system are expressible as goals (09 §2.3,
compiled). D1 to D3 for a formalized `Prov`, the diagonal sentence, and
any interpretation of HA or IΣ₁ are unattempted. The naive arithmetic
interpretation meets level stratification (09 §2.3, compiled)."

**00-summary's Gödel bullet** (line 576) should then point to 09 for
the conditions. It is not part of this task.

## 5. Unverified

- That the spec's elaboration is a finitely branching computable
  process (§2.2). DESIGN.md is prose.
- The relational Q axioms: I cited the prelude lemmas but did not write
  the axioms out. I did not try HA, IΣ₁, or Σ₁ induction beyond the
  fixed-level shape of `hyp_fixed.sl`.
- The S-axiom remark in route A is reasoning, not a compiled
  impossibility. A cleverer translation is not ruled out.
- Route B: no `Prov`, D2, D3, `Sub`, or G was built. Whether D2 holds
  given §71's one goal per unit and the global gensym and literal state
  is open.
- Route C's two lemmas, and the claim that normalization implies
  consistency in weak arithmetic (from memory).
- The named results are from memory, unchecked: G2 for HA, Feferman's
  Σ₁-presentation condition, Willard's self-verifying systems, Barras's
  Coq-in-Coq, and the Kleene G1 argument.
- §3.2's reading of parts 1, 3, 5, and 7 for the driver's call. Whether
  (E)'s "follows" implies termination of the stripped run.
- §3.4 premise 2 (the spec accepts P as the implementations do) and
  premise 3 (the evaluator's run and the driver's run are one semantics).
