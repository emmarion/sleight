# 07. Prior art

A Claude session's summary, written overnight at the owner's request.
Everything below is taken from `evidence/A6-prior-art.md`, the report
of a survey agent that fetched the sources it cites and quotes them
there with their URLs. This session has not re-read those sources, so
each line here is the survey's reading, not a checked fact. Points the
survey marked as recalled from memory are left out.

## 7.1 The closest precedents

**MetaCoq (Coq's type checker verified in Coq).** Normalization is a
hypothesis of the checker, not a result. The reduction machine has no
clock: it recurses on an accessibility proof that the hypothesis
supplies, and the proof is erased at extraction. The survey quotes the
authors: termination of reduction "is actually the only place where we
need to use this axiom". Where the checker is run inside the erasure
plugin, the hypothesis is discharged by an axiom named
`fake_normalization`. Numbers remain in two places: fuel bounded by
the size of a set in the universe-graph code, and a padding of the
accessibility proof, `Acc_intro_generator ... 1000`, used to run the
checker inside Coq. The checker is proved sound and complete: its
error result carries a refutation, a function from a typing derivation
to `False`. This is the handoff's result (ii) in a shipped system, and
it shows the open point of that route: something has to supply the
hypothesis where the program actually runs.

**CakeML (a verified, bootstrapped ML compiler).** The top-level
specification classifies every input string: it does not parse, or it
is ill-typed, or it executes with a set of behaviours. The compiler's
theorem matches each of its own outcomes to that classification, and
keeps one outcome that the theorem says nothing about, written
`Failure CompileError ⇒ true`. The parser and the type inferencer are
proved sound and complete; before completeness was proved, the
top-level relation had to carry a list of the declarations the
inferencer had rejected. The source semantics carries a clock that
exists only in the specification. Its top-level definition of a
program's behaviour asks whether some clock value suffices, which uses
classical logic. The FFI is an oracle in the semantics' state. The
compiler's own program is proved to terminate on every input, with no
hypothesis. The survey infers, from the passages it read, that this is
possible because CakeML's compiler never runs the program it compiles.
Sleight's compiler runs user code at compile time, so that theorem has
no counterpart here.

**CompCert.** Leroy's remark, quoted by the survey: "a compiler that
always fails (Comp(S) = Error for all S) is indeed verified, although
useless." CompCert's verified parser takes fuel (2^50 in the shipped
code) and has a third, internal-error result; its authors note that
termination on invalid input was not proved. Its source semantics
leaves C's evaluation order open, and that cost a second semantics
with a chosen order, a predicate that every order is safe, and a final
theorem that is a simulation, not an equation. Memory is blocks with
abstract identifiers and a deterministic allocator; states at
different stages are related by an injection, and pointer comparison
is defined so that it survives the injection.

**Cogent.** One language with two semantics, a pure one and one that
updates a store, and a machine-checked proof that every run of the
second has a matching run of the first. Sole reference is in neither
semantics. It is the invariant of the relation between them, with a
frame condition. Each foreign function owes the same three facts: its
updating version's run implies its pure version's, the results
correspond, and the frame condition holds.

**Verified extraction from Coq to OCaml.** The proof stops at
Malfunction, an untyped intermediate language of the OCaml compiler,
because OCaml has no formal specification. Its heap is an abstract
class with a `fresh` relation. The theorem covers results of
first-order type and assumes normalization.

## 7.2 What the precedents suggest for each decision

| Decision | Precedent | What it suggests |
|---|---|---|
| D1, the shape of "accepted or rejected" | CakeML's classification of the input string; MetaCoq's hypothesis; the always-failing compiler | State the verdict as a classification of source text. Name any outcome the theorem leaves out. A totality statement has content only with the other direction or with refutations. |
| D2, never both | MetaCoq and PLFA return `A -> False` and get it for free; CakeML proved completeness and had to add a determinism condition to its declarative rules | A positive `Fails` needs a separate exclusivity lemma to mean "has no typing". Expect determinism side conditions. |
| D3, the run | CompCert and CakeML specify a heap machine only; Cogent and Linear Haskell have both a pure and a mutating semantics, joined by a language-wide proof | A heap machine as the specification is the norm in compiler verification. A pure second reading is an addition whose proof is the sole-reference invariant. |
| D4, evaluation order | CakeML fixes right to left; Malfunction fixes function first, then arguments left to right; Standard ML fixes left to right; OCaml leaves it unspecified; CompCert proves a refinement from open to chosen | Each of the four formal semantics whose order the survey checked (CompCert, CakeML, Malfunction, and Standard ML) fixes an order or comes with a proved refinement to a chosen one. If slc emits OCaml source, a fixed order has to be imposed by sequenced `let`s, since OCaml promises none for applications, tuples, records, or arrays. |
| D5, addresses | CompCert's `nextblock` and injections; CakeML's list index; verified extraction's `fresh` relation | Both a deterministic allocator and a `fresh` relation are workable. With `slot-eq` as §67 states it, the specification has a choice at that point either way. |
| D6, what the outside supplies | CakeML's FFI oracle; Cogent's obligations on foreign code | Model the outside as an oracle the semantics is a function of. List each foreign implementation as an assumption shaped like the main theorem. |
| D8, fuel | MetaCoq: no clock in its reduction machine, a halting witness instead; interaction trees: a hand-written driver loop outside the proof; Agda Core: fuel in the proofs and an infinite fuel value supplied by the host; Lean4Lean: depth fuel 1000 and an error when it runs out; McBride: fuel re-supplied from outside is harmless when results are monotone in it | The two routes with no clock in the evaluator are the halting witness and the driver loop. They differ in what `compile` is: a function that cannot be called without the witness, or a process. Limits that are part of the language, such as §62's 10000, are a different thing. |
| D9, route | Lean4Lean ported first and verified later, and has conjectures; MetaCoq specified and proved together, and has completeness | A kernel that re-checks an untrusted front end certifies accepted programs and says nothing of rejected ones. |
| D10, where the output proof stops | Verified extraction stops at Malfunction; CompCert trusts extraction and the OCaml compiler; CakeML bootstraps in the logic | A small modelled language with a printer that decides nothing is the Malfunction design. The gap between the model and the OCaml compiler stays trusted. |
| Crashes (§31) | CakeML: the machine's behaviours are the specification's, possibly cut short by a resource limit | §31's "A crash produces no value, never a different one" has this formal counterpart. An output that always crashes satisfies it. |

## 7.3 Reading, in the survey's order of usefulness

1. Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, and
   Winterhalter, "Correct and Complete Type Checking and Certified
   Erasure for Coq, in Coq", Journal of the ACM, 2025.
   https://doi.org/10.1145/3706056
2. Tan, Myreen, Kumar, Fox, Owens, and Norrish, "The verified CakeML
   compiler backend", Journal of Functional Programming, 2019.
   https://cakeml.org/jfp19.pdf. With it: Owens, Myreen, Kumar, and
   Tan, "Functional Big-Step Semantics", ESOP 2016.
   https://cakeml.org/esop16.pdf
3. O'Connor and others, "Cogent: uniqueness types and certifying
   compilation", Journal of Functional Programming, 2021, section 4.
   https://doi.org/10.1017/S095679682100023X
4. McBride, "Turing-Completeness Totally Free", MPC 2015.
   https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf
5. Leroy, "Formal verification of a realistic compiler",
   Communications of the ACM, 2009, section 2.
   https://xavierleroy.org/publi/compcert-CACM.pdf
