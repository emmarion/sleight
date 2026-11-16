# A6. Prior art for "Sleight formalized in Sleight, and a compiler proved to agree with it"

Written by agent A6 (a Claude session). Nothing here is the owner's decision. Claims about the
literature are mine; claims about Sleight are tagged by where they come from.

## 0. Read this first

**Network.** The network worked. I downloaded sources with `curl` and read the extracted text
myself (not a summarizer's paraphrase). Blocked hosts: HAL (bot wall), ACM DL (403), gitlab.inria.fr
(bot wall), github.com HTML and API (403; `raw.githubusercontent.com` worked), bu.edu and
cl.cam.ac.uk for three papers (403/404). What I could not fetch is marked `[RECALL]`.

**Tags.**
- `[SOURCE Sn]` = I fetched the source `Sn` (URL in the key table below) in this session and read
  the passage I cite. For long papers I read only the cited passages, not the whole paper.
- `[RECALL]` = from my memory of the literature, unchecked. Treat as unverified.
- `[QUOTE file:line]`, `[RAN]`, `[INFERENCE]`, `[UNKNOWN]` as in the common brief.
- Quotations are exact, except for three repairs of `pdftotext` damage: I restored dropped
  `fi`/`ff` ligatures (S2), restored underscores in HOL identifiers and the prefix-order symbol
  (S14 to S17), and unwrapped line breaks. Section numbers are the papers' own where the text
  showed them; where I could not see one I name the passage instead.

**Local copies** (to re-check any quotation with `grep`):
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A6/dl/<name>/`
holds each PDF and its text (`flow.txt` or `paper.txt`); source files are in `metarocq-src/`,
`compcert-src/`, `vextr-src/`, `misc-src/`, and `misc2/` there.

**Source keys.**

| Key | What | URL |
|---|---|---|
| S1 | Sozeau, Boulier, Forster, Tabareau, Winterhalter, "Coq Coq Correct!", POPL 2020 | https://www.ps.uni-saarland.de/Publications/documents/SozeauEtAl_2020_CoqCoqCorrect.pdf |
| S2 | Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, Winterhalter, "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq", JACM 2025 (repository copy) | https://www.repository.cam.ac.uk/bitstreams/2306e91b-50a1-40c9-b1c7-3a05cce92bc4/download |
| S3 | MetaCoq sources, branch `coq-8.20`: `pcuic/theories/PCUICSN.v`, `safechecker/theories/{PCUICErrors,PCUICTypeChecker,PCUICSafeReduce}.v`, `erasure-plugin/theories/Erasure.v`, `safechecker-plugin/theories/SafeTemplateChecker.v` | https://raw.githubusercontent.com/MetaCoq/metacoq/coq-8.20/ (+ path) |
| S4 | MetaRocq README | https://raw.githubusercontent.com/MetaRocq/metarocq/main/README.md |
| S5 | Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean", arXiv:2403.14064v3 | https://arxiv.org/pdf/2403.14064 |
| S6 | Agda Core sources: `README.md`, `src/Agda/Core/{Reduce,Prelude}.agda`, `src/Agda/Core/Checkers/Converter.agda`, `app/Main.hs` | https://raw.githubusercontent.com/jespercockx/agda-core/master/ (+ path) |
| S7 | Brady, "Idris 2: Quantitative Type Theory in Practice", ECOOP 2021 | https://arxiv.org/pdf/2104.00480 |
| S8 | Brown and Palsberg, "Breaking Through the Normalization Barrier: A Self-Interpreter for F-omega", POPL 2016 | http://compilers.cs.ucla.edu/popl16/popl16-full.pdf |
| S9 | Bauer, blog post "A Brown-Palsberg self-interpreter for Gödel's System T" (2016) | https://math.andrej.com/2016/01/04/a-brown-palsberg-self-interpreter-for-godels-system-t/ |
| S10 | Turner, "Total Functional Programming", JUCS 10(7), 2004 | https://www.jucs.org/jucs_10_7/total_functional_programming/jucs_10_07_0751_0768_turner.pdf |
| S11 | McBride, "Turing-Completeness Totally Free", MPC 2015 | https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf |
| S12 | Harrison, "Towards self-verification of HOL Light", IJCAR 2006 | https://www.cl.cam.ac.uk/~jrh13/papers/holhol.pdf |
| S13 | Abrahamsson, Myreen, Kumar, Sewell, "Candle: A Verified Implementation of HOL Light", ITP 2022 (abstract only read) | https://cakeml.org/itp22-candle.pdf |
| S14 | Kumar, Myreen, Norrish, Owens, "CakeML: A Verified Implementation of ML", POPL 2014 | https://cakeml.org/popl14.pdf |
| S15 | Owens, Myreen, Kumar, Tan, "Functional Big-Step Semantics", ESOP 2016 | https://cakeml.org/esop16.pdf |
| S16 | Tan, Myreen, Kumar, Fox, Owens, Norrish, "The Verified CakeML Compiler Backend", JFP 2019 | https://cakeml.org/jfp19.pdf |
| S17 | Tan, Owens, Kumar, "A Verified Type System for CakeML", IFL 2015 | https://cakeml.org/ifl15.pdf |
| S18 | CakeML sources, `master`: `semantics/evaluateScript.sml`, `semantics/semanticPrimitivesScript.sml`, `semantics/ffi/ffiScript.sml` | https://raw.githubusercontent.com/CakeML/cakeml/master/ (+ path) |
| S19 | Leroy, "Formal verification of a realistic compiler", CACM 2009 | https://xavierleroy.org/publi/compcert-CACM.pdf |
| S20 | CompCert sources, `master`: `driver/Compiler.v`, `common/{Smallstep,Memory,Values}.v`, `cfrontend/{Cstrategy,Csem,Cexec}.v`, `cparser/Parse.ml` | https://raw.githubusercontent.com/AbsInt/CompCert/master/ (+ path) |
| S21 | Blazy and Leroy, "Mechanized semantics for the Clight subset of the C language", JAR 2009 | https://xavierleroy.org/publi/Clight.pdf |
| S22 | Jourdan, Pottier, Leroy, "Validating LR(1) parsers", ESOP 2012 | https://xavierleroy.org/publi/validated-parser.pdf |
| S23 | Anand et al., "CertiCoq: A verified compiler for Coq", CoqPL 2017 | https://www.cs.princeton.edu/~appel/papers/certicoq-coqpl.pdf |
| S24 | Mullen, Pernsteiner, Wilcox, Tatlock, Grossman, "Œuf: Minimizing the Coq Extraction TCB", CPP 2018 | https://homes.cs.washington.edu/~ztatlock/pubs/oeuf-mullen-cpp18.pdf |
| S25 | Verified extraction Rocq→OCaml: repository `README.md` and `theories/{SemanticsSpec,PipelineCorrect,Pipeline,CompileCorrect,Firstorder}.v` (branch `main`); the PLDI 2024 abstract as shown on rocq-prover.org | https://raw.githubusercontent.com/MetaRocq/rocq-verified-extraction/main/ (+ path); https://rocq-prover.org/papers/verified-extraction-from-coq-to-ocaml |
| S26 | Malfunction specification | https://raw.githubusercontent.com/stedolan/malfunction/master/docs/spec.md |
| S27 | Kanabar et al., "PureCake: A Verified Compiler for a Lazy Functional Language", PLDI 2023 | https://cakeml.org/pldi23-purecake.pdf |
| S28 | O'Connor, Chen, Rizkallah, Jackson, Amani, Klein, Murray, Sewell, Keller, "Cogent: uniqueness types and certifying compilation", JFP 31, e25, 2021 | https://doi.org/10.1017/S095679682100023X (fetched from https://www.cambridge.org/core/services/aop-cambridge-core/content/view/47AC86F02534818B95A56FA1A283A0A6/S095679682100023Xa.pdf/cogent-uniqueness-types-and-certifying-compilation.pdf) |
| S29 | Bernardy, Boespflug, Newton, Peyton Jones, Spiwack, "Linear Haskell", POPL 2018 (arXiv version with appendix) | https://arxiv.org/pdf/1710.09756 |
| S30 | Ahmed, Fluet, Morrisett, "L3: A Linear Language with Locations", Fundamenta Informaticae 2007 | https://www.ccs.neu.edu/home/amal/papers/linloc-fi07.pdf |
| S31 | Reinking, Xie, de Moura, Leijen, "Perceus: Garbage Free Reference Counting with Reuse", MSR-TR-2020-42 | https://www.microsoft.com/en-us/research/uploads/prod/2020/11/perceus-tr-v1.pdf |
| S32 | Ullrich and de Moura, "Counting Immutable Beans", IFL 2019 | https://arxiv.org/pdf/1908.05647 |
| S33 | Lorenzen, Leijen, Swierstra, "FP²: Fully in-Place Functional Programming", MSR-TR-2023-19 | https://www.microsoft.com/en-us/research/uploads/prod/2023/05/fbip.pdf |
| S34 | Marshall, Vollmer, Orchard, "Linearity and Uniqueness: An Entente Cordiale", ESOP 2022 | https://link.springer.com/content/pdf/10.1007/978-3-030-99336-8_13.pdf |
| S35 | Jung, Jourdan, Krebbers, Dreyer, "RustBelt", POPL 2018 | https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf |
| S36 | Jung, Dang, Kang, Dreyer, "Stacked Borrows", POPL 2020 (abstract only read) | https://plv.mpi-sws.org/rustbelt/stacked-borrows/paper.pdf |
| S37 | Weiss, Gierczak, Patterson, Ahmed, "Oxide: The Essence of Rust" (abstract only read) | https://arxiv.org/pdf/1903.00982 |
| S38 | Leroy and Grall, "Coinductive big-step operational semantics", Inf. Comput. 2009 | https://arxiv.org/pdf/0808.0586 |
| S39 | Xia et al., "Interaction Trees", POPL 2020 | https://arxiv.org/pdf/1906.00046 |
| S40 | Bove and Capretta, "Modelling general recursion in type theory", MSCS 2005 | https://www.cs.nott.ac.uk/~pszvc/publications/General_Recursion_MSCS_2005.pdf |
| S41 | Danielsson, "Operational Semantics Using the Partiality Monad", ICFP 2012 | https://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.pdf |
| S42 | Amin and Rompf, "Type Soundness Proofs with Definitional Interpreters", POPL 2017 | https://www.cs.purdue.edu/homes/rompf/papers/amin-popl17a.pdf |
| S43 | Wadler, Kokke, Siek, PLFA, chapter "Inference" | https://plfa.github.io/Inference/ |
| S44 | OCaml manual source `manual/src/refman/expr.etex` and `stdlib/repr.mli` (trunk) | https://raw.githubusercontent.com/ocaml/ocaml/trunk/ (+ path) |
| S45 | Milner, Tofte, Harper, MacQueen, "The Definition of Standard ML (Revised)" | https://smlfamily.github.io/sml97-defn.pdf |

---

## 1. Findings that bear directly on the decisions

**F1. The closest precedent for "the compiler agrees with the spec, no consistency theorem, under a
hypothesis H that the spec's runs halt" is MetaCoq, and it shows the exact shape.**
- Normalization is a *hypothesis*, not a result: `Class NormalizationIn ... (Σ : global_env_ext) := normalization_in : forall Γ t, welltyped Σ Γ t -> Acc (cored Σ Γ) t.` and the type checker is defined under the section context `{normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}`. [SOURCE S3 PCUICSN.v, PCUICTypeChecker.v]
- It is used in one place only: "termination of reduction to whnfs only holds if the system is strongly normalizing, and this is actually the only place where we need to use this axiom. This axiom is propositional, so we also know that none of the programs we develop can rely on its computational content, and it can be safely erased by extraction." [SOURCE S2 §1]
- The reduction machine has no fuel: "We implement the reduction machine of Coq without relying on fuel. Instead we assume strong normalization of the system (for well-typed terms) and proceed by well-founded induction. Once extracted, this should roughly correspond to the OCaml implementation." [SOURCE S3 PCUICSafeReduce.v]
- Termination is promised only for accepted input: "this only applies to inputs that satisfy potentially erased preconditions. For instance, our weak-head reduction machine is only guaranteed to terminate on well-typed terms." [SOURCE S2 footnote 26]
- Where the program is actually run, the hypothesis is discharged by an axiom: `Axiom fake_normalization : PCUICSN.Normalization.` with the comment "Ideally we'd have a MetaCoq template program that generates a proof of Strong Normalization for the particular program we're erasing. For now we just axiomatize SN." [SOURCE S3 erasure-plugin/theories/Erasure.v]
- The authors name the resulting position: "moving from a trusted code base (TCB) to a trusted theory base (TTB) paradigm". [SOURCE S2 abstract]
- Transfer: this is the handoff's result (ii) ("under a hypothesis H that every accepted compile-time form's spec run halts, `compile` is a total function"). [INFERENCE: I am matching the handoff's wording, item 4, to S2; the handoff says the owner's reply was not agreement to exact statements.]
- The same mechanism is expressible in the reference implementation: a non-erased function may recurse on an erased derivation that a machine halts. [RAN] `/home/user/sleight/_build/default/bin/main.exe /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A4/halts.sl` printed `3` and two warnings, exit 0; that file (another agent's) defines `(many run : (many (Nat) n) (subterm erased (Halts n) h) -> (many (Nat) steps))`. [RAN] `/home/user/sleight/_build/default/bin/main.exe /home/user/sleight/tests/erased_subterm.sl` printed `2` and one warning (a `many` function with a `subterm erased (Nat) n` parameter). This is what the implementation accepts, not a statement of what DESIGN.md says.

**F2. A total evaluator for all of Sleight, written as a Sleight function, cannot exist; the
literature offers four ways out, and the owner's `Program` idea is one of them.**
- Applying the theorem below to Sleight is [INFERENCE]. It rests on the premise that every Sleight function terminates, which the task statement gives and DESIGN.md supports with "Termination rests on levels." [QUOTE DESIGN.md:696, §17]; I did not check the premise.
- "Theorem: For any language in which all programs terminate, there are always-terminating programs which cannot be written in it - among these are the interpreter for the language itself." [SOURCE S10 §6]
- Turner's two accommodations: "1) We can have a hierarchy of languages, of ascending power, each of which can express the interpreters of those below it"; "2) ... it seems that there will always be at least one place – in the loader for example – where we are obliged to escape from the type discipline." [SOURCE S10]
- McBride: "There are termination proof obligations which we can formulate but not discharge within any given total language, even though the relevant programs—notably the language's own evaluator—are total." and "it takes the system in which you use it to execute arbitrary recursive computations for as long as you are willing to tolerate." [SOURCE S11 §1, §5]
- The four ways out: (a) an outer driver that loops over a total step (Turner's "loader", McBride's "system", interaction trees' hand-written `run`); (b) an explicit halting witness as an argument (Bove–Capretta, MetaCoq); (c) fuel or a clock; (d) stratification, an interpreter for a weaker fragment. [INFERENCE: my grouping of S10, S11, S39, S40, S2, S15, S12.]
- DESIGN.md already describes (a) for the run: "It never recurses, so an unbounded interaction is the driver's loop over total functions." [QUOTE DESIGN.md:1993-1994, §42]
- The typed self-interpreter of Brown and Palsberg does not give an evaluator over a datatype of programs. Their result is `u` with `(u ⌜e⌝) ≡β e` for a quoter that is a meta-level function, and it works because "it is possible for u and pu to be typeable in Fω, and yet for (pu pu) to be untypeable". [SOURCE S8 §1, §3.2] Bauer: "their conditions allow a self-interpreter for practically any total language expressive enough to encode numbers and pairs". [SOURCE S9]

**F3. "Every source program is accepted or rejected" has one fully worked precedent, CakeML's
top-level theorem, and it needed completeness results that changed the declarative type system.**
- The spec is a total classification of the source *text*: `cakeml_semantics ffi prelude input = case parse (lex input) of None ⇒ CannotParse | Some prog ⇒ if can_type_prog (prelude ++ prog) then Execute (semantics ffi (prelude ++ prog)) else IllTyped`. [SOURCE S16 §10.2]
- The theorem matches each compiler outcome to it (Fig. 10): `Success (code,data,cc')` gives `∃ behaviours. cakeml_semantics ffi prelude input = Execute behaviours ∧ ... machine_sem mc ffi ms ⊆ extend_with_resource_limit behaviours`; `Failure ParseError ⇒ cakeml_semantics ffi prelude input = CannotParse`; `Failure (TypeError _) ⇒ ... = IllTyped`; `Failure CompileError ⇒ true`; `Failure (ConfigError _) ⇒ true`. [SOURCE S16 Fig. 10]
- It rests on "The parser and type inferencer have been proved sound and complete, which means that an error there indicates a fault by the user." [SOURCE S16 §2.1]
- Before completeness existed, the top-level relation had to carry a list saying which declarations the inferencer rejected: "The bool list argument indicates which input declarations have type errors (needed because we have not yet verified completeness for the type inferencer; see Section 5)." [SOURCE S14 §2]
- Completeness forced a side condition into the declarative rules: "In CakeML, such definitions do not type check, and the CakeML type system thereby maintains the principal type property ... This is the critical property that supports a complete inference algorithm." [SOURCE S17 §3.3]
- A third outcome the theorem says nothing about is kept explicit (`Failure CompileError ⇒ true`). [SOURCE S16 Fig. 10]
- Without the other direction the totality statement is empty: "a compiler that always fails (Comp(S) = Error for all S) is indeed verified, although useless." [SOURCE S19 §2.2] and "there is nothing to prevent us from writing a function that always returns an error, even when there exists a correct derivation. Demonstrating both soundness and completeness is significantly stronger than demonstrating soundness alone." [SOURCE S43]
- Transfer: the handoff's "accepted programs carry a derivation of the spec's typing; rejected ones carry a derivation of a positive `Fails` relation" gives a theorem with content only together with "never both accepted and rejected", which the handoff lists as an open scope question. [INFERENCE: from S19, S43, and the handoff's section C. MetaCoq and PLFA get the exclusivity for free because their negative evidence is `A -> False`, see §6 below.]
- DESIGN.md already bounds macro expansion, so that part of acceptance needs no extra fuel: "At most 10000 expansions run in one run, every file on the command line included." [QUOTE DESIGN.md:2752-2753, §62]

**F4. Whether fuel shows in the final theorem depends on where it lives.** Summary table in §5.
The two clean precedents are opposite: CakeML keeps a clock in the *spec* and none in the
implementation ("these only appear in the proof, not in the implementation" [SOURCE S14 §1]);
MetaCoq keeps a halting *hypothesis* and no clock in its reduction machine [SOURCE S2 §1; S3
PCUICSafeReduce.v]. The cases where fuel
stays in the implementation all leave a visible third outcome: Lean4Lean "throw a deepRecursion
error if we run out of fuel" [SOURCE S5 §3.2.1]; CompCert's parser "Timeout_pr means that we ran
for 2^50 steps" → "internal error while parsing" [SOURCE S20 cparser/Parse.ml]; Agda Core
"not enough fuel to reduce a term" [SOURCE S6 Converter.agda].

**F5. CakeML's way of hiding the clock uses classical logic; Sleight's logic is reported to be
anticlassical.**
- CakeML: `semantics t = if ∃ c v s. sem_t (s_with_clock c) t = (Rval v,s) then Terminate else if ∀ c. ∃ s. sem_t (s_with_clock c) t = (Rtimeout,s) then Diverge else Crash`. [SOURCE S15 §2.3] Its 2014 REPL function "is total; however, it is not computable ... being a function in the logic, it is able to ask whether there exist a number of steps in which execution of code for the next declaration would terminate." [SOURCE S14 §2]
- Leroy and Grall: "The majority of our proofs are constructive, but some use the axiom of excluded middle", for example "By excluded middle, either ∃v. a ⇒ v or ∀v, ¬(a ⇒ v)." [SOURCE S38, the passage on Coq's presentation of coinduction, and the proof of Theorem 49]
- Danielsson: an evaluator returning a value with a proof, or a proof of non-termination, or a proof of going wrong: "It should be clear that it is impossible to implement eval in a total, constructive language, as this amounts to solving the halting problem." [SOURCE S41 §1]
- The README (session-written) says "Sleight's logic is anticlassical." [QUOTE README.md:108] The test it cites passes: [RAN] `/home/user/sleight/_build/default/bin/main.exe /home/user/sleight/tests/anticlassical.sl`, exit 0, no output.
- Transfer: a Sleight spec cannot define "the behaviour of a program" by case analysis on whether a halting clock exists, and cannot prove "halts or diverges". The run's spec has to be relational (`Halts p v`; divergence as a negative or step-indexed statement), and totality statements need a positive witness such as H. [INFERENCE: general constructive reasoning plus the test above; a single instance `P ∨ ¬P` is unprovable in general rather than refuted.]

**F6. Two semantics for one language, pure and mutating, with a proof that they agree: Cogent did
it mechanically, and the proof's invariant is exactly "unique means sole reference, plus a frame
condition".** Details in §3.6 and §4. The direction proved is update ⇒ value: "every evaluation in
the update semantics has a corresponding evaluation in the value semantics that preserves our
refinement relation". [SOURCE S28 §4.2.3] The mutating semantics is the one tied to the generated
code; the pure one exists "for equational reasoning". [SOURCE S28 abstract, §4.1] So if the spec's
run is a mutating heap machine from the start (handoff item 6), a sole-reference theorem is needed
only to justify a second, pure reading, not for compiler agreement. [INFERENCE: from the role each
semantics plays in S28; it matches the handoff's "claim of the session's" paragraph.]

**F7. Each formal semantics whose evaluation order I checked (CompCert, CakeML, Malfunction as used
by verified extraction, Standard ML) either fixes the order or comes with a proved refinement from
a nondeterministic spec to one chosen order.** CompCert does the second and pays
for it: a second semantics (`Cstrategy`), a `safe` predicate requiring that all orders are safe, and
a final theorem that is a backward simulation rather than an equality. [SOURCE S20 Cstrategy.v,
Csem.v, Compiler.v] CakeML fixes right-to-left. [SOURCE S16 §4.2; S18 evaluateScript.sml] Malfunction
fixes function first, then arguments left to right. [SOURCE S26] OCaml source leaves it unspecified.
[SOURCE S44] Details in §7.

**F8. DESIGN.md §31's crash clause has a precise formal counterpart in CakeML.**
- "A crash produces no value, never a different one." [QUOTE DESIGN.md:1321, §31]
- CakeML: `machine_sem mc ffi ms ⊆ extend_with_resource_limit (semantics ffi prog)` where `extend_with_resource_limit behaviours = behaviours ∪ { Terminate Resource_limit_hit io_list | ∃ t l. Terminate t l ∈ behaviours ∧ io_list ≼ l } ∪ { Terminate Resource_limit_hit io_list | ∃ ll. Diverge ll ∈ behaviours ∧ fromList io_list ≼ ll }`. [SOURCE S16 §2.3, Fig. 7]
- The same paper notes the weakness: "this weaker form of correctness allows for a trivial compiler implementation that always outputs a program that immediately cause an out-of-memory error." [SOURCE S16 §2.3]

**F9. `slot-eq` as DESIGN.md states it is already a nondeterministic, one-sided observation, so the
spec's run cannot be a function of the program alone.**
- "`ESome` proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs." [QUOTE DESIGN.md:3044-3046, §67]
- "An `extern` implementation must agree with its model: except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31)." [QUOTE DESIGN.md:1951-1955, §42]
- Precedents for a spec with such a choice: an oracle in the state, existentially quantified at the top (CakeML FOR-language: `non_det_o : (num -> bool)`, and "the correctness theorem is now stated as a subset relation" [SOURCE S15 §4]); or a relational spec with a backward simulation (CompCert [SOURCE S20 Compiler.v]). OCaml documents its own pointer equality the same one-sided way: "On non-mutable types, the behavior of [phys_equal] is implementation-dependent; however, it is guaranteed that [phys_equal e1 e2] implies [compare e1 e2 = 0]." [SOURCE S44 repr.mli]

**F10. A kernel that re-checks an untrusted elaborator's output certifies accepted programs only.**
Nothing follows about rejected ones unless the elaborator is proved complete or rejections carry
checkable negative evidence. [INFERENCE from S19 §2.2 ("validators are necessarily incomplete and
should reply false if they cannot establish S ≈ C") and S43; see §6.] This bears on the handoff's
"new certified kernel behind slc's front end" route against owner goal (4).

---

## 2. Self-formalization of a type theory in itself, and its limits

### 2.1 MetaCoq / MetaRocq

- **Specified.** The typing relation of PCUIC, close to Coq's kernel language, "without the module system, template polymorphism and η-conversion". [SOURCE S2 abstract]
- **Proved.** A type checker "proven sound and complete in Coq with respect to its formal specification" [SOURCE S2 abstract]; the README: "Implementation of a fuel-free and verified reduction machine, conversion checker and type checker for PCUIC. This relies on a postulate of strong normalization of the reduction relation of PCUIC on well-typed terms. The checker is shown to be correct and complete w.r.t. the PCUIC specification." [SOURCE S4]
- **How completeness is carried.** The result type holds a refutation: `Inductive typing_result_comp (A : Type) := | Checked_comp (a : A) | TypeError_comp (t : type_error) (a : A -> False).` and `infer ... : typing_result_comp ({ A : term & forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- t ▹ A ∥ })`. [SOURCE S3 PCUICErrors.v, PCUICTypeChecker.v] Conversion likewise returns "either a conversion or cumulativity proof for its inputs, or an error message together with a proof of the negation of conversion or cumulativity". [SOURCE S2 §6.3.3]
- **The route to completeness.** A bidirectional presentation is proved equivalent to the declarative one first, and "this part of our work does not rely on normalization, thus the equivalence between the declarative and algorithmic presentations of PCUIC is axiom free." [SOURCE S2 §1]
- **Constructive well-foundedness.** "While well-foundedness of a relation is classically stated as the absence of infinite descending chains, this negative statement is too weak in a constructive setting. Instead, we use the usual constructive reformulation ... the accessibility predicate Acc". [SOURCE S2 §5.1] The machine is `Fix_F` over `Acc` of a lexicographic order of reduction and position in the term. [SOURCE S1 §3.1–3.2]
- **A wrinkle worth knowing.** To *run* the checker inside Coq, where the hypothesis is opaque, they pad the accessibility proof: "We fuel the accessibility proof to run reduction inside Coq" with `Acc_intro_generator ... 1000`, which "*Lazily* add[s] 2^n - 1 Acc_intro on top of wf". [SOURCE S3 PCUICSafeReduce.v] So in-logic evaluation still needed a fuel-like device; extraction did not.
- **Erasure.** "Let Σ be a well-formed environment erasing to Σ′. Let Σ; Γ ⊢ t : T erasing to t′ and evaluating to v. Then there exists v′ s.t. Σ; Γ ⊢ t′ ▷ v′ and Σ; Γ ⊢ v ⇝E v′." (Theorem 4.7.) The erasure *function* does not commute with evaluation; a nondeterministic erasure *relation* containing it does, and the two agree on first-order types. [SOURCE S1 §4.3]
- **Trusted or assumed.** Strong normalization, and an abstract guard condition: `Axiom guard : FixOrCoFix → global_env_ext → context → mfixpoint term → Prop.` with properties such as stability under reduction. [SOURCE S2 §3.4] The 2020 paper also assumed subject reduction, validity, and others, since proved [SOURCE S1 §1; S4]. Still fuel inside one place: universe-graph longest paths use "the standard fuel trick, because we know that the number of necessary recursive calls is bounded by the cardinality of s". [SOURCE S2 §4.1]
- **Lesson for Sleight.** (1) State H as a parameter used at the single point where the evaluator loops; keep the declarative-to-algorithmic equivalence H-free so most of the agreement proof does not depend on it. (2) Run the evaluator only on code already accepted, so that "halts on accepted code" is all H must say; DESIGN.md has that order: "Such a form runs as soon as it has been elaborated". [QUOTE DESIGN.md:1179-1180, §27] (3) Expect to need a bounded-by-size fuel in places unrelated to user code, as MetaCoq's universe graph does. (4) How the top of the program obtains H is a real question: MetaCoq uses an `Axiom`. [INFERENCE from the sources above.] Whether Sleight has a way to postulate an erased fact at the top level: [UNKNOWN], I did not look.

### 2.2 Lean4Lean

- **Specified.** Lean's typing judgment (`VExpr`), formalizing Carneiro's earlier thesis. [SOURCE S5 §1–2]
- **Proved.** "a definition of the typing judgment, some regularity theorems we can prove and others we can state, and the verification of some representative functions from the typechecker. The remainder is left as future work." Unique typing and definitional inversion are stated as conjectures. [SOURCE S5 §1, §2.4]
- **Termination.** Not proved, by choice: "It is unlikely that we can prove termination of a typechecker for Lean in Lean ... We are up against Gödel's incompleteness theorem, so anything that would imply the unconditional soundness of Lean won't be directly provable." Also "the Lean type theory is known not to terminate." [SOURCE S5 §3.2.1]
- **Fuel.** "use a fuel parameter, a natural number which counts the number of nested recursive calls to one of the Methods, and throw a deepRecursion error if we run out of fuel. Currently, this limit is a fixed constant (1000), which turns out to be sufficient for checking all of Mathlib". "fuel is only consumed when making a recursive call that is not otherwise decreasing". Bove–Capretta was rejected because "the kernel API is fixed to match Lean's actual kernel function, and we also actually want it to time out on extreme cases." [SOURCE S5 §3.2.1 and footnotes 11, 12]
- **Completeness.** "Lean's typechecker is known to not be complete ... but MetaRocq has a proof of completeness." [SOURCE S5 §8]
- **Process note.** "we took the approach of quickly getting to feature parity with the real Lean kernel and proving correctness later, so we ended up with a feature-complete typechecker but are still lacking in some theorems." [SOURCE S5 §8]
- **Lesson.** Two designs, two outcomes: port first and verify later yields a fast checker and conjectures; MetaCoq's specify-and-prove-together yields completeness and no fuel. Lean4Lean also shows the mildest fuel: charge it only on calls that do not otherwise decrease, and count nesting depth rather than steps. And a depth limit that is part of the system's intended behaviour is not a proof artifact: DESIGN.md's 10000-expansion cap is of that kind. [INFERENCE from S5, S2, and DESIGN.md:2752-2753.]

### 2.3 Agda Core ("Agda in Agda")

- **What it is.** "implemented in Agda ... a well-scoped syntax, an environment-based evaluator, a formal definition of the typing and conversion rules, and a derivation-producing type checker." [SOURCE S6 README.md] So: sound by construction, no completeness claim in the README.
- **Fuel.** `data Fuel : Set where None : Fuel; More : {{Fuel}} → Fuel`; `reduce ... : ... → {{Fuel}} → Maybe (Term α)` loops a total `step` function; the *specification* of reduction quantifies fuel away: `ReducesTo v w = Σ0[ r ∈ Singleton α ] Σ0[ rsig ∈ Singleton sig ] ∃[ f ∈ Fuel ] reduce r rsig v {{f}} ≡ Just w`. [SOURCE S6 Prelude.agda, Reduce.agda]
- **The knot.** The Haskell driver supplies `let fl = Core.More fl`, a cyclic, infinite fuel. [SOURCE S6 app/Main.hs line 387]
- **Lesson.** This is the "single total step, looped from outside" design (handoff section C, first bullet) in its unverified form: the proofs speak of finite fuel, and the compiled program runs with a value the proof language does not contain. Sleight's `Program` driver is the place where that loop can live without leaving the language's model. [INFERENCE from S6 and DESIGN.md:1993-1994.]

### 2.4 Idris 2

- **Status.** "the first language with full first-class dependent types implemented in itself". "We do not discuss the metatheory of QTT". [SOURCE S7 §1] No verification of the compiler is claimed there.
- **Erasure.** "An argument with multiplicity 0 is guaranteed to be erased at run time." [SOURCE S7 §3.3]
- **Linear is not unique.** "A function which takes an argument with multiplicity 1 promises that it will not share the argument in the future; there is no requirement that it has not been shared in the past." [SOURCE S7 §3] In-place update is recovered only by controlling construction: "if this is the only way of constructing an Array, then all arrays are guaranteed to be used linearly, so we can have in-place update." [SOURCE S7 §4.1]
- **Lesson.** DESIGN.md takes `erased` and `many` from Idris 2 and `unique` from Clean: "`erased` is Idris 2's multiplicity 0 and `many` is its ω ... `unique` is in the spirit of Clean's uniqueness, but attached to binders rather than to types". [QUOTE DESIGN.md:503-505, §13] So the guarantee Sleight's spec must capture is the uniqueness kind (a fact about the past), which Idris 2's QTT does not provide; see §4.

### 2.5 The barrier, precisely

- Classical statement: "Theorem 3.2. If u ∈ Univ(N → N), then u isn't total." with the diagonal `pu(x) = u(x,x) + 1`. [SOURCE S8 §3.1]
- Two results that sidestep Gödel for a prover's own kernel: "I ⊢HOL Con(HOL) for a new axiom I about sets" and "⊢HOL Con(HOL − {∞})", that is, add strength or verify a weaker fragment. [SOURCE S12 §"On self-verification"]
- Candle is a HOL Light clone verified in HOL4 with "an end-to-end correctness theorem that guarantees the soundness of the entire system down to the machine code"; its REPL "executes the CakeML compiler internally". [SOURCE S13 abstract] The verifying logic and the verified logic are both HOL; what details make that non-circular I did not read. [UNKNOWN]
- **Lesson.** Harrison's two routes are the owner's two options seen from the logic side: a hypothesis (H, MetaCoq's SN), or a weaker object. For Sleight the second would mean an evaluator, at some level, for programs of strictly lower levels. Whether Sleight's levels support that: [UNKNOWN]. [INFERENCE: it rests on DESIGN.md §17–§18 (a function "may call a function of a strictly lower level" [QUOTE DESIGN.md:688-689]) and on the README's session-written strength claims (README.md:113-119), neither of which I checked against an attempt.]

### 2.6 Outer loops and partiality monads in total languages

- **Interaction trees.** "ITrees ... represent nonterminating computations without needing to resort to step-indexed approaches such as fuel." [SOURCE S39 §1] The only code outside Coq is the loop: `let rec run t = match observe t with | RetF r -> r | TauF t -> run t | VisF (Input, k) -> ...`, and "All but the outermost run driver are extracted from Coq". [SOURCE S39 §6, Fig. 19] Programs are compared "up to Tau", which "lets us remove any finite number of Tau's ... while infinite Tau's must be matched on both sides (i.e., this equivalence is termination sensitive)". [SOURCE S39 §2.2]
- **Partiality monad.** Semantics "as total, computable functions (total definitional interpreters)" into `A⊥ = νX. A ⊎ X`, "classically equivalent to the relational semantics". [SOURCE S41 abstract, §1] This needs coinductive types.
- **Petrol plus an outside agent.** "invoke petrol with ? as the quantity of fuel. We are free to refine the ? with suc ? and resume evaluation repeatedly for as long as we are willing to wait". [SOURCE S11 §5]
- [RECALL] Brady's book "Type-Driven Development with Idris", chapter 11, runs total, productive processes with `data Fuel = Dry | More (Lazy Fuel)` and one non-total definition `forever = More forever`. Same knot as Agda Core's.
- **Lesson.** A Sleight `Program` whose `Continue` steps a machine once is an interaction tree whose `Tau` is "one more driver iteration" and whose `Vis` is a `Request`. [INFERENCE from DESIGN.md:1972-1981 and S39.] The agreement statement for such a process is then per step plus "eventually", never a function from program to result; and the number of driver iterations must be invisible in it, as `Tau` counts are. Whether Sleight can state the "infinite Tau" half without coinduction: [UNKNOWN].

---

## 3. Verified compilers that bootstrap themselves

### 3.1 CakeML

- **Specified.** Source semantics as a clocked functional big-step interpreter: "These interpreter functions use a clock, which acts as fuel for the computation, to ensure that they terminate for all inputs. A special uncatchable timeout exception is raised if the clock runs out." [SOURCE S16 §2.2] The clock is decremented only where size does not decrease: "the clock should only be decremented on recursive function calls for which the currently evaluated expressions does not decrease in size". [SOURCE S15 §2.3] In the current source it is checked at function application, at `eval`, and at forcing a thunk. [SOURCE S18 evaluateScript.sml lines 96-130]
- **How the clock leaves the theorem.** Observable behaviour quantifies it: "If the evaluate function reaches a result for some clock value, then the program has terminating behaviour ... If the evaluate function hits a timeout for all clock values, then it has diverging behaviour and returns the least upper bound of the resulting partial FFI traces". [SOURCE S16 §2.2] The needed lemma: "if a program does not time out for a given clock, then every increment to the clock gives the same result". [SOURCE S15 §3.4]
- **Divergence preservation.** "decrementing the clock only on recursive calls in the functional big-step semantics gives us divergence preservation for free in compilation steps that do not cause additional clock ticks." [SOURCE S15 §3.4] In 2014: "It allows us to do all of our compiler proofs by induction and in the direction of compilation." [SOURCE S14 §1]
- **Top-level theorem.** See F3. Behaviours are `Diverge (io_event stream) | Terminate outcome (io_event list) | Fail`, with `outcome = Success | Resource_limit_hit | FFI_outcome final_event`. [SOURCE S16 §2.2] "a type-correct CakeML program never includes Fail in its semantics." [SOURCE S16 footnote 2]
- **FFI as an oracle.** `Type oracle_function = :'ffi -> word8 list -> word8 list -> 'ffi oracle_result`, `ffi_state = <| oracle; ffi_state; io_events |>`, and `call_FFI` appends an `IO_event` to the trace. [SOURCE S18 ffiScript.sml] "The FFI state, ffi, includes an oracle specifying how foreign function calls behave." [SOURCE S16 §2.3]
- **Type inference.** "inferencer soundness shows that any program with an inferred type has a valid typing derivation in the type system while inferencer completeness shows that any type that can be derived in the type system for a program is generalised by the inferred type." [SOURCE S17 §5] The principal-type check had to be switchable: "The inferencer completeness theorem relies on principal types; however, the induction in the type soundness proof does not go through with the principal typing check present. Therefore, we prove type soundness with u being false". [SOURCE S17 §6.2]
- **Bootstrapping in the logic.** "an application of the compiler function with the compiler's source implementation as argument is evaluated via logical inference. This bootstrapping method produces a machine code implementation of the compiler and also proves a theorem stating functional correctness of that machine code. Bootstrapping removes the need to trust an unverified code generation process. By contrast, CompCert first relies on Coq's extraction mechanism to produce OCaml, and then relies on the OCaml compiler". [SOURCE S16 §11]
- **The compiler's own totality.** The compiler program is proved to terminate on every input: "running main_64_prog in CakeML's source semantics from an appropriate initial state always terminates successfully with a list of I/O events." [SOURCE S16 §11.1] This is possible without any hypothesis because CakeML's compiler never runs user code. [INFERENCE: the compiler is a HOL function translated to CakeML (S16 §11.1); nothing in the passages I read has it evaluate the program being compiled.]
- **Trusted, as far as the passages I read say.** The theorem is relative to a machine semantics (`machine_sem`) and an `installed` predicate whose assumptions are met by "(unverified) wrapper assembly"; and "compiler_ui is not verified in the same sense ... Verifying it would require verifying the small assembly wrapper". [SOURCE S16 §10.1, §10.3] That HOL4 itself is trusted is [INFERENCE]; I did not find the paper's own list.
- **Lessons for Sleight.** (1) The spec-as-classification of source text (F3) is the template for goal (4). (2) The clock technique transfers only for the part that Sleight can state constructively: "halts with v" as "there is a clock value"; the classical `semantics` function does not transfer (F5). (3) Sleight's compiler differs from CakeML's in the one way that matters for totality: it runs user code at compile time ("Such a form runs as soon as it has been elaborated" [QUOTE DESIGN.md:1179-1180]), so CakeML's unconditional compiler-termination theorem has no analogue and MetaCoq's conditional one applies. (4) The oracle is how the spec can "run the models" of externs and of `World` requests while leaving the environment abstract (handoff section B, last sentence). [INFERENCE from the sources above.]

### 3.2 CompCert

- **Notion of correctness.** "We model the compiler as a total function Comp from source programs to either compiled code ... or a compile-time error". The property proved: "∀S, C, B ∉ Wrong, Comp(S) = OK(C) ∧ S ⇓ B ⟹ C ⇓ B", sufficient "provided the target language of the compiler has deterministic semantics". "Whether the compiler succeeds to compile the source programs of interest is not a correctness issue, but a quality of implementation issue". [SOURCE S19 §2.1–2.4]
- **Forward plus determinism gives backward.** `Lemma forward_to_backward_simulation: forall L1 L2, forward_simulation L1 L2 -> receptive L1 -> determinate L2 -> backward_simulation L1 L2.` [SOURCE S20 common/Smallstep.v] The final theorem: `Theorem transf_c_program_correct: forall p tp, transf_c_program p = OK tp -> backward_simulation (Csem.semantics p) (Asm.semantics tp).` [SOURCE S20 driver/Compiler.v]
- **Unspecified evaluation order.** In 2009 the source language avoided the issue: "all Clight expressions always terminate and are pure ... The first motivation for this design decision is to ensure determinism of evaluation. The C standard leaves evaluation order within expressions partially unspecified." [SOURCE S21 §2.2] Current CompCert C has a nondeterministic semantics ("In accordance with C's nondeterministic semantics, we allow reduction both to the left and to the right of a binary operator" [SOURCE S20 Csem.v]) and a chosen strategy ("It evaluates effectful subexpressions first, in leftmost-innermost order, then finishes with the evaluation of the remaining simple expression" [SOURCE S20 Cstrategy.v]) linked by `Theorem strategy_simulation: forall p, backward_simulation (Csem.semantics p) (semantics p).` [SOURCE S20 Cstrategy.v] The proof structure is stated in the file: "Forward simulations from [Cstrategy] to [Asm] ... Backward simulations for the same languages (derived from the forward simulation, using receptiveness of the source language and determinacy of [Asm]). Backward simulation from [Csem] to [Asm] (composition of two backward simulations)." [SOURCE S20 driver/Compiler.v]
- **The cost of nondeterminism.** "expressions can go wrong according to one reduction order while being defined according to another ... Since our compiler is going to pick one particular evaluation order, we must make sure that all orders are safe". [SOURCE S20 Csem.v] `Definition safe (s: Csem.state) : Prop := forall s', star Csem.step ge s E0 s' -> (exists r, final_state s' r) \/ (exists t, exists s'', Csem.step ge s' t s'').` [SOURCE S20 Cstrategy.v]
- **Executable form of a nondeterministic spec.** `do_step (w: world) (s: state) : list transition` returns all possible steps, with `do_step_sound` and `do_step_complete` against the relation `Csem.step`. [SOURCE S20 cfrontend/Cexec.v]
- **Memory.** "Memory is modeled as a collection of disjoint blocks, each block being accessed through byte offsets; pointer values are pairs of a block identifier and a byte offset." [SOURCE S19 §3.1] Allocation is deterministic: `alloc` returns `m.(nextblock)` and sets the next to `Pos.succ m.(nextblock)`. [SOURCE S20 common/Memory.v] States at different stages are related by an injection `meminj : Type := block -> option (block * Z)` with `mi_no_overlap`. [SOURCE S20 Memory.v, Values.v] Pointer comparison is partial: across blocks only `Ceq`/`Cne` are defined (`cmp_different_blocks`), and only when both pointers are valid. [SOURCE S20 Values.v] That partiality is what lets comparison survive an injection: `Lemma cmpu_bool_inject: ... Val.cmpu_bool valid_ptr1 c v1 v2 = Some b -> Val.cmpu_bool valid_ptr2 c v1' v2' = Some b`, under the hypothesis `valid_different_ptrs_inj` that distinct valid pointers stay distinct. [SOURCE S20 Values.v]
- **Fuel in CompCert.** The verified parser: "the interpreter requires an integer argument n, which we refer to as the fuel"; completeness is "there exists n0 such that for all ω and for all n ≥ n0 ..."; and "We have not proved that our parser terminates. Completeness (Theorem 3) implies that it terminates when supplied with a valid input. However, there remains a possibility that it might diverge when faced with an invalid input." [SOURCE S22 §2.5, §3.3, §7] In the shipped code: `let log_fuel = Camlcoq.Nat.of_int 50`. [SOURCE S20 cparser/Parse.ml]
- **Trusted.** "1. The formal semantics for the source (Clight) and target (PPC) languages. 2. The parts of the compiler that are not verified yet: the CIL-based parser, the assembler, and the linker. 3. The compilation chain used to produce the executable for the compiler: Coq's extraction facility and the Caml compiler and run-time system. 4. The Coq proof assistant itself." [SOURCE S19 §5; the list is of 2009]
- **Lessons for Sleight.** (1) If the spec's order is fixed and the output's semantics is deterministic, forward simulation is enough. (2) If order is left open, expect three extra things: a relational spec, a "safe under all orders" precondition or theorem, and a refinement-shaped final statement. (3) The 2012 parser is a caution for goal (4): sound, safe, and complete, and still no theorem that invalid input is rejected in finite time. (4) Abstract block names with a deterministic allocator, plus "equal up to an injection" in the compiler proof, is the long-standing way to have observable pointer equality without concrete addresses; it matches the handoff's address model B except that B lets an allocating step "take any address never taken before". [INFERENCE from the sources above and handoff section B.]

### 3.3 CertiCoq and Œuf

- **CertiCoq.** "we can restrict our reasoning to terminating programs since Coq is strongly normalizing. This way we avoid backward simulations (forward simulation proofs are much simpler) and avoid proving preservation of divergence." [SOURCE S23 "Principle 2"; a 2-page abstract, I did not read later CertiCoq papers]
- **Œuf.** A verified compiler "from a subset of Gallina to assembly" that keeps the front end out of the TCB "by reflecting Gallina programs to Œuf source and automatically ensuring equivalence using computational denotation." The subset is "ML-like ... free of dependent types", with recursion through eliminators. [SOURCE S24 abstract, §1, §3]
- **Lesson.** Every Sleight function is total, so for function bodies the CertiCoq principle applies: prove agreement over terminating evaluations, in the direction of compilation, with no divergence case; divergence exists only in the driver's loop. Œuf's "denote the deep embedding back into the host and compare" is a typed interpreter for a *weaker* language than its host, which is the stratified way round the barrier of F2. [INFERENCE from S23, S24.]

### 3.4 Verified extraction from Coq to OCaml (Forster, Sozeau, Tabareau, PLDI 2024)

I could not fetch the paper (ACM 403, HAL bot wall). What follows is from the abstract, the
repository README, and the Coq sources on `main`.

- **Target.** "Since OCaml does not have a formal specification, we make use of the Malfunction project specifying the semantics of the intermediate language of the OCaml compiler." [SOURCE S25 abstract] "we ... rely on the Malfunction and OCaml compilers to obtain `.cmx` files". [SOURCE S25 README]
- **What is modelled.** An inductive big-step relation `eval (locals) : heap -> t -> heap -> value -> Prop` over an *abstract* heap: `Class Heap := { heapGen : forall (value : Type), Type; fresh : forall {value : Type}, heapGen value -> pointer -> heapGen value -> Prop; deref : ...; update : ... }`, with `pointer` an abstract type. Application evaluates the function, then the argument. Ill-formed cases produce a `fail` value. [SOURCE S25 theories/SemanticsSpec.v]
- **Main theorem (as in the source today).** For an axiom-free, well-formed environment and a closed term `t` of first-order inductive type that reduces to an irreducible `v`, under `Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0` and further side conditions (eta-expanded terms, inductives without parameters, a relation between the erased and the Malfunction environments): `forall h, eval Σ' empty_locals h (compile_malfunction_pipeline expΣ expt typing).2 h (compile_value_mf Σ v)`. The heap is quantified and returned unchanged. [SOURCE S25 theories/PipelineCorrect.v, section `malfunction_pipeline_theorem_red`]
- **Interoperation.** "we prove that extracted programs of first-order data type are correct and can safely interoperate, whereas for higher-order programs already simple interoperations can lead to incorrect behaviour and even outright segfaults." [SOURCE S25 abstract] In the source this is a realizability statement, `realize_term ... (Arrow (Adt kn ind []) (Adt kn ind' [])) (compile_pipeline Σ f ...)`. [SOURCE S25 theories/Firstorder.v, `interoperability_firstorder_function`]
- **Assumed in the source.** `Axiom assume_can_be_extracted`, `Axiom trust_coq_kernel`, `Axiom unsupported_strings`, `unsupported_arrays`, `unsupported_lazy`, `unsupported_force`, and `Parameter Normalisation`. [SOURCE S25 Pipeline.v, CompileCorrect.v, Firstorder.v] "the cofixpoint to lazy/force translations is not verified yet." [SOURCE S25 README]
- **`Obj.magic`.** Coq's standard extraction inserts it: Letouzey's implemented extraction is described as "inserting Obj.magic to embed untyped terms". [SOURCE S1 §4] The standard extraction can also produce ill-typed OCaml: "our first attempt to extract the typechecker was producing an ill-typed term which shows that the current extraction mechanism is not correct in general." [SOURCE S1 §3.6] [RECALL] The PLDI paper's stated reason for targeting Malfunction is that it is untyped, so no `Obj.magic` and no OCaml typing argument are needed; I could not check the wording.
- **Lessons for Sleight.** (1) "End the proof at a small modelled subset of OCaml and print it with a printer that makes no decisions" (handoff section C) is this design, with the difference that the precedent chose the compiler's untyped intermediate language over OCaml source. (2) What stays trusted is the correspondence between the model and what the OCaml compiler does. (3) An abstract `Heap` class with a `fresh` *relation* and a theorem quantified over all heaps is a worked instance of the handoff's address model B. (4) Even this project proves agreement only for first-order results. [INFERENCE from S25.]

### 3.5 PureCake

- "a mechanically-verified compiler for PureLang, a lazy, purely functional programming language with monadic effects", ending at CakeML. [SOURCE S27 abstract]
- Semantics as interaction trees, adapted to HOL: `itree E A R ::= Ret (r : R) | Div | Vis (e : E) (k : A → itree E A R)`; "To recover the ability to express silent divergence, we add a nullary Div constructor". [SOURCE S27 §3.3]
- "CakeML's functional big-step semantics uses an oracle to model FFI behaviour where PureLang's interaction tree semantics models all possible FFI behaviours. We verify an interaction tree semantics for CakeML". [SOURCE S27 §2]
- **Lesson.** Two interchangeable ways to model the environment: an oracle parameter, or a tree that branches on every possible answer. Sleight's `Program` with `Request`s is already the tree. The `Div` constructor is a classical device (a function that decides divergence) and does not transfer. [INFERENCE from S27 and F5.]

### 3.6 Cogent

- **Specified.** Two big-step semantics for one language: "the functional value semantics, which is suitable for equational reasoning ... The second, the update semantics, is more imperative in flavour, where values may take the form of pointers to a mutable store." [SOURCE S28 §4.1]
- **Proved (Isabelle/HOL, machine-checked).** "Each of the theorems presented in this section are formalised and machine-checked in Isabelle/HOL". Theorem 4.3: if a typed expression evaluates to `u` in the update semantics from an environment corresponding to `V`, then it evaluates to some `v` under `V` in the value semantics, "and there exists a footprint that results from the original footprint such that u corresponds to v." [SOURCE S28 §4, §4.2.3]
- **Where uniqueness sits.** Not in either semantics. It is in the relation between them: a plain abstraction function "is not preserved by evaluation in the presence of aliasing of mutable data ... Therefore, the refinement relation must additionally encode the uniqueness property ensured by our type system, which rules out not just direct aliasing ... but also internal aliasing". The relation is typed and carries a footprint of read-only and writable pointers. [SOURCE S28 §4.2, §4.2.1]
- **Frame relation.** For any pointer `p`: "Inertia: Any value outside the footprint is unaffected ... Leak freedom: Any value removed from the footprint must be freed ... Fresh allocation: Any value added to the footprint must not overwrite anything else". [SOURCE S28 Definition 4.1]
- **Foreign functions.** Each has a pure model and an updating model, and the user owes, per function: if the update version evaluates then the value version does; the results correspond; and the frame relation holds. [SOURCE S28 §4.2.4]
- **Certifying, not certified.** "The refinement theorem connecting the two semantics allows the compiler to produce a proof via translation validation certifying the correctness of the generated C code". Costs: typing certificates were at first "gigabyte-sized", then "a few megabytes"; the C-side tools "take anywhere from 12 to 32 CPU hours". [SOURCE S28 abstract, §6.1] The compiler must also emit hints, because "the typing rules we have presented are not algorithmic", for instance "a table of hints that informs the proof synthesis tactic on how each context is split". [SOURCE S28 §5.2]
- **Scope.** "Cogent is a restricted language of total functions"; "the (purposeful) lack of built-in iteration or recursion". "The refinement theorem between our two semantic interpretations ... is only possible because Cogent is a significantly restricted language, disallowing aliasing of writable pointers." [SOURCE S28 §1, §4.2.4]
- **Lessons for Sleight.** (1) "Pure or heap machine" need not be either-or, but having both costs a refinement proof whose invariant is the sole-reference property with a footprint, proved once for the language. (2) The direction that makes the heap run *the* run is update ⇒ value. (3) Cogent's footprint has a read-only part because of its `!` (borrow); Sleight's `share` and "a `unique` binder may alias a live `many` one" where nothing can mutate [QUOTE DESIGN.md:514-516, §13] would need the analogous split. (4) Cogent's obligations on foreign functions are the precise form of DESIGN.md §42's "must agree with its model". [INFERENCE from S28 and the two DESIGN.md quotes.]

---

## 4. Uniqueness and linearity with in-place update: theorem, or part of the definition?

What DESIGN.md asserts: "Where a value can be mutated in place, either through the cell a
destructure hands back (§37) or by an extern's own in-place operation (§43), a `unique` binder on
that value is the only reference to it. Where nothing can mutate the value, the sole-reference
property is neither promised nor needed". [QUOTE DESIGN.md:510-515, §13]

| System | Where "sole reference" lives | Mechanized? | Tag |
|---|---|---|---|
| Cogent | A **theorem**: an invariant inside the typed refinement relation between the two semantics; neither semantics mentions it | Yes, Isabelle/HOL | [SOURCE S28 §4.2] |
| Linear Haskell | Partly **in the semantics**: in the pure, type-annotated semantics "Reduction gets stuck if a 1-variable is used more than once", and progress shows it never does. Then "the pure semantics and the semantics with mutation are observationally equivalent" (Theorem 3.9), by bisimulation, citing Cogent's authors for the technique | No mechanization is mentioned [INFERENCE from absence in the text] | [SOURCE S29 §3.4, App. A] |
| FP² | A **theorem** with the other direction: if the pure evaluation reaches `v` then the store evaluation reaches a store representing `v`, given that the owned store is *linear*; "On linear stores mutation is safe" | Paper proof (Appendix B) | [SOURCE S33 §2.3, Theorem 1] |
| Entente Cordiale | A **theorem** about an instrumented heap with reference counts: "all heap references have only one reference to them at the end of execution" (Theorem 5); "the heap semantics incorporates some typing information in order to ease the theorem statements and proofs" | Not stated in the passages I read [UNKNOWN] | [SOURCE S34 §3.4–3.5] |
| L3 | Neither: pointers are freely duplicable; a separate linear *capability* owns the contents: "a pointer to the object, which can be freely duplicated, and a capability for accessing the contents ... capabilities can be erased; at run time, they play no computationally significant role." Soundness by a semantic model "closely related to models for spatial logics" | Paper proof | [SOURCE S30 §1–2] |
| Perceus, Counting Immutable Beans | A **run-time test**: reuse happens under `if (is-unique(x))`; the theorems are that the reference-counted heap semantics agrees with the standard one (Theorem 1) and leaves no garbage (Theorem 2) | Paper proof | [SOURCE S31 §2.4, §3; S32 abstract] |
| RustBelt | A **theorem** via a semantic model: types are interpreted as ownership predicates in a separation logic; "fundamental theorem" plus "adequacy". [RECALL] The operational semantics itself is an ordinary heap machine | "machine-checked" per the abstract; in Coq is [RECALL] | [SOURCE S35 abstract, §1] |
| Stacked Borrows | **Part of the definition**: "an operational semantics for memory accesses in Rust. Stacked Borrows defines an aliasing discipline and declares programs violating it to have undefined behavior" | Yes, Coq | [SOURCE S36 abstract] |
| Oxide | Syntactic: "proved sound using progress and preservation" | Not stated in the abstract [UNKNOWN] | [SOURCE S37 abstract] |
| Clean | [RECALL] Uniqueness typing is defined over graph rewriting; the classic papers are Barendsen and Smetsers. Cogent's authors say Clean "does not prove, on paper nor in a machine-checked proof script, the semantic coincidence that results from the type system" | | [SOURCE S28 §4 for the quoted remark] |
| ATS | [RECALL] Linear "views" such as `T @ l` are proofs threaded through pointer operations and erased; the pointer itself is a plain address. The same split as L3's | | |

Other facts that bear on the choice:
- "linear types provide a restriction on what can be done with a value 'in the future' whilst uniqueness types provide a guarantee about what has been done with a value 'in the past'." [SOURCE S34 §2]
- Hofmann did the two-semantics coincidence first, by hand, for a language without heap objects, according to Cogent's authors. [SOURCE S28 §4]
- DESIGN.md separates location from uniqueness with `at` and slots, and says "Nothing relies on two slots being distinct." [QUOTE DESIGN.md:1809-1810, §38] L3 and ATS are the precedents for that separation. [INFERENCE: I did not study §35–§41 closely.]

**Lesson for Sleight.** Three coherent positions exist, and the literature has each:
1. *Heap machine is the spec; sole reference is a theorem about it.* (Cogent, FP², Entente, RustBelt.) The theorem is needed to give a pure reading or to justify DESIGN.md §13's sentence. It is not needed to state or prove that the compiler's output run matches the spec's run.
2. *Heap machine is the spec; mutating through a non-sole reference is a stuck step.* (Stacked Borrows; Linear Haskell's instrumented semantics.) Then §13's sentence is true by definition for runs that do not get stuck, and the burden moves to a progress theorem for accepted programs.
3. *Pure semantics is the spec; the heap machine is an implementation detail.* (Cogent's value semantics as the user-facing one.) The handoff says the owner voiced concern about a pure run and the session withdrew it (handoff item 7).
[INFERENCE: my classification; the handoff records that the owner "suspects the spec's run should be a mutating heap machine from the start", which is position 1 or 2.]

---

## 5. Fuel, clocks, and nontermination in a total metalanguage: is the fuel observable?

| Technique | Where the number lives | In the final theorem? | Needs | Tag |
|---|---|---|---|---|
| Clocked functional big-step (CakeML) | Spec only; decremented at non-structural calls | No: "evaluation terminates, if there exists some initial value of the clock for which the sem_t returns Rval. An evaluation is non-terminating if sem_t returns Rtimeout for all initial values of the clock." | Classical logic for the top-level case split; a monotonicity lemma | [SOURCE S15 §2.3, §3.4] |
| Same interpreter, run for testing | "by initialising the clock to a very large number" | Yes for that run, since a timeout remains possible (my reading) | Nothing | [SOURCE S15 §1] for the quotation |
| Fuel in a verified implementation (CompCert parser) | Implementation argument, 2^50 | Yes: "there exists n0 such that ... for all n ≥ n0"; out-of-fuel is a third result | Nothing | [SOURCE S22 §3.3; S20 Parse.ml] |
| Depth fuel (Lean4Lean) | Implementation constant 1000, charged only on non-decreasing calls | Would be: failure on exhaustion is an error the checker can return | Nothing | [SOURCE S5 §3.2.1] |
| Fuel plus an infinite value from outside (Agda Core; [RECALL] Idris `forever`) | Implementation argument, instantiated by `fl = More fl` | Proofs speak of finite fuel; the running program is outside them | A lazy host language | [SOURCE S6] |
| Fuel-indexed type soundness (Amin and Rompf) | Universally quantified in the theorem | Yes, as "for all n"; the conclusion is vacuous on `Timeout`: "if the interpreter returns a result that is not a timeout, then the result is a value" | Nothing | [SOURCE S42 §2.2] |
| Step-indexed logical relations | [RECALL] An index in the relation, quantified away by adequacy (Appel and McAllester 2001; Ahmed 2006). CakeML's clock doubles as the index | No | | [SOURCE S15 §1 for the last sentence] |
| Recursion on an accessibility or domain derivation (Bove–Capretta; MetaCoq) | Nowhere: "defined by structural recursion on the proof that the input values satisfy this predicate"; "If we suppress the proofs of the accessibility predicate, we get almost exactly the original algorithms" | No fuel; the theorem carries the hypothesis instead | A halting witness for each call; erasure of it | [SOURCE S40 abstract and overview; S2 §5.1] |
| Coinductive big-step (Leroy and Grall) | Nowhere | No fuel; two relations, evaluation and divergence | Coinduction; excluded middle for "one or the other" | [SOURCE S38] |
| Partiality (Delay) monad | Nowhere; a `later` constructor marks each delay | No; [RECALL] results are compared up to weak bisimilarity, which ignores finite delays | Coinductive types | [SOURCE S41 abstract, §1; S11 §6] for the monad |
| Interaction trees plus a driver | Nowhere; `Tau` steps | No, up to `eutt` | Coinduction; an untrusted loop | [SOURCE S39 §2, §6] |
| Petrol re-run by an outside agent with more each time | Chosen outside the language | No, if results are monotone in fuel: "petrol f n s is monotone in n" | The outer loop | [SOURCE S11 §5] |

"Fuel doubling" or iterative deepening: I found no paper that names and proves it as a technique.
[UNKNOWN] It is the last row made concrete: run a clocked total evaluator with fuel 1, 2, 4, ...
from an outer loop; the monotonicity lemma of S15 §3.4 is what makes the answer independent of the
schedule. In Sleight the outer loop would be the `Program` driver. [INFERENCE]

**Lesson for Sleight.** For owner goal (3), the choices that leave *no* number anywhere are the
halting-derivation route (needs H as an erased argument at each evaluator entry) and the
driver-loop route (needs no argument to run; H appears only in the theorem that the loop reaches
`Exit`). They differ in what `compile` *is*: under the first it is a total function that cannot be
called without H; under the second it is a process, and "accepted or rejected" becomes "the process
eventually exits with a verdict", a relational statement. CakeML's route (clock in the spec only) is
compatible with either and removes fuel from the *statement* of what a compile-time run computes.
[INFERENCE from the table, F1, F2, and F5.]

---

## 6. Certifying versus certified

- **Definitions.** A verified compiler: `∀S, C, Comp(S) = OK(C) ⟹ S ≈ C`. A verified validator: `∀S, C, Validate(S, C) = true ⟹ S ≈ C`, and "The combination of a verified validator Validate with an unverified compiler Comp does provide formal guarantees as strong as those provided by a verified compiler." A certifying compiler "either fails or returns both a compiled code C and a proof π". [SOURCE S19 §2.2]
- **The asymmetry.** "The property S ≈ C being undecidable in general, validators are necessarily incomplete and should reply false if they cannot establish S ≈ C." [SOURCE S19 §2.2] Every guarantee above is conditional on success.
- **In practice.** CompCert uses validators for register allocation and some optimizations [SOURCE S19 §3.2, §4.2]; CakeML's register allocation goes through a checker "designed to evaluate efficiently in the logic" [SOURCE S16 §7.2.2]; Œuf validates its reflection step [SOURCE S24]; Cogent certifies each compilation [SOURCE S28]; F* was given "a self-certifying type-checker ... whose metatheory is formalised in Coq" by Strub et al. [SOURCE S1 §5, as described there; the F* paper itself is RECALL].
- [RECALL] The de Bruijn criterion (Barendregt and Wiedijk, 2005): a proof assistant's results should be checkable by a small independent program. Coq and Lean elaborate into a core language that the kernel re-checks. Dedukti takes proofs exported from other systems and re-checks them in the λΠ-calculus modulo rewriting.
- **Negative results done right.** PLFA: `synthesize : ∀ (Γ : Context) (M : Term⁺) → Dec (∃[ A ] Γ ⊢ M ↑ A)`; "The negative proof can be thought of as a semantically verified error message". The refutations need determinism lemmas, for example `uniq-↑ : Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B`, used to turn "the function's argument fails" into "the application has no type". [SOURCE S43] MetaCoq does the same at scale (§2.1), and its route to completeness went through an *equivalent bidirectional presentation* with "canonical typing derivations". [SOURCE S2 §1]

**What a kernel-rechecks-core design cannot give about rejected programs.** [INFERENCE from the
sources in this section]
1. The kernel sees only what the elaborator emits. If the elaborator stops with an error, there is nothing to check, so the design yields no statement that the source has no typing.
2. A source-level statement "rejected implies no derivation exists" needs either (a) a declarative typing relation on *source* programs and a completeness proof of the elaborator against it, which is verification of the elaborator after all; or (b) negative certificates, each a refutation the kernel can check, which exist only if the declarative system is deterministic enough to refute by cases (unique types, principal types, a fixed search order). CakeML had to add a principal-type condition to its rules for exactly this [SOURCE S17 §3.3].
3. A kernel also cannot certify that elaboration *terminates*; CompCert's parser is the example where soundness, safety, and completeness were all proved and termination on invalid input was not [SOURCE S22 §7].
4. If "rejected" is defined as "the elaborator reported an error", the totality theorem is true and says nothing; CompCert's remark about the always-failing compiler applies [SOURCE S19 §2.2].

---

## 7. Evaluation order and allocation in formal semantics of real languages

**Order.**
- OCaml: "The order in which the expressions expr, argument_1, ..., argument_n are evaluated is not specified." The manual says the like of tuples ("The evaluation order of the subexpressions is not specified"), records, and arrays, and `let ... and ...` evaluates its right-hand sides "in some unspecified order". [SOURCE S44 expr.etex]
- Malfunction: "Evaluation is eager: functions and arguments are evaluated before their bodies. The function is evaluated before the arguments, and arguments are evaluated left to right." Its contract for undefined behaviour: for any syntactically valid program, either the interpreter and compiler agree, or the interpreter reports undefined behaviour, or both fail to terminate. [SOURCE S26]
- CakeML: "the adoption of right-to-left evaluation order for application expressions ... This change was necessary to keep the BVL code that implements multi-argument function applications short and fast." [SOURCE S16 §4.2] In the source: `evaluate st env [App op es] = (case fix_clock st (evaluate st env (REVERSE es)) of ...`. [SOURCE S18 evaluateScript.sml]
- Standard ML: the state convention threads the store through a rule's premises, and "the left-to-right order of the hypotheses indicates the order of evaluation." [SOURCE S45 §6.7]
- C in CompCert: §3.2 above.
- An oracle keeps a nondeterministic-order semantics a *function*: "non_det_o which represents an infinite stream of decisions that determine the subexpression evaluation ordering", quantified existentially at the top; "a program can both terminate and diverge depending on evaluation order". [SOURCE S15 §4]
- [RECALL] Owens's "A sound semantics for OCaml light" (ESOP 2008) fixes an order (I believe right to left) for its fragment; I could not fetch it.

**Allocation and address equality.**
- Deterministic allocators in specs: CompCert's `nextblock` [SOURCE S20 Memory.v]; CakeML's `store_alloc v st = (st ++ [v], LENGTH st)` [SOURCE S18 semanticPrimitivesScript.sml].
- A nondeterministic `fresh` relation over an abstract pointer type: verified extraction's `Heap` class [SOURCE S25 SemanticsSpec.v].
- Observable equality on locations: CakeML `do_eq (Loc b1 l1) (Loc b2 l2) = (if b1 ∧ b2 then Eq_val (l1 = l2) else Eq_type_error)`. [SOURCE S18] CompCert: §3.2. OCaml: F9.
- Stating "the same up to renaming of addresses": CompCert's memory injections with `mi_no_overlap` and `cmpu_bool_inject` [SOURCE S20]; quantifying the theorem over all heaps [SOURCE S25 PipelineCorrect.v]; [RECALL] nominal techniques (Pitts and others) treat addresses as atoms and require every definition to be invariant under permutations of atoms, so results are determined up to renaming.
- What DESIGN.md fixes: "every value is one word, either an immediate or a pointer to a block" [QUOTE DESIGN.md:1461-1462, §33]; "two separately built cells with equal contents are `is`-equal and are two blocks" [QUOTE DESIGN.md:1697-1698, §36]; "address equality does not change when contents do" [QUOTE DESIGN.md:1701-1702, §36]; and `slot-eq` (F9).

**Lesson for Sleight.** [INFERENCE from the sources in this section and the handoff]
1. On the handoff's question A (fixed order or any order): among the formal semantics I checked, order is left open only for C, where the standard leaves it open, and in a teaching example in S15. CakeML, Malfunction, and Standard ML fix one. Fixing it lets the spec's run be a function and the agreement theorem an equation.
2. If slc emits OCaml *source*, a fixed Sleight order must be imposed by the emitted code, because OCaml promises none for applications, tuples, records, and arrays. A single `let pattern = expr_1 in expr` does sequence: the manual has `expr` "evaluated in the environment enriched by the bindings performed during matching". [SOURCE S44 expr.etex, "Local definitions"] Whether slc's output relies on OCaml's unspecified order anywhere: [UNKNOWN], I did not read slc.
3. A deterministic allocator in the spec plus "up to injection" in the proof, and an abstract `fresh` relation, are both workable. With `slot-eq` as §67 states it, the spec is nondeterministic at that point regardless, so the simpler deterministic-allocator spec does not buy a functional spec by itself.
4. Relying on OCaml's `==` for immutable values gives only the one-sided guarantee OCaml documents; that happens to be the shape §67 allows.

---

## 8. Design questions, precedents, and what they suggest

Every cell in the last column is `[INFERENCE]` from the sources named in the middle column.

| Design question for this project | Precedent(s) | What the precedent suggests |
|---|---|---|
| Can `compile` be proved total, and under what hypothesis? | MetaCoq: SN as a propositional, erased hypothesis used only for the reduction machine (S2, S3). Lean4Lean: gave up, fuel 1000 (S5). Harrison: stronger axiom or weaker object (S12) | H as an explicit parameter, consumed only where the evaluator loops; "halts on accepted code" suffices if evaluation follows elaboration; keep the rest of the agreement proof H-free |
| How does the running compiler obtain H? | MetaCoq: `Axiom fake_normalization` at the plugin (S3) | Either a postulate at the top, or a design where running needs no witness (driver loop) and H appears only in a theorem |
| Fuel-free evaluator: halting derivation, driver loop, or clock? | MetaCoq `Acc` recursion (S2, S3); interaction trees' driver (S39); Agda Core's step function with fuel and an infinite fuel value (S6); CakeML's clock in the spec only (S14–S16); McBride (S11) | Derivation: a total function, no number anywhere, needs a witness per call. Driver: a process, no witness to run, statement becomes relational and "up to silent steps". Clock in the spec only is compatible with both. Of the two completed projects, CakeML uses the clock for run-time semantics and MetaCoq uses the derivation for compile-time reduction |
| Where may fuel remain? | MetaCoq universe graph, bounded by set size (S2); Lean4Lean depth limit (S5); DESIGN.md §62's 10000 expansions | Fuel bounded by a size of the input, and limits that are part of the language's definition, are not the fuel the owner wants gone; say so explicitly |
| What makes "accepted or rejected" a real theorem? | CakeML Fig. 10 with parser and inferencer soundness and completeness (S16, S17, S14); PLFA `Dec` (S43); MetaCoq `typing_result_comp` (S3); CompCert's always-failing compiler (S19); CompCert's parser without termination on invalid input (S22) | Spec the verdict as a classification of source text; prove both directions or return a refutation; treat "never both" as part of the same theorem; expect the declarative rules to need determinism side conditions; name any outcome the theorem excludes, as `CompileError ⇒ true` does |
| Positive `Fails` relation or negation of typing? | MetaCoq and PLFA use `A -> False` (S3, S43); no precedent found for a separate positive relation [UNKNOWN] | Negation gives exclusivity for free; a positive relation needs a separate exclusivity lemma to mean "has no typing". Functions in Sleight carry levels and its logic is anticlassical (README.md:108-111), so which form is workable there is for a prototype to say |
| Spec's run: pure, heap machine, or both? | Cogent: both, with a mechanized refinement (S28); Linear Haskell: both, by bisimulation (S29); FP²: both (S33); CompCert, CakeML: heap machines only (S20, S18) | Heap machine as the spec is the norm in compiler verification; a pure second semantics is an add-on costing a language-wide proof whose invariant is sole reference plus framing |
| Is "`unique` means sole reference" a theorem or a definition? | Theorem: Cogent, FP², Entente, RustBelt. Definition: Stacked Borrows. Stuck-if-violated instrumented semantics: Linear Haskell. Run-time test: Perceus (S28, S33, S34, S35, S36, S29, S31) | Each is coherent; compiler agreement needs none of them when the spec is the heap machine; DESIGN.md §13 states the property, so the choice decides whether that sentence is proved, true by definition, or left as a claim |
| Is the capability the pointer? | L3: pointer and capability split, capability erased (S30); [RECALL] ATS views | Precedent for Sleight's `at`/slot separation; "sole reference" then means sole *capability*, and pointers may be copied |
| Evaluation order: fix or leave open? | CompCert C with `Cstrategy` and `safe` (S20); CakeML fixed right-to-left (S16, S18); Malfunction fixed (S26); SML fixed (S45); OCaml unspecified (S44); oracle technique (S15 §4) | Fixed order: functional spec, equality theorem, forward simulation. Open order: relational spec, safety under all orders, refinement theorem. If open, the oracle keeps the spec a function |
| Addresses and allocation | CompCert blocks, `nextblock`, injections, partial comparison (S20); CakeML list index (S18); verified extraction's abstract `Heap` with `fresh` (S25); OCaml `phys_equal` (S44) | Abstract names with either a deterministic allocator or a `fresh` relation; equality observations must be stable under the renaming used in the proof; one-sided equality (§67) is the easiest kind to keep stable |
| Crashes and resource limits | CakeML `extend_with_resource_limit` and the 2014 out-of-memory clause (S16, S14) | State output agreement as "behaviours ⊆ spec's behaviours, possibly cut short by a crash"; this is §31 formalized; accept that an always-crashing output satisfies it |
| Externs and the FFI: models or implementations? | CakeML oracle (S16, S18); Cogent's per-function obligations (S28 §4.2.4); verified extraction's listed axioms (S25) | The spec runs the models; each implementation is an explicit assumption shaped like the main theorem; list them as the trusted base |
| Where should the proof stop on the OCaml side? | Verified extraction: at Malfunction, first-order results only (S25, S26); CompCert: trusts extraction and OCaml (S19); CakeML: bootstraps to machine code in the logic (S16) | A small modelled core with a decision-free printer is the Malfunction design; choose constructs whose behaviour OCaml documents; the model-to-compiler gap stays trusted |
| Retrofit slc, a certified kernel behind its front end, or a new compiler? | Verified validators (S19); Cogent's certificates (S28); Œuf (S24); MetaCoq's from-scratch verified checker (S2); Lean4Lean's port-then-verify (S5) | A kernel or validator gives agreement for accepted programs at low cost and nothing for rejected ones; goal (4) needs a verified elaboration path or negative certificates; port-then-verify has so far produced conjectures where specify-and-prove produced completeness |
| Forward or backward simulation; divergence? | CertiCoq Principle 2 (S23); CompCert (S19, S20); CakeML's clock (S14, S15) | Total functions: forward, big-step, terminating runs only. Divergence arises only in the driver loop and is handled per step |
| Erasure correctness ("stripped mode") | MetaCoq Theorem 4.7 and the erasure relation (S1 §4.3) | Expect that the erasure function does not commute with evaluation on higher-order or type-level values, and that a relation extending it is needed; agreement on first-order observations is the reachable statement |
| A total evaluator for all of Sleight in Sleight? | Turner (S10); Brown and Palsberg (S8); Bauer (S9); McBride (S11) | No. Choose among: driver, halting witness, fuel, stratification |

---

## 9. The four papers most worth the owner's time

1. **Matthieu Sozeau, Yannick Forster, Meven Lennon-Bertrand, Jakob Botsch Nielsen, Nicolas Tabareau, and Théo Winterhalter. "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq." Journal of the ACM 72(1), January 2025.** https://doi.org/10.1145/3706056 (open copies: https://inria.hal.science/hal-04077552 and https://www.repository.cam.ac.uk/bitstreams/2306e91b-50a1-40c9-b1c7-3a05cce92bc4/download). Read §1, §5.1, and §6.1–6.3. The same project as this one for Coq: agreement with a spec, a halting hypothesis instead of fuel, completeness with refutations, erasure. [SOURCE S2 for content; venue and issue from S4; the PDF prints the fourth author as "JAKOB NIELSEN", and "Botsch" comes from the HAL record as a web search showed it]
2. **Yong Kiam Tan, Magnus O. Myreen, Ramana Kumar, Anthony Fox, Scott Owens, and Michael Norrish. "The verified CakeML compiler backend." Journal of Functional Programming 29, e2, 2019.** https://cakeml.org/jfp19.pdf. Read §2 and §10–§11: the semantics with a clock and an FFI oracle, the top-level theorem that classifies every input string, and bootstrapping. Companion, short: **Scott Owens, Magnus O. Myreen, Ramana Kumar, and Yong Kiam Tan. "Functional Big-Step Semantics." ESOP 2016.** https://cakeml.org/esop16.pdf. [SOURCE S16, S15 for content; volume and article number are RECALL]
3. **Liam O'Connor, Zilin Chen, Christine Rizkallah, Vincent Jackson, Sidney Amani, Gerwin Klein, Toby Murray, Thomas Sewell, and Gabriele Keller. "Cogent: uniqueness types and certifying compilation." Journal of Functional Programming 31, e25, 2021.** https://doi.org/10.1017/S095679682100023X. Read §4 only (about 12 pages): two semantics, the typed refinement relation, the frame relation, and the obligations on foreign code. [SOURCE S28]
4. **Conor McBride. "Turing-Completeness Totally Free." MPC 2015 (LNCS 9129).** https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf. 15 pages in the author's copy. General recursion as a description, run by fuel, by a coinductive monad, or under a Bove–Capretta domain predicate, in one framework; it states exactly what is and is not lost by totality. [SOURCE S11 for content; proceedings volume is RECALL]

If a fifth: **Xavier Leroy. "Formal verification of a realistic compiler." Communications of the ACM 52(7), 2009.** https://xavierleroy.org/publi/compcert-CACM.pdf, §2 only, for the vocabulary (verified, validated, certifying; which simulation suffices when). [SOURCE S19; volume and issue are RECALL]

---

## 10. Things I am least sure of

1. **The PLDI 2024 verified-extraction paper was not read.** §3.4 rests on the abstract, the README, and the `main` branch sources, which may differ from the paper. The `Obj.magic` rationale is `[RECALL]`.
2. **MetaCoq sources were read at branch `coq-8.20`.** The JACM paper describes an earlier version. I saw `fake_normalization` in the erasure plugin only; how the `MetaCoq SafeCheck` command discharges the hypothesis I did not check. [UNKNOWN]
3. **The JACM text is the Cambridge repository copy**, likely the accepted manuscript; section numbers may differ from the published version.
4. **I read passages, not papers.** For S13, S36, and S37 only the abstract. For S28 I read §1, §4, and parts of §5 and §6; for S33 only the statements of Theorems 1 and 2; for S20 and S18 only the definitions and theorem statements quoted.
5. **F5's transfer to Sleight is an inference.** The test shows that excluded middle quantified over all types is refutable in the reference implementation; it does not show that any particular "halts or does not" is refutable. What I claim is unprovability in general, on ordinary constructive grounds.
6. **Whether Sleight's levels give Turner's hierarchy** (an evaluator at one level for code of lower levels) is unexamined. It leans on the README's session-written strength claims.
7. **"No mechanization" for Linear Haskell** is inferred from the text not mentioning one.
8. **All `[RECALL]` items**: Clean, ATS, OCaml light, Dedukti, the de Bruijn criterion, the step-indexing originals, nominal techniques, the Idris book's `forever`, the F* self-certification paper, and the volume and page data in §9.
9. **CakeML's `do_eq` on closures** returns `Eq_val T` in today's `master`; I recall older versions differing. I did not use this fact.
10. **CompCert's memory-model papers were not read**; §3.2's memory claims are from today's sources, which postdate them.
11. **Sibling agents' files.** The `[RAN]` on `proto/A4/halts.sl` runs another agent's scratch file as I found it; it may change.
12. **I did not read all of DESIGN.md**, only the sections quoted (§13, §15, §17, §18, §20, §27, §31, §33 in part, §36 in part, §38, §42, §62, §67, §68, §70) and searches. Any sentence here of the form "DESIGN.md says" is a quotation with its line; I make no claim about what DESIGN.md is silent on, and the handoff's statement that it does not fix evaluation order among sub-expressions is the handoff's, not something I verified.

## Appendix. Could not fetch

- ACM DL copies of the PLDI 2024 and JACM papers (403); HAL copies (bot wall). The JACM paper was obtained from the Cambridge repository instead.
- MenhirLib's `Interpreter.v` on gitlab.inria.fr (bot wall); CompCert's `Parse.ml` and S22 cover the same facts.
- Owens, "A sound semantics for OCaml light" (403); ATS papers on bu.edu (404); de Vries et al., "Uniqueness Typing Simplified" (proxy 502); CompCert memory model v2 (404 and bot wall).
