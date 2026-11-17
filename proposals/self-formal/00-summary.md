# 00. Summary: formalizing Sleight in Sleight, and a compiler proved against it

Written by Claude agents overnight, while the owner was asleep. Everything here is a proposal or an
agent's reading; nothing is approved or decided (CLAUDE.md rules 1 and 11). It condenses the five
track and two spike files; evidence and full hedges are in the file and section cited, which is
right where the two differ; DESIGN.md is right over both.

Citations: `01 §3.6` is section 3.6 of `01-spec-shape.md`; `02` dynamic semantics, `03` fuel and
termination, `04` compiler route, `05` theorems, `06` spike: certified stepper, `07` spike: round
trip. After a file number, `rN` is its review note N, `r2.N` its second, `r3.N` its third, and
`r4.N` its fourth. `§n` alone is DESIGN.md. "Owner statement n" is item n of the brief's "Owner
decisions", an earlier session's paraphrases, not the owner's words; they and the goals the brief
lists beside them (such as "minimize fuel use") are the only owner positions reported. "Tested"
means run on the reference and, where stated, on slc.

## 1. The picture in one page

Each item is the tracks' recommendation, not a decision.

- **Spec shape.** Source bytes, a small total reader to `Raw` with positions, then three relations:
  a fact engine free of evaluation (§29: "The engine of §7 reads no stored value"), a run, and
  elaboration with run premises; a threaded store Σ (§65's macro world) and a scoped Γ, with which
  of the two holds run-position facts open; rejection a positive `Fails` (01 §1, §4.2, §4.3;
  decisions 1, 13, 19).
- **The run.** A small-step heap machine over post-erasure code (§27): `Imm n | Ptr a` words,
  abstract never-reused addresses compared only for equality, mutable blocks, a total step, one
  fixed order, `Nat` primitive, `slot-eq` from an oracle (02 §3; decisions 4, 5, 7, 8, 9).
- **Fuel.** If Sleight's functions terminate and its checking ends (SOUNDNESS.md's (T), (C), and
  (E), argued, not proved), no hypothesis-free non-erased Sleight `compile` on source text is
  faithful on every source (key finding 2; partly untested). Fuel either stays internal, never
  showing in a result, or the unbounded part moves into the driver's `Program` loop, fuel-free in
  prototypes; mechanisms differ by track (decisions 18, 18a).
- **Theorems.** Intrinsic, since a type holds no call (§9): T1/T2 accepted ⇒ `Elab`, rejected ⇒
  `Fails`; T3 never both, per oracle; T4 every source accepted or rejected (owner statement 3),
  relative to a halting hypothesis H; T5 compile-time values match the spec run; T6 output refines
  the spec. Uniform H and stripped-run safety are expected to stay meta-theorems (05 §3, §7, r4.4;
  decisions 13, 14). Two toy spikes run this pattern fuel-free on both implementations, with partial
  correctness only and not Sleight's machine (key findings 16, 17).
- **Route and output end.** A new spec-first compiler of deriving functions beside the relations, in
  `mini/`'s shape, reusing slc's proved libraries, slc kept for differential testing (04 "R3"; 03
  frames its fuel work around slc). Prove to the post-erasure IR first, arguments atoms by type;
  later model slc's untyped OCaml subset and re-parse its output; `native-compute` at the output
  end's trust (04 Q1, Q3, Q4; decisions 17, 20, 21).

## 2. Key findings

1. **Elaboration reads run results, so it cannot be a typing relation separate from the run**: head
   dispatch reads a stored value (§6), `comptime-match` too (§28), and a run-position form runs
   before "the code after it is checked" (§27); `prove-literal-lt`, `unary`, macros, and
   `native-compute` run code (01 §3.1). So a kernel behind slc's front end must re-run run-position
   forms or check a run-length trace (04 Q1 "R2"), and `mini/` never meets the §29 round trip (04
   §2.4; 01 §3.10). That the run needs only the fact engine, scope, and Σ (no cycle) is an
   unverified reading of §65 (01 §3.2).
2. **The diagonal.** Tested mechanism: a macro `read-file`s its own file, runs a stand-in compiler,
   and expands to `compile-error` exactly when it accepts (`proto/fuel/diagonal.sl`, both
   implementations; 03 F6), inside a macro's output or a `comptime-match`, since `compile-error`
   fires in erased code too (§4; 03 r1). Reasoning: a non-erased `compile : Src -> Verdict` with no
   further evidence, faithful on every source, is impossible if Sleight's functions terminate and
   its checking ends (SOUNDNESS.md's (T), (C), and (E), (E) since §27 strips erased positions;
   argued, not proved; 03 §1, F6, r3.1). SOUNDNESS.md states these "about any program the checker
   accepts", and the unit Q may be rejected; 03 reads part 5's measure on activations of checked
   functions, and part 6's argument for (C), as covering Q's run anyway (03 F6, r4.1). The answer of
   the spec's run of `compile` on Q is taken to be determined by Q; Q fixes its flags (r3.3); with
   `slot-eq`, apply it to an all-`ENone` copy, if "faithful" means every run §67 permits agrees
   (r2.3, r3.4). It does **not** refute owner statement 4(ii) as mathematics, nor a `compile` taking
   erased evidence of H for its one source, though, if Sleight is sound, no Q can produce that
   evidence for itself; code outside Q may (r3.5). It suggests (untested, assuming soundness) that H
   for all sources, in a form a function can recurse on such as erased step counts, is not provable
   inside Sleight (03 F6, F7, r4.2). slc does not escape: its compile is one `Program` step, total
   through its fuel (03 F2, F3), its `World` blocking only the literal construction (03's reading,
   r2.1). 05 §4.3's version, through `read-file` in a macro, needs T1 to T4, determinism through T3,
   not T5, and, T1 to T3 being erased derivations, soundness of the logic; T3 holds per oracle, so
   with `slot-eq` it too uses the `ENone` copy (05 §1, r4.2, r4.3); a quine (unwritten) only for a
   run-position variant (05 r2.1, r2.2).
3. **Theorems must be intrinsic.** §9: "The elaborated form of a type never contains a function
   call" (tested). A toy checker returning its verdict with an erased `Elab` or `Fails` and an
   erased exclusivity lemma passes `--goal proved` (05 F1 to F3).
4. **Fuel-free shapes exist, with limits.** A total step looped by the driver runs with no fuel (02
   §2.6; 03 F5; 05 F6); under `--eval-fuel 1000` a 93025-step computation finishes as `Program`
   steps and runs out as one call, on both (03 F5). Recursion on an erased `Halts` is accepted, but
   a caller must supply it, per input or, for a terminating toy step, for every input
   (`proto/review3/05_halts_uniform.sl`), the uniform one ruled out for a faithful compiler under
   key finding 2's premises (05 F4, r3.4). Tested limits: fixed-level continuation closures call one
   another only with a decreasing argument, such as an erased counter (03 F4.1; 06 F4.1); a closure
   with a packed level is applied only with a packed `Predates`, and is extended at its packed
   level, not, on 06's reading of §18, at one minted during the run (18c); a function cannot iterate
   `Program` steps (03 F4.2); every function a step calls must be minted before the program's level
   (03 F4.3, 05 F6); a driven run's result reaches only its own later steps, never compile-time code
   or `qed` (05 F6, r2.5).
5. **`slot-eq` makes acceptance implementation-dependent.** §67: "which one a call answers may
   differ between runs". A run-position `comptime-match` on `ESome` is accepted by both; that
   `ENone` would reject is inferred, not observed (01 §3.8; 05 §2.2). Answers differ between
   implementations and modes, though no run-to-run variation was seen (02 §1, r4.4): `imm_eq.sl` is
   `ENone` interpreted, `ESome` in `--build` binaries with externs (02 §2.4, r2.5);
   `slot_eq_share.sl` is `ESome` only in slc's native build, which 04 attributes to ocamlopt's
   ability to share equal constants, and slc's `--byte` bootstrap would not see it (04 §2.5, r2.7);
   `const_share.sl` is `ENone` everywhere tried (02 second review).
6. **Evaluation order.** DESIGN.md fixes eagerness (§31), inner forms first in run position (§27),
   there, with §6, a head that is a form before the arguments (a reading), and, as 02 reads it,
   world effects through the unique `World`; in general it does not fix body statements, sibling
   arguments, `values` entries, or several §15 bindings (02 §2.2; rough edges 1 to 4). Gensym
   numbers expose elaboration order: both implementations elaborate a head that is a form (inferred,
   its number not printed), then expand every macro call among an application's arguments, left to
   right, then elaborate a head that is a name, then the arguments left to right
   (`proto/review3/gensym_*.sl`, `proto/review4/01_head_name_err.sl`; special forms' operands
   unchecked; 01 §3.6, r3.1, r4.2). At runtime the reference and `slc --interpret` run a head form
   before an argument form in a body (`proto/review3/head_arg_order.sl`, 02 §6, r3.1;
   `proto/review3/00_arg_head_order.sl`, this summary's own check); slc's compiled order is
   untested. Crashes, stuck states, and divergence can observe order; `Measure`'s cost readings are
   absorbed once the world's answers are inputs; that nothing else does is a conjecture (02 §2.3,
   r3.3).
7. **Extern mode changes acceptance by DESIGN.md's text.** §35: "with externs too, `(slot-of k)` is
   tag slot `k`"; `proto/dyn/tagslot.sl` is refused under `--no-extern` (02 §2.5, Q6).
8. **Compile-time fuel and crashes.** DESIGN.md does not mention fuel (03 F1). Both implementations
   refuse a run-position form whose run crashes (01 decision 7). slc's only fuel known to change a
   verdict is its depth bound (default 1000000000, fresh per form, macro run, and `Program` step);
   `merge-opens` would accept early if its bound were short, which 03 believes, unproved, it is not
   (03 §1, F3, r2.5). The reference has no default bound. §62's cap stops a self-calling macro
   (tested; 01 §3.5). slc's elaborator also carries a per-form expansion bound, separate from §62's
   per-run count (04 §2.3, r4.1).
9. **slc has no spec relation to retrofit against.** About 6% of ~18,650 lines are erased lemmas,
   mostly in libraries; the elaborator, interpreter, and emitter are trusted plain code, with 20
   `"internal:` sites, and the emitter trusts refutation (04 §2.2, §2.5).
10. **slc printer defect in `show-at`.** `slc --interpret` on a 100003-element list prints 49,999
    `Cons _ 0` then `Cons _ _ _)`: by §45 a wrong value, not a §31 crash, on which `self/README.md`
    is silent (04 r3.2). It reaches `--interpret`'s final printer, `comptime-match` mismatch
    messages, and `entry-value` (04 §2.3, r2, r2.2 to r2.4, r3.12), and `dump-context` reports (this
    summary's own check, `proto/review2/00_dump_deep.sl`). Compiled slc output and the reference
    print every element. `heap-strs-fuel` also cuts a request's string list short silently past 10^6
    elements; 04 reads both as plain bugs (04 §2.3, r3.4). The README's "1000000" (`:254-258`)
    matches no interpreter or printer fuel in `self/` (only `heap-strs-fuel`), and exhausted printer
    generation emits `?`, not "an error value" (04 §5, r4.5).
11. **Output-end risks in slc.** The emitter needs atom call and constructor arguments, which
    nothing types; the FFI's `-imm` operations, and the `(imm o n)` stores slc emits as
    `Array.unsafe_set` (`emit.sl:863-868`; five for `tests/cell_imm.sl`), bypass OCaml's write
    barrier (safety unchecked; 04 r3.1); the `Slots` implementation hashes raw addresses rather than
    searching with `slot-eq` as §69's models do, and its detection of GC moves is checked only by
    tests; `Bytes.unsafe_to_string` in `bytes-str` relies on uniqueness; 20-argument tail calls were
    checked only on amd64, OCaml 4.14.1, no flambda (04 §2.5, r2.5, r2.11, r2.12, r2.22).
12. **`mini/` gaps.** Malformed shapes have no derivation and `elab-program` can answer
    `ProgramStuck`; keywords are reserved though §19 lets special forms be shadowed; `Sexp` has no
    `Pos`; by MINIMAL.md, `mini/`'s language lacks multiplicities, `Matchable`, slots, macros, run
    position, literals, externs, and the `_` sugar (01 §3.7, §3.10; 04 §2.4, R3, r4.7; 04 reads
    owner statement 3 as needing `Stuck` refuted).
13. **Parameterization works by indexing.** A relation as an erased `TyCtor` parameter with a
    `(Model R)` record is accepted; a field is usable in types in a body after `let-match`, not in a
    signature (05 F7). Generic code can take apart a parameter relation's derivation given its
    constructors and an erased `Matchable` (05 r2.4). 05 F3's one-block limit is specific to
    `Certified`'s single level (05 r2.13).
14. **"`unique` is the sole reference"** is not needed for compiler correctness against a mutating
    heap spec; it links that machine to the tree reading the fact table relies on (05 §6, a
    reading).
15. **Source details are observable.** Columns are 1-based bytes in both (01 §3.9, r2.5). In two
    tests the reference reported only the first error and slc later ones too (01 §3.7); when
    compile-time fuel runs out (`fuel.sl`, `--eval-fuel 5`) the first message's position differs (01
    r3.3). slc gates each run-position run on no earlier error (`self/elab-main.sl:539`, `:545`,
    `:739`, `:2152`), so after one it seems to run none: a call and `(Succ (Zero))` get no `Settled`
    value, though a nullary `(Zero)` does, by an untraced path (01 §3.7, r4.1). The reference prints
    a first file's value before a second file's syntax error, then exits 1 (01 r2.11).
16. **The pattern works at toy scale.** 06's `advance` type is its soundness theorem, for whatever
    erased trace of fitting type the caller supplies (06 F2, r2.2); 07's `Verdict p` carries an
    erased `Elab [] p` or `Fails [] p`, and a spec-only `goal` passes `--goal proved` on both (07
    F2). The driver is the only loop. Wrong components are refused at the faulty proof term (07 F5;
    06 F2, where the first teeth check tests `step` only against `Step`, r3.5). Effort is mostly
    spec and determinism lemmas (06 F5; 07 F4).
17. **What the spikes do not prove.** Partial correctness only: in 06 a `step` always answering
    `SStuck`, an `advance` always `Ended` with `Stuck`, or a `run-total` always `AgreeStuck` fits
    the theorems' types (`proto/review3/06_vacuous.sl`), and that `run-total` halts or sticks within
    its count is read from its code, `finish` stopping only if the erased `Star` is real (06 F3,
    r4.3); in 07 a `step` answering `More`, with any `init`, passes; 07's exclusivity is about the
    spec alone, and its `Rejected` reason text is unconstrained (06 §1, r2, r3.4; 07 F7, r3, r2.4,
    third review). The drivers and printed text are outside the theorems (06 r2.3; 07 r2.4). In 07 a
    `step` that calls itself is refused (`proto/review4/07_loop_step_bad.sl`); that none can fail to
    return is §17's intent, untested (07 §1, r4.2). With one nondeterministic `Step` rule added,
    some program has both derivations and 07's `det.sl` is refused (compiled for that one variant;
    07 F4, r2.3).
18. **The output theorem cannot be "the same values, up to crash"**: §42 excepts `slot-eq`, §67 lets
    it vary, §69 extends this to `Slots`. 04 takes `slot-eq` answers as an oracle beside the host's
    answers to `world-do` and `read-file`, the theorem at most "values some spec run gives, for the
    same `slot-eq` and world answers, up to crash", itself a proposal (04 §2.6, r2.6, r3.5).

## 3. Decisions for the owner

Ordered so a decision precedes its dependents; spike decisions carry sub-letters. "Wording" says
whether DESIGN.md text would be needed (the owner confirms it word for word, rule 12) or it is a
formal-spec choice. Recommendations are the tracks', never decided.

### A. What the spec is about

**1. Where does the spec start?** (a) source bytes, a small reader before a `Raw` relation; (b)
`Raw`, reader trusted; (c) a core after dispatch and expansion; (d) the reader as a parameter with a
`Parses text raw` law (05 §4.4.3). *Rec.* (01, 04): (a), 04 adding that the reader be proved early:
statement 3 says "source code", positions are observable, and a core start drops head dispatch and
macros, central to DESIGN.md's aims (01's reading). 04 reads statement 3 as asking only totality,
which a total but unproved front end could give; "the spec's verdict on the text" needs reader and
expander proved (04 decision 2, r2.19). *Deps:* 14, `Pos` in the judgment, 17 (R2). *Wording:* none.
(01 decision 1, §4.1.)

**2. What does "parameterized the semantics" (owner statement 1) mean?** (a) one fixed spec; (b)
generic over a model record (extern models, oracle, and file system); (c) also syntax (1 (d)); (d)
also the prelude (16). *Rec.* (05): (b), plus (c) if syntax is separated; 04: the extern table (9).
*Deps:* the spec's signature, 9, 16. *Wording:* none. (05 decision 6, §4.4.)

### B. Making acceptance a function of the source

**3. Is elaboration order part of the language?** Visible through gensym numbers (§65), the
expansion count (§62), and which error comes first; DESIGN.md fixes head first (§6), statements
before later code (§27), and sequential threading (§65), not item order. (a) fix it; (b) leave it
free, acceptance a relation. *Rec.* (01): (a), both implementations' tested order of key finding 6
(a form head, the arguments' macro calls, a name head, the arguments, each left to right; rough edge
30), each statement before later code (01 §3.6, r3.1, r4.2). 07 reads a mirror-shaped `Fails` and a
zipper as needing a fixed order (07 F3). *Deps:* T3, 13's error content, 5. *Wording:* (a) needs it.
(01 decision 5; 05 §2.2; 07 §5.)

**4. Is runtime evaluation order fixed?** (O1) fix it: statements in written order, §15 bindings
before their statement, inner before outer, head, arguments, `values` left to right, scrutinee
before branch; (O2) only what DESIGN.md fixes, the spec a relation over orders, with a diamond proof
about as big as type soundness; (O3) O1 now, order-independence later. *Rec.* (02): O1/O3.
Sub-question: does §15's "behaves as if" fix timing (rough edge 4)? 02's variant "a form head, then
the §15 bindings" fits both implementations' tested runtime order (key finding 6) and §6 with §27;
the brief's proposal A fits hoisting only if applied after it (02 §2.2). 04 asks whether order is
meant to be unobservable (cross-file 2). *Deps:* lock-step versus confluence; slc's emitter vs O1.
*Wording:* O1, O3 need it. (02 decision 3, Q3; 04 rough edge 1.)

**5. How is `slot-eq`'s nondeterminism handled?** (a) an oracle parameter; (b) a nondeterministic
relation (T3 false); (c) compile-time answer = word equality; (d) forbid it at compile time; (e)
always `ENone` (`tests/slot_eq.sl` and `Slots` disagree); (f) always truthful (both implementations
fail it; 02 r2.5). *Rec.* by every track that decides it: (a), shapes differing: 01 an answer
stream; 02 a step → bit map with `ESome` needing the bit *and* equal words, theorem "some oracle
exists" (see 12); 05 an oracle also recording crash points and file contents, existentially
quantified in the verdict and logged by the compiler; 04 treats the answers as an oracle (key
finding 18). 05 warns an oracle free to answer `ENone` or crash lets a compiler over-reject while
meeting T1 to T3, a crash rejecting only sources that run compile-time code (§29), and only if it is
a rejection (6) (05 §3 T3, r3.3). See cross-file 1. *Deps:* T3, completeness, 8. *Wording:* (c), (d)
need it. (01 decision 6; 02 decision 4; 05 decision 3, §4.2.)

**6. What is a compile-time crash or fuel exhaustion?** §31 allows crashes "where the host cannot
represent what is asked of it"; §72 makes one "an error at its argument"; elsewhere silent. Both
implementations refuse. The tracks disagree:
- 01: the spec never crashes; the theorem allows a third outcome `Crashed` proving nothing (today an
  uncovered rejection, and a departure from §72 unless the compiled run is an oracle input).
- 02 (C4): a depth bound as compiler input, so acceptance is a function of (source, bound, flags,
  `read-file` oracle) given 4 and 5, and statement 3 would hold per bound if the rest of elaboration
  terminates (SOUNDNESS.md part 6 argues so without (T)); the bound bounds each run's steps (02's
  count, unchecked) if it counts activations, tail calls included, as `--eval-fuel` does; departs
  from §31; heap exhaustion stays host-dependent (02 Q5, r3.2, r4.1, r4.2). 01 and 02 are opposite
  and cross-referenced (01 r2.2; 02 r2.4).
- 03: fuel exhaustion is not obviously a §31 crash; `OutOfFuel` an outcome outside the spec; the
  answer bears on whether slc conforms. 04: open (under 10). 07: its toy's `FLetStuck` is a
  stand-in, and stuck is not a §31 crash.
- 05: open: is statement 3 about the spec, crash-free on 05's reading of §31, or also an
  implementation that "may crash"; keep crashes out of the oracle, or state completeness for the
  crash-free oracle.

*Deps:* 14, 5, slc's conformance. *Wording:* needed if crashes become rejections or a bound enters
the language; a third outcome is a theorem choice only. (01 decision 7; 02 decision 5; 03 decision
1; 04 decision 5; 05 decision 4; 07 decision 5.)

### C. The spec's run

**7. Does the spec run post-erasure code?** (R1) yes, as §27 and §29 say; (R2) typed code skipping
erased parts; (R3) R1 but performing skipped stores and calls. *Rec.* (02): R1; owner statement 6's
stripped-mode concern becomes type soundness of stripped code with a heap typing; stripping depends
on the fact table (§39), so elaboration outputs it. SOUNDNESS.md argues safety instead through a
"full semantics" running erased positions (part 3) and its (E) (part 7), which an R1 spec takes over
or replaces (02 Q1, r3.8). The reading "a mutating heap machine on code with erased positions
removed" is the earlier session's, unconfirmed. *Deps:* elaboration's output; type soundness.
*Wording:* none for R1, R2; R3 departs from §37, §39. (02 decision 1; 05 §3 T7.)

**8. Machine state and addresses.** (A1) `Imm n | Ptr a`, abstract never-reused addresses, mutable
blocks, explicit continuation, total step, `Program`-driven (brief's proposal B plus §33's
identities); (A2) natural addresses as slc; (A3) all boxed as slc's interpreter, §33's identities
via a block-to-word map (a cost, not an impossibility; 02 r2.2). *Rec.* (02): A1; its prototype uses
A2 (02 §2.6, r3.5). MINIMAL.md lists "Evaluation and typing are relations, not functions" under
"Decided about the semantics"; 02 reads A1's step as a deriving function beside such a relation, as
in `mini/` (r3.9). Unanswered by DESIGN.md: the word of an unapplied constructor; an extern type's
`Matchable` under `--no-extern` (§29); whether separately built values may share a word, which §33
settles only for values with no non-erased field ("however the value was built"; 04 rough edge 4,
r4.3; 02 Q2, r4.5). *Deps:* 5, T6. *Wording:* none unless sharing is settled there. (02 decision 2.)

**8a. Is the compile-time run a small-step relation over the compiler's own machine?** (a) yes, so
the evaluator proof is a list of step proofs; (b) big-step or another machine, which 07 reads as
perhaps nearer §27's "the evaluator runs the code" (though §31 calls the semantics "that of a
machine"), with a simulation proof 07 expects to dominate. *Rec.* (07): (a). In 06's toy big- and
small-step agree on runs ending on the empty stack, which 06 reads as presentation (06 Q1.4).
*Deps:* 8, T5's size. *Wording:* none. (07 decision 2, Q2.)

**8b. Should the next spike use the unique `Array` heap and abstract addresses?** 06's heap is
`many` lists, addresses positions. *Rec.* (06): yes, before scaling, given 8's A1; owner statement 6
concerns the spec's run, this the implementation's heap (06 r3.6); that `Array`'s `Nth`/`SetNth` API
carries 06's proofs is untested. *Wording:* none. (06 decision 4, Q3.)

**9. Externs in the spec.** (E1) run every model, agreement hypothesized; (E2) `Nat` primitive on
immediates, other models run; (E3) all extern primitive; (P) parameterize by an extern table,
agreement a separate testable obligation; (X) one axiom per implementation (103 functions, 7 types).
*Rec.* 02: E2, since under the `Nat` model §33's "word of the `Nat` of its position" and §35's
tag-slot literals need a further choice, or the spec refuses what the compiler accepts
(`tagslot.sl`; key finding 7; 02 decision 6, r3.4); 04, 05: P. They may combine; no track says how.
*Deps:* 2, trust base, cross-file 6. *Wording:* none; 02 asks if the extern-mode dependence is
intended. (02 decision 6; 04 decision 7; 05 §4.4.2; 01 decision 8.)

**10. Where may a compiled run crash?** (C1) "spec behaviour or a prefix ending in a crash" (an
always-crashing compiler passes); (C2) only at named resource events (allocation, stack push, FFI
past `array-limit` or `bytes-limit`, or the U62 host check); (C3) a spec indexed by heap and depth
bounds, the theorem for a host with c times as much. *Rec.* (02): C2, C3 later. 04 asks whether the
outcome is "a value some spec run gives, or a crash" (04 decision 5, r2.6). *Deps:* T6. *Wording:*
none as the tracks mark it; whether C2 constrains implementations, and so needs it, is unsure. 02
asks what a crash does to earlier effects. (02 decision 5, Q5.)

**11. What happens when the spec goes wrong?** (S1) a defined `abort` that compiled code must also
produce, as both implementations do (02); (S2) undefined after stuck (02); (W1) T6 assumes no going
wrong (05); (W2) going wrong permits anything after (05). *Rec.* 02: S1; 05 none, expecting
stripped-run safety to stay meta; 06 asks if "never stuck" is a target, a typing invariant (Q2.2)
then also serving type soundness (06 decision 3). *Deps:* T6, T7. *Wording:* none as the tracks mark
it; whether S1 needs it is unsure. DESIGN.md does not say what reaching absurd code does. (02
decision 7; 05 decision 7.)

**12. Compile-time values in the output: trees or heap graphs?** (V1) trees; (V2) graphs up to
renaming. *Rec.* (02): V1 for the theorem, V2 as an option, the spec's own store a heap: in 02's
reading 5's "some oracle exists" needs one block per `Settled` value, since an oracle only turns
`ESome` into `ENone` and `proto/review4/02_share_pair.sl` answers `ESome` on both, interpreted and
built (02 Q8, r4.6). Whether V1 suffices for slot facts is unverified. *Wording:* none. (02 decision
8.)

### D. The theorems

**13. Intrinsic theorems, positive `Fails`, and what a rejection carries.** (i) Intrinsic statements
(05: yes). (ii) Positive `Fails`: 01 and 05 agree but differ on shape (cross-file 11): 01 the `Err`
outcome of one total relation; 05 separate `Elab`, `Fails`, and an exclusivity lemma. 07 compiled
05's shape and recommends `Fails` mirror `Elab` premise by premise, so one context serves both,
fixing premise order (3); exclusivity is a plain induction either way, as 05's order-free
`t1_toy.sl` shows (07 decision 3, r4.3). (iii) Content: (a) "rejected"; (b) first error position and
macro trace; (c) also a structured reason, including §4's text and §28's expected constructor and
actual value; (d) full text. 01: (b) in the theorem, (c) in the relation, never (d), noting that the
first message's position differs when compile-time fuel runs out (key finding 15); 05 carries a
`Diag`; 07's mismatch rule carries the value, free reason text outside its theorem (07 r2.4).
Malformed syntax must be a positive error (01 §3.7). *Deps:* every pass's architecture; how much of
3 is pinned. *Wording:* none. (05 decisions 1, 2; 01 decision 4, §4.3; 07 decision 3.)

**14. The form of theorem 3 and the hypothesis H.**
- 01: (a) relative to H; (b) fuel, exhaustion a third outcome `OutOfFuel` or a rejection; (c) a
  coinductive "diverges". Rec.: (a), from (b): a fuelled deriving function is total with no
  hypothesis, and (a) would follow under H plus two lemmas, fuel monotonicity and a halting spec run
  being reached at some finite fuel, H applied to one program's finitely many runs (unchecked; 01
  r3.2, r4.4).
- 03: "H(src) ⇒ the driver reaches `Exit` with a verdict", plus an internal function taking erased
  H(src); or three outcomes. Rec.: the first, which 18's (a), (b), and (e) can give, leaving
  unbounded iteration to the driver; only (c) gives three outcomes (03 decision 2, r4.3).
- 05: (a) meta only; (b) Bove–Capretta `compile-h` on an erased `Halts` (one reading of 4(ii), in
  practice not callable without a proof or prior fuel run; key finding 4); (c) fuel whose
  `OutOfFuel` proves the spec run unfinished after `f` steps (one reading of 4(i)); (d) a step
  machine giving T1/T2. Rec.: (d) plus (b) or (c), uniform totality meta; alternative: a
  compile-time resource budget in the language, making statement 3 literal (a language change).
- 07: include completeness relative to per-source evidence (unwritten), else a never-answering
  stepper passes.

Sub-questions: H as 4(ii)'s "every accepted compile-time form's spec run halts" or the broader
"every compile-time run" (cross-file 5); H over evaluation only, `read-file` and `native-compute`
axiomatized (03: yes). *Deps:* 6, 18, whether elaboration takes fuel. *Wording:* only the budget
alternative. (01 decision 2; 03 decisions 2, 4, F7; 05 decision 5, §4.3; 07 decision 4.)

**15. Which flags are spec parameters; is the expansion limit one?** 01 in: prelude and extern
on/off, `--fn-same`, `--goal`, `--comptime-unconfine` names, and FFI names and arities; out:
`--eval-fuel`, `--no-native`, `--hints`, and `--warn-unused` (its review unsure on the last two);
warnings ignored, `--warnings-as-errors` a driver policy. §62 fixes the limit at 10000; 01, 03, and
04 keep it, and only making it a parameter `N` is open (01 r4.3). §62 does not say the cap's breach
is an error; both implementations make it one. *Wording:* for the 10001st expansion, or for `N`. (01
decisions 3, 8; 03 decision 5; 04 §2.3.)

**16. What is the prelude to the spec?** (a) a fixed elaborated snapshot; (b) the shipped text; (c)
any prelude text, `--no-prelude` the empty one, qualified: it also frees `extern` (§42), and whether
an empty text equals `--no-prelude` is the owner's call. *Rec.* (01): (c), since (a) seems to need
the 2881-line prelude elaborated in Sleight via the evaluator under proof. 05: generic over the
prelude is "too wide" (cross-file 3). Also: are INTERNALS.md's `def-prim` and `def-opaque` in (04
rough edge 3)? *Wording:* none. (01 decision 9, §4.5, r2.4; 05 §4.4.4.)

### E. The compiler

**17. Which route?** (R1) retrofit slc (very high effort, serial on one block); (R2) certified
kernel behind slc's unproved front end (trusted for meaning; re-runs run-position forms); (R3) new
spec-first compiler, `mini/`-style, reusing slc's proved libraries; (R4) translation validation.
*Rec.* (04): R3, R4 only at the output end, slc for differential testing: parallel work per
judgment, round trip designed in, nothing in slc to retrofit against (key finding 9); tens of
thousands of lines, a guess. 03's fuel work assumes slc (cross-file 7). *Deps:* all of group E.
*Wording:* none. (04 decision 1; 03 decision 3.)

**18. How is fuel kept out of results and theorems?**
- 03: (a) the compiler as a `Program`-stepped state machine; (b) iterative deepening (cheap stopgap;
  needs monotonicity and rolling back §62's and §65's counters); (c) `OutOfFuel` outcome; (d) a
  normalizing interpreter (ruled out by the diagonal, for a non-erased function on source text with
  no further evidence); (e) inline bursts suspending to the driver, replaying the current form.
  Rec.: (e) for slc, (a) for a new kernel, (b) as stopgap.
- 04: (F1) iterative deepening at the driver, failed attempts under doubling costing less than twice
  the last; (F2) explicit-stack, no fuel; (F3) fuel in the theorem. Rec.: F1 now; F2, if wanted,
  decided before R3 starts (04 F1, r4.2).
- 05: a step machine (14).

The brief's goal "minimize fuel use" bears on all. *Deps:* 17. *Wording:* none. (03 decision 3, Q1;
04 decision 3, Q2; 05 decision 5.)

**18a. Resumable checker: zipper or replay?** (a) zipper: erased `Ctx` and `Reach` advanced one
total step per `Program` step; (b) direct style, replaying with a proof-carrying answer oracle; (c)
bursts with replay on overflow (03's (e)), untested, expected to need (b)'s proof. *Rec.* (07):
zipper for a new kernel, replay only retrofitting slc. Replay needs proof-producing equality on
requests (heaps in full Sleight, 07's reading) and about quadratic work (07's estimate); the zipper
rewrites most of the elaborator into frames (07's expectation). *Deps:* 17, 18. *Wording:* none. (07
decision 1, F3, F6.)

**18b. Certified-stepper invariant: erased trace or counter closure?** Also a first-order derivation
context (untested; 07's `Ctx` is of that kind, on this summary's reading) or small-step as spec.
*Rec.* (06): the trace, as a working hypothesis; it calls the trace-versus-closure choice
presentation. *Wording:* none. (06 decision 1, Q1, F4.1.)

**18c. Should a function apply a closure whose level is packed beside it?** It can with a packed
`Predates` to its own level, and with a second one and a counter a step extends the closure at its
packed level (`proto/review4/06_packed_counter.sl`). Extending it at a level minted during the run
fails: by 06's reading of §18's rule for `prove-predates` ("`x` must have an introduction order (§5)
earlier than `L`'s"), such a level is never provable below the stepper's (06 F4.2, r4.1, r4.2). 06
proposes no change, since a counter closure works. *Wording:* only if changed. (06 decision 2.)

**19. Judgment shape and staging.** *Rec.* (01): 01 §4.2's layers and Σ/Γ split, the run a parameter
of elaboration so its metatheory holds for every lawful run (a relation-valued `TyCtor` index's
usability unverified; 05 F7). Open: run-position facts in Γ or Σ (01 r2.3). Staging S0 to S6:
reader; `mini/` recast; `Settled` and the round trip; erasure and uses; externs, macros, and
prelude; slots and cells; sugar, goals, and `native-compute` (S2 and S3 in either order). *Deps:*
how much of `mini/` is rewritten. *Wording:* none. (01 decisions 10, 11.)

**20. Where does the output proof stop?** (O1) the post-erasure IR, trusting the emitter, ~830 lines
of OCaml runtime, templates, and OCaml; (O2) model slc's untyped OCaml subset; (O3) a new target,
departing from what `self/README.md` reports as an owner decision on `lib/extract.ml` (unconfirmed,
not in the brief); (O4) re-parse output with a proved parser. *Rec.* (04): O1 now, O2 + O4 later; IR
arguments atoms by type. *Wording:* none. (04 decision 4, Q3.)

**21. `native-compute`.** (N1) exclude; (N2) oracle premise; (N3) the output end's trust, N2's
wording as premise; (N4) re-run in the proved evaluator. *Rec.* (04): N3; 02 C4: oracle or excluded;
01 notes §72 (6). *Wording:* none unless 6 changes §72. (04 decision 6, Q4.)

**22. Which checker's PASS is the trust root?** (B1) both `lib/` and slc (sharing `lib/ffi_core.ml`
and lineage); (B2) the proved compiler itself (benignly circular). *Rec.* (04): B1; 05 none. Logic
soundness stronger than consistency, as SOUNDNESS.md's (T), (S), and (E), and the checker stay
trusted (05 §5, r4.7). *Wording:* none. (04 decision 8; 05 decision 8.)

**23. Prove sole-reference and full-semantics safety inside Sleight?** 05: plausible and worth it,
as reachable-state invariants; it justifies `is` reasoning about a run but not the stripped run's
(E), which still needs (T); 06 calls such an invariant "the shape the full Sleight machine would
need anyway" (11). *Wording:* none; 02 asks what §13's "the only reference" means. (05 decision 9.)

## 4. Rough edges in DESIGN.md (questions, none resolved)
1. **Elaboration order.** §65 threads the macro world "sequentially" and gensym counts "over the
   whole run", but only §6's head-first and §15's hoisting fix part of the order; is item order (key
   finding 6) part of the language? (01 §5.1; 02 §5.12; 05 §8.5; 07 §5, r2.6.) See also 30.
2. **Runtime statement order.** §27 orders statements only in run position; §61's "stores `h` before
   the call" seems to presume written order. (02 §5.1, §5.11; 04 §5.1.)
3. **§15's bindings.** §29 mentions binders for "head, arguments and scrutinee (§15)", but §15 names
   only arguments; how are several ordered? (02 §5.2, §5.3; 04 §5.1.)
4. **§15's "behaves as if" and time**: if temporal, `((pick) (h n))` runs `(h n)` first, against §6
   with §27 and against the reference and `slc --interpret` (key finding 6). (02 §5.10.)
5. **Is evaluation order meant to be unobservable?** 04 notes it decides between a crash and
   divergence when one argument does each, a case §17's levels are meant to rule out ("Termination
   rests on levels"), unsettled. (04 §5.1, r2.20, r3.7; 02 §2.3.)
6. **`slot-eq` and acceptance**: §67 lets conforming implementations disagree on accepting a text;
   intended, given owner statement 3? (01 §5.2; 05 §8.1.)
7. **Shared words**: §36 makes two equal cells "two blocks", and §33 gives a value with no
   non-erased field one word "however the value was built"; may separately built values with a
   non-erased field, or of an extern type, share a word? (04 §5.4, r4.3.)
8. **Compile-time crash**: outside §72, an error, or no verdict? Is a fuel bound a crash "where the
   host cannot represent what is asked of it"? (01 §5.3; 03 §5; 04 §5.2; 05 §8.2.)
9. **Crash and earlier effects**, and where a crash may occur (§31). (02 §5.5.)
10. **Absurd code reached at runtime** is unspecified; both implementations abort. (02 §5.6, r2.10.)
11. **"The evaluator" (§27, §29)**: the spec's run? §42 and §29 describe runs of both the
    implementations and, under `--no-extern`, the models; which is the meaning is open, though §42's
    "the same values" reads as if the models were. (03 §5; 04 §5.5, r4.4; 05 §8.3.)
12. **`Nat`'s word under models**: §33's "the word of the `Nat` of its position" presupposes one
    word per `Nat`; the FFI must meet it only "With externs on", and §35's literal tag slots hold
    only "with externs too", so acceptance depends on extern mode (tested; apparently by design),
    and §42's "the same values" has nothing to compare for a program refused under models. (02
    §5.4.)
13. **§42's "the same values"**: trees or with sharing? (02 §5.8.)
14. **§13's "the only reference"**: do slot words (§38) and an array's `Stale` word (§44) count?
    §36's reading-back references a consumed binder's word. (02 §5.7.)
15. **The FFI table** (§42) puts one implementation's table into acceptance. (01 §5.9.)
16. **`def-prim`, `def-opaque`**: absent from §54, specified in INTERNALS.md; part of the language?
    (04 §5.3.)
17. **Where `Settled` comes from**: are built-in `Special` entries, and entries minted by the §65
    primitives, among §29's three sites, given "So any `Special` or `Macro` that is ever invoked
    (§6) comes from run position"? Literals are "as if minted by run-position forms" (§45). (01
    §5.12, r2.12, r4.6.)
18. **The expansion cap** (§62): does the prelude count, is the 10001st an error, and are §62 and
    §49's 1024 precedents for a compile-time budget? (01 §5.7; 03 §5; 05 §8.6.)
19. **Reader details**: `042` (§1 vs §45); `\q` (§45); `Pos` column unit (§42). The reference
    refuses the first two; columns are bytes in both. (01 §5.4 to §5.6.)
20. **Multiple errors**: DESIGN.md is silent; implementations differ. (01 §5.11.)
21. **`--warnings-as-errors`** (§4) depends on WARNINGS.md. (01 §5.8.)
22. **`dump-context`** is defined via MANUAL.md (§27, §54). (01 §5.10.)
23. **`read-file` that never ends** (a FIFO, §65). (03 §5.)
24. **May an implementation itself be "the driver's loop over total functions" (§42)?** (03 §5.)
25. **Character literal bounds** are "asserted rather than decided" (§45): a spec axiom. (05 §8.4.)
26. **Tests fix free behaviour**: `tests/slot_eq.sl` expects `ESome` where §67 allows `ENone`; not a
    contradiction. (02 §5.9.)
27. **Packed-level closures**: without a packed `Predates` to the caller's level, such a closure is
    uncallable, by §18's introduction-order rule for `prove-predates`; a consequence, not a gap;
    wanted (18c)? (06 §5.1, r3.1, r4.2.)
28. **Divergence** is never mentioned (07 searched); §17, §20, §33, §42, and §62 suggest functions
    halt, but nothing says every compile-time run does, or what a never-returning checker means, or
    whether levels, with §10's `Type : Type` and no positivity, prevent divergence. (07 §5, r2.7.)
29. **`comptime-match` mismatch text** (§28): if a rejection carries its reason (13), is the printed
    value part of the spec? (07 §5.)
30. **A name head** (§6: "The head is elaborated first"): both implementations elaborate a name head
    after the arguments' macro calls expand, so `(nosuch (loop))` is refused for the expansion
    limit, not the unbound head (`proto/review4/01_head_name_err.sl`); a deviation, or only which
    error is reported, which DESIGN.md does not fix? (01 §5.13, r4.2.)

## 5. Cross-file inconsistencies

Open ones; numbers follow the review log, gaps being resolved items.

1. **Addresses versus compiled `slot-eq`.** 02's A1 with N1 (`ESome` needs equal words) holds only
   if a compiled `ESome` never meets two words the machine keeps apart (02 r2.5); slc's native
   `ESome` on two `(str-append "a" "b")` is such a case, a mismatch "only if the spec says that
   every allocation takes a never-used address" (04 §2.5, r2.7).
2. **Is order observable?** 04 rough edge 1 suggests it may not be (though 04 adds crash versus
   divergence, r2.20); 02 §2.3 lists observers. Open in 04.
3. **Generic over the prelude**: 01 decision 9 yes; 05 §4.4.4 "too wide".
5. **H's wording**: 05 §2.3 uses 4(ii)'s "accepted" form; 01 decision 2, 03 F7, and 04 Q2 use
   broader ones; only 01 flags it.
6. **`--no-extern`**: 05 §5 drops agreement axioms for model-only programs; 02 §2.5 shows acceptance
   itself changes there; 05 omits it.
7. **Fuel target**: 03 (e) for slc, (a) for a new kernel; 04 R3 with F1 (03's stopgap); 05 a step
   machine, which 04 rates costly.
8. **Compile-time crashes**: 01, 02, and 03 incompatible (decision 6); 05's oracle "crash points"
   have no place in 01's crash-free spec.
9. **Going wrong**: 02 S1 versus 05 decision 7's W1/W2.
10. **Diagonal versions (largely reconciled)**: 03 F6 and 05 §4.3 share the `read-file` macro form;
    05 alone keeps a quine for a run-position variant (05 r2.1, r2.2).
11. **`Fails` shape**: 01 §4.3 rejects separate relations as "more duplication, against rule 5"; 05
    §3 recommends them.
14. **`--goal proved`** (not a contradiction): 05 says a driven verdict never reaches `qed` (05 F6,
    r2.5); 07's goal states the step functions' type, not a run's result, and `drive.sl` bypasses
    `Certified` (07 F7).

## 6. What is not yet known or unverified

- **The diagonal beyond its mechanism**: no faithful `compile` was put in Q; "H for all sources
  yields a runnable `compile`" is untested and assumes soundness (03 F6, r5); the carry-over to a
  rejected Q (part 5's invariants are stated for reachable states of accepted programs) and the
  `slot-eq` step are reasoning (03 §6, r2.3, r3.4, r4.1); all rests on (T), (C), (E), and logic
  soundness, unproved; 05's run-position variant assumes unwritten quines (05 §9).
- **Gödel II** conditions and README.md's IΣ₂ / ω^ω^ω claim are unchecked (05 §9). By 05's
  reasoning, if the logic is sound the diagonal rules out uniform H in a recursable form, and
  uniform stripped-run safety alone would give internal consistency, since an erased proof of
  `False` yields a run-position form that checks and reaches absurd code once stripped, so the
  program is refused (`proto/review4/05_stripped_absurd.sl`: "absurd code reached" on both);
  formalizing this inside Sleight is untried (05 §4.3, r2.3, r4.4).
- **SOUNDNESS.md's (T), (C), (E)** are argued, not proved; they "do not cover" `--no-prelude`
  programs with own models or `def-prim`; H also needs well-behaved host I/O (03 F7, r2.6; 05 §2.3,
  r2.8).
- **Erased derivations being "real"** rests on no closed proof of `False`, unshown given `Type :
  Type` and no positivity (06, 07 second reviews).
- **Conditional or proposed**: 02's N1 (cross-file 1); 04's output-theorem shape (04 second review).
  **Writability** of a function on erased H(src) evidence, and of P3 as an erased function (03 §6).
  **Order-independence**, of the machine and of §50 meta solving, and §13 as a heap invariant (02
  §6; 01 §6). **01's layering**: no-cycle run layer, Γ or Σ for run-position facts, empty prelude
  versus `--no-prelude`, relation-valued `TyCtor` at scale (01 §6, r2.3, r2.4; 05 F7 toys only).
- **At scale**: determinism, progress, preservation, sole reference, and simulation to refinement
  under `slot-eq` and crashes (05 §9); V1 trees and slot facts (02 §6); literal blocks as tag-slot
  words (02 review).
- **Closures as suspensions**: CPS `bind` with counters, level-indexed continuations, a packed level
  from a caller, extension at a level minted during the run (03 F4.1; 06 §6, fourth review). **C4's
  count** for a function called through data (02 fourth review).
- **Spikes at scale** (06 §6; 07 §6): Sleight's own machine (rules, frames, `at` and cells, and the
  oracle); nested round trips and how much of elaboration becomes frames; replay on (code, heap)
  requests; 8a (b)'s cost; 06's Q1.3 context, `Array` proofs, and 60–80-line estimate (Q2.1).
- **Spike completeness**: 07's Q3(a), program 6 having neither derivation, replay not looping on a
  mismatched head (07 §6, F7); "no verdict iff a run the checker reaches diverges", neither
  direction proved (07 F7, r3.5); no third vacuity; whether, with independent premises and a
  diverging run, a mirror-shaped `Fails`'s order decides whether a verdict exists (07 third and
  fourth reviews).
- **Reported histories and figures**: "accepted as first written" claims (06 F4, 07 F4) and 05's
  "first attempt refused" claims (one reproduced, 05 r3); 07's quadratic estimate; single-run
  timings (06 r2.6; 07 §6); all cost and effort figures (01 §6; 03 §6; 04 §6).
- **slc internals**: the path by which a nullary `(Zero)` is `Settled` after an error (01 §3.7, §6);
  that the per-form expansion bound never binds before the global count, store cycles, macro
  callbacks never evaluating, checkpoint rollback of counters, failed fuel attempts as prefixes (03
  §6, Q1, second review); `merge-opens`'s bound (03 §1).
- **`dump-context` and §45**: whether its reports, defined via MANUAL.md, fall under §45's printing;
  the cut is at least a silent wrong answer.
- **OCaml**: `let ... and` and argument order in versions other than 4.14, whose manual leaves them
  unspecified (02 §2.2, r4.3); other targets, flambda, many-argument tail calls; constant sharing
  beyond immutable tuples; GC safety of `-imm` operations and of `Array.unsafe_set` through an `int
  array` cast on a variant block; `Slots` hashing across GC moves; `bytes-str` input never mutated
  (02 §6; 04 §2.5, §6, r3.1, fourth review).
- **slc's runtime head-versus-argument order**: compiled output is untested. `slc --interpret`
  overflows on `proto/review3/head_arg_order.sl` at any depth, seemingly on its oversized
  `array-new`; in `proto/review3/00_arg_head_order.sl` (`--eval-fuel 20`) both implementations crash
  on that allocation in the head, and without it run out of fuel in the argument (02 §6, r3; this
  summary's own checks). §31 leaves "How a crash is reported" open, so whether the overflow is a
  defect is unsure.

## 7. Spikes
**06, a certified fuel-free stepper** (`proto/stepper/`). A register and mutable-heap language with
`if` and `while`, specified by big-step `Runs`; a total non-recursive `step` over an explicit stack,
one `Program` step each, run by the reference (also `--no-extern`, `--build`) and slc
(`--interpret`, `--build`) (06 §1, F1, F2). Proved: soundness as `advance`'s type, spec and step
determinism, `runs-star`, and, as `run-total`'s type, that an `AgreeHalted` result is the spec's;
that it halts or sticks within the count is read from its code; swapped or inverted components are
refused (06 F2, F3, r4.3; key finding 16). Not proved: progress, or anything about the driver (key
finding 17). Invariant: an erased trace folded by a 15-line `step-back`; a counter closure, at a
fixed or a packed level, also works (06 F4.1, F4.2, r4.1). Effort: ~210 proof lines against 90
stepper and 67 spec; 7821 steps take 1.33–1.5 s in the reference interpreter, 0.48–0.56 s in slc's,
under 0.01 s compiled (single runs per review; 06 F5, F6). Costs: one evidence type per partial
helper (§9, and "There is no currying", §17), long telescopes, and opaque numerals (§45) (06 F4.3,
F5).

**07, the §29 round trip with a suspendable checker** (`proto/roundtrip/`). Top-level `Let` (run at
check time), `Assert` (a `comptime-match`), and `Need` (facts only); inductive `Elab` with
evaluation premises, positive `Fails`, small-step `Step`; each `Program` step is one `cstep`,
handling a statement, a machine step, or, last, the empty list (`Accepted`; program 0: 6 + 19 + 1 =
26; 07 §1, F2, r2.1, r4.1). Proved: exclusivity via determinism of evaluation and lookups (07 F4,
r3.2), passing `--goal proved` for zipper and replay on both; four wrong standalone components
refused (07 F2, F5, r2.2). Not proved: completeness or termination (key finding 17). Zipper: erased
`Ctx`, one serving `Elab` and `Fails` since each "fails later" rule repeats its `Elab` rule's
premises (07's reading), and `Reach`; replay: direct style, ~50 of 127 lines for request equality,
not quite 03's (e) (07 F3, F6, r4). Effort: spec 178, determinism 123, zipper 151 (suspension ~45),
replay 127, and driver and tests 61; the evaluator side was trivial only because `Step` is the
implementation's machine (07 F4).

As a reading, the shape 03, 05, and the brief's proposal C describe is writable and checkable at toy
scale; completeness and scale remain open.

Review history, corrections, and re-runs: 00-summary-review-log.md.
