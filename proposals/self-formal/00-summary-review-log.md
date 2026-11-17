> This is the pre-condensation 00-summary.md, kept for its review notes and history.
> It is superseded by 00-summary.md, which states the same content condensed.
> Nothing here is approved; where the two differ, 00-summary.md and the cited track files are right.

# 00. Summary: formalizing Sleight in Sleight, and a compiler proved against it

Written by Claude agents overnight, while the owner was asleep. Everything
here is a proposal or an agent's reading; nothing is approved, and nothing
is a design decision (CLAUDE.md rules 1 and 11). This file only combines
the five track files and the two spike files: each claim's source,
evidence, and hedges are in the file and section it cites, and where this
file and a cited file disagree, the cited file (as corrected by its review
notes and second review notes) is right; this file's own corrections
are listed at its end.
Where either disagrees with DESIGN.md, DESIGN.md is right.

Citations: `01 §3.6` is section 3.6 of `01-spec-shape.md`; `02`
is `02-dynamic-semantics.md`, `03` is `03-fuel-termination.md`, `04` is
`04-compiler-route.md`, `05` is `05-theorems.md`, `06` is
`06-spike-certified-stepper.md`, and `07` is `07-spike-round-trip.md`.
`§n` alone is
DESIGN.md. "Owner statement n" is item n of the brief's "Owner decisions",
which are an earlier session's paraphrases, not the owner's words; they,
and the goals the brief lists beside them (such as "minimize fuel use"),
are the only owner positions this file reports.

## Contents

1. The picture in one page
2. Key findings
3. Decisions for the owner (23, and 8a, 8b, and 18a to 18c from the spikes)
4. Rough edges in DESIGN.md
5. Cross-file inconsistencies
6. What is not yet known or unverified
7. Spikes
8. Review notes
9. Second review propagation
10. Third review notes

## 1. The picture in one page

Each item is the tracks' recommendation, not a decision. Where the tracks
disagree, the decision listed says so.

- **Spec shape.** Start at source bytes: a small total reader function
  produces `Raw` forms with positions, and everything after it is a
  relation. Three layers: a fact engine free of evaluation (§7, "The engine
  of §7 reads no stored value", §29), a run relation that reads it, and an
  elaboration relation with run premises at each run-position form. A
  store Σ (§65's macro world) is threaded through all of elaboration; the
  scope Γ is restored when a scope ends. Which of the two holds the
  run-position facts is open, since §65 counts "the run-position entries
  with their values and facts" as part of the macro world (01 §4.2,
  second review note 3). Rejection is a positive `Fails`,
  the `Err` outcome of one total relation. (01 §1, §4.2, §4.3; decisions
  1, 13, 19.)
- **The run.** A small-step heap machine over post-erasure code, as §27
  already describes ("its erased positions are stripped, the evaluator runs
  the code"). Words are `Imm n | Ptr a` with abstract, never-reused
  addresses compared only for equality; blocks are mutable; the step is
  total, with an explicit continuation stack; one fixed evaluation order;
  `Nat` is a machine primitive; `slot-eq` reads an oracle. (02 §3 Q1, Q2,
  Q3, Q4, Q6; decisions 4, 5, 7, 8, 9.)
- **Fuel.** If Sleight's functions terminate (SOUNDNESS.md's (T), argued
  there, not proved; 03 §1), no hypothesis-free,
  non-erased Sleight `compile` on source text can be faithful for every
  source (the diagonal, key finding 2; partly untested reasoning). So
  fuel either stays as an internal device that never shows in a result, or
  the unbounded part is moved into the driver's `Program` loop, which
  prototypes show needs no fuel. The tracks recommend different
  mechanisms (decision 18): a stepped interpreter with bursts and replay
  (03), iterative deepening at the driver (04), or a whole-compiler step
  machine (05). 07 compiled both a derivation-zipper checker and a
  replaying one for a toy round trip, with no fuel (decision 18a).
- **Theorem statements.** Intrinsic: `compile` returns its verdict with an
  erased spec derivation, since a type holds no call (§9). T1/T2
  (accepted ⇒ `Elab` derivation; rejected ⇒ `Fails` derivation), T3
  (never both, per oracle), T4 (every source accepted or rejected:
  owner statement 3) relative to a halting hypothesis H, T5 (compile-time
  values match the spec run), T6 (output refines the spec). Uniform H and
  stripped-run safety are expected to stay meta-theorems. (05 §3, §7; 01
  decision 2; 03 Q2; decisions 13, 14.)
- **Evidence from the spikes** (findings, not recommendations). The
  pattern above (a spec relation, a total step that returns erased
  evidence, the `Program` driver as the only loop, and a verdict typed by
  the spec's derivation) compiles and
  runs today in two toys, a heap machine (06) and a §29 round trip (07),
  on the reference and slc. Both prove partial correctness only: a step
  that always answers "stuck" (06) or never answers (07) passes. Neither models Sleight's own machine. (Key
  findings 16, 17; section 7.)
- **Compiler route.** A new elaborator written spec-first as deriving
  functions beside the relations, in `mini/`'s shape, reusing slc's
  proved libraries and keeping slc for differential testing (04 §3 Q1,
  "R3"). 03's fuel recommendations are framed around changing slc instead
  (decision 17).
- **Output end.** Prove down to the post-erasure IR first, with call and
  constructor arguments atoms by type; later model the untyped OCaml subset
  slc emits and validate the printer per run by re-parsing (04 §3 Q3,
  "O1", then "O2 + O4"). `native-compute` carries the same trust as the
  output end (04 Q4 "N3"). (Decisions 20, 21.)

## 2. Key findings

Only findings the track and spike files support after their reviews.
"Tested" means a prototype was run on the reference (`_build/default/bin/main.exe`) and,
where stated, on slc.

1. **Elaboration reads run results, so it cannot be a typing relation
   separate from the run.** Head dispatch needs a `Settled` entry whose stored value
   names the form (§6 item 1); `comptime-match` reads a stored value (§28);
   a run-position form "is elaborated, its erased positions are stripped,
   the evaluator runs the code, and its results become `Settled`" before
   "the code after it is checked" (§27); `prove-literal-lt`, `unary`, macros,
   and `native-compute` also run code (01 §3.1). The fact engine reads no
   stored value (§29: "The engine of §7 reads no stored value"; 01 §1, §3.2,
   second review note 7). Consequences: a typing relation separate from
   evaluation does not fit DESIGN.md (01 §1); a kernel behind slc's front
   end must re-run every run-position form or check a trace as long as the
   run (04 Q1 "R2"); `mini/` has no run position and so never meets the §29
   round trip (04 §2.4; 01 §3.10). Whether the run layer needs only the fact
   engine, scope lookup, and Σ (so the layers form no cycle) is an
   unverified reading of §65 (01 §3.2).
2. **The diagonal argument, and what it does and does not rule out.**
   Mechanism tested: `proto/fuel/diagonal.sl` has a macro `read-file` its
   own file, run a stand-in `toy-compile`, and expand to `compile-error`
   exactly when it accepts; the reference and `slc --interpret` agree that
   the stand-in is wrong on it (03 F6). The rest is reasoning: a
   non-erased Sleight `compile : Src -> Verdict` with no further evidence,
   faithful to the spec on every source, is impossible if Sleight's
   functions terminate (SOUNDNESS.md's (T), argued there, not proved; 03
   §1, F6, second review note 4). If `compile` calls `slot-eq`, 03 applies
   the argument to its copy with every `slot-eq` answered `ENone`, which
   §67 permits (03's reasoning; second review note 3). The branch must be
   in a macro's output or a `comptime-match`, because `compile-error`
   "fires wherever it is elaborated, erased code included" (§4; 03 review
   note 1; compiled in `proto/review2/03_untaken_ce.sl`). Corrected
   conclusion (03 F6 "What it does not refute", review notes 3, 5): it does
   **not** refute owner statement 4(ii) read as mathematics, nor a
   `compile` that takes erased evidence of H for its one source; it does
   suggest (untested inference, assuming Sleight is sound) that H for all
   sources, in the form of erased step counts, is not provable inside
   Sleight. slc does **not** escape the argument: its whole compile runs
   in one `Program` step and is total through its fuel (03 F2, F3 row 1),
   which already makes it unfaithful where compile-time runs nest past
   the bound. Its elaborator's `World` stops a source from calling slc's
   own elaborator at compile time, but, in 03's reading, that blocks only
   the literal construction: a `compile` that uses its `World` only to
   read files has a `World`-free version taking the files from `Src`, to
   which F6 applies (03 F6 "The escapes", second review note 1). 05 §4.3
   now runs the same argument through `read-file` in a macro, with no
   quine, and needs T1 to T4 and determinism through T3, not T5; a quine
   (not written) is needed only for its run-position compile-and-run
   variant (05 second review notes 1, 2). 05 also gives a Gödel-II reading
   whose conditions are unchecked.
3. **Theorems must be intrinsic.** §9: "The elaborated form of a type never
   contains a function call" (tested refusal, 05 F1). A toy checker that
   returns `Accepted (erased (Elab s))` or `Rejected (erased (Fails s))`,
   with an erased exclusivity lemma, is accepted, and packaged as a goal it
   passes `--goal proved` (05 F2, F3).
4. **Fuel-free shapes exist, with limits.** A total step looped by the
   `Program` driver runs with no fuel counter (02 §2.6, with a fixed
   oracle function and a step counter, now `proto/review2/machine_fn_oracle.sl`,
   which prints `imm 1` (02 second review note 8); 03 F5; 05 F6). With `--eval-fuel 1000`, a
   93025-step computation finishes when cut into `Program` steps and fails
   with `out of fuel` as one call, in both implementations (03 F5).
   Recursion on an erased `Halts` derivation (Bove–Capretta) is accepted,
   but a caller must supply the `Halts`: a written-out term, a per-input
   proof, or a fuel run that has already done the work (05 F4). Limits,
   all tested: a continuation closure of one fixed-level type with no
   decreasing argument cannot call another, though with an erased
   `subterm` counter in its type it can, as runtime closures (03 F4.1,
   corrected in 03 review note 14) and as erased invariants (06 F4.1); a
   closure whose level is packed beside it can be built but not applied
   by the stepper (06 F4.2); a CPS `bind` with counters, and
   level-indexed continuations, are untested (03 F4.1); a function
   cannot iterate `Program` steps itself (03 F4.2); every function a step
   calls must be minted before the program's level (03 F4.3, 05 F6); and a
   driven run's result is held only by the run's own later steps (as
   `drive.sl`'s `Done` branch holds it): no compile-time code and no `qed`
   can obtain it, so it cannot serve a `--goal proved` run (05 F6, second
   review note 5).
5. **`slot-eq` makes acceptance depend on the implementation.** §67:
   "`ENone` proves nothing, so an implementation may always answer it, and
   which one a call answers may differ between runs." A run-position
   `comptime-match` on `ESome` is accepted by both implementations (01
   §3.8; 05 §2.2); that an `ENone` implementation would reject it is
   inferred from §67, not observed. In practice answers already differ:
   `(add 1 2)` against `3` is `ENone` in the reference interpreter and
   under `slc --interpret`, and `ESome` in the binary that either the
   reference or slc builds with `--build` and externs (02 §2.4, second
   review note 5); two run-position `(str-append "a" "b")`
   (`slot_eq_share.sl`) are `ESome` only in slc's native (ocamlopt) build,
   and `ENone` under `slc --build --byte`, `slc --interpret`, and the
   reference, which 04 attributes to ocamlopt 4.14.1 sharing equal
   immutable constants, as its `share.ml` shows for tuples. slc's
   `bootstrap.sh` compares tests built with `--byte`, so it would not see
   such a difference (04 §2.5, second review note 7). 02's `const_share.sl`
   (two run-position `(MkBox 5)`) answers `ENone` in the reference and slc,
   built and interpreted (02 second review, unsure points).
6. **What DESIGN.md does and does not fix about evaluation order.** Fixed:
   eagerness (§31); in run position, "the forms inside a form run before it
   does" (§27), and with §6's "The head is elaborated first", a head that
   is a form runs before the arguments (reading, 02 §2.2); and, as 02
   reads it, world effects are ordered by the unique `World` (02 §2.2
   item 5). Not fixed in general:
   the runtime order of body statements (though §61 presumes written order
   in one case), sibling arguments, `values` entries, and several §15
   bindings before one statement. §15 ("behaves as if it were first bound
   ... placed just before the statement or final form that contains the
   call") fixes timing only if "behaves as if" covers time; read that way it
   puts a hoisted argument before a form head, which the reference's
   `--extract` does not do (02 §2.2, rough edge 10). Elaboration order is
   separately observable through gensym numbers (01 §3.6, tested on both
   implementations). Order observers in the abstract machine, per 02 §2.3:
   crashes, stuck states, divergence, and cost via the `Measure` request;
   order-independence otherwise is an unproved conjecture.
7. **Extern mode changes acceptance by DESIGN.md's own text.** §35: "with
   externs too, `(slot-of k)` is tag slot `k`". `proto/dyn/tagslot.sl` is
   accepted with externs and refused under `--no-extern` (02 §2.5). A spec
   that ran the `Nat` model would have to choose a word per tag slot (02
   Q6).
8. **Compile-time fuel and crashes.** DESIGN.md does not mention fuel (03
   F1, by grep). Both implementations refuse a run-position form whose run
   crashes (MANUAL.md `--eval-fuel`; 01 decision 7). slc's only fuel
   known to change a verdict is its interpreter's depth bound (default
   1000000000, fresh per run-position form, macro run, and interpreted
   `Program` step); `merge-opens` (03 F3 row 6) would accept early if its
   bound were too short, which 03 believes it is not, unproved (03 §1,
   second review note 5). The reference has no bound by default (03 F3). The
   10000-expansion cap of §62 carries real weight: a macro whose output
   calls itself is refused at the cap (tested), and in 01's reading would
   otherwise expand without end (01 §3.5).
9. **slc has no spec relation to retrofit against.** About 6% of its
   ~18,650 lines are erased lemmas, almost all in the libraries; the
   elaborator, interpreter, and emitter are trusted plain code for
   correctness; there are 20 `"internal:` sites; and the emitter trusts
   refutation ("A wrong refutation would misdispatch silently here") (04
   §2.2, §2.5).
10. **slc printer defect, confined to `show-at` (reproduced in both
    reviews).** `slc --interpret deep.sl` on a 100003-element list prints
    49,999 `Cons _ 0` and then `Cons _ _ _)`, because `show-at`'s 100000
    depth budget is spent twice per nested field. Under §45, `_` is for a
    union with more than one constructor, erased fields, cells, slots,
    functions, opaque proofs, and values with no readable `Matchable`, so
    this is a wrong value, not a §31 crash ("A crash produces no value,
    never a different one") (04 §2.3, review note 2). `show-at` feeds
    `slc --interpret`'s final printer and, through `show-typed`, the
    `comptime-match` mismatch message (`elab.sl:4784`) (04 §2.3) and the
    entries `dump-context` reports (`entry-value`, `elab.sl:4890`; found
    by this file's third review, which saw the same cut in
    `proto/review2/00_dump_deep.sl`, a 60000-element list). The OCaml printer
    slc emits has no value-depth bound (its `show-fuel` bounds only
    printer generation, falling back to `?`): compiled slc output
    (`deep.sl`, and `proto/review2/04-deep-fn.sl`) and the reference
    print all 100003 elements, byte for byte alike. The defect also
    contradicts `self/README.md:254-258` ("never a wrong answer
    silently") (04 §2.3, second review notes 2 to 4).
11. **Output-end risks in slc.** The emitter needs call and constructor
    arguments to be atoms, which nothing types (an extern template would
    evaluate a non-atom twice; the templates state the assumption,
    `ffi_templates.txt:4`); `-imm` FFI operations bypass OCaml's write
    barrier (safety unchecked); the `Slots` implementation does not search
    with `slot-eq` as §69's models do, but hashes raw block addresses
    (`Obj.magic`, `ffi_core.ml:336`) and detects GC moves by a sentinel
    and the compaction count, checked only by tests; `Bytes.unsafe_to_string`
    on the argument (`bytes-str` and its template; the other two sites
    convert a fresh buffer) relies on uniqueness being sound; tail calls
    with 20 arguments were checked only on amd64 with OCaml 4.14.1 and no
    flambda, where they held (04 §2.5, second review notes 5, 11, 12, 22).
12. **`mini/` gaps.** A malformed shape has no derivation and
    `elab-program` can answer `ProgramStuck`; keywords are reserved `RKey`s
    though §19 says special forms "may be shadowed"; `Sexp` has no `Pos`
    (01 §3.7, §3.10; 04 §2.4). 04 reads owner statement 3 as needing
    `Stuck` refuted.
13. **Parameterization works by indexing.** A relation can be an erased
    `TyCtor` parameter, and a `(Model R)` record indexed by it is accepted;
    a field can be used in types inside a body after `let-match`, but not
    named in a signature (05 F7). Generic code can take apart a derivation
    of a parameter relation when the relation's constructors and an erased
    `Matchable` are passed in, by `open-adt` then `let-match`
    (`proto/review2/05_generic_match.sl`, accepted; 05 second review note
    4, which narrowed 05's earlier "cannot"). 05 F3's one-block constraint
    is specific to `Certified`'s single level: an ADT with a level per
    field accepts two blocks (05 second review note 13).
14. **The role of "`unique` is the sole reference".** Not needed for
    compiler correctness against a mutating heap-machine spec; it is what
    connects that machine to the tree reading of values the fact table
    relies on (05 §6, a reading).
15. **Source details are observable.** Macro positions expose columns, which
    are 1-based byte counts in both implementations: a two-byte `é` before
    the call gives column 41 for 40 characters (`pos_bytes.sl`; 01 §3.9,
    second review note 5). In the two programs tested, the reference
    reported only the first error and slc reported later ones too (01
    §3.7). After an error slc still runs some run-position code (a binding
    of `(Zero)` is computed and read by a `comptime-match`), but a call
    gives no `Settled` result and a macro bound after the error is not
    dispatched; why was not traced in slc's source (01 §3.7, second review
    note 1, which retracted "slc stops running compile-time code after an
    error"). With two files where the second has a syntax error, the
    reference prints the first file's final value on standard output
    before the error, and exits 1 (01 §3.7, second review note 11).
16. **The intrinsic-derivation and `Program`-driver pattern works at toy
    scale in today's Sleight.** In 06, the type of `advance` is the
    soundness theorem: its `Halted` result carries `(erased (Runs m0 c0
    mf) d)` for the `c0` and `m0` of whatever erased trace the caller
    supplies, `TNil` or any other whose type fits (06 F2, second review
    note 2). In 07, the final `Verdict p` carries an erased `Elab
    [] p` or `Fails [] p`, and the statement, packaged as a `goal`
    mentioning only spec types, passes `--goal proved` on both
    implementations, for both a zipper and a replay checker (07 F2). In
    both, the only loop is the driver, with no fuel, and wrongly written
    components are refused at the faulty proof term (06 F2; 07 F5). The
    effort goes mostly into the spec and its determinism lemmas rather
    than the suspension machinery (06 F5; 07 F4). Neither spike models
    Sleight's own machine, `at` and cells, the oracle, or nested round
    trips (06 §6; 07 §6).
17. **What the spikes' theorems do not say.** Both are partial
    correctness. In 06, "stuck" carries no evidence, so a `step` that
    always answered `SStuck` would pass every type (06 §1, review note
    2). In 07, a `step` that always returns `More` passes the same goal,
    the exclusivity field is a lemma about the spec alone, and the `why`
    text a `Rejected` carries is unconstrained, so a correct `Fails` can
    come with any reason (07 §1, F7, review note 3, second review note 4).
    In both, the driver's type says nothing about the outcome, so the
    driver and its printed text are outside the theorem; 07's `drive.sl`
    calls `cstep` and `rstep` directly, not through a `Certified` value
    (06 F2, second review note 3; 07 F7, second review note 4). A `step`
    that itself loops is refused (07 review note 3). 07's exclusivity
    proof uses determinism of evaluation and of every lookup, and without
    it exclusivity can fail, as compiled for one nondeterministic variant:
    `proto/review2/07_nondet_spec.sl` (07's spec plus one rule `SNumUp`)
    with `07_nondet_both.sl` builds both derivations for one program, and 07's
    `det.sl` against that spec is refused at `step-det` (07 §1, F4, second
    review note 3).
18. **The output theorem cannot be "the same values, up to crash".**
    §42 excepts `slot-eq` from the model agreement, §67 lets its answers
    "differ between runs", and §69 extends the exception to `Slots`, so
    the spec run is nondeterministic there, and `slot_eq_share.sl` gives
    two different values (key finding 5). 04 now treats `slot-eq`'s
    answers as a second oracle beside `world-do`'s, and puts the theorem
    at most as "the compiled run's values are values some spec run gives,
    for the same `slot-eq` and world answers, up to crash"; 04 marks that
    shape itself as a proposal (04 §2.6, decision 5, second review note
    6 and unsure points).

## 3. Decisions for the owner

Merged from all seven files, ordered so that a decision comes before those
that depend on it; the spikes' new decisions carry sub-letters next to the
decision they relate to, and their other decisions are folded into
existing ones. Each says whether it needs DESIGN.md wording, which
under rule 12 the owner confirms word for word, or is only a choice for the
formal spec. Recommendations are the tracks', never decided.

### A. What the spec is about

**1. Where does the spec start?**
Options: (a) source bytes, with a small reader function in front of a
relation over `Raw`; (b) `Raw`, with the reader trusted; (c) a core
language after dispatch and expansion; (d) the reader as a parameter
satisfying a `Parses text raw` law (05 §4.4.3).
Recommended (01, 04): (a); 04 adds that the reader be proved early. Why:
owner statement 3 speaks of "source code"; positions are observable; a
core start leaves out head dispatch and macros, which (01's reading) the
paragraph of DESIGN.md on the language's aims makes central. 05 offers (d)
if the syntax is to be separated.
Depends on it: the statement of theorem 3 (decision 14), whether `Pos` is
in the judgment, and whether a trusted front end (route R2, decision 17)
can serve owner
statement 3. 04 now reads owner statement 3's wording as asking only
totality, which a total but unproved front end could give; a claim that
the verdict is the spec's verdict on the text needs the reader and the
expander proved, which R2 does not do (04 decision 2, second review note
19).
Formal-spec choice only. Context: 01 decision 1, §4.1; 04 decision 2;
05 §4.4.3.

**2. What does "parameterized the semantics" (owner statement 1) mean?**
Options (05 §4.4): (a) one fixed spec and compiler; (b) generic over a
model record (extern models, the nondeterminism oracle, the file system);
(c) also over the syntax (decision 1 (d)); (d) also over the prelude
(decision 16). On externs specifically, see decision 9.
Recommended (05): (b), with (c) if the syntax is to be separated. 04
recommends parameterizing over the extern table (decision 9).
Depends on it: the spec's signature, decisions 9 and 16.
Formal-spec choice only. Context: 05 decision 6, §4.4, F7.

### B. Making acceptance a function of the source

**3. Is the order of elaboration part of the language?**
It is visible through gensym numbers (§65 "counting from 1 over the whole
run"), the expansion count (§62), and which error comes first. DESIGN.md
fixes "The head is elaborated first" (§6), statements before the code
after them (§27), and that the macro world is "threaded sequentially
through all of elaboration" (§65), but no left-to-right order of items.
Options: (a) fix it; (b) leave it free, making acceptance a relation.
Recommended (01): (a), as head first, then items left to right, depth
first, each statement before the code after it, which is the reference's
order as tested.
07 adds, as its reading, that a positive `Fails` mirroring `Elab` and a
derivation zipper both need this order (07 F3, §5).
Depends on it: determinism (T3), decision 13's error content, and the
oracle (decision 5), whose answers are consumed in some order.
(a) needs DESIGN.md wording. Context: 01 decision 5, §3.6; 02 rough edge 12;
05 §2.2, rough edge 5; 07 §5.

**4. Is the runtime evaluation order fixed?**
Options (02 Q3): (O1) fix it in the spec: statements in written order,
§15 bindings before their statement in order of appearance, inner before
outer, then the head, arguments, `values` entries left to right, scrutinee
before branch; (O2) fix only what DESIGN.md fixes and make the spec a
relation over orders, which needs an order-independence (diamond) proof of
roughly the size of type soundness; (O3) O1 now, order-independence later
as an optional theorem that would license reordering compilers.
Recommended (02): fix it (O1/O3). Sub-questions for the owner: does §15's
"behaves as if ... placed just before" fix timing? If it does, a hoisted
argument runs before a form head, against what the reference emits and
the run-position reading of §6 and §27; 02 names "a form head, then the
§15 bindings" as the variant matching both. The brief's earlier proposal A
("sub-expressions left to right, head first") agrees with hoisting only
if applied after it (02 §2.2). 04 instead asks whether order is meant to
be unobservable, so that any order is correct (04 rough edge 1); 02 §2.3
lists observers (see cross-file item 2).
Depends on it: whether the compiler theorem is lock-step (cheap) or needs
confluence (expensive); slc's emitter would need checking against O1
(02 Q3).
O1 and O3 need DESIGN.md wording; O2 does not. Context: 02 decision 3,
§2.2, §2.3; 04 §2.5,
rough edge 1; brief proposal A.

**5. How is `slot-eq`'s nondeterminism handled?**
Options: (a) an oracle parameter, so the spec is a function for each
oracle; (b) a nondeterministic relation, with existence but no
exclusivity (T3 false outright); (c) fix the compile-time answer to word
equality; (d) forbid `slot-eq` in run position or a macro; (e) always
`ENone` (02 N3: `tests/slot_eq.sl` and the `Slots` implementations would
disagree); (f) always truthful (02 N4: both implementations fail it;
`slc --interpret` answers `ENone` for equal immediates in `imm_eq.sl`, 02
second review note 5).
Recommended by all three tracks that address it as a decision: (a); 04,
after its second review, also treats `slot-eq`'s answers as an oracle
beside `world-do`'s in its theorem shape and trusted base (key finding
18). The shapes differ:
01 a stream of answers, like the `read-file` oracle; 02 a step-count → bit
map where `ESome` needs the bit set *and* equal words, the theorem being
"some oracle exists"; 05 an oracle that also records crash points and file
contents, existentially quantified in the verdict and logged by the
compiler. 05 warns that an oracle allowed to choose `ENone` everywhere, or
crashes, lets a compiler reject more than it should while meeting T1 to
T3. See cross-file item 1 on whether 02's shape covers slc's compiled
answers.
Depends on it: T3, the statement of completeness, and decision 8.
(a) and (b) are formal-spec choices; (c) and (d) change the language and
need DESIGN.md wording. Context: 01 decision 6, §3.8; 02 decision 4, Q4;
05 decision 3, §4.2, §3 T3.

**6. What is a crash or fuel exhaustion during a compile-time run?**
DESIGN.md: "A real run may crash where the host cannot represent what is
asked of it" (§31); for `native-compute`, "a run that crashes is an error
at its argument" (§72); otherwise silent. Both implementations refuse such
a form. The tracks disagree:
- 01: the spec's machine never crashes (§31's "unlimited stack and heap");
  the agreement theorem allows a third compiler outcome `Crashed` that
  proves nothing. 01 itself notes two tensions: today `Crashed` is a
  rejection the theorem says nothing about, and for `native-compute` it
  departs from §72 unless the compiled run's outcome is an oracle input.
- 02 (C4): put an explicit depth bound into the compile-time spec, taken as
  compiler input, so that acceptance is a function of (source, bound),
  once the order and the `slot-eq` answers are fixed (decisions 4, 5);
  owner statement 3 would then hold per bound, provided the rest of
  elaboration terminates. 02 reads a depth bound as bounding steps, since
  there is no loop form (unproved). This departs from §31 at compile time,
  and heap exhaustion stays host-dependent (02 Q5 C4, second review note
  3).
- 01 and 02 recommend opposite treatments (01: never crash, plus a
  `Crashed` outcome; 02: a bound whose exhaustion rejects); after their
  second reviews each file cross-references the other (01 second review
  note 2; 02 second review note 4).
- 03: fuel exhaustion is not obviously a §31 crash ("cannot represent");
  treat `OutOfFuel` as an outcome outside the spec. The answer bears on
  whether slc's current behaviour conforms.
- 05: open. On 05's reading of §31 the spec has no crash, so the question
  is whether owner statement 3 is about the spec or also about an
  implementation, which "may crash"; and crashes must be kept out of the
  oracle, or completeness stated for the crash-free oracle.
- 04: open, as a sub-question of decision 10.
- 07: its toy rejects a stuck compile-time run (`FLetStuck`), but 07
  calls that a stand-in, not a proposal, and a stuck term is a different
  kind of failure from a §31 crash (07 decision 5).
Depends on it: the form of theorem 3 (decision 14), the oracle (decision
5), and whether slc's present rejection is conforming.
Needs DESIGN.md wording if crashes become rejections or a bound enters
the language (02 C4); a third compiler outcome is a choice for the
theorem only. Context: 01 decision 7; 02 decision 5, Q5; 03 decision 1;
04 decision 5; 05 decision 4.

### C. The spec's run

**7. Does the spec run post-erasure code?**
Options (02 Q1): (R1) post-erasure code, as §27 and §29 say; (R2) typed
code with erased parts skipped (R1 with the strip inlined); (R3) R1 but
performing skipped stores and calls, which departs from §37 and §39.
Recommended (02): R1. It mostly confirms DESIGN.md; the stripped-mode
concern of owner statement 6 becomes a type-soundness obligation over
stripped code with a heap typing. Stripping depends on the fact table
(§39's call skipping), so it is an output of elaboration. The reading of
owner statement 6 as "the spec's run is a mutating heap machine on code
with erased positions removed" is the earlier session's and is not
confirmed (brief).
Depends on it: what elaboration outputs; the statement of type soundness.
Formal-spec choice for R1 and R2; R3 departs from §37 and §39. Context:
02 decision 1, §2.1; 05 §3 T7.

**8. Machine state and addresses.**
Options (02 Q2): (A1) `Imm n | Ptr a`, abstract never-reused addresses
compared only for equality, mutable blocks, explicit continuation, total
step, `Program`-driven (the brief's proposal B plus immediates and §33's
representation identities); (A2) natural-number addresses as in slc; (A3)
everything boxed, as slc's interpreter, where §33's identities then hold
only through a separate map from a block to its word, as slc's
`word-of-block` does; `slc --interpret tagslot.sl` does read `at` back
through a tag slot (a cost, not an impossibility; 02 Q2, second review
note 2).
Recommended (02): A1. Open sub-questions DESIGN.md does not answer: what
word an unapplied constructor is, and what an extern type's `Matchable` is
under `--no-extern` (02 Q2 table; §29 says a `Matchable` is "the FFI's
wrapper for an `extern` type and nothing otherwise"), and whether two separately built immutable values may share one
word (04 rough edge 4; cross-file item 1).
Depends on it: decision 5's oracle shape, T6.
Formal-spec choice, unless the sharing question is answered in DESIGN.md.
Context: 02 decision 2, Q2; 04 §2.5, rough edge 4.

**8a. Is the spec's compile-time run a small-step relation over the same
machine the compiler steps?**
Options (07 Q2): (a) yes, so the evaluator side of the proof is a list of
step proofs (07 F4); (b) big-step, or a different machine, closer to
DESIGN.md's prose but needing a simulation proof that 07 expects (its
reading) to dominate the effort.
Recommended (07): (a), if the evaluator part of the proof is to stay
small. In 06's toy, big-step `Runs` and small-step `Star` agree for runs
that end on the empty stack, and 06 reads the choice as one of
presentation there (06 Q1.4).
Depends on it: decision 8, and the size of T5.
Formal-spec choice only. Context: 07 decision 2, Q2; 06 Q1.4.

**8b. Should the next spike use the unique `Array` heap and abstract
addresses?**
06's heap is `many` lists with functional update, and an address is a
position (06 Q3). Recommended (06): yes, before scaling, since 02
recommends abstract addresses (decision 8, A1) and owner statement 6 says
the owner suspects the spec's run should be a mutating heap machine from
the start. That `Array`'s API, indexed by `Nth` and `SetNth`, would carry
06's proofs over is untested (06 §6).
No DESIGN.md wording. Context: 06 decision 4, Q3.

**9. Externs in the spec.**
Options: (E1) run every model, with each implementation's agreement a
hypothesis (02 Q6); (E2) `Nat` a machine primitive on immediate words,
every other model run (02); (E3) every extern primitive; (P) parameterize
the semantics by an extern table, so agreement becomes a separate testable
obligation (04 decision 7, 05 §4.4.2); (X) one agreement axiom per
implementation, 103 functions and 7 types (04 §2.6).
Recommended: 02 recommends E2, because under the `Nat` model §33's "the
word of the `Nat` of its position" and §35's tag-slot literals have no
meaning without a further choice (key finding 7). 04 and 05 recommend
parameterizing. The two may combine, but no track says how.
Depends on it: decision 2, the trust base, and whether `--no-extern`
checks the same language (cross-file item 6).
Formal-spec choice; 02 rough edge 4 asks whether DESIGN.md's extern-mode
dependence is intended. Context: 02 decision 6, §2.5; 04 decision 7,
§2.6; 05 decision 6, §5; 01 decision 8.

**10. What may a compiled run do differently at runtime: crash where?**
Options (02 Q5): (C1) CakeML-style "the spec's behaviour, or a prefix
ending in a crash" (a compiler that always crashes satisfies it); (C2)
crash only at named resource events (allocation, stack push, an FFI
primitive past `array-limit`, `bytes-limit`, or the U62 host check); (C3)
a spec indexed by a heap bound H and a depth bound D, with a theorem for
a host with at least c·H heap and c·D stack.
Recommended (02): C2, with C3 as a later strengthening. 04 asks a related
question: is the outcome space "a value some spec run gives, or a crash"?
§31 and §42 seem to force "up to crash", and `slot-eq` makes "the same
value" too strong (04 decision 5, second review note 6; key finding 18).
Depends on it: T6.
Formal-spec choice; 02 rough edge 5 asks what a crash does to effects
already performed. Context: 02 decision 5, Q5; 04 decision 5.

**11. What happens when the spec goes wrong (absurd code reached, stuck)?**
Options: (S1) a defined `abort` outcome that compiled code must also
produce, as both implementations already abort (02); (S2) undefined after
a stuck state (02); (W1) T6 assumes the spec run does not go wrong,
CompCert-style (05); (W2) going wrong is a behaviour after which anything
is allowed (05).
Recommended: 02 recommends S1; 05 states W1 and W2 without recommending
one, and expects stripped-run safety to stay a meta-theorem either way.
See cross-file item 9. 06 asks whether "never stuck" is a target for the
spec's own machine; if so, it names a typing invariant (06 Q2.2) as the
route that also serves type soundness, and positive failure evidence
(Q2.1) as cheaper for a toy, without recommending either (06 decision 3).
Depends on it: T6, T7.
Formal-spec choice; DESIGN.md does not say what reaching absurd code at
runtime does (02 rough edge 6). Context: 02 decision 7, Q7; 05 decision
7, §3 T7.

**12. Compile-time values embedded in the output: trees or heap graphs?**
Options: (V1) agree as trees; (V2) agree as heap graphs up to renaming,
keeping sharing. Recommended (02): V1 unless a reason for V2 turns up;
whether V1 suffices for slot facts derived at compile time is unverified.
Formal-spec choice; 02 rough edge 8 asks the same of §42's "the same
values". Context: 02 decision 8, Q8.

### D. The theorems

**13. Intrinsic statements, positive `Fails`, and what a rejection
carries.**
Questions: (i) state theorems intrinsically (05 recommends yes; graph
relations only where wanted); (ii) make `Fails` positive: both 01 and 05
recommend that, but differ on the shape (cross-file item 11): 01 makes
`Fails` the `Err` outcome of one total relation, so exclusivity follows
from the relation being functional, and rejects a separate `Fails`
relation as duplication; 05 has separate `Elab` and `Fails` relations with
exclusivity a separate lemma; (iii) what a rejection
carries: (a) only "rejected"; (b) the first error's position and
macro-call trace; (c) also a structured reason, including the text §4 and
§28 require; (d) full message text. 01 recommends (b) in the main
theorem, (c) available in the relation, never (d); 05's sketch carries a
`(many (Diag) msg)`. Malformed syntax must be a positive error, not "no
derivation" as in `mini/` (01 §3.7). 07 compiled 05's shape (separate
`Elab` and `Fails`, exclusivity a lemma) and recommends that `Fails`
mirror `Elab` premise by premise ("fails at premise k after 1..k−1
hold"), so that one context serves both and exclusivity is a plain
induction; that fixes the order of premises (decision 3) (07 decision 3,
F3). 07's mismatch rule carries the value, which bears on (iii) (07 §5);
in 07's toy the `why` text of `Rejected` is unconstrained by the type, so
a reason carried as free text is not covered by the theorem (07 second
review note 4).
Depends on it: the architecture of every compiler pass; how much of
decision 3's order the spec must pin down.
Formal-spec choice only. Context: 05 decisions 1, 2, §3; 01 decision 4,
§4.3; 07 decision 3.

**14. The form of theorem 3 (owner statement 3) and the hypothesis H.**
Options, as the tracks put them:
- 01: (a) relative to H, stated so that (b) a fuel parameter with a third
  outcome `OutOfFuel` is a corollary; (c) a coinductive "diverges"
  outcome. Recommends (a).
- 03: (i) "H(src) ⇒ the driver reaches `Exit` with accept or reject", a
  statement about the driver, paired with (iii) an internal Sleight
  function that takes erased H(src) evidence; or (ii) three outcomes with
  `OutOfFuel`. Recommends (i).
- 05: (a) meta-theorem only; (b) Bove–Capretta `compile-h` taking an
  erased `(Halts o src)` (one reading of owner statement 4(ii) as a type,
  not callable in practice without a proof or a prior fuel run); (c)
  honest fuel whose `OutOfFuel` carries a proof that the spec run has not
  finished after `f` steps (one reading of 4(i)); (d) a step machine whose
  invariant gives T1/T2. Recommends (d) for the running compiler plus (b)
  or (c) on the same step, uniform totality left meta; alternative: a
  compile-time resource budget in the language, under which owner
  statement 3 holds literally (05 §4.3 option 4, a language change).
- 07: the packaged theorem should include completeness, relative to
  per-source evidence (07 Q3(a), not written), since without it a
  stepper that never answers satisfies the statement (07 decision 4, F7;
  key finding 17).
Sub-questions: which H? Owner statement 4(ii)'s "every accepted
compile-time form's spec run halts", or the broader "every compile-time
run in the spec halts" that 01 and 03 F7 use (cross-file item 5). And is
H stated over evaluation only, with `read-file` and `native-compute`
axiomatized as terminating (03 recommends so)?
Depends on it: decision 6; decision 18; whether the deriving function for
elaboration takes fuel.
Formal-spec choice, except the resource-budget alternative, which needs
DESIGN.md wording. Context: 01 decision 2; 03 decisions 2, 4, Q2, F7; 05
decision 5, §3 T4, §4.3; 07 decision 4.

**15. Which flags are spec parameters, and is the expansion limit one?**
01 recommends in the spec: prelude on or off, extern on or off,
`--fn-same`, `--goal`, the `--comptime-unconfine` names, the FFI table's
names and arities, and the expansion limit as a parameter `N` (10000 by
default); not in it: `--eval-fuel`, `--no-native`, `--hints`, and
`--warn-unused`; acceptance ignores warnings, and `--warnings-as-errors`
is a driver policy the theorem does not cover. 01's own review is unsure
about excluding `--warn-unused` and `--no-native`. 03 and 04 treat §62's
cap as a fixed language rule rather than a parameter (cross-file item 4).
Open (03): §62 does not say that reaching the cap is an error; both
implementations make it one.
Formal-spec choice, except what the 10001st expansion does, which needs
DESIGN.md wording. Context: 01 decisions 3, 8; 03 decision 5; 04 §2.3.

**16. What is the prelude to the spec?**
Options (01): (a) a fixed elaborated snapshot Σ0; (b) the shipped text as
input; (c) any prelude text, with the spec finding `Nat`, `String`,
`Macro`, `Raw`, and so on at its end, `--no-prelude` being the empty one,
qualified: under §42 `--no-prelude` also allows `extern` anywhere, while
with a prelude it is allowed only in the prelude, and whether an empty
prelude text should behave as `--no-prelude` is left to the owner (01
decision 9, second review note 4).
Recommended (01): (c), since (a) seems to need the 2881-line prelude
elaborated inside Sleight, practically by reflection, which relies on the
evaluator the proof is meant to cover. 05 §4.4.4 instead finds being
generic over the prelude "too wide", since SOUNDNESS.md makes the
prelude's models and `def-prim` signatures assumptions (cross-file item
3). Related: whether the spec includes INTERNALS.md's `def-prim` and
`def-opaque`, which §54's registry omits (04 rough edge 3).
Formal-spec choice. Context: 01 decision 9, §4.5; 05 §4.4.4.

### E. The compiler

**17. Which route?**
Options (04 Q1): (R1) retrofit slc to return derivations (very high
effort, serial on one `def-fns` block); (R2) a certified kernel behind
slc's unproved front end (the front end stays trusted for meaning, and
the kernel must re-run run-position forms); (R3) a new compiler written
spec-first as deriving functions beside the relations, `mini/`-style,
reusing slc's proved libraries; (R4) translation validation of slc's
output by a proved checker.
Recommended (04): R3, with R4 only at the output end, and slc kept for
differential testing; reasons: work parallelizes per judgment, the round
trip is designed in, and slc has no relations to retrofit against
(key finding 9). Effort is guessed at tens of thousands of lines. 03's
fuel recommendations assume work on slc (cross-file item 7).
Depends on it: everything in this group. Formal/engineering choice; no
DESIGN.md wording. Context: 04 decision 1, §3 Q1; 03 decision 3.

**18. How is fuel kept out of results and theorems?**
Options and recommendations, which differ by track:
- 03: (a) the whole compiler as a defunctionalized state machine stepped
  by `Program` (very high cost for slc, moderate for a new kernel); (b)
  iterative deepening, retrying with 2n (cheap stopgap; needs a
  monotonicity lemma and rolling back §62's count and §65's gensym
  counter); (c) keep fuel and make `OutOfFuel` a distinct outcome; (d) a
  normalizing interpreter (ruled out by the diagonal for all sources, if
  it is a non-erased function on source text with no further evidence);
  (e) hybrid: a stepped interpreter run inline in bursts, suspending to
  the driver and replaying the current top-level form, so no result
  depends on the burst size. Recommends (e) for slc, (a) only for a new
  kernel built that way, (b) as stopgap. Converting the interpreter to a
  stepped machine is needed by (a) and (e).
- 04: (F1) iterative deepening at the driver, (F2) an explicit-stack
  compiler with no fuel anywhere, (F3) fuel in the theorem. Recommends F1
  now, F2 only if fuel should go from the code too; F2 must be decided
  before R3 starts.
- 05: recommends a step machine for the running compiler (decision 14).
Closures of one fixed-level type can call one another only with a
decreasing argument in their type, such as an erased counter (key
finding 4).
The brief lists "minimize fuel use" among the owner's goals; it bears on
all of these.
Depends on it: decision 17, the architecture of every elaboration
function. No DESIGN.md wording. Context: 03 decision 3, Q1; 04 decision
3, Q2; 05 decision 5.

**18a. Resumable checker: a derivation zipper, or direct style with
replay?**
Options (07 Q1): (a) zipper: the checker state is the elaboration
context `Ctx` plus, while waiting, the evaluation context `Reach`, both
erased, advanced by one total step per `Program` step; (b) direct style,
replaying from the start with a proof-carrying oracle of answers; (c)
inline bursts with replay only on overflow (03's (e)), untested, which
07 expects to need (b)'s proof.
Recommended (07): the zipper for a new certified kernel, and replay only
if slc itself is retrofitted, which matches 03 decision 3's split. Why:
both compile; replay adds a proof-producing equality on requests (on
terms and environments in the toy, probably on heaps in full Sleight, by
07's reading) and, by 07's estimate from the code, about quadratic work;
the zipper costs rewriting the elaborator into frames, which 07 expects
to cover most of elaboration.
Depends on it: decisions 17 and 18. No DESIGN.md wording. Context: 07
decision 1, Q1, F3, F6.

**18b. The invariant of a certified stepper: an erased trace, or a
counter-indexed closure?**
Options (06 Q1): an erased trace folded at the halt by a per-step lemma
(built); a closure at one fixed level with an erased step counter (built
in review); a first-order derivation context (untested; 07's `Ctx` is,
on this summary's reading, of this kind for elaboration); small-step as
the spec.
Recommended (06): the trace, as a working hypothesis; 06 calls the
choice between it and the counter closure one of presentation.
Depends on it: whatever relies on a certified stepper. No DESIGN.md
wording. Context: 06 decision 1, Q1, F2, F4.1.

**18c. Should a function be able to apply a closure whose level is
packed in its argument?**
As DESIGN.md stands (§17, §18), 06 found such a closure can be built but
not applied by code whose level was minted earlier (06 F4.2). 06 proposes
no change, since a fixed-level closure with a decreasing erased argument
works instead (key finding 4). A change would need DESIGN.md wording.
Context: 06 decision 2, rough edge 1.

**19. Judgment shape and staging.**
Recommended (01): the layers and Σ/Γ split of 01 §4.2, with the run
relation a parameter of elaboration where possible, so elaboration's
metatheory is proved once for every lawful run (unverified that a Sleight
ADT can usefully be indexed by a relation-valued `TyCtor` this way; 05 F7
is related evidence). Open within 01: whether run-position facts sit in
Γ or in the threaded Σ, which §65's macro world includes (01 §4.2, second
review note 3). Staging: reader; `mini/` recast in the final shape;
`Settled` and the round trip; erasure and uses; externs, macros, and the
prelude; slots and cells; sugar, goals, and `native-compute`. 01 finds S2
and S3 workable in either order.
Depends on it: how much of `mini/` is rewritten. No DESIGN.md wording.
Context: 01 decisions 10, 11, §4.2, §4.6.

**20. Where does the proof stop at the output end?**
Options (04 Q3): (O1) the post-erasure IR, trusting the emitter, about 830
lines of OCaml runtime, the templates, and OCaml; (O2) model the untyped
OCaml subset slc emits, an untyped word-and-block heap machine; (O3) a new
target (bytecode VM or C), which departs from what `self/README.md`
reports as an owner decision about `lib/extract.ml` (unconfirmed, not in
the brief's list); (O4) re-parse the emitted text with a proved parser.
Recommended (04): O1 now, O2 + O4 later; IR call and constructor
arguments atoms by type in any case.
No DESIGN.md wording. Context: 04 decision 4, §3 Q3, §2.5.

**21. `native-compute`.**
Options (04 Q4): (N1) exclude it; (N2) an oracle premise; (N3) the same
trust as the output end, with N2's wording as the premise; (N4) validate
by re-running in the proved evaluator. Recommended (04): N3. 02 C4 treats
its answer as an oracle or excludes it; 01 decision 7 notes §72's "an
error at its argument" (decision 6).
No DESIGN.md wording unless decision 6 changes §72. Context: 04 decision
6, Q4; 02 Q5 C4.

**22. Which checker's PASS is the trust root?**
Options: (B1) both `lib/` and slc check the proved compiler, noting that
they share `lib/ffi_core.ml` and a design lineage; (B2) the proved
compiler checks its own proofs (circular only in the benign sense).
Recommended (04): B1; 05 lists `lib/`, slc, or both without
recommending. Either way, Sleight's logic being sound in a sense stronger
than consistency, and the checker, stay in the trust base (05 §5).
No DESIGN.md wording. Context: 04 decision 8, Q5; 05 decision 8, §5.

**23. Prove "`unique` is the sole reference" and full-semantics safety
inside Sleight?**
05 thinks it plausible and worth it, as invariants of the spec's
reachable states; it justifies reasoning with `is` facts about a run but
does not settle the stripped run's (E), which still needs (T). 06 Q2.2
calls a well-formedness invariant for its toy "type soundness of the
object language" and "the shape the full Sleight machine would need
anyway" (decision 11).
No DESIGN.md wording, though 02 rough edge 7 asks what "the only
reference" (§13) means. Context: 05 decision 9, §6.

## 4. Rough edges in DESIGN.md

Merged and phrased as questions. None is resolved here.

1. **Order of elaboration.** §65 threads the macro world "sequentially
   through all of elaboration" and gensym counts "from 1 over the whole
   run", but only "The head is elaborated first" (§6) and §15's hoisted
   bindings "placed just before the statement or final form that contains
   the call" fix part of the order; neither orders two arguments. Is the
   left-to-right, depth-first order of items part of the language? (01
   §5.1; 02 §5.12; 05 §8.5; 07 §5, second review note 6, which notes that
   a zipper or a mirror-shaped `Fails` needs it.)
2. **Runtime order of body statements.** §27 orders statements only in run
   position ("This nests ..."). Is written order meant at runtime? §61's
   "The write stores `h` before the call" seems to presume it, or reads
   it off §19's tail requirement. (02 §5.1, §5.11.)
3. **§15 and heads, scrutinees, and several bindings.** §29 speaks of "the
   elaborator's own binders for its head, arguments and scrutinee (§15)",
   but §15 names only arguments. How are several bindings "placed just
   before the statement or final form" ordered among themselves? (02
   §5.2, §5.3; 04 §5.1.)
4. **Does §15's "behaves as if" fix timing?** If so, `((pick) (h n))` runs
   `(h n)` before `(pick)`, against §6's "The head is elaborated first"
   with §27's "runs as soon as it has been elaborated" in run position.
   (02 §5.10.)
5. **Is evaluation order meant to be unobservable?** 04 now notes that
   order decides between a crash and divergence when one argument does
   each. (04 §5.1, second review note 20; compare 02 §2.3.)
6. **`slot-eq` and acceptance.** §67's "which one a call answers may
   differ between runs", with `slot-eq` usable in run position, lets
   conforming implementations disagree on accepting a text. Intended,
   given owner statement 3? (01 §5.2; 05 §8.1.)
7. **Separately built values sharing a word.** §36 says "two separately
   built cells with equal contents are `is`-equal and are two blocks";
   may two separately built immutable values share one word? (04 §5.4.)
8. **Crash at compile time.** Outside §72, is a §31 crash in a
   run-position form an error at the form, or neither acceptance nor
   rejection? Is a fuel bound a crash "where the host cannot represent
   what is asked of it"? DESIGN.md does not mention fuel. (01 §5.3; 03
   §5; 04 §5.2; 05 §8.2.)
9. **Crash and earlier effects.** §31's "A crash produces no value, never
   a different one" does not say what happens to world effects already
   performed, or where a crash may occur. (02 §5.5.)
10. **Reaching absurd code at runtime.** Not specified; both
    implementations abort (`lib/eval.ml:66`, `self/runtime.ml:1`). (02
    §5.6, second review note 10.)
11. **"The evaluator" in §27 and §29.** Is it, in a formal spec, the
    spec's own run, and does it run extern models or implementations?
    §42's "running the models instead of the implementations must give a
    program the same values" suggests the models. (03 §5; 04 §5.5; 05
    §8.3.)
12. **`Nat`'s word under models.** §33's "the word of the `Nat` of its
    position" presupposes one word per `Nat`, which the model's `Succ`
    blocks do not obviously have, and §33 requires the extern `Nat`'s
    FFI to meet it only "With externs on"; §35 gives tag slots for
    literals only "with externs too", so acceptance depends on extern
    mode (tested). Then §42's "the same values" has nothing to compare
    for a program refused under the models. Intended? (02 §5.4.)
13. **"The same values" in §42**: compared as trees or with sharing? (02
    §5.8.)
14. **"The only reference" (§13).** Does "reference" exclude slot words
    (§38 "inert") and the `Stale` word an array keeps (§44 "the array may
    keep the plucked value alive")? §36's reading-back makes a reference
    from a consumed binder's word. (02 §5.7.)
15. **The FFI table in acceptance.** "The prototype's FFI is a fixed table
    keyed by the declared name" (§42) puts one implementation's table into
    the definition of acceptance. (01 §5.9.)
16. **`def-prim` and `def-opaque`.** §54 opens "Every special form, as a
    constructor of `Special`" but omits them; the prelude uses them and
    INTERNALS.md specifies them. Is INTERNALS.md part of the language for
    a formal spec? (04 §5.3.)
17. **Where `Settled` comes from.** §29: "Nothing else creates a
    `Settled`". Are the built-in `Special` entries (§42), which §6 needs
    `Settled`, and the fresh entries that `mint-settled` and
    `mint-settled-erased` mint and that `settled-ty-apply` and
    `settled-val-apply` give a handle to (§65), among its three sites? A literal's entries are "as if minted by
    run-position forms" (§45), which ties them to site 1. (01 §5.12,
    second review note 12.)
18. **The expansion cap.** §62: "At most 10000 expansions run in one
    run, every file on the command line included." Does the prelude
    count? Is the 10001st an error? Are §62 and §49's "at most 1024"
    precedents for a compile-time evaluation budget, or one-offs? (01
    §5.7; 03 §5; 05 §8.6.)
19. **Reader details.** What is `042` (§1 says digit atoms are numerals,
    §45 forbids a leading zero)? Is `\q` allowed by "Any other byte ...
    stands for itself" (§45)? What unit are `Pos` columns (§42 says only
    "a line and a column")? The reference refuses the first two;
    columns are 1-based bytes in both implementations. (01 §5.4–§5.6.)
20. **Multiple errors.** DESIGN.md is silent; the implementations differ
    after the first error. (01 §5.11.)
21. **`--warnings-as-errors`** is in §4, but which warnings exist is in
    WARNINGS.md, so acceptance under the flag depends on text outside
    DESIGN.md. (01 §5.8.)
22. **`dump-context`** is defined by reference to MANUAL.md (§27, §54).
    (01 §5.10.)
23. **`read-file` that never ends.** What of a FIFO inside the source
    directory (§65)? (03 §5.)
24. **The driver as an implementation shape.** §42's "an unbounded
    interaction is the driver's loop over total functions": may an
    implementation itself be such a loop? (03 §5.)
25. **Character literal bounds.** §45's bound proof is "asserted rather
    than decided", so it is an axiom of the spec, unlike numerals. (05
    §8.4.)
26. **Tests fix free behaviour.** `tests/slot_eq.sl` expects `ESome` where
    §67 allows `ENone`. Not a contradiction. (02 §5.9.)
27. **Packed-level closures.** §24 makes "a function, of `Fn` or `UniqueFn`
    type" first-class data, but a function stored with its level packed
    beside it can be built and extended, and, as far as 06 found, not
    called by code whose level was minted earlier (§17, §18). §57 shows
    the factory pattern for one direction; is the other meant to be
    impossible? (06 §5.1.)
28. **Diverging run-position forms.** DESIGN.md does not mention
    divergence (07 searched). §17 says "Termination rests on levels",
    §42 calls an unbounded interaction "the driver's loop over total
    functions", and §62 caps expansions; together they suggest functions
    are meant to halt, but no text says outright whether every
    compile-time run halts, or what a checker that never returns means
    for acceptance. Whether §17's levels, with §10's `Type : Type` and no
    positivity, keep every run-position form from diverging is unsettled.
    (07 §5, review, second review note 7.)
29. **The text of a `comptime-match` mismatch.** §28: "On a mismatch, the
    error prints the expected constructor and the actual value". If a
    rejection carries its reason (decision 13), the `Fails` rule must
    carry the value; is the printed text part of the spec? (07 §5.)

## 5. Cross-file inconsistencies

Listed, not resolved.

1. **Addresses versus compiled `slot-eq`.** 02 recommends never-reused
   abstract addresses (A1) and an oracle under which `ESome` needs equal
   words (N1), and says "there is an oracle" covers every implementation
   seen tonight (02 decision 4). 04 found slc's native (ocamlopt) build
   answering `ESome` for two separately computed `(str-append "a" "b")`,
   because ocamlopt shares equal constants; `slc --build --byte`, `slc
   --interpret`, and the reference answer `ENone` (04 §2.5, second review
   note 7). Under A1 those are two addresses, so no N1 oracle would explain
   the native answer. 04 itself says it is a mismatch "only if the spec
   says that every allocation takes a never-used address". 02's second
   review ran slc (on `proto/dyn/`, `imm_eq.sl`, and `const_share.sl`);
   its notes do not mention `slot_eq_share.sl`. It now hedges N1 as holding only if a
   compiled `ESome` never meets two words the abstract machine keeps
   apart, and saw no such sharing for two `(MkBox 5)` (02 second review
   note 5, unsure points). So the two files now agree on the condition;
   04's native result is a case that meets it.
2. **Is evaluation order observable?** 04 rough edge 1 suggests it may be
   unobservable, since effects are ordered by the unique `World` and "a
   crash and divergence both produce no value". 02 §2.3 lists observers:
   whether a write happens before a crash, divergence, stuck states, and
   cost through the `Measure` request (which also answers words
   allocated, 02 second review note 7). 04's second review added one
   observer to its own rough edge: order decides between a crash and
   divergence when one argument does each (04 second review note 20), so
   the gap has narrowed, but 04 still leaves the question open.
3. **Generic over the prelude.** 01 decision 9 recommends a spec over any
   prelude text; 05 §4.4.4 finds that "too wide".
4. **The expansion limit.** 01 decision 3 makes it a spec parameter `N`;
   03 decision 5 and 04 §2.3 treat it as a fixed language rule.
5. **The wording of H.** 05 §2.3 uses owner statement 4(ii)'s "every
   accepted compile-time form's spec run halts"; 01 decision 2, 03 F7,
   and 04 Q2 F1 use broader forms ("every compile-time run in the spec
   halts"; "every compile-time evaluation the spec performs while
   deciding src halts"; "every compile-time spec run halts"). 01 flags
   its own difference; 03 and 04 do not.
6. **What `--no-extern` buys.** 05 §5 says the extern agreement axioms can
   be removed "for programs checked and compiled with models only
   (`--no-extern`)". 02 §2.5 shows acceptance itself changes under
   `--no-extern` (`tagslot.sl`), so such programs are checked against
   different static facts. Not strictly contradictory, but 05 does not
   mention it.
7. **Which compiler the fuel work targets.** 03 recommends its hybrid (e)
   "for slc" and (a) only for a new kernel; 04 recommends a new compiler
   (R3) and iterative deepening (F1, 03's "cheap stopgap"); 05 recommends
   a step machine (03's (a), 04's F2), which 04 rates costly.
8. **Compile-time crashes.** 01 (spec never crashes; third compiler
   outcome), 02 (deterministic depth bound inside the spec, departing from
   §31), and 03 (`OutOfFuel` outside the spec, not a §31 crash) recommend
   incompatible treatments; 05's oracle option includes "crash points",
   which 01's never-crashing spec has no place for (05 itself flags the
   vacuity risk). 01 and 02 now name each other's opposite
   recommendation (01 second review note 2; 02 second review note 4);
   the disagreement stands.
9. **Going wrong.** 02 recommends `abort` as a defined outcome the
   compiled code must reproduce (S1); 05 decision 7 offers only that T6
   assume "the spec does not go wrong" or treat going wrong as "a
   behaviour after which anything is allowed".
10. **Two versions of the diagonal (largely reconciled).** 03 F6 needs no
    quine (`read-file` supplies the text), concerns a verdict-only
    `compile`, and branches in a macro's output (a run-position match with
    `compile-error` in an untaken branch is rejected anyway). After its
    second review, 05 §4.3 applies the same `read-file` macro form to
    `compile`, needing T1 to T4 and determinism through T3, not T5, and
    keeps a quine (not written) only for its run-position compile-and-run
    variant (05 second review notes 1, 2). The earlier difference over
    slc's `World` is gone: 03 now says slc does not escape (key finding 2).
11. **The shape of `Fails`.** 01 §4.3 recommends `Fails` as the `Err`
    outcome of one total relation and rejects a separate `Fails` relation
    as "more duplication, against rule 5"; 05 §3 and decision 2 recommend
    separate positive `Elab` and `Fails` relations with an exclusivity
    lemma, which is 01's rejected option (iii).
12. **Within 04 (resolved).** 04 now gives 20 `"internal:` sites
    throughout, as a grep of `self/` does (04 review note 27).
13. **03 F4.1 versus 06's `ho_counter.sl` (resolved).** 03 F4.1 concluded
    that nested suspensions cannot be composed as closures of one
    fixed-level type; 06's review found a fixed-level closure invariant
    with an erased step counter accepted. 03's refusals still reproduce,
    but their closure types have no decreasing argument, so 03's
    conclusion was too broad, not its tests. 03 F4.1 now limits it, and
    reports a counter version with runtime `many` closures (`fr/d.sl`,
    accepted and run by the reference, `--no-extern`, and `slc
    --interpret`) (03 review note 14). A CPS `bind` with counters is
    still untested.
14. **`--goal proved` and driven runs.** Not a contradiction: 05 now says
    a step machine's verdict "reaches only the driver and the run's own
    later steps, never compile-time code", so it cannot serve a `qed`
    (05 §4.3, F6, second review note 5), while 07 passes `--goal proved`.
    07's goal states the type of the step functions (`Certified`), not the
    result of a run, and 07's `drive.sl` calls `cstep` and `rstep`
    directly rather than through a `Certified` value (07 F2, F7, second
    review note 4).
15. **slc and the diagonal's `World` escape (resolved).** 03's first
    review had added "slc already takes this escape"; 03's second review
    retracted it (03 F6, second review note 1). This file had repeated
    the retracted claim; key finding 2 now follows 03.

## 6. What is not yet known or unverified

From the tracks' own "Unverified" sections and review notes.

- **The diagonal beyond its mechanism**: no faithful `compile` was put in
  Q; the step that H for all sources, given as erased step counts, would
  yield a runnable `compile` is untested and assumes Sleight is sound (03
  F6, §6, review note 5); the `slot-eq` copy step is 03's reasoning (03
  second review note 3); and the whole argument rests on SOUNDNESS.md's
  (T) and the logic's soundness, neither proved (03 second review, unsure
  points). 05's run-position variant assumes quines, unwritten; its macro
  form needs none (05 §9, second review note 2).
- **Gödel II**: whether Sleight meets its conditions, and README.md's IΣ₂
  / ω^ω^ω strength claim, are unchecked by all three passes over 05 (05
  §9; 03 F6). 05 now says the diagonal and its option 1 already rule out
  uniform H in a recursable form if the logic is sound, so only whether
  full-semantics safety is provable stays a guess (05 §4.3, second review
  note 3). 05's second review checked the step "uniform H plus
  stripped-run safety gives consistency" as far as it could, via
  `proto/review2/05_erased_to_many_false.sl` (an erased `(False)` yields a
  `many` one through an `absurd` function).
- **SOUNDNESS.md's (T), (C), and (E)**, on which H rests, are the sessions'
  argument, not proofs (05 §2.3; 03 review). SOUNDNESS.md part 1 says
  they "do not cover" a `--no-prelude` program with its own extern models
  or `def-prim` signatures, and H also needs host I/O to behave (03 F7,
  second review note 6; 05 §2.3, second review note 8).
- **Erased derivations being "real"**: every such claim in the spikes, and
  07's "by construction" claims, rest on Sleight's erased logic having no
  closed proof of `False`, which nothing shows given §10's `Type : Type`
  and no positivity (06 and 07 second reviews, unsure points).
- **02's N1 "there is an oracle"** holds only if a compiled `ESome` never
  meets two words the abstract machine keeps apart (02 second review,
  unsure points; cross-file item 1).
- **04's proposed output-theorem shape** ("values some spec run gives,
  for the same `slot-eq` and world answers") is itself a proposal, not a
  finding (04 second review, unsure points).
- **Whether a function taking erased H(src) evidence can be written**, and
  whether P3 (completeness from a derivation) is an erased Sleight
  function (03 §6).
- **Order-independence** in the abstract machine, and §13 as a provable
  heap invariant (02 §6).
- **Whether the run layer needs only the fact engine, scope, and Σ**, so
  the layers form no cycle (01 §6); and whether run-position facts belong
  in Γ or Σ (01 §4.2, second review note 3).
- **Whether an empty prelude text should behave as `--no-prelude`** (01
  second review, unsure points; decision 16).
- **Whether §50's meta solving is order-independent** within a boundary
  (01 §6).
- **Whether a relation-valued `TyCtor` parameter is usable at scale** for
  the spec's run (01 §6); the toys in 05 F7 are the only evidence.
- **Whether determinism, progress and preservation, and the sole-reference
  invariant are provable inside Sleight at scale**; only toys compiled (05
  §9).
- **Whether forward simulation gives refinement** given `slot-eq` and crash
  allowances (05 §9); whether V1 trees suffice for compile-time slot facts
  (02 §6).
- **Whether choosing the interned literal's block** as a tag slot's word
  under the `Nat` model is consistent (02 review).
- **Closures as suspensions beyond a chain**: a CPS `bind` with erased
  counters, level-indexed continuations, and whether any other placement
  of levels lets a stepper apply a packed-level closure (03 F4.1; 06 §6,
  review).
- **The spikes at scale** (06 §6; 07 §6): that the technique scales to
  Sleight's own machine (rule count, frame kinds, `at` and cell
  reading-back, the oracle); that the zipper extends to nested round
  trips with one frame per (rule, recursive premise) pair, and that most
  of elaboration would become frames; that replay in full Sleight needs
  equality on (code, heap) requests; that a simulation proof would
  dominate under decision 8a's option (b); that 06's first-order
  derivation context (Q1.3) works; that the prelude's `Array` carries 06's proofs (8b); and 06's
  60–80-line estimate for positive failure evidence (06 Q2.1).
- **Completeness for the spikes**: that 07's Q3(a) is writable for its
  toy, and that 07's diverging program 6 has neither derivation (07 §6,
  F7); that 07's replay variant cannot loop on a mismatched head answer
  (07 second review, unsure points).
- **Spike history and figures**: "accepted as first written" or "on the
  first compile" (06 F4, 07 F4, still the authors' reports; 07's F5
  histories were reproduced by editing today's files), and 05's "first
  attempt was refused" claims in F3 and F5 beyond one two-block check;
  07's quadratic-replay estimate; all spike timings are single runs on
  one machine. 06's `--build` timings were re-run by its second review
  (0.00 s and 0.06 s for the two long runs) (06 §6, second
  review note 6; 07 §6, second review; 05 second review).
- **slc internals**: why, after an error, slc still runs a constructor
  application but gives no `Settled` result for a call (not traced; 01
  §3.7, second review); whether its per-item expansion parameter never
  binds before the global count (03 second review: each decrement seems
  to accompany a global increment, not every path checked), and whether
  its store can hold cycles (03 §6); whether `merge-opens`'s bound is never short (03 §1);
  whether the macro primitives' callbacks into the elaborator never
  evaluate, which 03's (e) needs (03 §6); whether slc's checkpoint rolls
  back the expansion and gensym counters (03 Q1), and whether a failed
  depth-fuel attempt is a prefix of the successful run given effects and
  counters (03 second review).
- **OCaml facts**: that the manual leaves `let ... and` and argument order
  unspecified (from memory); behaviour on other targets, with flambda,
  and of tail calls with many arguments; GC safety of the `-imm` stores
  (still unchecked against the OCaml runtime sources); the `Slots`
  implementation's address hashing across GC moves, checked only by
  tests such as `tests/slots_compact.sl`; that a `many` `Bytes` is never
  mutated after `bytes-str` (02 §6; 04 §2.5, §6, second review).
- **The reference interpreter's order**: read from `lib/eval.ml:24` as
  arguments before head, not observed in a Sleight run, while the
  reference's extraction emits the head first (02 §6, §2.2).
- **All cost and effort figures**: lines of code, reuse percentages,
  `Program` step timings (single runs), and route effort (01 §6; 03 §6;
  04 §6).

## 7. Spikes

Two proof-technique spikes, each on a toy language, compiled and run on
the reference and on slc. Neither models Sleight itself.

**06: a certified, fuel-free stepper** (`proto/stepper/`).
- Built: a tiny language with registers and a heap of mutable blocks
  (allocate, read, write in place), `if`, and `while`, specified by a
  big-step `Runs m c m2`. A total, non-recursive `step` over an explicit
  command stack runs it, one `Program` continuation per step, with no
  fuel. The reference, `--no-extern`, `--build`, `slc --interpret`, and
  `slc --build` accept and run it (06 §1, F1, F2).
- Proved: soundness as the type of `advance`, whose `Halted` result
  carries `(erased (Runs m0 c0 mf) d)` for the program and memory the
  erased trace starts from, whatever trace of fitting type the caller
  passes (06 second review note 2); spec determinism (`runs-fn`); step
  determinism; `runs-star`; and `run-total`, which, given a `Runs`
  derivation, halts or sticks within its step count, a halt giving the
  spec's result (06 F2, F3, review note 2). Swapping `CSeq`'s order, or
  inverting the loop test in both the machine and its step relation, is
  refused (06 F2).
- Not proved: progress. "Stuck" carries no evidence, so a `step` that
  always answered `SStuck` would pass every type (06 §1, F3). `drive`'s
  type says nothing about `advance`'s outcome, so the driver and its
  printed text are outside the theorem (06 F2, second review note 3).
- The invariant: an erased trace of the steps, folded back at the halt by
  `step-back`, a non-recursive per-step lemma of 15 lines (06 F2, F5). In
  review, a closure invariant at one fixed level also worked once its
  type took an erased `subterm` step counter pinned by an `Eq`
  (`ho_counter.sl`). Without the counter it is refused for the missing
  decrease, and with its level packed in the state it can be built but
  not applied (06 F4.1, F4.2; decisions 18b, 18c).
- Effort: about 210 lines of proof against 90 of stepper code and 67 of
  spec. Checking adds about 0.1 s to the prelude's 0.44 s. 7821 steps
  take 1.5 s in the reference interpreter, 0.56 s under `slc
  --interpret`, and under 0.01 s compiled; the second review's re-run of
  the two long `--build` runs gave 0.00 s and 0.06 s. The long runs are
  `run.sl` with its loop bounds raised, and only allocation, read, and
  write walk the list heap (06 §1, F5, F6, second review note 6; single
  runs).
  The main costs are one evidence-carrying result type per partial
  helper, since a type holds no call (§9) and "There is no currying"
  (§17), and long positional constructor telescopes (06 F5). Numerals
  are opaque in erased derivations (§45; 06 F4.3).

**07: the §29 round trip with a suspendable checker**
(`proto/roundtrip/`).
- Built: a toy with top-level `Let t` (run at check time, giving a
  `Settled` value), `Assert i c` (a `comptime-match`: it reads a stored
  value and exports a fact), and `Need i c` (consults only facts); an
  inductive `Elab` with evaluation premises, a positive `Fails`, and a
  small-step `Step`. The checker suspends into a `Waiting` state; each
  `Program` step is one `cstep`: one machine step while `Waiting`, and
  otherwise one statement or the resumption after a run halts (07 second
  review note 1). The final `Verdict p` carries
  an erased `Elab [] p` or `Fails [] p`, with no fuel anywhere (07 §1,
  F2).
- Proved: exclusivity (`Elab ∧ Fails → False`), using determinism of
  evaluation and of every lookup. The statement, a `goal` mentioning only
  spec types, passes `--goal proved` on both implementations for both
  variants below. Four deliberately wrong single components, standalone
  functions not wired into the checker (two with the signatures of
  `check-assert` and `check-need`, two standing for one case of `mstep`
  and one transition of `cstep`), are refused at the faulty proof term
  (07 §1, F2, F5, review note 2, second review note 2). With one extra
  nondeterministic `Step` rule, some program has both derivations
  (compiled, `proto/review2/07_nondet_*.sl`; 07 second review note 3).
- Not proved: completeness or termination. A `step` that always returns
  `More` passes the same goal (`spin_vacuous.sl`), the exclusivity
  field mentions no part of the implementation, and the `why` text of
  `Rejected` is unconstrained. A `step` that itself loops is refused.
  The driver and its printed text are outside the statement (07 F7,
  review note 3, second review note 4).
- Zipper versus replay (decision 18a). The zipper's `Waiting` state holds
  two erased, defunctionalized contexts: `Ctx p0 es p` ("a derivation for
  `es ⊢ p` plugs into one for `[] ⊢ p0`") and `Reach`, the run so far.
  One `Ctx` serves `Elab` and `Fails`, which works, by 07's reading,
  because each "fails later" rule carries the same earlier premises as
  its `Elab` rule (07 §1, F3). The replay variant
  keeps the elaborator direct-style and re-elaborates from the start with
  a proof-carrying oracle of answers. It needs a proof-producing
  decidable equality on requests (about 50 of its 127 lines) and, by
  07's estimate from the code, about quadratic work (07 F6). It is not
  quite 03's (e): it has no inline bursts and replays the whole program
  (07 review note 4).
- Effort: spec 178 lines, determinism and exclusivity 123, the zipper
  checker with proof-producing lookups 151 (the suspension machinery
  about 45), replay 127, and driver and tests 61 (07 F2, F4). The
  evaluator side was trivial only because the spec's `Step` is the
  implementation's machine (07 F4; decision 8a).

What the two suggest together, as a reading: the shape that 03, 05, and
the brief's proposal C describe, a total step carrying erased evidence
and looped by the `Program` driver, is writable and checkable in
today's Sleight at toy scale, and its cost sits mostly in the spec and
its determinism lemmas (key finding 16). What remains is completeness,
which both spikes leave open (key finding 17; decision 14), and scale
(section 6).

## Review notes

Added by a final adversarial review, which read the brief, CLAUDE.md,
all of DESIGN.md, and files 01 to 07 with their review notes, checked
every quotation attributed to DESIGN.md against it (whitespace
normalized), and re-ran several claims.

Errors found and corrected above:

1. Key finding 1's title said elaboration and run "are one relation".
   01 proposes three layers (fact engine, run relation, elaboration
   relation with run premises); its claim is that elaboration cannot be
   a typing relation separate from evaluation. Retitled.
2. Decision 7 spoke of "owner statements 6 and 7" and quoted "a mutating
   heap machine on stripped code". The brief's unconfirmed reading
   concerns statement 6 alone, worded "the spec's run is a mutating heap
   machine on code with erased positions removed". Fixed.
3. Cross-file item 5 put 04 with 05 as using owner statement 4(ii)'s
   wording of H. 04 Q2 F1 says "every compile-time spec run halts",
   the broader form, without flagging it. Fixed.
4. The header said the brief's "Owner decisions" are the only owner
   positions in the file, but decision 18 attributed the goal "minimize
   fuel use" to the owner; that goal is in the brief's separate "Also"
   line. The header now covers the brief's listed goals, and decision
   18 attributes the goal to the brief.
5. Decision 6, 05's entry, turned 05's open question (is owner statement
   3 about the spec, or also about an implementation that "may crash")
   into the claim that it is about the spec. Restored as a question.
6. Decision 6, 03's entry, said the fuel question "decides" whether slc
   conforms; 03 says it "affects" that. Softened.
7. Decision 7 was marked "Formal-spec choice only", but its option R3
   departs from §37 and §39. Marked accordingly.
8. Decisions 3 and 4 were marked as needing DESIGN.md wording as a
   whole; only the options that fix an order do (3(a); 4 O1 and O3).
9. Key finding 17 stated "Exclusivity needs a deterministic spec" as
   fact; 07 F4 gives it as its expectation, not a compiled result.
   Hedged.
10. The diagonal was stated without its hedges in two places: the
    picture's "Fuel" item (now conditional on Sleight's functions
    terminating, and marked partly untested), and decision 18 (d) (now
    with 03's condition "a non-erased function on source text with no
    further evidence"). Key finding 2's "H for all sources is not
    provable" now carries 03's "in this form" (erased step counts).
11. Key finding 5's "`ESome` compiled with externs" did not say by
    which implementation; it is the reference's `--build` output.
    The slc sharing explanation is now attributed to 04, with its
    evidence (`share.ml`, tuples).
12. Quotation marks around paraphrases: cross-file item 9 ("assume the
    spec does not go wrong", "anything allowed after"), section 6 (the
    erased-step-count step; "uniform (T) versus safety"). Replaced by
    05's and 03's exact words or unquoted. Section 6's citation "03 §6"
    for the soundness assumption is now 03 F6, §6, and review note 5.
13. Smaller fixes: key finding 6 marks world-effect ordering as 02's
    reading; key finding 4 notes 02's fuel-free variant is uncommitted;
    key finding 11's tail-call sentence read as "held only without
    flambda"; key finding 12 attributes the `Stuck` point to 04;
    decision 8a's "06 calls" is now "06 reads"; decision 10's C3 says
    heap and stack, not "memory" for both; decision 18b's "my reading"
    named no author; "a sessions' argument" in section 6; cross-file
    item 12 shortened to its present state.

Re-run in review, all as the summary states: `diagonal.sl` accepted at
969 bytes and rejected with one byte added, on the reference and `slc
--interpret`; `slot_eq_comptime.sl` accepted and `slot_eq_comptime_none.sl`
refused on both; `imm_eq.sl` printing `1` for the first pair only when
built by the reference's `--build` with externs, `0` interpreted and under
`--no-extern --build`; `tagslot.sl` printing `3`, and refused under
`--no-extern`; `gensym_order.sl` giving the same numbering on both;
07's three `--goal proved` sets, including `spin_vacuous.sl`, and 05's
`spec.sl proof.sl`, all PASS on both; `slc --interpret deep.sl`
(unlimited stack) printing 49,999 `Cons _ 0` and then `Cons _ _ _)`.
`grep` finds neither "fuel" nor "diverg" in DESIGN.md, nor `def-prim`
or `def-opaque`.

Uncertain points, not changed:

- Whether decision 10's C2 (crashes only at named resource events) and
  decision 11's S1 (a defined `abort` that compiled code must produce)
  are formal-spec choices, as marked, or constraints on implementations
  that would need DESIGN.md wording.
- 02 N4's "the reference interpreter and slc fail it" (decision 5 (f))
  rested, for slc, on reading its source. (Since settled: 02's second
  review ran `slc --interpret imm_eq.sl`, which answers `ENone` for equal
  immediates; see Second review propagation.)
- Whether decision 1's recommendation, which 01 and 04 share, is
  fairly summarized as "(a), with the reader proved early": only 04
  says "early".
- The summary is still long (over 1000 lines). Most of the length is
  context the decisions cite; trimming further would drop content.

## Second review propagation

Each track and spike file now ends with "Second review notes" from a
second, independent review. This pass read all seven of those sections
and the corrected body text they point to, and changed this file (and
00-glance.md) to match. Each item names what changed here and the note
behind it. Nothing below is a decision.

1. Key finding 2, cross-file items 10 and 15: removed "slc as written
   escapes, since its elaborator needs a `World`". slc's compile runs in
   one `Program` step, total through its fuel; the `World` blocks only
   the literal construction (03 F6, second review note 1).
2. Key finding 2 and the picture's "Fuel" item: the diagonal's condition
   is now attributed to SOUNDNESS.md's (T), argued not proved (03 second
   review note 4); added the `slot-eq` copy step (03 second review note
   3) and the compiled untaken-branch refusal (03 second review,
   confirmed).
3. Key finding 2, cross-file item 10, and section 6: 05's diagonal needs
   T1 to T4 and determinism through T3, not T5, and no quine for the
   `read-file` macro form (05 second review notes 1, 2).
4. Key finding 8 and section 6: "slc's only fuel that can change a
   verdict" became "known to", with the `merge-opens` caveat (03 second
   review note 5).
5. Key finding 4 and cross-file item 14: a driven run's result is held
   by the run's own later steps; no compile-time code and no `qed` can
   obtain it (05 second review note 5). 02's fuel-free variant, earlier
   called uncommitted, is now reproduced as
   `proto/review2/machine_fn_oracle.sl` (02 second review note 8).
6. Key finding 5 and cross-file item 1: `imm_eq.sl` under slc (02 second
   review note 5); `slot_eq_share.sl`'s `ESome` only in slc's native
   build, `ENone` under `--byte`, `--interpret`, and the reference, and
   `bootstrap.sh`'s `--byte` blind spot (04 second review note 7);
   02's `const_share.sl` and N1 hedge (02 second review, unsure points).
   "02 did not run slc" removed there and in the review notes'
   uncertain points.
7. Key finding 10 and section 6: the printer defect is confined to
   `show-at` (`slc --interpret`'s final printer and `comptime-match`
   mismatch messages); compiled slc output and the reference print all
   elements; it contradicts `self/README.md:254-258`. The "printer
   defect elsewhere" unknown was removed (04 second review notes 2 to 4).
8. Key finding 11 and section 6: the `Slots` implementation hashes raw
   addresses; the template atom assumption; which `Bytes.unsafe_to_string`
   sites convert the argument (04 second review notes 5, 11, 12).
9. New key finding 18, decision 5, and decision 10: the output theorem is
   not "the same values, up to crash"; `slot-eq` is a second oracle
   beside `world-do` in 04 (04 second review note 6). Decision 5's
   option (f) now cites the slc run (02 second review note 5).
10. Key finding 13: generic code can take apart a parameter relation's
    derivation given its constructors and an erased `Matchable` (05
    second review note 4); 05 F3's one-block limit is specific to
    `Certified`'s single level (05 second review note 13).
11. Key finding 15 and section 6: slc's after-error behaviour as now
    tested (01 second review note 1, replacing the retracted "slc stops
    running compile-time code after an error"); the `é` column test (01
    second review note 5); the reference printing a first file's value
    before a second file's syntax error (01 second review note 11).
12. Key finding 1: "Only the fact engine is free of evaluation" replaced
    by §29's own words (01 second review note 7).
13. Picture "Spec shape", decision 19, and section 6: the open Γ-versus-Σ
    point for run-position facts (01 second review note 3).
14. Decision 6 and cross-file item 8: 01 and 02 now cross-reference their
    opposite recommendations (01 second review note 2; 02 second review
    note 4); 02's C4 "holds per bound" hedged with its conditions (02
    second review note 3).
15. Decision 8: option A3 restated as a cost, not a loss of §33's
    identities (02 second review note 2).
16. Decision 16: `--no-prelude` is not simply the empty prelude (01
    second review note 4); added to section 6 as an open question.
17. Decision 1: 04's reworded view on what a trusted front end can give
    (04 second review note 19).
18. Decision 13: 07's unconstrained `why` text (07 second review note 4).
19. Key finding 17, section 7: exclusivity failing without determinism
    is now compiled (`proto/review2/07_nondet_*.sl`); the second vacuity
    (`why` text); `drive.sl` calls `cstep` directly; a `Program` step is
    one `cstep`; the four wrong components are standalone functions (07
    second review notes 1 to 4). 06's driver is outside its theorem (06
    second review note 3).
20. Key finding 16 and section 7: `advance`'s theorem holds for any
    erased trace of fitting type, not only `TNil` (06 second review note
    2); 06's `--build` timings re-run, and which runs are long and which
    operations walk the heap (06 second review note 6). 06's register
    correction (note 1) touches nothing this file states.
21. Cross-file item 2 and rough edge 5: 04 adds crash versus divergence as
    an order observer (04 second review note 20); `Measure` also answers
    words allocated (02 second review note 7).
22. Rough edge 1: §15's hoisting fixes part of the order, and neither §6
    nor §15 orders two arguments (07 second review note 6). Rough edge
    10: abort sites cited (02 second review note 10). Rough edge 28:
    §42's "the driver's loop over total functions" added; the gap is now
    "not said outright" (07 second review note 7).
23. Section 6: Gödel half-guess narrowed to full-semantics safety (05
    second review note 3); SOUNDNESS.md part 1's exclusion and host I/O
    (03 second review note 6; 05 second review note 8); the "erased
    derivations are real" assumption (06, 07 second reviews); 07's
    replay-loop point; 04's theorem shape being a proposal; slc
    unknowns from 03's second review. "That the prelude calls no macros"
    was removed, now checked by grep (01 second review note 9).

## Third review notes

A third review checked each claim here and in 00-glance.md against the
cited track-file section as it now stands, after both of its reviews,
read DESIGN.md in full, and re-ran: `diagonal.sl` (969 bytes accepted,
one byte added rejected, reference and `slc --interpret`); the
`--eval-fuel 1000` pair (93025 steps finish as `Program` steps; one call
is out of fuel, reference and slc); `slot_eq_share.sl` (`(BTrue)` only
from slc's native build); `imm_eq.sl` (`ENone` interpreted on both, `ESome`
from both `--build` binaries); `tagslot.sl` (`3`, refused under
`--no-extern`); `07_nondet_both.sl` (`(MkBoth _ _ _)` on both) and
`det.sl` against `07_nondet_spec.sl` (refused at `det.sl:48`, inside
`step-det`); `pos_bytes.sl` (column 41); `machine_fn_oracle.sl` (`imm 1`);
`gensym_order.sl`; and 07's `--goal proved` sets for the vacuous
stepper (reference) and the replay variant (slc, compiled; slc refuses
`--goal` with `--interpret`). All matched.

Errors found and corrected:

1. Key finding 10 (and 00-glance) said the `show-at` defect is
   confined to `slc --interpret`'s final printer and the
   `comptime-match` mismatch message. `show-typed` also feeds
   `entry-value` (`elab.sl:4888-4891`), which `dump-context` reports
   use: `proto/review2/00_dump_deep.sl` (a 60000-element list, then
   `(dump-context xs)`) prints 49,999 `Cons _ 0` and then `Cons _ _ _)`
   under `slc --interpret`. Added; the claim is this review's, not 04's.
2. Rough edge 17 left out `settled-val-apply` and §45's literal entries,
   which 01's second review note 12 added. Added.
3. Decision 1 still cited DESIGN.md's "opening paragraph", which 01's
   second review note 6 corrected to the paragraph on the language's
   aims; and "with the reader proved early" was 04's alone (the first
   review's open point). Both fixed.
4. Rough edge 12 said §33's "the word of the `Nat` of its position" is
   stated "With externs on". §33 states it unconditionally; only the
   extern `Nat` FFI's obligation to meet it is "With externs on" (02
   §5.4). Fixed.
5. The picture's "The run" item cited decision 3 (elaboration order)
   and left out decision 5 (the `slot-eq` oracle it describes). Now
   decisions 4, 5, 7, 8, and 9.
6. Key finding 17 (and 00-glance, twice) said that without determinism
   exclusivity fails. 07 F4 compiled it for one nondeterministic
   variant ("for at least one"). Narrowed.
7. Key finding 8 marked "expands without end otherwise" as tested; the
   test shows only the refusal at the cap (01 §3.5). Reworded.
8. Section 6 still listed "whether `show-fuel` exhaustion only degrades
   printing" as unknown, while key finding 10 reports 04's second review
   settling it (its zero case emits a printer that prints `?`). Removed.
9. Decision 11 said 06 "recommends" a typing invariant; 06 decision 3
   names it as the route that also serves type soundness and Q2.1 as
   cheaper, recommending neither. Fixed.
10. Decision 1's "Depends on it" named theorem 3 and route R2 without
    their decision numbers, though 00-glance's "Linked" column listed
    14 and 17 for it; numbers added. 00-glance's row 5 listed 14, which
    decision 5's line does not name; removed there.
11. 00-glance: the diagonal bullet said 05 needs "no quine" unqualified
    (05 still assumes one for its run-position variant) and omitted
    determinism through T3; "`--build` binaries" lacked "with externs"
    (the reference's `--no-extern --build` answers `ENone`); decision 4
    "decides" lock-step versus confluence where §3 says it bears on it;
    04's F2 must be decided before R3 starts only "if it is wanted".
    Fixed.
12. Key finding 12: one line's indentation broke the list item. Fixed.

Unsure, not changed:
- Whether `dump-context` reports, which DESIGN.md defines only by
  reference to MANUAL.md (§27, §54), are held to §45's printing rules;
  they are at least a wrong answer given silently, against
  `self/README.md:254-258`.
- 03's own section 6 still says slc's elaborator "needs a `World`" as
  the reason it cannot play Q, which its revised F6 no longer relies
  on; that file is outside this review.

## Condensation review notes

A review of the condensation compared 00-summary.md and 00-glance.md item by item with this file
(as corrected by its three review sections) and spot-checked them against files 01 to 07 as they
now stand. Every decision (1 to 23, 8a, 8b, and 18a to 18c), rough edge (1 to 29), open cross-file
item, and unverified item survives. Re-run: `tagslot.sl` (`3`; refused under `--no-extern`).

Errors found and corrected in 00-summary.md (and 00-glance.md where it repeats them):

1. Cross-file item 16 (03 §6 against F6) is resolved: 03 §6 now gives slc's fuel as the reason and
   says a version taking the files from `Src` needs no `World` (03 coordinator note 1). Dropped;
   its number is left as a gap.
2. Decision 10 put 04's question ("is the outcome space 'a value some spec run gives, or a
   crash'?") in the recommendation slot as if 04 recommended it. Restored as 04's question, in the
   summary and in 00-glance row 10.
3. Rough edge 5 stated "It decides crash versus divergence" unconditionally; 04 r2.20 says order
   decides between them when one argument does each. Restored the condition and the attribution.
4. Decision 15 said 01's review is unsure about "the last two" excluded flags (`--hints`,
   `--warn-unused`); it is unsure about `--no-native` and `--warn-unused` (01's review notes,
   "Not changed, but unsure": "decision 8's exclusion of `--warn-unused` and `--no-native`").
   Named them.
5. Decision 1: "which an unproved total front end gives" had dropped the old text's "could give"
   (04 r2.19). Restored.
6. Decision 6: 03's "treat `OutOfFuel` as outside the spec" (a recommendation) had become the
   statement "`OutOfFuel` sits outside the spec"; 02's C4 "would hold per bound, provided the rest of
   elaboration terminates" had become "holds"; 05's question lost "on 05's reading of §31", and its
   "the crash-free one" read as either the spec or the oracle (it is the oracle). 04 and 07 were
   run into 05's bullet. Restored and split. The dropped "a third compiler outcome is a choice for
   the theorem only" is back in the wording line.
7. Key finding 4: "A total step looped by the driver needs no fuel" generalised "runs with no fuel";
   "fixed-level closures call one another only with a decreasing argument" generalised the tested
   pair (refused without one, accepted with an erased counter); the packed-level closure lost 06's
   "as far as found" and "by the stepper"; "is minted before" lost "must be" and the 05 F6
   citation. Restored. Decision 18's echo of the closure claim and 18c's hedge were aligned.
8. Key finding 2: "05 §4.3 gets the same with no quine" could read as 05 reaching the same
   conclusion independently; 05 runs the same `read-file` macro argument (05 §4.3). Reworded, with
   "it keeps a quine" restored to the clause that had lost its verb, and "(untested, assuming
   soundness) H ... is unprovable" restored to "assuming Sleight is sound ... that H ... is not
   provable".
9. Key finding 11: "GC moves caught by tests only" read as the moves being caught; the point is that
   the move detection is checked only by tests. "(unchecked)" after the write barrier read as the
   bypass being unchecked; it is the safety. Reworded.
10. Key finding 15: "slc several" errors replaced by the old "slc later ones too" (the count is not
    given in 01 §3.7). Key finding 16 lost 06 F2 for refused components. Key finding 17's "A
    self-looping `step` is refused" did not say which spike; it is 07 (07 r3).
11. Picture, "Spec shape": "where run-position facts live being open" did not parse. Reworded.
    Key finding 6: "with §6 a form head before arguments" read as §6 being a head; reworded.
12. Decision 5 lost 04's treating `slot-eq` answers as an oracle (old text, key finding 18), and
    05's oracle "logging crash points and files" misplaced who logs (the compiler logs; the oracle
    records crash points and file contents). Restored.
13. Decision 19's "(S2, S3 in either order)" named stages the text never numbers; now "Staging S0 to
    S6" with S2 and S3 identified (01 §4.6). Decision 23's "justifies ... but not the stripped run's
    (E)" read two ways; restored "does not settle". Decisions 10 and 11's "marked none; unsure"
    reworded as a plain statement.
14. Section 6, Gödel item: "the consistency step checked as far as" a file named no step and dropped
    05's condition; restored the step ("uniform H plus stripped-run safety gives consistency") and
    05's reading that the diagonal already rules out uniform H in a recursable form if the logic is
    sound (05 §4.3, r2.3).
15. Decision 14, 05's (b): "not callable without a proof" dropped "in practice". Restored.
16. Oxford commas added in decisions 2, 10, 15, 19, section 6, section 7, and key finding 6. 00-glance
    cited "§2 items 5, 18" without "00-summary"; fixed. Its row 18c said "packed in its argument"
    where the summary says "packed beside it"; aligned.

Unsure, not changed:
- 03 §6 now reads "as F6 now says", which narrates a revision (CLAUDE.md rule 18); 03 is outside
  this review.
- Key finding 10 says the printer defect "reaches" three consumers; 00-glance says "confined to
  `show-at`". Both follow 04 r2.2 to r2.4 and this file's third review; no further consumer was
  searched for.

## Third review propagation

Each track and spike file now ends with "Third review notes". This pass read all seven of those
sections and the corrected body text they point to, and changed 00-summary.md and 00-glance.md to
match. Citations `rN`, `r2.N`, and `r3.N` are as in 00-summary.md's header, which now defines
`r3.N`. Nothing below is a decision.

1. Picture "Fuel", key finding 2, and section 6: the diagonal's premise is now SOUNDNESS.md's (T),
   (C), and (E), (E) because §27 strips erased positions before a run (03 r3.1; 05 r3.1). Added the
   step carrying SOUNDNESS.md's claims over to a rejected Q (03 r3.2, listed as unverified), Q fixing
   its flags (03 r3.3), and the reading of "faithful" the `ENone` copy needs (03 r3.4). The
   underclaim about erased H evidence is replaced: if Sleight is sound, no Q can produce it for
   itself, while code outside Q may (03 r3.5). 00-glance's diagonal bullet aligned.
2. Key finding 4 and decision 14 (05's (b)): a uniform erased `Halts` proof exists for a terminating
   toy step (`proto/review3/05_halts_uniform.sl`); the diagonal rules it out for a faithful compiler
   (05 r3.4). Packed-level closures: a packed `Predates` is also refused (06 r3.2).
3. Key finding 6, decision 3, rough edge 1, and 00-glance (bullet and row 3): elaboration order is
   no longer "left to right, depth first"; both implementations take the head first, then expand
   every macro call among an application's arguments before elaborating any argument, then the
   arguments left to right (`proto/review3/gensym_*.sl`; 01 r3.1). Decision 3's recommendation now
   states that order.
4. Key finding 6, decision 4, rough edge 4, section 6, and 00-glance: the reference runs a head form
   before an argument form (`proto/review3/head_arg_order.sl`; 02 r3.1); section 6's "arguments
   before head per `lib/eval.ml:24`" item is removed. slc's order is listed as untested, since
   `slc --interpret` overflows its stack on that file at any depth (02 r3). This pass's own check
   (variants in the scratchpad, not kept): the overflow also occurs with the head at depth 0 and not
   with a small array size, so it seems to be slc's crash on the oversized `array-new`; since §31
   leaves how a crash is reported unspecified, it is listed in section 6 as possibly, not evidently,
   a defect.
5. Key finding 6: `Measure` cost is no longer an observer of order; it is absorbed once the world's
   answers are inputs (02 r3.3).
6. Decision 14 (01): the logic is reversed to 01's corrected form: the fuelled version needs no
   hypothesis, and (a) would follow under H plus fuel monotonicity (01 r3.2).
7. Decision 13 and key finding 15: §28's content is "the expected constructor and the actual value";
   the implementations differ on the first message's position after a compile-time crash (01 r3.3).
8. Decision 6 (02's C4): SOUNDNESS.md part 6 argues the rest of elaboration terminates without (T);
   the depth bound bounds steps by 02's count, a reading (02 r3.2).
9. Decision 7: SOUNDNESS.md's full-semantics route, which an R1 spec takes over or replaces (02
   r3.8). Decision 8: MINIMAL.md's "Evaluation and typing are relations, not functions" and 02's
   reading of the step as a deriving function beside such a relation (02 r3.9); 02's prototype
   addresses are natural numbers (02 r3.5). Decision 9: E1's alternative of dropping the
   extern-only facts (02 r3.4).
10. Key finding 10 and 00-glance: the claim that the `show-at` defect contradicts
    `self/README.md:254-258` is withdrawn (04 r3.2); `entry-value` added as a consumer (04 r3.12);
    `heap-strs-fuel` silently cutting a request's string list past 10^6 elements added (04 r3.4).
11. Key finding 11 and section 6: stores marked `(imm o n)` are emitted as barrier-free
    `Array.unsafe_set` on the constructor's block (04 r3.1).
12. Key finding 18 and 00-glance: `read-file` is an oracle beside `world-do` and `slot-eq` in 04
    (04 r3.5).
13. Rough edge 2 cites 04 §5.1 for §61 (04 r3.7); rough edge 5 adds that §17's levels are meant to
    rule out the diverging case, unsettled (04 r3.7).
14. Decision 5: 05's "rejects everything" is withdrawn under positive `Fails`, and the crash-oracle
    warning narrowed to sources that run compile-time code, if a crash counts as a rejection (05
    r3.2, r3.3).
15. Section 6: whether stripped-run safety alone gives consistency is not worked out (05 third
    review); one of 05's "first attempt refused" claims is reproduced (05 r3).
16. Decision 18c and rough edge 27: §18 says outright that "a function at a later level cannot be
    called from code at an earlier level", so the rough edge is reworded as a consequence, with
    whether it is wanted left to 18c (06 r3.1). Decision 8b: owner statement 6 concerns the spec's
    run, Q3.2 the implementation's heap (06 r3.6).
17. Key findings 16 and 17, section 7, and 00-glance: 06's further vacuous implementations, an
    always-`Ended`/`Stuck` `advance` and an always-`AgreeStuck` `run-total`
    (`proto/review3/06_vacuous.sl`; 06 r3.4); 06's first teeth check tests `step` only against
    `Step`, the stronger swap being refused in `step-back` (06 r3.5); 07's any-`init` vacuity (07
    third review).
18. Section 6: 07's "no verdict if and only if some run diverges" is false as worded; now "a run
    that the checker reaches", neither direction proved (07 r3.5). Section 7: in `step-det`,
    `SVar` against `SVarNo` needed `nth-nonth` (07 r3.2). Decision 8a: 07's (b) "nearer the prose"
    is 07's reading, with §31's "that of a machine" (07 r3.4).
19. Header: `r3.N` defined. Paragraphs touched were rewrapped to 100 columns and some condensed to
    keep 00-summary.md near 600 lines; 00-glance.md stays under 110 lines.

Unsure, not changed:
- 03 r3, 04 r3, and 05 r3 also corrected citations and details that 00-summary.md does not state
  (line ranges, attributions inside the track files); nothing here was changed for them.
- Key finding 10 drops 04's remark that the unrefuted zero cases of `str-split-fuel` and the sugar
  budget would be proof obligations, for length.

## Propagation check (third round)

A check of the third-round propagation against the track files as they now stand (all three review
sections), against the previous commit's 00-summary.md, and of 00-glance.md against 00-summary.md row
by row. Re-run on the reference and `_build/release/slc --interpret`: `proto/review3/gensym_depth.sl`,
`gensym_head.sl`, and `gensym_splice.sl` (outputs as 01 §3.6 quotes, both); `head_arg_order.sl`
(reference "out of fuel" under `--eval-fuel 20`, `Array.make` crash without it and at depth 0; slc a
stack overflow at depths 50 and 0, `1` with a small array); `06_vacuous.sl` after `std/list.sl` and
06's `spec.sl`, `machine.sl`, and `complete.sl` (accepted, both); `06_packed_predates_bad.sl`
(refused at 18:22 with "`L2` was not in scope when level `S` was minted", both; its first 13 lines,
through `use`, accepted); `05_halts_uniform.sl` after `proto/theorems/bove.sl` (prints `7`, both);
slc compiling `std/immediate.sl tests/cell_imm.sl` (five `Array.unsafe_set (of_any cell3 : int
array)` stores; `imm-stores` is `emit.sl:863-868`). Nothing below is a decision.

1. Key finding 4 and decision 18c said a packed-level closure could not be applied "also with a
   packed `Predates`" / "nor with a packed `Predates`". 06 F4.2 and r3.2 say the opposite for the
   application: with the `Predates` packed, a function at the stepper's level `S` applies the
   closure (the first 13 lines of `06_packed_predates_bad.sl` are accepted); what is refused is a
   step proving its fresh level `L2` below `S`. Both reworded.
2. Key finding 4 and decision 14 (05's (b)) said the diagonal rules out a uniform `Halts` proof for a
   faithful compiler with no premise; 05 F4 and §4.3 hold it only under the diagonal's premises and
   "if the logic is sound". Hedged by reference to key finding 2's premises.
3. New test `proto/review3/00_arg_head_order.sl`: the oversized `array-new` in the head form and a
   50-deep `tail` recursion in the argument form. Under `--eval-fuel 20` the reference crashes
   (`Array.make`) and `slc --interpret` overflows its stack, while with the allocation removed both
   report "out of fuel"; so `slc --interpret` too runs the head form first, as 02 §2.2 reads
   `self/elab-main.sl:178-182`. Key finding 6, decision 4, rough edge 4, section 6, and 00-glance's
   order bullet said slc's order was untested; now only slc's compiled order is listed as untested.
4. Key finding 11 read two ways: "the `-imm` operations and `(imm o n)` stores, emitted as
   `Array.unsafe_set`" made the FFI's `-imm` operations emitted code. 04 §2.5 places them in
   `lib/ffi_core.ml` and the templates and only the `(imm o n)` stores in emitted code. Reworded,
   with the re-run count of five.
5. Key finding 6's "Observers: crashes, stuck states, and divergence, `Measure` cost being absorbed
   ..." read as listing `Measure` among the observers. Reworded to 02 §2.3: crashes, stuck states,
   and divergence can observe order; `Measure` is absorbed once world answers are inputs; that
   nothing else does is the conjecture.
6. Key finding 15 and decision 13 called the `fuel.sl` `--eval-fuel 5` case "a compile-time crash".
   What happens there is fuel exhaustion, and whether that is a §31 crash is decision 6's open
   question. Reworded to "when compile-time fuel runs out". (01 decision 4 itself says "On a
   compile-time crash"; 01 is outside this check.)
7. 00-glance's diagonal bullet said "no source can produce that evidence for itself"; 03 F6 and
   r3.5 say no diagonal program Q can, while code outside Q may, and other sources may prove their
   own H (05 §4.3: "H for one particular program ... by an `erased` proof"). Narrowed to the
   diagonal source, with the outside-code clause restored.
8. 00-glance's printer bullet said the defect is "confined to `show-at`", which no file claims and
   which sits beside key finding 10's second silent cut in `heap-strs-fuel`. Now "lies in `show-at`,
   which feeds ...", with the `heap-strs-fuel` cut added.
9. Rewrapped key finding 4, decision 4, and two 00-glance bullets that the propagation left with
   a stray short line or over-long lines.

Checked and found consistent: the header's `r3.N` definition; key findings 2, 10, 16, 17, and 18;
decisions 3, 5, 6 (02's C4), 7, 8, 8a, 8b, 9, and 14 (01) against 01 to 07 as they now stand; rough
edges 1, 2, 5, and 27; section 6's diagonal, Gödel, and spike-completeness items; section 7.
00-glance's decision table agrees with 00-summary §3 row by row (recommendations, "Deps" numbers,
and wording marks), and its suggested order with the "Deps" entries. Nothing the previous commit
stated was dropped without a counterpart: its key finding 2 remark on 05's Gödel-II conditions is
in section 6, and its "arguments before head per `lib/eval.ml:24`" item was false (02 r3.1).
No narration, past-tense history, or missing Oxford comma was found in either file beyond the above.

Unsure, not changed:
- slc's compiled (`--build`) runtime order is still untested; no observable that distinguishes it
  without fuel was tried.
- Why `slc --interpret` overflows on the oversized `array-new` (FFI or model run) is untraced.
- Key finding 4's "per input or, for a terminating toy step, for every input" compresses 05 F4's
  three sources; 05 itself lists a uniform `erased` proof only as the second source's variant.

## Fourth review propagation

Each track and spike file now ends with "Fourth review notes". This pass read all seven of those
sections and the corrected body text they point to, and changed 00-summary.md and 00-glance.md to
match. 00-summary.md's header now defines `r4.N`. New citations are to `proto/review4/`; this pass
re-ran `01_head_name_err.sl` and `02_share_pair.sl` on both implementations, `05_stripped_absurd.sl`
(`--no-prelude`) and `06_packed_counter.sl` (after `std/list.sl spec.sl machine.sl`) on the
reference, and `07_loop_step_bad.sl` under `--goal proved` on the reference; each behaved as its
file says. Nothing below is a decision.

1. Key finding 15 and section 6 (01 r4.1): slc skips every run-position run after an error
   (`self/elab-main.sl:539`, `:545`, `:739`, `:2152`); a call and `(Succ (Zero))` get no `Settled`
   value, and only a nullary `(Zero)` does, by an untraced path. The earlier "still runs some
   run-position code" is gone; section 6 lists only that path.
2. Key finding 6, decision 3, 00-glance's order bullet and row 3 (01 r4.2): only a head that is a
   form is elaborated first; a name head is elaborated after the arguments' macro calls expand
   (`proto/review4/01_head_name_err.sl`). New rough edge 30 on §6's "The head is elaborated first";
   rough edge 1 points to it.
3. Decision 15, 00-glance row 15, and cross-file 4 (01 r4.3): §62 fixes 10000 and 01, 03, and 04
   all keep it; only making it a parameter `N` is open. The limit is removed from 01's flag list;
   the wording mark adds `N`. Cross-file 4 is resolved and deleted, its number left as a gap.
4. Decision 14 (01 r4.4): (a) from (b) needs a second lemma, that a halting spec run is reached at
   some finite fuel, besides monotonicity.
5. Decision 6, 02 (C4) (02 r4.1, r4.2): the depth bound bounds steps only if it counts activations,
   tail calls included, as `--eval-fuel` does; acceptance is a function of (source, bound, flags,
   `read-file` oracle). Section 6 adds C4's count for a function called through data (02's unsure
   point).
6. Decision 12, 00-glance row 12, and decision 5 (02 Q8, r4.6): 02's "some oracle exists" needs the
   spec's store to keep one block per `Settled` value (`proto/review4/02_share_pair.sl`); V1 is for
   the theorem, V2 an option, the store a heap.
7. Section 6 OCaml item (02 r4.3): the manual is quoted for 4.14; only other versions are unchecked.
   Constant sharing beyond immutable tuples added (04's unsure point).
8. Key finding 5 and 00-glance's `slot-eq` bullet (02 r4.4; 04 r4.8): answers vary between
   implementations and modes, not between runs as seen; ocamlopt "can" share equal constants.
9. Decision 8 and rough edge 7 (02 r4.5; 04 r4.3): §33 fixes one word for every value with no
   non-erased field, "however the value was built"; the open sharing question is narrowed to values
   with a non-erased field and extern values.
10. Key finding 2, section 6, and 00-glance's diagonal bullet (03 r4.1): carrying (T), (C), and (E)
    over to a rejected Q rests on part 5's per-activation measure and part 6's argument, as a
    reading; the circular detour is dropped; the step takes `compile`'s answer on Q to be determined
    by Q.
11. Key finding 2 (03 r4.2): "H for all sources" is qualified to a form a function can recurse on.
12. Decision 14, 03 (03 r4.3): 18's (a), (b), and (e) give form (i); only (c) gives three outcomes.
13. Key finding 8 (04 r4.1): slc's per-top-level-form expansion bound is separate from §62's per-run
    count.
14. Rough edge 11 (04 r4.4): DESIGN.md describes runs of both the implementations and the models;
    open is which is the meaning.
15. Key finding 10 (04 r4.5): the README's "1000000" matches no fuel in `self/`, and exhausted
    printer generation emits `?`.
16. Decision 18, 04 (04 r4.2): failed doubling attempts cost less than twice the last.
17. Key finding 12 (04 r4.7): MINIMAL.md's full list of what `mini/` lacks.
18. Key finding 2 and 00-glance's diagonal bullet (05 r4.2, r4.3): 05's version also needs soundness
    of the logic, and with `slot-eq` it goes through the `ENone` copy.
19. Picture "Theorems" and section 6 Gödel item (05 r4.4, r4.5): uniform stripped-run safety alone
    would give internal consistency (`proto/review4/05_stripped_absurd.sl`), by 05's reasoning.
20. Decision 22 (05 r4.7): the trust premise is SOUNDNESS.md's (T), (S), and (E).
21. Key finding 4, decision 18c, rough edge 27, section 6, section 7, and 00-glance row 18c (06 r4.1,
    r4.2): a packed-level closure is applied with a packed `Predates`, and with a second one and the
    counter is extended at its packed level (`proto/review4/06_packed_counter.sl`); what fails is
    extending at a newly minted level, by §18's introduction-order rule for `prove-predates`.
22. Key finding 17, section 7, and 00-glance's spikes bullet (06 r4.3): `run-total`'s halting within
    its count is read from its code, not its type; `finish` stopping rests on the erased `Star`.
    Section 7's timings give the range across reviews (06 r4.8).
23. Key finding 17 (07 r4.2): only a self-calling `step` is tested as refused
    (`proto/review4/07_loop_step_bad.sl`).
24. Decision 13 (07 r4.3): the mirror-shaped `Fails`'s reason is the shared context; exclusivity is a
    plain induction either way. Section 6 adds 07's unsure point on whether that order can decide a
    verdict.
25. Section 7, 07 (07 r4.1, r4.4): program 0's 26 steps are 6 statements, 19 machine steps, and the
    final `cstep`.
26. Rough edge 17 (01 r4.6) quotes §29's "So any `Special` or `Macro` ...". Rough edge 28 adds §20
    and §33 (07 r4.5).
27. To stay near 620 lines, several passages were condensed without changing their claims; a few
    details were left to the track files: rough edge 12's closing clause on §42's "the same values",
    decision 9's E1 alternative, and decision 10's reason for "up to crash" (all still in 02 and
    04). The rewrap also reflowed untouched paragraphs.

Unsure, not changed:
- Whether 01's rough edge 13 (here 30) is a deviation from §6 or only a matter of which error is
  reported; listed as a question.
- 00-summary is 622 lines, slightly above the target.
