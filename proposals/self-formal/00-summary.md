# 00. Summary: formalizing Sleight in Sleight, and a compiler proved against it

Written by Claude agents overnight, while the owner was asleep. Everything
here is a proposal or an agent's reading; nothing is approved, and nothing
is a design decision (CLAUDE.md rules 1 and 11). This file only combines
the five track files: each claim's source, evidence, and hedges are in the
track file and section it cites, and where this file and a track file
disagree, the track file (as corrected by its review notes) is right.
Where either disagrees with DESIGN.md, DESIGN.md is right.

Citations: `01 §3.6` is section 3.6 of `01-spec-shape.md`; `02`
is `02-dynamic-semantics.md`, `03` is `03-fuel-termination.md`, `04` is
`04-compiler-route.md`, and `05` is `05-theorems.md`. `§n` alone is
DESIGN.md. "Owner statement n" is item n of the brief's "Owner decisions",
which are an earlier session's paraphrases, not the owner's words; they
are the only owner positions anywhere in this file.

## Contents

1. The picture in one page
2. Key findings
3. Decisions for the owner (23)
4. Rough edges in DESIGN.md
5. Cross-file inconsistencies
6. What is not yet known or unverified
7. Spikes

## 1. The picture in one page

Each item is the tracks' recommendation, not a decision. Where the tracks
disagree, the decision listed says so.

- **Spec shape.** Start at source bytes: a small total reader function
  produces `Raw` forms with positions, and everything after it is a
  relation. Three layers: a fact engine free of evaluation (§7, "The engine
  of §7 reads no stored value", §29), a run relation that reads it, and an
  elaboration relation with run premises at each run-position form. A
  store Σ (§65's macro world) is threaded through all of elaboration; the
  scope Γ is restored when a scope ends. Rejection is a positive `Fails`,
  the `Err` outcome of one total relation. (01 §1, §4.2, §4.3; decisions
  1, 13, 19.)
- **The run.** A small-step heap machine over post-erasure code, as §27
  already describes ("its erased positions are stripped, the evaluator runs
  the code"). Words are `Imm n | Ptr a` with abstract, never-reused
  addresses compared only for equality; blocks are mutable; the step is
  total, with an explicit continuation stack; one fixed evaluation order;
  `Nat` is a machine primitive; `slot-eq` reads an oracle. (02 §3 Q1, Q2,
  Q3, Q4, Q6; decisions 3, 4, 7, 8, 9.)
- **Fuel.** No hypothesis-free, non-erased Sleight `compile` on source
  text can be faithful for every source (the diagonal, key finding 2). So
  fuel either stays as an internal device that never shows in a result, or
  the unbounded part is moved into the driver's `Program` loop, which
  prototypes show needs no fuel. The tracks recommend different
  mechanisms (decision 18): a stepped interpreter with bursts and replay
  (03), iterative deepening at the driver (04), or a whole-compiler step
  machine (05).
- **Theorem statements.** Intrinsic: `compile` returns its verdict with an
  erased spec derivation, since a type holds no call (§9). T1/T2
  (accepted ⇒ `Elab` derivation; rejected ⇒ `Fails` derivation), T3
  (never both, per oracle), T4 (every source accepted or rejected:
  owner statement 3) relative to a halting hypothesis H, T5 (compile-time
  values match the spec run), T6 (output refines the spec). Uniform H and
  stripped-run safety are expected to stay meta-theorems. (05 §3, §7; 01
  decision 2; 03 Q2; decisions 13, 14.)
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

Only findings the track files support after their reviews. "Tested" means
a prototype was run on the reference (`_build/default/bin/main.exe`) and,
where stated, on slc.

1. **Elaboration reads run results, so elaboration and run are one
   relation.** Head dispatch needs a `Settled` entry whose stored value
   names the form (§6 item 1); `comptime-match` reads a stored value (§28);
   a run-position form "is elaborated, its erased positions are stripped,
   the evaluator runs the code, and its results become `Settled`" before
   "the code after it is checked" (§27); `prove-literal-lt`, `unary`, macros,
   and `native-compute` also run code (01 §3.1). Only the fact engine is free
   of evaluation (01 §3.2). Consequences: a typing relation separate from
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
   functions terminate (03 F6). The branch must be in a macro's output or a
   `comptime-match`, because `compile-error` "fires wherever it is
   elaborated, erased code included" (§4; 03 review note 1). Corrected
   conclusion (03 F6 "What it does not refute", review notes 3, 5): it does
   **not** refute owner statement 4(ii) read as mathematics, nor a
   `compile` that takes erased evidence of H for its one source; it does
   suggest (untested inference, assuming Sleight is sound) that H for all
   sources is not provable inside Sleight. slc as written escapes, since
   its elaborator needs a `World`, which "only the driver supplies" (§42;
   03 F6). 05 §4.3 gives a related quine version for a compile-and-run
   function (no quine written) and a Gödel-II reading whose conditions are
   unchecked.
3. **Theorems must be intrinsic.** §9: "The elaborated form of a type never
   contains a function call" (tested refusal, 05 F1). A toy checker that
   returns `Accepted (erased (Elab s))` or `Rejected (erased (Fails s))`,
   with an erased exclusivity lemma, is accepted, and packaged as a goal it
   passes `--goal proved` (05 F2, F3).
4. **Fuel-free shapes exist, with limits.** A total step looped by the
   `Program` driver runs with no fuel counter (02 §2.6, in a review variant
   with the oracle as a function; 03 F5; 05 F6). With `--eval-fuel 1000`, a
   93025-step computation finishes when cut into `Program` steps and fails
   with `out of fuel` as one call, in both implementations (03 F5).
   Recursion on an erased `Halts` derivation (Bove–Capretta) is accepted,
   but a caller must supply the `Halts`: a written-out term, a per-input
   proof, or a fuel run that has already done the work (05 F4). Limits,
   all tested: a continuation closure of one fixed-level type cannot call
   another (03 F4.1; level-indexed continuations untested); a function
   cannot iterate `Program` steps itself (03 F4.2); every function a step
   calls must be minted before the program's level (03 F4.3, 05 F6); and a
   driven run's result never becomes a Sleight value, so it cannot serve a
   `--goal proved` run (05 F6).
5. **`slot-eq` makes acceptance depend on the implementation.** §67:
   "`ENone` proves nothing, so an implementation may always answer it, and
   which one a call answers may differ between runs." A run-position
   `comptime-match` on `ESome` is accepted by both implementations (01
   §3.8; 05 §2.2); that an `ENone` implementation would reject it is
   inferred from §67, not observed. In practice answers already differ:
   `(add 1 2)` against `3` is `ENone` in the reference interpreter and
   `ESome` compiled with externs (02 §2.4); two run-position
   `(str-append "a" "b")` are `ESome` compiled by slc and `ENone` under
   `slc --interpret`, because ocamlopt 4.14.1 shares equal immutable
   constants (04 §2.5).
6. **What DESIGN.md does and does not fix about evaluation order.** Fixed:
   eagerness (§31); in run position, "the forms inside a form run before it
   does" (§27), and with §6's "The head is elaborated first", a head that
   is a form runs before the arguments (reading, 02 §2.2); world effects
   are ordered by the unique `World` (02 §2.2 item 5). Not fixed in general:
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
   crashes (MANUAL.md `--eval-fuel`; 01 decision 7). slc's only fuel that
   can change a verdict is its interpreter's depth bound (default
   1000000000, fresh per run-position form, macro run, and interpreted
   `Program` step); the reference has no bound by default (03 F3). The
   10000-expansion cap of §62 carries real weight: a macro whose output
   calls itself expands without end otherwise (tested, 01 §3.5).
9. **slc has no spec relation to retrofit against.** About 6% of its
   ~18,650 lines are erased lemmas, almost all in the libraries; the
   elaborator, interpreter, and emitter are trusted plain code for
   correctness; there are 20 `"internal:` sites; and the emitter trusts
   refutation ("A wrong refutation would misdispatch silently here") (04
   §2.2, §2.5).
10. **slc printer defect (reproduced in review).** `slc --interpret deep.sl`
    on a 100003-element list prints 49,999 `Cons _ 0` and then
    `Cons _ _ _)`, because `show-at`'s 100000 depth budget is spent twice
    per nested field. Under §45, `_` is for a union with more than one
    constructor, erased fields, cells, slots, functions, opaque proofs, and
    values with no readable `Matchable`, so this is a wrong value, not a
    §31 crash ("A crash produces no value, never a different one") (04
    §2.3, review note 2). The compiled printer and the reference were not
    checked on this input.
11. **Output-end risks in slc.** The emitter needs call and constructor
    arguments to be atoms, which nothing types (an extern template would
    evaluate a non-atom twice); `-imm` FFI operations bypass OCaml's write
    barrier (safety unchecked); `Bytes.unsafe_to_string` relies on
    uniqueness being sound; tail calls with 20 arguments held on amd64
    4.14.1 without flambda only (04 §2.5).
12. **`mini/` gaps.** A malformed shape has no derivation and
    `elab-program` can answer `ProgramStuck`; keywords are reserved `RKey`s
    though §19 says special forms "may be shadowed"; `Sexp` has no `Pos`
    (01 §3.7, §3.10; 04 §2.4). Owner statement 3 needs `Stuck` refuted.
13. **Parameterization works by indexing.** A relation can be an erased
    `TyCtor` parameter, and a `(Model R)` record indexed by it is accepted;
    a field can be used in types inside a body after `let-match`, but not
    named in a signature, and generic code cannot take apart a derivation
    of a parameter relation (05 F7).
14. **The role of "`unique` is the sole reference".** Not needed for
    compiler correctness against a mutating heap-machine spec; it is what
    connects that machine to the tree reading of values the fact table
    relies on (05 §6, a reading).
15. **Source details are observable.** Macro positions expose columns, which
    are 1-based byte counts in both implementations (01 §3.9). In the two
    programs tested, the reference reported only the first error and slc
    reported later ones too (01 §3.7).

## 3. Decisions for the owner

Merged from all five files, ordered so that a decision comes before those
that depend on it. Each says whether it needs DESIGN.md wording, which
under rule 12 the owner confirms word for word, or is only a choice for the
formal spec. Recommendations are the tracks', never decided.

### A. What the spec is about

**1. Where does the spec start?**
Options: (a) source bytes, with a small reader function in front of a
relation over `Raw`; (b) `Raw`, with the reader trusted; (c) a core
language after dispatch and expansion; (d) the reader as a parameter
satisfying a `Parses text raw` law (05 §4.4.3).
Recommended (01, 04): (a), with the reader proved early. Why: owner
statement 3 speaks of "source code"; positions are observable; a core start
leaves out head dispatch and macros, which (01's reading) DESIGN.md's
opening paragraph makes central. 05 offers (d) if the syntax is to be
separated.
Depends on it: the statement of theorem 3, whether `Pos` is in the
judgment, and whether a trusted front end (route R2) can serve owner
statement 3.
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
Depends on it: determinism (T3), decision 13's error content, and the
oracle (decision 5), whose answers are consumed in some order.
Needs DESIGN.md wording. Context: 01 decision 5, §3.6; 02 rough edge 12;
05 §2.2, rough edge 5.

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
Needs DESIGN.md wording. Context: 02 decision 3, §2.2, §2.3; 04 §2.5,
rough edge 1; brief proposal A.

**5. How is `slot-eq`'s nondeterminism handled?**
Options: (a) an oracle parameter, so the spec is a function for each
oracle; (b) a nondeterministic relation, with existence but no
exclusivity (T3 false outright); (c) fix the compile-time answer to word
equality; (d) forbid `slot-eq` in run position or a macro; (e) always
`ENone` (02 N3: `tests/slot_eq.sl` and the `Slots` implementations would
disagree); (f) always truthful (02 N4: both implementations fail it).
Recommended by all three tracks that address it: (a). The shapes differ:
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
  compiler input, so that acceptance is a function of (source, bound); owner
  statement 3 then holds per bound. This departs from §31 at compile time,
  and heap exhaustion stays host-dependent.
- 03: fuel exhaustion is not obviously a §31 crash ("cannot represent");
  treat `OutOfFuel` as an outcome outside the spec, which decides whether
  slc's current behaviour conforms.
- 05: open; if the spec has no crash (its reading of §31), owner statement
  3 is about the spec, and crashes must be kept out of the oracle or
  completeness stated for the crash-free oracle.
- 04: open, as a sub-question of decision 10.
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
owner statements 6 and 7 as "a mutating heap machine on stripped code" is
the earlier session's and is not confirmed (brief).
Depends on it: what elaboration outputs; the statement of type soundness.
Formal-spec choice only. Context: 02 decision 1, §2.1; 05 §3 T7.

**8. Machine state and addresses.**
Options (02 Q2): (A1) `Imm n | Ptr a`, abstract never-reused addresses
compared only for equality, mutable blocks, explicit continuation, total
step, `Program`-driven (the brief's proposal B plus immediates and §33's
representation identities); (A2) natural-number addresses as in slc; (A3)
everything boxed, as slc's interpreter, which loses §33's identities.
Recommended (02): A1. Open sub-questions DESIGN.md does not answer: what
word an unapplied constructor is, and what an extern type's `Matchable` is
under `--no-extern` (02 Q2 table; §29 says a `Matchable` is "the FFI's
wrapper for an `extern` type and nothing otherwise"), and whether two separately built immutable values may share one
word (04 rough edge 4; cross-file item 1).
Depends on it: decision 5's oracle shape, T6.
Formal-spec choice, unless the sharing question is answered in DESIGN.md.
Context: 02 decision 2, Q2; 04 §2.5, rough edge 4.

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
a spec indexed by heap and depth bounds, with a theorem for a host with at
least c·H and c·D memory.
Recommended (02): C2, with C3 as a later strengthening. 04 asks the same
("same value, or one side crashed", which §31 and §42 seem to force).
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
See cross-file item 9.
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
derivation" as in `mini/` (01 §3.7).
Depends on it: the architecture of every compiler pass; how much of
decision 3's order the spec must pin down.
Formal-spec choice only. Context: 05 decisions 1, 2, §3; 01 decision 4,
§4.3.

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
Sub-questions: which H? Owner statement 4(ii)'s "every accepted
compile-time form's spec run halts", or the broader "every compile-time
run in the spec halts" that 01 and 03 F7 use (cross-file item 5). And is
H stated over evaluation only, with `read-file` and `native-compute`
axiomatized as terminating (03 recommends so)?
Depends on it: decision 6; decision 18; whether the deriving function for
elaboration takes fuel.
Formal-spec choice, except the resource-budget alternative, which needs
DESIGN.md wording. Context: 01 decision 2; 03 decisions 2, 4, Q2, F7; 05
decision 5, §3 T4, §4.3.

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
`Macro`, `Raw`, and so on at its end, `--no-prelude` being the empty one.
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
  normalizing interpreter (ruled out by the diagonal for all sources);
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
Closures cannot compose suspensions at one fixed level (key finding 4).
The owner's goal "minimize fuel use" (brief) bears on all of these.
Depends on it: decision 17, the architecture of every elaboration
function. No DESIGN.md wording. Context: 03 decision 3, Q1; 04 decision
3, Q2; 05 decision 5.

**19. Judgment shape and staging.**
Recommended (01): the layers and Σ/Γ split of 01 §4.2, with the run
relation a parameter of elaboration where possible, so elaboration's
metatheory is proved once for every lawful run (unverified that a Sleight
ADT can usefully be indexed by a relation-valued `TyCtor` this way; 05 F7
is related evidence). Staging: reader; `mini/` recast in the final shape;
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
does not settle the stripped run's (E), which still needs (T).
No DESIGN.md wording, though 02 rough edge 7 asks what "the only
reference" (§13) means. Context: 05 decision 9, §6.

## 4. Rough edges in DESIGN.md

Merged and phrased as questions. None is resolved here.

1. **Order of elaboration.** §65 threads the macro world "sequentially
   through all of elaboration" and gensym counts "from 1 over the whole
   run", but only "The head is elaborated first" (§6) is stated. Is the
   left-to-right, depth-first order of items part of the language? (01
   §5.1; 02 §5.12; 05 §8.5.)
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
5. **Is evaluation order meant to be unobservable?** (04 §5.1; compare 02
   §2.3.)
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
    implementations abort. (02 §5.6.)
11. **"The evaluator" in §27 and §29.** Is it, in a formal spec, the
    spec's own run, and does it run extern models or implementations?
    §42's "running the models instead of the implementations must give a
    program the same values" suggests the models. (03 §5; 04 §5.5; 05
    §8.3.)
12. **`Nat`'s word under models.** §33's "the word of the `Nat` of its
    position" is stated "With externs on", and §35's tag slots for
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
    `Settled`, and the entries `mint-settled`, `mint-settled-erased`, and
    `settled-ty-apply` mint (§65), among its three sites? (01 §5.12.)
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

## 5. Cross-file inconsistencies

Listed, not resolved.

1. **Addresses versus compiled `slot-eq`.** 02 recommends never-reused
   abstract addresses (A1) and an oracle under which `ESome` needs equal
   words (N1), and says "there is an oracle" covers every implementation
   seen tonight (02 decision 4). 04 found slc's compiled code answering
   `ESome` for two separately computed `(str-append "a" "b")`, because
   ocamlopt shares equal constants (04 §2.5); under A1 those are two
   addresses, so no N1 oracle would explain that answer. 04 itself says it
   is a mismatch "only if the spec says that every allocation takes a
   never-used address". 02 did not run slc.
2. **Is evaluation order observable?** 04 rough edge 1 suggests it may be
   unobservable, since effects are ordered by the unique `World` and "a
   crash and divergence both produce no value". 02 §2.3 lists observers:
   whether a write happens before a crash, divergence, stuck states, and
   cost through the `Measure` request.
3. **Generic over the prelude.** 01 decision 9 recommends a spec over any
   prelude text; 05 §4.4.4 finds that "too wide".
4. **The expansion limit.** 01 decision 3 makes it a spec parameter `N`;
   03 decision 5 and 04 §2.3 treat it as a fixed language rule.
5. **The wording of H.** 05 and 04 use owner statement 4(ii)'s "every
   accepted compile-time form's spec run halts"; 01 decision 2 and 03 F7
   use broader forms ("every compile-time run in the spec halts"; "every
   compile-time evaluation the spec performs while deciding src halts").
   01 flags its own difference.
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
   vacuity risk).
9. **Going wrong.** 02 recommends `abort` as a defined outcome the
   compiled code must reproduce (S1); 05 decision 7 offers only
   "assume the spec does not go wrong" or "anything allowed after".
10. **Two versions of the diagonal.** Not a contradiction, but different
    assumptions and scope: 03 F6 needs no quine (`read-file` supplies the
    text), concerns a verdict-only `compile`, and branches in a macro's
    output (a run-position match with `compile-error` in an untaken branch
    is rejected anyway); 05 §4.3 assumes a quine (not written), computes
    `cr(Q)` in run position for a compile-and-run function, and for
    `compile` needs T5. 05 does not mention that slc escapes through its
    `World`.
11. **The shape of `Fails`.** 01 §4.3 recommends `Fails` as the `Err`
    outcome of one total relation and rejects a separate `Fails` relation
    as "more duplication, against rule 5"; 05 §3 and decision 2 recommend
    separate positive `Elab` and `Fails` relations with an exclusivity
    lemma, which is 01's rejected option (iii).
12. **Within 04.** §2.2 counts 20 `"internal:` sites (corrected in
    review), but Q1 R1 still says "The 17 'internal' sites".

## 6. What is not yet known or unverified

From the tracks' own "Unverified" sections and review notes.

- **The diagonal beyond its mechanism**: no faithful `compile` was put in
  Q; the step "H for all sources, as erased step counts, would yield a
  runnable `compile`" is untested; it assumes Sleight is sound (03 §6). 05's
  version assumes quines, unwritten (05 §9).
- **Gödel II**: whether Sleight meets its conditions, and README.md's IΣ₂
  / ω^ω^ω strength claim, are unchecked (05 §9; 03 F6). Which half of each
  "uniform (T) versus safety" pair is provable is a guess (05 §4.3).
- **SOUNDNESS.md's (T), (C), and (E)**, on which H rests, are a sessions'
  argument, not proofs (05 §2.3; 03 review).
- **Whether a function taking erased H(src) evidence can be written**, and
  whether P3 (completeness from a derivation) is an erased Sleight
  function (03 §6).
- **Order-independence** in the abstract machine, and §13 as a provable
  heap invariant (02 §6).
- **Whether the run layer needs only the fact engine, scope, and Σ**, so
  the layers form no cycle (01 §6).
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
- **Level-indexed continuations** as a way to compose closures (03 F4.1).
- **slc internals**: whether slc stops running compile-time code after an
  error (one test, 01 §6); whether its per-item expansion parameter never
  binds before the global count, whether its store can hold cycles, and
  whether `show-fuel` exhaustion only degrades printing (03 §6); whether
  the macro primitives' callbacks into the elaborator never evaluate,
  which 03's (e) needs (03 §6); whether slc's checkpoint rolls back the
  expansion and gensym counters (03 Q1).
- **The printer defect elsewhere**: whether slc's compiled printer has the
  same cutoff, and whether the reference prints the deep list correctly
  (04 §6, review).
- **OCaml facts**: that the manual leaves `let ... and` and argument order
  unspecified (from memory); behaviour on other targets, with flambda,
  and of tail calls with many arguments; GC safety of the `-imm` stores;
  that a `many` `Bytes` is never mutated after `bytes-str` (02 §6; 04 §6).
- **The reference interpreter's order**: read from `lib/eval.ml:24` as
  arguments before head, not observed in a Sleight run, while the
  reference's extraction emits the head first (02 §6, §2.2).
- **That the prelude calls no macros** at its own elaboration (01 §6).
- **All cost and effort figures**: lines of code, reuse percentages,
  `Program` step timings (single runs), and route effort (01 §6; 03 §6;
  04 §6).

## 7. Spikes

Two further spike files, `06` and `07`, are in progress and will be
summarized here when they land.
