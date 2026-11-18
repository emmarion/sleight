# Handoff: formalizing Sleight in Sleight, decision phase

Written by a Claude session for the owner and the next session. Nothing
here is approved or decided. Every recommendation is a track's or this
session's proposal, and the "owner statements" are an earlier session's
paraphrases (agent-briefs/BRIEF.md), not the owner's words. CLAUDE.md
overrides anything here; DESIGN.md is right wherever these files differ.

## 1. Where things stand

- **Branch:** `ccr-666c572b-tc467z`. It holds the earlier scratch branch
  `ccr-12649ca3-qy84d1` and two more review rounds. No pull request.
  DESIGN.md, ASSUMPTIONS.md, DECISIONS.md, and OPEN.md are untouched.
- **The material:** 00-glance.md (one page), 00-summary.md (§3 lists 28
  decisions), track files 01 to 10, tests under `proto/`, and BUGS.md
  entries 13, 18, 19, and 23 to 27.
- **This session** settled four points the previous handoff left open:
  - slc's interpreter, like every other mode tried, runs a head form
    before an argument form in the two tests built to show it.
  - `array-move-imm` crashes the reference interpreter, as the other
    two `-imm` blits do (BUGS.md 26).
  - 08's GC stress tests pass on OCaml 4.14.1 with flambda and on 5.4.1
    with and without flambda, and the one without Zarith passes on
    arm64 under qemu.
  - Gödel II's condition (d) compiles in an abstract form, under the
    conditions 09 §2.4 B states.

  It also ran review rounds 7 and 8, each followed by fresh checks of
  the summary and glance.
- **Convergence:** it has stopped. As the reviewers reported:

  | Round | Errors per file | In the files | Summary and glance checks |
  |---|---|---|---|
  | 1 to 5 | 9–27, falling to 3–9 | — | — |
  | 6 | 3–14 | — | — |
  | 7 | 4–13 | about 88 | 38 |
  | 8 | 4–10 | about 79 | 25 |

  Every test result reproduced in every round. The errors that remain
  are general readings ("only", "cannot", "DESIGN.md does not say"),
  conditions lost in condensation, and new text's first-draft errors,
  this session's included. Each round still refutes a few general
  claims with one small test. This session's recommendation is to stop
  full review rounds, decide the questions below, and, if the work
  continues, turn the claims the conclusions rest on into tests with
  expected outputs checked by one script, treating the prose as an
  archive.

## 2. How a decision is made here

- The owner answers in chat. Where an answer leaves a gap, the session
  asks rather than filling it (CLAUDE.md rule 11).
- If the answer changes DESIGN.md (each decision below says whether it
  would), the session implements first, then shows the owner the
  proposed DESIGN.md text one section at a time, with new text in bold
  and removed text struck through. It edits DESIGN.md only after the
  owner confirms the exact wording, and all DESIGN.md edits from one
  discussion land as one commit (rule 12).
- Once DESIGN.md states a decision, the question leaves DECISIONS.md,
  and any ASSUMPTIONS.md entry that stood in for it is removed (rule
  14). DECISIONS.md holds proposed answers only, each marked not
  approved (rule 21).
- **Open question for the owner:** many of these decisions concern the
  formalization, not the language. They need no DESIGN.md wording,
  and no file says where such a decision is recorded once it is made.
  DESIGN.md states what the language is, and the files here are
  proposals. Where should formalization decisions be recorded?

## 3. The key decisions, in the suggested order

The order follows 00-summary §3: each decision comes before those that
depend on it. Each entry gives the question, what it unblocks, the
options, the tracks' recommendation and the main tension, the evidence,
and whether DESIGN.md wording is needed. The full text, with citations,
is in 00-summary §3 under the same number.

### Decision 1. Where does the spec start?

- **Question:** what does the formal spec take as input?
- **Unblocks:** the form of theorem 3 (decision 14), whether `Pos`
  appears in the judgment, and route R2 (decision 17).
- **Options:**
  - (a) source bytes, with a small reader before a relation on `Raw`;
  - (b) `Raw`, with the reader trusted;
  - (c) a core after head dispatch and macro expansion;
  - (d) the reader as a parameter with a `Parses text raw` law.
- **Recommended (01, 04): (a).**
  - Owner statement 3 speaks of "source code".
  - Positions are observable (error messages and `Pos` values).
  - A core start would leave head dispatch and macros outside the
    proof, and 01 reads those as central to DESIGN.md's aims.
- **Tension:** 04 reads statement 3 as asking only that every program
  be accepted or rejected, which a total but unproved front end could
  give. If the spec's verdict is to be about the text, the reader and
  the expander must be proved.
- **DESIGN.md wording:** none.
- **To answer:** (a), (b), (c), or (d); for (a), say whether the
  reader should be proved early, as 04 suggests.

### Decision 2. What does "parameterized the semantics" mean?

- **Question:** owner statement 1, in an earlier session's paraphrase:
  "we parameterized the semantics of the language, and this, or the
  syntax of the language, or both, and our compiler is proven to be in
  agreement with those." What is the semantics parameterized over?
- **Unblocks:** the spec's signature, how externs enter (decision 9),
  and what the prelude is to the spec (decision 16).
- **Options:**
  - (a) one fixed spec;
  - (b) generic over a model record: extern models, the `slot-eq`
    oracle, and the file system;
  - (c) (b) and also the syntax (decision 1 (d));
  - (d) (b) and also the prelude.
- **Recommended (05): (b),** plus (c) if the syntax is separated. 04
  recommends parameterizing over the extern table.
- **DESIGN.md wording:** none.
- **To answer:** say what "parameterized" was meant to cover.

### Decision 3. Is the order of elaboration part of the language?

- **Question:** must every implementation elaborate in one order?
- **Why it matters:**
  - Order shows in gensym numbers (§65), in the expansion count (§62),
    and in which error comes first.
  - It can also decide acceptance:
    `proto/review7/01_order_accept.sl` and `01_order_refuse.sl` differ
    in a gensym number and get opposite verdicts.
  - DESIGN.md fixes part of the order: head first (§6), statements
    before later code (§27), and sequential threading (§65). It does
    not fix the order of items.
- **Options:**
  - (a) fix it;
  - (b) leave it free, so that acceptance becomes a relation.
- **Recommended (01): (a), with the order both implementations follow
  in the tests:**
  1. a head that is a form;
  2. the macro calls among the arguments whose head is a name or
     `(share n)`, left to right;
  3. a head that is a name;
  4. the arguments, left to right, a macro call headed by any other
     form being expanded in its argument's turn;
  5. each statement before later code.

  07 reads its zipper and its mirror-shaped `Fails` as needing a fixed
  order.
- **Unblocks:** the exclusivity theorem T3, the content of errors
  (decision 13), and part of decision 5.
- **DESIGN.md wording:** needed for (a).
- **To answer:** (a) or (b). For (a), say whether the implementations'
  order is acceptable or a different one is wanted, for example one
  that expands form-headed macro calls with the others.

### Decision 6. What is a compile-time crash, or running out of fuel?

- **Question:** what happens, in the spec and the theorem, when
  compile-time code crashes or exhausts a bound?
- **What DESIGN.md and the implementations do:**
  - §31 allows crashes "where the host cannot represent what is asked
    of it". A crash "produces no value, never a different one", and how
    one is reported "is not specified". §72 makes a `native-compute`
    crash "an error at its argument".
  - Both implementations refuse a form whose run fails with a runtime
    error.
  - On a host limit, such as a stack overflow, either one dies with no
    message naming the file or the form (BUGS.md 27).
  - slc's interpreter runs on after it runs out of fuel, and may then
    die (`proto/review8/03_fuel_goes_on.sl`).
- **Options (the tracks disagree):**
  - (i) 01: the spec never crashes, and the theorem allows a third
    outcome, `Crashed`, that proves nothing. Today that outcome is a
    rejection the theorem does not cover, and it departs from §72
    unless the compiled run's outcome is an oracle input.
  - (ii) 02: a depth bound is an input. Acceptance is then a function
    of the source, the bound, the flags, and the `read-file` answers,
    given decisions 3, 4, and 5. This departs from §31's "unlimited
    stack and heap", and heap exhaustion stays host-dependent.
  - (iii) 03 and 05: keep fuel exhaustion an outcome outside the spec,
    and decide later whether statement 3 is about the spec or also
    about an implementation that "may crash".
- **Unblocks:** theorem 3's form (decision 14), the `slot-eq` oracle
  (decision 5), and whether slc conforms.
- **DESIGN.md wording:** needed for (ii), or if a crash becomes a
  rejection; (i) is a theorem choice only.
- **To answer:** (i), (ii), or (iii). Also say whether a host-limit
  death should be fixed in the implementations, as BUGS.md 27
  describes.

### Decision 4. Is the runtime evaluation order fixed?

- **Question:** must a run evaluate in one order? Owner statement 7
  asked whether DESIGN.md spells it out. It fixes eagerness (§31),
  run-position nesting (§27), and, read with §6, a head that is a
  form before the arguments. It does not fix the order of body
  statements, sibling arguments, `values` entries, or several §15
  bindings.
- **Options:**
  - (O1) fix it: statements in written order, §15 bindings before their
    statement, inner before outer, the head, then the arguments and
    `values` entries left to right, the scrutinee before the branch;
  - (O2) fix only what DESIGN.md fixes, with the spec a relation over
    orders and a diamond proof about as large as type soundness;
  - (O3) O1 now, order-independence later.
- **Recommended (02): O1, or O3.**
- **Evidence:**
  - Both implementations run a head form before an argument form, in
    seven modes, in the two world-write tests (`proto/dyn/`).
  - A real run can observe order: an argument's write is followed by
    another's crash, and §15 allows either order
    (`proto/review5/04_effect_vs_crash.sl`).
  - Whether §15's "behaves as if" fixes timing is rough edge 4.
- **Unblocks:** whether the compiler theorem is lock-step or needs
  confluence, and whether slc's emitter matches O1.
- **DESIGN.md wording:** needed for O1 and O3.
- **To answer:** O1, O2, or O3, and, for rough edge 4, whether §15's
  hoisting is meant to fix when an argument runs.

### Decisions 17 and 18. Which compiler route, and how is fuel kept out?

- **Decision 17, the route:**
  - (R1) retrofit slc: very high effort, and serial;
  - (R2) a certified kernel behind slc's unproved front end, re-running
    run-position forms;
  - (R3) a new spec-first compiler in `mini/`'s shape, reusing slc's
    proved libraries;
  - (R4) translation validation.

  **Recommended (04):** R3, with R4 only at the output end, and slc
  kept for differential testing. R3 gives parallel work per judgment
  and designs the round trip in, and slc has no spec relation to
  retrofit against. 04 guesses its size at tens of thousands of lines.
  03's fuel work assumes slc instead.
- **Decision 18, fuel out of results and theorems:** on 03's reading
  of the diagonal (00-summary key finding 2, under its premises), no
  hypothesis-free, non-erased `compile` on source text can be faithful
  on every source. So fuel either stays internal or moves into the
  driver's `Program` loop.
  - 03: a `Program`-stepped compiler for a new kernel, inline bursts
    for slc, and iterative deepening as a stopgap.
  - 04: iterative deepening at the driver now. An explicit-stack,
    fuel-free design, if wanted, must be decided before R3 starts.
  - 05: a step machine.
  - The spikes in 06 and 07 run this pattern fuel-free at toy scale,
    with partial correctness only.
- **DESIGN.md wording:** none.
- **To answer:** a route. Then say whether the fuel-free,
  `Program`-stepped design is wanted from the start, which matches the
  goal "minimize fuel use".

### After these

The glance's table gives one line for each of the other 21 decisions
(5, 7 to 16 with 8a and 8b, 18a to 18c, and 19 to 23). This session's findings bear
most on:
- **5, `slot-eq`.** A flag can now change acceptance
  (`proto/review7/01_slot_eq_native.sl`). Built code can also answer
  `ESome` where no spec run of the prelude's models can
  (`proto/review8/02_append_share.sl`). So the recommended oracle
  needs conditions on the spec's store that 02 gives as necessary,
  not sufficient.
- **14, the form of theorem 3 and its hypothesis H.**
- **13, the theorems' shape and positive `Fails`.**

## 4. Other things waiting for the owner

- **BUGS.md 26:** the reference interpreter's `-imm` blits move boxed
  values without a write barrier. 08 suggests mapping them to the
  barriered blit, as `-swap-imm` and `-place-imm` already are.
- **BUGS.md 27:** a host-limit death at compile time names nothing, and
  MANUAL.md:162-164 says such a form is refused.
- **Open from the previous handoff:**
  - whether entry 24 (README drift) belongs in BUGS.md;
  - whether entries 19 and 25 (slc after its first error) describe
    wanted behaviour. DESIGN.md is silent on both.
- **Whether to continue reviews,** or to restructure as §1 suggests.
- Stray files `/err.txt`, `/e1`, and `/e2` at the root of this
  session's container, left by reviewers. They are not in the
  repository and go away with the container.

## 5. For the next session

**Read first:** CLAUDE.md, then all of DESIGN.md (rule 19), this file,
00-glance.md, and 00-summary.md §3. agent-briefs/BRIEF.md has the only
list of owner statements, and those are paraphrases.

**Build:**
- The reference: `dune build`, giving `_build/default/bin/main.exe`.
- slc: `self/release.sh`, giving `_build/release/slc` in about 2.5
  minutes.

**Rebuilding the other toolchains:** this session's extra compilers
were in its scratchpad, which a new container will not have. GitHub
archive downloads were blocked here; Ubuntu's package archive was not.
- The sources are at
  `http://archive.ubuntu.com/ubuntu/pool/universe/o/ocaml/ocaml_5.4.1.orig.tar.xz`
  (also `ocaml_4.14.1.orig.tar.xz`) and
  `.../o/ocaml-zarith/ocaml-zarith_1.14.orig.tar.gz`. Build each with
  `./configure --prefix=...`, adding `--enable-flambda` for flambda.
- Build Zarith in its own directory with `make` and do not install it.
  Zarith's configure finds the system `ocamlfind`, and `make install`
  then writes into `/usr/local/lib/ocaml/4.14.1`. That happened once
  here and broke `--build` for about three minutes.
- For arm64: install `qemu-user-static`, `gcc-aarch64-linux-gnu`, and
  `libc6-dev-arm64-cross` with apt, then build OCaml 5.4.1 with
  `--target=aarch64-linux-gnu` and `make crossopt` and
  `make installcross`.
- `proto/gc/toolchain.sh` and `proto/gc/arm64.sh` then rerun 08's
  matrices.

**Agents:**
- Reviewers work from agent-briefs/REVIEW.md (the round-8 version) and
  BRIEF.md.
- An interruption or a container restart kills running agents. A
  stopped agent can be resumed by sending a message to its id; it keeps
  its partial edits.
- This environment's stop hook asks for every change to be committed
  and pushed, so reviews in progress are committed as snapshots.
- Mind `--extract` and `--build` argument order (an earlier run nearly
  overwrote a source file), and keep scratch outputs in the scratchpad.

**Files:**
- 00-glance.md and 00-summary.md: the condensations, which cite the
  track files.
- 00-summary-review-log.md: the history of the summary and the logs of
  its checks.
- 01 to 10: the tracks, spikes, and follow-ups. Each has review notes
  at the end, the latest overriding the earlier ones, and coordinator
  notes that record cross-file changes.
- `proto/`: every test the files cite. `proto/reviewN/` holds round N's
  tests.
- agent-briefs/: the briefs the agents worked from.
