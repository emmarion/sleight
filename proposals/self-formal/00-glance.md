# 00. At a glance

Written by Claude agents overnight. Proposals and agents' readings only; nothing is approved or decided.
Every line condenses the 00-summary section it cites; where they differ, 00-summary is right.
"Owner statement n" items are an earlier session's paraphrases, not the owner's words (00-summary header).

## What was done

- Five research tracks: 01 spec shape, 02 dynamic semantics, 03 fuel and termination,
  04 compiler route, and 05 theorems (00-summary header, §1).
- Two compiled spikes on toy languages: 06 a certified fuel-free stepper and
  07 the §29 round trip with a suspendable checker (00-summary §7).
- Three follow-up notes: 08 `imm`-store GC safety, 09 Gödel II and SOUNDNESS.md part 5, and 10 slc after an
  error (00-summary §2 items 19 to 22).
- Prototypes are under `proto/` (e.g. `proto/fuel/`, `proto/stepper/`, `proto/roundtrip/`, and
  `proto/godel/`) (00-summary §2, §7).

## Five things worth knowing first

- **Diagonal.** If Sleight's functions terminate (SOUNDNESS.md's (T) and (E), argued, not proved, and read as 03 reads
  them), then, under further premises 09 lists, no non-erased `compile : Src -> Verdict` with no further evidence can be
  faithful on every source; only the mechanism is tested. It does not refute owner statement 4(ii) as mathematics, nor a `compile` taking erased evidence
  of H for its one source, though, if Sleight is sound, the diagonal source cannot produce that evidence for itself
  (03's reasoning). 03 carries (T) and (E) to that source through an accepted detour that calls `compile` in a final
  value (compiled with a toy), reading part 5, which never mentions that call, as covering it; (C) is not used. slc
  does not escape it (03's reading). 05's version also needs logic soundness and crashes kept out of the oracle (00-summary
  §2 items 2, 21).
- **Spikes.** The intrinsic-derivation plus `Program`-driver pattern compiles and runs at toy scale, fuel-free, on
  both implementations, but proves partial correctness only: an always-"stuck" `step`, `advance`, or `run-total` (06)
  or a never-answering `step` (07) passes, and 07's `Rejected` reason text is unconstrained. For one variant with a
  nondeterministic rule added, both derivations exist (compiled). Neither models Sleight's own machine (00-summary §2
  items 16, 17).
- **`slot-eq`.** §67 lets answers differ between runs, so acceptance can depend on the implementation; answers already
  differ between implementations and modes, though not between runs as far as seen (`imm_eq.sl`, `slot_eq_share.sl`).
  Both answers now reach acceptance: a `comptime-match` on `slot-eq` asked through `native-compute` passes by
  default and fails under `--no-native`, on both implementations (`01_slot_eq_native.sl`). The output theorem therefore
  cannot be "the same values, up to crash";
  04 makes `slot-eq` an oracle beside the host's answers to `world-do` and `read-file` (00-summary §2 items 5, 18).
- **Evaluation order.** DESIGN.md fixes eagerness and some run-position order, but not body statements, sibling
  arguments, `values` entries, or several §15 bindings in general. Elaboration order is visible through gensyms; both
  implementations elaborate a head that is a form (inferred), then expand an application's argument macro calls, then
  elaborate a head that is a name, then the arguments, left to right. At runtime both implementations, in the seven
  modes tried, run a head form before an argument form in the two tests built to show it. A real run observes order
  via a §31 crash, which the spec's run would not have: an argument's write precedes another's crash, §15 allowing
  either order (00-summary §2 item 6).
- **slc printer defect.** `slc --interpret` on a 100003-element list prints 49,999 `Cons _ 0` then `Cons _ _ _)`: a
  wrong value, not a §31 crash, from `show-at`, which also feeds `comptime-match` messages and `dump-context` reports;
  compiled slc output and the reference print all elements. `heap-strs-fuel` likewise cuts a request's string list
  short past 10^6 elements (00-summary §2 item 10; BUGS.md 23, 18).

## Follow-ups 08 to 10 (00-summary §2 items 19 to 22, §8)

- **GC.** Compiled `imm` stores look GC-safe on OCaml 4.14.1 when both words are immediates, among 08's conditions
  (08's reading); 08's stress tests also pass on 4.14.1 with flambda, on 5.4.1 with and without flambda (systhreads
  and domains too), and on arm64 under qemu, while real arm64 hardware and the multi-domain memory model are
  unchecked. The reference interpreter's `-imm` blits corrupt its heap (all three tried; BUGS.md 26).
- **Gödel II** may apply; nothing establishes it. Missing: a formalized `Prov` with D1 to D3, a diagonal sentence (a
  macro in a goal type can build one from its own file's text), and lemmas tying `Prov` to the stripped run. The
  derivation's internal steps (⊢ Con → ¬`P g`) go through despite level stratification for an abstract relation given
  D2, D3, and the diagonal's D1 instance as hypotheses (`g2_step.sl`); reading that as ⊢ Con → G needs `g` to be a code
  of ¬`P g` itself, which no structural formula code can be and a unit's text might (`09_g2_cycle.sl`). 03's diagonal already rules out a
  faithful hypothesis-free `compile`, under its premises; Gödel II, if those hold and Sleight is consistent, would
  make uniform stripped-run safety unprovable (09).
- **slc after its first error** can print false later messages and drops some; acceptance seems unchanged (10; BUGS.md 25). Defects
  found are in BUGS.md 13, 18, 19, and 23 to 27.

## Decisions, at a glance (00-summary §3)

"Linked" copies each decision's "Deps" entry in §3, which sometimes names what an entry rests on rather than its
dependents (e.g. 6 lists 14 and 14 lists 6), so read it as "linked to".
Wording column: whether DESIGN.md wording would be needed, as §3 marks it.

| # | Question | Recommended | Linked | Wording |
|---|---|---|---|---|
| 1 | Where does the spec start? | (a) source bytes, small reader before a `Raw` relation (01, 04) | 14, 17 | no |
| 2 | What does "parameterized the semantics" mean? | (b) generic over a model record (05); 04: extern table | 9, 16 | no |
| 3 | Is the order of elaboration part of the language? | (a) fix it: form head, argument macro calls, name head, then arguments, left to right (01) | 5, 13 | part |
| 4 | Is the runtime evaluation order fixed? | fix it, O1/O3 (02); 04 asks if order is meant to be fixed | — | part |
| 5 | How is `slot-eq`'s nondeterminism handled? | (a) oracle parameter (01, 02, 05; 04 treats it as one); shapes differ | 8 | part |
| 6 | What is a compile-time crash or fuel exhaustion? | tracks disagree; 01 and 02 opposite, cross-referenced | 5, 14 | part |
| 7 | Does the spec run post-erasure code? | R1, as §27 and §29 say (02) | — | no (R3 departs from §37, §39) |
| 8 | Machine state and addresses? | A1: `Imm n \| Ptr a`, abstract never-reused addresses (02) | 5 | no, unless sharing goes in |
| 8a | Compile-time run small-step over the compiler's machine? | (a) yes, the evaluator proof a list of step proofs (07) | 8 | no |
| 8b | Next spike on unique `Array` heap, abstract addresses? | yes, before scaling (06) | — | no |
| 9 | Externs in the spec? | tracks disagree (02: E2; 04, 05: parameterize) | 2 | no |
| 10 | Where may a compiled run crash? | C2, named resource events; C3 later (02); 04 asks if "a value some spec run gives, or a crash" | — | no (unsure) |
| 11 | What happens when the spec goes wrong? | 02: S1 defined `abort`; 05: no recommendation | — | no (unsure) |
| 12 | Compile-time values in output: trees or heap graphs? | V1 trees for the theorem, V2 an option, the spec's store a heap (02) | — | no |
| 13 | Intrinsic theorems, positive `Fails`, rejection contents? | intrinsic, positive `Fails`; tracks disagree on its shape | 3 | no |
| 14 | Form of theorem 3 and hypothesis H? | tracks disagree | 6, 18 | part (budget option) |
| 15 | Which flags are spec parameters; is expansion limit one? | 01's flag list; §62's 10000 kept (01, 03, 04), only a parameter `N` open | — | part (10001st expansion, or `N`) |
| 16 | What is the prelude to the spec? | tracks disagree (01: any prelude text, `--no-prelude` qualified; 05: too wide) | — | no |
| 17 | Which compiler route? | R3, new spec-first compiler; slc for differential tests (04) | 18–23 | no |
| 18 | How is fuel kept out of results and theorems? | tracks disagree | 17 | no |
| 18a | Resumable checker: derivation zipper or replay? | zipper for a new kernel; replay only retrofitting slc (07) | 17, 18 | no |
| 18b | Certified stepper invariant: erased trace or counter closure? | erased trace, as a working hypothesis (06) | — | no |
| 18c | Apply a closure whose level is packed beside it? | no change proposed; it works with a packed `Predates` or one derived from a `Predates` about its holder, except, on 06's reading of §18, applying one extended at a level minted during the run (06) | — | only if changed |
| 19 | Judgment shape and staging? | 01 §4.2 layers (Γ/Σ home of run-position facts open); run relation as a parameter (01) | — | no |
| 20 | Where does the proof stop at the output end? | O1 now, O2 + O4 later (04) | — | no |
| 21 | `native-compute`? | N3, same trust as the output end (04) | — | no, unless 6 changes §72 |
| 22 | Which checker's PASS is the trust root? | B1 (04); 05 no recommendation | — | no |
| 23 | Prove sole-reference and full-semantics safety inside Sleight? | plausible and worth it (05) | — | no |

"—" means the entry's "Deps" names no decision number, or there is none. 17's reads "all of group E" (decisions 17 to 23).

## Suggested order to decide

§3 is ordered so a decision precedes those that depend on it; on its links, these come first:

1. **Decision 1** (spec start): bears on theorem 3's statement and on route R2 (§3 decision 1).
2. **Decision 2** (what "parameterized" means): bears on 9 and 16 (§3 decision 2).
3. **Decision 3** (elaboration order): bears on T3, 13's error content, and the oracle (5) (§3 decision 3).
4. **Decision 6** (compile-time crashes): bears on 14 and 5, and on whether slc conforms (§3 decision 6).
5. **Decision 4** (runtime order): bears on lock-step versus confluence for the compiler theorem (§3 decision 4).
6. **Decision 17** (route), with 18: everything in group E depends on 17, and 04 says its F2, if wanted, must be
   decided before R3 starts (§3 decisions 17, 18).

Review history, corrections, and re-runs: 00-summary-review-log.md.
