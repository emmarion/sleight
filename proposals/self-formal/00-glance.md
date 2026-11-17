# 00. At a glance

Written by Claude agents overnight. Proposals and agents' readings only; nothing is approved or decided.
Every line condenses the 00-summary section it cites; where they differ, 00-summary (and its Review notes,
Second review propagation, and Third review notes) is right.
"Owner statement n" items are an earlier session's paraphrases, not the owner's words (00-summary header).

## What was done

- Five research tracks: 01 spec shape, 02 dynamic semantics, 03 fuel and termination,
  04 compiler route, and 05 theorems (00-summary header, §1).
- Two compiled spikes on toy languages: 06 a certified fuel-free stepper and
  07 the §29 round trip with a suspendable checker (00-summary §7).
- Each file was adversarially reviewed twice ("Review notes", then "Second review notes"), and 00-summary was
  reviewed and then updated to the second reviews (00-summary Review notes, Second review propagation).
- Prototypes are under `proto/` (e.g. `proto/fuel/`, `proto/stepper/`, `proto/roundtrip/`, and the second
  reviews' `proto/review2/`) (00-summary §2, §7).

## Five things worth knowing first

- **Diagonal.** If Sleight's functions terminate (SOUNDNESS.md's (T), argued, not proved), no non-erased
  `compile : Src -> Verdict` with no further evidence can be faithful on every source; only the mechanism is
  tested. It does not refute owner statement 4(ii) as mathematics, nor a `compile` taking erased evidence of H
  for its one source. slc does not escape it: its compile is one `Program` step bounded by fuel, and its `World`
  blocks only the literal construction (03's reading). 05 now agrees it needs T1–T4 and determinism, not T5,
  and no quine in its `read-file` macro form (00-summary §2 item 2).
- **Spikes.** The intrinsic-derivation plus `Program`-driver pattern compiles and runs at toy scale, fuel-free, on both
  implementations, but proves partial correctness only: an always-"stuck" (06) or never-answering (07) step passes,
  and 07's `Rejected` reason text is unconstrained. With one nondeterministic rule added, 07's exclusivity fails
  (compiled). Neither models Sleight's own machine (00-summary §2 items 16, 17).
- **`slot-eq`.** §67 lets answers differ between runs, so acceptance can depend on the implementation; answers already
  differ (interpreters vs `--build` binaries with externs on `imm_eq.sl`; slc's native build vs `--byte`,
  `--interpret`, and the reference on `slot_eq_share.sl`). That an `ENone` answer rejects is inferred. The output
  theorem therefore cannot be "the same values, up to crash"; 04 makes `slot-eq` a second oracle beside `world-do`
  (§2 items 5, 18).
- **Evaluation order.** DESIGN.md fixes eagerness and some run-position order, but not body statements, sibling arguments,
  `values` entries, or several §15 bindings in general; elaboration order is visible through gensyms (00-summary §2 item 6).
- **slc printer defect.** `slc --interpret` on a 100003-element list prints 49,999 `Cons _ 0` then `Cons _ _ _)`:
  a wrong value, not a §31 crash. It is confined to `show-at` (`--interpret`'s final printer, `comptime-match`
  mismatch messages, and `dump-context` reports); compiled slc output and the reference print all elements
  (00-summary §2 item 10).

## Decisions, at a glance (00-summary §3)

"Linked" copies each decision's "Depends on it" line in §3; that line names dependents in most entries
but sometimes the decisions an entry itself rests on (e.g. 6 lists 14 and 14 lists 6), so read it as "linked to".
Wording column: whether DESIGN.md wording would be needed, as §3 marks it.

| # | Question | Recommended | Linked | Wording |
|---|---|---|---|---|
| 1 | Where does the spec start? | (a) source bytes, small reader before a `Raw` relation (01, 04) | 14, 17 | no |
| 2 | What does "parameterized the semantics" mean? | (b) generic over a model record (05); 04: extern table | 9, 16 | no |
| 3 | Is the order of elaboration part of the language? | (a) fix it: head, then items left to right (01) | 5, 13 | part |
| 4 | Is the runtime evaluation order fixed? | fix it, O1/O3 (02); 04 asks if order is unobservable | — | part |
| 5 | How is `slot-eq`'s nondeterminism handled? | (a) oracle parameter (01, 02, 05; 04 treats it as one); shapes differ | 8 | part |
| 6 | What is a compile-time crash or fuel exhaustion? | tracks disagree; 01 and 02 opposite, now cross-referenced | 5, 14 | part |
| 7 | Does the spec run post-erasure code? | R1, as §27 and §29 say (02) | — | no (R3 departs from §37, §39) |
| 8 | Machine state and addresses? | A1: `Imm n \| Ptr a`, abstract never-reused addresses (02) | 5 | no, unless sharing goes in |
| 8a | Compile-time run small-step over the compiler's machine? | (a) yes, to keep the evaluator proof small (07) | 8 | no |
| 8b | Next spike on unique `Array` heap, abstract addresses? | yes, before scaling (06) | — | no |
| 9 | Externs in the spec? | tracks disagree (02: E2; 04, 05: parameterize) | 2 | no |
| 10 | Where may a compiled run crash? | C2, named resource events; C3 later (02); 04: "a value some spec run gives, or a crash" | — | no (review unsure) |
| 11 | What happens when the spec goes wrong? | 02: S1 defined `abort`; 05: no recommendation | — | no (review unsure) |
| 12 | Compile-time values in output: trees or heap graphs? | V1 trees, unless a reason for V2 (02) | — | no |
| 13 | Intrinsic theorems, positive `Fails`, rejection contents? | intrinsic, positive `Fails`; tracks disagree on its shape | 3 | no |
| 14 | Form of theorem 3 and hypothesis H? | tracks disagree | 6, 18 | part (budget option) |
| 15 | Which flags are spec parameters; is expansion limit one? | 01's flag list; tracks disagree on the limit | — | part (10001st expansion) |
| 16 | What is the prelude to the spec? | tracks disagree (01: any prelude text, `--no-prelude` qualified; 05: too wide) | — | no |
| 17 | Which compiler route? | R3, new spec-first compiler; slc for differential tests (04) | 18–23 | no |
| 18 | How is fuel kept out of results and theorems? | tracks disagree | 17 | no |
| 18a | Resumable checker: derivation zipper or replay? | zipper for a new kernel; replay only retrofitting slc (07) | 17, 18 | no |
| 18b | Certified stepper invariant: erased trace or counter closure? | erased trace, as a working hypothesis (06) | — | no |
| 18c | Apply a closure whose level is packed in its argument? | no change proposed (06) | — | only if changed |
| 19 | Judgment shape and staging? | 01 §4.2 layers (Γ/Σ home of run-position facts open); run relation as a parameter (01) | — | no |
| 20 | Where does the proof stop at the output end? | O1 now, O2 + O4 later (04) | — | no |
| 21 | `native-compute`? | N3, same trust as the output end (04) | — | no, unless 6 changes §72 |
| 22 | Which checker's PASS is the trust root? | B1 (04); 05 no recommendation | — | no |
| 23 | Prove sole-reference and full-semantics safety inside Sleight? | plausible and worth it (05) | — | no |

"—" means the entry's "Depends on it" line names no decision number, or there is none.
17's line reads "everything in this group" (decisions 17 to 23).

## Suggested order to decide

§3 is ordered so a decision precedes those that depend on it; on its links, these come first:

1. **Decision 1** (spec start): bears on theorem 3's statement and on route R2 (§3 decision 1).
2. **Decision 2** (what "parameterized" means): bears on 9 and 16 (§3 decision 2).
3. **Decision 3** (elaboration order): bears on T3, 13's error content, and the oracle (5) (§3 decision 3).
4. **Decision 6** (compile-time crashes): bears on 14 and 5, and on whether slc conforms (§3 decision 6).
5. **Decision 4** (runtime order): bears on lock-step versus confluence for the compiler theorem (§3 decision 4).
6. **Decision 17** (route), with 18: everything in group E depends on 17, and 04 says its F2, if wanted, must be
   decided before R3 starts (§3 decisions 17, 18).

## What the second reviews changed most (00-summary Second review propagation)

- Retracted: slc escaping the diagonal; "slc stops running compile-time code after an error"; the
  printer defect possibly reaching compiled output (items 1, 7, 11).
- Now compiled: exclusivity failing for one nondeterministic variant (07); generic matching on a parameter
  relation (05); the column unit as bytes (01) (items 10, 11, 19).

## Third review notes

- Twelve corrections, listed in 00-summary's Third review notes. Among them: the printer defect also reaches
  `dump-context` reports (`proto/review2/00_dump_deep.sl`); rough edge 17 now includes `settled-val-apply`;
  rough edge 12 no longer makes §33's `Nat` identity conditional.
