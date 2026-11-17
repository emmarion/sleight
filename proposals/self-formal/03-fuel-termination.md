# 03. Fuel, termination, and the `Program` driver

Written overnight by a Claude agent, as one track of the self-formalization
exploration. It is a proposal and an agent's reading. Nothing in it is
approved or decided, and where it and DESIGN.md disagree, DESIGN.md is right.

## 1. Summary

- slc has one fuel that can change a verdict: the compile-time interpreter's
  depth bound (default 10⁹, fresh for each run-position form, each macro
  run, and each step of an interpreted `Program`). Running out is reported
  as a refusal of the form, which DESIGN.md does not obviously license. The
  other "fuels" are a language rule (§62's 10000 expansions), erased
  termination measures, and a handful of bounds that a measure proof could
  replace.
- The prototype (`proto/fuel/`) shows a CEK interpreter and a toy checker
  that suspends into it for compile-time splices. Every function in it is
  checked total. The only unbounded loop is the driver's loop over
  `Program`. It runs under the reference, under `slc --interpret`, and
  compiled by both. With `--eval-fuel 1000`, a 93025-step computation
  finishes when cut into `Program` steps and fails with `out of fuel` when
  run as one call, in both implementations.
- The checker refuses suspension by first-class closures. A
  continuation closure at a fixed level cannot call another one at the
  same level. A function also cannot iterate `Program` steps itself.
  Suspension therefore has to be defunctionalized: explicit data frames,
  plus one fresh `UniqueFn` per driver step that calls down to the
  stepper. I compiled each of these claims.
- A diagonal argument (a sketch, hedged in F6) says that no total Sleight
  function `compile : Src -> Verdict` can agree with the spec on every
  source, because a source can run `compile` on its own text at compile
  time (through `read-file`). So "every source is accepted or rejected"
  cannot be a Sleight function type. It can be (i) "H(src) ⇒ the driver
  reaches `Exit`", or (ii) a three-outcome theorem with `OutOfFuel`.
  "H ⇒ halts" can be proved internally from a spec derivation, but H
  itself cannot.
- Recommendation for the owner to weigh: a hybrid. Make the interpreter a
  stepped machine. Run it inline in bursts, and when a burst runs out,
  suspend to the driver and replay the current top-level form. Fuel
  then never affects a result. The alternative, CPS-converting the
  95-function elaborator block into a state machine, is cleaner but much
  larger.

## 2. Findings

### F1. What DESIGN.md says (quoted)

- §17: "Termination rests on levels." "Every call decreases a lexicographic
  order whose first component is the level, followed by the
  `subterm`-marked arguments from left to right."
- §20: "The top level is above every function level, and no function body
  can call into it." §3: "All recursion, including mutual recursion, goes
  through `def-fns` and `def-adts`." So the top level of a file cannot
  loop (my reading).
- §27: "A `Program` value (§42) is run: the driver consumes it at `unique`
  and applies each step's continuation once." §32: "The driver consumes a
  program's final `Program` value at unique (§27) and applies each
  continuation once."
- §42: "`(Program L)` is an enum indexed by a level, read by the driver
  (§27)." "It never recurses, so an unbounded interaction is the driver's
  loop over total functions." Also: "the world, the one value of `World`,
  which only the driver supplies". So compile-time code holds no `World`
  and cannot itself be a driven `Program` (my reading).
- §29: "Every fact derived from a stored value ... relies on the evaluator
  having evaluated correctly." "The checker never evaluates." §9:
  "elaborating a type calls none: the only code that runs is a macro's
  expansion (§62)."
- §31: "Evaluation is eager. The semantics is that of a machine with
  unlimited stack and heap. A real run may crash where the host cannot
  represent what is asked of it. A crash produces no value, never a
  different one."
- §62: "At most 10000 expansions run in one run, every file on the command
  line included." §49: `unary` makes "at most 1024" successors.
- §65: `read-file` reads a file at expansion time. §72: `native-compute`
  runs compiled code at compile time, and "It may crash where the
  evaluator would not, and the other way round (§31)."
- DESIGN.md does not mention fuel. It does not say whether a bound on
  evaluation is a crash that §31 permits. MANUAL.md:154-166 makes
  `--eval-fuel` crash "with `out of fuel` (DESIGN.md section 31)".

### F2. `Program` and the slc driver (code)

- `lib/prelude.sl:1337-1342`: `Exit : (erased (Level) L) (many (U8) code)`
  and `Continue : (erased (Level) L) (unique (UniqueFn L (unique (World) w
  at vacant-slot) -> (unique (World) w2 at w) (unique (Program L) p)) k)`.
- `self/main.sl:186-191`: slc is `(Continue _ start)` with `start` at
  `io-lvl`. The whole compile runs inside that one step. `Continue` occurs
  again only in `self/interp.sl:114`, where `--interpret` turns each step
  of the interpreted program into one of slc's own. Each such step calls
  `apply` with a fresh fuel (`interp.sl:109`, `143`).
- `self/interp.sl:61,67`: `interp-lvl` is minted before `io-lvl`. The step
  closure at `io-lvl` calls `interp-program` at `interp-lvl` (lines
  98-114). This is the same knot as my prototype's `drive`/`again`.

### F3. Inventory of fuel in slc

| # | Where | What it bounds | On exhaustion | Removable? |
|---|---|---|---|---|
| 1 | interpreter `eval`/`apply`, `self/elab-main.sl:159-190, 405-430`. Default `1000000000` in `self/core.sl:3614` (`MkMacros ... 1000000000`), `--eval-fuel` in `self/main.sl:121-132` | Depth of application nesting. Two units per interpreted call, and tail calls spend too. Fresh per run-position form (`elab-main.sl:450-462, 550, 744`), per macro run (`:525`), and per interpreted `Program` step (`interp.sl:109,143`) | `BError "out of fuel"`. The form is refused like any runtime error (MANUAL.md:158-162) | Only by restructuring (options below). This is the fuel that matters. |
| 2 | Expansion budget: `expansion-limit` 10000 (`self/elab.sl:26`), checked globally at `elab-main.sl:559-560`. Also threaded as the structural `fuel` parameter of the elaborator block, reset to 10000 per top-level item (`elab-main.sl:3379, 3387, 3391`) | §62's language rule. The per-item parameter is also the block's first termination measure | Error "more than 10000 macro expansions" | The global count is the spec and stays. The per-item parameter looks like a measure the global count always hits first. I have not verified that. |
| 3 | Erased measures: `xf`, `callbacks`, `hop-k` (`elab-main.sl:143-159`), `Steps` (`elab.sl:1242`), and the sugar budget | Termination evidence only. Zero cases are refuted. The sugar budget's zero case is an internal error (README "Choices") | Refuted or internal error | Already not fuel in the sense of an extra outcome. |
| 4 | Generated printer `show-fuel` 100000 (`self/emit.sl:4, 1379-1438`) | Recursion through types when emitting printers | Falls back to `"show_any"` or empty arms (`emit.sl:1380, 1417, 1438`). This changes emitted code, not a verdict | Possibly, by a measure on the memo. Unverified. |
| 5 | Store walks: `list-refs` and `rope-walk` with fuel = heap size or twice it (`self/eval.sl:171-180, 455-473`), and `heap-strs`/`heap-pairs`/`heap-jobs` with 1000000 (`eval.sl:1018-1055`) | Walking lists in the mutable store | `None` or `Fail`, then an error block | Needs either an acyclicity measure (addresses pointing below) or a visited set. I could not determine whether `hwrite` can make cycles. |
| 6 | Length-bounded loops: `str-split-fuel` (`self/base.sl:100-109`, fuel = string length), `parse-pieces` (`emit.sl:138-153`), `frame-chain` (`elab.sl:816-828`, fuel = the frame id itself), and `merge-opens` (`elab.sl:1987-2004`, fuel = count of opened objects + 1) | Loops whose real measure is a length or an id | Silent truncation or an early `UOk` | Yes: with a decrease proof, as `reader.sl` already does for `str-split` with an `Add` invariant (README "reader.sl"). |
| 7 | Reference: `lib/eval.ml:4, 70-79`, `fuel : int option ref = ref None` | No bound unless `--eval-fuel` is given | `Runtime "out of fuel"` | The reference diverges on a diverging compile-time run. |

Note: self/README.md says the interpreter's fuel is "1000000". The code
(`core.sl:3614`) and MANUAL.md:163 say 1000000000. The README looks stale.

### F4. Compiled checks of the suspension patterns (rule 2)

Files are in my scratchpad and are not committed. Reproduce each from the
text here.

1. **A CPS bind over closures is refused.** Take `Res = RDone n | RAsk q (k
   : Fn L (Nat) -> (Res))`. A `bind` at level L that calls `g` gives
   `error: same-level call to g decreases no subterm argument`. A `bind` at
   a higher level B, building `k2` at L that calls `k`, gives the same
   error at `(k a)`. A resume closure at fixed level L cannot call
   another resume closure, so nested suspensions cannot be composed as
   closures.
2. **A function cannot iterate `Program` steps.** The function `run-all :
   (subterm unique (Program L) p) (World) -> ...` matches `Continue _ k`,
   calls `(k w)`, and recurses on the result `p2`. It is refused:
   "`p2` is not a strict subterm of `(Continue L k)`". This matches
   SOUNDNESS.md's point 3, "A stored function is a leaf". Only the driver
   iterates, or a function that is given fuel.
3. **The `Program` knot is accepted, as in `interp.sl`.** `drive` at PA
   returns `Continue P again`. `again` is a `def-unique` at P, defined in
   `drive`'s body and closing over `many` state, and it calls `drive`.
   The constraint I hit twice: **every function a step calls must be
   minted before `P`** ("`(level-of arg-nat)` was not in scope when level
   `P` was minted"). The driver's level must come last in the file order.

### F5. Prototype results

`proto/fuel/machine.sl` contains these parts:
- A CEK machine for an untyped call-by-value λ-calculus with numerals,
  `+`/`*`/monus, and `ifz`. It has an explicit environment and a stack of
  continuation frames.
- `step : State -> Out State`, total by checking. It is not recursive
  except for `lookup` on the environment.
- A toy checker in the same machine. `MState` is `Checking src depth
  frames | Built term frames | Comptime cek frames | Running cek`. A
  splice `SRun t` suspends checking into `Comptime`, and the checker
  resumes on the numeral the CEK machine halts with. An unbound variable,
  a stuck splice, or a closure-valued splice rejects the source.
- `burst` (n steps, structural on n) and `drive` (one `Program` step per
  burst).

`cek.sl` runs `sum n` through the Z combinator. `suspend.sl` checks a
source with splices and then runs the result.

Runs:
```
main.exe machine.sl suspend.sl -- 0 10 1  -> value 116 after 370 steps, 370 Program steps   (exit 0)
                                  1 10 1  -> rejected: unbound variable 1 ...               (exit 1)
                                  2 10 1  -> rejected: compile-time run stuck: applied a number (exit 1)
                                  3 10 1  -> splice is omega: runs until killed, constant 22 MB at 3 s and at 8 s
slc --interpret: same outputs. slc --build and main.exe --build: same outputs.
```

The fuel escape, in both implementations:
```
--eval-fuel 1000, cek 3000 1       -> value 4501500 after 93025 steps, 93025 Program steps
--eval-fuel 1000, cek 3000 100000  -> runtime error: out of fuel
```

Cost of a `Program` step. These are single runs on one machine, so
they are rough:

| implementation | per machine step, batched | extra per `Continue` |
|---|---|---|
| reference interpreter (93025 steps) | ≈ 4 µs | ≈ 4 µs |
| `slc --interpret` (93025 steps) | — (elaboration dominates) | ≈ 1 µs |
| reference `--build` (31M steps) | ≈ 11 ns | ≈ 10 ns |
| `slc --build` (31M steps) | ≈ 15 ns | ≈ 9 ns |

With bursts of 1000 steps per `Continue` the overhead is negligible. The
only friction was the level order (F4.3) and a type and a constructor
sharing the name `Fin`.

### F6. The diagonal argument

This is a sketch: my own reasoning, not checked.

Assume `compile : Src -> Verdict` is a total Sleight function that agrees
with the spec on every source. slc's sources are Sleight files, so a
source Q can load them and call `compile` in run position. Q can obtain
its own text with `read-file` inside a macro (§65). Q then runs
`compile` on itself and, in run position, does the opposite of the
answer: `compile-error` if the answer is accept, accept otherwise. Under
the assumption, Q's spec run terminates, so Q's spec verdict exists and
differs from `compile(Q)`. That is a contradiction.

So no total Sleight function is a faithful compiler for all sources. The
same argument applies to a total, faithful universal evaluator. This is
Kleene's diagonalization, and it needs no appeal to Gödel's second
theorem. Gödel II is the logical shadow of it: a language that proved
the termination of all its own programs would roughly prove its own
consistency.

The escape hatches:
- `compile_n` with fuel: Q's call to `compile_n(Q)` needs more than n
  steps, so it answers `OutOfFuel`.
- The `Program` driver: its loop is not a function Q can call (F4.2), and
  compile-time code has no `World`.

Hedges:
- This assumes slc's code can be run at compile time by a source, which
  I believe holds (slc's own `native-compute` runs `ocamlfind`, and a
  source can load `self/*.sl`). I did not build Q.
- README.md's strength remark ("about IΣ₂ ... ordinal ω^ω^ω") is
  attributed there to "the author". I make no claim about it. The
  argument above does not depend on it.

### F7. What the hypothesis H amounts to

My reading: H is "every compile-time evaluation the spec performs while
deciding src halts". Going through DESIGN.md, compile-time computation
happens at these places:
- run-position forms and everything they call (§27, §29);
- macro functions (§62), at most 10000 of them per run;
- macro primitives, which check and canonicalize but do not evaluate
  (§65, §29 "The checker never evaluates");
- `unary`, at most 1024 successors (§49);
- `native-compute`, which runs compiled code and an external toolchain
  (§72);
- `read-file`, which is host I/O (§65).

The top level cannot loop (§3, §20). So H would follow from two things:
- SOUNDNESS.md's claims (T), totality, and (C), checking terminates,
  applied to the code that is run;
- host assumptions. `read-file` must not block, for instance on a FIFO.
  DESIGN.md does not say whether that can happen. The external compile
  and run under `native-compute` must also halt.

In that reading, H is an instance of the language's own termination
claim plus I/O. By F6 it is not provable in Sleight for all sources.
For one given source it is a statement about that source, so it may be
provable case by case.

A divergence source that I believe is *not* there: macro → elaboration →
macro recursion is bounded by §62's global count, and slc enforces that
count at `elab-main.sl:559-560`.

## 3. Options

### Q1. How to take fuel out of the verdict

**(a) The whole compiler as a state machine stepped by `Program`.**
- Design: defunctionalize the elaborator's 95-function main block
  (`elab-main.sl:158` onward, about 3240 lines) and the interpreter into
  one `MState` with explicit frames, as `machine.sl` does at toy scale.
  slc's `start` becomes `drive init`.
- Pros:
  - There is no fuel anywhere.
  - Every step is total by checking.
  - The theorem shape is the cleanest (Q2).
  - The `xf`/`callbacks`/`hop-k` measures disappear.
- Cons: a rewrite of the largest and most intricate part of slc. The
  code becomes frame-oriented and less readable. Closures cannot do the
  composition (F4.1), so every non-tail call site becomes a frame
  constructor.
- Risks:
  - Performance (each `Continue` costs about 10 ns compiled, but the
    frame allocation per elaborator call is untested).
  - Rule 17's self-compile timing.
- Cost: very high for slc. Moderate for a new, small certified kernel
  written in this style from the start.

**(b) Iterative deepening.**
- Design: `compile_n` as today, with `OutOfFuel` made a distinct outcome
  rather than an error message. On `OutOfFuel` the driver restarts with
  2n, either the whole compile or only the current top-level form, using
  the environment checkpoint that `run-toplevel` already has.
- Pros: small change. Fuel never shows in a result. The total time is at
  most about twice that of the run that succeeds.
- Cons:
  - Needs a monotonicity lemma: success at n gives the same result at
    every m ≥ n.
  - Effects are re-performed on restart (`native-compute` runs, file
    reads). They are probably idempotent but not formally so.
  - Depth fuel decreasing on tail calls (README) makes a long loop need
    large n.
- Cost: low.

**(c) Keep fuel and prove it is the only extra outcome.**
- Design: the theorem is "accept ⇒ spec accepts, reject ⇒ spec rejects,
  `OutOfFuel` ⇒ no claim". `OutOfFuel` must be separated from
  rejection: today it is a rejection (F3 row 1).
- Pros: cheapest, and honest.
- Cons: owner decision 3 ("accepted or rejected") holds only
  conditionally and is not realized by the tool. A user can see
  `OutOfFuel` on a program the spec accepts.
- Cost: low (relabel the outcome, then the proofs).

**(d) A stratified, normalizing interpreter.**
- Design: the interpreter terminates by a measure mirroring the program's
  levels and subterm order, as a normalization proof in Sleight.
- Pros: no driver loop. A total function.
- Cons: F6 rules it out for all sources. At best it works for a fragment
  bounded by a fixed number of levels and `subterm` parameters, with
  "too deep" as a new extra outcome, i.e. fuel in another shape. It would
  also need the checker's soundness invariants as the interpreter's
  input evidence.
- Recommendation: do not pursue, except as research.

**(e) Hybrid: a stepped interpreter, bursts inline, and replay.**
- Design:
  - The interpreter becomes `step` over an explicit machine state, as in
    `machine.sl`.
  - The elaborator calls `burst B` inline. On `Paused`, it aborts the
    current top-level form, returning the paused machine and the index
    of the request.
  - The driver finishes the machine in `Program` steps, appends the
    answer to an oracle list, and re-elaborates that form. Answers
    already in the oracle are not recomputed.
  - Inline bursts and driver steps are the same `step`, so B affects
    cost only.
- Pros:
  - No result depends on B.
  - The elaborator stays direct-style.
  - Only the interpreter is rewritten, and every fuel-free option needs
    that anyway.
  - Replay is rare: only evaluations longer than B trigger it.
- Cons:
  - Needs oracle plumbing (the `ElabWorld` could carry it).
  - Needs the theorem "replay with true answers equals direct
    elaboration".
  - Effects are re-performed on replay, as in (b).
  - The macro primitives' callbacks into the elaborator must be total
    non-evaluating functions callable within one step. slc currently
    puts them in the same block, under the `callbacks` measure. I have
    not checked whether they can be split out.
- Cost: medium.

### Q2. Theorem shapes (my proposal)

Let `Verdict src v` be the spec's inductive (big-step) relation. A
source whose compile-time run diverges has no derivation.

- (P1) Partial correctness. If the procedure produces v, then `Verdict
  src v`. Under (a) and (e), the state carries an erased partial
  derivation, and `step` preserves it.
- (P2) Each step is total. This is free from checking. Under (b) and (c),
  `compile_n` is total.
- (P3) Completeness. From an erased `(Verdict src v)` derivation, the
  procedure produces v: under (a) and (e) as a step count n with a proof
  that iterating `step` n times reaches v, and under (b) as an n with
  `compile_n src = v`. This is structural recursion on the derivation,
  so it can be an erased Sleight function. F6 does not forbid it,
  because F6 forbids proving H, not proving H ⇒ halts. Unverified.
- Determinism: v is unique.
- Owner decision 3 then reads "∀ src, H(src) ⇒ the driver reaches
  `Exit` with accept or reject". For (c) it reads "∀ src, H(src) ⇒ ∃ n,
  `compile_n src ≠ OutOfFuel`", where the tool fixes n.
- The fact that `drive`'s `Continue` chain iterates `step` follows from
  how `drive` is written. It is external to the language, since the
  driver is.

### Q3. Secondary fuels (F3 rows 4-6)

- (i) Replace each with a measure proof: string-length `Add` invariants;
  frame ids with `Lt`; a length-indexed list of opened objects; a
  visited set or an address-descent invariant for store walks.
- (ii) Leave them, documented as "cannot affect a verdict".
- Row 6 truncates silently on exhaustion. Even though the bound is
  believed sufficient, (i) seems worth its low cost there.

## 4. Decisions for the owner

1. **Does "fuel" bounding a compile-time run count as a §31 crash?**
   Recommended: no. Treat `OutOfFuel` as an outcome outside the spec,
   so that (c) has to say so explicitly. It affects whether slc's
   current behaviour (F3 row 1) is conforming.
2. **The form of decision 3: (i) "H ⇒ the driver reaches `Exit`", or
   (ii) a three-outcome theorem with `OutOfFuel`?** Recommended: (i).
   F6 suggests that no total function can do better, and the prototype
   shows the `Program` loop can carry it. This choice decides between
   (a)/(e) and (b)/(c).
3. **Which route: (a), (b), (c), or (e)?** Recommended: (e) for slc, and
   (a) only for a new small kernel built that way from the start. (b) is
   the cheap stopgap. Converting the interpreter to a stepped machine is
   needed by (a) and (e).
4. **Is H stated over the spec run including host I/O (`read-file`,
   `native-compute`), or are those axiomatized as terminating?**
   Recommended: axiomatize them, and state H for evaluation only.
5. **Should the formal spec model §62's 10000-expansion cap and §49's
   1024 as language rules?** Recommended: yes. They are in DESIGN.md, so
   they are not fuel.

## 5. Rough edges in DESIGN.md (questions, not resolved)

- §31: "A real run may crash where the host cannot represent what is
  asked of it." MANUAL.md cites this for `out of fuel`, but a fuel
  bound is not obviously "cannot represent". DESIGN.md is silent on
  bounding evaluation.
- §62: "At most 10000 expansions run in one run". DESIGN.md does not say
  that the 10001st is an error. Both implementations make it one.
- §65 `read-file`: DESIGN.md does not say what happens with a file whose
  read does not end, such as a FIFO inside the source directory.
- §29/§31: the spec of a compile-time run is "the evaluator", with
  "Evaluation is eager". For P1 and P3 the run must be a defined
  relation. Evaluation order is the subject of another track.
- §42: "an unbounded interaction is the driver's loop over total
  functions". Consistent with F4.2. DESIGN.md does not say whether an
  implementation may itself be such a loop. That is an implementation
  matter, but the theorem in Q2 relies on it.

## 6. Unverified claims

- F6 as a whole. I did not build Q. Nor did I confirm that a source can
  load and run slc's own functions at compile time within §62's cap and
  practical time.
- That the per-item expansion parameter (F3 row 2) never binds before
  the global count.
- Whether the store can hold cycles (F3 row 5).
- That `show-fuel` exhaustion only degrades printing (F3 row 4).
- That the macro primitives' elaborator callbacks never evaluate, which
  (e) requires.
- That P3 can be written as an erased Sleight function.
- The cost of option (a) on slc. The cost figures in F5 come from single
  timings on one machine.
- That a generic `burst` over any step function would type-check through
  a level factory (§57). The prototype avoided it by using one machine
  type.
