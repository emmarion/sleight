# 03. Fuel, termination, and the `Program` driver

Written overnight by a Claude agent, as one track of the self-formalization
exploration. It is a proposal and an agent's reading. Nothing in it is
approved or decided, and where it and DESIGN.md disagree, DESIGN.md is right.
"Owner item n" and "decision 3" refer to the brief's list of owner
decisions, which is an earlier session's paraphrase, not the owner's words.

## 1. Summary

- slc has one fuel known to change a verdict: the compile-time interpreter's
  depth bound (default 10⁹, fresh for each run-position form, each macro
  run, and each step of an interpreted `Program`). Running out is reported
  as a refusal of the form, which DESIGN.md does not obviously license. The
  other "fuels" are a language rule (§62's 10000 expansions), erased
  termination measures, and a handful of bounds that a measure proof could
  replace. One of those, `merge-opens` (F3 row 6), would accept early if
  its bound were too small; I believe it is not, but did not prove it.
- The prototype (`proto/fuel/`) shows a CEK interpreter and a toy checker
  that suspends into it for compile-time splices. Every function in it is
  checked total. The only unbounded loop is the driver's loop over
  `Program`. It runs under the reference, under `slc --interpret`, and
  compiled by both. With `--eval-fuel 1000`, a 93025-step computation
  finishes when cut into `Program` steps and fails with `out of fuel` when
  run as one call, in both implementations.
- The checker refuses suspension by first-class closures of one
  fixed-level type that has no decreasing argument: such a continuation
  closure cannot call another one at the same level. With an erased
  `subterm` counter in the closure type, a closure at a fixed level can
  call the one before it (F4.1). A function also cannot iterate
  `Program` steps itself. I compiled these claims (F4). I propose
  defunctionalized suspension: explicit data frames, plus one fresh
  `UniqueFn` per driver step that calls down to the stepper.
  Counter-indexed closures may be an alternative, but only a chain of
  closures was compiled, not a CPS `bind`. I did not try level-indexed
  continuations.
- A diagonal argument (F6; its mechanism is compiled in
  `proto/fuel/diagonal.sl`, the rest is my reasoning) says that, if
  Sleight's functions terminate and its checking ends (SOUNDNESS.md's
  (T), (C), and (E), argued there, not proved), no non-erased Sleight function `compile : Src -> Verdict` that
  takes no further evidence can agree with the spec on every source. A source's
  macro can `read-file` its own text, call `compile` on it, and expand to
  a `compile-error` exactly when the answer is "accept". So "every source
  is accepted or rejected" cannot be the type of such a function. It can
  be (i) "H(src) ⇒ the driver reaches `Exit`", a statement about the
  driver, which no compile-time code can run; (ii) a three-outcome
  theorem with `OutOfFuel`; or (iii) a function that also takes erased
  evidence of H(src) for the one source. Read as mathematics, "under H,
  compile is a total function" is untouched by F6. "H(src) ⇒ halts" may
  be provable internally from a spec derivation. My inference is that H
  for all sources, in a form a function can recurse on, is not, if
  Sleight is sound.
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
  loop (my reading). The exception is a macro whose expansion contains
  another macro call, and §62's cap bounds that.
- §27: "A `Program` value (§42) is run: the driver consumes it at `unique`
  and applies each step's continuation once." §32: "The driver consumes a
  program's final `Program` value at unique (§27) and applies each
  continuation once."
- §42: "`(Program L)` is an enum indexed by a level, read by the driver
  (§27)." "The driver flushes after every write. It never recurses, so an
  unbounded interaction is the driver's loop over total functions." Also:
  "the world, the one value of `World`,
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
- §65: `read-file` takes a `MacroWorld`, and "Only the expander supplies a
  `MacroWorld`, to a macro's function", so it runs only inside a macro
  expansion. "`here` must name one of these", a source file or a
  `--comptime-unconfine` name, and `path` "must land, through any
  symlinks, inside that directory or below it". So a source file may
  read itself. §72: `native-compute`
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
| 1 | interpreter `eval`/`apply`, `self/elab-main.sl:159-190, 405-430`. Default `1000000000` in `self/core.sl:3614` (`MkMacros ... 1000000000`), `--eval-fuel` in `self/main.sl:121-132` | Depth of application nesting. Two units per interpreted call, and tail calls spend too. Fresh per run-position form (`elab-main.sl:450-462, 550, 744`), per macro run (`:525`), and per interpreted `Program` step (`interp.sl:109,143`) | `BError "out of fuel"`. The form is refused like any runtime error (MANUAL.md:163-165) | Only by restructuring (options below). This is the fuel that matters. |
| 2 | Expansion budget: `expansion-limit` 10000 (`self/elab.sl:26`), checked globally at `elab-main.sl:559-560`. Also threaded as the structural `fuel` parameter of the elaborator block, reset to 10000 per top-level item (`elab-main.sl:3379, 3387, 3391`), and as `run-toplevel`'s own `fuel` (`elab-main.sl:3362`), 10000 per file (`self/main.sl:29`), spent at `elab-main.sl:3375` and `3382` | §62's language rule. The per-item parameter is also the block's first termination measure | Error "more than 10000 macro expansions" | The global count is the spec and stays. The two parameters look like measures the global count always hits first. I have not verified that. |
| 3 | Termination measures: `xf`, `callbacks`, `hop-k` (`elab-main.sl:147-159`; erased in `eval`, though `expand` takes `xf` at `many`, `elab-main.sl:555`), `Steps` (`elab.sl:1241-1244`, whose `SS` field is `many`), and the sugar budget | Termination evidence. I did not check that every zero case is refuted. The sugar budget's zero case is an internal error (README "Choices") | Refuted or internal error | Already not fuel in the sense of an extra outcome. |
| 4 | Generated printer `show-fuel` 100000 (`self/emit.sl:4, 1379-1438`) | Recursion through types when emitting printers | Falls back to `"show_any"` or empty arms (`emit.sl:1380, 1417, 1438`). This changes emitted code, not a verdict | Possibly, by a measure on the memo. Unverified. |
| 5 | Store walks: `list-refs` and `rope-walk` with fuel = heap size or twice it (`self/eval.sl:171-180, 455-473`), and `heap-strs`/`heap-pairs`/`heap-jobs` with 1000000 (`eval.sl:1018-1055`) | Walking lists in the mutable store | `None` or `Fail`, then an error block | Needs either an acyclicity measure (addresses pointing below) or a visited set. I could not determine whether `hwrite` can make cycles. |
| 6 | Length-bounded loops: `str-split-fuel` (`self/base.sl:100-109`, fuel = string length), `parse-pieces` (`emit.sl:138-153`), `frame-chain` (`elab.sl:816-828`, fuel = the frame id itself), and `merge-opens` (`elab.sl:1987-2004`, fuel = count of opened objects + 1) | Loops whose real measure is a length or an id | Silent truncation or an early `UOk` | Yes: with a decrease proof, as `reader.sl` already does for `str-split` with an `Add` invariant (README "reader.sl"). |
| 7 | Reference: `lib/eval.ml:4, 70-79`, `fuel : int option ref = ref None` | No bound unless `--eval-fuel` is given | `Runtime "out of fuel"` | The reference diverges on a diverging compile-time run. |

Note: self/README.md says the interpreter's fuel is "1000000". The code
(`core.sl:3614`) and MANUAL.md:162 say 1000000000. The README looks stale.

### F4. Compiled checks of the suspension patterns (rule 2)

Files are in `proto/fuel/fr/`: `fr/a.sl`,
`fr/b.sl`, and `fr/d.sl` for 1, and `fr/c.sl` for 2. A reviewer re-ran
`fr/a.sl`, `fr/b.sl`, and `fr/c.sl` under the reference and got the
errors quoted below; `fr/d.sl` was added in a later review (note 14).
The file behind 3 was not saved. Reproduce each from the text here.

1. **A CPS bind over closures is refused.** Take `Res = RDone n | RAsk q (k
   : Fn L (Nat) -> (Res))`. A `bind` at level L that calls `g` gives
   `error: same-level call to g decreases no subterm argument`. A `bind` at
   a higher level B, building `k2` at L that calls `k`, gives the same
   error at `(k a)`. In that version `k2` at L also calls `bind` at B,
   which §17 forbids anyway ("A function may call a function of a
   strictly lower level"). So a resume closure whose type fixes its
   level L and has no decreasing argument cannot call another resume
   closure of that type. A decreasing argument changes this.
   `fr/d.sl` gives the closure type `(Fn L (subterm erased (Nat) j)
   (erased (Eq (Nat) j n) e) (many (Nat) a) -> (many (Nat) r))`. A
   function `extend` defines a `many` closure `k2` at L for `(Succ n)`.
   `k2` takes `e` apart against `Refl` and calls the old closure at L on
   `n`, a strict subterm of `j`. Three `extend`s over a base closure,
   applied to 10, print `13`. The reference, `--no-extern`, and `slc
   --interpret` all agree. This is the shape of 06's
   `proto/stepper/ho_counter.sl`, with runtime closures in place of
   erased ones. So a continuation can be extended one frame at a time as
   a closure of one fixed-level type. Untested: a CPS `bind` whose
   continuations call back into `bind`. My reading is that it would need
   one measure covering `bind` and the continuations together. I also
   did not test a level-indexed `Res` whose continuations sit at
   existentially bound lower levels and carry `Predates` proofs. 06 F4.2
   found that a closure whose level is packed with it in the state can be
   applied and extended at that packed level when two `Predates` proofs
   and a counter are packed with it too
   (`proto/review4/06_packed_counter.sl`). A closure extended at a newly
   minted level is accepted, but on 06's reading of §18 the stepper
   cannot then apply it, and a packed `Predates` cannot reach the new
   level.
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
   `P` was minted"). So `P` must be minted after the level of every
   function a step calls.

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
| `slc --interpret` (93025 steps) | ≈ 1 µs | ≈ 1 µs |
| reference `--build` (31M steps) | ≈ 11 ns | ≈ 10 ns |
| `slc --build` (31M steps) | ≈ 15 ns | ≈ 9 ns |

A reviewer's rerun of the reference rows, subtracting a 0.46 s run with
n = 0, gave ≈ 6.6 µs per batched step and ≈ 4.6 µs extra per `Continue`.
A later rerun (three runs each, on a shared machine) gave 12 to 17 ns
per batched step and 6 to 12 ns extra per `Continue` for both compiled
rows, and, subtracting a 0.3 s run with n = 0, ≈ 1.4 µs and ≈ 1.4 µs for
`slc --interpret`. That is the same order throughout; the difference
between the two compiled rows is within the noise.

With bursts of 1000 steps per `Continue` the overhead is negligible. The
only friction was the level order (F4.3) and a type and a constructor
sharing the name `Fin`.

### F6. The diagonal argument

The mechanism is compiled; the rest is my reasoning and is not checked.

**The mechanism (compiled).** `proto/fuel/diagonal.sl` defines a macro
that reads its own file with `read-file`, at the position of its own call,
runs a stand-in `toy-compile` on the text ("accept iff the length is
even"), and expands to `compile-error` exactly when `toy-compile`
accepts. Run from its directory, as `main.exe ../../../../std/macro.sl
diagonal.sl`, the file is 969 bytes and is accepted. With one byte
added it is rejected. The reference and `slc --interpret` agree on both.
Whatever `toy-compile` computes, its answer on this file is wrong.

The branch must be in what the macro returns, or in a `comptime-match`.
§4 says `compile-error` "fires wherever it is elaborated, erased code
included". A run-position `match` with a `compile-error` in its untaken
branch is rejected (compiled).

**The argument.** Assume `compile : Src -> Verdict` is a non-erased Sleight
function, with no further evidence among its parameters, that agrees
with the spec on every source. Its termination is then the checker's
(§17). Then a unit Q holds `compile`'s code and the macro above with
`compile` in place of `toy-compile`. Q needs no quotation of itself,
since `read-file` supplies the text. `Src` must carry every file the
unit reads (§65) and the flags; Q fixes the flags it assumes, and the
argument concerns Q run with them. Q can read each file of its unit, since
each is a source file. Q's spec run consists of one macro run of a total
function plus ordinary elaboration, so it ends, by SOUNDNESS.md's (T)
for the macro run and (C) for the rest; since §27 strips erased
positions before a run, the run's termination also uses (E). (The
detour below needs (T) and (E) only for an accepted program, and (C)
not at all.)
SOUNDNESS.md states these "about any program the checker accepts", and
Q may be rejected. Read literally, that scope does not cover Q, and it
makes (C) vacuous, since an accepted program's elaboration has ended. A
detour through an accepted program covers Q if the call to `compile` is
placed where acceptance does not depend on it. Let P be Q's text before
the macro call, followed by a function of no arguments that applies
`compile` to Q's files written as literals, as P's final value. A
`def-fns` "involves no evaluation" (§29), and the driver applies a final
`(Fn L -> (many T y))` only after elaboration (§27), so P is accepted
if Q's text before the macro call is. `proto/review5/03_detour.sl` is
that P for `toy-compile`: `--extract` accepts it, and run, it prints
`(BFalse)`. (T) and (E) for P then say that this call of `compile`
returns, reading part 5 as counting the driver's call as one of the
activations it covers. Q's text before the macro call elaborates as in
P, and the macro's call of `compile` is the same call on the same
text, so it returns too, if its result is determined by its code and
argument (below). The macro's other code can be treated the same way,
apart from `read-file`, which is host I/O. The rest of Q is the
elaboration of the macro's output, one `compile-error` or nothing, so
Q's spec run ends without (C) being applied to Q (my reasoning). With
the call in run position instead, the detour would be circular: that
program is accepted only if the call ends.

Q's spec verdict is the opposite of the answer the spec's
own run of `compile` on Q gives, which contradicts the assumption. This
takes that answer to be determined by Q. If
`compile` calls `slot-eq`, whose answer may differ between runs (§67),
the argument applies instead to its copy with every `slot-eq` answered
`ENone`, which §67 allows an implementation to do always, so that copy
must be faithful too, if "faithful" means that every run §67 permits
agrees with the spec (my reasoning).

So, if Sleight's functions do terminate, no such function is a faithful
compiler for all sources. It is the halting-problem form of
diagonalization. The self-reference comes from `read-file`, not from
Kleene's recursion theorem. I make no claim about Gödel's theorems here.
Whether their hypotheses hold for Sleight's logic (§10: `Type : Type`
with no positivity) is not settled in this file.

The same argument applies to a total evaluator that takes source text,
or any encoding Q can build of itself. I believe it does not carry over
to every typed representation of programs: Brown and Palsberg (POPL
2016) report a self-interpreter for System Fω. I have not checked how
that applies here.

**What it does not refute.**
- Owner item 4(ii), read as mathematics. Under H the spec relation is
  total, and with determinism it is a function. F6 says only that the
  language's own termination checker cannot witness this for a
  hypothesis-free Sleight `compile`.
- A Sleight function `compile : (many Src s) (erased (H s) h) -> Verdict`.
  Q would have to produce erased evidence of H(Q) inside Q. Rerunning
  the argument with that evidence shows that, if Sleight is sound, no Q
  can, though code outside Q may prove H(Q) (my reasoning). Such a function can recurse on an erased halting
  derivation: `tests/erased_subterm.sl` recurses on an erased `subterm`
  argument, and 05's `proto/theorems/bove.sl` does so on an erased
  `Halts` derivation, with each step returning an erased relation
  between its input and its output, since a type holds no call (§9).
  Both are accepted. That this scales to a compiler is untested. (slc's
  `eval` is not an instance: its `xf` stays fixed within an evaluation,
  whose recursion is bounded by the `many` fuel of F3 row 1.)

**H for all sources (inference, untested).** Suppose a Sleight
function returned, for every source, erased evidence that the stepper
halts within an erased n. Recursing on that n would then give a
hypothesis-free non-erased `compile`, which F6 forbids. So if Sleight is
sound and the stepper is faithful, Sleight cannot prove H for all
sources in this form.

**The escapes.**
- `compile_n` with fuel. Q's call to `compile_n(Q)` must answer
  `OutOfFuel`, or the contradiction returns.
- The `Program` driver. A `Program`'s continuation needs a `unique` world
  (§42), "which only the driver supplies". `World` is opaque, with no
  `Matchable` (§8). The driver runs only a file's final value, after
  elaboration (§27). So no compile-time code can step a `Program`: not a
  run-position form, not a macro (it holds a `MacroWorld`, not a
  `World`), and not a `native-compute` argument, which is a `(Fn L ->
  (many T r))` (§72). Q can still call a total stepper for as many steps
  as it fixes. A faithful stepper then cannot finish on Q within that
  bound, which does not contradict anything (my reading). Within §62's
  cap, the expander gives user code only bounded iteration.
- slc does not take this escape: its whole compile runs inside one
  `Program` step (F2), and it is total because of its fuel (F3 row 1),
  which already makes it unfaithful on sources whose compile-time runs
  nest deeper than the bound. Its elaborator does thread `ElabWorld`, a
  newtype over a placed `World` (`self/eval.sl:1492-1494`, built in
  `self/main.sl:133`), so a source cannot call slc's elaborator at
  compile time. That alone is no escape, in my reading: a `compile` that
  uses its `World` only to read files could take their contents from
  `Src` instead and need no `World`, and F6 applies to that version.

README.md's strength remark ("about IΣ₂ ... ordinal ω^ω^ω") is attributed
there to "the author". I make no claim about it, and the argument above
does not depend on it.

### F7. What the hypothesis H amounts to

My reading: H is "every compile-time evaluation the spec performs while
deciding src halts". Going through DESIGN.md, compile-time computation
happens at these places:
- run-position forms and everything they call (§27, §29);
- macro functions (§62), at most 10000 of them per run;
- macro primitives, which check and canonicalize but do not evaluate
  (§65, §29 "The checker never evaluates");
- `unary`, at most 1024 successors, checked "with `nat-cmp`" (§49), and
  `prove-literal-lt`, which decides with `lt-dec` and "relies on the
  evaluator (§29)" (§45);
- `native-compute`, which runs compiled code (§72), through an external
  compile in both implementations (MANUAL.md:195);
- `read-file`, which is host I/O (§65);
- possibly literals: §45 defines a numeral's value as what
  `(bin-to-nat b)` returns, and its entries are "as if minted by
  run-position forms", but leaves to the implementation "whether a
  literal's entries are produced by elaborating statements or created
  directly to the same effect".

The top level cannot loop (§3, §20), apart from macro re-expansion,
which §62 caps. So H would follow from two things:
- SOUNDNESS.md's claims (T), totality, and (C), checking terminates,
  applied to the code that is run, and (E) as well, since §27 runs a
  form with "its erased positions are stripped" (unless a formal spec
  runs unstripped code). SOUNDNESS.md part 1 makes these claims
  relative to the shipped prelude and says they "do not cover" a
  `--no-prelude` program with its own extern models or `def-prim`
  signatures, so H does not follow from them for such a program;
- host assumptions. `read-file` must not block, for instance on a FIFO.
  DESIGN.md does not say whether that can happen. The external compile
  and run under `native-compute` must also halt.

In that reading, H is an instance of the language's own termination
claim plus I/O. By F6's inference (untested, and assuming Sleight is
sound), it is not provable in Sleight for all sources in a form a
function can recurse on, such as erased step counts.
For one given source it is a statement about that source, so it may be
provable case by case.

A divergence source that I believe is *not* there: macro → elaboration →
macro recursion is bounded by §62's global count, and slc enforces that
count at `elab-main.sl:559-560`.

## 3. Options

### Q1. How to take fuel out of the verdict

**(a) The whole compiler as a state machine stepped by `Program`.**
- Design: defunctionalize the elaborator's 95-function main block
  (`elab-main.sl:158-3234`, about 3080 lines) and the interpreter into
  one `MState` with explicit frames, as `machine.sl` does at toy scale.
  slc's `start` becomes `drive init`.
- Pros:
  - There is no fuel anywhere.
  - Every step is total by checking.
  - The theorem shape is the cleanest (Q2).
  - The `xf`/`callbacks`/`hop-k` measures disappear.
- Cons: a rewrite of the largest and most intricate part of slc. The
  code becomes frame-oriented and less readable. As proposed, every
  non-tail call site becomes a frame constructor. Closures without a
  decreasing argument cannot do the composition (F4.1). Closures with an
  erased counter might, but that is untested beyond a chain of closures.
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
- Pros: small change. Fuel never shows in a result. The fuel bounds
  depth, not work (MANUAL.md:154-157), so a failed attempt is a prefix of
  the successful run, but it is not half as long. Doubling from n₀ to n
  costs at most about log₂(n/n₀) + 1 times the successful run, not twice
  (my reasoning).
- Cons:
  - Needs a monotonicity lemma: success at n gives the same result at
    every m ≥ n.
  - Effects are re-performed on restart (`native-compute` runs, file
    reads). They are probably idempotent but not formally so.
  - State the spec observes must be rolled back with the checkpoint: §62's
    expansion count ("At most 10000 expansions run in one run") and §65's
    gensym counter. Otherwise a restart can change a verdict near the
    cap. I have not checked that slc's checkpoint covers them.
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
- Cons: F6 rules it out for all sources, if it is a non-erased
  function on source text with no further evidence. At best it works for a fragment
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
  - Effects are re-performed on replay, and the expansion and gensym
    counters must be rolled back, as in (b).
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
- (P2) Each step is total. This follows from the step being accepted,
  given SOUNDNESS.md's (T) and (E). Under (b) and (c), `compile_n` is
  total in the same sense.
- (P3) Completeness. From an erased `(Verdict src v)` derivation, the
  procedure produces v: under (a) and (e) as a step count n with a proof
  that iterating `step` n times reaches v, and under (b) as an n with
  `compile_n src = v`. A type holds no call (§9), so "iterating `step`"
  and "`compile_n src = v`" cannot be written as types directly. They
  need a step relation, and `step` must return erased evidence that
  relates its input to its output. This is structural recursion on the
  derivation, so it may be an erased Sleight function. F6 does not
  forbid it: F6's inference concerns H for all sources, not H(src) ⇒
  halts.
  Unverified.
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
   F6 suggests that no hypothesis-free, non-erased Sleight function can
   do better, and the prototype shows the `Program` loop can carry it.
   (i) can be paired with (iii) of the summary, a Sleight function that
   takes erased H(src) evidence, as an internal form of the same theorem.
   (a), (b), and (e) can give (i), since each leaves any unbounded
   iteration to the driver; (c) gives (ii).
3. **Which route: (a), (b), (c), or (e)?** Recommended: (e) for slc, and
   (a) only for a new small kernel built that way from the start. (b) is
   the cheap stopgap. Converting the interpreter to a stepped machine is
   needed by (a) and (e).
4. **Is H stated over the spec run including host I/O (`read-file`,
   `native-compute`), or are those axiomatized as terminating?**
   Recommended: axiomatize them, and state H for evaluation only.
5. **What does the 10001st expansion do?** §62 states the cap ("At most
   10000 expansions run in one run") and §49 states "at most 1024", so
   both are language rules a formal spec must model. They are not fuel,
   and that part is not a question. Open: §62 does not say whether
   reaching the cap is an error. Both implementations make it one (§5
   below).

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

- F6 beyond its mechanism. `diagonal.sl` checks the mechanism with a toy
  `compile`, but no Q holds a faithful compiler. slc as it stands cannot
  play that part, since it is not faithful (its fuel can reject) and its
  elaborator carries a `World`, though, as F6 says, a version taking
  the files from `Src` would need none. The steps marked as inference in
  F6 (that recursion on an erased halting derivation scales from 05's toy
  to a compiler, and H not provable) are untested.
- That the detour through the accepted program P carries (T) and (E)
  over to the run of the possibly rejected Q (F6). It assumes that the
  spec accepts P as the checker does and that part 5 covers the
  driver's call. Only P's shape is compiled, with `toy-compile`.
- That the per-item and per-file expansion parameters (F3 row 2) never
  bind before the global count.
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
- That counter-indexed closures can express a CPS `bind`, or replace
  frames in option (a) (F4.1).

## Review notes

An adversarial reviewer checked this file against DESIGN.md (read in
full), the cited code, and reruns of the prototypes, and then made these
changes.

1. F6, the run-position branch. The original had Q do "in run position
   ... `compile-error` if the answer is accept". §4 makes `compile-error`
   fire "wherever it is elaborated", and a run-position `match` with
   `compile-error` in its untaken branch is rejected (compiled). F6 now
   branches in a macro's output, and `proto/fuel/diagonal.sl` (new)
   compiles that mechanism under the reference and `slc --interpret`.
2. F6, the hedge "slc's code can be run at compile time by a source,
   which I believe holds". It does not hold for slc as written: the
   elaborator threads `ElabWorld`, a newtype over a placed `World`
   (`self/eval.sl:1492-1494`, `self/main.sl:133`), and no compile-time
   code holds a `World` (§42). The `ocamlfind` remark was beside the
   point. F6 now says that slc already takes the `Program` escape, and
   that the argument concerns a World-free `compile`.
3. F6 and the summary, the scope of the conclusion. "Cannot be a Sleight
   function type" was too broad. The argument refutes only a non-erased
   `compile` with no further evidence. It does not refute one that takes
   erased H(src) evidence, nor item 4(ii) read as mathematics. Option
   (iii) was added to the summary and to Decision 2.
4. F6, "This is Kleene's diagonalization" and "Gödel II is the logical
   shadow of it". These are now the halting-problem diagonal, with the
   self-reference supplied by `read-file`. The Gödel claim was dropped,
   since §10 (`Type : Type`, no positivity) leaves the hypotheses
   unsettled. A hedge was added that the claim about evaluators depends
   on the representation (Brown and Palsberg, POPL 2016, from memory and
   not checked).
5. F6/F7, "H itself cannot [be proved]". The original rested on F6
   alone, but F6 forbids only a runnable function. Added the missing step
   as an untested inference: H for all sources, given as erased step
   counts, would yield a runnable `compile` by recursion on an erased
   measure, as slc's `eval` does with `xf`. Also added that this assumes
   Sleight is sound.
6. F7 left out compile-time evaluation sites: `prove-literal-lt` ("relies
   on the evaluator", §45), and `unary`'s `nat-cmp` check (§49). Both are
   now listed. Added the macro re-expansion caveat to "the top level
   cannot loop" (F1 and F7).
7. Q1(b), "at most about twice". The fuel bounds depth, not steps
   (MANUAL.md:154-157), so the bound is about log₂(n/n₀) + 1 runs.
   Corrected.
8. Q1(b)/(e). Added that §62's expansion count and §65's gensym counter
   must be rolled back on restart or replay, or a verdict near the cap
   can change. Unchecked against slc's checkpoint.
9. Q2 P3. A type holds no call (§9), so "iterating `step` n times
   reaches v" needs a step relation and evidence returned by `step`.
   Added.
10. F3 row 3. `Steps`'s `SS` field is `many` (`elab.sl:1245`), and
    `expand` takes `xf` at `many` (`elab-main.sl:555`). So "erased
    measures" was inexact. "Zero cases are refuted" was not checked and
    is now marked so.
11. F4. The files for checks 1 and 2 are in `proto/fuel/fr/`
    (`fr/a.sl`, `fr/b.sl`, `fr/c.sl`), and their reruns reproduce the
    quoted errors. The file for check 3 was not saved. F4.1's conclusion
    is narrowed to fixed-level continuation types. A level-indexed
    alternative is untested.
12. Decision 5 was not a real question. §62 and §49 already state those
    rules. It now asks the remaining open point, what reaching the
    expansion cap does.
13. F1's §65 summary now quotes what `read-file` may read.
14. F4.1, the summary, Q1(a), and section 6, after 06's review found
    `proto/stepper/ho_counter.sl`. "A continuation closure at a fixed
    level cannot call another one" was too broad. The checks in
    `fr/a.sl` and `fr/b.sl` still give the quoted errors, but their
    closure types have no decreasing argument. `fr/a.sl` also calls
    `bind` upward from L, which §17 forbids. `ho_counter.sl` (erased
    closures) and a new `fr/d.sl` (runtime `many` closures) have an
    erased `subterm` counter, and both are accepted and run under the
    reference, `--no-extern`, and `slc --interpret`. F4.1 now limits
    the refusal to closure types without a decreasing argument and
    reports `fr/d.sl`. The proposal for defunctionalized frames stands,
    but F4.1 no longer forces it. A CPS `bind` with counters remains
    untested.

Confirmed as written:
- The DESIGN.md quotes in F1. "DESIGN.md does not mention fuel" holds:
  grep finds no "fuel".
- `core.sl:3614` (1000000000), `prelude.sl:1337-1342`, `main.sl:121-132`
  and `186-191`, `interp.sl:61-67`, `98-114` and `143`, the
  `elab-main.sl` fuel sites (450, 455, 462, 525, 550, 559-560, 744, 3379,
  3387, 3391), `elab.sl:26`, `eval.ml:4, 70-79`, the README/MANUAL
  mismatch, and the F3 rows 4-6 locations.
- The F5 runs (0/1/2/3 under the reference, and 2 under `slc
  --interpret`). The `--eval-fuel 1000` pair under both. The timings
  were the same order.

Uncertain points:
- Whether a Sleight function taking erased H(src) evidence can actually
  be written (P3, F6 "what it does not refute").
- Whether Sleight's logic is sound enough for the "H not provable"
  inference. That rests on SOUNDNESS.md's (T), which is the sessions'
  argument, not an owner decision.
- The compiled timing rows and the 22 MB figure were not re-run.

## Second review notes

A second adversarial reviewer read DESIGN.md in full, SOUNDNESS.md parts
1, 3, 5, 6, 7, and 9 to 11, the cited code, and re-ran `diagonal.sl`
(and a one-byte-longer copy) under the reference and `slc --interpret`,
`fr/a.sl` to `fr/d.sl` (reference, `--no-extern`, `slc --interpret`),
`suspend.sl` 0/1/2 under both and 0/2 built by both, 3 under a timeout,
and the `--eval-fuel 1000` pair under both. All behave as the body says.

Errors found and changed:

1. F6, "slc already takes this escape" (introduced by review note 2).
   slc's whole compile runs in one `Program` step (F2), and it is total
   through its fuel (F3 row 1), not through the driver. Holding a
   `World` does stop a source from calling it at compile time, but a
   `compile` that uses its `World` only for file reads has a World-free
   version taking the files from `Src`, to which F6 applies (my
   reasoning). Rewritten; review note 2's conclusion no longer stands.
2. F6, "as slc's `eval` recurses on `(subterm erased (Nat) xf)`" (also
   review note 5). In `elab-main.sl:159-190` `eval` passes `xf`
   unchanged; it drops only at macro expansion (`elab-main.sl:509-511`,
   where it is `many`), and evaluation recursion is bounded by the
   `many` `fuel`. Replaced the precedent with `tests/erased_subterm.sl`
   and 05's `proto/theorems/bove.sl`, both accepted, which also test the
   "erased relation returned with each step" point in toy form. Section 6
   updated.
3. F6, the argument assumed `compile` answers the same on Q inside and
   outside Q's run. A `compile` that calls `slot-eq` need not (§67).
   Added that the argument then applies to its copy with every
   `slot-eq` answered `ENone`, which §67 permits.
4. Summary, the diagonal bullet stated the conclusion without the body's
   condition that Sleight's functions terminate. Added it, attributed to
   SOUNDNESS.md's (T), which that note argues but does not prove.
5. Summary, "one fuel that can change a verdict". F3 row 6's
   `merge-opens` returns an early `UOk` on exhaustion (`elab.sl:1988`),
   which would accept if its bound (opens + 1, `elab.sl:2004`) were
   short. Now "known to", with that caveat.
6. F7, H from SOUNDNESS.md. Added (E) for a stripped spec run, and that
   part 1 excludes `--no-prelude` programs with their own models or
   `def-prim`s ("the claims do not cover such a program").
7. F7, "an external toolchain" was attributed to §72, which does not say
   it. Now cited to MANUAL.md:195.
8. F3 citations: MANUAL.md:158-162 → 163-165 (the refusal text) and
   MANUAL.md:163 → 162 (the default); `elab.sl:1242` → 1241-1244 (`Steps`;
   review note 10's 1245 is also off: `SS` is line 1244); and
   `elab-main.sl:143-159` → 147-159 (143-146 are `native-cids`).
9. Q1(a), "about 3240 lines" counted to the end of the file. The block
   is `elab-main.sl:158-3234`, about 3080 lines; 95 functions confirmed.
10. F4.3, "the driver's level must come last in the file order"
    overstated the constraint. Now: `P` after the level of every
    function a step calls.
11. Header: the owner items cited as "owner item" and "decision 3" are
    the brief's paraphrases. Said so.

Confirmed: §4's "fires wherever it is elaborated" with a compiled check
(`proto/review2/03_untaken_ce.sl`: a run-position `match` whose untaken
branch holds `compile-error` is refused); `diagonal.sl` is 969 bytes and
`macro-fail` expands to a `compile-error` form (`std/macro.sl:28-36`);
the `fr/` errors as quoted; `interp.sl:109` passes the same `fuel` to
each step; Brown and Palsberg, POPL 2016, F_ω (from memory). Rough
re-timing: about 7 µs per batched reference step and 2 µs extra per
`Continue`, the same order as F5.

Unsure:
- Whether Q1(b)'s claim that a failed depth-fuel attempt is a prefix of
  the successful run survives effects and counters; (b) already lists
  them as needing rollback.
- Whether F3 row 2's per-item parameter can bind first; each `xf`
  decrement seems to accompany a global-count increment, but I did not
  check every path.
- F6 and F7 still rest on SOUNDNESS.md's (T) and on the logic's
  soundness, neither proved.

## Coordinator notes

1. §6's first item still gave "it needs a `World`" as the reason slc
   cannot stand in for the faithful `compile`, which the second review's
   correction of F6 had superseded. Reworded to match F6; flagged by the
   third review of 00-summary.
2. F4.1's last sentence still gave 06's superseded "built but not
   applied" finding; restated to match 06 F4.2 after its fourth review.
   Flagged by the fourth-round propagation check of 00-summary.

## Third review notes

A third adversarial reviewer read DESIGN.md in full, SOUNDNESS.md parts
0 to 7, the brief, and the cited code, and re-ran `diagonal.sl` (969
bytes, accepted under the reference and `slc --interpret`), `fr/a.sl` to
`fr/d.sl` under both, `suspend.sl` 0/1/2, and the `--eval-fuel 1000` pair
under both. All behave as the body says.

Errors found and changed:

1. Summary and F6, the premise. Q's spec run ending needs checking to
   end as well as functions to terminate, and §27 strips erased
   positions before a run, so the stripped run's termination needs
   SOUNDNESS.md's (E) too. The premise is now (T), (C), and (E).
2. F6, Q may be rejected. SOUNDNESS.md part 1 states its claims "about
   any program the checker accepts", and Q is rejected whenever
   `compile` accepts it. Added the step that carries the claims over:
   the same call of `compile` on Q's text runs in an accepted program
   (Q's text before the macro call, then that call in run position).
   Listed in section 6 as unverified.
3. F6, the flags. `Src` carries the flags, but Q cannot read them; Q
   fixes the flags it assumes, and the argument concerns Q run with
   them. Added.
4. F6, the `slot-eq` copy. That the `ENone` copy is faithful follows
   only if faithfulness means every run §67 permits agrees with the
   spec. Said so.
5. F6, "What it does not refute": "Q would have to produce erased
   evidence of H(Q) inside Q, and nothing above says it can" was an
   underclaim. Rerunning the diagonal with that evidence passed to
   `compile` gives the same contradiction, so, if Sleight is sound, no
   Q can; code outside Q may still prove H(Q).
6. F7, "(E) as well if the spec's run strips erased positions". §27
   says a run-position form is run with "its erased positions are
   stripped". The condition now cites §27, keeping the caveat for a
   formal spec that runs unstripped code.
7. Q2 P2, "free from checking". Totality of an accepted step is
   SOUNDNESS.md's (T) and (E), argued, not proved. Hedged.

Confirmed: the F1 quotes (§3, §17, §20, §27, §29, §31, §32, §42, §49,
§62, §65, §72); `merge-opens` (`elab.sl:1987-2004`, two `UOk` exits on
exhaustion), `Steps` (`elab.sl:1241-1244`), `ElabWorld`
(`eval.sl:1492-1494`), `core.sl:3614`, `elab.sl:26`, `elab-main.sl:555`,
`559-560`, and `158-3234` (the file has 3398 lines); MANUAL.md:154-166 and
195; the reference's expansion cap (`lib/elab.ml:684`); DESIGN.md has no
"fuel". Under `slc --interpret`, `fr/a.sl` reports, besides the quoted
error, "`B` was not in scope when level `L` was minted" at the upward
call to `bind`, which agrees with F4.1's remark that §17 forbids that
call; the reference stops at the first error. The F6 reasoning,
checked step by step, holds under the premises now stated.

Unsure:
- Whether "faithful" for a nondeterministic spec is best read as "every
  permitted run agrees" (item 4); a weaker reading would need another
  route for a `compile` that calls `slot-eq`.
- The compiled timing rows and the 22 MB figure were not re-run by any
  review.

## Fourth review notes

A fourth adversarial reviewer read the brief, CLAUDE.md, DESIGN.md in
full, SOUNDNESS.md parts 0 to 7 and 9, and MANUAL.md:150-166, and
re-ran `diagonal.sl` (969 bytes, accepted) and a copy with one byte
added (`proto/review4/03_diag/diagonal.sl`, 970 bytes, rejected with
"toy-compile accepts this source") under the reference and `slc
--interpret`, `fr/a.sl` to `fr/d.sl`, `suspend.sl` 0/1/2 and 3 under
a timeout, and the `--eval-fuel 1000` pair under both. All behave as
the body says.

Errors found and changed:

1. F6, carrying (T), (C), and (E) over to a rejected Q (added by third
   review note 2). The detour through "an accepted program, Q's text
   before the macro call followed by that call in run position" is
   circular: that program is accepted only if the call ends, which is
   what the step is meant to show. Also, read with part 1's scope
   ("about any program the checker accepts"), (C) is vacuous. F6 now
   rests the step on part 5's per-activation measure over checked
   functions and on part 6's argument for (C), as a reading; section 6
   updated. The sentence after it, "the same inside Q's run as outside
   it", now says what the step needs: that the answer of the spec's run
   of `compile` on Q is determined by Q.
2. Summary and F7, "H for all sources is not [provable]". F6's
   inference covers only H in a form a function can recurse on, such
   as erased step counts ("in this form"); the summary and F7 had
   dropped that qualifier. Restored.
3. Decision 2, "This choice decides between (a)/(e) and (b)/(c)". Q1(b)
   restarts in the driver, and "Fuel never shows in a result", so (b)
   gives form (i), as Q2's P3 already treats it; only (c) gives (ii).
   Fixed.
4. Q2 P3, "F6 concerns H for all sources": F6's main argument concerns
   a hypothesis-free `compile`; its inference is what concerns H.
   Reworded.

Confirmed: the F1 quotes against DESIGN.md (§3, §17, §20, §27, §29,
§31, §32, §42, §49, §62, §65, §72); grep finds no "fuel" in DESIGN.md;
§62 says nothing about what reaching the cap does; MANUAL.md:154-166
(depth, units given back on return, `out of fuel` citing §31);
`interp.sl:105-114, 143`, `main.sl:186-191`, `elab.sl:1987-2004`, and
that `Continue` occurs in `self/` only at `interp.sl:114` and
`main.sl:191`. The F6 diagonal checked step by step: Q's verdict is the
negation of the value the spec's own run of `compile` on Q produces,
so the contradiction needs only that run to end and to be
deterministic, not that `compile` be evaluated "outside" Q. Q's
`read-file` of the other files of its unit (`std/macro.sl` here) needs
a `Pos` naming each, which a macro can build (§65 "`here` must name one
of these, spelled as the command line names it").

Unsure:
- Whether part 5's argument really needs nothing from the acceptance of
  the rest of Q: its invariants (I1) to (I3) are stated for reachable
  states of the full semantics of a program, and Q is not such a
  program when rejected.
- The compiled timing rows and the 22 MB figure, still not re-run.
