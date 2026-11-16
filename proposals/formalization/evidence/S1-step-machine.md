# S1: a fuel-free step machine for mini's `Core`, looped by the `Program` driver

Spike by one Claude session (agent S1). Nothing here is the owner's decision. Every claim carries one tag:
`[QUOTE]`, `[RAN]`, `[READ]`, `[INFERENCE]`, or `[UNKNOWN]`.

All code is in `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S1/`
(called `S1/` below); `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S1/RUN.md`
lists every command. Commands below are run from `S1/` with

```sh
R=/home/user/sleight/_build/default/bin/main.exe     # reference interpreter, built 09:31
S=/home/user/sleight/_build/release/slc              # slc release build, built 09:38
B="base.sl term.sl core.sl eval.sl"                  # unmodified copies of mini/
```

- [RAN] `diff -q mini/$f.sl S1/$f.sl` for `base`, `term`, `core`, and `eval` printed nothing but my "identical" echoes; `git diff --stat 4bb81cc HEAD -- DESIGN.md MANUAL.md mini lib std tests self CLAUDE.md` printed nothing (the repository head moved from `4bb81cc` to `7970e3f` during the session, in other directories).
- [RAN] No file inside `/home/user/sleight` was written by this spike; every write went under the scratchpad.

## 1. Findings that bear on decisions

1. **The proposal works as stated.** [RAN] A machine whose `step` is one total function with no fuel, looped by the `Program` driver, evaluates mini's `Core`; it answers `(MkEvaled _ _ vs p)` with an erased `p : (Eval env0 c0 vs)` or `EvalStuck`; it ran 38,000,028 steps (a recursion 1,000,000 deep) under a 64 KB host stack, where mini's fuelled `eval` overflows the default 8 MB host stack at depth 30,000 (sections 3, 5).
2. **Agreement with the big-step spec in the "machine halts ⇒ spec derives" direction cost no proof.** [RAN] The intrinsically typed stack type-checked on the first run of the checker; the only proof terms are applications of the spec's own constructors (`EvVar`, `EvApp`, and so on), written where a value is returned or a frame is popped (section 4).
3. **The converse direction is proved for every rule, as a relation.** [RAN] `eval-reaches` (78 lines with its lemmas) type-checks: from `(Eval env c vs)`, for every stack `k`, the state "evaluate `c` in `env` with `k`" reaches "return `vs` to `k`" through the step relation `StepTo` (121 lines). Four deliberately wrong variants are refused (section 6).
4. **The converse direction also exists as a running, total, fuel-free function.** [RAN] `run-from-spec : (many (Core) program) (erased (List (Val)) vs) (erased (Eval (ENil) program vs) derivation) -> (many vs is out)` type-checks and runs: it loops the machine by `subterm erased` recursion on the reachability path, needs neither fuel nor the driver, and ran 38,000,028 steps under a 64 KB host stack (section 7).
5. **There is a much smaller fuel-free evaluator when a derivation is at hand.** [RAN] `eval-by`, mini's direct evaluator with `fuel` replaced by `(subterm erased (Eval env c vs) d)`, is 56 lines plus 35 lines of guided lookups (the fuelled one is 74 lines plus 13 of result types), has no stuck case, returns `(many vs is out)`, and its calls on a body, a branch, and a statement's rest are `tail` calls. Its host stack grows with the depth of non-tail nesting (section 7).
6. **A flaw in the proposed design, and a fix at no run-time cost.** [RAN] With the stack exactly as proposed, every rule whose last premise is in tail position (call body, match branch, and rest of a statement) leaves a frame that holds only erased data, so a chain of 10,000 `let`s followed by a 10,000-iteration tail-recursive loop reaches a machine stack of 30,002 frames. Moving those three frames into an erased `Tail` context held by a `newtype` wrapper gives a deepest sampled stack of 3 frames on the same program (section 4.2).
7. **Speed.** [RAN] Compiled (reference extraction and slc alike): about 23 to 25 million steps per second unbatched and 28 to 31 million batched. Reference interpreter: about 165,000 steps per second, batched or not. On an input the fuelled evaluator can run (depth 10,000), the fuelled evaluator, the batched machine, and the unbatched machine take 13.5 ms, 14.2 ms, and 18.0 ms net (section 5).
8. **The pattern carried over to a mutable store.** [RAN] A second, 174-line prototype (`S1/heap/`) has a store-threading spec `(HEval before e v after)`, a machine whose store is a `unique` prelude `Array` updated in place and carried through the driver's `def-unique` continuations, and ran a 10,000,000-iteration object-language loop (150,000,011 steps) at a constant 5.9 MB maximum resident set. It also type-checked on the first run (section 9).
9. **What is not proved.** [INFERENCE] Nothing here shows that the unguided `step` never answers `EvalStuck` when a derivation exists, nor that `StepTo` is deterministic; section 6.4 says what each would take. [INFERENCE] rests on: no such lemma is in `S1/`.
10. **The checker fought very little.** [RAN] Over the whole session it raised six errors (five distinct causes) and four kinds of warning, all listed in section 8; none forced a change to the design.

## 2. The owner's statement this spike tests, and what DESIGN.md says about the driver

- [QUOTE handoff.md:20] "A fuel-free self-interpreter is possible because the top level is not a function; it is the continuation that the driver loops over, the prelude's `Program` with `Continue` and `Exit` (DESIGN.md §27 and §42). Whether that approach makes sense for the interpreter was left to analysis." (The handoff file was written by a previous session; it presents this as the owner's statement.)
- [QUOTE DESIGN.md:1165-1167, §27] "A `Program` value (§42) is run: the driver consumes it at `unique` and applies each step's continuation once."
- [QUOTE DESIGN.md:1993-1994, §42] "The driver flushes after every write. It never recurses, so an unbounded interaction is the driver's loop over total functions."
- [QUOTE mini/README.md:5-7] "beside each relation stands a function that derives it by structural recursion, or answers "stuck" on a shape the rules have no derivation for (evaluation alone still burns fuel)."

## 3. What works

### 3.1 Test (a): the program of tests/mini_eval.sl

- [RAN] `$R $B mini_eval_ref.sl` (mini's fuelled `eval` at fuel 1000) prints
  `(MkEvaled _ _ (Cons _ (VCon 12 $ Cons _ (VCon 11 $ Nil _) $ Nil _) $ Nil _) _)`.
- [RAN] `$R $B machine.sl drive.sl test_a_value.sl` (the same four `let`s, then `step-many` with quantum 1000, printed by the built-in printer) prints
  `(MkPair _ _ (Halted _ _ $ MkEvaled _ _ (Cons _ (VCon 12 $ Cons _ (VCon 11 $ Nil _) $ Nil _) $ Nil _) _) 40)`: the same value, in 40 steps.
- [RAN] `$R $B machine.sl drive.sl test_a_program.sl` (the same program under the `Program` driver, one `step` per driver step) prints `done unary 1 steps 40`.
- [RAN] With `machine_tail.sl` in place of `machine.sl` the two commands print the same value with `36` steps, and `done unary 1 steps 36`.

### 3.2 Test (b): deep and long programs

[READ S1/programs.sl:1-61] `programs.sl` builds, with tail-recursive Sleight helpers, `Core` for: `double` (a function that walks `Succ^n Zero` and returns `Succ^2n Zero`, recursing in non-tail position), `drop` (the same walk with the recursive call in tail position), `pred`, and `chain-drop` (`n` successive `let`s that count up, then `drop`). `main.sl` takes `step|batch|fuel  shape  n  [quantum|fuel]`.

- [RAN] `$R $B machine.sl programs.sl drive.sl main.sl -- fuel double 1000 1000` prints `stuck fuel 1000`; `... -- step double 1000` prints `done unary 2000 steps 38028`; `... -- batch double 1000 100` prints `done unary 2000 steps 38028`.
- [RAN] `... -- step double 10000` prints `done unary 20000 steps 380028`.
- [RAN] `python3 measure.py interp 100000 2 double 10,1000` includes `interp v1 step double 100000  wall 23.424s ... done unary 200000 steps 3800028`.
- [RAN] `./bin/slc_v1 step double 1000000` prints `done unary 2000000 steps 38000028`.
- [RAN] Mini's fuelled `eval` on the same inputs with ample fuel: `./bin/slc_v1 fuel double 10000 100100` prints `done unary 20000 fuel 100100`; `./bin/slc_v1 fuel double 30000 300100` prints `Fatal error: exception Stack overflow`; under the interpreter, `$R $B machine.sl programs.sl drive.sl main.sl -- fuel double 30000 300100` prints `Fatal error: exception Stack overflow` after 7.3 s (`ulimit -s` is 8192 KB).

### 3.3 Stuck is a final result, not fuel exhaustion

- [RAN] `$R $B machine.sl programs.sl drive.sl test_stuck.sl` prints
  `"stuck steps 1\nstuck steps 5\nstuck steps 18\nstuck steps 7\nstuck steps 26\ndone unary 0 steps 28\n"`
  for, in order: an unbound variable, an atom called as a function, a match with no branch for the scrutinee's constructor, a call with too few arguments, two values passed as one argument, and a program that is not stuck.
- [READ S1/machine.sl:68-137] `step` has no fuel parameter, and answers `(Halted _ _ $ EvalStuck _ _)` in exactly these places: `env-dec` misses, a returned value list is not a singleton where one value is needed, a head is not a `VAtom`, a callee is not a `VClo`, a scrutinee is not a `VCon`, `branch-dec` misses, and `bind-all` fails (three sites). I read the whole function.
- [INFERENCE] `EvalStuck` carries no evidence (it is mini's constructor, [READ S1/eval.sl:42]), so "the machine answers stuck only when no derivation exists" is not established by types; see section 6.4.

### 3.4 Host stack use

- [RAN] `( ulimit -s 64; ./bin/slc_v1 step double 1000000; ./bin/slc_v1 fuel double 300 3100 )` prints `done unary 2000000 steps 38000028` then `Fatal error: exception Stack overflow`. The same limit with `./bin/slc_v1 batch double 1000000 100000`, and with `./bin/ref_v2 step double 1000000`, prints the `done` line.
- [RAN] Under the interpreter: `( ulimit -s 256; $R $B machine.sl programs.sl drive.sl main.sl -- step double 20000 )` prints `done unary 40000 steps 760028`, and so does `-- batch double 20000 10000000` (one driver step, 760,028 `tail` calls).
- [RAN] A caveat: `( ulimit -s 64; ./bin/slc_v1 step chain-drop 10000 )` prints `Fatal error: exception Stack overflow`, while `chain-drop 300` and `step drop 1000000` complete. [READ S1/core.sl:56-61,79,127] mini's `env-dec` recurses with `notail` on the environment (as `bind-all` and `branch-dec` do on their lists), and `chain-drop 10000` builds an environment 10,000 entries deep. [INFERENCE] So one `step` uses host stack in proportion to the environment (and, through `bind-all` and `branch-dec`, to a parameter list or a branch list), never to the depth of the evaluation; a tail-recursive lookup would remove that. Rests on the three runs above and on reading `env-dec`.
- [RAN] An interaction with the interpreter's own bound: `$R --eval-fuel 100000 $B machine.sl programs.sl drive.sl main.sl -- step double 10000` and `-- batch double 10000 1000` print `done unary 20000 steps 380028`; `-- batch double 10000 10000000` prints `main.sl: runtime error: out of fuel`. [QUOTE MANUAL.md:156-157] "so `n` bounds how deeply applications nest, a tail call nesting inside the call it replaces." [QUOTE MANUAL.md:161-162] "Without the flag the reference has none and slc's is 1000000000." [INFERENCE] So under an evaluator that counts tail calls as nesting, it is the driver's loop, not a `tail`-recursive quantum, that keeps a long run inside the bound.

## 4. The types

### 4.1 v1: the design as proposed (`machine.sl`, 136 lines)

[INFERENCE] The CPS-and-defunctionalize transform of `eval`, `eval-list`, and `eval-stmt` gives two mutually recursive stack types, because two kinds of result are awaited: an `Eval` (by a `Stack`) and an `EvalList` (by a `ListStack`). `eval-stmt` has one call site, so its continuation is folded into `KLetRhs` and `KStmtRest`. [READ S1/machine.sl:1-56,68, pasted below; lines 57-60 declare a helper type `Single` in the second block, left out of the paste.]

```scheme
(def-adts
  ((Stack : ((Env) env) ((Core) c) ((Env) env0) ((Core) c0) -> Type)
    enum
    (many KDone : (erased (Env) env0) (erased (Core) c0) -> (Stack env0 c0 env0 c0))
    (many KAppHead : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (erased (Core) h) (many (List (Core)) args)
       (many (Stack env (CApp h args) env0 c0) k) -> (Stack env h env0 c0))
    (many KCallFn : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (erased (Core) fn) (many (List (Core)) args)
       (many (Stack env (CCall fn args) env0 c0) k) -> (Stack env fn env0 c0))
    (many KCallBody : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args)
       (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Nat) id) (erased (List (Nat)) ps) (erased (Core) body)
       (erased (List (Val)) vals) (erased (Env) env1) (erased (Env) env2)
       (erased (Eval env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val)))) p) (erased (EvalList env args vals) q)
       (erased (BindGroup cenv group group cenv env1) g) (erased (BindAll env1 ps vals env2) b)
       (many (Stack env (CCall fn args) env0 c0) k) -> (Stack env2 body env0 c0))
    (many KMatchScrut : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (erased (Core) scrut) (many (List (Branch)) bs)
       (many (Stack env (CMatch scrut bs) env0 c0) k) -> (Stack env scrut env0 c0))
    (many KMatchBody : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) scrut) (erased (List (Branch)) bs)
       (erased (Nat) ctor) (erased (List (Val)) fields) (erased (List (Nat)) ids) (erased (Core) body) (erased (Env) env1)
       (erased (Eval env scrut (Cons (Val) (VCon ctor fields) (Nil (Val)))) p) (erased (BranchOf bs ctor ids body) br)
       (erased (BindAll env ids fields env1) b)
       (many (Stack env (CMatch scrut bs) env0 c0) k) -> (Stack env1 body env0 c0))
    (many KListHead : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (erased (Core) c) (many (List (Core)) cs)
       (many (ListStack env (Cons (Core) c cs) env0 c0) k) -> (Stack env c env0 c0))
    (many KLetRhs : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (many (List (Nat)) ids) (erased (Core) rhs) (many (Core) rest)
       (many (Stack env (CStmt (SLet ids rhs) rest) env0 c0) k) -> (Stack env rhs env0 c0))
    (many KStmtRest : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Stmt) stmt) (erased (Core) rest) (erased (Env) env1)
       (erased (EvalStmt env stmt env1) p)
       (many (Stack env (CStmt stmt rest) env0 c0) k) -> (Stack env1 rest env0 c0)))
  ((ListStack : ((Env) env) ((List (Core)) cs) ((Env) env0) ((Core) c0) -> Type)
    enum
    (many KAppArgs : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) h) (erased (List (Core)) args) (many (Nat) ctor)
       (erased (Eval env h (Cons (Val) (VAtom ctor) (Nil (Val)))) p)
       (many (Stack env (CApp h args) env0 c0) k) -> (ListStack env args env0 c0))
    (many KCallArgs : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args)
       (many (Env) cenv) (many (List (FnDef)) group) (erased (Nat) id) (many (List (Nat)) ps) (many (Core) body)
       (erased (Eval env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val)))) p)
       (many (Stack env (CCall fn args) env0 c0) k) -> (ListStack env args env0 c0))
    (many KValues : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Core)) items)
       (many (Stack env (CValues items) env0 c0) k) -> (ListStack env items env0 c0))
    (many KListTail : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) c) (erased (List (Core)) cs) (many (Val) v)
       (erased (Eval env c (Cons (Val) v (Nil (Val)))) p)
       (many (ListStack env (Cons (Core) c cs) env0 c0) k) -> (ListStack env cs env0 c0))))

(def-adts
  ((State : ((Env) env0) ((Core) c0) -> Type)
    enum
    (many SEval : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (many (Core) c) (many (Stack env c env0 c0) k) -> (State env0 c0))
    (many SEvalList : (erased (Env) env0) (erased (Core) c0) (many (Env) env) (many (List (Core)) cs) (many (ListStack env cs env0 c0) k) -> (State env0 c0))
    (many SRet : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) c) (many (List (Val)) vs) (erased (Eval env c vs) p)
       (many (Stack env c env0 c0) k) -> (State env0 c0))
    (many SRetList : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Core)) cs) (many (List (Val)) vs) (erased (EvalList env cs vs) p)
       (many (ListStack env cs env0 c0) k) -> (State env0 c0)))
  ((Stepped : ((Env) env0) ((Core) c0) -> Type)
    enum
    (many Next : (erased (Env) env0) (erased (Core) c0) (many (State env0 c0) s) -> (Stepped env0 c0))
    (many Halted : (erased (Env) env0) (erased (Core) c0) (many (Evaled env0 c0) r) -> (Stepped env0 c0))))

(def-fns _ $ (many step : (erased (Env) env0) (erased (Core) c0) (many (State env0 c0) s) -> (many (Stepped env0 c0) r))
```

- [READ S1/machine.sl:68-137] `step` is one `match` on the state with no recursive call; it calls mini's `env-dec`, `bind-all`, `bind-group`, `bind-atoms`, and `branch-dec`, and a five-line `single`. A typical pop: on `SRetList` meeting `KAppArgs` it answers `(Next _ _ $ SRet _ _ env2 (CApp h args) (Cons _ (VCon ctor vs) (Nil _)) (EvApp env2 h args ctor vs p2 p) k2)`.
- [READ S1/machine.sl:99] When the stack is `KDone`, the returned derivation is the goal's: `((KDone _ _) (Halted _ _ $ MkEvaled _ _ vs p))`.
- [READ S1/drive.sl:1-5,48-61] `step-many` recurses by `subterm` on a `Nat` quantum with a `tail` call; `drive` (level `WORK`) calls `step` once, and `drive-batched` calls `step-many` once, then each builds a `def-unique` continuation at level `PROG` that calls it again, as `tests/io_echo.sl` does.

### 4.2 v2: erased tail contexts (`machine_tail.sl`, 154 lines), an improvement I chose, not one the checker forced

- [READ S1/machine.sl:9-14,17-21,26-28] In v1 the frames `KCallBody`, `KMatchBody`, and `KStmtRest` have every field erased except the parent stack. [INFERENCE] They exist only so that popping them can wrap the returned derivation in `EvCall`, `EvMatch`, or `EvStmt`; a machine without derivations would not push them, since the body of a call, the branch of a match, and the rest of a statement are in tail position. Rests on reading the three frames and the three pops at `machine.sl:109-110,117-118,125-126`.
- [RAN] `./bin/slc_sample_v1 chain-drop 10000 500` prints `deepest sampled stack 30002` and `done unary 0 steps 260032`; `./bin/slc_sample_v2 chain-drop 10000 500` prints `deepest sampled stack 3` and `done unary 0 steps 230027`. With `double 10000 500` the two print `59999` and `39997`. (`sample.sl` computes the stack depth once per quantum with `depth.sl` or `depth_tail.sl`.)
- [READ S1/machine_tail.sl:1-35,65-72] v2 replaces the three frames by an erased-only relation `(Tail env c env1 c1)` (constructors `TailHere`, `TailCall`, `TailMatch`, and `TailStmt`, holding what the three frames held), an erased function `finish-tail` that turns `(Eval env c vs)` into `(Eval env1 c1 vs)` by `subterm` recursion on the `Tail`, and

```scheme
  ((Resume : ((Env) env) ((Core) c) ((Env) env0) ((Core) c0) -> Type)
    enum newtype
    (many MkResume : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) c) (erased (Env) env1) (erased (Core) c1)
       (erased (Tail env c env1 c1) t) (many (Stack env1 c1 env0 c0) k) -> (Resume env c env0 c0)))
```

  Every parent pointer of a frame, and the stack of `SEval` and `SRet`, becomes a `Resume`. A tail transition unwraps the `Resume`, extends the `Tail`, and rewraps; `SRet` unwraps and applies `finish-tail` in an erased position before looking at the frame.
- [QUOTE DESIGN.md:1478-1480, §33] "A newtype value built by a wrapping constructor is represented exactly as that constructor's one non-erased field, with no tag and no wrapper." [QUOTE DESIGN.md:1488, §33] "Erased fields occupy no space." [INFERENCE] So by the specification a `Resume` is its `Stack` at run time and the `Tail` costs nothing.
- [READ S1/extract/ref_v2.ml:1349,1655,1657 (the whole `step` function, one line), written by `$R $B machine_tail.sl programs.sl drive.sl main.sl --extract extract/ref_v2.ml`] The reference extractor's OCaml agrees: the `CApp` case builds the frame as `K21_1 { f0 = env; f1 = args; f2 = k }` (three fields, none of the erased ones) and stores it directly in the next state; no application of `MkResume` occurs in `step`; the `SRet` state is matched as `K20_2 { f0 = vs; f1 = resume } -> (let k = resume in ...`; `finish_tail` is defined as `() : Obj.t = (to_any ())` and never called; `MkResume` as a value is `(fun (f0 : Obj.t) : Obj.t -> f0)`. [READ S1/extract/slc_v2.ml:999, written by `$S $B machine_tail.sl programs.sl drive.sl main.sl > extract/slc_v2.ml`] slc's output has the same shape (`K14_1 { f0 = env; f1 = args; f2 = k }`; `K15_2 { f0 = vs; f1 = resume } -> (let k = resume in`), and [RAN] `grep -c 'finish_tail\|MkResume' extract/slc_v2.ml` counts 0. (Variable names shortened in these excerpts.)
- [RAN] v2 type-checked on the first run and passes tests (a), (b), and `test_stuck.sl` (which prints the same lines with `24` for the last).
- [INFERENCE] `KValues` (which wraps an `EvalList` into `EvValues`) is the one remaining frame with only erased data; removing it needs a second kind of tail context from `EvalList` to `Eval`. Not done.

## 5. Measurements

One machine with 4 cores, shared with other agents (load average between 0.7 and 2.5 during the runs, [RAN] `uptime`). Times are the best wall time of the stated number of runs. "Net" subtracts a baseline run that builds the same input and evaluates nothing (`fuel SHAPE N 0`). [RAN] `ocamlfind ocamlopt -version` prints `4.14.1`.

### 5.1 Steps per second, `double`, v1 (`machine.sl`) and v2 (`machine_tail.sl`)

| back end | n | machine | unbatched | quantum 10 | quantum 100 | quantum 1000 | quantum 10000 |
|---|---|---|---|---|---|---|---|
| slc `--build` | 1,000,000 | v1 (38,000,028 steps) | 23.6 M/s | 28.6 M/s | 30.3 M/s | 29.7 M/s | 29.2 M/s |
| slc `--build` | 1,000,000 | v2 (36,000,024 steps) | 25.2 M/s | 27.8 M/s | 29.4 M/s | 31.1 M/s | 29.8 M/s |
| reference `--build` | 1,000,000 | v1 | 23.0 M/s | 27.5 M/s | 28.5 M/s | 31.4 M/s | 29.4 M/s |
| reference `--build` | 1,000,000 | v2 | 25.1 M/s | 27.7 M/s | 29.4 M/s | 28.8 M/s | 29.0 M/s |
| reference interpreter | 100,000 | v1 (3,800,028 steps) | 169 k/s | 155 k/s | | 172 k/s | |
| reference interpreter | 100,000 | v2 (3,600,024 steps) | 162 k/s | 157 k/s | | 163 k/s | |
| `slc --interpret` | 100,000 | v1 | 537 k/s | | | 612 k/s | |

- [RAN] `python3 measure.py slc 1000000 3 double 10,100,1000,10000` (10:53) printed, for v1: baseline `0.157s`; `step ... wall 1.769s net 1.612s ... => 23580387 steps/s`; `batch ... 10 ... net 1.330s => 28574117`; `100 ... net 1.253s => 30332232`; `1000 ... net 1.280s => 29697115`; `10000 ... net 1.303s => 29165034`; for v2: baseline `0.164s`; `net 1.430s => 25167395`; `1.297s => 27762570`; `1.224s => 29417552`; `1.156s => 31133382`; `1.207s => 29824788`.
- [RAN] `python3 measure.py ref 1000000 3 double 10,100,1000,10000` printed, for v1: `net 1.650s => 23035470`; `1.380s => 27529431`; `1.333s => 28498747`; `1.211s => 31369244`; `1.294s => 29356363`; for v2: `1.432s => 25139379`; `1.298s => 27731409`; `1.224s => 29419865`; `1.248s => 28841027`; `1.243s => 28960925`.
- [RAN] `python3 measure.py interp 100000 2 double 10,1000` printed, for v1: baseline `0.930s`; `step ... wall 23.424s net 22.494s => 168932 steps/s`; `batch ... 10 ... net 24.571s => 154653`; `batch ... 1000 ... net 22.093s => 172004`; for v2: baseline `0.875s`; `22.161s => 162451`; `22.965s => 156761`; `22.118s => 162765`.
- [RAN] `python3 timeit.py 2 $S --interpret $B machine.sl programs.sl drive.sl main.sl -- ARGS` printed `0.590s` for `fuel double 100000 0`, `7.667s` for `step double 100000`, and `6.796s` for `batch double 100000 1000`; the table divides 3,800,028 by the differences.
- [QUOTE MANUAL.md:184-185] "`--build prog` writes the same program out and compiles it to `prog` with `ocamlfind ocamlopt -package zarith,unix -linkpkg`". The build commands are in `RUN.md`; [RAN] each took between 0.9 s and 1.6 s.
- [INFERENCE] Driver overhead per step, compiled: (1.612 s − 1.253 s) / 38,000,028 ≈ 9.4 ns, about a quarter of an unbatched step of this machine. Under the interpreter it is below the noise between runs. Arithmetic on the lines above.
- [INFERENCE] Differences of a few percent between neighbouring cells are within run-to-run noise on this shared machine; an earlier run of the same commands at 10:09 gave, for example, 25.0 M/s and 29.6 M/s for slc v1 unbatched and quantum 10.

### 5.2 Against mini's fuelled direct-style `eval` on the same input

| back end | n | fuelled `eval` (fuel 10n+100) | v1 unbatched | v1 quantum 1000 | v2 quantum 1000 |
|---|---|---|---|---|---|
| slc `--build`, net of 2.27 ms start-up (measured on the v1 binary) | 10,000 | 13.5 ms | 18.0 ms | 14.2 ms | 12.4 ms |
| slc `--build`, 8 MB stack | 30,000 | stack overflow | | | |
| slc `--build`, `ulimit -s unlimited` | 100,000 | 0.448 s | | 0.131 s | |
| slc `--build`, `ulimit -s unlimited` | 1,000,000 | 42.3 s | | 1.395 s | |
| reference interpreter, net of 0.61 s | 1,000 | 0.15 s | 0.24 s | | |
| reference interpreter, net of 0.64 s | 10,000 | 2.27 s | 2.33 s | | |
| reference interpreter, 8 MB stack | 30,000 | stack overflow | | | |
| reference interpreter, `ulimit -s unlimited` | 100,000 | 167.6 s | 22.5 s net (default stack) | | |

- [RAN] `python3 total.py 100 ./bin/slc_v1 ARGS` (mean of 100 runs, process start included) printed `2.27 ms` for `fuel double 10000 0`, `15.81 ms` for `fuel double 10000 100100`, `20.29 ms` for `step double 10000`, `16.49 ms` for `batch double 10000 1000`; `./bin/slc_v2` gave `19.19 ms` and `14.66 ms`.
- [RAN] `( ulimit -s unlimited; python3 timeit.py 3 ./bin/slc_v1 ARGS )` printed `0.448s` for `fuel double 100000 1000100`, `0.131s` for `batch double 100000 1000`, `42.348s` for `fuel double 1000000 10000100`, and `1.395s` for `batch double 1000000 1000`.
- [RAN] Interpreter, `python3 timeit.py 3 $R $B machine.sl programs.sl drive.sl main.sl -- ARGS`: `0.611s` (`fuel double 1000 0`), `0.760s` (`fuel double 1000 10100`), `0.851s` (`step double 1000`), `0.644s` (`fuel double 10000 0`), `2.914s` (`fuel double 10000 100100`), `2.975s` (`step double 10000`); `fuel double 30000 300100` printed `Fatal error: exception Stack overflow` at `7.271s`; under `ulimit -s unlimited`, `12.501s` for that and `167.624s` for `fuel double 100000 1000100`.
- [INFERENCE] The fuelled evaluator's time grows faster than linearly with depth (10 times the depth costs 94 times the time between n = 100,000 and n = 1,000,000, compiled). A likely cause is the OCaml 4.14 runtime scanning a deep stack at each minor collection; I did not profile it. The machine's time is linear in the step count across the same range (0.131 s and 1.395 s).

## 6. The converse direction (the stretch goal), for v1

### 6.1 What is stated and proved

- [QUOTE DESIGN.md:419-420, §9] "The elaborated form of a type never contains a function call, and elaborating a type calls none". [INFERENCE] So "`step s` is `Next s2`" cannot be written in a type, and the machine's step relation has to be declared as its own ADT.
- [READ S1/graph.sl:1-121] `StepTo : ((Env) env0) ((Core) c0) ((State env0 c0) s) ((State env0 c0) s2) -> Type` has 25 constructors, one per `Next` that `step` can answer: 11 from `SEval`, 2 from `SEvalList`, 8 from `SRet` (one per frame other than `KDone`), and 4 from `SRetList`. Six take a premise from mini's relations (`EnvOf`, `BindGroup`, `BindAtoms`, `BranchOf`, and `BindAll`). [READ S1/graph.sl:122-127] `Reaches` is its reflexive-transitive closure, as a list: `ReachHere` and `ReachStep`.
- [READ S1/reach.sl:15-18,71-73, pasted]

```scheme
  ((erased eval-reaches : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (subterm erased (Eval env c vs) d)
      (erased (Env) env0) (erased (Core) c0) (erased (Stack env c env0 c0) k) ->
      (erased (Eval env c vs) d2) (erased (Reaches env0 c0 (SEval env0 c0 env c k) (SRet env0 c0 env c vs d2 k)) r))
  ((erased eval-list-reaches : (erased (Env) env) (erased (List (Core)) cs) (erased (List (Val)) vs) (subterm erased (EvalList env cs vs) d)
      (erased (Env) env0) (erased (Core) c0) (erased (ListStack env cs env0 c0) k) ->
      (erased (EvalList env cs vs) d2) (erased (Reaches env0 c0 (SEvalList env0 c0 env cs k) (SRetList env0 c0 env cs vs d2 k)) r))
```

- [RAN] `$R --warn-unused $B machine.sl graph.sl reach.sl traced.sl guided.sl evalby.sl runguided.sl depth.sl programs.sl drive.sl` prints only mini's four `(MkUnit)` lines: no error, no warning. `python3 timeit.py 5 $R $B` prints `0.557s`; with `machine.sl graph.sl reach.sl traced.sl guided.sl evalby.sl runguided.sl` added, `0.860s`.
- [RAN] Every rule is covered, not two or three. Wrong variants are refused: `$R $B machine.sl graph.sl mutants/reach_m1.sl` (a wrong last step in the `EvApp` case) prints ``error: argument 7, `k`, of `StRetValues`: type mismatch: expected `(Stack env (CValues args) __?1 __?2)`, got `(Stack env (CApp h args) env0 c0)` ``; `reach_m2.sl` (first step dropped) and `reach_m3.sl` (claiming zero steps for `EvToken`) print type mismatches on the `Reaches` type; `reach_m4.sl` (the `EvFormer` case deleted) prints ``error: this `match` is missing a branch for the following unrefuted constructor:`` with a note naming `EvFormer`.
- [READ S1/traced.sl:1-86] `step-traced` is `step` with each `Next` also carrying an erased `(StepTo env0 c0 s s2)`; its result type `(Traced env0 c0 s)` is indexed by the source state. [RAN] It type-checks (same command as above). [INFERENCE] So `StepTo` contains the graph of that function. `step` and `step-traced` are two texts; nothing proves they compute the same thing, and a final design would keep only the second.

### 6.2 Lines per case (`reach.sl`, 78 lines in all)

[READ S1/reach.sl:1-81, counted by line numbers.]

| part | lines |
|---|---|
| lemmas `reach-trans`, `reach-one`, `reach-then` | 5, 3, 3 |
| the two signatures, the `def-fns` line, and the `match` line | 8 |
| `EvVar`, `EvFormer`, `EvToken` | 1 each |
| `EvApp` | 8 |
| `EvCall` | 11 |
| `EvMatch` | 8 |
| `EvValues` | 5 |
| `EvStmt`, with `EvLet` (5), `EvDefLvl`, `EvDefFns`, `EvDefAdts` (1 each) inside | 16 |
| `EvLNil` and `EvLCons` | 8 |

[READ S1/reach.sl:21-28] A case reads as the machine's trace: one `let` per premise for the induction hypothesis with the right frame, then a chain. `EvApp` in full:

```scheme
      ((EvApp _ h args ctor vals p q)
        (let ((erased p2) (erased to-head)) (eval-reaches env h _ p _ _ (KAppHead _ _ env h args k)))
        (let ((erased q2) (erased to-args)) (eval-list-reaches env args vals q _ _ (KAppArgs _ _ env h args ctor p2 k)))
        (values (EvApp env h args ctor vals p2 q2)
          (ReachStep _ _ _ _ _ (StApp _ _ env h args k)
            $ reach-trans _ _ _ _ _ to-head
            $ ReachStep _ _ _ _ _ (StRetAppHead _ _ env h args ctor p2 k)
            $ reach-then _ _ _ _ _ to-args (StRetAppArgs _ _ env h args ctor vals p2 q2 k))))
```

### 6.3 What was awkward

- [READ S1/graph.sl:1-121] The relation is the largest single piece (121 lines for 25 rules) and repeats, rule by rule, what `step` already says; each rule spells out both states with every erased index.
- [READ S1/reach.sl:16-18] The theorem returns a derivation `d2` rather than reusing `d`. [INFERENCE] The states hold erased derivations, and a frame stores the derivation the machine built for an earlier premise, so the target state is `(SRet ... d2 k)` for the derivation the path builds, which I did not show equal to `d`. The existential form needs no such equality.
- [RAN] The dependent pair of results in the `EvStmt` case is bound by a `let` whose two binders carry types, the second mentioning the first, with `(match erased p _ ...)` as its right-hand side; the checker accepted the `_` annotation there.
- [RAN] Nothing else was awkward: the first version of `reach.sl` type-checked, with one "lopsided `match`" warning (section 8).

### 6.4 What is still missing for "the machine only diverges if the spec does", stated about the plain `step`

- [INFERENCE] Two facts are missing. (1) Determinism: `(StepTo s a)` and `(StepTo s b)` give `a` equal to `b`. Because states contain derivations, this needs not only that `EnvOf`, `BranchOf`, `BindAll`, `BindGroup`, and `BindAtoms` are functional but that their derivations (and those of `Neq` and `Lt` inside them) are unique. (2) Progress: when some `(StepTo s a)` exists, `step s` does not answer `EvalStuck`. Mini's deciders give no evidence on a miss ([READ S1/core.sl:54,73,121]: `EnvMiss`, `BDStuck`, and `BrMiss` carry only erased indices), so (2) needs either deciders that return evidence of absence or the guided functions of section 7. This rests on reading the relation and the deciders; I wrote neither lemma.
- [INFERENCE] The intrinsically typed state is what makes direction "halts ⇒ derives" free and is also what makes (1) depend on uniqueness of derivations. A machine over proof-free states with one erased invariant beside it would reverse that trade. Not tried.
- [RAN] Section 7 sidesteps both: the guided machine needs neither determinism nor progress, because it follows the given path and has no stuck branch.

## 7. Fuel-free without the driver, given an erased derivation

- [QUOTE DESIGN.md:493-495, §12] "The `is` clause gives `d` its type through `c` while its multiplicity differs. This is how an erased witness is turned into a runtime value."
- [READ S1/guided.sl:1-39] Five functions redo mini's lookups and binders guided by an erased proof and return `is` results, for example `env-get : (subterm many (Env) env) (many (Nat) x) (erased (Val) v) (erased (EnvOf env x v) p) -> (many v is found)`. Their impossible cases are absurd branches discharged by the proof itself or by mini's `neq-irrefl`.

### 7.1 `eval-by`: the direct evaluator with the fuel replaced by the derivation (`evalby.sl`, 56 lines)

- [READ S1/evalby.sl:2] `(many eval-by : (erased (List (Val)) vs) (many (Env) env) (many (Core) c) (subterm erased (Eval env c vs) d) -> (many vs is out))`, with `eval-list-by` and `eval-stmt-by` alike.
- [READ S1/evalby.sl:1-56] In each branch a `(let-match erased d (EvXxx ...))` picks the one rule that fits the code (the others are refuted automatically), run-time values are taken apart by `let-match` with no other branch (`(let-match many head (VAtom ctor))`), and the calls on a call's body, a match's branch, a `values`, and a statement's rest are written `tail`.
- [RAN] `$R $B guided.sl evalby.sl programs.sl test_evalby.sl` (derivation obtained from mini's fuelled `eval` by `comptime-match`, then `(eval-by vs (ENil) program derivation)`) prints the ten-`VCon 12` numeral that `double` of five should give.
- [RAN] `./bin/slc_guided direct double 10000 100000000` prints `guided direct evaluator: unary 20000`; `python3 timeit.py 5` gives `0.022s` for it and `0.017s` for `none double 10000 100000000` (the plain machine run that produces the derivation), so about 5 ms for the guided evaluation. `./bin/slc_guided direct double 1000000 100000000` prints `Fatal error: exception Stack overflow`.
- [RAN] `mutants/evalby_m1.sl` (arguments of the constructor dropped) is refused: ``value mismatch: expected `(VCon ctor __1)`, got `(VCon ctor (Nil (Val)))` ``; `mutants/evalby_m2.sl` (wrong environment for the body) is refused with a type mismatch on `d`.
- [RAN] A `many` function recursing on a `subterm erased` parameter has precedent: `grep -n "subterm erased" tests/comptime_tail.sl` shows a line starting `(def-fns X $ (many countdown : (subterm erased (Nat) n) (many (Bin) c) (erased (Numeral c n) v)`. [QUOTE DESIGN.md:864-865, §21] "Subterm recursion (§17) may go through an erased field."
- [QUOTE DESIGN.md:1319-1322, §31] "The semantics is that of a machine with unlimited stack and heap. A real run may crash where the host cannot represent what is asked of it. A crash produces no value, never a different one."

### 7.2 `run-guided` and `run-from-spec`: the machine as one total function (`runguided.sl`, 118 lines)

[READ S1/runguided.sl:1-2,117-119, pasted]

```scheme
(def-fns _ $ (many run-guided : (erased (Env) env0) (erased (Core) c0) (erased (List (Val)) vs) (erased (Eval env0 c0 vs) p)
    (many (State env0 c0) s) (subterm erased (Reaches env0 c0 s (SRet env0 c0 env0 c0 vs p (KDone env0 c0))) path) -> (many vs is out))

(def-fns _ $ (many run-from-spec : (many (Core) program) (erased (List (Val)) vs) (erased (Eval (ENil) program vs) derivation) -> (many vs is out))
  (let ((erased rebuilt) (erased path)) (eval-reaches (ENil) program vs derivation (ENil) program (KDone _ _)))
  (run-guided _ _ vs rebuilt (load program) path))
```

- [READ S1/runguided.sl:3-115] `run-guided` matches the run-time state as `step` does; in each branch it takes the erased path apart (`(let-match erased path (ReachStep _ _ _ _ _ first rest))`), takes the erased step apart with the one `StepTo` rule that fits, builds the next state with the guided lookups, and makes a `tail` call on `rest`. On `SRet` meeting `KDone` it returns the values: `(let-match erased path (ReachHere _ _ _) (absurd (ReachStep _ _ _ _ _ first _) first))`. It has no stuck branch and no `Stepped` result.
- [RAN] `./bin/slc_guided machine double 1000000 100000000` prints `guided machine: unary 2000000` (then the plain run's `done unary 2000000 steps 38000028`); the same under `ulimit -s 64` prints the same two lines, for the slc build and for the reference build. `python3 timeit.py 5` gives `2.496s` for it and `1.458s` for `none double 1000000 100000000`, so about 1.04 s for the guided run of 38,000,028 steps.
- [RAN] Three mutants are refused: a wrong stack (`runguided_m1.sl`: ``expected `(Stack env h env0 c0)`, got `(Stack env (CApp h args) env0 c0)` ``), a wrong final value (`runguided_m2.sl`: ``value mismatch: expected `vs`, got `(Nil __?1)` ``), and a deleted frame case (`runguided_m3.sl`: a missing branch for `KListHead`).
- [INFERENCE] Read as a theorem: for every `program` and `vs`, an erased `(Eval (ENil) program vs)` suffices for a total function that runs the explicit-stack machine and returns exactly `vs`. This is the shape of the handoff's item 4(ii), a previous session's formulation ("under a hypothesis H that every accepted compile-time form's spec run halts, `compile` is a total function", [READ handoff.md:22]), with H supplying the derivation. Whether H can be supplied in that form is outside this spike.
- [INFERENCE] `run-guided` and the driver-looped `step` are different functions. Each is tied to the spec on its own (one returns the spec's values, the other returns a spec derivation with its values); nothing proves the unguided one halts whenever the guided one does (section 6.4).

## 8. Every place the checker objected

[RAN] These are all the errors and warnings of the session, in order, the deliberate mutants aside; every other first check of a new file printed nothing. In particular `machine.sl` (apart from one warning), `machine_tail.sl`, `graph.sl`, `reach.sl` (apart from one warning), `traced.sl`, `guided.sl`, `evalby.sl`, `run-guided`, and the three `heap/` files were accepted as first written.

1. ``drive.sl:33:5: error: no telescope to reuse for `_` `` for `(let ((many outcome)) (match many result _ ...))`. Got around by typing the binder: `(let ((many (String) outcome)) ...)`. [QUOTE DESIGN.md:2255, §47] "`let` whose binders all carry a type or `is` clause".
2. ``drive.sl:40:31: error: argument 2, `p`, of `MkU8`: type mismatch: expected `(Lt 0 u8-modulus)`, got `(Lt (Zero) u8-modulus)` `` with the note "0 in `(Lt 0 u8-modulus)` is a numeral literal, opaque to the checker by default". Got around by writing `(MkU8 (Zero) u8-modulus-pos)`.
3. ``drive.sl:50:69: error: same-level call to `finish` decreases no subterm argument`` with the hint "consider defining `finish` at a lower level, or `drive` at a higher one". Got around with a third level `FINISH` minted before `WORK`.
4. ``test_a_program.sl:10:14: error: `(level-of load)` was not in scope when level `PROG` was minted``, and later the same for `rerun` in `main_guided.sl`. Everything the program's continuation calls must sit at a level minted before the program's level, and a level is minted where its `def-lvl` (or the `_` of a `def-fns`) stands. Got around by moving `load` above the `def-lvl`s and by defining `rerun` at the existing level `WORK`. This is the one rule that shaped the file layout: helpers first, then `def-lvl FINISH`, `WORK`, `PROG`, then the drivers, then the `start` continuation.
5. ``runguided.sl:119:45: error: argument 6, `path`, of `run-guided`: type mismatch: expected `(Reaches (ENil) program __1 (SRet ...))`, got `(Reaches (ENil) program (SEval (ENil) program (ENil) program (KDone (ENil) program)) (SRet ...))` `` with the note "`__1` is anonymous, minted here" at `(load program)`. A call's result is opaque to the checker. Got around by giving `load` an `is` return: `-> (many (SEval (ENil) program (ENil) program (KDone (ENil) program)) is s)`.
6. Warnings: ``machine.sl:128:8: warning: lopsided `match`; flatten it with a `let-match` on `KCallArgs` `` and the same at `reach.sl:74:6` on `EvLCons` (rewritten as `let-match` with branches); four ``unused `env`; write `_` in its place`` under `--warn-unused` (done); ``declaration of `nat-or` shadows a previous binder`` (renamed `parse-nat-or`); ``declaration of `pred-body` shadows a previous binder`` when a test repeated a name of `programs.sl` (the test no longer loads `programs.sl`).

Rules that shaped the code without producing an error:

- [QUOTE DESIGN.md:933-935, §21] "When the discriminant is erased, that is, an `erased` match or a match on a union in any mode, at most one branch may be **real**." [INFERENCE] So `run-guided` cannot ask the erased path whether to stop; it tests the run-time state for `KDone` and uses the path only to refute and to recurse.
- [QUOTE DESIGN.md:920-922, §21] "Its body is checked against the annotation as written, with no branch-forced facts." [INFERENCE] So where a branch must refute something about the scrutinee, `run-guided` lists each frame instead of using `else`.
- [QUOTE DESIGN.md:723-725, §18] "After canonicalization, `a` must be a strict subtree of `b`. The search walks through applications of type constructors and value constructors". [RAN] The recursive call on `p1`, two constructors below `d` in the `EvStmt` and `EvLet` case, was accepted with no written proof.

## 9. Does it scale to a mutable heap? A second prototype (`S1/heap/`, 174 lines)

- [READ S1/heap/heap.sl:1-35] A language `HExpr` with `HLit`, `HGet`, `HSet`, `HPred`, `HSeq`, and `HWhile`; values are `Nat`; the store model is `(List (Copy (Nat)))`; the spec threads the store: `HEval : (Store before) ((HExpr) e) ((Nat) v) (Store after) -> Type`, with the prelude's `Nth` for a read and `SetNth` for a write, and a `HvWhileStep` rule whose third premise is the rest of the loop.
- [READ S1/heap/heap.sl:37-90] The stack type is `(HStack s e s0 e0)`: it awaits the evaluation of `e` *started in store `s`*. A frame stores the erased derivation of an earlier premise with both of its stores, for example `HKSetValue` holds `(erased (HEval s address a s1) p)` and awaits the value's evaluation from `s1`. Tail positions (the second half of `HSeq`, the rest of a loop) use the erased `HTail` and `newtype` `HResume` of section 4.2. The control is `many` and indexed by the store model as it is now: `(HControl now s0 e0)`.
- [READ S1/heap/heapstep.sl:1-2, pasted]

```scheme
(def-fns _ $ (many hstep : (erased Store now) (erased Store s0) (erased (HExpr) e0) (many (HControl now s0 e0) c) (unique (Array (Copy (Nat)) now) heap) ->
    (erased Store after) (unique (Array (Copy (Nat)) after) heap-after at heap) (many (HStepped after s0 e0) r))
```

- [READ S1/heap/heapstep.sl:18-32] A read does `array-length`, `lt-dec`, `std/list.sl`'s `nth-exists`, and `array-get`; a write does the same and `array-place`, whose `SetNth` result goes straight into `HvSet`. An address out of range answers `HStuck`.
- [QUOTE DESIGN.md:1333-1335, §32] "Its body may close over `unique` binders as unique: each such binder that the body uses at unique is consumed by the definition itself". [READ S1/heap/heapdrive.sl:30-39] `hdrive` passes the `unique` array to `hstep-many`, and the `def-unique` continuation closes over the array it got back.
- [RAN] `$R --warn-unused /home/user/sleight/std/list.sl heap/heap.sl heap/heapstep.sl heap/heapdrive.sl -- 5 1 1` prints `done value 0 steps 86` (count a one-cell store down from 5 in a `while`, then read the cell); with a store of size 0 (`-- 5 0 1`) it prints `stuck steps 5`.
- [RAN] `/usr/bin/time -f "%es wall, %MKB max RSS" ./bin/slc_heap N 1 Q` prints, with the program's `done value 0 steps ...` line: `0.02s wall, 5792KB` for N = 100,000, Q = 1 (1,500,011 steps); `0.21s, 5864KB` for N = 1,000,000, Q = 1; `2.28s, 5944KB` for N = 10,000,000, Q = 1 (150,000,011 steps); `0.83s, 5904KB` for N = 10,000,000, Q = 1000. `( ulimit -s 64; ./bin/slc_heap 10000000 1 1 )` prints the `done` line.
- [RAN] Mutants are refused: using the array after it was consumed (``error: unique value `heap1` has conflicting non-erased uses``), and returning the old store index after a write (``expected `(SetNth (Copy (Nat)) now a (MkCopy (Nat) v) now)`, got `(SetNth (Copy (Nat)) now a (MkCopy (Nat) v) after)` ``).

Assessment:

- [INFERENCE] The direction "halts ⇒ derives" needs no heap invariant: a frame's derivation is about stores named in its own indices, and composing derivations is threading indices. That is why the store prototype was no harder than the pure one. Rests on the prototype above, which has one store and no allocation.
- [INFERENCE] What changes for a full evaluator: (1) the spec relation gains a store before and after, and every stack, tail, and control type gains the store index; (2) `step` takes and returns the `unique` store beside the `many` control; (3) each access needs evidence the address is valid, obtained by a run-time check (as here) or from an invariant; (4) the relation `StepTo` and the proof of section 6 gain the same indices. I expect (4) to grow in proportion to the rule count, as in section 10, but did not write it for the store machine.
- [UNKNOWN] Allocation. The prototype's store has a fixed size. [QUOTE MANUAL.md:23-24] "holds `Vec`, a growable array indexed by its contents" (said of `std/vec.sl`); [READ std/vec.sl:395, that line only] it defines a `vec-push`. I did not use it, so a growing store under this pattern is untested.
- [INFERENCE] The spec's store model here is the index type the prelude's array happens to have, `(List (Copy (Nat)))`. A spec with its own model of blocks and words would need a representation relation between that model and the run-time structure's index, and lemmas for each access. Not explored.
- [UNKNOWN] Whether values that are addresses, sharing, and DESIGN.md's slots (§35 to §38) fit the same indices. Nothing here tests them.

## 10. Code size

[RAN] Non-blank, non-comment lines and bytes, by `sed -n A,Bp FILE | grep -vc '^[[:space:]]*$\|^[[:space:]]*;'` and `wc -c`:

| piece | lines | bytes |
|---|---|---|
| mini's `Eval`, `EvalList`, `EvalStmt` relation (`eval.sl` 6-36), needed by everything | 31 | 3,394 |
| **mini's fuelled evaluator**: result types (38-50) and `eval`, `eval-list`, `eval-stmt` (52-125) | 13 + 74 = **87** | 861 + 4,864 = 5,725 |
| **machine v1** (`machine.sl`): stack types 42, state types 17, and `single`, `step`, and `load` 77 | **136** | 10,728 |
| machine v2 (`machine_tail.sl`): `Tail` and `finish-tail` 28, stack types 32, state types 17, and functions 77 | 154 | 12,147 |
| driver: `step-many`, printer, levels, `finish`, `drive`, and `drive-batched` (`drive.sl`) | 54 | 3,649 |
| step relation and closure (`graph.sl`) | 127 | 12,266 |
| converse proof (`reach.sl`) | 78 | 6,643 |
| `step-traced` (`traced.sl`) | 85 | 7,032 |
| guided lookups (`guided.sl`) | 35 | 2,494 |
| `eval-by` (`evalby.sl`) | 56 | 2,937 |
| `run-guided` and `run-from-spec` (`runguided.sl`) | 118 | 8,118 |
| store prototype (`heap/heap.sl`, `heapstep.sl`, and `heapdrive.sl`) | 84 + 50 + 40 | 13,885 |

- [INFERENCE] The erased-derivation-carrying machine is about 1.6 times the fuelled evaluator in lines and 1.9 times in bytes (136 against 87; 10,728 against 5,725). Most of the difference is the stack types (42 lines), which the fuelled evaluator gets from the host; the proof terms inside `step` are the same `EvXxx` applications the fuelled evaluator writes.
- [INFERENCE] The converse direction costs more than the machine: relation plus proof is 205 lines, about 1.5 times the machine, and `run-guided` adds 118. Across machine, relation, proof, and guided runner the count is 459 lines for 8 expression forms and 4 statement forms, about 40 lines per form. Arithmetic on the table.
- [INFERENCE] `eval-by` with its lookups (91 lines) is the size of the fuelled evaluator (87) and needs no machine, relation, or proof.

## 11. Options this suggests (proposals for the lead and the owner, none decided)

1. [INFERENCE] If the evaluator must run code whose halting is not known, the driver-looped machine is the only one of the three that fits, and v2 (erased tail contexts) is the variant to take, since v1's stack grows on every object-level tail call and statement.
2. [INFERENCE] If the theorem is to have the form "given the spec's run (hypothesis H), the compiler's evaluation is total and agrees", `eval-by` gives it in about 90 lines with a host stack proportional to non-tail nesting, and `run-from-spec` gives it with a constant host stack at about five times the code (machine, relation, proof, guided lookups, and guided runner).
3. [INFERENCE] The two can coexist: the unguided machine under the driver where no derivation is at hand, a guided function where one is. They are separate functions, each tied to the spec directly.
4. [INFERENCE] If "stuck" must mean "the spec has no derivation" (the handoff's proposal that rejections carry a derivation of a positive relation, [READ handoff.md:40]), mini's deciders need to return evidence on a miss; this spike did not do that.
5. [INFERENCE] A quantum of 100 to 1,000 steps per driver step recovers the driver's overhead when compiled (about 9 ns per driver step); under the interpreters it makes no measurable difference.

## 12. Things I am least sure of

1. [INFERENCE] That nothing erased costs anything at run time. I read the extracted `step` of v2 from both compilers (section 4.2) and it holds there; I did not read the extracted code of the store machine or of the guided runners, where the same is expected.
2. [INFERENCE] That the checker's acceptance of `eval-reaches`, `run-guided`, and `eval-by` means what their types say. Evidence: 14 mutants across the files were all refused with the expected messages. I did not review `lib/elab.ml`, and [QUOTE DESIGN.md:438-439, §10] "There is no universe stratification, and no positivity requirement on function or datatype signatures", so the logic itself is not known to be consistent; the handoff records the owner as not expecting a `no_false` theorem ([READ handoff.md:19]).
3. [INFERENCE] The cause of the fuelled evaluator's superlinear time at great depth (section 5.2); the numbers are measured, the explanation is a guess.
4. [INFERENCE] The timings. The machine was shared; I report best-of-k wall times, and repeated runs of the same command differed by up to about 10 percent (for example `1.381s` and `1.521s` for `./bin/slc_guided none double 1000000 100000000` in two sessions of five runs).
5. [UNKNOWN] How the pattern behaves with allocation, addresses as values, and slots (section 9). The store prototype covers one fixed-size store of numbers.
6. [INFERENCE] The figure of about 40 lines per form for the full set of artifacts comes from 12 forms of a language with no multiplicities, cells, or coercions; I would not extrapolate it to full Sleight without a second data point.
7. [UNKNOWN] Whether a `many` function recursing on a `subterm erased` parameter is intended by the owner. DESIGN.md's telescope grammar allows the combination and a test uses it (section 7.1); I found no sentence that discusses it ([RAN] `grep -n "subterm erased" DESIGN.md` prints nothing).
8. [INFERENCE] `chain-drop` is a poor benchmark: its cost is quadratic in `n` because every `let` deepens the environment that `env-dec` walks. I use it only for stack depth, at `n` up to 10,000. A compiled run of it at `n` = 1,000,000 did not finish in ten minutes and was stopped, and under the interpreter `n` = 10,000 takes minutes.
