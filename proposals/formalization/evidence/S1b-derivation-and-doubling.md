# S1b: recursion on an erased derivation, and fuel doubling

Two spikes on `mini/`'s evaluator, for comparison with the explicit-stack machine another agent is building.
All code is in `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S1b/`;
`RUN.md` there lists every command. I modified nothing in `/home/user/sleight`; the four `mini/` files I
load are copies that `cmp` reports identical to the originals `[RAN]`.

Tags: `[QUOTE file:line]`, `[RAN]`, `[READ file:lines]`, `[INFERENCE]`, `[UNKNOWN]`, as the common brief
defines them. In `[RAN]` items, `$M` is `/home/user/sleight/_build/default/bin/main.exe`, `$SLC` is
`/home/user/sleight/_build/release/slc`, and commands run in the S1b directory.

## 1. Findings that bear on the decision

1. **Pattern 1 works, and is small.** `eval-by` computes an expression's values with no fuel argument and no
   failure outcome, recursing on an erased derivation. Both checkers accept it. It needed no lemma.
   `[RAN]` section 2.1, 2.2.
2. **Pattern 1 is a theorem, not an entry point.** Its signature is "given a derivation of the spec's run,
   evaluation is a total function". Nothing in a compiler can hand it that derivation for arbitrary input
   except a run that has already halted. `[INFERENCE]` section 3.
3. **Pattern 2 works with a small change.** One failure constructor carrying `Stuck` or `OutOfFuel`, and a
   16-line `Program` step that doubles the fuel. It runs under the reference interpreter, reference
   `--build`, `slc --build`, and `slc --interpret`. `[RAN]` section 4.
4. **Retries can waste much more than a constant factor**, because mini's fuel bounds depth. Measured: 1.0
   to 1.5 times a single run on a program whose work grows with its depth, and about 9 times on a program that
   does a large shallow computation before a deep one. `[RAN]` section 5.
5. **"The answer never depends on the fuel" is provable, and is proved here**, but only for an evaluator
   that returns evidence on failure as well as on success. The statement cannot be made about `mini/eval.sl`'s
   `eval` as it stands, because a Sleight type cannot mention a function call. The proof is about 600 lines
   including the evaluator, against 73 lines for all of Pattern 1. `[RAN]` section 6.
6. **A measured side effect:** `eval-by` ran 1.7 times faster than the fuelled `eval` under the interpreter,
   and 7 to 11 times faster compiled at depth 400000, where the fuelled evaluator's stack depth dominates.
   `[RAN]` section 2.5.

## 2. Pattern 1: recursion on an erased derivation

### 2.1 Final signatures

`[READ proto/S1b/evalby.sl:1-78]` (whole file), pasted:

```scheme
env-by        : (many (Env) env) (many (Nat) x) (erased (Val) v) (subterm erased (EnvOf env x v) p) -> (many v is r)
bind-all-by   : (many (Env) env) (many (List (Nat)) ids) (many (List (Val)) vs) (erased (Env) out)
                (subterm erased (BindAll env ids vs out) p) -> (many out is r)
bind-group-by : (many (Env) cenv) (many (List (FnDef)) group) (many (List (FnDef)) defs) (many (Env) env) (erased (Env) out)
                (subterm erased (BindGroup cenv group defs env out) p) -> (many out is r)
bind-atoms-by : (many (Env) env) (many (List (Nat)) ids) (erased (Env) out) (subterm erased (BindAtoms env ids out) p) -> (many out is r)
branch-by     : (many (List (Branch)) bs) (many (Nat) c) (erased (List (Nat)) fields) (erased (Core) body)
                (subterm erased (BranchOf bs c fields body) p) -> (many fields is fs) (many body is b)
eval-by       : (many (Env) env) (many (Core) c) (erased (List (Val)) vs) (subterm erased (Eval env c vs) d) -> (many vs is r)
eval-list-by  : (many (Env) env) (many (List (Core)) cs) (erased (List (Val)) vs) (subterm erased (EvalList env cs vs) d) -> (many vs is r)
eval-stmt-by  : (many (Env) env) (many (Stmt) s) (erased (Env) out) (subterm erased (EvalStmt env s out) d) -> (many out is r)
```

`eval-by`'s signature is the one the task proposed `[READ proto/S1b/evalby.sl:32]`. The last three are one
`def-fns` block `[READ proto/S1b/evalby.sl:31-78]`.

### 2.2 It is accepted

- `[RAN]` `$M --warn-unused base.sl term.sl core.sl eval.sl evalby.sl` prints five `(MkUnit)` lines, no error,
  and no warning. A first test of `env-by` alone drew one warning (section 8, item 1); with that fixed, the
  whole file compiled without an error or a warning on its first run (this session's history; the files do
  not record it).
- `[RAN]` The signature stated as a goal, with `eval-by` given as its proof:
  `$M --goal proved base.sl term.sl core.sl eval.sl evalby_goal.sl evalby.sl evalby_qed.sl` prints
  `evalby_goal.sl:7:1: note: proved` `` `(goal many (EvalTotal))` `` and `--goal proved: PASS`. The same
  command with `$SLC` prints the same two lines and `PASS`. `EvalTotal` packages a level with a function of
  the type above `[READ proto/S1b/evalby_goal.sl:1-7]`.
- The rule it rests on: `[QUOTE DESIGN.md:864-865]` (§21) "Subterm recursion (§17) may go through an erased
  field." and `[QUOTE DESIGN.md:696-699]` (§17) "Termination rests on levels. A function's parameters may be
  marked `subterm`; the marks are part of its signature. Every call decreases a lexicographic order whose
  first component is the level, followed by the `subterm`-marked arguments from left to right."
- The repository already has `many` functions that recurse on an erased `subterm` parameter:
  `[READ tests/erased_subterm.sl:12-15]`, `[READ tests/nub.sl:28-31]`, `[READ tests/comptime_tail.sl:33-41]`.

### 2.3 Answers to the task's questions

**(a) Erased decreasing argument with a non-erased result; the one-real-branch rule.**

Accepted (2.2). The rule does get in the way if the derivation is matched first:

- `[QUOTE DESIGN.md:933-937]` (§21) "When the discriminant is erased, that is, an `erased` match or a match on
  a union in any mode, at most one branch may be **real**. The others must each be automatically absurd,
  absurd by proof, or the branch of a phantom constructor under a non-erased scrutinee."
- `[RAN]` `probes/a1_erased_first.sl` matches `d` at `erased` with two present branches in a `many`
  function: `error: a match without a runtime discriminant can have only one real branch`.
- `[RAN]` `probes/a2_letmatch_erased_first.sl` writes `(let-match erased d (EvLNil _))` before looking at
  `cs`: ``error: this `let-match` is missing a branch for the following unrefuted constructor:`` with the note
  ``value constructor `EvLCons`, which is declared here``.
- `[RAN]` `probes/a3_use_erased_field.sl` returns `vs` directly:
  ``error: `vs`, declared `erased`, used in a non-erased position``.
- `[RAN]` `probes/a4_no_decrease.sl` calls itself on the same `d`:
  ``error: same-level call to `eval-by4` decreases no subterm argument``.
- `[RAN]` `probes/a5_erased_fn_ok.sl`: the same two-branch match on `d` is accepted in an `erased` function.

The working idiom, used in every case of `evalby.sl`: match the run-time data at `many` first, so the
derivation's index refutes every rule but one, then `let-match erased` on the derivation.

```scheme
((CApp h args)
  (let-match erased d (EvApp _ _ _ ctor vals p q))
  (let-match many (notail $ eval-by env h (Cons _ (VAtom ctor) (Nil _)) p) (Cons _ hv _))
  (let-match many hv (VAtom ctor2))
  (Cons _ (VCon ctor2 (notail $ eval-list-by env args vals q)) (Nil _)))
```

Where the rule is chosen by a run-time test and not by a constructor, as in `EnvOf` (here or further on),
the function makes the test and then matches the proof with one real branch and one absurd-by-proof branch
`[READ proto/S1b/evalby.sl:1-5]`:

```scheme
(match many (nat-dec x y) _
  ((NDSame _) (match erased p _ ((EnvHere _ _ _) w) (absurd (EnvThere _ _ _ _ _ n _) (neq-irrefl x n))))
  ((NDDiff _ _ n) (match erased p _ (absurd (EnvHere _ _ _) (neq-irrefl x n)) ((EnvThere _ _ _ _ _ _ p2) (tail $ env-by rest x v p2)))))
```

**(b) Does a `many` match on the returned value refute the other constructors?**

Yes. A call's result `is` the derivation's value through the return `(many vs is r)`, and forcing refutes the
rest.

- `[RAN]` `evalby.sl` is accepted with `(let-match many fv (VClo cenv2 group2 def))` and no other branch
  (line 45), and the same for `VAtom` (line 40) and `VCon` (line 54).
- `[RAN]` `probes/b4_call_result_refutes.sl` lists `(absurd VCon)`, `(absurd VFormer)`, `(absurd VClo)`,
  `(absurd VToken)`, and `(absurd Nil)` after such a call and is accepted; §21 makes `(absurd C)` an error
  unless `C` is refuted `[QUOTE DESIGN.md:914]` "It is an error if `C` is not refuted."
- `[RAN]` `probes/b5_call_result_wrong_branch.sl` writes a present `VCon` branch:
  ``error: branch `VCon` is refuted; omit it or write `(absurd VCon)` ``.

`EnvMiss` cannot be refuted from the `EnvOf` evidence, because mini's `EnvMiss` carries none
`[READ mini/core.sl:51-54]`:

- `[RAN]` `probes/b1_envdec_miss.sl` (`let-match` on `(env-dec env x)` naming only `EnvHit`):
  ``error: this `let-match` is missing a branch for the following unrefuted constructor:`` naming `EnvMiss`.
- `[RAN]` `probes/b2_envdec_absurd.sl` (`(absurd (EnvMiss _ _) p)`):
  ``error: `p` : `(EnvOf env x v)` is not refuted: it may be headed by `EnvHere` ``.
- `[RAN]` `probes/b3_envdec_hit_only.sl` (the miss assumed away): the hit's value is not known to be the
  derivation's: ``error: value mismatch: expected `v`, got `w` ``.

So a lookup that recurses on the erased `EnvOf` proof is the short route (`env-by`, 5 lines). The other
route was also built: `[RAN]` `probes/b6_envdec_strengthened.sl` gives `EnvMiss` a `NoEnv` proof, proves
`no-env-absurd` and uses `env-of-unique`; it is accepted and prints `(VAtom 7)`, and takes 23 lines besides the 10 of `env-of-unique`.

**(c) Lemmas for functional relations.**

None were needed. Each helper follows the derivation it is given, so no second derivation of the same
judgment ever arises `[READ proto/S1b/evalby.sl:1-78]`.

Lemmas are needed only if mini's own deriving functions are reused, since they return their own outputs
and evidence:

- `[RAN]` `probes/c2_reuse_bindgroup_nolemma.sl` calls mini's `bind-group` in place of `bind-group-by`:
  ``error: argument 5, `p`, of `bind-all-by`: type mismatch: expected `(BindAll e1 ps2 vals2 env2)`, got `(BindAll env1 ps2 vals2 env2)` ``.
- `[RAN]` `probes/evalby_b.sl` reuses `bind-group` and `bind-atoms` with `bind-group-unique` and
  `bind-atoms-unique` and is accepted. That works only for those two, which have no failure outcome; for
  `env-dec`, `bind-all`, and `branch-dec` the miss cannot be refuted (b1, b2 above).
- All the functionality lemmas were written anyway, for section 6: `evaluniq.sl` proves `env-of-unique`,
  `bind-all-unique`, `bind-group-unique`, `bind-atoms-unique`, `branch-of-unique`, and `eval-unique`,
  `eval-list-unique`, and `eval-stmt-unique`. `[RAN]` `$M --warn-unused base.sl term.sl core.sl eval.sl
  evaluniq.sl`: accepted, no warning. 84 lines. `[RAN]` `probes/c1_uniq_missing_step.sl` drops one step and
  is refused: ``argument 6, `q`, of `eval-unique`: type mismatch: expected `(Eval env2 body3 v2)`, got `(Eval env23 body3 v2)` ``.

`eval-unique`'s signature `[READ proto/S1b/evaluniq.sl:43]`:

```scheme
eval-unique : (erased (Env) env) (erased (Core) c) (erased (List (Val)) v1) (erased (List (Val)) v2)
              (subterm erased (Eval env c v1) p) (erased (Eval env c v2) q) -> (erased (Eq (List (Val)) v1 v2) e)
```

**(d) Line count; fuel-free and stuck-free.**

| | lines | source |
|---|---|---|
| mini's `eval`, `eval-list`, `eval-stmt` | 74 | `[RAN]` `sed -n '52,125p' eval.sl \| wc -l` |
| mini's outcome types `Evaled`, `EvaledList`, `EvaledStmt` | 13 | `[RAN]` `sed -n '38,50p' eval.sl \| wc -l` |
| mini's `env-dec`, `bind-all`, `bind-group`, `bind-atoms`, `branch-dec` | 29 | `[RAN]` `sed` over `core.sl` lines 56-61, 75-81, 93-97, 106-109, 123-129 |
| `eval-by`, `eval-list-by`, `eval-stmt-by` | 48 | `[RAN]` `sed -n '31,78p' evalby.sl \| wc -l` |
| the five `-by` helpers | 25 | `[RAN]` non-blank lines of `evalby.sl` 1-29 |

So 73 lines replace 116, and the three decision types `EnvDec`, `BindDec`, and `BranchDec` are not used.

- Fuel-free and stuck-free in the source: `[RAN]` `grep -c 'Stuck\|fuel\|Fail' evalby.sl` prints `0`.
- Fuel-free at run time: `[RAN]` `$M base.sl term.sl core.sl eval.sl evalby.sl program_small.sl
  evalby_demo.sl --extract /dev/stdout | grep -o 'let rec v[0-9]*_eval_by ([^=]*='` prints
  `let rec v55588_eval_by (v55630_env : Obj.t) (v55632_c : Obj.t) : Obj.t =`: two run-time parameters, the
  environment and the code.
- `[READ proto/S1b/probes/evalby_demo.ml:1647-1654]` The extracted helpers and the three evaluators take
  only their `many` parameters; a refuted constructor has no case in the extracted `match`.
- `[INFERENCE]` Because refuted cases have no code, the extracted function's safety rests on the
  derivation being real. Rests on reading the extracted OCaml; I did not run it on a value the proof excludes,
  and the language gives no way to do so.

### 2.4 Use on the `tests/mini_eval.sl` program

`[READ proto/S1b/evalby_demo.sl:1-6]`:

```scheme
(def-fns _ $ (many rerun : (many (Nat) fuel) (many (Env) env) (many (Core) c) -> (many (Maybe (List (Val))) r))
  (match many (eval fuel env c) _
    ((EvalStuck _ _) (None _))
    ((MkEvaled _ _ vs p) (Some _ (eval-by env c vs p)))))
(rerun 1000 (ENil) program)
```

- `[RAN]` `$M base.sl term.sl core.sl eval.sl mini_eval.sl | tail -1` (the baseline) prints
  `(MkEvaled _ _ (Cons _ (VCon 12 $ Cons _ (VCon 11 $ Nil _) $ Nil _) $ Nil _) _)`.
- `[RAN]` `$M --warn-unused base.sl term.sl core.sl eval.sl evalby.sl program_small.sl evalby_demo.sl | tail -1`
  prints `(Some _ $ Cons _ (VCon 12 $ Cons _ (VCon 11 $ Nil _) $ Nil _) $ Nil _)`: the same values. The same
  under `--no-extern`.
- `[RAN]` At the top level, with `comptime-match` binding the derivation (`evalby_demo_top.sl`): prints
  `(Cons _ (VCon 12 $ Cons _ (VCon 11 $ Nil _) $ Nil _) $ Nil _)`.
- `[RAN]` Compiled by slc: `$SLC base.sl term.sl core.sl eval.sl evalby.sl evaluniq.sl program_small.sl
  evalby_demo.sl --build build/evalby_demo_slc && ./build/evalby_demo_slc | tail -1` prints the same `Some`.

### 2.5 Run-time cost against the fuelled evaluator

`evalby_deep.sl` runs the fuelled `eval` once, then `eval-by` with the derivation it returned, on the deep
program of section 4. Times are the program's own cumulative user time from the prelude's `Measure` request.

- `[RAN]` `$M base.sl term.sl core.sl eval2.sl neg.sl eval3.sl evalby.sl program_deep.sl doubling.sl
  evalby_deep.sl -- 3001 8192`: `program built at user-ns 5842000`, `fuelled eval done at user-ns 291381000`,
  `eval-by done at user-ns 457610000`, then `fuelled: (VCon 12 (VCon 11))` and `eval-by: (VCon 12 (VCon 11))`.
  So 286 ms fuelled, 166 ms `eval-by`.
- `[RAN]` `(ulimit -s unlimited; ./build/evalby2_ref 200000 524288)`, three runs: fuelled 459, 408, and
  370 ms; `eval-by` 42, 57, and 45 ms. `./build/evalby2_slc`, three runs: fuelled 514, 431, and 444 ms;
  `eval-by` 59, 40, and 55 ms.
- `[INFERENCE]` The compiled gap is mostly stack depth: `eval-by` calls a body in tail position
  (`(tail $ eval-by e2 body2 outs r)`, `evalby.sl` lines 50 and 57), while mini's `eval` must rewrap every
  result and so nests one frame per object-level call. Rests on reading both sources; a profile would check
  it.

## 3. What Pattern 1 is, and what could supply the derivation

- `[INFERENCE]` The use in 2.4 is circular as a way to compute: the derivation comes from a fuelled run that
  already produced the values. The point of the pattern is the theorem in `eval-by`'s type.
- `[QUOTE scratchpad/handoff.md:22]` "the owner asked whether a theorem could take as a hypothesis that the
  spec is sound and prove that the compiler terminates". That is the previous session's account of the
  owner's question, not the owner's words. `[INFERENCE]` For the evaluator, `eval-by` is that
  theorem with hypothesis "this run of the spec has a derivation", and the checker's termination rule is its
  proof.
- What could supply the derivation in a real compiler, `[INFERENCE]` throughout:
  1. A run that has halted, by any means: a fuelled attempt (2.4), the doubling loop of section 4, or a
     driver-looped machine. Each yields the derivation only after computing the answer, so none removes the
     need for the loop.
  2. A proof that accepted compile-time code halts. The handoff records that no such theorem is expected:
     `[QUOTE scratchpad/handoff.md:19]` "No `no_false` theorem is expected: for consistency, proving properties
     about the language runs into a diagonalization argument."
  3. An assumption. DESIGN.md has no form that postulates a proof: `[RAN]` `grep -n -i
     "postulate\|assume\|axiom\|trust" DESIGN.md` finds only Axiom K (§9), the three termination axioms (§18),
     `gensym-unique` (§65), `placed-slot` and `placed-eq` (§66), and two unrelated uses of the words. So a
     top-level program cannot call `eval-by` on input it has not already run.
- `[INFERENCE]` The same shape would state the owner's whole-compiler version: a `compile-by` taking the
  source at `many` and an erased derivation of the spec's elaboration judgment, returning the judgment's
  output with `is`. mini already writes elaboration as such a judgment `[QUOTE mini/README.md:39-40]`
  "`elab.sl` — `ElabProgram`, `ElabExpr`, `ElabStmt`, `ElabTerm` and their helpers, each judgment total with
  an `Ok` or `Err` outcome". I did not build this.

## 4. Pattern 2: fuel that is never observed

### 4.1 The change to the evaluator

`eval2.sl` is `mini/eval.sl` with one failure constructor per outcome type carrying a reason
`[READ proto/S1b/eval2.sl:33-50]`:

```scheme
(def-adts $ (Why : -> Type)
  enum
  (many Stuck : -> (Why))
  (many OutOfFuel : -> (Why)))
...
(many EvalFail : (erased (Env) env) (erased (Core) c) (many (Why) w) -> (Evaled env c))
```

I used one constructor with a reason, not the two constructors the task named as an example, so that each
of the 13 propagation sites stays one branch, `((EvalFail _ _ w) (EvalFail _ _ w))`. `[RAN]` `diff` of the
two function blocks: 36 of 74 lines differ, all by this renaming. `[RAN]` `probes/p2_small.sl` prints
`(MkPair _ _ (MkEvaled ...) $ MkPair _ _ (EvalFail _ _ $ OutOfFuel) $ EvalFail _ _ $ Stuck)` for fuel 1000,
fuel 5, and an unbound variable.

### 4.2 The driver

`[READ proto/S1b/doubling.sl:50-65]` Each attempt is one call of a total function; the step returns
`Continue` with a fresh continuation that calls `attempt` with `(nat-add fuel fuel)`:

```scheme
(def-fns PA $ (many attempt : (unique (World) w at vacant-slot)
    (many (Fn evaluator (many (Nat) fuel) (many (Core) c) -> (many (Outcome) o)) ev) (many (Core) c) (many (Nat) fuel) ->
    (unique (World) w2 at w) (unique (Program P) p))
  (let ((many outcome)) (ev fuel c))
  ...
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
    (attempt v ev c (nat-add fuel fuel)))
  (values w2 (Continue P again)))
```

This is the pattern of `tests/io_echo.sl` `[READ tests/io_echo.sl:17-26]`, and the loop is the driver's:
`[QUOTE DESIGN.md:1993-1994]` (§42) "It never recurses, so an unbounded interaction is the driver's loop over
total functions." `ev` is `by-eval` (over `eval2.sl`'s `eval`) or `by-run` (over section 6's `run`).

### 4.3 Demonstrations

(a) The `tests/mini_eval.sl` program. `F="base.sl term.sl core.sl eval2.sl neg.sl eval3.sl"`.

- `[RAN]` `$M $F program_small.sl doubling.sl doubling_small.sl 2>/dev/null | grep -v MkUnit` prints
  `fuel 1: out of fuel`, `fuel 2: out of fuel`, `fuel 4: out of fuel`, `fuel 8: out of fuel`,
  `fuel 16: values (VCon 12 (VCon 11))`. Exit 0. The same lines with `-- 1 1` (evaluator `run`), under
  `$M --no-extern`, and under `$SLC --interpret`.
- `[RAN]` A stuck program, `(CCall (CVar 99) (Nil _))`: `fuel 1: out of fuel`, `fuel 2: stuck`, exit 1.

(b) A deep program. `deep-program n` builds the Core for `Succ^n Zero` and two mutually recursive functions
that walk it and answer its parity `[READ proto/S1b/program_deep.sl:1-38]`.

- `[RAN]` `$M $F program_deep.sl doubling.sl doubling_deep.sl -- 3000 1` prints 13 `out of fuel` lines for
  fuel 1 to 4096, then `fuel 8192: values (VCon 11)`.
- `[RAN]` The least sufficient fuel for n = 3000 is 6007 with either evaluator: `./build/dbl2_ref 3000 6006`
  and `./build/dbl2_ref 3000 6006 0 1` print `fuel 6006: out of fuel`; with `6007` both print
  `fuel 6007: values (VCon 11)`.

### 4.4 Timings, deep program

`timing.sh RUNS -- cmd` reports the least and the median wall time. The machine was shared with other
agents, so the spread is wide.

Reference interpreter, n = 3000, 9 runs each. `[RAN]` `./timing.sh 9 -- $M $F program_deep.sl doubling.sl
doubling_deep.sl -- N START 0 EV`:

| | `eval` (EV 0) min / median | `run` (EV 1) min / median |
|---|---|---|
| elaboration only (`-- 0 16`) | 0.641 s / 0.663 s | |
| doubling from 1 | 1.012 s / 1.092 s | 1.115 s / 1.184 s |
| single run at fuel 8192 | 0.905 s / 0.995 s | 0.963 s / 1.045 s |
| single run at fuel 6007 | 0.944 s / 1.029 s | 0.989 s / 1.042 s |

`[INFERENCE]` Net of elaboration, doubling costs about 1.2 to 1.5 times a single run here (least times:
`eval` 0.37 s against 0.26 to 0.30 s; `run` 0.47 s against 0.32 to 0.35 s). The program's own clock agrees: `[RAN]` an earlier run printed
`fuel 4096 done at user-ns 93445000` and `fuel 8192 done at user-ns 429269000`, so 13 failed attempts took
88 ms and the successful one 336 ms.

Compiled, n = 200000, 9 runs each, with `ulimit -s unlimited`. `[RAN]` builds: `$M $F program_deep.sl
doubling.sl doubling_deep.sl --build build/dbl2_ref` and the same with `$SLC ... --build build/dbl2_slc`;
both succeed. `[RAN]` `./timing.sh 9 -- ./build/B 200000 START 0 EV`:

| binary, evaluator | doubling from 1 | single at 524288 | single at 400007 |
|---|---|---|---|
| `dbl2_ref`, `eval` | 0.466 s / 0.604 s | 0.530 s / 0.619 s | 0.530 s / 0.594 s |
| `dbl2_ref`, `run` | 0.587 s / 0.658 s | 0.445 s / 0.620 s | 0.511 s / 0.671 s |
| `dbl2_slc`, `eval` | 0.428 s / 0.608 s | 0.400 s / 0.417 s | 0.390 s / 0.401 s |
| `dbl2_slc`, `run` | 0.419 s / 0.468 s | 0.417 s / 0.460 s | 0.408 s / 0.496 s |

`[INFERENCE]` The difference between doubling and a single run is inside the noise at this size. `[RAN]`
`./build/dbl2_ref 200000 1` printed `fuel 262144 done at user-ns 55856000` and `fuel 524288 done at user-ns
469986000`: the 19 failed attempts are 12% of the total.

Two observations from these runs:

- `[RAN]` With the default 8 MB stack (`ulimit -s` prints `8192`), `./build/dbl2_ref 200000 1` prints
  `fuel 131072: out of fuel` and then `Fatal error: exception Stack overflow`; `./build/dbl2_slc 200000 1`
  does the same. A recursive evaluator's depth is the host's stack. §31 allows this: `[QUOTE DESIGN.md:1319-1321]`
  "The semantics is that of a machine with unlimited stack and heap. A real run may crash where the host
  cannot represent what is asked of it. A crash produces no value, never a different one."
- `[RAN]` `(ulimit -s unlimited; ./build/dbl2_ref 1000000 1)` succeeds at fuel 2097152 after 18.8 s of user
  time (`fuel 2097152 done at user-ns 18816270000`), against 0.72 s for n = 200000 (`fuel 524288 done at
  user-ns 717028000`): superlinear. `[UNKNOWN]` why; I did not profile it.

## 5. What a failed attempt can waste

- `[READ mini/eval.sl:52-125]` Every recursive call in `eval`, `eval-list`, and `eval-stmt` passes the same
  `f`, the predecessor of the fuel it was given. So the fuel bounds how deeply the evaluator's calls nest,
  not how many there are.
- `[INFERENCE]` A failed attempt therefore runs everything the successful run does up to the first place
  the nesting exceeds the fuel. Its cost is bounded by the whole run's cost W, not by its fuel. With D the
  depth needed, doubling from 1 makes about log2 D failed attempts, so the total is at most about
  (1 + log2 D) W, and that bound is reached when the work before the deepest point is most of W.
- A program built to show it: `wide-program k n` first calls a function that calls itself twice at each
  of k levels, then runs the deep walk `[READ proto/S1b/program_deep.sl:14-37]`. `[INFERENCE]` That is about
  2^(k+1) calls at a depth near 3k; the trace below fits, fuel 128 being the first to finish the wide part
  for k = 20.
  `[RAN]` `./build/dbl2_ref 20000 1 20 2>&1 >/dev/null` (k = 20, n = 20000), cumulative user time per attempt:
  `fuel 64 done at user-ns 747000`, `fuel 128 done at user-ns 230027000`, `fuel 256 done at user-ns
  453222000`, then about 190 to 255 ms more for each of fuel 512 to 32768, ending `fuel 65536 done at user-ns
  2053926000`. Ten attempts, the last of them the successful one, each run the wide part in full.
  `[RAN]` `./timing.sh 5 -- ./build/dbl2_ref 20000 1 20`: min 1.909 s, median 1.991 s; `... 20000 65536 20`
  (single run): min 0.208 s, median 0.224 s. With `dbl2_slc`: 1.928 s / 1.940 s against 0.204 s / 0.229 s.
  That is about 9 times (8.5 to 9.5 across the four pairs of figures).
- `[INFERENCE]` A fuel that counts steps would behave differently: an attempt with budget s does at most s
  steps, so the attempts cost at most 1 + 2 + 4 + ... up to the first budget that suffices, under 4 W in
  total whatever the program's shape. It rests on the standard geometric sum; I did not build such an
  evaluator. In Sleight it would have to return the fuel left over with a proof that it is no more than the
  fuel given, and turn that into the `Subterm` proof each later call needs; the prelude has the lemma for
  that step `[READ lib/prelude.sl:284]` (`lt-subterm`). The relations of section 6 would index a step count in
  place of a depth.

## 6. "The answer never depends on the fuel"

### 6.1 Why it cannot be stated about `mini/eval.sl`'s `eval`

- `[QUOTE DESIGN.md:419-421]` (§9) "The elaborated form of a type never contains a function call, and
  elaborating a type calls none: the only code that runs is a macro's expansion (§62)."
- `[INFERENCE]` So "`(eval m env c)` equals `(eval n env c)`" is not a type. A property of what a function
  returns can only be read off the evidence in its return type. mini's `eval` returns evidence on success
  (`MkEvaled` holds an `Eval` derivation) and none on failure `[READ mini/eval.sl:38-42]`.
- `[INFERENCE]` Two parts follow from the existing types alone. Soundness: every answer carries its
  derivation. Agreement of successes: by `eval-unique` (2.3 c), any two attempts that both return values, at
  any two fuels, return the same values. What is missing is that failure cannot follow success: fuel n
  succeeds, and a larger fuel answers `OutOfFuel` or `Stuck`. To exclude that, failure must carry evidence.

### 6.2 The statement, as Sleight types

The relations `[READ proto/S1b/eval3.sl:1-95]`:

- `EvalD n env c vs`, `EvalListD`, `EvalStmtD`: mini's three relations with a size. Each rule concludes at
  `(Succ f)` from premises at `f`, as the function passes `f` to every call.
- `FailEv n env c w`, `FailListEv`, `FailStmtEv`: why an attempt with fuel `n` failed with reason `w`. One
  rule for fuel zero in each judgment, one per place a sub-evaluation's failure is passed on, and one per
  place the function finds a wrong shape. 25 rules in all.
- `Ran n env c`: `Done` with values and an `EvalD n`, or `Failed` with a reason and a `FailEv n`.

`run`, `run-list`, and `run-stmt` are mini's three functions returning those
`[READ proto/S1b/eval3.sl:97-168]`:

```scheme
run : (subterm many (Nat) fuel) (many (Env) env) (many (Core) c) -> (many (Ran fuel env c) r)
```

The theorem `[READ proto/S1b/fuelthm.sl:145-153]`, `[READ proto/S1b/sized.sl:33, 82-94]`:

```scheme
enough-fuel : (erased (Nat) k) (erased (Nat) n) (erased (Nat) m) (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs)
              (erased (Why) w) (erased (Plus k n m) pl) (erased (EvalD n env c vs) d) (erased (FailEv m env c w) e)
              -> (erased (False) x)

fuel-is-unobservable : (erased (Nat) k) (erased (Nat) n) (erased (Nat) m) (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs)
              (erased (Plus k n m) pl) (erased (EvalD n env c vs) d) (many (Ran m env c) r) -> (many vs is v)

eval-sized : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (subterm erased (Eval env c vs) d)
              -> (erased (Nat) n) (erased (EvalD n env c vs) s)

(many MkFuelBound : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (erased (Nat) n)
   (erased (Fn fuel-bound-lvl (erased (Nat) k) (erased (Nat) m) (erased (Plus k n m) pl) (many (Ran m env c) r) -> (many vs is v)) all)
   -> (FuelBound env c vs))

fuel-bound : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (erased (Eval env c vs) d) -> (erased (FuelBound env c vs) b)
```

`(Plus k n m)` is mini's `k + n = m` `[READ mini/base.sl:72-75]`. In words: if the spec's run of `c` in `env`
has a derivation with values `vs`, there is an `n` such that whatever `run` returns at any fuel `k + n` is
`Done` with exactly `vs`. `fuel-is-unobservable` is a `many` function with no failure branch: `[RAN]` its
extracted code is `(match (of_any v69942_r : yes t12_n4) with | K12_0 { f0 = v69986_vs2 } -> v69986_vs2)`.

### 6.3 It is proved

- `[RAN]` `$M --goal proved base.sl term.sl core.sl eval2.sl evaluniq.sl neg.sl eval3.sl fuelthm.sl sized.sl
  fuelgoal.sl fuelqed.sl` prints ``fuelgoal.sl:7:1: note: proved `(goal erased (FuelUnobservable))` ``,
  ``fuelqed.sl:1:1: note: by this `qed` ``, and `--goal proved: PASS`. The same command with `$SLC` prints
  the same. `FuelUnobservable` packages a level with a function of `fuel-bound`'s type
  `[READ proto/S1b/fuelgoal.sl:1-7]`.
- `[RAN]` The whole set with warnings on, `$M --warn-unused base.sl term.sl core.sl eval2.sl evaluniq.sl
  neg.sl eval3.sl fuelthm.sl sized.sl`: accepted, no warning.
- `[RAN]` Used at run time (`fuel_demo.sl`): run at fuel `n`; on `Done`, run again at `k + n` and take the
  values through `fuel-is-unobservable`. Prints `(MkPair _ _ (Some _ $ Cons _ (VCon 12 $ Cons _ (VCon 11 $
  Nil _) $ Nil _) $ Nil _) $ None _)` for first fuels 16 and 8.
- Checks that the checker is not accepting these vacuously, each a one-line sabotage that is refused
  `[RAN]` `probes/run_probes.sh`:
  - `d1` (out-of-fuel stage, one uniqueness step removed): ``argument 6, `e`, of `no-oof`: type mismatch:
    expected `(FailEv f env2 body3 (OutOfFuel))`, got `(FailEv f env23 body3 (OutOfFuel))` ``.
  - `d2` (the same proof claimed for `Stuck` while `Stuck` still had no evidence): `` `e` : `(FailEv (Succ
    __1) env (CVar __2) (Stuck))` is not refuted: it may be headed by `FStuck` ``.
  - `d3` (no weakening before `no-oof`): ``expected `(EvalD m env c vs)`, got `(EvalD n env c vs)` ``.
  - `d4` (final proof, one uniqueness step removed): `` `ns` : `(NotSingle vs3)` is not refuted: it may be
    headed by `NSNil` ``.

### 6.4 What the proof consists of, and its size

Non-blank lines, `[RAN]` `grep -cv '^[[:space:]]*$' FILE`, each file ending in one `(MkUnit)` line:

| file | lines | content |
|---|---|---|
| `evaluniq.sl` | 85 | the eight functionality lemmas of 2.3 (c) |
| `neg.sl` | 117 | negative evidence `NoEnv`, `NoBind`, `NoBranch`, `BadShape`; the deciding functions that return it (36 lines, replacing 20 of mini's); the five lemmas by which it excludes the positive evidence |
| `eval3.sl` | 166 | `EvalD` (31), `FailEv` (49), `Ran` (13), and `run` (72) |
| `fuelthm.sl` | 146 | sized to unsized (`evald-forget`), size plus one (`evald-step`), `evald-weaken`, `no-fail` and its two siblings (77), `enough-fuel`, `fuel-is-unobservable` |
| `sized.sl` | 86 | `plus-comm` and friends, `eval-sized` and its two siblings, `fuel-bound` |

600 lines, of which the evaluator and its deciding functions are 108. The out-of-fuel half alone,
with `Stuck` left unverified, was 360 lines `[RAN]` (`probes/eval3_oofonly.sl` 151, `probes/fuelthm_oofonly.sl`
126, `probes/sized_oofonly.sl` 86, less three `(MkUnit)` lines), plus `evaluniq.sl`.

Every one of these files compiled without an error the first time it was run. `[RAN]` (the session's
compile log; the probes above are the evidence that errors are reported when present.)

### 6.5 What it does not cover

- It is a theorem about `run` in `eval3.sl`, not about `eval` in `mini/eval.sl`. `run` uses `env-dec2`,
  `bind-all2`, `branch-dec2`, and `shape-dec`, which return negative evidence, where `eval` uses mini's
  functions and `else` branches `[READ proto/S1b/eval3.sl:97-168]`, `[READ mini/eval.sl:52-125]`.
  `[INFERENCE]` The two have the same control structure, and by 6.1 their agreement cannot be stated.
  `[RAN]` The doubling driver gave the same lines with either (4.3), and the same least fuel (4.3 b).
- `[INFERENCE]` It says nothing about a program with no derivation. In particular it does not prove that a
  program stuck at fuel n is stuck, and not out of fuel, at every larger fuel. The route I see needs
  `FailEv ... (Stuck)` to survive adding fuel (one case per rule) and then that two failures at one fuel have
  one reason, which compares each pair of failure rules for the same form: I count 44 pairs for mini. Not
  attempted.
- `[INFERENCE]` That the driver's loop reaches a fuel of the form `k + n` is arithmetic outside Sleight:
  the loop is the driver's (4.2), so no Sleight type speaks of it halting.

## 7. Comparison

| | Pattern 1: erased derivation | Pattern 2: fuel doubling |
|---|---|---|
| Runs on arbitrary input today | No: no caller can supply the derivation (section 3) | Yes `[RAN]` 4.3 |
| Fuel in the evaluator | None `[RAN]` 2.3 (d) | One `Nat`, decreasing on every call |
| Failure outcomes in the evaluator | None | `Stuck` and `OutOfFuel` at every call site |
| Each answer agrees with the spec | By the return `(many vs is r)` | By the `Eval` derivation in `MkEvaled`, plus `eval-unique` |
| "If the spec's run halts, the answer is computed" | The function's type; 73 lines, no lemma `[RAN]` 2.2 | `FuelUnobservable`; about 600 lines, and the evaluator must return failure evidence `[RAN]` 6.3, 6.4 |
| Stuck programs | Have no derivation, so are outside the function's domain | Reported as `stuck`; not proved stable under more fuel (6.5) |
| Run-time cost | Faster than the fuelled evaluator on the program measured `[RAN]` 2.5 | A single attempt costs what mini's `eval` costs; retries add 0 to 50% on the deep program and multiply the cost by about 9 on the wide one `[RAN]` 4.4, 5 |
| Unbounded loop | None | The `Program` driver's |

What each still trusts, `[INFERENCE]` throughout:

- Both trust the checker and erasure, as any Sleight program does. Pattern 1 leans on them harder: its
  compiled code has no case for a shape the derivation excludes (2.3 d), and the same holds for
  `fuel-is-unobservable` (6.2).
- Pattern 1 trusts whoever supplies the derivation. Inside Sleight that can only be a proof.
- Pattern 2 trusts the driver to keep applying continuations, and nothing else that Pattern 1 does not.
- Neither removes the host's stack limit (4.4).

`[INFERENCE]` The two are not alternatives for the same job. Pattern 1 states and proves the conditional the
owner asked about. Pattern 2 is a way to run. A design could use both: run by doubling, and state
correctness in Pattern 1's form. What that combination leaves unproved is exactly 6.3's theorem, that the
fuelled loop finds the answer whenever one exists.

One fact about the implementations that bears on "minimize fuel": `[QUOTE MANUAL.md:154]` "`--eval-fuel n`
bounds the evaluator." and `[QUOTE MANUAL.md:161-162]` "Without the flag the reference has none and slc's is
1000000000." slc's own evaluator is fuelled today.

## 8. Checker obstacles

There were few. Each with its message and the way round it. Item 1 reproduces with `$M base.sl term.sl
core.sl probes/t1_envby.sl`; items 2 to 5 are this session's history and the files no longer show them.

1. `[RAN]` First draft of `env-by` used `((ENil) (match erased p _))`. Accepted, with ``warning: a non-erased
   `match` with no non-absurd branch compiles to a runtime `absurd`; mark the enclosing branch or function
   `absurd` instead`` (WARNINGS.md item 6). Fix: `(absurd (ENil) p)`, which §51 allows
   `[QUOTE DESIGN.md:2362-2363]` "any other expression `e`. It is elaborated as an erased value and accepted
   when `(match erased e _)` with no branches would refute."
2. `[RAN]` A driver step at level `PA` calling `attempt`, also at `PA`: ``error: same-level call to `attempt`
   decreases no subterm argument`` with ``hint: a call to a strictly lower level needs no decreasing
   argument; consider defining `attempt` at a lower level, or `begin` at a higher one``. Fix: make the caller
   the `def-unique` at level `P`.
3. `[RAN]` A helper defined after `(def-lvl P)` and called from a `P`-level function: ``error: `(level-of
   user-ns-line)` was not in scope when level `P` was minted``. Fix: define it before the levels.
4. `[RAN]` A function returning a `Request` at `many`, passed to `world-do`: ``error: the return `q` of
   `user-ns-line`, declared `many`, used at unique``. Fix: do the `world-do` inside the helper (`stamp`).
5. `[RAN]` `sized.sl` first draft: three ``warning: lopsided `match`; flatten it with a `let-match` on ...``,
   and one unused-binder warning on a placeholder since removed. Fix: `let-match` with branches.
6. Not a checker obstacle: a cleanup command `rm -f build/*` was refused by the session's safety check, so
   seven stale binaries remain in `proto/S1b/build/` (`deep_ref`, `deep_slc`, `dbl_ref`, `dbl_slc`,
   `evalby_ref`, `evalby_slc`, `evalby_demo_slc`). `dbl2_*` and `evalby2_*` are current.

Things that worked without trouble and might not have, all `[RAN]` by the files being accepted: mutual
recursion across three functions on erased derivations of three different types; a nested `def-fns` at an
earlier level inside a later function (`fuel-bound`); an `erased` function whose signature has `many`
entries, stored in an erased field; `_` for erased arguments throughout; absurd functions calling
themselves and each other.

## 9. Things I am least sure of

1. That acceptance by the two checkers means the proofs are sound. I tested that sabotaged proofs are
   refused (the `c` and `d` probes), not that the checkers have no hole. The reference and slc both accept
   the final files (`$SLC --warn-unused` over the whole set exits 0), and DESIGN.md §21 allows the recursion
   used.
2. The timings. The machine was shared, runs varied by 30%, and the compiled deep runs are dominated by
   stack depth. The figure of about 9 times in section 5 is far outside the noise; the 1.0 to 1.5 of 4.4 is not
   precise.
3. The claim that `run` and mini's `eval` are the same evaluator. I compared their text, and their outputs
   on the programs of section 4, no more.
4. The step-counting analysis in section 5, and the count of 44 pairs in 6.5: reasoned, not built.
5. What extracted code does on a shape its proof excludes. I read the OCaml; I did not provoke it.
6. Whether `FuelBound`, with the bound existentially packed beside a function field at a fixed level, is
   the form the owner would want the theorem in. It type-checks and both checkers pass the goal; other
   packagings are possible.
7. Section 3's list of what could supply a derivation is my reasoning from DESIGN.md's lack of a
   postulate form. I searched DESIGN.md for four words; a mechanism under another name would escape that
   search.
