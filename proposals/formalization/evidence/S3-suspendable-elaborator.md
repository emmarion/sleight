# S3. Which suspendable elaborator does Sleight's type system permit, and at what cost?

One agent's prototypes and reading, for the lead. Nothing here is an owner decision.

**Conventions.** Every factual claim carries one tag: `[QUOTE file:line]`, `[RAN]`, `[READ file:lines]`,
`[INFERENCE]`, or `[UNKNOWN]`. Unless a command says otherwise it was run in

    /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S3/

(called `S3/` below), with `M=/home/user/sleight/_build/default/bin/main.exe` and
`S=/home/user/sleight/_build/release/slc`. `S3/RUN.md` lists the commands; `S3/results-demo.txt`,
`S3/results-built.txt`, `S3/results-interp.txt`, and `S3/obstacles/OUTPUT.txt` are the transcripts the
`[RAN]` claims below were copied from, and `S3/slc-counts.py` produces the counts of section 8.1. The repository was at commit `4bb81cc` when I started; commits
adding only `proposals/formalization/` arrived while I worked, and
`git diff --stat 4bb81cc HEAD -- DESIGN.md lib self tests std mini MANUAL.md TUTORIAL.md CLAUDE.md`
printed nothing `[RAN]`. The code files contain no comments.

---

## 1. Findings, most decision-relevant first

1. **All three designs are accepted and run with no fuel.** Replay (R), continuation-passing (M), and an
   explicit-stack machine (D) each type-check under the reference and under slc, run as a `Program`, and
   print the same certified result on every tree I tried. `[RAN]` section 3.
2. **The task's expected obstacle for M does not arise; a different one does.** A continuation defined at a
   level *above* the walk calls the walk as an ordinary lower-level call, with no `subterm` proof.
   `[RAN]` section 5.1. What the level rules do force: one fixed continuation level minted at the top
   level, and `bind` as a *constructor* that the driver interprets, not as a function. A function `bind`
   is refused at one level, and a `bind` that mints a level per call produces continuations the driver
   cannot call. `[RAN]` section 5.3.
3. **M and D take the elaborator's recursion out of the termination checker.** A walk whose continuation
   re-enters itself on the same tree is accepted and loops under the driver; the same recursion written
   directly is refused. `[RAN]` section 5.5. R keeps every pass an ordinary `def-fns` function that the
   checker accepts as terminating. `[RAN]` section 3.
4. **R's replay cost is real and quadratic in the requests per replay unit.** Toy, native code: 8,000
   requests in one unit take 0.70 s, 16,000 take 5.5 s, 32,000 take 39.5 s; M and D take under 0.01 s for
   8,000. Reference interpreter, 1,000 requests: R 5.8 s against 0.5 s for M and D. `[RAN]` section 7.
5. **Two measures remove most of that cost, and both are implemented.** (a) A checkpoint per unit, kept by
   the driver as a typed frame stack (`rc.sl`): 200,000 units in 0.08 s. (b) An inline quantum of machine
   steps tried before a request is issued (`rq.sl`): with the quantum above the run length, one pass and
   no replay. `[RAN]` sections 4.5, 4.6, 7.
6. **A top-level form is too coarse a replay unit for slc's own source.** slc's elaborator main block is
   one `def-fns` form of 3,076 lines holding 125 textual `and`/`or` macro calls. `[RAN]` section 8.1. With
   one replay per macro call and no quantum, that form would be elaborated about 126 times.
   `[INFERENCE]` from the count and from finding 4.
7. **R gives the "total under H" statement as a checked function.** With the log behind an oracle
   parameter, `total-under-h` (5 lines) type-checks: an oracle that can never fail to answer makes the
   same `elab` return `Done` with its derivation. `[RAN]` section 4.4. This proves that one pass is total
   under H; it does not prove that the replay loop ends (section 4.8).
8. **R needs a depth budget wherever it elaborates syntax that came from the log** (macro output), because
   that syntax is not a subterm. `[RAN]` section 4.7. DESIGN.md already bounds expansions:
   `[QUOTE DESIGN.md:2752-2753, §62]` "At most 10000 expansions run in one run, every file on the command
   line included." M and D need no budget there. `[RAN]` section 4.7.
9. **Sizes on the toy are close.** Before the shared driver boilerplate: R 53 lines, D 45, M 70, R with
   checkpoints 70. `[RAN]` section 6. I do not expect these ratios to hold at 8,500 lines (section 8).
10. **Cost of each for slc, in one line each** (`[INFERENCE]`, section 8): R touches the 7 call sites
    where slc starts a run or an expansion, plus a driver; M and D rewrite the 95 functions and 358
    internal call sites of the main block and give up checked termination for them.

---

## 2. The toy

`[READ S3/common.sl:1-67]` The toy has:

- a syntax tree `Tree`: `TLeaf n`, `TGen`, `TNode l r`, `TRun start`, `TIf c th el`;
- "evaluation": the Collatz iteration on a `Nat`, as a relation `Step n n2`, a total function
  `step : (many (Nat) n) -> (many (Stepped n) r)` answering `Halted`, `Stuck`, or `Next` with an erased
  `Step` proof, and the request "run `s` to 1 and count the steps", specified by `Runs s a`;
- "elaboration": a walk that threads a counter `g` (standing for the gensym counter) and returns a sum.
  `TGen` returns the counter and increments it; `TRun s` returns the answer to the request; `TIf c th el`
  elaborates `c`, then `th` if its value is zero and `el` otherwise, so which child is elaborated next
  depends on a computed value.

The specification never mentions a log, a continuation, or a stack:

```scheme
(def-adts $ (Elab : ((Tree) t) ((Nat) g) ((Nat) v) ((Nat) g2) -> Type)
  enum
  (many ELeaf : (erased (Nat) n g) -> (Elab (TLeaf n) g n g))
  (many EGen : (erased (Nat) g) -> (Elab (TGen) g g (Succ g)))
  (many ENode : (erased (Tree) l r) (erased (Nat) g a g1 b g2 c) (erased (Elab l g a g1) pa) (erased (Elab r g1 b g2) pb) (erased (Add a b c) pc) -> (Elab (TNode l r) g c g2))
  (many ERun : (erased (Nat) s a g) (erased (Runs s a) p) -> (Elab (TRun s) g a g))
  (many EIfZero : (erased (Tree) c th el) (erased (Nat) g g1 b g2) (erased (Elab c g (Zero) g1) pc) (erased (Elab th g1 b g2) pt) -> (Elab (TIf c th el) g b g2))
  (many EIfSucc : (erased (Tree) c th el) (erased (Nat) g m g1 b g2) (erased (Elab c g (Succ m) g1) pc) (erased (Elab el g1 b g2) pe) -> (Elab (TIf c th el) g b g2)))
```

The machine's state carries the erased partial derivation `Reach s n k` ("`s` reaches `n` in `k` steps"),
and the erased lemma `reach-runs` turns it into the big-step `Runs s k` when the machine halts:

```scheme
((Runs : ((Nat) s) ((Nat) a) -> Type)
  enum
  (many RunsHalt : -> (Runs (Succ (Zero)) (Zero)))
  (many RunsStep : (erased (Nat) s s2 a) (erased (Step s s2) st) (erased (Runs s2 a) r) -> (Runs s (Succ a))))
((Reach : ((Nat) s) ((Nat) n) ((Nat) k) -> Type)
  enum
  (many ReachRefl : (erased (Nat) s) -> (Reach s s (Zero)))
  (many ReachStep : (erased (Nat) s n n2 k) (erased (Reach s n k) r) (erased (Step n n2) st) -> (Reach s n2 (Succ k))))
```

Every design ends in the same function, which takes the certificate as an erased parameter
`[READ S3/trees.sl:31-32]`:

```scheme
(def-fns _ $ (many report : (erased (Tree) t) (many (Nat) v g2) (many (String) what) (many (Nat) count steps) (erased (Elab t (Zero) v g2) _certificate) -> (many (String) s))
```

Every program is a `Program` whose `Continue` wraps one total step, in the shape of
`/home/user/sleight/tests/io_echo.sl` `[READ tests/io_echo.sl:11-26]`. The basis in the specification:
`[QUOTE DESIGN.md:1993-1994, §42]` "It never recurses, so an unbounded interaction is the driver's loop
over total functions." Each machine step is one driver step `[READ S3/r.sl:12-36]`. No function in `r0.sl`, `r-elab.sl`, `r.sl`,
`ro.sl`, `rc.sl`, `m.sl`, `mu.sl`, or `d.sl` takes a counter that bounds work `[READ those files in full]`.
`rq.sl` has one counter, a quantum, discussed in section 4.6.

---

## 3. What runs

`[RAN]` `./demo.sh > results-demo.txt 2>&1` runs each of the eight programs on four trees and on a tree
whose request cannot be answered, through `$M common.sl trees.sl <design>.sl -- <args>`, with `r-elab.sl`
before `r.sl` and `rc.sl`. The 32 runs on the four trees exit 0 with no warning; the 8 runs with `-- stuck`
(a `(TRun (Zero))`, which the machine cannot step) print `machine stuck` and exit 2. On the demo tree
(5 requests, taking 0, 8, 8, 16, and 111 steps):

```
r0, r, ro:  value 138 counter 3 elab-calls 6 driver-steps 154
rq:         value 138 counter 3 elab-calls 2 driver-steps 14
rc:         value 138 counter 3 elab-calls 9 driver-steps 168
m:          value 138 counter 3 asks 5 driver-steps 182
mu:         notes 8 value 138 counter 3 asks 5 driver-steps 182
d:          value 138 counter 3 asks 5 driver-steps 178
```

`[RAN]` The same eight programs give the same values on `chain 10 6` (value 80, counter 1),
`balanced 4 7` (256, 0), and `chain 10 0` (55, 11); see `S3/results-demo.txt`.

`[RAN]` The step counts: `./bin/r chain 1 1`, `chain 1 6`, `chain 1 7`, and `chain 1 27` print values 0,
8, 16, and 111.

`[RAN]` Other runners, all eight programs, on the final files: `$M --no-extern common.sl trees.sl <design>.sl`
and `$S --interpret common.sl trees.sl <design>.sl` print the same lines as above on the demo tree, and
`$S common.sl trees.sl <design>.sl --build bin-slc/<design>` followed by `./bin-slc/<design> chain 1000 6`
prints `value 8000 counter 1` for each (the `bin-slc` directory is since removed). So both implementations
accept every design.

`[RAN]` Under `$M --warn-unused`, none of the design files warns.

---

## 4. Design R: replay with a log

### 4.1 Key types `[READ S3/r-elab.sl:1-8, S3/r.sl:1-10]`

```scheme
(def-adts $ (Entry : -> Type)
  enum
  (many MkEntry : (many (Nat) s a) (erased (Runs s a) p) -> (Entry)))

(def-adts $ (Outcome : ((Tree) t) ((Nat) g) -> Type)
  enum
  (many Done : (erased (Tree) t) (erased (Nat) g) (many (Nat) v g2) (many (List (Entry)) rest used) (erased (Elab t g v g2) p) -> (Outcome t g))
  (many Need : (erased (Tree) t) (erased (Nat) g) (many (Nat) s) (many (List (Entry)) used) -> (Outcome t g)))

(def-fns _ $ (many elab : (subterm many (Tree) t) (many (Nat) g) (many (List (Entry)) log used) -> (many (Outcome t g) r)) ...)

(def-adts $ (RState : -> Type)
  enum
  (many Elaborating : (many (List (Entry)) rev-log) -> (RState))
  (many Running : (many (List (Entry)) used) (many (Nat) s n k) (erased (Reach s n k) r) -> (RState)))
```

`elab` is structurally recursive on the tree and is 23 lines `[READ S3/r-elab.sl:10-32]`. The request site:

```scheme
((TRun s)
  (let-match many log (Cons _ e rest) ((Nil _) (Need _ _ s used)))
  (let-match many e (MkEntry s2 a p))
  (let-match many (nat-eq s2 s) (Equal _ _ _) ((Unequal _ _ _ _ _) (Need _ _ s used)))
  (Done _ _ a g rest (Cons _ e used) (ERun s a g p)))
```

### 4.2 Refinement (i): entries carry proofs, and a mismatch is just `Need`

- `[RAN]` `$M common.sl trees.sl r-elab.sl checks/log-mismatch.sl` evaluates `elab` on `(TRun 6)` with a
  log whose only entry answers request 1, and on `(TNode (TRun one) (TRun 6))` with the same log. Output:
  `(MkPair _ _ (Need _ _ 6 $ Nil _) $ Need _ _ 6 $ Cons _ (MkEntry 1 0 _) $ Nil _)`.
- `[RAN]` `checks/log-match.sl`: `(Done _ _ 0 1 (Nil _) (Cons _ (MkEntry 1 0 _) $ Nil _) _)`.
- `[RAN]` `checks/forged-entry.sl`, which writes `(MkEntry 6 (Zero) (RunsHalt))`, is refused: "argument
  3, `p`, of `MkEntry`: type mismatch: expected `(Runs 6 (Zero))`, got `(Runs (Succ (Zero)) (Zero))`".
- `[READ /home/user/sleight/lib/prelude.sl:83-88, 216-217]` The check is the prelude's `nat-eq`, which
  returns `(EqDec (Nat) Lt a b)`; its `Equal` constructor has type `(EqDec T R a a)`, so matching it forces
  the logged request and the current one equal, and the logged proof then has the type the rule needs.
  There is no separate `Eq` value.
- `[READ S3/r-elab.sl:10-32]` `elab` has no branch for "the log is wrong". `Need` returns the entries
  consumed so far (`used`, newest first); the driver's next log is that list plus the new entry
  `[READ S3/r.sl:14-22]`, so a stale tail is dropped without a check.
- `[INFERENCE]` Soundness therefore needs nothing of the log: any list of `Entry` values, in any order,
  yields either `Need` or a `Done` whose derivation type-checked. It rests on the types above.

### 4.3 Refinement (ii): `Done` carries the derivation

`[READ S3/r-elab.sl:5-8, S3/r.sl:6-10, S3/trees.sl:31-32]` `Done` holds `(erased (Elab t g v g2) p)`; the
driver's `Finished` holds `(erased (Elab t (Zero) v g2) p)`; `report` demands it. `[RAN]` section 3: it
type-checks and runs.

### 4.4 The log behind an oracle, and a theorem under H (`ro.sl`)

`[READ S3/ro.sl:1-41]` `elab` takes the oracle as a function value at a level `O` minted before it, and
is generic in the oracle's state `S` and in the type `F` of what it returns when it has no answer:

```scheme
(def-adts $ (Asked : (Type S) (Type F) ((Nat) s) -> Type)
  enum
  (many Answer : (erased Type S F) (erased (Nat) s) (many S st) (many (Nat) a) (erased (Runs s a) p) -> (Asked S F s))
  (many Unanswered : (erased Type S F) (erased (Nat) s) (many F f) -> (Asked S F s)))

(def-fns _ $ (many elab : (erased Type S F) (many (Fn O (many S st) (many (Nat) s) -> (many (Asked S F s) r)) ask)
    (subterm many (Tree) t) (many (Nat) g) (many S st) -> (many (Outcome S F t g) r)) ...)

(def-fns _ $ (erased total-under-h : (many (Fn O (many (Unit) u) (many (Nat) s) -> (many (Asked (Unit) (False) s) r)) h) (many (Tree) t) (many (Nat) g) ->
    (erased (Nat) v g2) (erased (Elab t g v g2) p))
  (match erased (elab _ _ h t g (MkUnit)) _
    ((Done _ _ _ _ v g2 _ p) (values v g2 p))
    (absurd (Need _ _ _ _ f) f)))
```

- `[RAN]` `$M common.sl trees.sl ro.sl` prints `value 138 counter 3 elab-calls 6 driver-steps 154`, so
  `total-under-h` type-checks beside the running program.
- `[RAN]` With `(False)` replaced by `(Unit)` in the hypothesis (`obstacles/total-needs-false.sl`), the
  checker refuses: "`f` : `(Unit)` is not refuted: it may be headed by `MkUnit`". So the theorem is
  checked, not vacuously accepted.
- `[INFERENCE]` Reading: `h` is the hypothesis "every request has an answer with a `Runs` derivation";
  under it the very function the replay driver calls returns a result with its `Elab` derivation. This
  is the toy form of the handoff's result (ii). The hypothesis here covers every request, not only those
  this tree makes; relativizing it is not attempted.
- `[READ S3/ro.sl:13-35, 55-60]` The elaborator's code no longer mentions the log at all; the log is one
  oracle (`from-log`, 6 lines).

### 4.5 Checkpoints (`rc.sl`)

`[READ S3/rc.sl:1-40]` The driver walks the right spine of the tree itself and keeps it as a typed frame
stack; each left child is a replay unit with its own log, elaborated by the unchanged `elab` of
`r-elab.sl`; a finished unit is committed with its derivation:

```scheme
(def-adts $ (Spine : ((Tree) t) ((Nat) g) ((Tree) top) -> Type)
  enum
  (many SpTop : (erased (Tree) top) -> (Spine top (Zero) top))
  (many SpLeft : (erased (Tree) l top) (erased (Nat) g) (many (Tree) r) (many (Spine (TNode l r) g top) up) -> (Spine l g top))
  (many SpRight : (erased (Tree) l r top) (erased (Nat) g g1) (many (Nat) a) (erased (Elab l g a g1) pa) (many (Spine (TNode l r) g top) up) -> (Spine r g1 top)))
```

- `[RAN]` `$M common.sl trees.sl r-elab.sl rc.sl -- chain 10 6` prints
  `value 80 counter 1 elab-calls 21 driver-steps 143`: two passes per unit, where `r.sl` makes 11 passes
  over the whole tree.
- `[RAN]` `./bin/rc chain 200000 6` takes 0.08 s (section 7); the whole-tree certificate
  `(Elab top (Zero) v g2)` is still produced, through the frames' types.
- `[INFERENCE]` This is design D applied to the spine only and design R inside each unit. In the real
  compiler the spine would be: the list of top-level forms, the bodies of a `def-fns` block, and the
  statements of a body.

### 4.6 An inline quantum (`rq.sl`)

The idea is from a session's draft, not from me: `[QUOTE /home/user/sleight/proposals/formalization/04-fuel.md:89-91]`
"The inline quantum of F2 matters for W-replay: if the elaborator first tries up to some number of machine
steps on the spot, only long runs ever cause a replay." `[READ S3/rq.sl:44-70]` In `rq.sl` this is confined to the
oracle: it consults the log, otherwise runs up to `quantum` steps by recursion on the counter, and
otherwise answers `Unanswered` with the machine state reached, from which the driver continues:

```scheme
(def-adts $ (Pending : -> Type)
  enum
  (many Paused : (many (List (Entry)) used) (many (Nat) s n k) (erased (Reach s n k) r) -> (Pending))
  (many Crash : -> (Pending)))
```

- `[RAN]` `for q in 0 5 10 20 200; do $M common.sl trees.sl rq.sl -- demo 0 0 $q; done` prints elab-calls
  6, 5, 3, 2, and 1, each with `value 138 counter 3`. `elab` and `total-under-h` are textually those of
  `ro.sl`.
- `[RAN]` `./bin/rq chain 8000 6 0` takes 1.01 s (8,001 passes); `./bin/rq chain 8000 6 100` takes 0.00 s
  (1 pass).
- `[READ S3/rq.sl:57-63]` The counter is `(subterm many (Nat) quantum)` on `try-run`. Running out changes
  no result: it returns the state for the driver to continue. Whether the owner counts that as fuel is
  the owner's call; the base designs do not have it.

### 4.7 Checker obstacles met in R

| what | exact message `[RAN]`, command in `S3/obstacles/run.sh` | workaround |
|---|---|---|
| Recursing into syntax taken from the log (`obstacles/x-r-no-budget.sl`) | "`out` is not a strict subterm of `(XExpand s)`" | a depth budget as a leading `subterm` parameter (`obstacles/x-r-budget.sl`, accepted, prints `(XDone 3 $ Nil _)`) |
| An oracle at level `O` calling a helper defined later with `_` (`obstacles/oracle-helper-level.sl`) | "`(level-of try-run)` was not in scope when level `O` was minted" | mint the helper's level before `O` (`rq.sl` lines 1-2) |
| A plain non-decreasing self-call (`obstacles/r-loop-rejected.sl`) | "same-level call to `spin` decreases no subterm argument" | none wanted: this is the check R keeps |

`[RAN]` The only refusals I met while writing the R files were level-order ones in `rq.sl`: the one in the
table and the same message for a helper called from `start` at level `P`. `r0.sl`, the first `r.sl` (which
then held `elab` too), `ro.sl`, and `rc.sl` type-checked as first written, with warnings about shadowed
names and lopsided matches that I then removed.

`[INFERENCE]` On the budget: §62's bound is on the count of expansions, and nesting depth cannot exceed
the count, so a depth budget of 10,000 runs out only where §62 already makes the program an error. That
makes it a rule of the language, not an implementation limit; whether to read it that way is the owner's
call. An alternative I did not build: store each expansion back into the tree the elaborator is given, so
that descending into it is structural.

### 4.8 What must be true for replay to be correct

- **Soundness needs nothing.** `[INFERENCE]` from 4.2 and 4.3: the certificate is built from proofs that
  were checked against the request actually made.
- **No effect inside a pass.** `[READ S3/r-elab.sl:10]` `elab` takes no `World`.
  `[QUOTE DESIGN.md:1976-1977, §42]` "which the driver applies to the world, the one value of `World`,
  which only the driver supplies". `[INFERENCE]` So a pass cannot perform a request twice; effects belong
  to the machine run, which the driver performs once.
- **Machine runs are not replayed.** `[RAN]` `./bin/r chain 10 6`, `./bin/r chain 100 6`, and
  `./bin/r chain 1000 6` report `driver-steps` 101, 1001, and 10001, that is `10k + 1`: 9 machine turns per
  request, each once, plus `k + 1` passes.
- **Messages.** `[READ S3/r.sl:14-17]` a pass that ends in `Need` returns nothing but the request; only
  the final pass's result is reported. `[INFERENCE]` Accumulated warnings would be handled the same way,
  or committed at checkpoints.
- **Progress needs determinism, and I did not prove it.** `[INFERENCE]` The loop ends only if each pass
  consumes the previous log entirely and then asks the next request. That holds if `elab` is a function
  of its arguments. One place where a Sleight function's answer may vary:
  `[QUOTE DESIGN.md:3044-3046, §67]` "`ENone` proves nothing, so an implementation may always answer it,
  and which one a call answers may differ between runs." An elaborator whose requests depended on
  `slot-eq` could ask different requests on different passes; the types would keep the result sound, and
  the loop could fail to progress.
- **Termination of the loop under H is not a theorem here.** `[INFERENCE]` `total-under-h` covers one
  pass with a complete oracle. That the replay loop reaches such a pass needs a further argument: either
  a completeness lemma about `elab` (if the specification derives a result through answers `T`, then
  `elab` on log `T` returns `Done`), or a bound on the number of requests. For the toy the bound is the
  number of `TRun` nodes; for the real elaborator I do not know a simple one. `[UNKNOWN]`
- **The request-equality check must be affordable.** In the toy it is `nat-eq`. `[INFERENCE]` A real
  request is a piece of code plus the store it runs in, or a macro plus its arguments plus the scope its
  primitives read (`[QUOTE DESIGN.md:2954, §65]` "`resolve` looks a name up in the scope at the macro
  call"). Comparing whole stores or scopes per replayed request would be expensive. Whether the store
  can be taken from the previous log entry instead of compared is `[UNKNOWN]`.

---

## 5. Design M: requests with continuations

### 5.1 The answer to the task's level questions

`[READ S3/m.sl:5-45]` Two levels are minted at the top level, `W` then `K`. The walk is at `W`. Every
continuation is a nested `def-fns K`, so its type is `(Fn K ...)`, and inside it the call `(walk r g1)`
is a call to a strictly lower level.

- `[RAN]` section 3: it type-checks under both implementations with the bare call, no `(subterm p)` and
  no written `(predates p)`.
- The rules that allow it: `[QUOTE DESIGN.md:688-690, §17]` "A function may call a function of a
  strictly lower level. It may call a function of its own level only under the `Subterm` rules of §19."
  `[QUOTE DESIGN.md:798-801, §19]` "A call to a function of a strictly lower level carries `(predates p)`
  immediately after the callee. `p` is a `Predates` relating the callee's level, read from its `Fn` or
  `UniqueFn` type, to the current level (§5)." `[QUOTE DESIGN.md:2408-2409, §54]` "`def-fns`: one or more
  mutually recursive functions at one level, written on the form," and `[QUOTE DESIGN.md:2411-2412, §54]`
  "It may be nested in a body."
- DESIGN.md is silent on any relation between a nested function's level and its enclosing function's:
  `grep -n -i "nested\|nest " DESIGN.md` gives nine lines (469, 1082, 1261, 1625, 1840, 2303, 2341, 2412,
  2773), none of which restricts the level `[RAN]`.
- The walk never calls a continuation; only the driver's step does, from a level above `K`
  `[READ S3/m.sl:64-77]`. This is the shape of `Program` itself: a function below level `L` returns a
  `(Program L)` whose continuation is at `L` `[READ tests/io_echo.sl:17-22]`.

The case the task described, a continuation at the walk's own level, is refused exactly as predicted:

- `[RAN]` `obstacles/cont-same-level.sl`: "same-level call to `walk` decreases no subterm argument" with
  the hint "a call to a strictly lower level needs no decreasing argument; consider defining `walk` at a
  lower level, or `after-l` at a higher one".
- `[RAN]` `obstacles/cont-same-level-proof.sl`, which passes `(subterm p)` with
  `p` from `(prove-subterm r t)`: "argument 1, `t`, of `walk` is its `subterm` parameter 1, but the
  enclosing function `after-l` has none".

### 5.2 Key types `[READ S3/m.sl:1-12, 47-62]`

```scheme
(def-adts $ (Walked : ((Tree) t) ((Nat) g) -> Type)
  enum
  (many MkWalked : (erased (Tree) t) (erased (Nat) g) (many (Nat) v g2) (erased (Elab t g v g2) p) -> (Walked t g)))

(def-lvl W)
(def-lvl K)

(def-adts $ (ElabM : (Type A) -> Type)
  enum
  (many Ret : (erased Type A) (many A a) -> (ElabM A))
  (many Ask : (erased Type A) (many (Nat) s) (many (Fn K (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM A) next)) k) -> (ElabM A))
  (many Bind : (erased Type A X) (many (ElabM X) m) (many (Fn K (many X x) -> (many (ElabM A) next)) f) -> (ElabM A)))

(def-adts $ (Stack : (Type X) (Type A) -> Type)
  enum
  (many KNil : (erased Type A) -> (Stack A A))
  (many KCons : (erased Type X Y A) (many (Fn K (many X x) -> (many (ElabM Y) next)) f) (many (Stack Y A) rest) -> (Stack X A)))
```

The level `K` is a reference to the top-level entry, not an index of `ElabM`. One arm of the walk
`[READ S3/m.sl:18-26]`:

```scheme
((TNode l r)
  (def-fns K $ (many after-l : (many (Walked l g) wl) -> (many (ElabM (Walked t g)) next))
    (let-match many wl (MkWalked _ _ a g1 pa))
    (def-fns K $ (many after-r : (many (Walked r g1) wr) -> (many (ElabM (Walked t g)) next))
      (let-match many wr (MkWalked _ _ b g2 pb))
      (let ((many c) (erased pc)) (add a b))
      (Ret _ (MkWalked _ _ c g2 (ENode l r g a g1 b g2 c pa pb pc))))
    (Bind _ _ (walk r g1) after-r))
  (Bind _ _ (notail $ walk l g) after-l))
```

The continuations capture erased proofs (`pa`) and the answer's proof arrives as an erased parameter of
the `Ask` continuation. The driver's step pushes on `Bind`, pops on `Ret`, starts the machine on `Ask`,
and calls the continuation when the machine halts `[READ S3/m.sl:64-77]`.

### 5.3 The obstacle catalogue for M

All `[RAN]`; commands are in `S3/obstacles/run.sh`, transcript in `S3/obstacles/OUTPUT.txt`.

| attempt | exact message | consequence |
|---|---|---|
| `bind` as a function at a level above `K`, whose new continuation at `K` calls the stored continuation (`bind-above.sl`) | "same-level call to `k` decreases no subterm argument" | a `K` continuation cannot call another `K` continuation |
| the same, with the new continuation calling `bind` (`bind-above2.sl`) | "`B` was not in scope when level `K` was minted" | a `K` continuation cannot call a function above `K` |
| `bind` at a level below `K` calling `f` (`bind-below.sl`) | "`K` was not in scope when level `W` was minted" | a function below `K` cannot run a continuation |
| new continuation at a higher level `K2` (`bind-higher-k2.sl`) | "argument 3, `k`, of `Ask`: type mismatch: expected `(Fn K (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM A) next))`, got `(Fn K2 (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM A) next))`" | then the level must be an index or existential |
| continuation at a level minted inside the walk, `def-fns _` (`cont-local-level.sl`) | "argument 2, `f`, of `CBind`: type mismatch: expected `(Fn K (many (Nat) v) -> (many (CM) next))`, got `(Fn (level-of after-l) (many (Nat) a) -> (many (CM) next))`" | the continuation level must be the fixed top-level one |
| existential level: `bind-ask` mints `L2` in its body, and its continuation at `L2` calls both the stored continuation and `bind-ask` (`exists-level-bind.sl`) | accepted | such a `bind` can be written |
| the driver calling a continuation from that package (`exists-level-driver.sl`) | "`L` was not in scope when level `D` was minted" | but nothing at a fixed level can run its result |
| packaging a bound `(Predates (Level) L2 TOP)` with it (`exists-level-bound.sl`) | "`L2` was not in scope when level `TOP` was minted" | and a body-minted level cannot be put below an older one |
| `_` for a continuation's parameter and return types (`closure-sig-infer.sl`) | "cannot infer `__?1` in `__?1`" | every continuation's signature is written out |
| a `def-fns` continuation capturing a `unique` binder (`cont-captures-unique.sl`) | "`def-fns` cannot capture `b` at unique" | unique state is passed as a parameter (5.4) |

So, to the task's questions:

- *Can `bind` build a continuation that calls both the stored continuation and `bind`'s own recursion?*
  Only at a level minted inside `bind`'s body, and then the driver cannot call the result. The rule
  behind the last two refusals: `[QUOTE DESIGN.md:733-736, §18]` "`L` must be an entry created by
  `def-lvl`, or a `let` binder forwarding from one (§19). `x` must have an introduction order (§5)
  earlier than `L`'s."
- *Does the continuation's level have to appear in `ElabM`'s type, and grow with each `bind`?* With a
  function `bind`, yes, and it then needs the existential package of
  `[QUOTE DESIGN.md:3134, §71]` "an existential, such as a function with its level, is packaged by an
  ADT (§21)", which the driver cannot open usefully. With `Bind` as a constructor, no: one level, no
  index, no growth.
- *Can the walk call itself from inside a continuation it creates?* Yes, as a lower-level call (5.1).

### 5.4 Unique state (`mu.sl`)

`[READ S3/mu.sl:5-11, 16-22, 24-60, 79-93]` `mu.sl` threads a `unique` box, updated in place through its cell,
through the walk, every continuation, the driver's step, and the `def-unique` step closures. The
continuations take and return it:

```scheme
(many Bind : (erased Type A X) (many (ElabM X) m)
   (many (Fn K (unique (Box) b) (many X x) -> (unique (Box) b2 at b) (many (ElabM A) next)) f) -> (ElabM A))
```

`[RAN]` `$M common.sl trees.sl mu.sl` prints `notes 8 value 138 counter 3 asks 5 driver-steps 182`.
Continuations as `UniqueFn` values that capture the unique state were not attempted.

### 5.5 Termination is no longer checked

- `[RAN]` `$M common.sl trees.sl obstacles/m-unchecked-loop.sl` is accepted and prints
  `still looping after 100000 driver steps; giving up` (the cut-off is in that file's driver, to end the
  demonstration). Its walk is
  `(def-fns W $ (many spin : (subterm many (Tree) t) -> (many (LoopM) m)) (def-fns K $ (many again : (many (Nat) x) -> (many (LoopM) next)) (spin t)) (LBind (LRet 0) again))`.
- `[RAN]` The direct form `(notail $ spin t)` in `obstacles/r-loop-rejected.sl` is refused: "same-level
  call to `spin` decreases no subterm argument".
- `[RAN]` For the same reason M needs no budget for syntax that is not a subterm:
  `obstacles/x-m-no-budget.sl`, whose continuation calls `(xwalk out)` on a tree it was handed, is
  accepted.
- `[INFERENCE]` So with M, "the elaborator terminates whenever its runs do" is a claim about the driver
  loop that the type checker does not make. It could be recovered by indexing `ElabM` with a decreasing
  measure and writing an erased interpreter of `ElabM` by recursion on that index; I did not try, and I
  expect the measure to be as intricate as the one slc's elaborator carries today (section 8.1).

### 5.6 Other costs seen on the toy

- `[READ S3/m.sl:8-12]` `ElabM A` has one result type, so a function's several returns travel as one
  packaged value (`Walked`).
- `[RAN]` The walk is 32 lines (`m.sl` 14-45) against `elab`'s 23, and needs 28 more lines for the
  interpreter of `ElabM` (section 6).
- `[RAN]` Per node with no requests, in native code, M is about 9 times slower than the direct walk
  (section 7), because every `Bind` and `Ret` is a driver step.

---

## 6. Design D: the elaborator as an explicit-stack machine

Implemented, since it was short. `[READ S3/d.sl:1-48]`

```scheme
(def-adts $ (Frames : ((Tree) t) ((Nat) g) ((Tree) top) -> Type)
  enum
  (many FTop : (erased (Tree) top) -> (Frames top (Zero) top))
  (many FNodeL : (erased (Tree) l top) (erased (Nat) g) (many (Tree) r) (many (Frames (TNode l r) g top) up) -> (Frames l g top))
  (many FNodeR : (erased (Tree) l r top) (erased (Nat) g g1) (many (Nat) a) (erased (Elab l g a g1) pa) (many (Frames (TNode l r) g top) up) -> (Frames r g1 top))
  (many FIfC : (erased (Tree) c top) (erased (Nat) g) (many (Tree) th el) (many (Frames (TIf c th el) g top) up) -> (Frames c g top))
  (many FIfZero : (erased (Tree) c th el top) (erased (Nat) g g1) (erased (Elab c g (Zero) g1) pc) (many (Frames (TIf c th el) g top) up) -> (Frames th g1 top))
  (many FIfSucc : (erased (Tree) c th el top) (erased (Nat) g m g1) (erased (Elab c g (Succ m) g1) pc) (many (Frames (TIf c th el) g top) up) -> (Frames el g1 top)))

(def-adts $ (DState : ((Tree) top) -> Type)
  enum
  (many Down : (erased (Tree) top) (many (Tree) t) (many (Nat) g) (many (Frames t g top) fs) -> (DState top))
  (many Up : (erased (Tree) t top) (erased (Nat) g) (many (Nat) v g2) (erased (Elab t g v g2) p) (many (Frames t g top) fs) -> (DState top))
  (many Running : (erased (Tree) top) (many (Nat) s n k g) (erased (Reach s n k) r) (many (Frames (TRun s) g top) fs) -> (DState top)))
```

`[READ S3/d.sl:1-8, S3/m.sl:18-45]` A frame holds what M's corresponding continuation captures, including
the erased partial derivation. `dturn` is one non-recursive total function of 27 lines `[READ S3/d.sl:22-48]`. `[RAN]` It type-checked as first
written and prints `value 138 counter 3 asks 5 driver-steps 178`.

`[RAN]` Sizes, non-blank lines and bytes, of everything before each design's `Program` driver boilerplate
(`drive`, `start`, `Continue`; 18 to 23 lines per design), counted by a Python snippet that cuts each file at
`(def-lvl drive-lvl)`:

| | r0 | r | ro | rq | rc | m | mu | d |
|---|---|---|---|---|---|---|---|---|
| lines | 43 | 53 | 76 | 92 | 70 | 70 | 84 | 45 |
| bytes | 1995 | 3255 | 4571 | 5577 | 4752 | 3984 | 5231 | 3198 |

By part: R's elaborator (`Entry`, `Outcome`, `elab`) is 30 lines and 1,912 bytes, and its driver states
and step 20 lines; M's elaborator (`Walked`, levels, `ElabM`, `walk`) is 42 lines and 2,379 bytes, and its
interpreter of `ElabM` 28 lines; D's frames, states, and step together are 45 lines and 3,198 bytes. The
shared `common.sl` and `trees.sl` are 58 and 27 lines.

So on the toy, D is no larger than R. `[INFERENCE]` I do not expect that to carry over. A toy node has at
most two pending sub-elaborations and three live values. A frame must list every live variable with its
type and every erased index those types mention; `FIfSucc` already needs seven erased indices for one
proof. The largest function of slc's elaborator has 422 lines and is called from 39 sites in its block (8.1). M gets the
same capture from the language's closures and writes only the continuation's parameter.

D has the same unchecked termination as M `[INFERENCE]`: `dturn` is total, and nothing in its type says
that the loop over it ends. D's state is first-order data, which a measure or a simulation relation can
be stated about; M's is closures.

---

## 7. Measurements

The machine is shared with other agents, so these are noisy. Start values are 6 throughout, 8 machine
steps per request (section 3), so the machine's own work is small next to the elaborator's. The timing
transcripts were taken just before I added the `stuck` shape to the argument parser in `trees.sl`; the
elaborators and drivers have not changed since.

`[RAN]` `./time-built.sh` (reference `--build`, best of 3, seconds; `rq` at its default quantum 100):

```
built: chain k 6 (k requests); best of 3, seconds
k          r0        r       ro       rq       rc        m       mu        d
10       0.00     0.00     0.00     0.00     0.00     0.00     0.00     0.00
100      0.00     0.00     0.00     0.00     0.00     0.00     0.00     0.00
1000     0.00     0.00     0.00     0.00     0.00     0.00     0.00     0.00
2000     0.02     0.02     0.03     0.00     0.00     0.00     0.00     0.00
4000     0.07     0.11     0.15     0.00     0.00     0.00     0.00     0.00
8000     0.37     0.70     0.95     0.00     0.00     0.00     0.00     0.00
built: chain k 6, linear designs only          (columns: rc m mu d)
50000       0.02     0.02     0.02     0.01
100000      0.04     0.05     0.05     0.04
200000      0.08     0.10     0.11     0.07
```

`[RAN]` `./bin/r chain 16000 6`: 5.53 s, `elab-calls 16001`. `./bin/r chain 32000 6`: 39.54 s,
`elab-calls 32001`. `elab` is called `k + 1` times in every R run without checkpoints or quantum
(11, 101, 1001, ...).

`[RAN]` `./time-interp.sh` (one run each, seconds, about 0.43 s and 0.29 s of start-up included):

```
reference interpreter (main.exe): chain k 6
k            r0        r       ro       rq       rc        m       mu        d
0          0.43     0.45     0.43     0.47     0.45     0.44     0.42     0.44
10         0.42     0.42     0.46     0.47     0.44     0.44     0.43     0.45
100        0.47     0.53     0.52     0.44     0.48     0.45     0.46     0.46
1000       4.56     5.77     7.04     0.50     0.54     0.56     0.54     0.52
slc --interpret: chain k 6
k            r0        r       ro       rq       rc        m       mu        d
0          0.28     0.30     0.30     0.28     0.32     0.29     0.29     0.31
10         0.30     0.30     0.30     0.29     0.31     0.31     0.34     0.30
100        0.30     0.30     0.33     0.31     0.30     0.30     0.35     0.30
1000       1.74     2.35     2.92     0.33     0.35     0.32     0.35     0.32
```

`[RAN]` Earlier single runs of `r.sl` under `$M`, before the file was split: k = 2000 took 26.95 s and
k = 4000 took 107.41 s, four times per doubling.

`[RAN]` The cost of trampolining, on a tree with no requests and 33,554,431 nodes
(`./bin/<design> balanced 24 0`): r0 0.13 s, r 0.12 s, ro 0.11 s, rq 0.13 s, rc 0.13 s, m 1.07 s,
mu 1.17 s, d 0.90 s. M reports 67,108,861 driver steps. That is roughly 4 ns per node for the direct
walk and 27 to 35 ns for M and D. `[INFERENCE]` A real elaborator does far more than 30 ns of work per
call, so this overhead should not matter there.

`[RAN]` Certification costs R about a third on the interpreter (r0 4.56 s, r 5.77 s at k = 1000) and
about a factor of two in native code at k = 8000 (0.37 s against 0.70 s). `[INFERENCE]` The difference
is the `nat-eq` check and the `used` list, since erased arguments do not run.

---

## 8. Scaling to the real elaborator

### 8.1 Facts about slc that bear on this

- `[RAN]` `wc -l self/elab.sl self/elab-main.sl`: 5,139 and 3,398 lines, 8,537 together.
- `[RAN]` `python3 slc-counts.py` (in `S3/`; it reads `self/elab-main.sl`). The main block is one
  `def-fns` form, lines 158 to 3233, 3,076 lines; no line from 159 to 3234 starts in column 0
  (`awk 'NR>=159 && NR<=3234 && /^\(/' self/elab-main.sl | wc -l` prints 0). The script finds 95
  functions, at least 78 of which thread `ElabWorld` (those whose header line names it), and 358 call
  sites of the block's own functions inside the block (a regular-expression count of `(name ` and
  `$ name `; `elab-expr-demand` 39, `elab-term` 24, `elab-prim-call` 21, `eval` 20).
- `[RAN]` The same script counts 125 occurrences of `(and `, `$ and `, `(or `, `$ or ` in that block,
  37 of them in `elab-expr-demand` (422 lines), spread over 33 functions. These are textual counts; I did
  not check that each is a macro call. `and` and `or` are macros `[READ std/macro.sl:176-188]`.
- `[RAN]` `grep -o` counts in `self/elab-main.sl`, `self/interp.sl`, `self/main.sl`, `self/elab.sl`:
  `run-code` 5 call sites, `env-expand` 1, `native-batch` 1.
- `[READ self/eval.sl:1492-1494]` `ElabWorld` is a newtype over the placed `World`:
  `(many MkElabWorld : (erased (World) w) (unique (Placed vacant-slot (World) w) p) -> (ElabWorld))`.
  `[READ self/elab-main.sl:509-2101, signatures only]` The block's functions take
  `(unique (ElabWorld) ew)` and `(many (Env) env)` and return `(many (Env) r)`. `[INFERENCE]` So the
  elaborator's own state is a persistent `many` value, and the one unique thing it threads is the world
  it needs because runs and expansions happen inside it.
- `[QUOTE self/README.md:273-281]` (a session's description, not verified beyond the signatures)
  "Because the elaborator's main block also holds the interpreter and macro expansion, a call within it
  is ordered first by the expansion budget, then by an erased count of callbacks from the interpreter
  into the elaborator, which the interpreter learns from the macro run's `Performer` when a primitive
  calls back, then by an erased hop count that each function fixes in its type as a `hop-` constant and
  that drops on every call from the elaborator towards the interpreter; after those three, each function
  decreases as described above, the interpreter by its fuel."
- `[QUOTE self/README.md:298-300]` "**Errors are values.** The language has no exceptions, so an
  elaboration error is recorded in the environment and elaboration goes on; every error is reported at
  the end and no OCaml is written."
- `[RAN]` slc compiling its own 15 source files takes 5.38 s wall
  (`/usr/bin/time ./_build/release/slc $SL > /dev/null` with `SL` from `self/bootstrap.sh` line 23).
- Where requests arise, by the specification: `[QUOTE DESIGN.md:1179-1180, §27]` "Such a form runs as
  soon as it has been elaborated, before the code after it is checked"; `[QUOTE DESIGN.md:1185-1186, §27]`
  "This nests: the forms inside a form run before it does"; and a macro call can stand almost anywhere:
  `[QUOTE DESIGN.md:2743-2746, §62]` "A call also expands in a telescope, among the binders of a `let`
  and as one of its entries, as a branch of a `match` or `let-match`, as a constructor of a `def-adts`,
  and as an argument or an entry of a `values`, where its forms take its place."

### 8.2 Design R at that scale `[INFERENCE]` throughout, resting on 8.1 and sections 4 and 7

- **What changes.** The 7 call sites that start a run, an expansion, or a native batch become oracle
  calls; the evaluator leaves the block and becomes the driver's machine; the driver holds the world.
  Every other function keeps its direct style and its checked termination. The measures that exist only
  because the interpreter shares the block (callbacks, hops, the interpreter's fuel) could go; the
  expansion budget stays (4.7).
- **Propagating "no answer".** In the toy every call site matches on `Need`. slc already records errors
  in `Env` and goes on, so a missing answer could be recorded the same way, with the pass finishing in
  that mode and the driver discarding it. If functions are to return derivations, each already returns a
  sum of accepted and rejected, and "no answer" is a third case of it.
- **State.** `Env` is persistent, so a checkpoint is a value the driver keeps. The gensym counter and
  minted entries change during macro runs (`[QUOTE DESIGN.md:2882-2884, §65]` "The macro world is the
  elaborator's program store: the run-position entries with their values and facts, the literal table,
  the gensym counter and the expansion count."), so they belong in the logged answer.
- **Effects.** `read-file` and `native-compute` happen in the driver while it serves a request, once.
  Messages are part of a pass's result and are reported from the committing pass.
- **Replay cost.** Without measures, the main block alone would be elaborated about 126 times; if that
  block is a large share of the 5.4 s self-compile, that is minutes. With a quantum, a short expansion
  such as `and` costs no replay, and only runs longer than the quantum do. With checkpoints at top-level
  forms, at the bodies of a `def-fns`, and at the statements of a body, a replay repeats one statement.
  The spine frames needed for those checkpoints are a small instance of design D (4.5).
- **What is new work.** A decidable equality on requests with a proof (4.8); the completeness or
  bounding argument if loop termination under H is to be a theorem (4.8).

### 8.3 Design M at that scale `[INFERENCE]` throughout

- **What changes.** Every function from which a request can be reached returns an `ElabM`, and every
  call site of such a function becomes a `Bind` with a nested `def-fns K` whose signature is written by
  hand (5.3). Macro calls can stand in telescopes, branches, and arguments (8.1), so I expect that to be
  most of the 95 functions and most of the 358 call sites. Each distinct return telescope needs a
  packaging ADT, since the block's functions return several values, some depending on earlier ones.
- **State.** Because `Env` is `many`, continuations can capture it, and the world can stay with the
  driver, so the parameter-passing of `mu.sl` may not even be needed.
- **What is lost.** Checked termination for everything reached through a continuation (5.5). What is
  gained: no replay, no request-equality check, no expansion budget needed for termination, and a host
  stack that need not grow with elaboration depth (in `m.sl` only the direct call on a first child uses
  it).
- **Levels.** One level `K` minted before the block; the driver's step above it. No obstacle found.

### 8.4 Design D at that scale `[INFERENCE]` throughout

The same rewrite as M with every continuation replaced by a frame constructor that declares its captured
variables and their indices, and every function cut at each call site into separate arms of one step
function. I expect this to be the largest of the three in code, and the most mechanical. Its advantages
over M are that states are first-order data (they can be compared, printed, and related to the
specification by an explicit invariant) and that no closure signature has to mention a level.

### 8.5 Options, as I see them `[INFERENCE]`

1. **R with a quantum and spine checkpoints** (`rq.sl` and `rc.sl` combined; not built as one file). It
   keeps the elaborator a set of checked total functions, changes the fewest lines of slc, keeps
   `total-under-h`, and confines replay to runs longer than the quantum within one statement. It leaves a
   counter in the compiler (the quantum), a budget on expansion depth, and an unproved loop-termination
   argument.
2. **M** if no replay and no counter at all matter more than checked termination of the elaborator and
   the size of the rewrite.
3. **D** if the elaborator's state should be data that theorems are stated about.

Questions this raises for the owner: whether a quantum counts as fuel; whether the expansion budget may
be justified by §62's limit; whether an elaborator whose recursion is trampolined through the driver,
and so unchecked, is acceptable given that `Program` itself works that way.

---

## 9. Things I am least sure of

1. **Whether the acceptance of M is intended.** DESIGN.md does not restrict a nested function's level
   (5.1), both implementations accept it, and `tests/io_echo.sl` relies on the same shape, but that test
   was written by a session. If the owner means nested functions to sit at or below something, M changes.
2. **Loop termination for R.** I argue it needs determinism plus a completeness or counting lemma (4.8).
   I did not write that lemma even for the toy, so I cannot say how hard it is.
3. **The request-equality check at real scale** (4.8). The toy's request is one `Nat`.
4. **`rq.sl`'s progress** when a logged request and an inline one coincide or interleave oddly. Its
   results are certified whatever happens; I tested only the demo tree and chains.
5. **The slc counts** (8.1) are regular-expression counts over text. The 125 may include occurrences that
   are not macro calls, and the 358 includes the 20 calls of `eval`, which would leave the block.
6. **How much of slc's 5.4 s is the main block.** I did not profile, so "minutes" in 8.2 is a rough
   product, not a measurement.
7. **Whether macro-world primitives ever need a function that can itself issue a request.** If a callback
   from a running macro had to elaborate syntax containing a macro call, the driver would need nested
   activations in every design. I read §65 as not requiring that, but did not check slc's `apply-answer`.
8. **Extrapolated sizes** for M and D (8.3, 8.4) are judgment, not measurement. The toy says D is the
   smallest; I argue the opposite at scale.
9. **Timings** were taken on a shared machine, single runs for the interpreters, and the toy's per-node
   work is far below a real elaborator's, so the ratios, not the absolute numbers, are what to keep.
10. **Not attempted:** `UniqueFn` continuations that capture unique state; a measure-indexed `ElabM`;
    batching several elaborator steps per driver step in M or D; storing expansions back into the syntax
    tree for R; relativizing H to the requests one tree makes.
