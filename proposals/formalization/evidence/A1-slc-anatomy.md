# A1 — Anatomy of `slc` (`self/`): where it uses fuel (Q1), and how ready it is to carry proofs (Q2)

Analysis only. Nothing inside `/home/user/sleight` was modified, created, or deleted by this agent; apart
from this report, every file it wrote is under
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A1/`.

**Tags.** Every factual claim carries one of `[QUOTE file:line]`, `[RAN]`, `[READ file:lines]`,
`[INFERENCE]`, `[UNKNOWN]`, as the common brief defines them. A tag at the head of a bullet or table row
covers the whole bullet or row. File paths without a directory are in `/home/user/sleight/self/`.

**Shorthand in commands.** `SLC=/home/user/sleight/_build/release/slc`,
`REF=/home/user/sleight/_build/default/bin/main.exe`,
`P=/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A1`.
Unless stated, commands ran with `cd $P`.

**Whose words are whose.** `DESIGN.md` is the owner's specification. Everything else quoted here
(`self/*.sl`, `self/README.md`, `MANUAL.md`, code comments, the reference in `lib/`) was written by earlier
sessions. Where this report says "slc does X" or "the reference does X", that is a statement about an
implementation, never about the language.

---

## 0. Coverage: what was read and what was only searched

- [READ] In full: `DESIGN.md` (lines 1–3156, all sections), `MANUAL.md`, `CLAUDE.md`, the handoff,
  `self/README.md`, `main.sl`, `interp.sl`, `heap.sl`, `eval.sl`.
- [READ] In part: `elab-main.sl` lines 1–1010, 1086–1268, 1392–1421, 1495–1553, 1663–1684, 1822–2046,
  2101–2275, 2556–2564, 2693–2730, 2797–2887, 3066–3190, 3235–3398, plus the header line of each of the
  95 functions of its main block; `core.sl` lines 1–135, 355–431, 475–483, 536–655, 876–1015, 1341–1378,
  1521–1665, 1856–1864, 1902–1920, 2216–2693, 2800–2834, 3744–3893, 4096–4133; `elab.sl` lines 808–835,
  955–1000, 1236–1250, 1960–2032, 2864–2896, 4655–4796; `emit.sl` lines 1–12, 128–156, 305–372, 880–962,
  1196–1242, 1360–1480; `base.sl` lines 92–110, 255–300, 520–536; `escape.sl` lines 18–36, 76–120.
- [RAN] The fuel census (§2) does not rest on the partial reads. It rests on two exhaustive searches, each
  hit then read: (i) every `(subterm many|erased (Nat) x)` parameter in `base escape heap reader core eval
  elab emit interp main` (an awk scan; 59 functions), and (ii) every `(subterm …)` parameter of the main
  block of `elab-main.sl` classified by kind (output reproduced in §2.6); plus greps for
  `fuel|budget|steps|Steps|hop|limit|depth|expansion|callback` (counts per file in §2.6).

---

## 1. Headline findings (most decision-relevant first)

**H1. A whole compile is one driver step.** `main.sl` ends in `(Continue _ start)`, and `start` reads the
arguments and files, elaborates (running every compile-time evaluation and macro expansion), emits, and
returns `Exit`. [QUOTE main.sl:187-191]

```
(def-unique io-lvl $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (start-with args w1))

(Continue _ start)
```

[RAN] Confirmed by instrumenting a scratch copy of slc's own emitted OCaml (only the driver loop patched to
count `Continue`s; §6.1): compiling a small file, a failing compile, `--interpret` of a plain final, and the
full self-compile each printed `DRIVER-STEPS (continuations applied): 1`; `--interpret tests/io_echo.sl`
with three input lines printed `5`.

**H2. The compile-time interpreter is direct recursion on the host stack, bounded by a depth fuel that is
semantic.** Running out makes slc refuse the program (`compile-time evaluation failed: out of fuel`).
[READ core.sl:3614] slc's default is 1000000000. [QUOTE MANUAL.md:161-162] "Without the flag the reference
has none and slc's is 1000000000." [RAN] (§2.2) Both tools accept `--eval-fuel`, both report `out of
fuel`, and both need exactly 10002 units for a 5000-iteration loop.
[RAN] At the default fuel a 500000100-iteration tail loop is refused by slc after 117.8 s with `out of
fuel`. [RAN] For non-tail recursion the fuel is not what binds: slc dies with an uncaught `Fatal error:
exception Stack overflow` (exit 2) somewhere between 50000 and 75000 nested interpreted calls at the default
8 MB stack, long before 1000000000 units are spent.

**H3. The census has sixteen rows; `self/README.md` names two of them as the only non-structural
recursions and describes five more.** [READ; table in §2.1] Five rows are semantic (a): the interpreter
fuel (row 1), the expansion budget where it is charged for rewrites that are not macro expansions (row 2,
in part), the constant `heap-strs-fuel` (11), the compile-time printer's depth (12), and the generated
printer's fuel (13). Three have no runtime effect (b): `callbacks` (4), `hop-N` (5), and `Steps` (7). Three
report an error for a case believed unreachable (c): `sugar` (6), `rope-walk` (10), and `list-refs` at two
of its four call sites (9). Four return a silent default for a case believed unreachable (c\*):
`merge-opens` (14), `frame-chain` (15), `str-split-fuel` and `parse-pieces` (16), and `list-refs` at its
other two call sites, one of which turns a macro's output into the empty list. Three are the §62 limit or
follow it (d): the global count (3), `splice-go`'s budget (8), and row 2 where the charge follows a real
expansion.

**H4. The "10000 macro expansions" budget is also charged for rewrites that are not macro expansions, and
that is observable.** [RAN] A file of 10001 top-level forms whose heads are computed forms and which
contains no macro call is refused by slc and accepted by the reference:

```
$ $SLC --interpret heads_10001.sl
heads_10001.sl:10002:1: error: more than 10000 macro expansions
$ $REF heads_10001.sl
0
```

With 9999 such forms both print `0`. DESIGN.md §62 sanctions a count of *expansions*:
[QUOTE DESIGN.md:2752-2753 (§62)] "At most 10000 expansions run in one run, every file on the command line
included." No expansion runs in that file. (§2.3)

**H5. `slc --interpret` silently truncates a deep final value.** [RAN] A 60000-element list printed by
`slc --interpret` (with the stack limit raised) ends `… Cons _ 49998 $ Cons _ _ _)` with exit code 0: the
printer's depth budget of 100000, two units per list cell, ran out. The reference prints all 60000 elements
for the same file (§2.4). At the default 8 MB stack the slc command dies with `Segmentation fault` (exit
139).

**H6. Evaluation is interleaved with elaboration at sub-expression granularity.** [RAN] In one self-compile
(instrumented scratch copy, output byte-identical to the release slc's) `run-code` was entered 2270 times,
`env-expand` (macro expansion) 470 times, and the interpreter-to-elaborator callback `apply-answer` 8 times;
`eval` was called 189571 times in total. Between two consecutive entries of `run-toplevel` the maximum was
689 `run-code` calls (a table-building `let` in `core.sl`) and 125 `env-expand` calls (the 95-function main
block). (§6.3) [INFERENCE] Any design that suspends or replays the elaborator around each interpreter run
has to cope with those numbers.

**H7. The elaborator's state is one persistent value.** `Env` is a `many` record of 23 fields holding the
scope, fact table, store, literal table, macro counters, and the diagnostics list; the only linear thing
threaded through elaboration is the `World` wrapped as `ElabWorld`. [READ core.sl:2325-2332] The only
outside-world effects that can happen in the middle of elaborating a form are a macro's `read-file`
(`ReadFileIn`) and `native-compute` (`mktemp`, `WriteFile`, `ocamlfind`, `Exec` of the compiled program,
`ListDir`, `DeleteFile`, `DeleteDir`). [READ eval.sl:1431-1445; elab-main.sl:3-60, 119-131] Messages are
written only after all files are elaborated. [READ main.sl:139-143] (§6.4)

**H8. Evaluation order as slc implements it.** Calls and constructor applications are flattened by the
elaborator into nested `let`s: head first, then arguments left to right, each argument completely before the
next. [RAN, emitted OCaml in §4.2] A `values` inside a function body binds the nested arguments of *all* its
entries first and only then runs the entries' own calls; the same `values` in run position completes each
entry before starting the next. [RAN, timing probes in §4.3] The emitter never produces a nested OCaml
application whose argument is itself a call in the cases tested; it relies on the elaborator's `let`s.

**H9. What slc proves about itself is termination and representation invariants, plus relational
specifications of a few library functions. No language-level judgement appears.** [RAN] §5.1 lists every
indexed type family in `self/`. [INFERENCE] From their names, and from the definitions that were read, none
is a typing relation, an evaluation relation, or a canonical-form relation. [READ base.sl:261-300, 520-537,
609-614] `idmap-get`, `list-nth`, `length`, and `list-append` do return evidence of separately defined
relations (`MapsTo`/`Absent`, `Nth`/`OutOfRange`, `Length`, `Concat`).

**H10. slc already contains one fuel-free traversal of the mutable store.** `trace-loop` in `emit.sl`
terminates by an erased count of allocation stamps not yet seen, with no runtime budget and no failure case.
[READ emit.sl:1209-1226] [INFERENCE] It is a precedent for removing the store-walking fuels (`list-refs`,
`rope-walk`, `show-at`) without a step machine.

### What follows for the two questions

All [INFERENCE]; each bullet names the finding it rests on.

- **Q1, interpreter fuel.** It cannot be removed inside the present structure (H1, H2): the only unbounded
  loop DESIGN.md provides is the driver's, the compile is one driver step, and the interpreter is entered
  from deep inside the elaborator's recursion thousands of times per compile (H6). §6.5 lists four ways to
  bridge that, from a rewrite of the elaborator as a machine to a driver-level retry that only makes the
  fuel non-semantic.
- **Q1, host stack.** Removing fuel does not remove the second bound: slc overflows the host stack at
  50000–75000 nested calls today (H2). An explicit-stack interpreter would remove it; a larger host stack
  only moves it.
- **Q1, the other budgets.** The expansion budget's non-§62 charges (H4), the printer depth (H5), and
  `heap-strs-fuel` are local fixes; H10 shows the technique for the store walks. `merge-opens` (row 14) is
  the one silent default on a path the checker's own answers depend on: its zero case answers "merged"
  (DESIGN.md §8's invariant on opened `Matchable`s). Which way a wrong answer there would err was not
  worked out.
- **Q2, retrofit.** Nothing the elaborator returns is evidence about the program (H9). Its functions
  record errors in the `Env` and continue with placeholders (§5.3), and the `Env` hides the fact table's
  indices (§5.2). Carrying a derivation through it means changing the result of essentially every
  elaborator function in a 3077-line block, and deciding what a derivation is after the first recorded
  error.
- **Q2, natural seams.** Two places already have the shape proofs need: the library functions that return
  evidence of a separately defined relation (§5.2), and `Code ctx ms`, an intrinsically scoped target
  language with a small interpreter over it (six functions, lines 159–441, plus `eval.sl`). The seam between
  elaborating and running is not clean, though: values flow back into elaboration at sub-expression
  granularity (H6), so a specification of "elaborate" and one of "run" are mutually dependent in the same
  way.
- **Q2, order.** Whatever order the formal spec fixes, slc's present behaviour is not uniform: a `values`
  runs in a different order inside a function body than in run position (H8).

---

## 2. Fuel census (item 1)

### 2.1 The table

Classes: **(a)** semantic, running out changes what the user observes; **(b)** refuted or erased, no runtime
effect; **(c)** reports an internal error or an error value for a case believed unreachable; **(c\*)**
believed unreachable but returns a silent default (no report); **(d)** sanctioned by DESIGN.md.

| # | Parameter | Declared | Decreases at | Initial value | Zero case | Class |
|---|---|---|---|---|---|---|
| 1 | interpreter `fuel` | `(subterm many (Nat) fuel)` on `eval`, `eval-list`, `eval-updates`, `eval-picked`, `eval-branch`, `apply` (elab-main.sl:159, 335, 345, 359, 388, 402); plain `(many (Nat) fuel)` on `run-code` (443) and `interp-program` (interp.sl:98) | one unit per application at `CApp` (185-190), one more per call of an interpreted function body in `apply` (424, 434) | `(env-fuel e)` at elab-main.sl:450, 455, 462, 525, 550, 744 and interp.sl:143, 146, 153; `env-fuel` reads `Macros.fuel` (core.sl:2257, 2602-2605); default `1000000000` (core.sl:3614); `--eval-fuel n` overrides (main.sl:121-122, 132) | error block `"out of fuel"`; evaluation continues with error values; reported after the run as `compile-time evaluation failed: out of fuel` (core.sl:2412, 2815-2819) | **(a)** |
| 2 | expansion budget: `xf`, called `fuel` on the elaborator functions | `(subterm many (Nat) fuel)` on the 66 `hop-8` functions and `apply-answer`; `(subterm many (Nat) xf)` on 11 expansion helpers; `(subterm erased (Nat) xf)` on 17 (the six interpreter functions and the run helpers); `(subterm many (Nat) fuel)` on `run-toplevel` (3362) | 23 sites, listed in §2.3 | `expansion-limit` = 10000 (elab.sl:26): once per file (main.sl:29) and afresh per top-level item (elab-main.sl:3379, 3387, 3391, 3398); `0` in `--interpret` (interp.sl:109, 146, 153) | user-facing error `more than 10000 macro expansions` | **(d)** at sites that follow a real expansion; **(a)**, not covered by §62, at sites that follow a non-macro rewrite (H4) |
| 3 | global expansion count `Macros.expansions` (not a recursion parameter) | core.sl:2257 | incremented in `expand` (elab-main.sl:564) | 0 (core.sl:3614) | `expand` refuses when the count reaches 10000 (elab-main.sl:559-560) | **(d)** §62 |
| 4 | `callbacks` | `(subterm erased (Nat) callbacks)` on all 95 functions of the main block (one spelled `_`) | interpreter to elaborator call, elab-main.sl:321-323 (`Succ k` to `k`) | `0` from the top level; `Succ 0` from `MkMacroPerformer sl x 0 …` (525) | none: erased; the `Performer` constructor carries the `Succ` | **(b)** |
| 5 | `hop-0` … `hop-9` | erased constants (elab-main.sl:147-156), fixed per function as `(subterm erased hop-N is _)` | every call from an elaborator function towards the interpreter goes to a smaller `hop` | n/a | none: erased | **(b)** |
| 6 | `sugar` | `(subterm many (Nat) sugar)` on the 66 `hop-8` functions | one unit when a `let-match` with branches is rewritten to a `match` (elab-main.sl:1868-1876) | `raw-size`/`raws-size` of the form being elaborated (3379, 3387, 3391, and after every re-elaboration, e.g. 769, 784, 1840) | `internal: the sugar budget is spent` (1871) | **(c)** |
| 7 | `Steps n` | `(def-adts $ (Steps : ((Nat) n) -> Type)` (elab.sl:1242-1247); a `(subterm many (Steps …) st)` on 11 functions of the main block | `(let-match many st (SS _ k))` (elab-main.sl:1328, 1668, 1773, 3068) | `one-step`, `two-steps`, or `(SZ)` written at each call | none: the index refutes `SZ` | **(b)** |
| 8 | `splice-go`'s own `fuel` | elab-main.sl:577 | one unit per expansion spliced back into the work list (590) | `expansion-limit` (593) | `more than 10000 macro expansions` (586) | **(d)**; unreachable if row 3 fires first [INFERENCE] |
| 9 | `list-refs` `fuel` | eval.sl:171 | per list cell (180) | `(hsize _ hp)`, the number of allocations so far (eval.sl:260, 270, 669; elab-main.sl:532) | `None`; callers then do four different things: an empty `RList` silently (eval.sl:260), error block `slots constructor: out of fuel` (271), error block `list-to-array: out of fuel` (670), **a macro's output treated as the empty list** (elab-main.sl:532) | **(c)** at two sites, **(c\*)** at two |
| 10 | `rope-walk`/`rope-fields` `fuel` | eval.sl:455, 464 | per nesting level (463, 468) | `2 × hsize` (eval.sl:473) | `Fail "flatten: out of fuel"`, which becomes an error block (653, 692) | **(c)** |
| 11 | `heap-strs`/`heap-pairs`/`heap-jobs` `fuel` | eval.sl:1020, 1027, 1047 | per list cell | constant `heap-strs-fuel` = 1000000 (eval.sl:1018), used at 1055, 1146, 1159 | `(Nil _)`: the list is silently cut at 1000000 elements | **(a)**, silent; only under `--interpret` (`ConfinePaths`, `Exec`) |
| 12 | compile-time printer `depth` | `show-at`, `show-fields`, `shown-field` (elab.sl:4680, 4706, 4715) | two units per nesting level (4682, 4717) | constant 100000 (elab.sl:4730 for `comptime-match` messages; interp.sl:15 for `--interpret` finals) | prints `_` | **(a)**, silent (H5) |
| 13 | generated-printer `fuel` | `show-type`, `show-arms`, `show-block-fields` (emit.sl:1379, 1416, 1437) | per nested type, per constructor, and per field | `show-fuel` = 100000 (emit.sl:4; used 1473, 1478) | emits a call of `show_any`, which prints `?` (runtime.ml:18); or omits arms and fields | **(a)** in principle; not exercised here |
| 14 | `merge-opens` `fuel` | elab.sl:1987 | per merge of two opened objects | `Succ` of the number of opened objects (elab.sl:2004) | `(UOk env)`: reports success without finishing | **(c\*)** |
| 15 | `frame-chain` `fuel` | elab.sl:816 | per expansion frame followed | the frame's own number (`frame-chain e x x shown`, elab.sl:828) | the chain of "in the expansion of" notes is cut | **(c\*)**, diagnostics only |
| 16 | `str-split-fuel` `fuel`; `parse-pieces` `fuel` | base.sl:100; emit.sl:138 | per separator; per template hole | length of the string (base.sl:107-109; emit.sl:152-153) | returns what it has so far | **(c\*)** |

All sixteen rows: [READ at the cited lines]. Rows 1, 2, 3, and 12 also have [RAN] evidence below.

Related parameters that are **not** fuel, found by the same searches: [READ core.sl:3880; core.sl:1579;
escape.sl:80-106; reader.sl:222-225; emit.sl:1209-1226]

- `unify`'s `(subterm erased (Nat) n)`: the erased count of rule-free table entries; it steps down by a
  proof (`Subterm k n` inside `Less`), and no runtime value is tested.
- `canon`'s `(subterm erased (List $ Rule) after)`: the erased suffix of the rules list still to chase.
- `escape-into`, `put-bytes`, `read-scan`, `unescape-into` (`escape.sl`), and `lit-walk` (`reader.sl`): a
  runtime counter `left` tied to the data by erased `Add`/`StrLength` proofs; its zero case is the true end
  of the input.
- `trace-loop` (`emit.sl`): `(subterm erased (Nat) rest)`, the count of stamps not yet seen (H10).
- Data recursions on a `Nat` (`list-replicate`, `idmap-set`, `byte-run`, `repeat-field`, `spell-bits`,
  `show-nat`, `proof-errs`, `cell-read-bindings`, `entries-anonymize`, `facts-insert`, the `plus*` lemmas,
  the count helpers in `emit.sl`, `splice-tail`'s `k`, `native-jobs`'s `k`).

Outside `self/*.sl` but compiled into slc: [READ lib/prelude.sl:2542-2543] the `unary` macro refuses more
than 1024 successors, which DESIGN.md §49 sanctions: [QUOTE DESIGN.md:2286-2287 (§49)] "with as many
successors as separate the two, at most 1024".

**DESIGN.md is silent on fuel.** [RAN] `grep -n -i "fuel" DESIGN.md` prints nothing; the only numeric
budgets `grep -n -i "fuel\|budget\|step count\|at most 10000\|limit\b" DESIGN.md` finds are §44's
`array-limit`/`bytes-limit` and §62's 10000. What DESIGN.md says about the run:
[QUOTE DESIGN.md:1319-1323 (§31)] "Evaluation is eager. The semantics is that of a machine with unlimited
stack and heap. A real run may crash where the host cannot represent what is asked of it. A crash produces
no value, never a different one. How a crash is reported is not specified; it need not be a runtime error."
`MANUAL.md` (a session's text) files fuel exhaustion under that paragraph:
[QUOTE MANUAL.md:157-159] "A run that would go further crashes with `out of fuel` (DESIGN.md section 31)."
Whether running out of an implementation-chosen fuel is a §31 crash is that file's reading, not DESIGN.md's
wording.

### 2.2 Row 1, the interpreter fuel: code and experiments

[QUOTE elab-main.sl:185-187]

```
        (match many fuel _
          ((Zero)
            (let ((erased h3) (many hp3) (erased le3) (many r) (erased rpk)) $ error-vals _ hp2 ms2 "out of fuel")
```

[QUOTE elab-main.sl:424] `(let-match many fuel (Succ k) ((Zero) (error-w _ hp ms "out of fuel" _ w)))`

- [READ elab-main.sl:185-191, 402-435] The fuel is passed down, never returned: a callee gets `k`, and the
  caller continues with its own `fuel`. So it bounds nesting depth. A tail call in interpreted code is a tail
  call of `apply` then `eval` with the decreased value, so a tail loop spends two units per iteration and
  never gets them back.
- [READ elab-main.sl:416-422] A call of an extern function goes to `apply-extern` and spends only the
  `CApp` unit.
- [READ elab-main.sl:448-465, 544-553, 706-747, 509-525] Every run-position form, every hoisted temporary,
  and every macro expansion starts with a fresh `(env-fuel e)`.
- [READ elab-main.sl:187; core.sl:2409-2415, 2815-2819] Running out does not abort the run. `error-vals`
  allocates a `BError` block; `halloc` records the first error message in the heap's `crash` field; the
  interpreter goes on with the error block as a value; `env-with-heap` turns `crash` into the error
  `compile-time evaluation failed: …` when the heap is put back into the environment.

Programs (written by this agent):

```
; fuel_tail.sl
(def-fns _ $ (many count : (subterm many (Nat) n) (many (Nat) acc) -> (many (Nat) r))
  (match many n _ ((Zero) acc) ((Succ k) (tail (count k (Succ acc))))))
(let ((many x)) (count 5000 0))
x
; fuel_deep.sl
(def-fns _ $ (many depth : (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _ ((Zero) 0) ((Succ k) (Succ (notail (depth k))))))
(let ((many x)) (depth 5000))
x
```

[RAN] Both tools, with and without a small fuel (output of each command follows it):

```
$ $REF fuel_tail.sl                         -> 5000                                   (exit 0)
$ $REF --eval-fuel 1000 fuel_tail.sl        -> fuel_tail.sl: runtime error: out of fuel   (exit 1)
$ $SLC fuel_tail.sl > fuel_tail.ml          -> (50073 bytes of OCaml)                 (exit 0)
$ $SLC --eval-fuel 1000 fuel_tail.sl > fuel_tail.fuel.ml
     -> fuel_tail.sl:3:17: error: compile-time evaluation failed: out of fuel         (exit 1, 0 bytes)
$ $SLC --interpret --eval-fuel 1000 fuel_tail.sl
     -> fuel_tail.sl:3:17: error: compile-time evaluation failed: out of fuel         (exit 1)
$ $SLC --interpret fuel_tail.sl             -> 5000                                   (exit 0)
```

`fuel_deep.sl` gave the same six results with `fuel_deep.sl:3:17` in slc's message.

[RAN] Smallest passing value, by bisection over `--eval-fuel n` (`n` in 0…40000, success = exit 0):

```
REF fuel_tail.sl: 10002     SLC fuel_tail.sl: 10002
REF fuel_deep.sl: 10002     SLC fuel_deep.sl: 10002
```

[RAN] Fuel bounds depth, not work. `fuel_seq.sl` calls `(depth 1000)` four times in sequence and adds the
results; `$REF fuel_seq.sl` prints `4000`; the smallest passing `--eval-fuel` is `2004` for both tools.

[RAN] The default is reachable. `fuel_default.sl` is `fuel_tail.sl` with `500000100` for `5000`:

```
$ /usr/bin/time -f "... wall %e s, user %U s, maxrss %M KB, exit %x" timeout 500 $SLC --interpret fuel_default.sl
fuel_default.sl:3:17: error: compile-time evaluation failed: out of fuel
slc default-fuel run: wall 117.83 s, user 113.20 s, maxrss 29052 KB, exit 1
```

The reference was not run on that file. [QUOTE MANUAL.md:161-162] "Without the flag the reference has none
and slc's is 1000000000."

[RAN] The host stack binds first for non-tail recursion. `fd.sl` is `fuel_deep.sl` with the depth replaced:

```
depth 20000:  slc=[20000]  ref=[20000]
depth 50000:  slc=[50000]  ref=[50000]
depth 100000: slc=[Fatal error: exception Stack overflow]  ref=[100000]
depth 200000: slc=[Fatal error: exception Stack overflow]  ref=[Fatal error: exception Stack overflow]
$ $SLC fd100k.sl > fd100k.ml ; echo $?            -> Fatal error: exception Stack overflow ; 2 ; 0 bytes
$ $SLC --eval-fuel 150000 fd100k.sl               -> Fatal error: exception Stack overflow   (exit 2)
$ (ulimit -s 65536; $SLC --interpret fd100k.sl)   -> 100000                                  (exit 0)
```

[INFERENCE from these runs] A fuel of 150000 permits a depth of about 75000 and the stack still overflowed,
and depth 50000 passed, so at 8 MB (`ulimit -s` printed `8192`) slc's limit lies between 50000 and 75000 nested interpreted calls.

[RAN] Speed, for scale: a 3000000-iteration tail loop took 0.97 s under `slc --interpret` and 3.05 s under
the reference.

[RAN] A side observation about the reference, which matters to anyone using it as an oracle for order or
fuel: under `--eval-fuel 1000000` the reference answers a 600000-iteration *tail* loop with `Fatal error:
exception Stack overflow`, where slc answers `out of fuel` (files `ord_common.sl` + `ord_c1.sl`). Without the
flag the reference ran a 3000000-iteration tail loop to completion. [INFERENCE] The reference's fuel
accounting appears to cost it its tail calls; this was not checked in `lib/eval.ml`.

**What removing row 1 would take.** [INFERENCE] `eval` recurses into closure bodies it did not receive as
arguments, so no structural measure exists; the fuel is what the termination checker accepts. The only
unbounded iteration DESIGN.md offers is the driver's:
[QUOTE DESIGN.md:1993-1994 (§42)] "The driver flushes after every write. It never recurses, so an unbounded
interaction is the driver's loop over total functions." So a fuel-free interpreter needs its loop moved to
the driver, which needs the elaborator suspended or replayed around each of the entry points listed in §3.10
(§6.5 gives the options and their sizes). A smaller change that makes the fuel non-semantic without making
each step total is also sketched in §6.5 (option D).

### 2.3 Row 2, the expansion budget: where it is spent

[READ at each line] Sites where the budget is matched as `(Succ f2)` with the `(Zero)` branch reporting
`more than 10000 macro expansions`, grouped by what was rewritten:

- After a real macro expansion or a splice of expansions into a list: elab-main.sl:511 (`env-expand`), 766
  and 781 (`elab-expr-demand`), 1258 and 1266 (`elab-term`), 1779 (`elab-tele`), 1846 and 1854
  (`elab-body`), 1896 (`elab-refute`), 1943 (`elab-stmts`), 1970 (`elab-stmt`, `let` binders), 2106
  (`elab-let-match`), 2645 (`elab-ctors`), 2803 (`elab-match`), 3375 (`run-toplevel`).
- After a rewrite that is **not** a macro expansion:
  - 1126: a compound head computed to a `Settled` special form or macro is replaced by a handle and the
    form is elaborated again.
  - 1838, 1934, 3382: `settle-item` replaced a statement's compound head by a handle. At 1838 and 1934 the
    decreased budget also governs the rest of the body; at 3382 it governs the rest of the file.
  - 1501 (`cell-alloc`), 1541 (`cell-write`), 1682 (cell invocation): the budget is spent only so that the
    termination checker accepts a call on a list (`bare`, `dues`) that is not a subterm of `args`.
  - 2562 (`elab-settled-apply`): a raw built from handles is elaborated.

[QUOTE elab-main.sl:3379-3383]

```
  (let ((unique ew2) (many envs) (many settled) (many _) (many _)) $ settle-item ew1 expansion-limit 0 _ (raw-size item) item envf (Nil _) (Many))
  (let-match many settled (None _)
    ((Some _ item2)
      (let-match many fuel (Succ f2) ((Zero) (values ew2 (env-error envs "more than 10000 macro expansions"))))
      (tail $ run-toplevel ew2 f2 (Cons _ item2 rest) frames expanded loading $ env-in-expansion envs 0)))
```

[RAN] The probe behind H4. `heads_N.sl` is

```
(def-fns _ $ (many pick : -> (many (Special) s)) def-lvl)
((pick) L0)
…                       ; N such lines
(Zero)
```

```
N=3:      slc --interpret -> 0                       ref -> 0
N=9999:   slc --interpret -> 0   (0.82 s)            ref -> 0   (0.73 s)
N=10001:  slc --interpret -> heads_10001.sl:10002:1: error: more than 10000 macro expansions
          ref -> 0
```

[INFERENCE] For real expansions the `(Zero)` branches look unreachable: `expand` refuses first, because the
global count (row 3) is at least the number of expansions along any path. That argument is not in the
types.

**What removing the non-§62 charges would take.** [INFERENCE] Each is a place where the code hands a raw of
its own making to a function that wants a subterm. Line 3382 needs only a one-step budget per item, since a
settled item's head is an atom and `settle-item` then returns `None` [READ elab-main.sl:1216-1218]; the
existing `Steps` type does exactly that. Lines 1501, 1541, and 1682 need `Within`/`Sub` evidence kept
through `cell-marks`/`sub-raws` instead of dropped.

### 2.4 Row 12, the compile-time printer: experiment

```
; longlist.sl
(def-fns _ $ (many build : (subterm many (Nat) n) (many (List (Nat)) acc) -> (many (List (Nat)) r))
  (match many n _ ((Zero) acc) ((Succ k) (tail (build k (Cons (Nat) k acc))))))
(build 60000 (Nil (Nat)))
```

[RAN]

```
$ (ulimit -s 1000000; $SLC --interpret longlist.sl > longlist.slci.out); echo $?     -> 0   (738888 bytes)
$ head -c 60 longlist.slci.out   -> (Cons _ 0 $ Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Cons
$ tail -c 70 longlist.slci.out   -> ns _ 49995 $ Cons _ 49996 $ Cons _ 49997 $ Cons _ 49998 $ Cons _ _ _)
$ $SLC --interpret longlist.sl > ll.default.out      (default 8 MB stack)
     -> Segmentation fault, exit 139, 0 bytes
```

[RAN] The reference on the same file, stack limit raised the same way:

```
$ (ulimit -s 1000000; timeout 500 $REF longlist.sl > longlist.ref.out)     -> exit 0 after 202.72 s, 888898 bytes
$ tail -c 70 longlist.ref.out   ->  $ Cons _ 59996 $ Cons _ 59997 $ Cons _ 59998 $ Cons _ 59999 $ Nil _)
$ cmp longlist.ref.out longlist.slci.out   -> differ: char 738884, line 1
```

So the two implementations print different text for this final value, and slc's is the truncated one.
(For shorter lists the reference took 1.43 s at 5000 elements, 3.87 s at 10000, and 16.67 s at 20000.)

[RAN] Compiling the same file is impractical for a different reason: `$SLC longlist.sl --build ./longlist_prog`
overflowed slc's own stack at 8 MB (`Fatal error: exception Stack overflow`, exit 2); with the limit raised,
slc wrote a 15489385-byte, 243254-line `main.ml`, and `ocamlopt` ran on it for more than 400 s at about 1 GB
of memory before this agent killed it. So the compiled program's printing of this value was not observed.
[UNKNOWN]

### 2.5 What removing the other rows would take

All [INFERENCE], each resting on the code cited in the table.

- Rows 9, 10, 12 (walks of the store): the store is not an inductive value once a cell has been written,
  because `store-write` stores a body whose references are valid at the *current* history, so a written
  block may point at younger blocks. [READ heap.sl:204-207] `trace-loop` shows the fuel-free alternative: a
  seen-set of stamps with an erased proof that it is bounded by the store's size. Row 9's two silent call
  sites could at least report.
- Row 11: use the store's size instead of a constant, or report at zero.
- Row 13: the recursion is over types, and a non-regular datatype has unboundedly many instances. Either a
  bound stays, or the generated program prints by value shape instead of by type.
- Row 14: an index on the opened list by its length, decreased by `env-unopen`, would refute the zero case.
  Today zero means "report success". [READ elab.sl:1987-1996]
- Rows 15, 16: evidence that each step goes to a strictly smaller frame number, or a strict suffix of the
  string, as `reader.sl` already carries for its own scanning (`suffix-sub`, reader.sl:236).
- Row 6: a proof that the rewrites nest at most as deep as the form is large. `self/README.md` says why it
  has none: [QUOTE README.md:391-394] "its zero case is reported as an internal error, not refuted, since
  the sugar forms are found by resolving a head in the prelude's scope, which no proof here speaks about".

### 2.6 The searches behind "exhaustive"

[RAN] Occurrences per file (`grep -c`):

```
fuel:       base 4, core 3, elab-main 422, elab 11, emit 11, eval 20, interp 7, main 4, others 0
budget:     elab-main 1, elab 2            Steps: elab-main 11, elab 4
hop:        elab-main 105, elab 2          depth: core 2, elab 7, emit 28, reader 2
expansion:  core 9, elab-main 73, elab 6, eval 2, main 1, reader 1
callback:   elab-main 450                  limit: elab-main 6, elab 1, main 3, reader 3
```

`depth` in `emit.sl` is a name-generation depth (`names-depth`) and `limit` in `reader.sl` is
`pragma-limit`, a word count; neither bounds a recursion. [READ emit.sl:365-369, 571-574; reader.sl:194]

[RAN] Kinds of `(subterm …)` parameter in the main block (`sed -n '158,3234p' elab-main.sl`, then a sed/sort
over every `(subterm …)`), abbreviated:

```
94 subterm erased Nat callbacks (+1 spelled `_`)     67 subterm many Nat fuel (66 hop-8 functions + apply-answer)
66 subterm erased hop-8, each followed by subterm many (Nat) sugar
17 subterm erased Nat xf      11 subterm many Nat xf      11 subterm many (Steps …)
 6 subterm erased hop-0, each followed by subterm many (Nat) fuel   (the interpreter)
 1 subterm erased hop-3 followed by subterm many (Nat) fuel         (splice-go)
 1 subterm many Nat k                                               (splice-tail; a count)
the rest: subterm many/erased over List, Syn, Pair, Code, LetParts, Headers, AdtHeaders, Ann
```

---

## 3. The compile-time interpreter (item 2)

### 3.1 Shape

- [READ elab-main.sl:159-441] The interpreter is six functions, `eval`, `eval-list`, `eval-updates`,
  `eval-picked`, `eval-branch`, and `apply`, inside the same `def-fns` block as the elaborator. They are
  direct-style: sub-evaluations are `notail` calls on the host stack; `let` bodies, branch bodies, and the
  called function's body are reached by `tail` calls.
- [RAN] §2.2: host stack overflow at 50000–75000 nested interpreted calls confirms the host-stack use.
- [QUOTE eval.sl:1-5] "the compile-time interpreter (DESIGN.md section 29's round trip; lib/eval.ml): a
  plain recursive evaluator over post-erasure code and the store of self/heap.sl, bounded by a fuel that
  decreases along the call stack so the checker accepts it. Every value is an address; every step returns
  the grown store with a proof of the growth, by which what was held before is widened. Extern functions run
  as the host's own (section 42)."

### 3.2 Code

- [READ core.sl:604-622] The interpreted language is `Code ctx ms`, indexed by the frames of non-erased
  identifiers in scope (`ctx`) and the multiplicities of the values produced (`ms`). Constructors: `CVar`
  (with a `Mem id ctx` path), `CConst id` (a `Settled` entry, read from the store when run), `CValue` (a
  closed block), `CErased`, `CValues`, `CApp`, `CLet`, `CLetRec`, `CMatch`, `CCellAlloc`, `CCellWrite`,
  `CCellCopy`, `CCellRead`, `CWorldDo`, `CPrim`, `CAbsurd`, `CError`.

### 3.3 Values and the store

- [READ heap.sl:56-58, 45-47] A value is a `Ref Block hs`: a `newtype` over `MkValue pos lp body`, that is,
  an allocation stamp `pos` (a `Nat`) together with the block's body as it was when allocated, plus an
  erased proof that it was allocated within history `hs`. Every value is one, a `Nat` included (`BExt (PNat
  n)`), and so is the token for an erased result (`BToken`).
- [READ core.sl:566-578] Blocks: `BArray`, `BSlots`, `BTag ctor fields`, `BTup`, `BExt payload`, `BCtorFn`,
  `BMat`, `BGroup` (a `def-fns` group closed over its frames), `BFn group member id` (a closure), `BToken`,
  `BError msg`.
- [READ heap.sl:65-69, 163-170, 191-207] The store is `MkStore next ln writes`: the next stamp, and an
  `IdMap` from stamp to *current* body. `alloc` only increments `next` and returns the new `Ref`; it does not
  insert into the map. `store-read` looks the stamp up in `writes` and falls back to the body inside the
  `Ref`. `store-write` sets the stamp's entry in `writes`.
- [READ base.sl:255-259, 283-300] `IdMap` is a persistent binary trie keyed by the halves of a `Nat`.
- [READ core.sl:2383-2425] The interpreter threads a `Heap hs` = the store, the `Settled` entries map, the
  finals list, and `crash : Maybe String`.
- [QUOTE heap.sl:1-6] "the compile-time store: a value is stamped with its position in an erased ghost
  history, and refers to other values directly rather than through an address. The history makes position ->
  value a function (suffix-unique below), which is what lets the emitter name a value it has already
  written. Parametric in the block type, which takes the reference type as its parameter so that it never
  mentions the history. Nothing here is settled design."

### 3.4 In-place mutation

- [READ elab-main.sl:251-269] `CCellWrite` evaluates the cell, then the written slots, reads the block,
  and `hwrite`s a `BTag` with the fields replaced at the same stamp; the result is the same `Ref`.
- [READ elab-main.sl:271-288] `CCellCopy` (a `cell-write` at `many`) allocates a fresh block instead.
- [READ eval.sl:159-169, 535-542, 684-685, 688-690] Extern in-place operations do the same through
  `hwrite`: array change, `Slots` insertion, and `ErWrite` for the `Bytes` setters.
- [INFERENCE] So mutation is a functional update of a map keyed by stamp; any other `Ref` with that stamp
  sees the new content on its next read, as an alias would in a real heap.

### 3.5 `slot-eq`

[QUOTE eval.sl:809] `(Some _ $ match many (nat-eqb (ref-pos _ _ a) (ref-pos _ _ b)) _ ((BTrue) some) ((BFalse) none)))`

- [READ eval.sl:804-809; elab-main.sl:319-329] `slot-eq` answers `ESome` exactly when the two values have
  the same allocation stamp. Two separately allocated blocks holding equal immediates answer `ENone`.
- [READ eval.sl:383-394, 666] A fieldless constructor of an untagged, non-extern, non-newtype type is not
  allocated: `construct` returns the stored value of the built-in entry `null-id` (the entry whose absence
  `array-new` reports as `no vacant-slot`), so all such values share one stamp.

### 3.6 Extern functions and extern types

- [READ elab-main.sl:416-422; eval.sl:547-703] A function marked `extern` whose name the FFI table knows
  carries `impl = Some …`; `apply` then calls `apply-extern`, a `match` with one arm per `Extern`
  constructor that computes with slc's own host values (for example `(ExAdd) (ErPayload $ PNat $ nat-add na
  nb)`). The model body is not interpreted.
- [READ core.sl:475-483; eval.sl:663] `ext-twin` first maps the `U62`, `Many`, and `Imm` variants to a twin;
  the `match` then ends in `(else (ErPayload $ PStr "an extern with no implementation of its own"))`, a
  value, not an error block. [INFERENCE] It looks unreachable; it is not refuted.
- [READ core.sl:552-556; eval.sl:281-293, 328-346, 398-431] Extern types are host payloads: `ExtNat` is
  `PNat`, `ExtString` is `PStr`, `ExtArray` is `BArray`, and so on. Construction goes through
  `ext-construct` and matching through `dispatch`/`ext-destruct`, which present the payload as the model's
  constructor index and fields (matching a `Nat` allocates a fresh `PNat` for the predecessor).
- [RAN] slc has no models mode: `$SLC --no-extern fuel_tail.sl` prints `slc: unknown flag --no-extern`
  (exit 1); `$REF --no-extern fuel_tail.sl` prints `5000`.

### 3.7 `world-do` and the `Performer`

- [READ eval.sl:1503-1516] Every interpreter function is generic in a world type `W` and takes a
  `Performer W xf callbacks` and a `unique W`. A `Performer` holds two functions: one performs a request
  (`CWorldDo`), one runs a primitive (`CPrim`). It has two constructors; `MkMacroPerformer` has result type
  `Performer (MacroState s) x (Succ k)`.
- [READ eval.sl:1518-1533; elab-main.sl:443-446] Run-position code runs with `W = Unit` and `compile-time`,
  whose two functions allocate error blocks (`` `world-do` reached with no world ``).
- [READ elab-main.sl:517-525; eval.sl:1499-1501, 1535-1580] A macro runs with `W = MacroState s`, which
  holds the `Env` and the placed `ElabWorld`; `macro-prim` implements `gensym`, `resolve`, `read-file`,
  `settled-eq`, `mint-settled`, `mint-settled-erased`, and the three `intern-` forms against that `Env`.
- [READ interp.sl:129-143; eval.sl:1064-1169] `--interpret` runs with `W = ElabWorld` and a `perform` that
  unwraps the real `World` and calls `perform-request`, which issues the real `world-do`.

### 3.8 How a run-position form is run and embedded ("Settled")

- [READ elab-main.sl:544-553, 706-747, 536-542, 2209-2216, 2160-2167, 666-678, 3393-3398] A piece of code
  is run during elaboration exactly when the environment is at run position, nothing has failed yet, and
  its context `ctx` is empty. Seven places do so: `call-returns` (each call), `hoist-temp` (each hoisted
  argument or head), `run-form` (at the end of every expression), `elab-let` (the right-hand side),
  `elab-let-match` (the scrutinee), `open-bind` (the `let` behind `open-adt`), and `run-toplevel` for a
  file's final expression (`env-run-final`).
- [READ elab-main.sl:443-446, 449-457; elab.sl:961-976, 986-992; eval.sl:1610-1623] Each calls `run-code` on closed code with
  the heap taken out of the `Env`; the resulting `Ref`s are written into the entries map as `SSettled v x`
  (`set-run-states`, `set-field-states`); the heap is put back; and the form's own code is replaced by
  `CValues` of `CConst id`.
- [READ emit.sl:657-661] In the emitted OCaml a `CConst` is the name of the block its entry holds.
- [RAN] §6.3: 2270 such runs in a self-compile.

### 3.9 Macro expansion, and the callback into the elaborator

- [READ elab-main.sl:555-567] `expand` checks that the head is a macro entry, refuses at 10000 expansions,
  increments the count, and calls `env-expand`.
- [READ elab-main.sl:509-534] `env-expand` builds the `Pos` and the argument list in the store (each
  argument an extern `Raw` payload wrapping the reader's own syntax tree), applies the macro's function with
  `apply x _ _ (env-fuel e) …` under `MkMacroPerformer sl x 0 requests prims`, and reads the result list
  back with `list-refs` and `heap-syns`.
- [QUOTE elab-main.sl:321-323]

```
                  (let-match many pf (MkMacroPerformer s x k _ prim) ((MkPerformer _ _ _ _ prim) (prim _ hp1 p avs w1)))
                  (let-match many (or (sp-eq p $ SpExpr $ ExSettledTyApply) $ sp-eq p $ SpExpr $ ExSettledValApply) (BTrue) ((BFalse) (prim _ hp1 p avs w1)))
                  (let ((erased h3) (many hp3) (erased le3) (many v) (unique (MacroState s) w3)) $ notail $ apply-answer x k _ s _ hp1 (sp-eq p $ SpExpr $ ExSettledTyApply) avs w1)
```

- [READ elab-main.sl:467-507] Why the interpreter calls back: `settled-ty-apply` and `settled-val-apply`
  must check an application as a term where the macro runs. `apply-answer` builds a raw from the handles,
  calls `elab-term` on it in a quiet snapshot of the `Env`, and answers `Some` or `None` by whether an error
  was recorded. This is the only path from the interpreter into the mutually recursive block's elaborator
  functions.
- [READ elab-main.sl:159, 467, 509; eval.sl:1511-1516] How the checker accepts it: every function of the
  block is ordered first by the expansion budget, then by `callbacks`, then by `hop`. Matching the
  `Performer` as `MkMacroPerformer` reveals `callbacks = Succ k`, so `apply-answer` is called at `k`. An
  expansion started from inside the callback goes through `env-expand`, which decreases the budget and may
  then give the new run `callbacks = 1` again.
- [RAN] §6.3: 8 callbacks in a self-compile.

### 3.10 Call graph between elaborator and interpreter

[READ: every edge below is a call site at the cited line of `elab-main.sl`] [RAN] The edges *into* each
helper and into `eval`/`apply` are complete: a grep for each helper's name finds exactly the call sites
shown (`eval` is called from outside the six interpreter functions only at line 445, and `apply` only at
525 and in `interp.sl`). The edges among the 66 `hop-8` functions are a selection.

```
ELABORATOR (hop-8; 66 functions)            RUN/EXPANSION HELPERS (hop 1-7)                INTERPRETER (hop-0)

run-toplevel ─(3371)────────────────────────▶ expand ─(564)─▶ env-expand ─(525)──────────▶ apply   [macro function]
 (outside block)─(3379)▶ settle-item ─(1224)▶ hoist-temp ─(542)─▶ env-run-let ─(455)─▶ run-code ─(445)─▶ eval
               ─(3387)▶ elab-stmt
               ─(3391)▶ elab-expr-demand
               ─(3398)──────────────────────▶ env-run-final ─(450)─▶ run-code

elab-expr-demand ─(754)──▶ expand-one ─(570)─▶ expand
                 ─(771)──▶ splice-call ─(633)▶ splice-tail ─(620)▶ splice ─(593)▶ splice-go ─(581)▶ expand
                 ─(1161)─▶ elab-call ─(3172/3173)▶ hoist-argument ─(697)▶ hoist-temp
                                     ─(3174)─▶ check-args ▶ check-args-go ─(3120)▶ elab-expr-demand   [each argument]
                                                                          ─(3134)▶ hoist-argument
                                     ─(3184)─▶ call-returns ─(744)──────────────▶ run-code
                 ─(1107, 2513, 2572)─────────▶ call-returns                         [world-do form, primitives]
                 ─(873)──▶ native-batch ─▶ emit-program, native-run                 [no eval: OCaml compile and run]
                 ─(1168)─────────────────────▶ run-form ─(550)──────────────────▶ run-code
elab-stmt ▶ elab-let ─(2215)────────────────▶ env-run-let
          ▶ elab-let-match ─(2164)──────────▶ env-run-let
          ▶ elab-open-adt ─(2089)▶ open-bind ─(677)▶ env-run-let ;  open-absurd/refute ─(929, 1916)▶ open-contradicts ─(682)▶ open-bind
          ▶ comptime-scrutinee ─(1193)▶ elab-expr-demand ;  then elab-comptime-match (elab.sl:4781: a store read, no eval)
elab-body ─(1842)▶ body-head ─(647)▶ expand ;  elab-refute ─(1891)▶ expand ;  elab-stmts ─(1938)▶ expand
elab-body ─(1834)▶ settle-item ;  elab-stmts ─(1931)▶ settle-item ;  settle-item ─(1220)▶ compute-head ─(1203/1207)▶ elab-expr-demand
elab-term ─(1252)▶ expand-one ;  elab-term ─(1261)▶ splice-call ;  elab-stmt(let) ─(1966)▶ splice-binders ─(640)▶ splice-entries
elab-tele ─(1774)▶ splice-entries ─(611)▶ splice ;  body-head ─(652)▶ splice-tail ;  elab-let-match (2102), elab-ctors (2640), elab-match (2799) ▶ splice-tail
elab-expr-demand ─(1117)▶ compute-head   [a compound head]
cell items, cell-write input, cell-same/fn-same operands ─(1413, 1527, 1572, 1576)▶ hoist-unplaced ─(703)▶ hoist-temp
cell invocation ─(1678)▶ hoist-temp

INTERPRETER ─▶ ELABORATOR
eval (CPrim, under MkMacroPerformer) ─(323)▶ apply-answer (hop-9) ─(490)▶ elab-term (hop-8) ─▶ … ─▶ expand ─▶ env-expand ─▶ apply

INTERPRETER ─▶ library code outside the block
eval (CPrim) ─▶ performer's prim = macro-prim (eval.sl:1540): resolve-answer, settled-eq-answer (canon-env),
               mint-answer (bind-entry), intern-lit (bind-lit), read-file-answer (world-do ReadFileIn), gensym
eval (CWorldDo) ─▶ performer's perform: no-world | macro-no-world | interp.sl perform ▶ perform-request (real requests)
apply ─(420)▶ apply-extern (eval.sl:547)

--interpret (interp.sl): interp-finals ─(146, 153)▶ apply ;  interp-program's step ─(109)▶ apply ;  final-text ─(15)▶ show-at
```

- [RAN] `grep -n "env-run-fields" *.sl` finds only its definition (elab-main.sl:460): it has no caller.
- [READ elab.sl:4680-4726; interp.sl:13-16] The printer for values (`show-at`) reads the store by type; it
  does not call `eval`. In a normal compile no final value is printed by slc at all: a generated printer is
  emitted into the program. [READ emit.sl:1463-1480]

---

## 4. Evaluation order as implemented (item 3)

This section reports what slc does. [RAN] `grep -n -i "left to right\|right to left\|order of
evaluation\|evaluation order\|evaluated\|in order" DESIGN.md` finds eleven lines (370, 699, 826, 985, 1163,
1307, 1420, 1844, 1878, 1895, 2185); none of them states an order among the sub-expressions of one form.
The sentence of DESIGN.md nearest to the subject is
[QUOTE DESIGN.md:655-661 (§15)] "Every argument to a constructor, a function or a cell behaves as if it
were first bound to an anonymous variable. An argument that is already a variable is not rebound. That
binding is a statement (§27) placed just before the statement or final form that contains the call, so its
entry stays in scope, anonymously, for the rest of the expression around it, as the entries of a `let`'s
right-hand-side statements do."

### 4.1 In the interpreter (i)

[READ at the cited lines of elab-main.sl]

- `CApp` (178-191): the head code, then the arguments by `eval-list`, which is left to right (337-341),
  then the fuel test, then `apply`.
- `CValues` (177, 361-386): entries left to right (`eval-picked`).
- `CLet` (192-197): the right-hand side, then the rest.
- `CMatch` (206-246): the scrutinee; then, for a match through a held `Matchable`, the `Matchable`'s code;
  then the dispatch; then the chosen branch.
- `CCellWrite` and `CCellCopy` (251-288): the cell, then the written items left to right (`eval-updates`,
  349-357), then the write or the copy.
- `CCellAlloc` (247-250): the slot items left to right. `CPrim` (311-312): the arguments left to right.
  `CWorldDo` (304-310): the request, then the perform.

In practice the sub-codes of `CApp`, `CMatch`, and the cell forms are variables or constants, because the
elaborator has already bound everything else:

- [READ elab-main.sl:3171-3175, 3083-3149] `elab-call` hoists the head (`hoist-argument`, giving `hsc`),
  then `check-args-go` walks the arguments left to right; each argument's code is elaborated, its own
  hoisted statements `prea` and then its own binding `scb` are appended to the chain (`SSeq chain (SSeq prea
  scb)`), and the call receives variables (`id-codes`). The statements are `SSeq hsc apre`: head first.
- [READ elab-main.sl:1147-1158] A constructor application does the same.
- [READ elab-main.sl:2818-2826, 2885] A `match` binds its scrutinee to a fresh `saved` by a `CLet` and
  matches on the variable.
- [READ elab-main.sl:1524-1552, 1397-1421] A `cell-write` hoists the cell, then each item left to right
  (`hoist-unplaced`), then writes.
- [READ elab-main.sl:2693-2711] `elab-values` differs: each entry's hoisted statements go into the shared
  prefix `(SSeq pre1 pre2)`, but the entry's own code stays inside the `CValues`. When an entry is a call,
  the call itself is that code [READ elab-main.sl:738-739], so the nested arguments of all entries precede
  every entry's call.
- [READ elab-main.sl:739-747, 536-542] In run position each call and each hoisted temporary is run as soon
  as it has been elaborated, so there the order is the elaborator's own traversal: an entry of a `values`
  is elaborated, and therefore run, completely before the next entry is looked at.

### 4.2 In the emitter (ii): emitted OCaml

- [READ emit.sl:909-918] For `CApp` the emitter writes `(name arg1 … argn)` with the emitted arguments in
  place; it adds no bindings of its own.
- [READ emit.sl:365-369] For `CValues` of more than one entry it binds every entry that is not a name:
  `(let tupN_a0 = … in let tupN_a1 = … in (tupN_a0, tupN_a1))`. The comment gives an `ocamlopt` bug, not
  evaluation order, as the reason.

[RAN] `order.sl` (this agent's test) and the OCaml slc wrote for it (`$SLC order.sl > order.ml`; the
reference and `slc --interpret` print the same final value for the program):

```
(def-fns _ $ (many nested : (many (T) x) (many (T) y) -> (many (T) r))
  (f (g x) (h y)))
(def-fns _ $ (many vals : (many (T) x) (many (T) y) -> (many (T) p) (many (T) q))
  (values (g (k x)) (h (k y))))
(def-fns _ $ (many deep : (many (T) x) -> (many (T) r))
  (f (g (h x)) (k (g x))))
(def-fns _ $ (many ctor : (many (T) x) -> (many (T) r))
  (C (g x) (h x)))
```

[QUOTE $P/order.ml:861, 863, 865, 867]

```
let rec v42106_nested_a1573 (v42108_x : Obj.t) (v42110_y : Obj.t) : Obj.t = (let v42122___42122__ = (v42040_g_a1561 v42108_x) in (let v42130___42130__ = (v42053_h_a1564 v42110_y) in (v42087_f_a1570 v42122___42122__ v42130___42130__)))
let rec v42147_vals_a1576 (v42149_x : Obj.t) (v42151_y : Obj.t) : Obj.t = (let v42161___42161__ = (v42070_k_a1567 v42149_x) in (let v42175___42175__ = (v42070_k_a1567 v42151_y) in (let tup4_a0 = (v42040_g_a1561 v42161___42161__) in let tup4_a1 = (v42053_h_a1564 v42175___42175__) in (to_any (tup4_a0, tup4_a1)))))
let rec v42189_deep_a1579 (v42191_x : Obj.t) : Obj.t = (let v42205___42205__ = (v42053_h_a1564 v42191_x) in (let v42211___42211__ = (v42040_g_a1561 v42205___42205__) in (let v42221___42221__ = (v42040_g_a1561 v42191_x) in (let v42227___42227__ = (v42070_k_a1567 v42221___42221__) in (v42087_f_a1570 v42211___42211__ v42227___42227__)))))
let rec v42240_ctor_a1582 (v42242_x : Obj.t) : Obj.t = (let v42254___42254__ = (v42040_g_a1561 v42242_x) in (let v42262___42262__ = (v42053_h_a1564 v42242_x) in (to_any (K11_2 { f0 = v42254___42254__; f1 = v42262___42262__ }))))
```

So: `(f (g x) (h y))` is `g`, `h`, `f`; `(f (g (h x)) (k (g x)))` is `h`, `g`, `g`, `k`, `f`; and
`(values (g (k x)) (h (k y)))` is `k x`, `k y`, then `g`, then `h`.

[RAN] `order2.sl`: a `match` on a call and a computed head.
[QUOTE $P/order2.ml:859, 863] (source: `(match many (g (h x)) _ …)` and `((pick (g x)) (h y))`)

```
let rec v42087_sc_a1569 (v42089_x : Obj.t) : Obj.t = (let v42099___42099__ = (v42051_h_a1563 v42089_x) in (let v42105___42105__ = (v42040_g_a1561 v42099___42099__) in (match (of_any v42105___42105__ : t11) with | K11_0 -> …
let rec v42183_hd_a1575 (v42185_x : Obj.t) (v42187_y : Obj.t) : Obj.t = (let v42197___42197__ = (v42040_g_a1561 v42185_x) in (let v42203___42203__ = (v42158_pick_a1572 v42197___42197__) in (let v42213___42213__ = (v42051_h_a1563 v42187_y) in ((of_any v42203___42203__ : Obj.t -> Obj.t) v42213___42213__))))
```

(The first line is cut here after the first arm; the file has the rest.)

[INFERENCE] In these programs no OCaml application has a call as an argument, so OCaml's own argument
order never matters. A form whose arguments the elaborator does not hoist could still emit one;
`check-args` has a `prepare` flag that is false for type-constructor applications and term arguments
(elab-main.sl:1139, 3117-3118), which are erased. No counterexample was looked for beyond the tests above.

### 4.3 Order observed at compile time, by which crash comes first

A pure program cannot observe order, so these probes use two crashes that look different. `dive` recurses
non-tail and overflows the host stack at once (fatal); `spin` is a long tail loop.

```
; ord_common.sl
(def-fns _ $ (many spin : (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _ ((Zero) 0) ((Succ k) (tail (spin k)))))
(def-fns _ $ (many dive : (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _ ((Zero) 0) ((Succ k) (Succ (notail (dive k))))))
(def-fns _ $ (many same : (many (Nat) a) -> (many (Nat) r)) a)
```

[RAN] Timing probe: if the 20000000-iteration `spin` (2.7 s alone under slc, 9.6 s under the reference)
runs before the crash, the run is slow.

| file | form | where | slc `--interpret` | reference |
|---|---|---|---|---|
| `tp_spin_only.sl` | `(same (spin 20000000))` | run position | 2.69 s, prints `0` | 9.59 s, prints `0` |
| `tp_body_values.sl` | `(values (dive 3000000) (same (spin 20000000)))` | function body | **2.63 s**, then Stack overflow | **10.09 s**, then Stack overflow |
| `tp_run_values.sl` | the same `values` | run position | 0.39 s, Stack overflow | 0.98 s, Stack overflow |
| `tp_body_call.sl` | `(two (dive 3000000) (same (spin 20000000)))` | function body | 0.41 s, Stack overflow | 0.96 s, Stack overflow |
| `tp_run_call.sl` | the same call | run position | 0.40 s, Stack overflow | 1.01 s, Stack overflow |

[INFERENCE from the table] In a function body the nested argument `(spin …)` of the second `values` entry ran before the first
entry's own call `(dive …)`; in run position the first entry's call ran first; in a call, the first argument
ran completely before the second argument's nested argument, in both positions. The two implementations
agree with each other on all five.

[RAN] A second probe for run position, by message instead of time (slc only, `--eval-fuel 1000000`, so that
`(spin 600000)` runs out of fuel and `(dive 3000000)` overflows the stack):

```
ord_run.sl       (let ((many a) (many b)) (values (spin 600000) (same (dive 3000000))))
   -> ord_run.sl:1:34: error: compile-time evaluation failed: out of fuel          [column 34 is `(spin`]
ord_run_swapped.sl  (values (same (dive 3000000)) (spin 600000))  -> Fatal error: exception Stack overflow
ord_call_run.sl  (let ((many a)) (two (spin 600000) (same (dive 3000000))))
   -> ord_call_run.sl:2:22: error: compile-time evaluation failed: out of fuel
```

After the first failure slc runs nothing more [READ elab-main.sl:739, 545, 539], so `dive` never ran.

Two cautions. [RAN] This message probe does not work inside function bodies, because there an out-of-fuel
error is a value and the run continues (`ord_body.sl` and `ord_call_body.sl` both end in Stack overflow
whichever ran first); the timing probe was used instead. [RAN] It does not work on the reference at all,
because the reference under `--eval-fuel` overflows its stack on the tail loop alone (`ord_c1.sl`, §2.2).

---

## 5. What is already proved inside slc (item 4)

### 5.1 Every indexed type family in `self/`

[RAN] A grep for every type constructor declared with at least one parameter (`Name : (…) -> Type`):

```
base:   IdMap MapsTo Absent Lookup NameMap NMKid KidIs NoKid KidLookup NotPrefix NMapsTo NAbsent NLookup
        Concat OutOfRange NthLookup Lockstep LockstepDec NameIndex Braun Bounded Pile
escape: EscW EscWidth EscStep EscRun Scan
heap:   Wrap Hist Value Len Suffix Ref StoredBody Store
core:   Picked ManySame PosOf At Mem AtIn Extern Block Frames Group Func Code Shape Branch MemRule AppendR
        MemRuleW Plus3 Pred Pred3 Here Facts In RuledIn Ins Out Taken Inserted Removed C1Here C1 AllRuled
        Keys Looked AboveHere Above Fr FrL FrT FrP FrS FrM Guard GuardL GuardT GuardP GuardS GuardM Ord
        Prefix RuleFound FrBox FrLBox FrTBox FrPBox FrSBox FrMBox Opens Table Added EInfo State Heap
        Outcome SolTypes
eval:   St ApplyParts MacroState Performer
elab:   StmtCode Hoisted ExprDemand DemandBridge Invoke Within Final Sub Steps SrcEntry SrcSg ElseBody
        BranchParts RefuteForm Header Headers Bound AdtHeader AdtHeaders Tids LetParts CtorParts
        RealBranch Atom Ren Drop Kept Given Ann
emit:   Names                reader, elab-main: none
```

[INFERENCE] From the names and the definitions read (those cited below), none of these is a typing
judgement, an evaluation relation, a canonical-form relation, or an erasure relation between source and
code. The definitions of the `elab` families other than `Steps` and `Final` were not read.

### 5.2 Claim by claim

| README claim | The type in the code | What it guarantees | What it does not |
|---|---|---|---|
| "Canonicalization … terminate[s] by proof" | `canon : (subterm erased (List $ Rule) after) (subterm many (Term) t) … -> (many (Term) r) (erased (Fr n f r) fr)` (core.sl:1579-1580) | termination, by the erased suffix of the rules list and then the term; the result's variables are all rule-free entries of the table (`Fr`, core.sl:1343-1355) | that `r` is the canonical form of `t`: any term over rule-free variables has that type. `TErr` and `TSlotOf` are fresh unconditionally (`FrErr`, `FrSlotOf`). A variable with no fact yields `TErr "no fact for x"` (core.sl:1584-1586) |
| "forced unification terminate[s] by proof" | `unify : (subterm erased (Nat) n) … (subterm many (Term) a) … -> (many (Outcome n bnd) r)`; `Less` carries `(erased (Subterm (Nat) k (Nat) n) p)` (core.sl:3880, 3761-3765) | termination: a binding rules one entry out and the count strictly drops | that the resulting table equates `a` and `b`; that `Contra` is one of §7's four cases; anything about which facts were added |
| the fact table "is a trie whose type index counts its rule-free entries", with erased invariants | `Facts n`, `In`, `RuledIn`, `Ins`, `Out` (core.sl:931-976); `Table n f c` holding `Ord`, `Keys`, `AllRuled`, `C1`, `Above` (core.sl:1910-1912) | the trie and the rules list agree; no rule mentions a key at or before it; every key is below the fresh counter. The rules list itself is `erased`: it is a ghost | any relation to DESIGN.md §7's notion of a fact. Inside `Env` the indices are existential (`(erased (Nat) nfree) (erased (Facts nfree) ffacts)`, core.sl:2328), so a function that takes an `Env` knows nothing about its table's index |
| "heap histories" | `Hist`, `Value`, `Len`, `Suffix`, `Ref` (heap.sl:38-58); `alloc … -> … (erased (Suffix B l2 l) sf) (many (Ref B l2) addr)`; `store-read … -> (erased (Hist B) s) (many (B (Ref B s)) body) (erased (Suffix B l s) sf)` | a reference is never dangling; growth is monotone; `store-read` is total; a stamp names one value (`suffix-unique`, `ref-unique`) | anything about what a block contains. A write may store any body valid at the current history (heap.sl:204-207). [QUOTE heap.sl:71-72] "a position names one value: the history has one suffix of each length, and a value sits at the head of the suffix it was allocated onto. Nothing calls these; they are the obligation." |
| "code indexed by scope and erasures" | `Code ctx ms`; `CVar … (many (Mem id ctx) p)`; `CLet … (erased (Picked (Nat) ms ids) pk)` (core.sl:604-612); `eval … -> … (erased (Picked (Ref Block hs2) ms vs) pk)` (elab-main.sl:160) | variable lookup in the interpreter is total (`frames-get`, eval.sl:826-841); a `let` binds exactly the non-erased results; `eval` returns exactly as many values as `ms` has non-erased positions (`vals-one` refutes the empty list, eval.sl:757-760) | well-typedness of the code. `CApp` relates neither the callee's arity nor its results to the call, hence the runtime checks `arity mismatch`, `not a group`, `no such member`, `cannot apply a value that is not a function` (elab-main.sl:410-441); `CMatch` has no coverage evidence (`no branch`, 238, 390); `CConst` is not known to be `Settled` (`unbound constant`, eval.sl:802) |
| "Lockstep" | `Lockstep A B xs ys` (base.sl:558); `list-fit … -> (many (List B) r) (erased (Lockstep A B xs r) p)` (base.sl:595) | two lists have one length, so a walk over both needs no placeholder | nothing about the elements. `lockstep-dec`'s `LdNo` carries no evidence (base.sl:582-583) |
| "evidence-returning lookups" | `idmap-get … -> (many (Lookup V k m) r)` with `Hit … (erased (MapsTo V k v m) p)` and `Miss … (erased (Absent V k m) p)` (base.sl:261-283); `list-nth` gives `Nth` or `OutOfRange`; `length` gives `Length`; `list-append` gives `Concat` (base.sl:520-537, 609-614) | **these are stated against separately defined relations**, and both outcomes carry evidence | they are library facts about maps and lists |
| the `Steps` budget "stated in the type, so the zero case is refuted" | elab.sl:1242-1247 | as claimed | — |
| "a forcing without the merge after it does not type-check" | `Forced` is `Forcing (many (Env) e)` or `Refuted (many (Clash) m)` (core.sl:4103-4106) | only a naming discipline: any code may match `(Forcing env)` and take the `Env` out, as `merge-opens` does (elab.sl:1992) | that the merge happened |
| escape: "Every read and write of both is in bounds by proof" | `escape-into`, `put-bytes` with `Add`, `StrLength`, `Length` indices (escape.sl:80-106) | as claimed, for the lines read | `read-string` (escape.sl:279) was not read |

All rows: [READ at the cited lines].

**Answer to "independent specification or intrinsic invariants?"** [INFERENCE from the table] Intrinsic
invariants everywhere at the level of the language (terms, facts, code, store). Independent relations with
deriving functions exist only for the data-structure library (`IdMap`, `NameMap`, lists) and, by their
signatures in the prelude, for the comparison and string primitives slc calls (`nat-cmp` returns a
`(Cmp (Nat) Lt a b)`, `str-split` takes and returns `StrLength`/`Lt` evidence). [READ lib/prelude.sl:203,
1180]

### 5.3 The internal-error and "believed impossible" paths that remain

[RAN] `grep -n -o 'internal: [^"]*"' *.sl`: 20 messages.

- `elab-main.sl`: 121 (`` `native-compute` of a function with no stored value``), 415 (`an alias applied`,
  an interpreter error block), 505 (`a message built while a check ran quietly`), 735 (`call return
  count`), 1871 (`the sugar budget is spent`), 2770 (`` `coercible-ctor` argument count``).
- `elab.sl`: 984 (`run-position entry … has no value`), 1627 (`` not a `Matchable` ``), 1637 (`no tag
  slot`), 1659 (`not bound at runtime`, a `CError`), 1855 (`return projection size`), 1938 (`reconstruction
  size`), 2029 (`… cannot sit at …`), 2158 (`a minted constant read as a literal`), 2753 and 2758 (a
  contradiction while opening), 4372 (`an unchecked result`), 4791 (`the verified value contradicts the
  facts in force`).
- `eval.sl`: 837 and `emit.sl`: 589 (`an alias with no target`).

[RAN] Counts of the other ways an "impossible" case is absorbed (`grep -c -F`):

```
BError _  (interpreter error blocks):  eval 45, elab-main 3, core 2, interp 2, elab 1, emit 1
CError _  (error nodes in code):       elab-main 33, elab 12, core 1, emit 1
TErr "    (error terms):               elab-main 35, elab 10, core 1, main 1
(absurd   (cases refuted in types):    core 27, escape 8, emit 8, base 6, heap 2, elab-main 2, elab 1, eval 1
```

[READ eval.sl:54-61, 858-863; elab-main.sl:237-244] Some absorbers are silent defaults, not errors:
`heap-nat` answers `0` for a block that is no number, `heap-str` answers the empty string, `field-at`
answers its fallback, `pctor` builds a dummy constructor when a prelude name is missing, and a `CMatch`
whose scrutinee has no readable discriminant runs its first branch.

---

## 6. `main.sl` as a `Program`, and suspending the elaborator (item 5)

### 6.1 Driver steps today

- [READ main.sl:174-191, 159-163, 113-157, 13-30] `start` → `start-with` → `read-files` (a tail-recursive
  loop of `ReadFile` requests) → `compile` → `run-files` (a tail-recursive loop over the files, calling
  `run-toplevel` per file) → messages → `emit-program` → write or `build` → `Exit`. All of it is one
  function application inside one continuation.
- [READ interp.sl:98-114, 119-157] Only `--interpret` yields more steps: `interp-program` returns
  `(Continue _ step)`, where `step` is a `def-unique` closure over the heap and the program's continuation
  that calls `apply` once and then `interp-program` again. Each `Continue` of the interpreted program is one
  step of slc. Plain, thunk, and `String -> String` finals are handled inside the first step.

[RAN] Instrumentation. `stepcount/slc_steps.ml` is `slc-self-1.ml` (slc's output for its own sources) with
line 807 changed from
`let rec loop v = match o.step v with Exit code -> u8 code | Continue k -> loop (o.apply k []) in`
to a version that counts `Continue`s and prints the count to stderr at `Exit`; compiled with
`ocamlfind ocamlopt -package zarith,unix -linkpkg slc_steps.ml -o slc_steps` (13.4 s).

```
$ stepcount/slc_steps order.sl > stepcount/order.ml        -> DRIVER-STEPS (continuations applied): 1   (output identical to release slc's)
$ stepcount/slc_steps --interpret order.sl                 -> DRIVER-STEPS (continuations applied): 1
$ stepcount/slc_steps heads_10001.sl                       -> (the error), DRIVER-STEPS (continuations applied): 1, exit 1
$ printf 'a\nb\nc\n' | stepcount/slc_steps --interpret tests/io_echo.sl   -> DRIVER-STEPS (continuations applied): 5
$ stepcount/slc_steps $SL > stepcount/self.ml              -> DRIVER-STEPS (continuations applied): 1   (output identical to slc-self-1.ml)
```

### 6.2 The pattern for a driver loop already exists in slc

[QUOTE interp.sl:108-114]

```
  (def-unique io-lvl $ (unique step : (unique (World) u at vacant-slot) -> (unique (World) u2 at u) (unique (Program io-lvl) next))
    (let ((erased _) (many hp3) (erased _) (many vs) (erased pk) (unique (ElabWorld) eu)) (apply 0 0 _ fuel _ hp1 f0 (Nil _) many-one _ pf $ MkElabWorld _ $ place-at _ u))
    (let-match unique eu (MkElabWorld _ pu))
    (let ((unique u1)) (unplace-at _ _ _ pu))
    (let-match erased (placed-slot _ _ _ pu) (Refl _ _))
    (tail $ interp-program fuel pcs pf _ hp3 (vals-one _ vs pk) u1))
  (values w (Continue _ step)))
```

[READ interp.sl:60-67, 98, 108] `interp-program` is at `interp-lvl`; the closure `step` it builds is at the
higher `io-lvl` and calls back down into `interp-program`. Nothing recurses through the driver; the state
between steps (heap, continuation value, fuel) lives in the closure. [INFERENCE] A step machine looped by
the driver would have this shape with "one machine step" in place of "`apply` with fuel".

### 6.3 How often the elaborator enters the interpreter

[RAN] `stepcount/slc_count.ml`: the same scratch copy with a counter incremented at the entry of the OCaml
functions emitted for `run-code`, `env-expand`, `apply-answer`, `native-batch`, `eval`, and `apply`, and a
line printed to stderr at each entry of `run-toplevel`. Self-compile, output byte-identical to the release
slc's:

```
last line:  TOP 2515 run=2270 exp=470 cb=8 nat=0 eval=189571 apply=35373
run-toplevel entries: 2515
max run-code calls between consecutive entries: 689 (after entry 822)
max env-expand calls between consecutive entries: 125 (after entry 2444)
max eval calls between entries: 30625 (after entry 2444)
intervals with >=1 interpreter entry: 274   >=2: 171   >10: 23   >100: 4
intervals above 100 run-code or 50 env-expand:  entry 822: run-code +689;  entry 838: run-code +620;
                                                entry 1446: run-code +108;  entry 2444: env-expand +125
```

- [RAN] Top-level forms per file by `grep -c "^("`, cumulative: prelude 358, std/list 385, std/macro 417,
  base 589, escape 627, heap 655, reader 740, core 1320, eval 1496, elab 2194, embed 2202, header 2203,
  emit 2395, elab-main 2437, interp 2471, main 2491.
- [INFERENCE] So entries 822 and 838 are in `core.sl` (the special-form and extern tables are the likely
  forms; not confirmed), entry 1446 is in `eval.sl` (`request-table` fits), and entry 2444 is the main
  block of `elab-main.sl`.
- [RAN] `grep -o '(and \|(or \|$ and \|$ or '` counts 443 textual uses of the `and`/`or` macros in
  `self/*.sl` (strings and comments not excluded), 125 of them inside the main block (lines 158–3234),
  the same number as the expansions at entry 2444.

### 6.4 Is the elaborator's state functional? What happens to the world mid-form?

- [READ core.sl:2325-2332] `Env` is `MkEnv` with the store, scope, entries, table (with erased indices),
  run-position marker, objects, literal table, finals, level, enclosing function, claimed names,
  diagnostics (`List Said`), usage tracking, literals, location, prelude scope, uniqueness state, help
  text, and `Macros`.
- [READ core.sl:2255-2257] `Macros` holds the expansion count, the gensym counter, primitive signatures,
  source names, the fuel, a flag, the goals, the expansion trail, and the native mode.
- [READ core.sl:2444-2665] Every accessor and updater takes and returns `(many (Env) …)`; an update
  rebuilds the record.
- [READ base.sl:255-259; heap.sl:65-69] The maps inside are persistent tries; the store is a counter and a
  persistent map.
- [INFERENCE] So a checkpoint is the `Env` value from before the form, at no cost, and elaborating a form
  is a deterministic function of (`Env`, raw form, answers from the world). Re-running a form from its
  checkpoint reproduces the same stamps, ids, gensym numbers, and expansion counts.
- [READ eval.sl:1492-1494; elab-main.sl:124-128] The one linear value is `ElabWorld`, a newtype over the
  placed `World`, threaded through 78 of the 95 functions of the main block. [RAN: `grep -c`]
- [RAN: Grep for `world-do _` over `self/*.sl`, 42 sites] Sites reachable while a form is being elaborated:
  - `ReadFileIn` in `read-file-answer` (eval.sl:1442), reached from a macro's `read-file`.
  - In `native-run` (elab-main.sl:40-60), reached from `native-compute` (elab-main.sl:873): `Exec` of
    `mktemp -d`, `WriteFile`, `Exec` of `ocamlfind`, `GetEnvs`, `Exec` of the compiled program once per
    argument, `ListDir`, `DeleteFile`, `DeleteDir`.
  - Nothing else. The requests in `perform-request` (eval.sl:1064-1169) are reached only from
    `--interpret`, after elaboration; the rest are in `main.sl` before or after elaboration.
- [READ eval.sl:1518-1526] Run-position user code cannot perform a request: its performer answers with an
  error block.
- [INFERENCE] Abandoning and re-running a form therefore repeats at most file reads and a
  `native-compute` build-and-run. Neither changes anything a later step can see except a temporary
  directory, but a re-run can observe a changed file.

### 6.5 Where a driver-level loop would have to go, and what suspending costs

Facts first. [READ, §3.10] `eval`/`apply` are entered from outside the interpreter at five call sites:
`run-code`'s call of `eval` (445; `run-code` has five callers, one of them the dead `env-run-fields`),
`env-expand`'s call of `apply` (525), and, under `--interpret`, three calls of `apply` in `interp.sl`.
The first two sit below `hop-8` elaborator functions whose callers hold host-stack frames: the main block
has 313 `notail` call sites and 38 `tail` sites. [RAN: `grep -o` on lines 158–3234] The interpreter also
re-enters the elaborator (`apply-answer` → `elab-term`), and that `elab-term` can start another expansion.

DESIGN.md requires values of inner forms before the outer form's elaboration can continue:
[QUOTE DESIGN.md:1178-1187 (§27)] "A form is in run position when it is under no function body and no match
branch. Such a form runs as soon as it has been elaborated, before the code after it is checked: it is
elaborated, its erased positions are stripped, the evaluator runs the code, and its results become `Settled`
with the resulting values (§29). Its code is then those values, so the form around it does not run it
again. A form in an erased position runs nothing, and its results are `Settled` with the token of §5. This
nests: the forms inside a form run before it does, and the statements of a `let`'s right-hand side complete
before the enclosing `let` does." Macro calls expand inside bodies, types, and telescopes too
[READ elab-main.sl:1252, 1774, 1842, 1891, 1938], so a suspension point can lie at any depth of any form.

Options, all [INFERENCE], with the measured sizes that bear on each:

- **A. Make the elaborator a machine too** (explicit continuation frames for the 95 functions). Each of the
  313 non-tail call sites becomes a frame kind carrying the function's indices (`ctx`, `expect`, `root`,
  the `Within`/`Sub` evidence). This is a rewrite of the 3077-line block.
- **B. Replay from a checkpoint.** The driver keeps the `Env` from before a top-level form and a log of
  interpreter answers; elaboration of the form runs until it needs an answer that is not in the log,
  records the request, and (like today's behaviour after an error, where nothing more is run) finishes the
  form with placeholders; the driver loops the step machine on the request, appends the answer, and
  elaborates the form again. The elaborator stays direct-style and total. Cost: a form is re-elaborated
  once per interpreter entry inside it: up to 689 times for the largest table in `core.sl`, and 125 times
  for the 3077-line main block (§6.3), which is 22% of slc's source bytes (310836 of 1409411).
  Finer checkpoints, or treating macro expansion separately (the handoff's open question on keeping fuel
  for macros), would be needed to make this usable.
- **C. Keep the elaborator, make only the interpreter an explicit-stack machine, and loop it in place.**
  This removes the host-stack overflow (H2) but the in-place loop still needs a bound, so the fuel becomes a
  step count and stays semantic.
- **D. Keep everything, and let the driver retry with more fuel.** When a run exhausts its fuel, mark the
  form "needs more fuel" (again like a failure: nothing further runs), return to the driver, and re-elaborate
  that one top-level form from its checkpoint with the fuel doubled. No `out of fuel` is ever reported; the
  compile loops exactly when the compile-time code does. Cost: one re-elaboration per doubling, only for
  forms that exhaust the fuel, which no form of the self-compile does at any realistic starting fuel (the
  whole self-compile makes 189571 `eval` calls). It does not make each step total, does not fix the host
  stack unless combined with C, and repeats a form's `read-file`/`native-compute` effects on retry.

What each option needs from the state is what §6.4 found: checkpoints are free, and determinism holds up to
the two effects.

A per-step batch size ("run at most N machine steps, then yield to the driver") would be a `Nat` that
decreases, but running out of it is not an error and changes nothing the user sees. [INFERENCE]

---

## 7. Size and speed (item 6)

[RAN] `wc -l -c`:

```
base.sl 1148 lines / 68860 bytes      escape.sl 317 / 20593      heap.sl 253 / 15716      reader.sl 742 / 43074
core.sl 4133 / 316789                 eval.sl 1652 / 118112      elab.sl 5139 / 362936    header.sl 6 / 458
emit.sl 1516 / 100652                 elab-main.sl 3398 / 334587 interp.sl 157 / 11741    main.sl 191 / 15893
total self/*.sl: 18652 lines, 1409411 bytes.   self/README.md: 467 lines.
also compiled in: lib/prelude.sl 2881 lines, std/list.sl 206, std/macro.sl 188, lib/embed.sl 27; runtime.ml 21.
```

- [RAN] The main block of `elab-main.sl` is lines 158–3234: 3077 lines, 310836 bytes, **95 functions**
  (awk over the function headers). Cross-check: the OCaml group `a53182` in slc's output for itself has 95
  `let rec`/`and` members.
- [RAN] By `hop`: 6 at `hop-0` (the interpreter), 2 at `hop-1`, 6 at `hop-2`, 4 at `hop-3`, 4 at `hop-4`, 2
  at `hop-5`, 3 at `hop-6`, 1 at `hop-7`, 66 at `hop-8` (the elaborator proper), 1 at `hop-9`
  (`apply-answer`). The interpreter's six functions occupy lines 159–441.
- [RAN] slc's output for itself has 1875 top-level OCaml functions in 1689 `let rec` groups, 9639 lines,
  3758994 bytes.
- [RAN] `def-fns` forms per file (`grep -c "^ *(def-fns"`): base 141, escape 28, heap 25, reader 74, core
  490, eval 163, elab 664, emit 178, elab-main 52, interp 16, main 18.

[RAN] slc compiling its own sources, from `/home/user/sleight`, with
`SL="std/list.sl std/macro.sl self/base.sl self/escape.sl self/heap.sl self/reader.sl self/core.sl
self/eval.sl self/elab.sl lib/embed.sl self/header.sl self/emit.sl self/elab-main.sl self/interp.sl
self/main.sl"` (the `SL=` line of `self/release.sh`) and
`/usr/bin/time -f "… wall %e s, user %U s, sys %S s, maxrss %M KB, exit %x" _build/release/slc $SL > $P/slc-self-$i.ml`:

```
run 1: wall 5.08 s, user 4.90 s, sys 0.13 s, maxrss 214284 KB, exit 0
run 2: wall 5.56 s, user 5.35 s, sys 0.13 s, maxrss 214104 KB, exit 0
run 3: wall 5.41 s, user 5.18 s, sys 0.14 s, maxrss 214248 KB, exit 0
```

The three outputs are byte-identical (`cmp`), 3758994 bytes each; stderr was empty apart from the timing
line.

[RAN] The reference on the same sources, `timeout 600 _build/default/bin/main.exe $SL`:

```
slc: usage: slc [--no-prelude] … > out.ml
ref plain: wall 97.24 s, user 95.91 s, sys 0.17 s, maxrss 88728 KB, exit 1
```

The usage line and exit 1 are expected: after checking the files the reference runs their final value,
which is slc's own `Program`, with no arguments. Other experiments of this agent ran on other cores during
this measurement, and other agents share the machine (load average was about 1.2), so the 97 s may be
somewhat inflated. [INFERENCE]

---

## 8. Where `self/README.md` and the code disagree

- [QUOTE README.md:254-257] "**Termination is structural except in the interpreter and the generated
  printer.** Those two take a `Nat` that decreases along the call stack (not a step count), so a fuel of
  1000000 or 100000 bounds depth, not work". [READ core.sl:3614] The default interpreter fuel in the code is
  `1000000000`. [RAN] `grep -n -i` over `README.md` for `fuel|budget|depth` and for the names of the
  functions in rows 8–12 and 14–16 finds no mention of those rows' budgets anywhere in the file.
- [QUOTE README.md:257-258] "running out returns an error value, never a wrong answer silently". [RAN] H5,
  and [READ] rows 9 (two sites), 11, 14, 15, 16, are silent.
- [QUOTE README.md:85-91] "`heap.sl` — a store for the compile-time interpreter, parametric in its block
  type: addresses below a bound, carried as their bijective spelling with erased `Numeral` and `Lt` proofs,
  widened by a `coerce`; and a Braun tree of blocks sized by its count". [READ heap.sl:1-207] The file
  now has stamps in a ghost history, references that hold the value itself, and an overlay map of writes;
  it has no Braun tree and no `Numeral`.
- [QUOTE eval.sl:481-482] "The dispatch below has one case per Extern and no else, so a new one has to say
  which." [READ eval.sl:663] The `match` in `apply-extern` ends in an `else`.
- [QUOTE main.sl:122] "--eval-fuel takes a number of steps". [RAN, §2.2] The flag bounds depth.
- [QUOTE README.md:385-386] "**The elaborator's group carries a budget of sugar expansions** as its first
  `subterm` parameter, ahead of the raw." [READ elab-main.sl:752] In the code `sugar` is the fourth
  `subterm` parameter of an elaborator function, after the expansion budget, `callbacks`, and `hop-8`.

---

## 9. Things I am least sure of

1. **Unread code.** About 45% of `elab-main.sl`'s main block, most of `elab.sl`, most of `core.sl`, and most
   of `emit.sl` and `base.sl` were searched, not read (§0). The census is exhaustive for `Nat`-typed
   `subterm` parameters and for the listed keywords. A budget carried as a non-`Nat` value other than
   `Steps`, or a `Nat` budget that is not marked `subterm` and not named by any of the keywords, would have
   escaped it.
2. **Reachability claims.** "Believed unreachable" for rows 8, 9, 10, 14, 15, and 16, and for the `else` of
   `apply-extern`, is my reasoning, not something the types or a test establish. Row 9 and row 10 assume the
   store has no cycle through `BTag` fields; whether a `cell-write` can build one was not determined.
   [UNKNOWN]
3. **Row 13.** I did not construct a program that exhausts the generated printer's fuel, so "(a) in
   principle" is from reading `show-type`; what such a program does in practice (it may instead run very
   long) is [UNKNOWN].
4. **Order probes.** §4.3 observes order only through which crash arrives first, and the body-level result
   for `values` rests on one timing pair per implementation (2.63 s against 0.39 s for slc). The emitted
   OCaml (§4.2) and the code (§4.1) agree with it. I did not test `unique` positions, cell forms, or
   `world-do`.
5. **The reference.** Statements about the reference come from running it and from `MANUAL.md`; I did not
   read `lib/eval.ml`. In particular the explanation of its stack overflow on tail loops under `--eval-fuel`
   is a guess.
6. **Which forms are the heavy ones in §6.3.** The file is certain to within the accuracy of the cumulative
   counts (2491 counted forms against 2515 entries); the specific form is a guess.
7. **Option costs in §6.5.** The option list is mine, and the costs are extrapolated from counts in one
   self-compile; no option was prototyped.
8. **`Fr`'s strength.** I read `Fr`'s constructors and `canon`'s signature, not the `Guard`/`Ord` lemmas
   that make the chase total, so "guarantees termination" for `canon` rests on the function type-checking
   under the reference (it does: the release slc was built from it), not on my having followed the proof.
