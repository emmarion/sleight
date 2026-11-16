# A2: how the reference runs programs, and whether sibling evaluation order is observable

Agent A2, 2026-11-16. Everything below about `lib/`, `bin/`, `self/`, and the prebuilt binaries is
**implementation behaviour**, never the language's definition. `DESIGN.md` is quoted where it speaks, and
"DESIGN.md is silent" is said where it does not. Nothing inside `/home/user/sleight` was modified.

Scratch directory (all programs, scripts, and logs):
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A2/` (called `A2/` below).

Tags: `[QUOTE file:line]`, `[RAN]`, `[READ file:lines]`, `[INFERENCE]`, `[UNKNOWN]`, as the common brief defines them.

---

## 0. The findings that matter most

1. **An accepted program can observe sibling order, by three routes. None goes through a value the program
   computes.**
   - Which requests reach the outside before a crash. `[RAN]` `A2/observe_order_crash_1.sl` holds
     `(values (say w "A\n") (deep 100000))` and prints `A` before it runs out of fuel or stack;
     `A2/observe_order_crash_2.sl` holds `(values (deep 100000) (say w "A\n"))` and prints nothing before
     the same crash. All five runs agree (§3.4).
   - The answer of a host-dependent request, with no crash. `[RAN]` `A2/observe_order_measure_1.sl` and
     `A2/observe_order_measure_2.sl` differ only in the order of two `values` entries and print
     `measured BEFORE the build` and `measured AFTER the build` (a `Measure` reading against a sibling
     that allocates 200000 list cells).
   - At compile time, `gensym` numbers show the order in which sibling macro calls are expanded (§3.6).
2. **I found no accepted program that observes sibling order through the language's own effects**
   (the sequence of `world-do` requests, in-place mutation through `unique` cells and extern arrays,
   `slot-eq` answers, closures over unique values). `[RAN]` Of 27 attack programs, 22 were rejected by
   both checkers (the usual error: ``unique value `x` has conflicting non-erased uses``), and the 3 accepted
   order probes printed the same output for both textual orders in all five runs (§3.5). This is evidence,
   not proof.
3. **Major: the reference and slc evaluate in different orders.** slc moves the input of a `cell-write`,
   the items of a `cell-write`, and the items of a `cell-alloc` to before the whole enclosing statement;
   the reference evaluates them where they stand. `[RAN]` `A2/repro_cellwrite_order.sl`: the reference
   (interpreter, `--no-extern`, and `--build`) prints `A` before the crash, slc (`--build` and
   `--interpret`) prints nothing. `[RAN]` `A2/repro_cellwrite_order_measure.sl`, no crash: the reference
   prints `measured BEFORE the build`, slc prints `measured AFTER the build`. Details in §3.2.
4. **Neither implementation runs a body's form "left to right, each sub-expression completely before the
   next".** Both first run every argument temporary of the whole statement or final form (head forms and
   non-variable arguments, left to right, innermost first), then evaluate what remains where it stands.
   `[RAN]` `A2/observe_hoisting_crash.sl` holds `(values (say w "A\n") (id-nat (deep 100000)))`: in all
   five runs the crash comes before `A` is printed, so `(deep 100000)`, nested in the second entry, ran
   before the first entry. `[INFERENCE]` Under the handoff's proposal A ("left to right, each completely
   before the next") this program would print `A` first, so proposal A describes neither implementation.
5. **The same form runs in a different order at the top level than in a function body, in both
   implementations.** `[RAN]` `(values (deep 100000) (id-nat (boom 7)))` at the top level runs `deep`
   first; inside a function body it runs `boom` first (§3.3).
6. **What DESIGN.md fixes** (the quotes are in §2). Run position: a form runs as soon as it is elaborated,
   inner forms first (§27). Elaboration: the head first (§6). Bodies: each argument is bound by a
   statement placed just before the statement or final form that contains the call (§15). Evaluation is
   eager (§31). `[INFERENCE]` from greps and one full reading: **DESIGN.md is silent** on the order
   among the argument bindings of one statement, the order of the entries of a `values`, head versus
   arguments at run time in a body, when the input and items of a `cell-write` or the items of a
   `cell-alloc` are evaluated, and (in so many words) that a body's statements run in textual order (§2).
7. **In `lib/eval.ml`, one expression leaves an order to the OCaml compiler:**
   `apply (eval1 env f) (List.map (eval1 env) args)`. `[RAN]` As built here it evaluates the arguments
   (left to right) and then the head. `[READ lib/elab.ml:1136-1142, 1412-1423]` The elaborator only ever
   puts variables there, so this cannot be seen from a program (§4.1).
8. **Heap.** `[READ lib/value.ml:14-25, 91-94; lib/eval.ml:47-55, 61; lib/elab.ml:1662-1695, 2654-2669]`
   The reference's heap is the OCaml heap: a constructor value with fields is
   `VCtor of ctor * value array`, a `unique` `cell-write` and a `unique` cell invocation assign into that
   array, `slot-eq` is OCaml `==`, `cell-same` and `fn-same` compile to nothing, and a `delegate`-bodied
   function is the same closure value as its callee (§4.3). `[RAN]` All five runs agree on eight
   `slot-eq` questions about identity (`A2/heap/`).
9. **Other disagreements noticed** (`[RAN]` and `[READ]` evidence in §5): slc's interpreter keeps
   evaluating after a fuel error where the reference stops; `slot-eq` answers differ among the reference
   interpreter, compiled code, and slc's interpreter; under `--no-extern` every `Measure` reading is 0.

---

## 1. How the runs were made

`REF=/home/user/sleight/_build/default/bin/main.exe`, `SLC=/home/user/sleight/_build/release/slc`.

`[RAN]` `for f in eval value elab extract driver_core program ffi ffi_core ffi_templates term env special prelude; do diff -q lib/$f.ml _build/default/lib/$f.ml; done; diff -q lib/prelude.sl _build/default/lib/prelude.sl`
printed no difference: the sources I read are the ones the prebuilt reference was built from.
`[UNKNOWN]` Whether `_build/release/slc` was built from the `self/*.sl` now in the tree; I did not check.

The five runs, named as the task names them:

| name | command |
|---|---|
| (a) | `$REF f.sl` |
| (b) | `$REF f.sl --no-extern` |
| (c) | `$REF f.sl --build prog && ./prog` |
| (d1) | `$SLC f.sl --build prog && ./prog` |
| (d2) | `$SLC --interpret f.sl` |

Crash probes add a limit so that a 100000-deep non-tail recursion crashes: `--eval-fuel 2000` for (a),
(b), and (d2); `bash -c "ulimit -s 64; exec ./prog"` for (c) and (d1). The scripts are
`A2/order/probe.sh` (print, then crash), `A2/order/probe3.sh` (two different crashes), and
`A2/order/plain5.sh` (no limit). Their outputs are kept in `A2/order/probe_run1.log` to
`probe_run8.log`, and `A2/attacks/attacks_summary.log`.

Three building blocks recur. `[RAN]` All were accepted by both checkers (every probe below ran).

```scheme
; A World packed into one unique value (after self/eval.sl:1492-1494's ElabWorld), so that a size-one
; expression can perform I/O and hand the world back.
(def-adts $ (WBox : -> Type)
  enum newtype
  (many MkWBox : (erased (World) w) (unique (Placed vacant-slot (World) w) p) -> (WBox)))
(def-fns _ $ (many say : (unique (World) w at vacant-slot) (many (String) s) -> (unique (WBox) b))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut s)))
  (MkWBox _ (place-at _ w1)))
; n-deep non-tail recursion: "out of fuel" under --eval-fuel, "Stack overflow" in compiled code.
(def-fns _ $ (many deep : (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many n (Succ m) ((Zero) 0))
  (Succ (notail $ deep m)))
; A crash of another kind: every implementation tried reports Z.Overflow.
(def-fns _ $ (many boom : (many (Nat) k) -> (many (Nat) r)) (nat-shl k 4611686018427387904))
```

---

## 2. What DESIGN.md says about order

`[RAN]` Searches over `DESIGN.md`:
`grep -n -i -E "\border\b|\bordered\b|ordering|sequential|sequentially|sequence|eager|left to right|right to left|left-to-right|as soon as"`
(33 matching lines), and
`grep -n -i -E "evaluat|\bbefore\b|\bafter\b|\bfirst\b|\bthen\b|\bruns?\b|\bran\b|running|\bonce\b|complete"`
(251 matching lines), and
`grep -n -i -E "in (the )?order|one after|lazy|call-by|side effect|\beffects?\b|deterministic|nondetermin|unspecified|not specified"`
(13 matching lines). I read every matching line. I also read all of `DESIGN.md` once in full tonight. The statements that bear on the order of evaluation
or of elaboration:

**Elaboration order and run position**

- `[QUOTE DESIGN.md:236]` §6: "1. The head is elaborated first."
- `[QUOTE DESIGN.md:240-242]` §6: "A head that is a form is `Settled` in run position, since it runs as soon as it is elaborated (§29)"
- `[QUOTE DESIGN.md:1179-1180]` §27: "Such a form runs as soon as it has been elaborated, before the code after it is checked"
- `[QUOTE DESIGN.md:1185-1187]` §27: "This nests: the forms inside a form run before it does, and the statements of a `let`'s right-hand side complete before the enclosing `let` does."
- `[QUOTE DESIGN.md:1192-1194]` §27: "The binders of a run-position statement declare their multiplicities (§19), which is what allows the statement to be stripped and run before the code after it is elaborated."
- `[QUOTE DESIGN.md:1202-1203]` §28: "Everywhere else, in run position (§27), each of them runs as soon as it is elaborated and its results are `Settled`"
- `[QUOTE DESIGN.md:1301-1302]` §29: "Round trips nest: a form in run position runs before the form that contains it."
- `[QUOTE DESIGN.md:1355-1356]` §32: "A top-level binder, which is a `Settled` (§29), may be `unique` under the same rules, since run-position statements are sequential."
- `[QUOTE DESIGN.md:2321-2322]` §50: "and an argument (its parameter, given the arguments before it)" (about what an expectation may use, not about running).

**Bodies**

- `[QUOTE DESIGN.md:655-661]` §15: "Every argument to a constructor, a function or a cell behaves as if it were first bound to an anonymous variable. An argument that is already a variable is not rebound. That binding is a statement (§27) placed just before the statement or final form that contains the call, so its entry stays in scope, anonymously, for the rest of the expression around it, as the entries of a `let`'s right-hand-side statements do."
- `[QUOTE DESIGN.md:1105]` §27: "An expression is a series of **statements** followed by a final form."
- `[QUOTE DESIGN.md:1129-1130]` §27: "Those statements run, or their code is emitted, whether or not the `let`'s own binders are erased."
- `[QUOTE DESIGN.md:1319]` §31: "Evaluation is eager."
- `[QUOTE DESIGN.md:1652-1654]` §36: "At a call, the argument for a parameter written `at` is elaborated at the parameter's multiplicity and its uses count like any argument's. If it is not a variable, it is bound first."
- `[QUOTE DESIGN.md:1843-1844]` §39: "Calling an at-function skips its runtime; its arguments are still evaluated, as §15 binds them."
- `[QUOTE DESIGN.md:1895-1896]` §40: "The match skips its runtime: its scrutinee is evaluated as for any match"
- `[QUOTE DESIGN.md:2717-2718]` §61: "The write stores `h` before the call: left to the invocation, that store would follow the call and the `tail` claim would fail."
- `[QUOTE DESIGN.md:1335-1336]` §32: "consumed by the definition itself, where the `def-unique` is elaborated, not at each call"

**Checking, which is explicitly order-free**

- `[QUOTE DESIGN.md:620-621]` §15: "Each binder is checked by the uses it has on each path through the code. The order of the uses does not matter."

**Crashes, the driver, and things allowed to vary**

- `[QUOTE DESIGN.md:1319-1323]` §31: "The semantics is that of a machine with unlimited stack and heap. A real run may crash where the host cannot represent what is asked of it. A crash produces no value, never a different one. How a crash is reported is not specified; it need not be a runtime error."
- `[QUOTE DESIGN.md:1166-1167]` §27: "the driver consumes it at `unique` and applies each step's continuation once."
- `[QUOTE DESIGN.md:1993-1994]` §42: "The driver flushes after every write. It never recurses, so an unbounded interaction is the driver's loop over total functions."
- `[QUOTE DESIGN.md:1952-1955]` §42: "except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31)."
- `[QUOTE DESIGN.md:3044-3046]` §67: "`ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs."

**Compile time**

- `[QUOTE DESIGN.md:2884-2886]` §65: "It is threaded sequentially through all of elaboration, carried out of every scope where uses are carried, and passed along rather than joined."
- `[QUOTE DESIGN.md:2928]` §65: "`gensym` mints a number, counting from 1 over the whole run, every file"
- `[QUOTE DESIGN.md:283-284]` §7: "Compile-time effects in unreachable code still happen."

**Where DESIGN.md is silent.** `[INFERENCE]` Resting on the greps above and one full reading; a sentence I
missed would refute it. I found no sentence that states:

1. the order of the argument-binding statements of §15 among themselves (two arguments of one call, or
   arguments of two calls in one statement);
2. the order in which the entries of a `values` are evaluated ("left to right" occurs once in the file,
   at line 699, about the lexicographic termination order);
3. whether, in a body, a head that is a form runs before the arguments (§6 line 236 is about
   elaboration; in run position §27 turns elaboration order into run order);
4. when the cell and the items of a `cell-write`, or the items of a `cell-alloc`, are evaluated relative
   to the rest of their statement (they are not "arguments to a constructor, a function or a cell", so
   §15 does not obviously cover them);
5. in so many words, that the statements of a function body execute in the order written. The nearest
   are §27's scoping ("visible to the rest of that expression"), §61 line 2717, and §32 line 1356, which
   speaks of run-position statements only.

`[INFERENCE]` For run position, §27 lines 1179-1187 together with §6 line 236 do fix an order (head, then
the rest in the order the elaborator checks it, inner forms first), provided "the code after it" means
textual order. Both implementations run top-level forms that way (§3.3).

A note from an earlier session, not an owner decision: `[QUOTE ASSUMPTIONS.md:1589-1593]` "The source
language is pure and specifies no observable evaluation order. Destructive updates implement that pure
semantics; their execution order must not be observable in well-typed programs. The interpreter's
traversal order is an implementation choice." `[QUOTE handoff.md:50]` "The session wrongly relied on item
168 for "the language is pure and order-free"." Findings 1 and 3 above are concrete data against which
the note can be judged.

---

## 3. The experiment

### 3.1 The order each implementation uses, measured

All rows are inside a function body unless marked "top level". "First" means which sibling ran first.
`A` means the first `values` entry `(say w "A\n")` printed before the crash. Sources: `A2/order/*.sl`;
outputs: `A2/order/probe_run1.log`, `probe_run2.log`, `probe_run5.log`, `probe_run6.log`,
`probe_run8.log`.

`[RAN]` `cd A2/order; ./probe.sh NAME` (print, then crash; five runs each):

| probe | form under test | (a) | (b) | (c) | (d1) | (d2) | reading |
|---|---|---|---|---|---|---|---|
| `v1` | `(values (say w "A\n") (deep 100000))` | A | A | A | A | A | entries left to right |
| `v2` | `(values (deep 100000) (say w "A\n"))` | – | – | – | – | – | entries left to right |
| `c1` / `c2` | `(keep (say …) (deep …))` / `(keep2 (deep …) (say …))` | A / – | A / – | A / – | A / – | A / – | call arguments left to right |
| `k1` / `k2` | `(MkBN (say …) (deep …))` / `(MkNB (deep …) (say …))` | A / – | A / – | A / – | A / – | A / – | constructor arguments left to right |
| `i1` / `i2` | `(cell (say …) (deep …))` / `(cell (deep …) (say …))` | A / – | A / – | A / – | A / – | A / – | cell-invocation arguments left to right |
| `h1` | `((pick (deep …)) (say …))` | – | – | – | – | – | head form before the argument |
| `h2` | `((say-fn w "A\n") (deep …))` | A | A | A | A | A | head form before the argument |
| `n1` | `(values (say …) (id-nat (deep …)))` | – | – | – | – | – | nested argument of a later entry runs before the earlier entry |
| `n4` | `(values (deep …) (id-box (say …)))` | A | A | A | A | A | nested argument of a later entry runs before the earlier entry |
| `m1` | `(values (say …) (match many (id-nat (deep …)) …))` | – | – | – | – | – | nested argument of a scrutinee is moved out too |
| `m2` / `m3` | `(values (say …) (match many (deep …) …))` and swapped | A / – | A / – | A / – | A / – | A / – | a scrutinee's own call stays in place |
| `p7` | `(values (say …) ((pick (deep …)) 5))` | – | – | – | – | – | a head form in a later entry is moved out |
| `p8` | `(values (say …) ((deep-cell …) 1 2))` | – | – | – | – | – | a cell head form too |
| `p9` | `(values (say …) (slot-eq (deep-slot …) vacant-slot))` | – | – | – | – | – | a primitive's argument too |
| `p5` | `(values (say …) (share (deep-cell …)))` | A | A | A | A | A | `share`'s operand stays in place |
| `p6` | `(values (say …) (cell-match unique (deep-cell …) …))` | A | A | A | A | A | `cell-match`'s input stays in place |
| **`p1`** | `(values (say …) (cell-write unique (deep-cell …) (MkS2 _ _)))` | A | A | A | **–** | **–** | **`cell-write` input: in place in the reference, moved out in slc** |
| **`p2`** | `(values (say …) (cell-alloc (MkS2 (deep-slot …) _)))` | A | A | A | **–** | **–** | **`cell-alloc` item: same split** |
| **`p3`** | `(values (say …) (cell-write unique c0 (MkS2 (deep-slot …) _)))` | A | A | A | **–** | **–** | **`cell-write` item: same split** |
| `g1` | `(match many n … ((Succ _) (id-nat (deep …))))` with `n = 0` | 8 | 8 | 8 | 8 | 8 | nothing is moved out of a branch that is not taken |

`[RAN]` `cd A2/order; ./probe3.sh NAME` (two crashes: `deep` shows as `out of fuel` in (a) and as
`Stack overflow` elsewhere; `boom` shows as `Z.Overflow` everywhere; (b) not run, because `boom`'s numeral
2^62 cannot be built without the extern `Nat`: `./plain5.sh at15_slot_eq_across_implementations`, which
holds the same numeral, died with `Fatal error: exception Z.Overflow` in run (b)):

| probe | form under test | (a) | (c) | (d1) | (d2) | reading |
|---|---|---|---|---|---|---|
| `x1` / `x2` | `(cell-write unique (deep-cell …) (MkS2 (boom-slot 7) _))` and roles swapped | deep / boom | deep / boom | deep / boom | deep / boom | input before items |
| `x3` / `x4` | `(cell-write unique c0 (MkS2 (deep-slot …) (boom-slot 7)))` and swapped | deep / boom | deep / boom | deep / boom | deep / boom | items left to right |
| `x6` / `x7` | `(cell-alloc (MkS2 (deep-slot …) (boom-slot 7)))` and swapped | deep / boom | deep / boom | deep / boom | deep / boom | items left to right |
| **`x5`** | `(cell-write unique (deep-cell …) (MkS2 (id-slot (boom-slot 7)) _))` | **boom** | **boom** | **deep** | **deep** | **nested argument of an item: before the input in the reference, after it in slc** |
| **`x5b`** | `(cell-write unique (boom-cell 7) (MkS2 (id-slot (deep-slot …)) _))` | **deep** | **deep** | **boom** | **boom** | **the same split** |
| `x8` / `x9` | `(values (deep …) (id-nat (boom 7)))` / `(values (boom 7) (id-nat (deep …)))` | boom / deep | boom / deep | boom / deep | boom / deep | nested argument first, as `n1` |
| `x10` / `x11` | `(add2 (deep …) (boom 7))` / `(add2 (boom 7) (deep …))` | deep / boom | deep / boom | deep / boom | deep / boom | arguments left to right |

`[INFERENCE]` Summary of the rule both implementations follow in a body, read off the two tables and the
code of §4.1: within one statement or final form, (1) every head that is a form and every non-variable
argument of a call, constructor application, cell invocation, `world-do`, or primitive is evaluated first,
in left-to-right, innermost-first order, head before arguments; (2) then what remains is evaluated where it
stands: the entries of a `values` left to right, a match's scrutinee, the operand of `share`, the input
of `cell-match`. The two implementations differ on which group the input of `cell-write` and the items
of `cell-write` and `cell-alloc` belong to (§3.2).

### 3.2 Major finding: the reference and slc disagree on order

Minimal reproduction, `A2/repro_cellwrite_order.sl` (the three building blocks of §1, then):

```scheme
(def-adts $ (S2 : -> Type) enum (many MkS2 : (many (Nat) x) (many (Nat) y) -> (S2)))
(def-fns _ $ (many deep-cell : (many (Nat) n) -> (unique (Cell MkS2 vacant-slot vacant-slot) c))
  (let ((many _)) (deep n))
  (cell-alloc MkS2))
(def-lvl P)
(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique b) (unique _c)) (values (say w "A\n") (cell-write unique (deep-cell 100000) (MkS2 _ _))))
  (let-match unique b (MkWBox _ pw))
  (let ((unique w1)) (unplace-at _ _ _ pw))
  (let-match erased (placed-slot _ _ _ pw) (Refl _ _))
  (let ((unique w3) (many _)) (world-do _ w1 (WriteOut "end\n")))
  (values w3 (Exit P code0)))
(Continue P start)
```

`[RAN]` in `A2/`:

```
$ main.exe repro_cellwrite_order.sl --eval-fuel 2000
A
repro_cellwrite_order.sl: runtime error: out of fuel            [exit 1]
$ main.exe repro_cellwrite_order.sl --no-extern --eval-fuel 2000
A
repro_cellwrite_order.sl: runtime error: out of fuel            [exit 1]
$ slc --interpret repro_cellwrite_order.sl --eval-fuel 2000
slc: runtime error: out of fuel                                 [exit 1]
$ main.exe repro_cellwrite_order.sl --build rc_ref && (ulimit -s 64; ./rc_ref)
A
Fatal error: exception Stack overflow                           [exit 2]
$ slc repro_cellwrite_order.sl --build rc_slc && (ulimit -s 64; ./rc_slc)
Fatal error: exception Stack overflow                           [exit 2]
$ main.exe repro_cellwrite_order.sl            (no limit)
A
end                                                             [exit 0]
$ slc --interpret repro_cellwrite_order.sl     (no limit)
Fatal error: exception Stack overflow                           [exit 2]
```

The same split without any crash, `A2/repro_cellwrite_order_measure.sl`, whose `start` holds
`(values (measure w) (cell-write unique (build-cell 200000) (MkS1 _)))` and prints which side of the
200000-cell build the `Measure` reading fell on:

`[RAN]` in `A2/`:

```
$ main.exe repro_cellwrite_order_measure.sl                              measured BEFORE the build
$ main.exe repro_cellwrite_order_measure.sl --build m_ref && ./m_ref     measured BEFORE the build
$ slc --interpret repro_cellwrite_order_measure.sl                       measured AFTER the build
$ slc repro_cellwrite_order_measure.sl --build m_slc && ./m_slc          measured AFTER the build
```

The generated OCaml shows the cause.

`[RAN]` `$REF p1_values_say_cellwrite_input_deep.sl --extract out/p1_ref.ml` (in `A2/order`), the body of
`start`:

```ocaml
let x157_a0 = (v40764_say l40902)
and x157_a1 = (let v40936 = (v40844_deep_cell l40904) in (let cell156 = v40936 in cell156))
in (to_any (x157_a0, x157_a1))
```

`[RAN]` `$SLC p1_values_say_cellwrite_input_deep.sl > out/p1_slc.ml`, the body of `start`:

```ocaml
(let v42251___42251__ = (v42153_deep_cell_a1577 a1590) in
 (let (v42255_b, v42257__c) = (of_any
    (let tup3_a0 = (v42071_say_a1567 a1589) in
     let tup3_a1 = (let cell3 = v42251___42251__ in cell3) in (to_any (tup3_a0, tup3_a1))) ...
```

`[READ lib/elab.ml:1620-1636]` The reference emits `CLet ([input_id], input, wrap (CCellWrite …))` for a
`cell-write`: the input is bound by a `let` inside the form's own code.
`[READ lib/elab.ml:1989-2004]` Its `cell_items` binds each item in a local `wrap` around the write, in
source order.
`[READ self/elab-main.sl:1512-1552]` slc's `elab-cell-write` returns
`(MkHoisted _ _ bctx (SSeq _ _ _ ipre $ SSeq _ _ _ ssc ipre2) …)`: the input's own temporaries, then the
input (`ssc`, from `hoist-unplaced`, line 1527), then the items (`ipre2`), all as statements to be placed
before the enclosing statement.
`[READ self/elab-main.sl:1392-1421]` slc's `elab-cell-items` passes each item through `hoist-unplaced`
(line 1413).

`[INFERENCE]` DESIGN.md does not say which is right (§2, silence item 4). The difference cannot change a
value the program computes unless sibling order can (§3.7); it changes what precedes a crash and what a
host-dependent request answers.

`[UNKNOWN]` Whether other forms differ between the two. The forms tried are the rows of §3.1.

### 3.3 Top level versus body

`[RAN]` `A2/order/probe_run3.log`, each file run as `$REF f.sl --eval-fuel 2000` and
`$SLC --interpret f.sl --eval-fuel 2000` (here `boom` is the array version in `A2/order/boom.inc`,
which the reference reports as `Z.Overflow` and slc's interpreter as `Stack overflow`):

| file | form | where | reference | slc |
|---|---|---|---|---|
| `t3_top_values_deep_nested_boom` | `(values (deep 100000) (id-nat (boom 7)))` | top level | `out of fuel` (deep first) | `compile-time evaluation failed: out of fuel` (deep first) |
| `t4_top_values_boom_nested_deep` | `(values (boom 7) (id-nat (deep 100000)))` | top level | `Z.Overflow` (boom first) | `Stack overflow` (boom first) |
| `b3_body_values_deep_nested_boom` | the form of `t3` | function body | `Z.Overflow` (boom first) | not decisive (§5, item 2) |
| `b4_body_values_boom_nested_deep` | the form of `t4` | function body | `out of fuel` (deep first) | not decisive |

`[RAN]` For slc in a body, `x8` and `x9` of §3.1 are decisive and agree with the reference: the nested
argument runs first.

`[READ lib/elab.ml:1338, 1341-1355]` In run position the reference's `elab_expr` calls `run_form` on
every sub-form as soon as it has elaborated it, and replaces its code by the resulting value.
`[READ lib/elab.ml:1141, 1422]` In run position an argument or head is not added to `pending`; in a body it
is. So at the top level the order is the elaborator's own traversal (left to right, inner first), and in a
body the temporaries are moved to before the statement.

`[INFERENCE]` Both orders agree with DESIGN.md as far as it speaks: §27 for run position, §15 for bodies.
They are two different orders for the same text.

### 3.4 The routes by which order is observed

**Crash prefix.** `[RAN]` `./probe.sh v1_values_say_deep` and `./probe.sh v2_values_deep_say`: stdout is
`A` then a crash in all five runs for `v1`, and empty then a crash in all five for `v2`
(`A2/order/probe_run1.log`; copies of the programs: `A2/observe_order_crash_1.sl`,
`A2/observe_order_crash_2.sl`). Without a limit both print `A` and `100000`. `[RAN]`
`$REF v1_values_say_deep.sl` printed `A`, `100000`.

**Host-dependent answers.** `[RAN]` `./plain5.sh q1_measure_values_measure_build` printed
`measured BEFORE the build` in all five runs; `./plain5.sh q2_measure_values_build_measure` printed
`measured AFTER the build` in (a), (c), (d1), and (d2), and `measured BEFORE the build` in (b)
(`A2/order/probe_run7.log`). The (b) line is §5 item 4, not an order effect: under `--no-extern` the
reading is always 0.
`[RAN]` `./plain5.sh q3_measure_values_measure_nested_build`
(`(values (measure w) (id-list (build 200000 (Nil _))))`) printed `measured AFTER the build` in (a),
(c), (d1), and (d2): the moved-out argument of §3.1's `n1`, seen without a crash.

`[INFERENCE]` Any request whose answer depends on time or memory would serve as well as `Measure`
(`Exec` running a clock, for example); I tried only `Measure`.

**Why two siblings cannot both do I/O.** `[RAN]` `A2/attacks/at01_two_world_siblings.sl`,
`(values (say w "A\n") (say w "B\n"))`, is refused by both checkers:
``at01_two_world_siblings.sl:22:60: error: unique value `w` has conflicting non-erased uses``.
`[INFERENCE]` So every request a step performs lies on one chain of world binders, each produced by the
call that consumed the previous one; sibling order can cut that chain short (a crash) or shift what else
has happened by the time a link runs, but cannot reorder its links. This rests on the rejections of
§3.5, not on a proof.

### 3.5 Attack attempts on the language's own effects

All files are in `A2/attacks/`; `[RAN]` `./chk.sh FILE` runs `$REF FILE` and `$SLC --interpret FILE`;
the consolidated output is `A2/attacks/attacks_summary.log`. In every row the two checkers gave the same
verdict and the same first error line. The numbers follow the file names (9 was not used).

| # | idea | file | verdict (first error, both checkers) |
|---|---|---|---|
| 1 | two `world-do` siblings in one `values` | `at01_two_world_siblings.sl` | rejected: ``unique value `w` has conflicting non-erased uses`` |
| 2 | one sibling uses the world, the other a `(share w)` for I/O | `at02_world_and_shared_world.sl` | rejected: `` `ws`, declared `many`, used at unique `` |
| 2b | the same, the second sibling only holding `(share w)` | `at02b_world_unique_and_share.sl` | rejected: conflicting non-erased uses |
| 3 | two `def-unique` closures each capturing the world (§32) | `at03_two_closures_capture_world.sl` | rejected: conflicting non-erased uses |
| 3b | a second world by `coerce` through a newtype with a `many` field (§34) | `at03b_forge_world_by_coerce.sl` | rejected: `` `x`, declared `many`, used at unique `` |
| 4 | one entry writes a `unique` cell in place, the other takes `(slot-of u)` (§15: not a use) and compares it with a slot taken earlier | `at04_cellwrite_vs_slot_of.sl` | **accepted**; `(Cons _ 1 $ Cons _ 41 $ Cons _ 1 $ Cons _ 42 $ Nil _)` for both textual orders, in all five runs |
| 5 | one entry writes the cell, the other reads it with `cell-match many (share u)` | `at05_cellwrite_vs_cellmatch.sl` | rejected: conflicting non-erased uses |
| 5b | the same with `cell-match unique u` | `at05b_cellwrite_vs_cellmatch_unique.sl` | rejected: conflicting non-erased uses |
| 6 | keep `(share u)`, then write `u` at unique, then read the alias | `at06_share_then_unique_write.sl` | rejected: conflicting non-erased uses, "already shared here" |
| 7 | a `def-fns` closure mentions `(share u)`; `u` is then written at unique and the closure called | `at07_closure_shares_then_unique_write.sl`, `at07b_closure_shares_values_sibling.sl` | rejected: conflicting non-erased uses, "already shared here" |
| 8 | a `unique` binder aliasing a live `many` one (§13, §34): `coerce` a `many` list into a unique newtype box, then reach a unique cell of the list's block | `at08_unique_alias_of_many_then_mutate.sl` | rejected: `` `u`, declared `many`, used at unique `` |
| 8b | ask the newtype's unique destructure for a cell binder | `at08b_newtype_cell_binder.sl` | rejected: ``a `let-match` pattern on `MkLBox` under `unique` expects 1 binder, got 2`` |
| 8c | wrap the `many` list in a newtype whose field is labelled `unique` | `at08c_unique_field_newtype_from_many.sl` | rejected: `` `xs`, declared `many`, used at unique `` |
| 10 | read a cell through a `many` Slot taken earlier, naming the cell only as an erased `at` parameter (§36), so that no use is recorded | `at10_erased_cell_at_slot.sl` | rejected: `` `c`, declared `erased`, used in a non-erased position `` |
| 10b | the same reader taking the cell at `many`, called with `(share u)` beside a unique write | `at10b_many_cell_param_at_slot.sl` | rejected: conflicting non-erased uses |
| 11 | an erased mention of a consumed value (§15): after `u` is consumed by a real write of `y`, an erased `cell-write erased u (Boxed (slot-of z))` retypes it (accepted on its own); the real cell is then invoked with `(at) z`, asking for the store to be skipped | `at11_erased_retype_of_consumed_cell.sl` | rejected: `` `at` argument 1 is not in its slot's location class `` |
| 11b | the same, invoking the erased retyped cell in a non-erased position | `at11b_invoke_erased_retyped_cell.sl` | rejected: `` `ue`, declared `erased`, used in a non-erased position `` |
| 11c | the same, asking `cell-same` (§68) to equate the real cell with the erased retyping, both being at `u` | `at11c_cell_same_with_erased.sl` | rejected: `` `ue`, declared `erased`, used in a non-erased position `` |
| 12 | a `def-unique` closure captures the cell and writes it when called; a sibling takes `(slot-of u)` of the captured, consumed cell | `at12_unique_closure_vs_slot_of.sl` | **accepted**; `(Cons _ 1 $ Cons _ 41 $ Cons _ 1 $ Cons _ 42 $ Nil _)` in all five runs |
| 13 | an extern in-place array operation against a shared read of the same array (§44) | `at13_array_swap_vs_get.sl`, `at13b_array_swap_then_get_statements.sl` | rejected: conflicting non-erased uses |
| 14 | after `array-pluck` the box and the array both hold the box's word (§44); one entry updates the box in place, the other reads the array's stale slot through `(share b)` | `at14_pluck_alias.sl` | **accepted**; `(Cons _ 1 $ Cons _ 7 $ Cons _ 1 $ Cons _ 7 $ Nil _)` in all five runs: the reader obtains a `(Slot)`, never the contents |
| 15 | `slot-eq` on separately made equal words (not an order probe) | `at15_slot_eq_across_implementations.sl`, `at15b_slot_eq_no_bignum.sl` | **accepted**; answers differ among implementations (§5 item 3), which §67 allows |
| 16 | at the top level: a closure with `(share u)` of a unique `Settled` cell, then a unique write; and the write and a read as `values` siblings | `at16_toplevel_unique_closure.sl`, `at16b_toplevel_values_siblings.sl` | rejected: conflicting non-erased uses |

Also learned while writing them: `[RAN]` an in-place array operation cannot itself be a sibling, because
it returns several values: a first draft with `(values (array-swap …) …)` was refused with
``the enclosing `let` expects 5 values, got 2`` and, from slc, `expected 1 values, got 4`. `[QUOTE DESIGN.md:1106-1107]` §27: "each entry of which is a size-one expression".

`[INFERENCE]` Why the accepted probes (4, 12, 14) see nothing: the only thing a sibling can take from a
`unique` value another sibling is consuming is its address, as a `(Slot)`, and the address does not
change when the contents do. `[RAN]` `A2/heap/h1_inplace_and_copy.sl` confirms the address part in all five
runs (§4.3).

Ideas listed by the task and where they are covered: `slot-eq` answers (4, 12, 14, 15); `(slot-of x)`
not being a use (4, 12); a `unique` binder aliasing a live `many` one (8, 8b, 8c); erased mentions of
consumed values (11, 11b, 11c, and 10; the consumed `u` is also named by `slot-of` in 4 and 12); argument temporaries (§3.1 rows `n1`, `n4`, `m1`,
`p7`, `p9`, `x5`, `x8`, and §3.4's `q3`); `world-do` (1 to 3b); extern arrays (13, 14); `share` (2, 6, 7,
`p5`); `at` (10, 10b); closures over unique values (3, 12); crashes and fuel (§3.4).

### 3.6 Compile time: macro expansion order is observable through `gensym`

`[RAN]` `A2/attacks/ct01_gensym_sibling_order.sl` defines a macro `tick` that expands to the numeral of
the `gensym` number it is given. Both `$REF` and `$SLC --interpret` print the same value:

| form | numbers received, in the form's written order |
|---|---|
| body: `(values (tick) (tick) (tick))` | 1 2 3 |
| body: `(add3 (tick) (tick) (tick))` | 4 5 6 |
| body: `(add3 (tick) (nat-add (tick) 0) (tick))` | 7 **9 8** |
| body: `((pick (tick)) (tick) (tick))` | (head 10) 11 12 |
| top level: `(values (tick) (tick) (tick))` | 13 14 15 |
| top level: `(add3 (tick) (nat-add (tick) 0) (tick))` | 16 **18 17** |
| top level: `((pick (tick)) (tick) (tick))` | (head 19) 20 21 |

`[INFERENCE]` The head's number (10, 19) is not printed; it is the one number missing from each run of
consecutive numbers.
`[INFERENCE]` So macro calls written directly as arguments are expanded before a macro call nested
inside an earlier argument, and a head form is elaborated before both. `[READ lib/elab.ml:1368, 1380, 1383]`
The reference's `elab_form` settles a computed head (`expand_one (!settle_head pos)`), then expands the
directly written argument macro calls (`spliced_framed`), then elaborates the head and the arguments.
`[INFERENCE]` DESIGN.md gives "the head is elaborated first" (§6) and "threaded sequentially" (§65) and
no rule for siblings, so a spec that starts at source text has to choose this order or leave `gensym`
numbers open; a program can turn the number into acceptance or rejection (for example by a
`comptime-match` on it), which I did not write.

### 3.7 The finding, worded with care

- **Here are programs that observe sibling order:** `A2/observe_order_crash_1.sl` against
  `A2/observe_order_crash_2.sl` (stdout before a crash), and `A2/observe_order_measure_1.sl` against
  `A2/observe_order_measure_2.sl` (a `Measure` answer, no crash). `[RAN]` as reported in §3.4. Whether
  these count depends on what the spec's run says about crashes (§31 leaves the report of a crash
  unspecified and says nothing of the output before it) and about the answers of requests.
- **For everything else: 22 rejections and 3 order-insensitive accepted probes** (§3.5), across 15 ideas
  and 8 variants. The 22 refusals are of five kinds: more than one non-erased use of a `unique` binder on
  a path (13 programs), a `many` binder used at unique (4), an erased binder used in a non-erased position
  (3), a newtype constructor having no cell binder (1), and an `(at)` argument not at its slot (1); a
  sixth, a sibling that is not size one, met a first draft. **This is evidence, not proof, that sibling order cannot change the values an accepted
  program computes, or the sequence and arguments of the requests it makes, when no crash occurs and
  request answers are taken as given.**
- `[INFERENCE]` The property, if true, rests on `unique` meaning sole reference wherever mutation can
  happen (§13 lines 510-513 say so in words). The handoff records, as a session's answer and not as an
  owner decision, that the project would not itself prove that. If so, a formal run that leaves sibling
  order open would be relying on an unproved property,
  and a formal run that fixes an order has to pick one: the reference's (which slc does not fully share),
  slc's, or the handoff's proposal A (which neither implements, §0 item 4).

---

## 4. How the reference runs a program (implementation behaviour)

### 4.1 Evaluation order in `lib/eval.ml`

`[READ lib/eval.ml:17-81]` I read the whole evaluator (81 lines). For each OCaml expression that evaluates
several sub-codes:

| code form | OCaml expression (`lib/eval.ml`) | what fixes the order | measured |
|---|---|---|---|
| `CValues cs` | line 23: `List.map (eval1 env) cs` | the stdlib's `List.map` | 1 2 3 |
| `CApp (f, args, _)` | line 24: `apply (eval1 env f) (List.map (eval1 env) args)` | among arguments: `List.map`. Head versus arguments: **the OCaml compiler** (two arguments of one application) | arguments 1 2, then head 0 |
| `CLet (ids, rhs, body)` | line 25: `eval (bind ids (eval env rhs) env) body` | data dependency: `rhs` is an argument of the call that evaluates `body` | 1 2 |
| `CMatch` | lines 28, 33: `let v = eval1 env scrut in` … `eval1 env code` (a held `Matchable`) … branch | `let` sequencing | scrutinee 1, held matchable 2, branch 3 |
| `CCellAlloc (c, ss)` | line 46: `Array.of_list (List.map (eval1 env) ss)` | `List.map` | 1 2 |
| `CCellWrite` / `CCellCopy` | lines 48-54: `match eval1 env c with` … `List.iter (fun (i,_,s) -> fs.(i) <- eval1 env s) ss` | the `match` scrutinee, then `List.iter` | cell 0, items 1 2 |
| `CPrim (p, cs)` | line 59: `match p, List.map (eval1 env) cs with` | `List.map` (`p` is a variable) | 1 2 3 4 |
| `CCellRead`, `CWorldDo` | lines 56, 57 | one sub-code each | – |

`[RAN]` `grep -n "^let rec map\b" -A 2 /usr/lib/ocaml/list.ml` (OCaml 4.14.1, `ocamlfind ocamlopt -version`):
`let rec map f = function [] -> [] | a::l -> let r = f a in r :: map f l`. The `let r = f a in` fixes
left to right. `[RAN]` same file: `let rec iter f = function [] -> () | a::l -> f a; iter f l`.

`[RAN]` The "measured" column: `A2/harness/harness.ml` links the built reference library
(`_build/default/lib/sleight.cmxa`, read-only) and calls `Eval.eval` on hand-made code whose sub-codes
are `CWorldDo`s that print a number. Built with
`ocamlfind ocamlopt -package zarith,unix -linkpkg -I $B/.sleight.objs/byte -I $B/.sleight.objs/native $B/sleight.cmxa harness.ml -o harness`
(`B=/home/user/sleight/_build/default/lib`), output:

```
CApp (head=0, args=1,2): 1 2 0
CValues [1;2;3]: 1 2 3
CCellAlloc [1;2]: 1 2
CCellWrite (cell=0, items=1,2): 0 1 2
CCellCopy (cell=0, items=1,2): 0 1 2
CPrim SlotEq [1;2;3;4]: 1 2 3 4
CLet (rhs=1, body=2): 1 2
CMatch (scrut=1, held matchable=2, branch=3): 1 2 3
```

`[RAN]` `A2/ocaml_order/ord.ml`, compiled with both `ocamlfind ocamlopt` and `ocamlfind ocamlc` 4.14.1:
application `f (p "1") (p "2")` printed `21`; `let a = p "1" and b = p "2"` printed `12`; a tuple and a
record each printed `21`; an application whose head prints, `21head`.

**Why the one compiler-dependent order cannot be seen.**
`[READ lib/elab.ml:1136-1142]` In `check_args`, for a non-erased argument in a non-erased position, an
argument whose term and code are not both a variable is bound to a fresh temporary `x`; in a body
`(x, code)` is pushed on `env.pending` and the argument's code becomes `V.CVar x`.
`[READ lib/elab.ml:1412-1423]` `elab_head` does the same for a head that is not a name, before the
arguments are checked.
`[READ lib/elab.ml:2268-2272, 2353-2356, 2481]` `pending` is turned into nested `CLet`s around the code
of the statement (`elab_stmt`, `elab_let`) or of a body's final form (`hoisted`), oldest outermost.
`[INFERENCE]` So the `f` and `args` of every `CApp` the elaborator emits are `CVar`s (or constants), whose
evaluation has no effect; I checked every caller of `check_args` that produces code (constructor
application 1398, `elab_call` 1459, cell invocation 2016, `world-do` 1761, `settled-*-apply` 1785,
primitives 1813) and each passes `~bind_args:true`. A caller I misread would refute this.

**What the elaborator's code fixes, in a body.**
`[READ lib/elab.ml:1739-1753]` A `values` becomes `CValues` of its entries' codes: the entries are
evaluated in place.
`[READ lib/elab.ml:2067-2075]` A match binds its scrutinee by `CLet ([x], scode, body)` at the match
itself.
`[READ lib/elab.ml:2031-2064]` A `cell-match` binds its input by `CLet ([sid], code, …)` at the form and
reads each word with `CCellRead`.
`[READ lib/elab.ml:1651-1661]` `share` returns its operand's code unchanged.
`[READ lib/elab.ml:2006-2029]` A cell invocation with stores is `CCellWrite` (at `unique`) or `CCellCopy`
(at `many`) over the head's code and the bound arguments; with no store it is the head's code.

### 4.2 Evaluation order in extracted OCaml

`[QUOTE MANUAL.md:40]` "dune exec bin/main.exe -- tests/io_echo.sl --extract echo.ml" is the flag's
documented use.

Source, `A2/extract/small.sl`:

```scheme
(def-fns _ $ (many two : (many (Nat) x) (many (Nat) y) -> (many (Nat) p) (many (Nat) q))
  (values (f (g x) (h y)) (g (h (g y)))))
(def-fns _ $ (many nested : (many (Nat) x) (many (Nat) y) -> (many (P2) r))
  (MkP2 (f (g x) (h y)) (g (h x))))
```

`[RAN]` `$REF small.sl --extract small_ref.ml` (printed value of the program: `(MkP2 15 9)`), lines
1405-1406 of the output, reflowed:

```ocaml
let rec v40782_two (v40784_x : Obj.t) (v40786_y : Obj.t) : Obj.t =
  (let v40796 = (v40750_g v40784_x) in
  (let v40804 = (v40762_h v40786_y) in
  (let v40820 = (v40750_g v40786_y) in
  (let v40826 = (v40762_h v40820) in
  (let x157_a0 = (v40730_f v40796 v40804) and x157_a1 = (v40750_g v40826) in
   (to_any (x157_a0, x157_a1)))))))
let rec v40842_nested (v40844_x : Obj.t) (v40846_y : Obj.t) : Obj.t =
  (let v40860 = (v40750_g v40844_x) in
  (let v40868 = (v40762_h v40846_y) in
  (let v40874 = (v40730_f v40860 v40868) in
  (let v40884 = (v40762_h v40844_x) in
  (let v40890 = (v40750_g v40884) in
  (to_any (K13_0 { f0 = v40874; f1 = v40890 })))))))
```

So extraction **let-binds every argument** (the binding is the elaborator's, §4.1; the extractor prints
each `CLet` as an OCaml `let`), and prints a call as an application to names.
`[READ lib/extract.ml:401-407]` A `CApp` is printed as `(name arg …)` or as a constructor build over the
extracted argument texts.
`[READ lib/extract.ml:129-134, 400]` A multi-entry `CValues` goes through `bind_args`, which joins the
bindings with `" and "`: an OCaml `let … and … in`.

`[INFERENCE]` From memory of the OCaml manual, not checked tonight: the order of the bindings of a
`let … and …` is unspecified by OCaml. `[RAN]` Measured on this install it is left to right (`12` above),
and probes `v1` and `v2` agree in run (c).

`[RAN]` slc on the same file (`$SLC small.sl > small_slc.ml`) emits the same shape, with the `values`
entries bound by nested `let`s:
`(let tup6_a0 = (v42036_f_a1559 …) in let tup6_a1 = (v42057_g_a1562 …) in (to_any (tup6_a0, tup6_a1)))`.
`[READ self/emit.sl:350-369]` slc's `values-rope` uses `let-binds-rope`, which joins with `" in let "`.

`[READ lib/extract.ml:429-433]` An extracted `CCellWrite` is `(let cellN = <cell> in <stores>; cellN)`,
the stores joined by `; `.
`[READ lib/extract.ml:418-425]` A `CMatch` is an OCaml `match` on the extracted scrutinee.

### 4.3 Heap and mutation

**Interpreter values.** `[READ lib/value.ml:14-25]` `value` is
`VCtor of ctor * value array | VTuple of value list | VExt of adt * payload | VCtorFn of ctor | VMatchable of adt | VFn of closure | VToken | VWord of Z.t | VHandle …`.
`[READ lib/value.ml:91-94]` `construct c args`: an extern type's FFI constructor when externs are on;
otherwise the bare field for a newtype (`tuple args`), `word c` for a constructor with no non-erased
field, and `VCtor (c, Array.of_list args)` for the rest.
`[READ lib/value.ml:87-89]` `vacant = VWord Z.zero`; `word c` is `VWord k`, `k` the position among the
type's fieldless constructors, when the type is tagged, and `vacant` otherwise. So a hollow value and a
fieldless constructor are `VWord`s, and a block is an OCaml array.
`[READ lib/elab.ml:300-313, 1400-1401]` A fieldless constructor applied in source elaborates to a
constant, the one `Settled` `VWord k` of its tag slot (tag slot 0 is `vacant-slot`'s entry), not to a
call of `construct`.

**In-place update.** `[READ lib/eval.ml:47-55]` `CCellWrite` evaluates the cell to a `VCtor (k, fs)`,
assigns `fs.(i) <- …` for each item, and returns the same value; `CCellCopy` first does `Array.copy fs`
and returns a new `VCtor`; a `VWord` cell (an empty cell) is returned as it is.
`[READ lib/elab.ml:1636]` A `cell-write` at `many` elaborates to `CCellCopy`, at `unique` to `CCellWrite`.
`[READ lib/elab.ml:2027-2028]` A cell invocation at `many` with a store is `CCellCopy`; at `unique` with a
store, `CCellWrite`; with every store skipped, the cell's own code.
`[READ lib/eval.ml:45-46]` `cell-alloc` builds a `VCtor` with the item values (`vacant` for `_`), or the
constructor's word when it has no field.
`[READ lib/eval.ml:56]` `cell-match` reads `fs.(i)`.
`[READ lib/elab.ml:1603-1607]` `(slot-of x)` in a non-erased position is the code `CVar x`: the value
itself.

**Identity.** `[READ lib/eval.ml:61]` `slot-eq` is `if a == b then some else none`, OCaml physical
equality on `value`. `[INFERENCE]` For two `VWord`s that is identity of the OCaml box, not equality of
the numbers, which matches §5 item 3.
`[READ lib/elab.ml:1662-1695]` `cell-same` and `fn-same` check `same_slot` in the fact table and emit
`V.CVar Prelude.null` (the word of `vacant-slot`); nothing is compared at run time.
`[READ lib/extract.ml:438]` Extracted `slot-eq` is `(if a == b then some else none)` on `Obj.t`.

`[RAN]` `A2/heap/h1_inplace_and_copy.sl`, `./plain5.sh h1_inplace_and_copy`: all five runs print
`(Cons _ 1 $ Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 1 $ Cons _ 6 $ Nil _)`: a unique `cell-write` keeps
the address (1), a unique invocation keeps it (1), a `many` `cell-write` gives a new address (0), a
`many` invocation with a store gives a new address (0), a `many` invocation with every store skipped
gives the block itself (1), and the content read back is the written one (6).

`[RAN]` `$REF h1_inplace_and_copy.sl --extract h1_ref.ml`, from `run`:
`(let cell159 = v40778_x in (match (of_any cell159 : t10) with K10_0 r160 -> r160.f0 <- v40774_n); cell159)`
for the unique `cell-write`, and
`(match (of_any v40802_y : t10) with K10_0 r155 -> (to_any (K10_0 { f0 = r155.f0 })))` for the `many`
one. `[READ lib/extract.ml:99-106, 487-510]` Extracted types are OCaml variants with inline records of
`mutable fN : Obj.t` fields, a fieldless constructor being a constant constructor.

**Function values.** `[READ lib/value.ml:27-29]` A function value is
`VFn { fn = { fname; params; body : code; impl }; env : venv Lazy.t }`: a closure record.
`[READ lib/eval.ml:13-15]` A `def-fns` block's closures share one lazily tied environment.
`[READ lib/elab.ml:2654-2669]` A `delegate`-bodied function gets no closure of its own:
`Hashtbl.replace V.aliases x (V.resolve f)` makes its id an alias of its callee's, and it is dropped from
the block's functions. `[READ lib/eval.ml:20; lib/value.ml:76-78]` Variable lookup goes through
`resolve`. So the delegate *is* its callee's closure value.
`[READ lib/elab.ml:2663-2664]` An at-function's body code is replaced by `CValues []`.
`[RAN]` `A2/heap/h2_delegate_identity.sl`, `./plain5.sh h2_delegate_identity`: all five runs print
`(Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Nil _)`: `slot-eq` of a delegate and its callee answers `ESome`, two
closures made by two calls of one factory answer `ENone`, a closure with itself `ESome`.

**Addresses.** `[INFERENCE]` In the reference an address is an OCaml heap pointer, and the only question
a program can put to one is `slot-eq`'s. `[READ lib/ffi_core.ml:323-389]` The extern `Slots` table
hashes raw addresses internally (`address`, resynchronised after the collector moves blocks), compares
with `==`, and hands the program indices numbered by insertion.

### 4.4 Extern types and functions, and `--no-extern`

`[READ lib/elab.ml:2608, 2665]` An `extern` function keeps both its model (`body`, the elaborated code)
and its implementation (`impl = Some (Ffi.claim_fn …)`).
`[READ lib/eval.ml:78-79]` `apply` uses `impl` when `!use_externs`, and otherwise interprets the body.
`[READ lib/elab.ml:2784; lib/value.ml:91-94, 102-108]` An `extern` type records `adt.ext`;
`construct` and `dispatch` use it when `!use_externs`.
`[READ bin/main.ml:81]` `--no-extern` sets `Value.use_externs := false`.
`[READ lib/ffi.ml:45-73, 98-201]` The FFI is two fixed tables, of types (`Array`, `Bytes`, `Slots`,
`Nat`, `Half`, `Raw`, `String`) and of functions keyed by name.

`[QUOTE MANUAL.md:279-281]` "`dune test` runs every `tests/*.sl`, once with the FFI and once without, and
extracts, compiles and runs every test that runs, both ways, against the same directives"
`[READ test/runtest.ml:76-93]` The runner loops over `(true, "with externs")` and
`(false, "without externs")`, cut to one by `; externs: only` or `; externs: none`.
`[RAN]` `grep -l "^; externs: only" tests/*.sl | wc -l` → 23; `grep -l "^; externs: none" tests/*.sl | wc -l`
→ 1; `ls tests/*.sl | wc -l` → 1337.
`[READ self/bootstrap.sh:2-12]` slc's bootstrap compares each test's stdout, stderr, and exit code with the
reference interpreter's, compiled and under `--interpret`.
`[INFERENCE]` Those suites compare outputs of complete, non-crashing runs, which is why the order
difference of §3.2 is invisible to them.

### 4.5 The driver

`[READ lib/elab.ml:2877-2904]` A file's final expression (its last item, when that is not a statement) is
elaborated, run, and handed to `consume`.
`[READ lib/program.ml:113-118]` `consume` dispatches on the final's type: `Main` (String to String),
`Program`, `Thunk` (applied, result printed), `Plain` (printed).
`[READ lib/program.ml:116]` For a `Program`: `Eval.perform := d.perform w; w.exit (d.run_program w v)`.
`[READ lib/driver_core.ml:402-406]` The loop:
`let rec loop v = match o.step v with Exit code -> u8 code | Continue k -> loop (o.apply k []) in try loop v with Halt code -> code`.
The continuation is applied to **no arguments** and returns one value, the next `Program`.
`[INFERENCE]` That is the reference's rendering of §42's "A world is taken `at vacant-slot`, so the
driver passes it no word" and of the `at w` return: the world has no run-time representation at all.
`[READ lib/eval.ml:57]` `world-do` is `CWorldDo c -> [ !perform (eval1 env c) ]`.
`[READ lib/driver_core.ml:298-400]` `perform` decodes the request and does the I/O at that moment.
`[READ bin/main.ml:6]` stdout is flushed after each write (`flush_to`).
`[READ lib/extract.ml:434, 631-637]` Extracted code calls `driver.Driver_core.perform world …` on a
global `world` record, and its driver is the same `Driver_core` source.

**I/O at compile time.**
`[READ lib/eval.ml:5]` `Eval.perform` starts as a function that raises `Runtime "no world"`.
`[RAN]` `grep -n "Eval\.perform" lib/*.ml bin/*.ml` finds one assignment, `lib/program.ml:116`, in
`consume`. `[INFERENCE]` No run-position form can reach `world-do`: it needs a `unique` `World`
binder, and none exists at the top level (§42 line 1976-1977; and attack 3b shows one cannot be forged by
`coerce`).
`[READ lib/elab.ml:614-619, 690-691]` A macro's `read-file` reads a file from disk while the macro is
being expanded (`Driver_core.read_within`), confined to the directories of the source files and of
`--comptime-unconfine` names.
`[READ lib/extract.ml:685-704; lib/elab.ml:1696-1738]` `native-compute` writes the program so far as
OCaml into a temporary directory, runs `ocamlfind ocamlopt`, runs the compiled program once per argument,
and reads each run's stdout, all during elaboration, unless `--no-native`.
`[READ lib/elab.ml:586]` `gensym` increments a global counter during expansion.
`[INFERENCE]` So compile time can read files, write temporary files, and run processes, and cannot
write to the program's stdout except through warnings and errors on stderr.

### 4.6 Run-position forms and fuel

`[READ lib/elab.ml:1327-1339]` Every `elab_expr` in run position ends with `run_form`.
`[READ lib/elab.ml:1341-1355, 2430]` `run_form` evaluates the form's code with
`Eval.eval env.values code` (`env.values` holds the stored values of the `Settled` entries), stores each
result as `Settled v`, stores `VToken` for erased entries, and returns as the form's code a `CVar` of the
now-`Settled` entry or a `CConst` of the value, so the enclosing form does not run it again.
`[READ lib/elab.ml:1533-1552]` A call in run position runs once, with all its returns, and its result
entries become `Settled`.
`[READ lib/elab.ml:2456, 2469]` A run-position `let` runs its right-hand side's code and binds the
values.
`[INFERENCE]` There is no separate stripping pass: the elaborator produces post-erasure `code` directly
(erased positions yield `CErased`, erased arguments are left out of `codes` at `lib/elab.ml:1153`).
`[READ lib/elab.ml:2670-2673]` A run-position `def-fns` evaluates nothing: it builds the closures with
`Eval.close` and stores them.

**Fuel.** `[READ lib/eval.ml:4]` `fuel : int option ref = ref None`.
`[READ bin/main.ml:79]` `--eval-fuel n` sets it to `Some n`.
`[READ lib/eval.ml:70-81]` Only `apply` spends: 1 unit for an extern implementation or a constructor
function, 2 for a function interpreted from its body; `spend` raises `Runtime "out of fuel"` when fewer
units remain, and restores the old amount when the application returns (`Fun.protect ~finally`). So fuel
bounds nesting depth, not the number of steps.
`[QUOTE MANUAL.md:159-162]` "It bounds every run the evaluator makes, at compile time and, in the
reference and under `slc --interpret`, the program's own; the OCaml that `--extract` or slc writes out
has no bound. Without the flag the reference has none and slc's is 1000000000."
`[RAN]` `$REF tests/comptime_fuel.sl --eval-fuel 1000` printed
`tests/comptime_fuel.sl: runtime error: out of fuel`. `[RAN]` `$REF v1_values_say_deep.sl` with no flag
ran the 100000-deep recursion to completion.

---

## 5. Other disagreements among the implementations

1. **Order of `cell-write` input and of `cell-write` and `cell-alloc` items** (§3.2).
2. **After a fuel error, slc's interpreter keeps going.** `[READ self/elab-main.sl:185-188; self/eval.sl:717-720; self/core.sl:2409-2415]`
   Out of fuel is an error *block* (`BError`) returned as the call's value; `halloc` records the first
   such message in the heap; evaluation continues with the error block in place of the value.
   `[READ self/interp.sl:129-137]` slc's `perform` refuses requests once a crash is recorded.
   `[READ self/interp.sl:98-99]` The message is reported when the step returns.
   `[RAN]` `A2/order/e1_error_then_io.sl` (a fuel-exhausting statement, then a `WriteOut "after\n"`): both
   `$REF … --eval-fuel 2000` and `$SLC --interpret … --eval-fuel 2000` print nothing and report
   `out of fuel`. `[RAN]` `A2/order/b1_body_values_deep_boom.sl` with `--eval-fuel 2000`: the reference
   reports `out of fuel`, slc dies with `Fatal error: exception Stack overflow`, because it went on to
   evaluate the second sibling after the first one's fuel error. `[READ lib/eval.ml:74]` The reference
   raises an OCaml exception at once.
3. **`slot-eq` answers.** `[RAN]` `./plain5.sh at15b_slot_eq_no_bignum` (in `A2/attacks`):

   | question | (a) | (b) | (c) | (d1) | (d2) |
   |---|---|---|---|---|---|
   | two fieldless constructor values made by two calls | 1 | 1 | 1 | 1 | 0 |
   | two equal small numbers computed separately | 0 | 0 | 1 | 1 | 0 |
   | two separately built blocks with equal contents | 0 | 0 | 0 | 0 | 0 |
   | one variable with itself | 1 | 1 | 1 | 1 | 1 |
   | a fieldless constructor's word against the numeral `0` | 0 | 0 | 1 | 1 | 0 |

   `[INFERENCE]` §67 allows every one of these differences ("an implementation may always answer"
   `ENone`). None depends on sibling order.
4. **`Measure` under `--no-extern` answers 0 in every field.** `[READ lib/driver_core.ml:363]`
   `let nat x = match nat_of_z with Some f -> … | None -> o.zero`. `[RAN]` `./plain5.sh meas_print`
   (in `A2/order`): (a), (c), (d1), and (d2) print `minor-words > 0`, (b) prints `minor-words = 0`.
5. **How a crash is reported.** `[RAN]` (from the logs above) The reference interpreter reports fuel
   exhaustion as `FILE: runtime error: out of fuel` with exit 1, and lets `Z.Overflow` escape as
   `Fatal error: exception Z.Overflow` with exit 2; compiled programs die with
   `Fatal error: exception Stack overflow`, exit 2; slc reports a compile-time fuel error as
   `FILE:LINE:COL: error: compile-time evaluation failed: out of fuel`. `[RAN]` An `array-make` of 2^62
   elements is `Z.Overflow` in the reference and in slc-compiled code, and `Stack overflow` in slc's
   interpreter (`A2/order/t_boom_top.sl`, `probe_run4.log`). §31 leaves crash reports unspecified.
6. **slc's interpreter overflows the host stack where the reference does not.** `[RAN]`
   `$SLC --interpret repro_cellwrite_order.sl` (no limit) dies with `Stack overflow` on the 100000-deep
   recursion that `$REF` completes. §31 allows it.
7. **Run position versus body order** (§3.3) is a difference between two positions, not between
   implementations: both agree with each other.

`[RAN]` Everything else compared equal across the five runs: all rows of §3.1 not in bold, the identity
experiments of §4.3, and attack programs 4, 12, and 14.

---

## 6. What this suggests for the spec's run (my inferences; nothing here is decided)

- `[INFERENCE]` If the correctness theorem is to cover what a program writes before a crash, or the
  answers of requests like `Measure`, the spec's order must be exactly the compiler's, including which
  sub-expressions are moved to before the statement. Today that would mean choosing between two
  implementations that differ (§3.2), and neither matches "left to right, each completely before the
  next" (§0 item 4).
- `[INFERENCE]` If instead a crash may cut the request sequence at any point and request answers are
  inputs the theorem quantifies over, sibling order appears not to matter for accepted programs (§3.7);
  but "appears" rests on uniqueness being sole reference, which (by a session's answer recorded in the
  handoff, not an owner decision) the project would not itself prove.
- `[INFERENCE]` A third shape avoids both: a spec run that is a relation leaving sibling order open, and a
  theorem that the compiler's run is one of the spec's runs. That needs no commutation proof and no
  uniqueness theorem, at the price of a nondeterministic spec. I have not tried it.
- `[INFERENCE]` Whatever is chosen, run position and bodies currently use different orders for the same
  text (§3.3), and DESIGN.md's wording supports each in its own place (§27, §15); a single rule for both
  would be a change to one of them.
- `[INFERENCE]` If the spec starts at source text, macro expansion order needs a rule too, since
  `gensym` exposes it (§3.6).
- `[READ self/core.sl:2409-2423; self/eval.sl:717-720]` slc's compile-time interpreter is already a heap
  machine written in Sleight (`halloc`, `hread`, `hwrite` over a store indexed by an allocation history).
  I read only these functions and the evaluator's main cases (`self/elab-main.sl:158-470`), not the whole
  of `self/eval.sl` or `self/heap.sl`.

---

## 7. Files

All under `A2/` =
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A2/`.

- Reproductions at the top: `repro_cellwrite_order.sl`, `repro_cellwrite_order_measure.sl`,
  `observe_order_crash_1.sl`, `observe_order_crash_2.sl`, `observe_order_measure_1.sl`,
  `observe_order_measure_2.sl`, `observe_hoisting_crash.sl`.
- `order/`: the order probes (`v*`, `c*`, `k*`, `i*`, `h*`, `n*`, `m*`, `p*`, `x*`, `t*`, `b*`, `w*`,
  `q*`, `g1`, `e1`), the shared pieces (`hdr.inc`, `boom.inc`, `boom2.inc`, `meas.inc`, `tail.inc`), the
  scripts (`probe.sh`, `probe2.sh`, `probe3.sh`, `plain5.sh`), the logs (`probe_run1.log` to
  `probe_run8.log`), and per-run stdout and stderr in `order/out/`.
- `attacks/`: `at01` to `at16b`, `ct01_gensym_sibling_order.sl`, `chk.sh`, `attacks_summary.log`.
- `heap/`: `h1_inplace_and_copy.sl`, `h2_delegate_identity.sl`, `h1_ref.ml`.
- `extract/`: `small.sl`, `small_ref.ml`, `small_slc.ml`.
- `harness/harness.ml` (drives the built `lib/eval.ml`), `ocaml_order/ord.ml` (OCaml's own orders).

Built binaries were deleted from the scratch directory to save space; every script rebuilds what it needs.

---

## 8. Things I am least sure of

1. **That sibling order cannot change values.** §3.5 is 27 programs. A hole in the uniqueness rules that I
   did not think of would overturn finding 2. I did not attack `comptime-match` at `unique`, handles
   (`MUnique`), `Placed` beyond the `WBox` idiom, `Slots`, `Bytes`, `tail`, or `delegate`.
2. **That the reference's `CApp` head and arguments are always atoms** (§4.1). It rests on my reading of
   `check_args`, `elab_head`, and their callers, not on a dump of emitted code.
3. **The extent of the reference-versus-slc order difference.** I found it for the `cell-write` input and
   for `cell-write` and `cell-alloc` items, and tested about twenty other forms that agree. Forms I did
   not test (`coerce` with a non-variable source, `open-adt`, `let-match` scrutinees, `cell-same` and
   `fn-same` operands, the `at` wrappers with head forms, `comptime-match`) may differ.
4. **The silence claims of §2.** They rest on greps and one full reading of a 3156-line file.
5. **My reading of §15's "the statement or final form that contains the call"** as the outermost
   enclosing statement or final form. The implementations behave that way for calls; the text could be
   read otherwise.
6. **The `Measure` probes' threshold** (300000 minor words). Each configuration was run once or twice;
   the readings were on the expected side each time, and I did not print the raw numbers.
7. **The OCaml manual's wording on `let … and …`** is from memory; only the measured behaviour on this
   install is checked.
8. **Whether `_build/release/slc` matches `self/` at HEAD.** I compared the reference's build inputs with
   `lib/`, not slc's.
9. **Two-crash probes under slc's interpreter with a fuel limit are unreliable** (§5 item 2); for (d2) I
   therefore ran `probe3.sh` without a fuel flag, where `deep` overflows the host stack. That makes the
   (d2) column of the second table depend on the host's default stack size.
10. **Crash kinds as observations.** Reading "which of two crashes was reported" as "which sibling ran
    first" assumes the first crash ends the run, which holds for hard crashes and for the reference's fuel
    error, and not for slc's fuel error.
