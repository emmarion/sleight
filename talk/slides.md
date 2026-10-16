# Sleight: A Language for LLMs

Sixty minutes over Zoom, for an audience of mostly PL experts. An opening, the agent runner, the language in order of importance, what is proved, and a close; an appendix follows for questions.

`./build.sh` writes `slides.pdf`, building the two charts first if they are missing; `./build.sh charts` rebuilds them.

## 1. Title

**Sleight: A Language for LLMs**

Eric Marion
October 14, 2026
[github.com/emmarion/sleight](https://github.com/emmarion/sleight), Apache-2.0
Code: doi.org/10.5281/zenodo.23361871
Slides: doi.org/10.5281/zenodo.23367392

- **Sleight**: a dependently typed language whose proofs erase, built for LLMs to write
- **An agent runner**: tests whether models can write Sleight, and where they get stuck

## 2. Why now

<!-- _class: split -->

- Code that proves itself: possible for decades, rarely done
- Models write code cheaply: the trade-off may now be worth it
- The type checker, not a reviewer, decides
- Proofs erase: no runtime cost

| System | Proof : code |
|---|---|
| seL4 | about 20 : 1 |
| CertiKOS | 15 : 1 |
| CompCert | 7 : 1 |
| Verus systems | 7.5–10 : 1 |
| IronFleet | 5 : 1 |

---

# The agent runner

## 3. The harness

- Fresh context each session: 50% for work, then 20% for notes
- HANDOFF.md: notes for the next session
- FEEDBACK.md: notes for us
- Agent sees each program's time and memory
- No-docs runs: learnable from the compiler alone?
- Auto-launched DigitalOcean fleet

## 4. The heapsort task

- "a fast, in-place heapsort in Sleight, certified correct"
- "not finished while the sort allocates"
- No bignum arithmetic: machine integers only
- "... any runtime recursion could be a tail call"
- "This task will likely take many sessions"

## 5. The heapsort task file

<!-- _class: taskfile -->

~~~text
#!pi -f ../../std -f ../../README.md -f ../../WARNINGS.md -f ../../DESIGN.md -f ../../lib/prelude.sl -f ../../tests -f ../../pal -f ../../self -f heapsort-fast -c work -k HANDOFF.md:60000 -k FEEDBACK.md:120000 -n 20 PI_RUN_TIMEOUT=60 PI_CONTEXT_STOP=50 PI_REWRITE_STOP=20 PI_FIRST_ERROR=no PI_OCAML=1
Your task is to write a fast, in-place heapsort in Sleight, certified correct against
heapsort-fast/spec.sl. Or: to lay the groundwork for a future session to do so.
This task will likely take many sessions, so leaving solid, well-recorded
progress matters more than finishing in this one.

To check your work, compile in order: std/nat.sl, std/list.sl,
std/macro.sl, std/tactics.sl, heapsort-fast/spec.sl, your files,
heapsort-fast/accept.sl, then heapsort-fast/perf.sl. The finished solution must
compile with no warnings, and none of the files in work/files.txt may contain
a `;! suppress`; intermediate work may have both. A solution is not
finished while the sort allocates, any array write could be an `-imm` one, any
runtime arithmetic could be a `u62-*` call, or any runtime recursion could be a
tail call, even if measurements show no gain.

For reference: README.md (the implementations and their command lines),
WARNINGS.md (the warnings the compilers emit), DESIGN.md (the language),
prelude.sl (the standard library), std/ (source libraries, among them
std/nat.sl, which holds `Le`, and std/list.sl, lemmas about `Length`, `Nth`,
`SetNth` and `Repeat`), tests/ (example programs), pal/ (a
certified program), and self/ (the compiler, itself written in Sleight).

Only work/, HANDOFF.md, and FEEDBACK.md carry over to the next session. In
work/, keep files.txt, listing in order the files that go between
heapsort-fast/spec.sl and the accept file. Generally put experiments and `sl`
captures in scratch/, which does not carry over; helper programs worth keeping
can go in work/. Keep work/ tidy, pruning files that have served their purpose.

Your session has two phases: first experimenting, then writing HANDOFF.md and
FEEDBACK.md. HANDOFF.md tells the next session where things stand and what to
try next; rewrite it each session instead of adding to it. FEEDBACK.md tells
Sleight's maintainers what slowed you down because of Sleight, its library, or its tools,
rather than because of the problem itself; add to it each session instead of
rewriting it. Each phase has its own budget of tokens. In the second phase,
those two are the only files you can edit; there's no need to edit them, or to
read FEEDBACK.md, before then, so spend the first phase on the task itself.

Hint: heapsort-fast/perf.sl times the sort alone and reports what it
allocates. To try another size, copy it to scratch/ and change both
`perf-size` and the numeral that `perf-size-fits` bounds.

Hint: to compile without running, use the `sl` tool's `ocaml` option.

Hint: the input array can be coerced to `Copy (U62)` elements at no cost (see
`coerce` in DESIGN.md and `init-witness` in prelude.sl).

Hint: heapsort-fast/bsearch-demo.sl coerces a `List (Nat)` with an `AllTo`
proof to `List (U62)` at no cost, and holds `bsearch`, a certified binary
search, with a program that times it. It compiles with no warnings. Its
`Absent` proof walks the whole list, yet the search runs in O(log n), since
erased code never runs; to see what is left, compile std/nat.sl, heapsort-fast/spec.sl and
heapsort-fast/bsearch-demo.sl with the `sl` tool's `ocaml` option.

Hint: spec.sl ties `u62-modulus` to the numeral 4611686018427387904, so a
bound on a concrete number, such as `Lt K u62-modulus`, is one line (here
K = 1048576):

```
(let ((erased (Lt 1048576 u62-modulus) mib-below-u62)) (prove-literal-lt 1048576 4611686018427387904))
```

Hint: spec.sl's `;! warn` pragmas flag runtime arithmetic that is not a
`u62-*` call, and array writes that are not `-imm`.
~~~

## 6. The sort's spec

```scheme
(def-adts
  ((SortedPerm : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) ((List A) ys) -> Type)
    enum
    (many MkSortedPerm : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R)
        (erased (List A) xs) (erased (List A) ys)
        (erased (Ascending A R ys) sorted) (erased (Permutation A xs ys) perm)
        -> (SortedPerm A R xs ys))))

;! warn Succ at runtime use `u62-inc` or `u62-add`
;! warn array-swap use `array-swap-imm`
```

## 7. How the models did

![heapsort-runs](chart/heapsort-runs.png)

## 8. Certified vs. uncertified sorts

![certified-sorts](chart/certified-sorts.png)

## 9. What the models complained about

- Thin standard library
- Numerals don't unfold to `Succ`
- A noisy style warning
- Refuting impossible cases
- One mistake, many error messages
- Balancing parentheses

## 10. In their own words

> "By far the biggest time sink was paren balancing." (glm-5.3)

> "No `assume`/`admit` escape hatch." (mimo-v2.6-pro)

> "`at` vs value identity is the single biggest modeling obstacle." (deepseek-v4.1-flash)

## 11. Agents trying to prove False

- Task: prove False, up to 20 sessions
- No run succeeded
- They reported many suspected holes
- One lead was real
- Our self-hosted compiler accepted a proof of False (fixed)

---

# The language

## 12. What Sleight is

- Statically and strictly typed
- Restricted dependent types
- Eager evaluation
- Uniqueness: guaranteed in-place updates
- Multiplicities on every binder, as in Idris 2
- Performance claims checked at compile time: tail calls, zero-cost coercions
- `Type : Type`, no positivity check, yet sound (Lean proof)
- Everything is first class; nothing is global
- Self-hosted: a second compiler, written in Sleight, compiles itself

## 13. Sleight, Lean 4, Idris 2, ATS2

<!-- _class: compare -->

| | Sleight | Lean 4 | Idris 2 | ATS2 |
|---|---|---|---|---|
| **Erasure** | declared on each binder | by sort; `Vect`'s index stays | quantity 0 | proofs erased |
| **In-place updates** | guaranteed: checked | only if refcount is 1 | linearity only: can alias\* | by hand, via linear views |
| **Tail calls** | guaranteed: checked | self calls only, unchecked | Chez does them, unchecked | self calls; `fnx` unchecked |
| **Termination** | required, no escape | required; `partial` escapes | optional (`total`) | optional metrics |
| **`Type : Type`, no positivity check** | yes, sound | no: universes, positivity | `Type : Type`, inconsistent | no positivity check |

- "Checked" means a claim the compiler confirms or rejects

\* Linear, not unique: a mutable array can escape its linear scope and be written through twice (slide 70)

## 14. Proofs are programs

- Curry–Howard: types are propositions, programs are proofs
- `(SortedPerm A R xs ys)`: `ys` is `xs` sorted by `R`
- Checking the program checks the proof
- OpenAI: 722 model-written manuscripts, part checked in Lean

## 15. Dependent types

- `(Vec (Nat) 3)`: exactly three numbers
- `(Vec (Nat) n)`: exactly `n`, whatever `n` is
- `zip-add`: takes two vectors of the same length
- Mismatched lengths: a type error, not a crash

## 16. Example: adding two vectors

```scheme
(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) m) (many A x) (many (Vec A m) xs)
       -> (Vec A (Succ m)))))

(def-fns _ $ (many zip-add : (erased (Nat) n)
    (subterm many (Vec (Nat) n) xs) (many (Vec (Nat) n) ys) -> (many (Vec (Nat) n) r))
  (let-match many xs (VCons _ m x xt) ((VNil _) (VNil _)))
  (let-match many ys (VCons _ _ y yt))
  (VCons _ m (nat-add x y) (notail (zip-add m xt yt))))
```

## 17. Erasure

- Proofs and types are deleted before the code runs
- Declared on every binder
- Unions: sum types with an erased tag
- Matching on one: every branch but one refuted
- Matching on an erased value in runtime code: the same
- `assume_init` with evidence, not `unsafe`
- Proofs of impossibility compile to nothing

## 18. Erasure: Lean vs Sleight

- Lean erases by sort: proofs and types
- Lean's `Vect`: the `Nat` index is stored in every cell
- (Lean's `Vector` avoids it with a `Prop` proof)
- Idris 2 and Sleight: declare the index erased

## 19. Coercions

- `coerce`: same bits, new type, backed by an erased proof
- Proofs relate values, not just types
- Built from `refl`, `sym`, `trans`, newtype wrapping and constructors
- A function that only forwards is its callee's pointer

## 20. Why coercions are free

- Every value is one word
- Tags only where needed
- A newtype is exactly its field
- `coerce` erases to a renaming
- Proofs about whole lists: erased recursion, never run

## 21. A zero-cost unwrap

```scheme
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-fns _ $ (many unwrap-all : (many (List (Meters)) ms) -> (many (List (Nat)) ns))
  (let ((erased ws) (erased p)) (unwrap-witness ms))
  (coerce ms p))
```

- `unwrap-witness`: a recursion over the list proving each `Meters` is its `Nat`
- It's erased and never runs
- Compiles to the identity function

## 22. Uniqueness

- A `unique` binder is the only reference: update in place
- On the binder, not the type: no unique types
- `share` gives up uniqueness, explicitly and for good
- You write the reuse; the compiler checks it

## 23. `at` is not `is`

- Every variable has a slot: its location
- `x at v`: `x` is in the same memory as `v`
- `x is v`: `x` has the same value as `v`
- Equal values can live in different blocks
- A cell is the memory a value occupies
- Matching a unique value can give you its cell
- Calling the cell builds a new value there

## 24. What a match gives back

| Field ↓ / match → | `erased` | `many` | `unique` |
|---|---|---|---|
| erased | erased | erased | erased |
| many | erased | many | many |
| unique | erased | many | unique |

- A unique field of a shared value comes out shared

## 25. A proof about overwritten memory

```scheme
(def-fns _ $ (many swap-in : (erased (List (Nat)) xs) (unique (Array (Nat) xs) a)
    (unique (Nat) x) (erased (Nth (Nat) xs 0 7) nth) ->
    (erased (List (Nat)) ys) (unique (Array (Nat) ys) r at a)
    (erased (SetNth (Nat) xs 0 x ys) p))
  (let ((unique old) (erased ys) (unique r) (erased p)) (array-swap _ _ a 0 x _ nth))
  (values ys r p))
```

- `array-swap`: the prelude primitive the heapsorts use
- `r at a`: same memory, new contents `ys`
- `SetNth xs 0 x ys`: the proof relating old contents to new
- `nth`, a proof about `xs`, is rejected as one about `ys`

## 26. Tail call modulo cons

```scheme
(def-fns _ $ (many append-into : (erased Type A)
    (unique (Cell Cons vacant-slot vacant-slot) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell))
  (let-match many xs (Cons _ hd tl) ((Nil _) (share (cell _ h ys))))
  (let ((unique next)) (cell-alloc Cons))
  (let ((unique cell2)) (cell-write unique cell (Cons (slot-of h) (slot-of next))))
  (let ((many r2)) (tail (append-into _ next hd tl ys)))
  (share (at (cell2 _ h r2))))
```

- Builds the result front to back, in place
- Allocates the next cell before the recursive call
- `tail`: checked to be a tail call
- Per element: one allocation, two stores, constant stack

## 27. Termination using levels

```scheme
(Fn L (subterm many (Nat) n) (many (Nat) d) ->
      (many (Nat) q) (many (Nat) r))
```

- Every function has a level, in its type
- Levels are first class, created by `def-lvl`
- Calls to a lower level: always allowed
- Calls at the same level: a smaller `subterm` argument
- The termination proofs are usually inferred
- Levels are ordered by creation
- Levels can be created at run time

## 28. What levels give you

- Every function terminates; there's no `partial` escape
- Only same-level calls can recurse
- Only those calls must be marked `tail` or `notail`
- No `notail` marks: stack depth known at compile time
- This holds even through function pointers
- Future: levels as a basis for proving running time

## 29. Types don't compute

- A type never contains a call
- Type checking: canonicalize, then compare
- Termination never reads a type
- So non-positive types like `MkBad : (Bad -> False) -> Bad` are allowed
- Looping through one is rejected at the call

## 30. Matching as forced unification

- Entering a branch adds `is` facts
- Equating two constructors merges their signatures and `Matchable`s, recursively
- The branch is refuted if that fails (`Zero` against `Succ`), or by occurs check (`x` against `(Succ x)`)
- Constructors are first class: two variables may hold the same one
- Axiom K holds by construction

## 31. Settled and Hypothetical

- Run position: outside every function body and branch
- Code there runs as soon as it's checked
- Its results are Settled: values the compiler can use
- Inside a body, everything is Hypothetical
- The type checker itself never evaluates
- `comptime-match`: proof by reflection

## 32. Kernel-style dynamism

```scheme
(def-fns _ $ (many strict? : -> (many (Bool) b)) (BTrue))

(let ((many report))
  (match many (strict?) (((Special) s))
    ((BTrue) compile-error)
    ((BFalse) compile-warn)))

(report "TODO: prove the bound")   ; error, or warning if strict? is BFalse
```

- Kernel (Shutt's Lisp): special forms as first-class values
- Here too: special forms are values of the enum `Special`
- One namespace; even `let` can be shadowed
- A form dispatches only on a head known at compile time (Settled)
- Macros are values too; their output is checked like hand-written code

## 33. A tactic is a macro

```scheme
(lt-lemma (erased mixed : (erased (Nat) a b c)
    (erased (Lt (Succ a) b) h1) (erased (Lt b c) h2) -> (erased (Lt a (Succ c)) r)))

(lt-lemma (erased too-strong : (erased (Nat) a b) (erased (Lt a b) h)
    -> (erased (Lt (Succ a) b) r)))
; error: lt-lemma: no chain of hypotheses reaches the goal
```

- `lt-lemma` reads the lemma's statement as syntax
- Searches for a chain of `Lt` facts and writes the proof
- The proof it writes is checked like any other code
- `too-strong` is false, so no chain exists

## 34. The fact table is the language

| Field | Holds |
|---|---|
| name | optional |
| multiplicity | `erased`, `many` or `unique` |
| state | Settled (with its value) or Hypothetical |
| type | a term |
| `is` | a term: what the entry equals |
| slot | its location (`at`) |
| introduction order | orders levels |
| level marker | set by `def-lvl` |

- Plus the context: current level, enclosing `subterm` arguments
- Nothing else: no list of types, no list of functions

## 35. Two views of the table

- Type checking reads the current facts, branch facts included
- Dispatch reads the facts as of the last run position
- So a branch can't turn a name into `let`
- And a macro expands the same way in every branch

---

# What is proved

## 36. Three implementations

| | Written in | Role |
|---|---|---|
| Reference interpreter and compiler | OCaml | defines correct behavior |
| slc, the compiler | Sleight | compiles itself to identical output |
| Lean model | Lean 4 | machine-checked soundness (a fragment: no macros, arrays or I/O yet) |

- Shared test suite: a disagreement is a bug in one of them

## 37. What the Lean model proves

- `eval`: the evaluator is total, with no fuel
- `checked_runs`: a checked program runs to a value of its type
- `no_false`: no checked program proves `False`
- `eval_sound`: erasing proofs doesn't change the result
- `machine_main`: in-place updates give the same results (open: delegates)
- Native arithmetic is proved against its model
- Three standard axioms, no `sorry`

---

# Close

## 38. What might be new

- First-class levels for termination, with `Type : Type` and no positivity check
- Stack depth known at compile time, even through function pointers
- Erasure and uniqueness on every binder; location as a separate fact (`at`)
- Proofs about overwritten memory
- Kernel-style special forms, compiled and dependently typed
- Performance claims checked at compile time

## 39. What's next

- Finish the Lean proof
- Reconsider the s-expression syntax
- Levels as a basis for proving running time

## 40. Thanks

- Code: [github.com/emmarion/sleight](https://github.com/emmarion/sleight), [doi.org/10.5281/zenodo.23361871](https://doi.org/10.5281/zenodo.23361871)
- Slides: [doi.org/10.5281/zenodo.23367392](https://doi.org/10.5281/zenodo.23367392)
- Questions

---

# Appendix

## A1. Everything that's first class

- Types, type constructors, value constructors
- Functions (`Fn`, `UniqueFn`)
- `Matchable`: which constructors are distinct, as data
- Special forms and macros
- Levels and proofs: `Level`, `Subterm`, `Predates`, `Coercible`, `Delegate`, `AtFn`
- Cells and slots
- No global list of types or functions; everything nests

## A2. Compiled output: Lean vs Sleight

```text
-- Lean 4.34 IR: the index is a field of every cons
let x_3 : tobj := proj[0] x_1;
let x_15 : obj := ctor_1[Vect.cons] x_3 x_11 x_12;

(* Sleight, extracted OCaml: index gone *)
let rec zip_add xs ys = match xs with
  | K5_1 { f0 = x; f1 = xt } ->
      (match ys with K5_1 { f0 = y; f1 = yt } ->
        K5_1 { f0 = add x y; f1 = zip_add xt yt })
  | K5_0 -> K5_0
```

- Lean keeps the length in every cell; Sleight's compiled code has none

## A3. Axiom K in four lines

```scheme
(def-fns _ $ (erased k : (erased Type A) (erased A x) (erased (Eq A x x) p) ->
    (erased (Eq (Eq A x x) p (Refl A x)) q))
  (match erased p _
    ((Refl _ _) (Refl (Eq A x x) (Refl A x)))))
```

- Matching `p` against `Refl` is enough: every proof of `x = x` is `Refl`
- Accepted by both compilers

## A4. Rejecting the paradox

```scheme
(def-adts $ (Absurd : -> Type) enum)
(def-adts $ (Bad : -> Type)
  enum
  (many MkBad : (erased (Level) l) (many (Fn l (many (Bad) b) -> (many (Absurd) f)) g) -> (Bad)))
(def-lvl W)
(def-fns W $ (many omega : (many (Bad) b) -> (many (Absurd) f))
  (let-match many b (MkBad l g))
  (g b))
```

```text
9:3: error: `l` was not in scope when level `W` was minted
```

- `omega` would loop by calling the function stored in its argument
- Rejected: that function's level didn't exist when `W` was created

## A5. Hiding the paradox behind a factory

```scheme
(def-fns F $ (many factory : (many (Bad) b) -> (erased (Level) W) (many (Fn W -> (many (Absurd) f)) o))
  (def-lvl W)
  ...
      (def-fns W $ (many o : -> (many (Absurd) f)) (g (predates pl) b))
      (values W o))))
(def-lvl K)
(def-fns K $ (many knot : (many (Bad) b) -> (many (Absurd) f))
  ...
  (let ((erased p)) (prove-predates W K))
  (o (predates p)))
(knot (MkBad K knot))
```

- `knot` hides the loop behind a level created at run time
- All three implementations reject it: `W` was created after `K`

## A6. Building levels at run time

```scheme
(def-fns _ $ (many compose-all : (subterm many (List (Fn M (many (Nat) x) -> (many (Nat) y))) fs) ->
    (erased (Level) N) (many (Fn N (many (Nat) x) -> (many (Nat) y)) g))
  (match many fs _
    ((Nil a) (def-lvl N)
      (def-fns N $ (many id : (many (Nat) x) -> (many (Nat) y)) x)
      (values N id))
    ((Cons a f rest)
      (let ((erased L1) (many g1)) (notail $ compose-all rest))
      (def-lvl N)
      (def-fns N $ (many g : (many (Nat) x) -> (many (Nat) y)) (f (g1 x)))
      (values N g))))
```

- Each step creates a new level above the last
- The tower is as tall as the list
- Callable only from the top level: `main`'s level is fixed at compile time

## A7. The map factory

```scheme
(def-fns _ $ (many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) -> (many (List B) ys)) mapped))
  (def-fns _ $ (many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) -> (many (List B) ys))
    (match many xs _
      ((Nil a) (Nil B))
      ((Cons a hd tl) (Cons B (f hd) $ notail $ map A B f tl))))
  (values (level-of map) map))

(let ((erased ML) (many map-nat)) (map-factory (level-of inc)))
(map-nat (Nat) (Nat) inc (Cons _ 0 $ Cons _ 1 $ Nil _))
```

- `map` calls `f`, so it must sit above `f`'s level
- The factory creates that level: a level-polymorphic `map`
- Prints `(Cons _ 1 $ Cons _ 2 $ Nil _)`

## A8. The agent tasks

- `spec`, `reverse`: learn the language from the compiler alone (no docs)
- `fib`: a calibration task
- `big`, `big-golf`: write a 2 MiB file (no docs)
- `ip`, `ip-hard`: find the VM's IP, impossible by design; with (`ip`) or without (`ip-hard`) source
- `false`: prove False
- `heapsort-fast`, `manacher-fast`: certified and fast
- `sl-tools`: build tools for future agents
- The rest get DESIGN.md, the prelude and the tests

## A9. What the runs found

- `false`: no proof of False, but a real lead
- `ip`: placeholders, honestly labelled
- `ip-hard`: answered "UNKNOWN"
- A compiler crash, found from a model's notes
- `unary` gets slow past distance 400

## A10. The working method

- One human designs, agents implement
- Agents propose, the owner decides
- DESIGN.md uses only the owner's exact wording
- Every file says how far to trust it
- Compile a claim, don't argue it

## A11. The soundness sketch

- (C) checking terminates
- (T) every call returns
- (S) no memory word is read as the wrong type
- (E) erasing proofs doesn't change the run
- Invariants: facts hold; `Subterm` is strict; `Predates` follows creation order

## A12. The three refutation cases

- Occurs check: `x` against `(Succ x)`
- Clash: constructors one `Matchable` keeps apart (`Zero` against `Succ`), signatures that can't unify, or `Matchable`s that can't merge
- A function type's own parameter equated with an outside variable (`tests/binder_clash.sl`)

## A13. `Matchable` and opening

- `(Matchable enum List (many Nil) (many Cons))`
- At most one opened `Matchable` per constructor
- Two that collide either unify or contradict
- An unopened type constructor unifies with any of the same signature

## A14. The uniqueness audit

- Of the uniqueness implementation, written by Codex
- About 200 adversarial probes
- No way found to alias a unique value or misread memory
- F1: wrong value from an erased word, fixed
- Q5: slot-indexed types, still open

## A15. Arrays

- Indexed by the list of its elements
- `Nth`, `SetNth`, `Repeat`, `Length`
- `MaybeUninit`: one word either way
- `array-pluck`, `array-unpluck`: free in-place row updates
- `init-witness`: a zero-cost coercion

## A16. `Sharing` sides

- `wrap` puts `(Shared)` on a many field's source side
- `trans` needs equal middle sides
- Stops a shared value from becoming unique

## A17. Macro primitives

- `gensym`, `gensym-unique`, `settled-eq`
- `intern-nat`, `-char`, `-string`, `mint-settled`
- `resolve`, `read-file`, `settled-of`
- `settled-type`, `-erase`, `-mult`, `-value`
- At most 10,000 expansions per run

## A18. The machine-level proof

- The machine run: cells written in place, slots as words
- `machine_main`: it ends where the stripped run does
- Assumes: no delegates
- Three standard axioms, no `sorry`

## A19. Lean runner vs OCaml, on the test suite

- 327 accepted, same value as OCaml
- None mismatched
- 474 rejected by both
- 182 unsupported; 19 rejected only by Lean
- No test OCaml rejects is accepted

## A20. Merge sort: Sleight vs Lean

- In-place list merge sort, certified
- Same algorithm proved in Lean
- 0.6–0.78 s vs 1.0–1.33 s, 1M elements
- About 140–210 words allocated

## A21. Sources

- seL4 20:1, CertiKOS 15:1, CompCert 7:1, SeKVM 7:1
- IronFleet 5:1 safety, 8:1 liveness; Verus 7.5–10:1
- OpenAI, [github.com/openai/math](https://github.com/openai/math)
- Tsoukalas et al., arXiv 2605.22763
- Xu & Odersky; Kan, Kan & Ertel; Verina; Qin et al.

## A22. Numbers

| What | Count |
|---|---|
| Spec (DESIGN.md) | 66 sections |
| Decisions made without the owner (ASSUMPTIONS.md) | 204 items |
| Reference interpreter, OCaml | ~6,100 lines |
| Self-hosted compiler, Sleight | ~16,700 lines |
| Lean model | ~19,800 lines |
| Test files | 1,027 |
| Self-hosting check | 948 run identically, 1,171 refused as expected, 0 failed |

## A23. All the sort times

| Heap sort, 2^20 ints | M4 Pro | Xeon 8358 |
|---|---|---|
| ATS, certified, clang | 50 ms | 105 ms |
| C, clang | 50 ms | 128 ms |
| **Sleight, certified, three agent runs** | **88–91 ms** | **136–157 ms** |
| Sleight, certified, Claude outside the runner | 91 ms | 145 ms |
| C, gcc | | 140 ms |
| ATS, certified, gcc | | 140 ms |
| OCaml, -unsafe | 92 ms | 164 ms |
| OCaml | 101 ms | 178 ms |
| Lean, verified | 118 ms | 228 ms |
| Idris 2, certified | 210 ms | 425 ms |

## A24. Line counts for the same sort

| Sort | Verified | Lines |
|---|---|---|
| C | no | 17 |
| OCaml | no | 23 |
| ATS | no | 26 |
| Lean | yes | 263 |
| ATS | yes | 281 |
| Idris 2 | yes | 338 |
| Sleight, Claude outside the runner | yes | 611 |
| Sleight, three agent runs | yes | 834–2,099 |

## A25. Idris 2: linearity isn't uniqueness

```idris
leak : LinArray Int
leak = newArray 1 (\1 a => a)        -- the continuation returns the array

main = do
  let a = leak                        -- now unrestricted
  let (_ # a1) = write a 0 1
  let (_ # a2) = write a 0 2          -- `a` used again
  let (v1 # _) = mread a1 0
  printLn v1                          -- Just 2
```

- Linearity limits how the callee uses a value, not who else holds it
- In-place writes rely on the array never leaving `newArray`'s scope
- It can leave: `a1` now reads `2`
- Linear Haskell blocks this: the result must be `Ur`, which an array can't be
- Sleight's `unique` is on the binder: no scope rule to escape
