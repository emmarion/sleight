# 04. The compiler route and the output end

Written overnight by an agent exploring options while the owner was
asleep. Everything here is a proposal or a reading. Nothing in it is
approved, and nothing here is a design decision.

Labels used below: **[D]** what DESIGN.md says (quoted, with §), **[C]**
what the code does (file:line), **[T]** something I compiled or ran, **[O]**
an owner decision from the brief's list, **[P]** my own reading, inference, or
proposal.

## 1. Summary

- [C] slc is about 18,650 lines across 12 files. It carries proofs of
  *termination, totality, scoping, and in-bounds access*. It carries **no** proof
  that relates its output to a specification: nothing in `self/` has a
  judgment ("this raw elaborates to that", "this code evaluates to that").
  By a crude count, about 6% of its lines are erased lemmas, and almost all
  of them sit in `heap.sl`, `escape.sl`, `base.sl`, and `core.sl`. The
  elaborator, the interpreter, and the emitter (about 12k lines) are trusted
  plain code as far as correctness goes.
- [P] Recommendation: **route 3**, a new elaborator written spec-first as
  deriving functions over the formal relations, in the shape `mini/` already
  uses. It would reuse slc's proved libraries and possibly its reader.
  **Route 4** (translation validation) would be used at the output end
  only, by re-parsing the emitted text. Retrofitting slc (route 1) looks
  costly and serial. A de Bruijn kernel (route 2) saves less than usual,
  because Sleight's expensive checking (forcing, slots, uniqueness, `at`)
  is in the core and not in the sugar.
- [P] Fuel: there are two ways to keep fuel out of the *theorem*. One is
  the iterative-deepening driver: a `Program` loop that retries with more
  fuel, so each step is total and fuel never appears in the statement. The
  other is an explicit-stack compiler stepped by the driver.
- [P] Output end: first stop the proof at the post-erasure IR (slc's
  `Code`, 17 constructors, `core.sl:604-623`). Later, model the small
  untyped OCaml subset that `emit.sl` actually writes, and check the printer
  per run by re-parsing.
- [C/T] Concrete risks found: the emitter relies on call and constructor
  arguments being atoms, which nothing types. A printer depth budget makes
  `slc --interpret` print a wrong value (`... Cons _ _ _)`) for a list of
  more than about 50,000 elements. The `-imm` FFI operations bypass
  OCaml's write barrier. `slot-eq` compiles to OCaml `==`, and ocamlopt
  shares equal immutable constants, so a compiled run can answer `ESome`
  where `slc --interpret` answers `ENone` (2.5).
- [C] There are 103 FFI implementations and 7 extern types. Under §42 each
  one is an agreement axiom.

## 2. Findings

### 2.1 slc's pipeline

- [C] Source order (`self/bootstrap.sh:23`): `std/list.sl`, `std/macro.sl`,
  `base`, `escape`, `heap`, `reader`, `core`, `eval`, `elab`,
  `lib/embed.sl`, `header`, `emit`, `elab-main`, `interp`, `main`.
- [C] Reader: `self/reader.sl` (742 lines). It includes the port of
  `lib/indent.ml` (`self/README.md:92-102`).
- [C] Elaborator: `self/elab.sl` (5139 lines) and `self/elab-main.sl`
  (3398 lines). The main block starts at `elab-main.sl:158`. It is one
  mutually recursive `def-fns` that holds the compile-time interpreter
  (`eval`, `apply`, `run-code`, `elab-main.sl:158-445`), the macro
  expander (`splice-go`, `elab-main.sl:577-586`, with the 10000-expansion
  limit at `:511` and `:560`), and the elaborator proper.
- [C] Post-erasure IR: `Code ctx ms` (`core.sl:604-623`), indexed by its
  frames and by the multiplicities of its results. Its constructors are
  `CVar`, `CConst`, `CValue`, `CErased`, `CValues`, `CApp`, `CLet`,
  `CLetRec`, `CMatch`, `CCellAlloc`, `CCellWrite`, `CCellCopy`,
  `CCellRead`, `CWorldDo`, `CPrim`, `CAbsurd`, and `CError`. A run-position
  value is embedded as a `CValue` block or a `CConst` id. The emitter
  writes the compile-time heap blocks, closures included, as OCaml data
  (`self/README.md:353-362`).
- [C] Emitter: `self/emit.sl` (1516 lines) writes OCaml text as a rope.
  `lib/ffi_core.ml`, `lib/driver_core.ml`, `self/runtime.ml`, and
  `lib/ffi_templates.txt` are embedded into slc when slc is compiled
  (`bootstrap.sh:26`, `self/README.md:133-142`).
- [C] `slc` runs a whole compile inside **one** `Program` step: `start`
  is a single `def-unique` continuation (`self/main.sl:187-191`). So
  every compile-time evaluation sits inside one call to a total function.
  [P] The interpreter would need fuel (or some other measure) even with
  more steps, since one total step cannot run an arbitrary evaluation to
  completion; the single step only means the driver loop is not used to
  spread the work.
- [C] `self/README.md:463-465` says macros are "Not modelled". The macro
  expander at `elab-main.sl:505-586` contradicts that. The README line
  looks stale.

### 2.2 What already carries proofs

All [C]. Line counts come from a crude awk heuristic: lines inside a
definition whose header is `(erased name :`.

| file | lines | in erased lemma defs | what is proved |
|---|---|---|---|
| heap.sl | 253 | ~148 (58%) | the store's `alloc` and `deref` are total, by size (`README:85-91`) |
| escape.sl | 317 | ~64 (20%) | every read and write in bounds (`README:74-84`) |
| base.sl | 1148 | ~197 (17%) | deciders return evidence: `Cmp`, `MapsTo` or `Absent`, `Nth`, `Length`, `Concat` (`README:63-73`) |
| core.sl | 4133 | ~637 (15%) | canonicalization and forced unification terminate by proof; fact-table invariants (`README:282-297`); opened-object index (`README:327-352`) |
| elab.sl, elab-main.sl | 8537 | ~14 (≈0%) | termination: `Steps` budgets (`elab-main.sl:1243, 1305, 1327, 1725-1772`), `hop-` constants (`elab-main.sl:147-156`); arity and length invariants: `Lockstep`, `Picked` |
| eval.sl | 1652 | ~15 | store growth (`Suffix`), scoping of `Code` |
| emit.sl | 1516 | 0 | termination only (`README:263-264`) |
| reader, interp, main | 1090 | ~9 | essentially none |

- [C] Total: about 1,084 of about 18,650 lines (≈6%) are lemma
  definitions. More code carries intrinsic indices, such as
  `Code ctx ms`, `Heap hs`, and `Table n f c`. Those indices give
  scoping and arity, not correctness.
- [C] Plain code with respect to correctness:
  - **Errors are values.** An elaboration error is recorded and
    elaboration goes on (`README:298-311`).
  - **The interpreter is untyped.** It returns error blocks for "not a
    group", "no such member", "arity mismatch", "internal: an alias
    applied", and "out of fuel" (`elab-main.sl:185-187, 404-437`).
  - **"internal:" sites.** A grep finds 20 string literals beginning
    `"internal:` in `self/*.sl` (12 in `elab.sl`, 6 in `elab-main.sl`, 1
    each in `eval.sl` and `emit.sl`). Examples: `elab.sl:984` ("has no
    value"), `elab.sl:1659` ("not bound at runtime"), and
    `elab-main.sl:1871` (sugar budget spent). Each one marks an invariant
    that is believed but not proved.
- [P] My estimate of how near slc is to the shape a correctness proof
  needs: **0%** has a spec relation, and ≈15–20% of the code (the
  libraries and the canonicalization and unification core) carries
  invariants that a correctness proof would reuse. The rest would need to
  be re-shaped rather than annotated.

### 2.3 Fuel and budget uses in slc

| site | kind | zero case |
|---|---|---|
| interpreter `eval`/`apply` (`elab-main.sl:185-187, 424`) | fuel. MANUAL.md:154-162: "bounds how deeply applications nest, a tail call nesting inside the call it replaces"; slc's default 10^9 | error value "out of fuel", reported as an error. MANUAL calls it a §31 crash |
| `show-at` depth 100000 (`elab.sl:4680-4682`, used at `elab.sl:4730`, `interp.sl:15`) | printer fuel | **prints `_` silently**. The budget is spent twice per nested field (`show-at` at `elab.sl:4682` and `shown-field` at `:4717`). [T] `slc --interpret deep.sl` (a 100003-element list, stack unlimited) prints 49,999 `Cons _ 0` and then `Cons _ _ _)`. [P] That is a wrong output under §45 ("Any other value prints by its type", and `_` is listed only for a union with more than one constructor, erased fields, cells, slots, functions, opaque proofs, and values with no readable `Matchable`), not a §31 crash ("A crash produces no value, never a different one") |
| `show-fuel` 100000 (`emit.sl:4`, `:1473`, `:1478`) | fuel for generating type printers | not examined |
| `heap-strs-fuel` 10^6 (`eval.sl:1018-1025`; also passed to `heap-pairs` and `heap-jobs`, `eval.sl:1055, 1146, 1159`) | fuel | truncates the list (returns `Nil`) |
| `str-split-fuel` (`base.sl:100-109`) | fuel equal to the string's length | unreachable but not refuted |
| sugar budget (`elab-main.sl:1871`, `README:385-394`) | budget sized by the form | "internal" error, not refuted |
| `Steps n` (`elab-main.sl:1243...`) | budget | zero case refuted by type |
| macro expansions ≤ 10000 (`elab-main.sl:511, 560`; the elaborator group's first `subterm` parameter, named `fuel`, is this budget and is checked again at `:586, 764, 779`) | **specified**: [D] §62 "At most 10000 expansions run in one run, every file on the command line included." | refusal, as §62 requires |

- [P] So the only fuel a correctness theorem must face is the interpreter's
  (and the printers', which look like plain bugs that could be fixed by
  recursion on the value's structure). The expansion limit is part of the
  language.

### 2.4 `mini/`'s deriving functions (the shape route 3 would copy)

- [C] Each judgment is an ADT whose constructors are its rules
  (`mini/elab.sl`). For example, `ElabProgram` at `mini/elab.sl:1229-1235`
  has `ProgramOk`, `ProgramSize`, and `ProgramErr`, and `Fails` is defined
  from it at `:1241`.
- [C] The deriving function returns the derived data with an erased
  derivation, or `Stuck`:
  `elab-program : (List Sexp) items -> (ProgramDec items)`, where
  `MkProgramDec` holds `(many POut out) (erased (ElabProgram items out) p)`
  and `ProgramStuck` holds nothing (`mini/elabfn.sl:2373-2386`). The
  intermediate functions do the same (`TermDec`/`TermStuck`,
  `mini/elabfn.sl:744-747`). Every function threads the context's
  well-formedness `WF` (`mini/README.md:51-59`).
- [C] Only `eval` uses fuel (`mini/eval.sl:53-54, 102-103, 111-112`).
  `mini`'s language has **no run position**: nothing in `mini/elab.sl`
  calls the evaluator. So `mini` never meets the §29 round trip.
- [P] `Stuck` is soundness without completeness. Owner decision [O]3 ("It
  should be a theorem that every program's source code is either accepted
  or rejected as an error") needs `Stuck` to be refuted. Two ways to do
  that: make every raw shape either derive or `Fail`, or prove that the
  `Stuck` cases are unreachable from a WF context.

### 2.5 What `emit.sl` emits and relies on

- [C] Every value is an `Obj.t`. The casts are `%identity` externals
  (`lib/ffi_core.ml:1-5`, `to_any`/`of_any`/`cast`). Tagged types become
  OCaml variants per *shape* with **mutable** inline records of `Obj.t`
  (`emit.sl:291`, `README:212-246`). A cell write is `r.fi <- arg`
  (`emit.sl:823`). So slc mutates only blocks that OCaml declares
  mutable. I found no `Obj.set_field`.
- [C] A call is written `(name a1 ... an)` and a constructor is written
  `K { f0 = a0; ... }`, with the argument texts inlined
  (`emit.sl:909-919`, `build-rope` at `:452-459`). `CApp`'s arguments have
  type `List (Code ctx many-one)` (`core.sl:611`), so nothing in the types
  says that they are atoms.
- [T] In practice the elaborator hoists every non-variable argument into a
  `let`, as §15 describes. In `proto/04-compiler-route/order.sl` and
  `ord2.sl` each call or constructor argument that is not a variable is
  let-bound before the call that uses it. The bindings are in source
  order in `order.sl`, but not in `ord2.sl` (next item), so the emitted
  order is §15's placement, not source order in general. A multi-value result is sequenced by
  `let tup_a0 = ... in let tup_a1 = ... in` (`emit.sl:365-369`). [P] So
  OCaml's unspecified (in practice right-to-left) argument order does not
  matter *today*, but only because of an untyped invariant of the
  elaborator. [T] A two-argument test (`proto/04-compiler-route/argorder.ml`)
  evaluated right to left under both ocamlopt and ocamlc 4.14.1. Extern
  templates use an argument several times, as the `Succ` fast path
  `if Obj.is_int {a0} && ... {a0} ...` does (`lib/ffi_templates.txt:10`;
  holes `HArg i`, `emit.sl:105, 333`). An argument that is not an atom
  would be evaluated more than once.
- [D] §15: "Every argument to a constructor, a function or a cell behaves
  as if it were first bound to an anonymous variable. ... That binding is
  a statement (§27) placed just before the statement or final form that
  contains the call". [T] In `ord2.sl`, `(values (f a a) (f (Succ a) a))`
  binds `Succ a` *before* `(f a a)`, consistent with that sentence.
- [C] **Refutation is trusted at output.** A match with no default arm, or
  a phantom-index GADT copy that omits refuted constructors, is matched
  after an `of_any` cast. `README:242-244`: "A wrong refutation would
  misdispatch silently here". [P] So the OCaml program's memory safety
  rests on the elaborator's correctness, which is exactly what a proof
  would supply.
- [C] `slot-eq` compiles to `(if h == b then some else none)`
  (`emit.sl:966-968`). [P] [D] §67 allows `ENone` always, but `ESome`
  "proves that `a` and `b` hold one word". If OCaml or flambda shares two
  structurally equal *immutable* constants (slices, tuples), `==` says
  `ESome` for two values the spec allocated separately. [T] This
  happens without flambda: `proto/04-compiler-route/share.ml` finds two
  equal `("ab", 0, 2)` tuple constants `==` under ocamlopt 4.14.1 (not
  under ocamlc), and `slot_eq_share.sl`, two run-position
  `(str-append "a" "b")`, prints `(BTrue)` compiled by slc and
  `(BFalse)` under `slc --interpret`. [P] §67 allows both answers ("which
  one a call answers may differ between runs"), and in the compiled run
  the two do hold one word. It is a refinement mismatch only if the spec
  says that every allocation takes a never-used address (the earlier
  session's proposal B).
- [C] The `-imm` operations write through `(cast a : int array)` with
  `Array.unsafe_set` and `caml_blit_bytes` (`lib/ffi_core.ml:234-241,
  315-320`). [P] These skip `caml_modify`, which I believe is safe only
  when both the old and the new words are immediates, as `(imm o n)` and
  `Imm` require ([D] §37, §44). This is a dependency on OCaml runtime
  internals (GC barriers). The code comment at `ffi_core.ml:315-316`
  concerns speed, not safety; I found no safety argument and did not
  check one.
- [C] `Bytes.unsafe_to_string` without a copy (`lib/ffi_core.ml:148, 173,
  260`). `bytes-str` takes its `Bytes` at `many` (`lib/prelude.sl:1738`).
  [P] This is safe only if a `many` `Bytes` is never mutated afterwards.
  That follows from §13/§16 (only `unique` is mutated; `share` ends unique
  uses) if uniqueness checking is sound. I found no counterexample, and I
  did not search hard.
- [C] The runtime checks, once at start-up, that ints have 63 bits, that
  zarith holds small values unboxed, and that the host's maximum array and
  string lengths are below 2^54 and 2^57 (`lib/ffi_core.ml:27-28`). Element
  accesses use `unsafe_get`/`unsafe_set` with no bounds check
  (for example `ffi_core.ml:139, 223-241, 254`), relying on the Sleight-side `Nth`
  evidence. `Nat` is a `Z.t`, with an inline fast path
  for small ints in the emitted `Succ`.
- [T] **Tail calls.** `README:244-246` says tail-position calls are OCaml
  tail calls. On this machine (amd64, OCaml 4.14.1), a tail call into a
  20-argument function ran 10^7 iterations under a 1 MB stack, while a
  non-tail control overflowed (`proto/04-compiler-route/tc3.ml`, `tc4.ml`).
  [T] Re-run in review: the call in `tc3.ml` goes through
  `caml_apply20` and is emitted as a `jmp`; a direct 20-argument call to
  a known function is also a `jmp` (no flambda).
  [P] I did not find a platform where OCaml drops a tail call with many
  arguments. Whether `tail` (§19: "A claim the compiler cannot honour is an
  error") holds on every OCaml target remains unverified.
- [C] `self/release.sh:17` builds slc with `-O3` when flambda is
  available, so such release builds also trust flambda with `Obj.t`
  casts. The ocamlopt on this machine reports `flambda: false`.

### 2.6 Extern and FFI inventory

- [C] `lib/ffi.ml` registers **103** function implementations and **7**
  extern types: `Array`, `Bytes`, `Slots`, `Nat`, `Half`, `String`, and
  `Raw` (`lib/ffi.ml:45-73` for the types, `:98-201` for the functions). `lib/prelude.sl` also declares
  6 `extern at` functions with no implementation: `array-unpluck`,
  `nat-same`, `string-same`, `bytes-same`, `array-same`, and `half-same`
  ([D] §39: "the marks are a promise").
- [C] Classified by name:

  | class | count | examples |
  |---|---|---|
  | `Nat`/`U62` arithmetic and bits (pure) | 41 | add, divmod, nat-cmp, u62-*, popcount |
  | strings (pure, slices) | 12 | str-cmp, str-split, append, flatten, nat-str |
  | bytes (mutation at unique) | 24 | bytes-set, bytes-blit, bytes-str |
  | arrays (mutation at unique, `-imm` barrier-free) | 22 | array-swap, array-pluck, array-blit-imm |
  | `Slots` (searches with `slot-eq`) | 4 | slots-find, slots-intern |

- [C] These are *not* in the FFI table but are implemented by the
  driver, the elaborator, or the runtime:
  - `world-do`, with 21 request kinds (`Driver_core.request` in emitted
    code, `K3_0`..`K3_20`);
  - `slot-eq`, `cell-same`, and `fn-same`;
  - the handle and macro-world primitives of §64-65;
  - `native-compute`.

  [P] These are specified by DESIGN.md directly, not by models. So they
  are part of the spec semantics, not agreement axioms. The exception is
  `world-do`: the world's answers would have to be a parameter of the
  semantics (an oracle).
- [D] §42: "An `extern` implementation must agree with its model: except
  through `slot-eq` (§67), running the models instead of the
  implementations must give a program the same values, though not the
  same cost, and either may crash where the other does not (§31)." [P] So
  each of the 103 implementations, and each extern type's view and wrap
  pair, is one axiom of the form "agrees with the model up to crash". The
  correctness theorem can only be "same values, up to crash".
- [C] slc does not model `--no-extern`: its interpreter always runs the
  FFI (`README:463-464`). So even slc's *compile-time* results rely on the
  FFI agreement axioms.

### 2.7 `native-compute` in slc

- [C] `native-batch` (`elab-main.sl:119-131`) does the following:
  - emits the program so far with slc's own emitter;
  - runs `ocamlfind ocamlopt` through `world-do Exec`
    (`native-run`, `elab-main.sl:40-60`);
  - reads back each result as a printed constructor index.
- [C] `--no-native` runs the same calls in the evaluator (`README:183-184`),
  and `bootstrap.sh` compares the two modes.
- [D] §29: "A stored value that `native-compute` produced relies on its
  compiled run in the same way (§72)". §72: "It may crash where the
  evaluator would not, and the other way round (§31). A program that
  cannot be compiled is an error at the form, and a run that crashes is
  an error at its argument."

### 2.8 Who checks slc's proofs today

- [C] `bootstrap.sh` step 1: the reference (`lib/*.ml` and `bin/*.ml`,
  about 6,900 lines of OCaml) type-checks `self/*.sl` while extracting stage 1. Step 3: slc
  checks itself, twice, and the two outputs must match byte for byte
  (`README:198-201`).
- [C] slc's own proofs use **proof by reflection**: `comptime-match` and
  `prove-literal-lt` at `self/base.sl:157-161, 181-182`. [D] §29 says
  such facts rely "on the evaluator having evaluated correctly". [P] So
  the trusted base of slc's proofs includes the checking implementation's
  evaluator **and its FFI** (`nat-eq` is extern).

## 3. Options

[P] Every effort, cost, and risk rating in this section is my guess, not
a measurement.

### Q1. The route

Each route is described by what is proved, what is trusted, how it handles
the round trip, its effort, its risks, and how it parallelizes.

**R1. Retrofit slc.** Change slc's functions to return erased derivations
of the spec's relations, as `mini/` does.
- *Proved:* everything slc does, if finished.
- *Trusted:* only the spec, the checker, OCaml, and the FFI.
- *Round trip:* natural, because slc's interpreter is already inside the
  elaborator's block. Its results must come with an evaluation derivation.
- *Effort:* very high.
  - The main block is **one** mutually recursive `def-fns`
    (`elab-main.sl:158` onward), so a change of return type ripples
    through every function in it.
  - The interpreter is untyped (2.2) and would need a typed-heap
    invariant.
  - Errors-as-values with cascades (`README:298-311`) are not the shape
    of a `Fails` derivation.
  - The 17 "internal" sites become proof obligations.
- *Risk:* high. The shape slc took was chosen for termination and speed
  (the opened-object cache, ropes, templates, `Steps`, `hop-`), not for
  correspondence with a relation. Proofs would fight caches whose
  agreement with the uncached search is a discipline, not a theorem
  (`README:347-350`: "What the index does not prove is that a cached name
  is canonical").
- *Parallelism:* poor. One block, one signature set. Agents would
  serialize on `elab-main.sl`.

**R2. Certified kernel behind slc's front end** (de Bruijn criterion).
slc's reader, macro expander, sugar (§46-53), `_` solving, decrease
inference (§48), and messages stay unproved. They output a fully explicit
core program, which a proved kernel re-checks and compiles. The kernel is
a checker, an evaluator, and a code generator.
- *Proved:* the kernel.
- *Trusted:* nothing in the front end for the *type safety* of the core
  program the kernel accepts; a front-end bug there can only cause a
  rejection. [P] The front end is still trusted for *meaning*: a wrong
  desugaring, macro expansion, or reading can produce a different core
  program that the kernel accepts, so the theorem relates the output to
  the front end's core program, not to the source.
- *Round trip:* [D] §6 dispatch, §28 `comptime-match`, and §45 literals
  depend on stored values. The kernel cannot trust the front end's values,
  so it must **re-run every run-position form** with its own evaluator, or
  check an evaluation trace. Traces are as long as the run.
  - Macro expansion need not be re-run. [D] §62: "The forms are elaborated
    and checked as if they had been written there". [P] But then the
    theorem speaks of the *expanded* program. The source-to-expanded step
    is trusted, which sits uneasily with [O]3, which speaks of source text.
    Closing that gap means proving the expander, which runs the evaluator
    on macro functions and reads elaborator state (§64-65 handles,
    `resolve`, `settled-eq`).
- *Effort:* high. [P] The kernel is not small. Forcing (§7), `Matchable`
  (§8), erasure (§14), uniqueness (§15-16), slots, `at`, and cells
  (§35-41) are all core, and they are most of the checking. The savings
  are the reader, sugar, metas, messages, and `dump-context`. I could not
  measure what fraction of slc those are.
- *Risk:* medium. There are two checkers to keep in agreement, and a kernel
  rejection of front-end output is an unhelpful error.
- *Parallelism:* good between front end and kernel. Inside the kernel,
  the same as R3.

**R3. New compiler written spec-first.** For each judgment of the formal
spec, write a relation and, beside it, a deriving function returning the
derivation, threading WF invariants, as `mini/elabfn.sl` does. Reuse
slc's proved libraries: heap, escape, base deciders, and the
canonicalization and unification invariants, adapted.
- *Proved:* elaboration agrees with the relations (accepted ⇒ `Ok`
  derivation, rejected ⇒ `Fails` derivation); compile-time values agree
  with the spec run; the IR agrees with the spec run.
- *Trusted:* the reader (unless the spec starts at text), the output end,
  the FFI, and the checker.
- *Round trip:* designed in. The elaboration relation takes the spec
  run's result as a premise at each run-position form. The deriving
  function calls the proved evaluator, which returns a derivation of that
  run.
- *Effort:* [P] the largest up-front cost, but it is mostly writing
  rather than surgery. `mini/` is 6849 lines in all, of which
  `mini/elab.sl` (1243 lines) holds the elaboration relations and
  `mini/elabfn.sl` (2388 lines) the deriving functions; the rest is
  contexts, canonicalization, unification, and evaluation. It covers a
  language without multiplicities, slots, macros, or run position. Scaling that by DESIGN.md's size is
  guesswork. Tens of thousands of lines seems likely.
- *Risk:*
  - the formal spec is wrong, which no proof catches;
  - performance: slc's speed came from caches (`README:351-352`: 66 s to
    under 3 s for the opened-object cache);
  - `Stuck` cases left open (2.4).
- *Parallelism:* **best.** Once the context, `WF`, and term interfaces are
  frozen, each judgment's relation and deriving function is an
  independent work item. `bootstrap.sh`-style differential testing
  against slc and `lib/` checks each one.

**R4. Translation validation.** An unproved compiler (slc) emits, per run,
a certificate. A proved checker validates it.
- *Proved:* the checker.
- *Trusted:* nothing in slc for soundness.
- *Round trip:* [P] for acceptance, the certificate is the typing
  derivation plus an evaluation derivation for every run-position form.
  The second is as long as the compile-time run. The alternative is for
  the checker to re-run a proved evaluator, which turns it into most of
  R3's compiler. For rejection, the certificate is a `Fails` derivation,
  which is cheap.
- *Effort:* medium if R3's relations exist (the checker is a derivation
  checker), and slc must be taught to emit derivations, which is R1-like
  surgery on its outputs. High otherwise.
- *Parallelism:* good. The compiler keeps evolving while the checker is
  built.
- [P] **Where R4 is clearly worth it: the output end** (Q2, option O4).

**[P] Recommendation:** R3 for elaboration and evaluation, with R4 only
at the output end. R2 and R3 converge anyway: a "kernel" of R3's
relations plus the deriving elaborator, with slc's reader in front.

### Q2. Removing fuel from the theorem

**F1. Iterative deepening at the driver.** Keep fuel in the code. The
compiler is a `Program` whose step runs `compile-with-fuel n` and, on
running out, returns `Continue` with fuel `2n`. The theorem needs a
monotonicity lemma (a result at fuel `n` is the result at every `m ≥ n`)
and an adequacy lemma (if the spec run halts, some fuel suffices).
Statement: "if every compile-time spec run halts (the H of [O]4, with
which the owner was in general agreement but not agreement to an exact
statement), the loop exits with the spec's verdict". No fuel appears in
the statement.
- *Pros:* small change to any route. Fuel stays only as an internal
  device. It uses [O]2's driver loop, though not in the fuel-free way
  [O]2 has in mind.
- *Cons:* restarts repeat work. [P] How much depends on what fuel counts:
  with fuel that counts steps and doubles, the failed attempts cost at
  most about as much as the last one; with slc's fuel, which bounds
  nesting depth (MANUAL.md:154-157), a failed attempt can do nearly all
  of the successful run's work, so the overhead can grow with the number
  of doublings.
  Compile-time effects repeat (`native-compute`'s temporary files and
  processes; `read-file` is idempotent). The step function still contains
  fuel.

**F2. Explicit-stack compiler.** The elaborator and the evaluator are one
small-step machine with a total step function, and each driver step
does bounded work. There is no fuel anywhere. Every `Continue` is related
by an erased proof to a prefix of the spec derivation (proposal C in the
brief).
- *Pros:* no fuel at all. It is the cleanest theorem: "the compiler can
  only diverge if the spec run diverges" ([O]4 i) becomes a
  step-correspondence lemma.
- *Cons:* the elaborator must be suspendable mid-form, because run
  positions nest (§27 "This nests") and macro calls run the evaluator
  from inside elaboration. That is a CPS or defunctionalized elaborator,
  which is much harder to write as deriving functions. It fits R3 better
  than R1. It is costly.

**F3. Keep fuel in the theorem**, as slc and `mini/eval.sl` do: "with
enough fuel, ...". This is the cheapest option and conflicts with the
owner's goal of minimizing fuel.

[P] Recommended: F1 now, and F2 only if the owner wants fuel gone from
the code as well as from the statement.

### Q3. The output end

**O1. Stop at the IR.** Prove agreement down to slc-style `Code` plus the
embedded heap snapshot. Trust the emitter, `runtime.ml`, `ffi_core.ml`,
`driver_core.ml`, the templates, and OCaml.
- *Pros:* cheap. It covers everything that is Sleight-specific.
- *Cons:* about 1.5k lines of `emit.sl` plus about 830 lines of OCaml
  runtime (`ffi_core.ml` 398, `driver_core.ml` 408, `runtime.ml` 21) and
  the templates stay trusted. The atom invariant (2.5) is
  unchecked.
- *Cost:* low.

**O2. Model the emitted OCaml subset.** [C] What is actually emitted:
- `let`, `let rec ... and`, `fun`, and full application;
- a `match` on variants with inline mutable records, and `r.fi <- e`;
- tuples;
- the `%identity` casts, `Obj.is_int`, `==`, `failwith`, and `exit`;
- calls into `Ffi_core` and `Driver_core`.

[P] Because of the casts, the honest model is an **untyped word-and-block
heap machine**: blocks with tags and mutable fields, immediates, and
closures. That is very close to the heap machine the owner suspects the
spec run should be ([O]6). The proof is IR → subset AST agreement. The
printer is decision-free text.
- *Pros:* removes the emitter from the trusted base. The atom invariant
  becomes a checked property, for example an IR whose `CApp` takes
  `Atom`s only.
- *Cons:* we still trust that ocamlopt (and flambda under `-O3`)
  compiles the subset per the model. That covers `Obj.t` casts (sound
  only for well-typed source, which O2's proof gives), tail calls (2.5),
  and GC barriers for the `-imm` operations.
- *Cost:* medium.

**O3. Emit something easier to model.** Options include a bytecode run by a
tiny trusted VM, or C.
- *Pros:* the semantics of the target is ours, and evaluation order,
  tail calls, and representation are explicit.
- *Cons:*
  - a new VM or runtime with its own GC (C) or performance cost (VM);
  - it abandons what `README:212-215` reports as the owner's decision
    that `lib/extract.ml` is the specification of slc's emitter (not in
    the brief's list of owner decisions, so treat it as unconfirmed);
  - [D] §1's fast-code aim is "an aim for the language, not for the
    implementations", so O3 is allowed.
- *Cost:* high.

**O4. Translation validation of the printer** (combined with O2). Emit
fully parenthesized text. A proved parser for the subset reads it back,
and the result must equal the proved IR → subset translation.
- *Pros:* the printer stays unproved and fast.
- *Cons:* we still trust that OCaml's parser reads the subset as ours
  does. A fully parenthesized grammar keeps that small.
- *Cost:* low on top of O2.

[P] Recommended: O1 first. Then O2 + O4 once R3's IR is stable. Make the
IR's call and constructor arguments syntactically atomic in either case.

### Q4. `native-compute`

- **N1. Exclude** it from the proved fragment: the theorem has a
  side condition "no `native-compute`".
- **N2. Oracle.** The theorem is conditional on each native run returning
  what the spec run returns. [D] §29 already concedes that this is a
  reliance.
- **N3. Same trust as the output.** `native-compute` runs the proved
  compiler's own emission of the program so far, plus OCaml. The theorem
  is "if the output end is correct (the O1 or O2 trust), `native-compute`
  agrees up to crash". [P] This adds little trust beyond the output
  end's: also the host's process execution, temporary files, and slc's
  reading back of the printed answers (`elab-main.sl:40-60`), and the
  native build's own ocamlopt flags.
  [P] This is the natural fit, with N2's wording as the formal premise.
  [D] §72's "may crash where the evaluator would not, and the other way
  round" already gives the "up to crash" slack.
- **N4. Validate** by re-running in the proved evaluator. This defeats the
  purpose except as a check mode (slc's `--no-native` already exists).

### Q5. Bootstrapping and the trust base

- **B1.** The proved compiler P is checked by **both** `lib/` (OCaml) and
  slc, two separately written unproved checkers, and compiled by slc.
  Then P compiles itself as a fixpoint check, as `bootstrap.sh` does now.
  [P] P checking its own proofs adds no independent assurance about P's
  checker. The two checkers are what is trusted. They are not fully
  independent: slc follows the reference's scheme, both are tested
  against each other, and both run `lib/ffi_core.ml`'s FFI, so a shared
  misreading of DESIGN.md or an FFI bug would affect both.
- **B2.** Prove P, then let P's proved elaborator check P's proofs. [P]
  This is circular only in the benign sense that a bug in P could accept
  a false proof of P. B1's cross-check still guards against it.
- **[P] Trusted base at the end** (R3 + O1 + F1 + N3):
  - the formal spec agreeing with DESIGN.md (human review only);
  - the checker(s) that checked P, which is `lib/` and/or slc;
  - their evaluators and FFI, because P's proofs, like slc's, use
    reflection (2.8);
  - the consistency of Sleight's proof fragment. [O]1 says no consistency
    theorem is expected. `SOUNDNESS.md` argues relative soundness of
    `Type : Type` and is itself a session's argument;
  - the 103 + 7 extern agreement axioms;
  - a world oracle for `world-do`;
  - the emitter plus about 830 lines of OCaml runtime plus the templates
    (dropped by O2 + O4);
  - OCaml 4.14 (with flambda if `-O3`) and zarith.

## 4. Decisions for the owner

1. **Which route?** Recommended: R3 (spec-first deriving functions),
   with slc kept as the fast reference for differential testing. Why
   ([P] my reasons):
   - its work parallelizes per judgment (as R2's kernel would, but R2
     leaves the front end trusted for meaning);
   - it designs the round trip in;
   - slc has no relations to retrofit against.

   Everything below depends on this choice.
2. **Does the theorem start at source text or after the reader (or after
   macro expansion)?** [O]3 suggests source text. If so, the reader and the
   macro expander must be proved. That rules out R2's "trusted front end"
   for [O]3. Recommended: text, with the reader proved early, since it is
   small (742 lines in slc).
3. **Fuel: F1 (iterative deepening; fuel in the code, not in the theorem)
   or F2 (explicit-stack compiler; no fuel anywhere)?** Recommended: F1
   first. F2 changes how every elaboration function is written, so it
   must be decided before R3 starts if it is wanted.
4. **Where does the proof stop at the output end: the IR (O1), the modelled
   OCaml subset (O2 + O4), or a new target (O3)?** Recommended: O1 now, and
   O2 + O4 later. Whatever is chosen, the IR's call and constructor
   arguments should be atoms *by type*.
5. **Is the outcome space of the theorem "same value, or one side
   crashed"?** [D] §31 and §42 seem to force it. Two sub-questions:
   - does running out of an implementation's evaluator fuel count as a
     §31 crash (MANUAL.md:157-158 says so)?
   - what is a crash during a run-position form? An error, a third
     outcome, or nothing? (See 5.2.)

   [O]3's "accepted or rejected" depends on the answer.
6. **`native-compute`: N3 (same trust as the output end)?** Recommended:
   yes.
7. **Do externs get one agreement axiom each, or does the theorem take the
   implementations as a parameter** (a semantics parameterized by an
   extern table, matching [O]1's "we parameterized the semantics")?
   Recommended: parameterize. The 103 agreements then become a separate,
   testable obligation (`--no-extern` vs FFI, as `dune test` already runs).
8. **Which checker is trusted for the proofs (B1 two checkers, or B2
   self)?** Recommended: B1. Keep `lib/` and slc both checking P, bearing
   in mind that they share the FFI and a design lineage (Q5).

## 5. Rough edges, contradictions, and gaps in DESIGN.md

1. **Evaluation order is only partly fixed.** §15 places hoisted argument
   bindings "just before the statement or final form that contains the
   call", but it does not order the hoisted bindings of *different* calls
   in one form relative to each other. [P] For a nested call it arguably
   does fix inner before outer, since the inner call's argument bindings
   go before the statement that binds the outer call's argument, and §31
   says "Evaluation is eager". §27's "the forms inside a form run before
   it does" is said of run position, not of evaluation in general. DESIGN.md does not say whether
   order is meant to be *unobservable*. [P] It may be. `World` is unique,
   so effects are data-ordered, and a crash and divergence both produce
   no value. Question for the owner: is order intended to be
   unobservable, so that any order is correct?
2. **A crash at compile time.** §31: "A real run may crash where the host
   cannot represent what is asked of it." §72 makes a crashed native run
   "an error at its argument". DESIGN.md does not say what a crash (or
   fuel exhaustion) in an *evaluator* run of a run-position form is.
   MANUAL.md:162-164 says both implementations refuse such a form, which
   describes the implementations, not the language.
3. **`def-prim` and `def-opaque` are not in §54's registry**, although
   §54 opens "Every special form, as a constructor of `Special`", the
   prelude uses them (`lib/prelude.sl:1399-1403`, for `Placed` and
   `place-at`), and slc registers them as `Special` constructors
   (`self/core.sl:337`). They are specified in INTERNALS.md §1-2, which
   calls itself "the contract between the prelude and the compilers",
   not in DESIGN.md. §66 says only "The prelude declares an opaque type".
   Question for the owner: does a formal spec of the language include
   INTERNALS.md's forms, or treat the prelude's primitives as given?
4. **"Fresh address" versus sharing.** §38 says "Nothing relies on two
   slots being distinct", and §67 lets `ENone` be answered always. §36
   says "two separately built cells with equal contents are `is`-equal
   and are two blocks", which is about cells. DESIGN.md does not say
   whether two separately built immutable values may share one word. That matters for whether `==` (2.5) refines the
   spec's `slot-eq`.
5. **§27 and §29 name "the evaluator"** as part of the semantics (§27:
   "the evaluator runs the code"; §29: "The evaluator runs that code"). [P] A formal spec needs its own run in that role, and
   DESIGN.md does not say whether that run executes the models or the
   implementations of externs. §42's "running the models instead of the
   implementations must give a program the same values" suggests the
   models are the meaning.

Not DESIGN.md, but found:
- `self/README.md:463-465` ("Not modelled: ... macros") looks stale
  against `elab-main.sl:505-586`.
- slc's `show-at` depth fuel prints a wrong value (2.3), reproduced in
  review.

## 6. Unverified claims

- The lemma-line percentages come from a crude heuristic (2.2). The
  "15–20% reusable" figure is my judgment.
- That OCaml's argument evaluation order is right-to-left in general:
  only one two-argument test on 4.14.1 (2.5). Today's emitted code does
  not depend on it.
- Whether flambda shares more constants than plain ocamlopt does: not
  tried (plain ocamlopt already shares, 2.5).
- That the `-imm` barrier bypass is GC-safe on 4.14 or OCaml 5: not
  checked on either.
- That a `many` `Bytes` is never mutated after `bytes-str` (2.5): argued
  from §13/§16, not tested adversarially.
- Tail calls with many arguments on non-amd64 targets: not tested.
- Effort figures for every route: guesses.
- Whether the reference prints the 100003-deep list correctly: it did not
  finish within 120 s under an unlimited stack, so I do not know.
- The fraction of slc's elaborator that R2's front end would remove: not
  measured.

Evidence files: `proposals/self-formal/proto/04-compiler-route/`
(`order.sl`, `ord2.sl`, `deep.sl`, `slot_eq_share.sl`, `tc3.ml`,
`tc4.ml`, `share.ml`, `argorder.ml`). Compile them with
an slc built by `self/release.sh` and with `ocamlfind ocamlopt` (4.14.1).

## Review notes

An adversarial review read the brief, CLAUDE.md, all of DESIGN.md, and
every cited file and line, re-ran the evidence with the `_build/release/slc`
built from the current sources, and corrected the text above in place.

1. `Code` has 17 constructors, not 18, at `core.sl:604-623` (624-628 is
   `CC`). Summary and 2.1 corrected.
2. The printer bug reproduces, but at about 50,000 elements, not 100000:
   `show-at`'s depth is spent twice per nested field. The output has
   49,999 `Cons _ 0`, then `Cons _ _ _)`. The §45 and §31 reasons it is a
   defect are now quoted. Summary and 2.3 corrected.
3. "17 internal: sites" became 20, by grep. 2.2 corrected.
4. "each nested call is let-bound ... in source order" was contradicted
   by the file's own `ord2.sl` result, where `Succ a` is bound before the
   earlier-written `(f a a)`. 2.5 reworded: let-bound before use, in
   §15's placement, not source order in general.
5. The `Succ` fast path is an extern template (`ffi_templates.txt:10`),
   not inlined helper code; `HArg` is at `emit.sl:105, 333`, not 79-85.
6. `slot-eq` sharing: "I did not try" replaced with a test. Plain
   ocamlopt 4.14.1 (no flambda) shares equal immutable tuple constants,
   and a two-string `slot-eq` program answers `ESome` compiled and
   `ENone` under `--interpret`. Two new evidence files were added
   (`slot_eq_share.sl`, `share.ml`).
7. `ffi_core.ml:30-31` "array and string bounds hold" was wrong: lines
   27-28 check the host's maximum lengths once; element accesses are
   unchecked `unsafe_get`/`unsafe_set`. 2.5 corrected.
8. The `-imm` safety condition is an OCaml runtime claim and was labelled
   [C]; it is now [P]. "checked on 4.14.1 only by testing" had no source
   (the code comment is about speed) and was removed.
9. The argument-order claim was tested (`argorder.ml`, right to left
   under ocamlopt and ocamlc 4.14.1); 2.5 and section 6 updated.
10. `lib/ffi.ml:40-120` became `:45-73` (types) and `:98-201`
    (functions). The 103 implementations, 7 types, 6 `extern at`
    functions, the five category counts, and 21 request kinds were
    recounted and are right.
11. The "about 900 lines" of OCaml runtime are 827. Corrected to about
    830. The "6,900 lines" of the reference holds only with `bin/*.ml`
    (lib/*.ml alone is 6,639). Wording corrected.
12. "that is why the interpreter needs fuel" (2.1) was a [P] inference
    under [C], and arguably wrong. Reworded.
13. R2 "A front-end bug can only cause a rejection" was too strong: the
    front end stays trusted for meaning. Corrected.
14. F1 "at most about 2×" does not hold for slc's fuel, which bounds
    nesting depth rather than steps. Corrected and hedged.
15. "owner's H, [O]4" overstated [O]4, which records general agreement,
    not agreement to an exact statement. "matches [O]2's driver loop"
    glossed over [O]2's fuel-free intent. Both reworded.
16. Decision 1's "the only route whose work parallelizes per judgment"
    contradicted R2's own "Inside the kernel, the same as R3". Reworded.
17. B1 and decision 8 called `lib/` and slc "independent". They share
    `lib/ffi_core.ml` and a design lineage. Qualified.
18. N3 "adds no new trust" left out process execution, temporary files,
    and reading back the answers. Corrected to "little".
19. Rough edge 1: §15 arguably does fix inner-before-outer for nested
    calls, and §27's sentence is about run position. Reworded as [P].
20. Rough edge 3: `def-prim`/`def-opaque` are specified in INTERNALS.md
    §1-2. Added, and the edge is recast as a question.
21. Rough edge 4: added §36's sentence on separately built cells.
22. Rough edge 5: "the evaluator runs the code" is §27's wording; §29
    says "The evaluator runs that code". Both are now cited.
23. Rough edge 2: added that MANUAL.md:162-164 describes the
    implementations refusing such a form.
24. The `mini/` size used for the R3 estimate counted only two files.
    The 6,849-line total was added.
25. A blanket [P] label was added to the effort, cost, and risk ratings
    in section 3.
26. Smaller citations were added: `heap-strs-fuel`'s other users, the
    elaborator's `fuel` parameter (it is the §62 expansion budget),
    `Lockstep`/`Picked` described as arity invariants, and no flambda on
    this machine.

Re-checked and found right: the line counts and the ≈6% lemma
heuristic (1,085 lines by the same awk rule), the §15, §42, §62, §67,
§72, and §29 quotations, `slot-eq` emitting `(if h == b then ...)`
(`emit.sl:969`), the `-imm` operations writing through an `int array`
cast, and a match on a type with a refuted constructor compiling to a
phantom-index GADT copy with no default arm (a three-constructor test in
review).

Uncertain points the review could not settle:

- Whether slc's *compiled* printer (`show-fuel`, `emit.sl:4`) has the
  same cutoff. The compiled `deep.sl` is a 22 MB OCaml file that ocamlopt
  had not finished compiling when the review ended.
- Whether the five-way FFI classification by name matches each
  function's real behaviour. Only the counts were checked.
- Whether `self/README.md:463-465` ("Not modelled: ... macros, which the
  reference does not implement either") is stale or means something
  narrower. `lib/elab.ml` does have expansion code, so stale is likely.
- Whether the 20-argument tail call holds on other targets or with
  flambda. Only amd64 4.14.1 without flambda was checked.
- The [P] claim that `-imm` stores are safe when both words are
  immediates (2.5) was not checked against the OCaml runtime sources.
