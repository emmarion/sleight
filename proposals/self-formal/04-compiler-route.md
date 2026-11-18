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
  `Code`, 17 constructors, `core.sl:604-622`). Later, model the small
  untyped OCaml subset that `emit.sl` actually writes, and check the printer
  per run by re-parsing.
- [C/T] Concrete risks found: the emitter relies on call and constructor
  arguments being atoms, which nothing types. A printer depth budget makes
  `slc --interpret` print a wrong value (`... Cons _ _ _)`) for a list of
  more than about 50,000 elements; the OCaml printer slc emits prints the
  same list in full. The `-imm` operations of `lib/ffi_core.ml` and their
  templates, and the stores of a cell
  invocation or `cell-write` marked `(imm o n)` in emitted code, bypass
  OCaml's write barrier (08 reads them as GC-safe on OCaml 4.14.1 when
  both words are immediates; the reference interpreter's `-imm` blits
  are not, BUGS.md 26), and the `Slots` implementation hashes raw heap
  addresses.
  `slot-eq` compiles to OCaml `==`, and ocamlopt can share two equal immutable
  constants, so a native compiled run can answer `ESome` where
  `slc --interpret` and the reference's interpreter answer `ENone` (2.5).
- [C] There are 103 FFI implementations and 7 extern types. [P] Under §42
  each one is an agreement axiom.

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
  expander (`splice-go`, `elab-main.sl:577-590`, with the 10000-expansion
  limit at `:511` and `:560`), and the elaborator proper.
- [C] Post-erasure IR: `Code ctx ms` (`core.sl:604-622`), indexed by its
  frames and by the multiplicities of its results. Its constructors are
  `CVar`, `CConst`, `CValue`, `CErased`, `CValues`, `CApp`, `CLet`,
  `CLetRec`, `CMatch`, `CCellAlloc`, `CCellWrite`, `CCellCopy`,
  `CCellRead`, `CWorldDo`, `CPrim`, `CAbsurd`, and `CError`. A run-position
  value is embedded as a `CValue` block or a `CConst` id. The emitter
  writes the compile-time heap blocks, closures included, as OCaml data
  (`self/README.md:353-362`).
- [C] Emitter: `self/emit.sl` (1516 lines) writes OCaml text as a rope.
  `lib/ffi_core.ml`, `lib/driver_core.ml`, `self/runtime.ml`, and
  `lib/ffi_templates.txt` are embedded into slc when slc is compiled, with
  `lib/specials.txt` and `lib/prelude.sl` (`bootstrap.sh:26`,
  `self/README.md:133-142`).
- [C] `slc` runs a whole compile inside **one** `Program` step: `start`
  is a single `def-unique` continuation (`self/main.sl:187-191`). So
  every compile-time evaluation sits inside one call to a total function.
  (Under `--interpret`, the interpreted program's own `Continue` steps
  then become further steps of slc's, `interp.sl:95-114`.) [P] Inside one
  step the interpreter needs fuel (or some other measure), since one total
  step cannot run an arbitrary evaluation to completion. Spreading the
  evaluation over many driver steps, each doing bounded work, is the way
  around that (F2 in Q2); slc does not do it.
- [C] `self/README.md:463-465` says macros are "Not modelled", "which the
  reference does not implement either". The macro expander at
  `elab-main.sl:509-629` contradicts the first half, and the reference
  expands macros too: slc's own sources use the `and` and `or` macros of
  `std/macro.sl` (`self/README.md:61-62`), which the reference elaborates
  in `bootstrap.sh` step 1. The README line is stale.

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
| interpreter `eval`/`apply` (`elab-main.sl:185-187, 424`) | fuel. MANUAL.md:154-163: "bounds how deeply applications nest, a tail call nesting inside the call it replaces"; slc's default 10^9 | error value "out of fuel", reported as an error. MANUAL calls it a §31 crash |
| `show-at` depth 100000 (`elab.sl:4680-4682`, used by `show-typed` at `elab.sl:4730`, which the `comptime-match` mismatch message uses at `:4784` and `entry-value` at `:4890`, and by `slc --interpret`'s final printer at `interp.sl:15`) | printer fuel | **prints `_` silently**. The budget is spent twice per nested field (`show-at` at `elab.sl:4682` and `shown-field` at `:4717`). [T] `slc --interpret deep.sl` (a 100003-element list, stack unlimited) prints 49,999 `Cons _ 0` and then `Cons _ _ _)`. [P] That is a wrong output under §45 ("Any other value prints by its type", and `_` is listed only for a union with more than one constructor, erased fields, cells, slots, functions, opaque proofs, and values with no readable `Matchable`), not a §31 crash ("A crash produces no value, never a different one"). `self/README.md:254-258` ("running out returns an error value, never a wrong answer silently") is said of "the interpreter and the generated printer", the emitted one ("a generated printer per type for a final function's result", `README:143-146`); `show-at` is what `README:369-370` calls `elab.sl`'s compile-time printer. [P] Whether that sentence covers `show-at` is unclear: its "100000" matches both `show-at`'s depth and `show-fuel`, and the emitted printers take no fuel at all, so the README is either silent on this defect or contradicted by it |
| `show-fuel` 100000 (`emit.sl:4`, `:1473`, `:1478`) | fuel for *generating* the emitted OCaml printers, one per type, memoized (`emit.sl:1379-1386`) | [C] uses `show_any`, which prints `?` (`self/runtime.ml:18`). [P] It bounds the nesting of types met while generating, not of values, so it seems hard to reach. [T] The generated printer recurses on the value with no bound: `deep.sl` compiled by slc (the 22 MB output built with `ocamlc` under an unlimited stack) and `proto/review2/04-deep-fn.sl` (the same list, built at run time) compiled by `slc --build` both print all 100003 elements, byte for byte as the reference does (`deep.sl` under the reference, unlimited stack, about 7 minutes), where `slc --interpret` cuts them as above |
| `heap-strs-fuel` 10^6 (`eval.sl:1018-1025`; also passed to `heap-pairs` and `heap-jobs`, `eval.sl:1055, 1146, 1159`) | fuel | truncates the list (returns `Nil`) |
| `str-split-fuel` (`base.sl:100-109`) | fuel equal to the string's length | unreachable but not refuted |
| sugar budget (`elab-main.sl:1871`, `README:385-394`) | budget sized by the form | "internal" error, not refuted |
| `Steps n` (`elab-main.sl:1243...`) | budget | zero case refuted by type |
| macro expansions ≤ 10000 (`elab-main.sl:560`: the run's count, `env-expansions`, is checked at `:560`. The elaborator group's first `subterm` parameter, named `fuel` (`elab-main.sl:752`), starts at the same limit for each top-level form (`:3379-3391`), loses one per expansion along a nesting path, and its zero case gives the same message at about twenty sites, among them `:766, 781, 1126, 1258, 1266, 1501, 1541` and `env-expand`'s check at `:511`; `splice-go` keeps a separate counter, started at the limit at `:593` and checked at `:586`, and `run-toplevel` another, started at the limit at `main.sl:29` and checked at `elab-main.sl:3375, 3382`) | **specified**: [D] §62 "At most 10000 expansions run in one run, every file on the command line included." | refusal ("more than 10000 macro expansions"); §62 states the limit but not what happens past it |

- [P] So the fuel a correctness theorem must face is the interpreter's;
  `show-at`'s and `heap-strs-fuel`'s, whose zero cases give a wrong answer
  silently (a `_`, or a request's string list cut short past 10^6
  elements), look like plain bugs that recursion on the value's structure
  could fix; and the zero cases of `str-split-fuel` and the sugar budget,
  which are believed unreachable and would become proof obligations. The
  expansion limit is part of the language.

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
  (`emit.sl:823`), except a store marked `(imm o n)` (§37), which is
  emitted as `Array.unsafe_set (of_any cell : int array) k (of_any n : int)`
  on the constructor's block (`imm-stores`, `emit.sl:863-868`, used at
  `:876`). [T] Compiling `std/immediate.sl tests/cell_imm.sl` with slc
  emits five such stores. So slc mutates only blocks that OCaml declares
  mutable, but not always through the field syntax. I found no
  `Obj.set_field`.
- [C] A call is written `(name a1 ... an)` and a constructor is written
  `K { f0 = a0; ... }`, with the argument texts inlined
  (`emit.sl:909-919`, `build-rope` at `:452-459`). `CApp`'s arguments have
  type `List (Code ctx many-one)` (`core.sl:611`), so nothing in the types
  says that they are atoms.
- [T] In `proto/04-compiler-route/order.sl` and `ord2.sl`, each call or
  constructor argument that is neither a variable nor a literal is
  let-bound before the call that uses it, as §15 describes (a literal,
  such as the `1` of `ord2.sl`'s `(f a 1)`, is passed as a named
  top-level constant); two tests do not show that this always holds. The bindings are in source
  order in `order.sl`, but not in `ord2.sl` (next item), so the emitted
  order is §15's placement, not source order in general. A multi-value result is sequenced by
  `let tupN_a0 = ... in let tupN_a1 = ... in`, `N` a depth
  (`emit.sl:365-369`); the
  comment at `emit.sl:362-364` gives the reason as a workaround for an
  ocamlopt failure (`Selection.size_expr`), not evaluation order. [P] So
  OCaml's unspecified (in practice right-to-left) argument order does not
  matter *today*, but only because of an untyped invariant of the
  elaborator. [T] A two-argument test (`proto/04-compiler-route/argorder.ml`)
  evaluated right to left under both ocamlopt and ocamlc 4.14.1. Extern
  templates use an argument several times, as the `Succ` fast path
  `if Obj.is_int {a0} && ... {a0} ...` does (`lib/ffi_templates.txt:10`;
  holes `HArg i`, `emit.sl:105, 333`). An argument that is not an atom
  would be evaluated more than once. The templates' header states the
  assumption: "Every hole but a body is filled with a variable name"
  (`lib/ffi_templates.txt:4`).
- [D] §15: "Every argument to a constructor, a function or a cell behaves
  as if it were first bound to an anonymous variable. ... That binding is
  a statement (§27) placed just before the statement or final form that
  contains the call". [T] In `ord2.sl`, `(values (f a a) (f (Succ a) a))`
  binds `Succ a` *before* `(f a a)`, consistent with that sentence.
- [T] **In the tests run, a head that is a form runs before the
  arguments.** In `proto/review5/04_head_arg_compiled.sl`, `((pickbig h) (bigbytes k))`
  has a head whose run crashes in `Array.make` and an argument whose run
  crashes in `Bytes.create`. slc emits, with its generated names shortened here,
  `let v1 = (pickbig h) in let v2 = (bigbytes k) in ((of_any v1 : ...) v2)`,
  and the program built by `slc --build` (ocamlopt) and by
  `slc --build --byte` dies with `Invalid_argument("Array.make")`, as the
  reference interpreter does; with a small `h` it dies in
  `Bytes.create`, so the argument's crash is reachable. 02 §2.2's two
  world-write tests (`proto/dyn/head_crash_arg_write.sl`,
  `head_write_arg_crash.sl`) show the same order under the reference,
  `slc --interpret`, and slc's native and `--byte` builds. The three
  tests are all inside a function body, one call shape each. [P] A
  reading of §15 by timing alone, the argument's binding placed before
  the statement or final form and the head run inside it, would give
  the other order. In run
  position §6 elaborates the head first ("The head is elaborated
  first") and a head that is a form "runs as soon as it is elaborated";
  inside a body I found no sentence that places a head that is a form
  relative to the arguments (rough edge 1). §29 lists "the elaborator's
  own binders for its head, arguments and scrutinee (§15)", which reads
  as if the head were bound as §15 binds an argument, but neither
  section orders those binders among themselves.
- [C] **Refutation is trusted at output.** A match with no default arm, or
  a phantom-index GADT copy that omits refuted constructors, is matched
  after an `of_any` cast. `README:242-244`: "A wrong refutation would
  misdispatch silently here". [P] So the OCaml program's memory safety
  rests on the elaborator's correctness, which is exactly what a proof
  would supply.
- [C] `slot-eq` compiles to `(if h == b then some else none)`
  (`emit.sl:964-969`). [P] [D] §67 allows `ENone` always, but `ESome`
  "proves that `a` and `b` hold one word". If OCaml or flambda shares two
  structurally equal *immutable* constants (slices, tuples), `==` says
  `ESome` for two values the program built separately. [T] This
  happens without flambda: `proto/04-compiler-route/share.ml` finds two
  equal `("ab", 0, 2)` tuple constants `==` under ocamlopt 4.14.1 (not
  under ocamlc), and `slot_eq_share.sl`, two run-position
  `(str-append "a" "b")`, prints `(BTrue)` compiled by `slc --build`
  (ocamlopt) and `(BFalse)` under `slc --build --byte`, under
  `slc --interpret`, and under the reference's interpreter; the
  reference's own native build prints `(BTrue)` too. `bootstrap.sh` builds the
  tests it compares with `--byte` (`self/README.md:191`), so those runs
  would not show this; its `native-compute` runs are built with ocamlopt
  (`elab-main.sl:38`) and compared with `--no-native`, so a test that
  returned a `slot-eq` answer through `native-compute` could, though I
  did not look for one. [P] §67 allows both answers ("which
  one a call answers may differ between runs"), and in the compiled run
  the two do hold one word. It is a refinement mismatch only if the spec
  says that every allocation takes a never-used address (the earlier
  session's proposal B).
- [C] The `-imm` operations write through `(cast a : int array)` with
  `Array.unsafe_set` and `caml_blit_bytes` (`lib/ffi_core.ml:235-241,
  315-320`), and so do their templates (`lib/ffi_templates.txt:51-52`)
  and the emitted `imm` cell stores above. [T] ocamlopt 4.14.1 compiles
  an `Array.unsafe_set` on an `int array` to a store with no call to
  `caml_modify`, and the same store on an `Obj.t array` to one with the
  call (`proto/review5/04_barrier.ml`, read from its assembly); the
  comment at `ffi_core.ml:315-317` calls `caml_blit_bytes` "a plain
  memmove". [P] Skipping `caml_modify` is, I believe, safe
  when both the old and the new words are immediates, as `(imm o n)` and
  `Imm` require ([D] §37, §44). That is a sufficient condition, not a
  necessary one: the 4.14.1 runtime's own comment asks for the barrier
  unless "the value being overwritten is not a shared block and the
  value being written is not a young block" (08 §3). This is a dependency on OCaml runtime
  internals (GC barriers). The code comment at `ffi_core.ml:315-317`
  concerns speed, not safety. 08 gives the safety argument: from the
  4.14.1 runtime sources and stress tests, it reads both kinds of store
  as GC-safe on OCaml 4.14.1, amd64, without flambda, when both words
  are immediates (for a blit, every word of both ranges), every read of
  such a field is a mutable load, and the target is not a flat float
  array. It reads OCaml 5 the same way for one domain, without running
  anything there; OCaml 5, flambda, arm64, and systhreads are untested
  (08 §7, §8). The reference interpreter's `-imm` blits fail the
  immediacy conditions, since its array elements are boxed `VWord`s,
  and corrupt its heap (08 §1, §7; BUGS.md 26).
- [C] `Bytes.unsafe_to_string` without a copy (`lib/ffi_core.ml:148, 173,
  260`). At 148 and 173 the buffer is a fresh local one. At 260
  (`bytes_str`), and in the template that emitted programs use in its
  place (`lib/ffi_templates.txt:80`), it is the argument: `bytes-str`
  takes its `Bytes` at `many` (`lib/prelude.sl:1738`).
  [P] This is safe only if a `many` `Bytes` is never mutated afterwards.
  That follows from §13/§16 (only `unique` is mutated; `share` ends unique
  uses) if uniqueness checking is sound. I found no counterexample, and I
  did not search hard.
- [C] The `Slots` implementation (`lib/ffi_core.ml:323-398`) does not
  search with `slot-eq` as the models do (§69). It hashes raw block
  addresses (`address`, `Obj.magic` at `:336`), and detects that the GC
  has moved blocks by a sentinel block allocated young and by the
  compaction count (`:345-360`). The comment at `:337-344` records an
  earlier version that missed lookups after a compaction on 4.14.1.
  [P] This is another dependency on OCaml runtime internals; §69's
  "How an implementation finds a slot is left to it" allows it, but
  nothing checks it except tests such as `tests/slots_compact.sl`.
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
  a known function is also a `jmp` (no flambda;
  `proto/review2/04-tc-direct.ml`, 10^7 iterations under a 1 MB stack).
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
  | arrays (mutation at unique; `-imm` barrier-free in `ffi_core.ml`, though the table maps `array-swap-imm` and `array-place-imm` to the barriered `swap` and `place`, `ffi.ml:102, 107`) | 22 | array-swap, array-pluck, array-blit-imm |
  | `Slots` (models search with `slot-eq`; the implementation hashes addresses, 2.5) | 4 | slots-find, slots-intern |

- [C] These are *not* in the FFI table but are implemented by the
  driver, the elaborator, or the runtime:
  - `world-do`, with 21 request kinds (`Driver_core.request` in emitted
    code, `K3_0`..`K3_20`);
  - `slot-eq`, `cell-same`, and `fn-same`;
  - the handle and macro-world primitives of §64-65;
  - `native-compute`.

  [P] These are specified by DESIGN.md directly, not by models (for
  `world-do`'s requests through `lib/prelude.sl`, which §42 makes "the
  reference for the requests and their answers"). So they
  are part of the spec semantics, not agreement axioms. Three of them make
  the semantics depend on more than the program: `world-do` and §65's
  `read-file`, whose answers come from the host and would have to be a
  parameter of the semantics (an oracle), and `slot-eq`, of which §67
  says "which one a call answers may differ between runs".
- [D] §42: "An `extern` implementation must agree with its model: except
  through `slot-eq` (§67), running the models instead of the
  implementations must give a program the same values, though not the
  same cost, and either may crash where the other does not (§31)." [P] So
  each of the 103 implementations, and each extern type's view and wrap
  pair, is one axiom of the form "agrees with the model up to crash and
  up to what `slot-eq` answers"; §69 applies the `slot-eq` exception to
  the `Slots` functions ("The models search with `slot-eq`, so §42's
  exception for `slot-eq` covers what the implementations answer"). The
  correctness theorem can then be at most "the compiled run's values are
  values some spec run gives, for the same `slot-eq` and world answers,
  up to crash", not "the same values" (2.5's `slot_eq_share.sl` gives
  different values compiled and interpreted, which §67 allows).
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
- *Proved:* everything slc does down to its IR, if finished; the emitter
  too only with a model of OCaml (Q3, O2).
- *Trusted:* the spec, the checker, OCaml, the FFI, and the output end
  unless it is modelled (Q3).
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
  - The 20 `"internal:` sites (2.2) become proof obligations.
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
- *Round trip:* [D] §6 dispatch, §28 `comptime-match`, §45
  `prove-literal-lt`, and §49 `unary` depend on stored values or on the
  evaluator (§45: "like a `comptime-match`, it relies on the evaluator"). The kernel cannot trust the front end's values,
  so it must **re-run every run-position form** with its own evaluator, or
  check an evaluation trace. Traces are as long as the run.
  - Macro expansion need not be re-run. [D] §62: "The forms are elaborated
    and checked as if they had been written there". [P] But then the
    theorem speaks of the *expanded* program. The source-to-expanded step
    is trusted, which sits uneasily with a correctness theorem about
    source text; [O]3 speaks of source text.
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
  language without multiplicities, `Matchable`, slots, macros, run
  position, literals, externs, or the `_` sugar (MINIMAL.md's
  "What is removed" and "What remains"). Scaling that by DESIGN.md's size is
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
  with fuel that counts steps and doubles, the failed attempts together
  cost less than twice what the last one does; with slc's fuel, which bounds
  nesting depth (MANUAL.md:154-157), a failed attempt can do nearly all
  of the successful run's work, so the overhead can grow with the number
  of doublings.
  Compile-time effects repeat (`native-compute`'s temporary files and
  processes; `read-file` gives the same answer only if the file has not
  changed between attempts). The step function still contains
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
- `Array.make`, and `Array.unsafe_set` through `int array` casts (the
  `imm` cell stores, 2.5) and `Ffi_core.word array` casts (`emit.sl:1252`);
- tuples;
- the `%identity` casts, `Obj.is_int`, `==`, `failwith`, `absurd ()`,
  and `exit`;
- calls into `Ffi_core` and `Driver_core`;
- from the templates (`lib/ffi_templates.txt`): `if`, machine-integer
  arithmetic and comparison, and direct Zarith and Stdlib calls such as
  `Z.succ`, `String.make`, and `Char.code`.

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
  - [D] DESIGN.md's opening paragraphs, before §1, call fast code "an
    aim for the language, not for the implementations". [P] So nothing
    in DESIGN.md seems to rule O3 out.
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
  - a world oracle for `world-do` and `read-file`, and the answers of
    `slot-eq`, which §67 leaves free;
  - the OCaml runtime internals the FFI and the emitted code rely on: the
    barrier bypass of the `-imm` operations and the `imm` cell stores,
    and the `Slots` address hashing (2.5);
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
   macro expansion)?** [O]3 suggests source text. [P] [O]3's wording by
   itself asks only that every source text gets one of the two verdicts,
   which a total but unproved front end could give. If the theorem is
   also to say that the verdict is the spec's verdict on the text, the
   reader and the macro expander must be proved, which R2's trusted front
   end does not do. Recommended: text, with the reader proved early,
   since it is small (742 lines in slc).
3. **Fuel: F1 (iterative deepening; fuel in the code, not in the theorem)
   or F2 (explicit-stack compiler; no fuel anywhere)?** Recommended: F1
   first. F2 changes how every elaboration function is written, so it
   must be decided before R3 starts if it is wanted.
4. **Where does the proof stop at the output end: the IR (O1), the modelled
   OCaml subset (O2 + O4), or a new target (O3)?** Recommended: O1 now, and
   O2 + O4 later. Whatever is chosen, the IR's call and constructor
   arguments should be atoms *by type*.
5. **Is the outcome space of the theorem "a value some spec run gives,
   or a crash"?** [D] §31 and §42 seem to force "up to crash", and §67
   (`slot-eq` "may differ between runs") with §42's `slot-eq` exception
   makes the spec run nondeterministic, so "the same value" is too strong
   (2.6). Two sub-questions:
   - does running out of an implementation's evaluator fuel count as a
     §31 crash (MANUAL.md:158-159 says so)?
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
   it does" is said of run position, not of evaluation in general. §61
   reads as if a body's statements run in written order, though it shows
   only one statement before one call: "The write
   stores `h` before the call: left to the invocation, that store would
   follow the call". DESIGN.md does not say whether
   order is meant to be *unobservable*. [P] A real run can observe it
   without any divergence, through a crash §31 permits; the spec's own
   run, with "unlimited stack and heap" (§31), would not crash in the
   example below, so both orders would give it the same output. `World` is unique, so world effects are ordered among
   themselves, but not against a crash in pure code: in
   `proto/review5/04_effect_vs_crash.sl`, `(both (say w) (big n))` has
   one argument that writes to standard output and one that crashes, and
   §15 orders the two bindings neither way. [T] slc's native build and
   the reference interpreter both print `effect ran` and then crash; the
   other order would crash with no output, and §42 has the driver flush
   "after every write". A crash and a divergence in two arguments are a
   second such case, if §17's levels ("Termination rests on levels")
   leave any divergence, which is not settled here. Head-versus-argument
   order is in 2.5 and 02 §2.2. Question for the owner: is order meant
   to be fixed, and if not, is every order a correct run, so that the
   output above may differ between implementations?
2. **A crash at compile time.** §31: "A real run may crash where the host
   cannot represent what is asked of it." §72 makes a crashed native run
   "an error at its argument". DESIGN.md does not say what a crash (or
   fuel exhaustion) in an *evaluator* run of a run-position form is.
   MANUAL.md:162-164 says both implementations refuse such a form, which
   describes the implementations, not the language. On a host stack
   overflow in run position, both instead die with "Stack overflow" and
   no message naming the file or the form
   (`proto/review7/02_deep_runpos.sl`).
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
   and are two blocks", which is about cells, and §37 calls the result of
   a `many` `cell-write` "a fresh block" and that of a `many` invocation
   with a store "a fresh copy". §33 fixes the word of a value with no
   non-erased field, "however the value was built", when its type is
   tagged or is untagged and not marked `extern` ("an unspecified word
   otherwise"), so separately built values of that kind do share one
   word. For any other value with a non-erased field, and for a value of
   an extern type such as the `String`s of `slot_eq_share.sl`, I found
   no sentence saying whether two separately built ones may share one
   word. That matters for
   whether `==` (2.5) refines the spec's `slot-eq`.
5. **§27 and §29 name "the evaluator"** as part of the semantics (§27:
   "the evaluator runs the code"; §29: "The evaluator runs that code"). [P] A formal spec needs its own run in that role. DESIGN.md
   describes runs of both kinds: by §42 the prototype runs the
   implementations unless `--no-extern` "runs the models instead", and
   §29 makes an extern type's `Matchable` "the FFI's wrapper" (§24:
   "Its value holds the construction and matching of an `extern`
   type"). It requires the two to agree except through `slot-eq`, and
   does not say which of them the meaning is. [P] §42's "running the
   models instead of the implementations must give a program the same
   values" reads as if the models were the meaning; decision 7's
   parameterization would leave the choice open.

Not DESIGN.md, but found:
- `self/README.md:463-465` ("Not modelled: ... macros") is stale
  against `elab-main.sl:509-629` and the reference (2.1).
- slc's `show-at` depth fuel prints a wrong value (2.3), reproduced in every
  review that re-ran it. `self/README.md` either does not mention it or
  contradicts it: its "never a wrong answer silently" (`:254-258`) is
  said of "the interpreter and the generated printer", and whether that
  printer is `show-at` is unclear (2.3). The emitted OCaml printer does
  not have the defect.
  That README sentence also says running out "returns an error value";
  the emitted printers' generation fuel (`show-fuel`, 2.3) instead
  emits `show_any`, which prints `?` (`self/runtime.ml:18`), and its
  "1000000" matches no interpreter or printer fuel in `self/` (the
  interpreter's default is 10^9, `core.sl:3614`; the only 1000000 is
  `heap-strs-fuel`, `eval.sl:1018`).
- `self/README.md:385-386` puts the sugar budget "as its first `subterm`
  parameter". In `elab-expr-demand` (`elab-main.sl:752`) it is `sugar`,
  the fourth, after `fuel` (the expansion bound of 2.3), `callbacks`,
  and a `hop-` index.

## 6. Unverified claims

- The lemma-line percentages come from a crude heuristic (2.2). The
  "15–20% reusable" figure is my judgment.
- That OCaml's argument evaluation order is right-to-left in general:
  only one two-argument test on 4.14.1 (2.5). That today's emitted code
  does not depend on it: shown for two tests only, and resting on the
  untyped atom invariant.
- That slc's compiled code runs a head that is a form before the
  arguments in general: three tests in a function body, one call shape
  each (2.5).
- Whether flambda shares more constants than plain ocamlopt does: not
  tried (plain ocamlopt already shares, 2.5).
- That the `-imm` and `imm`-store barrier bypass is GC-safe beyond
  OCaml 4.14.1 on amd64 without flambda, where 08 reads it as safe when
  both words are immediates: OCaml 5, flambda, arm64, and systhreads are
  not checked (08 §7, §8).
- That a `many` `Bytes` is never mutated after `bytes-str` (2.5): argued
  from §13/§16, not tested adversarially.
- Tail calls with many arguments on non-amd64 targets: not tested.
- Effort figures for every route: guesses.
- The fraction of slc's elaborator that R2's front end would remove: not
  measured.

Evidence files: `proposals/self-formal/proto/04-compiler-route/`
(`order.sl`, `ord2.sl`, `deep.sl`, `slot_eq_share.sl`, `tc3.ml`,
`tc4.ml`, `share.ml`, `argorder.ml`), `proto/review2/04-deep-fn.sl`
and `proto/review2/04-tc-direct.ml` from the second review, and
`proto/review5/04_head_arg_compiled.sl`, `04_effect_vs_crash.sl`, and
`04_barrier.ml` from the fifth, and, from 02, `proto/dyn/head_crash_arg_write.sl`,
`head_write_arg_crash.sl`, and `proto/review7/02_deep_runpos.sl`. Compile them with
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
27. Q1 R1 still said "The 17 'internal' sites" after item 3 corrected
    2.2 to 20. A later recount (`grep -rn '"internal:' self/`) again
    gives 20: 12 in `elab.sl`, 6 in `elab-main.sl`, and 1 each in
    `eval.sl` and `emit.sl`. R1 now says 20 and points to 2.2.

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

## Second review notes

A second adversarial review read the brief, CLAUDE.md, and all of
DESIGN.md, opened the cited lines, and re-ran every evidence file with
`_build/release/slc`, the reference, and OCaml 4.14.1 (no flambda).

1. `Code` is at `core.sl:604-622`, not `604-623`; `CC` starts at 623
   (the first review's note 1 says 624-628). Summary and 2.1 corrected.
2. The first review's open question on the compiled printer is settled.
   `show-fuel` bounds the *generation* of the emitted printers, one per
   type, and its zero case emits `show_any`, which prints `?`
   (`emit.sl:1379-1380`, `self/runtime.ml:18`). The emitted printer
   recurses on the value with no bound: `deep.sl` compiled by slc (built
   with `ocamlc` under an unlimited stack; `ocamlc` overflows its own
   stack otherwise) and the new `proto/review2/04-deep-fn.sl` print all
   100003 elements. The 2.3 table, 2.3's [P], and the summary are
   updated.
3. The reference also prints the full list, byte for byte as compiled
   slc does (about 7 minutes). The section 6 item saying this was unknown
   is removed.
4. The `show-at` defect contradicts `self/README.md:254-258` ("never a
   wrong answer silently"), and `show-typed` also feeds the
   `comptime-match` mismatch message (`elab.sl:4784`). Added.
5. The `Slots` implementation was missing from the OCaml-internals risks:
   it hashes raw addresses (`Obj.magic`, `ffi_core.ml:336`) and tracks
   GC moves by a sentinel and the compaction count (`:345-360`). The 2.6
   table said `Slots` "searches with `slot-eq`", which is what the models
   do (§69), not the implementation. Added to 2.5, 2.6, and the trusted
   base.
6. 2.6's "The correctness theorem can only be 'same values, up to
   crash'" ignored §42's own `slot-eq` exception, §67 ("which one a call
   answers may differ between runs"), and §69's extension of the
   exception to `Slots`. The spec run is nondeterministic there, and
   `slot_eq_share.sl` shows two different values. 2.6, decision 5, and
   the trusted base corrected; `slot-eq` joins `world-do` as an oracle.
7. `slot_eq_share.sl`: `(BTrue)` holds for a native build only;
   `slc --build --byte`, `slc --interpret`, and the reference all print
   `(BFalse)`. `bootstrap.sh` compares tests built with `--byte`, so it
   would not see such a difference. Added.
8. 2.5 cited `emit.sl:966-968` for `slot-eq`, while the first review's
   notes said 969; the code is at 964-969. Corrected.
9. "In practice the elaborator hoists every non-variable argument" was a
   generalization from two tests. Reworded to what the tests show.
10. The `let tup_ai` sequencing exists, by its comment, to avoid an
    ocamlopt failure (`emit.sl:362-364`), not for evaluation order.
    Added.
11. The templates state the atom assumption themselves ("Every hole but
    a body is filled with a variable name", `ffi_templates.txt:4`).
    Added.
12. Of the three `Bytes.unsafe_to_string` sites, 148 and 173 convert a
    fresh local buffer; only 260 and the `bytes-str` template
    (`ffi_templates.txt:80`, what emitted programs use) convert the
    argument. Clarified.
13. The `-imm` lines are `ffi_core.ml:235-241`, not 234-241.
14. O2's list of "what is actually emitted" left out what the templates
    emit (`if`, machine-integer arithmetic, Zarith and Stdlib calls) and
    `absurd ()`. Added.
15. O3 attributed the fast-code aim to §1; it is in DESIGN.md's opening
    paragraphs, before §1. "so O3 is allowed" was an inference labelled
    [D]; now [P].
16. R1 claimed everything proved and trusted only "the spec, the
    checker, OCaml, and the FFI", while R3 lists the output end as
    trusted; the emitter cannot be proved without an OCaml model.
    R1 aligned with Q3.
17. R2 said "§45 literals depend on stored values". What depends on the
    evaluator is §45's `prove-literal-lt` (quoted) and §49's `unary`.
    Corrected.
18. F1 called `read-file` idempotent; it repeats its answer only if the
    file is unchanged. Hedged.
19. Decision 2 said source text "rules out R2's trusted front end for
    [O]3". [O]3's wording asks for totality (every source accepted or
    rejected), which a total unproved front end can give; proving the
    reader and expander is needed for a correctness claim about text.
    Decision 2 and R2's round-trip item reworded.
20. Rough edge 1's [P] that order may be unobservable left out that order
    decides between a crash and divergence when one argument does each.
    Added.
21. `self/README.md:463-465` is stale, not "looks stale": the reference
    elaborates the `and`/`or` macros of `std/macro.sl` that slc's sources
    use (`self/README.md:61-62`). 2.1 and section 5 updated.
22. The direct 20-argument tail call the first review describes is now
    an evidence file (`proto/review2/04-tc-direct.ml`).

Re-checked and found right: the file and line counts, 20 `"internal:`
sites, 103 FFI functions and their five class counts, 7 extern types, 6
`extern at` functions, 21 request kinds, `main.sl:187-191`, the
expansion-limit sites, `MANUAL.md:154-164`, the `mini/` citations and
sizes, `base.sl:157-161, 181-182`, `release.sh:17`, every [T] result in
2.5 (order, ord2, argorder, share, tc3, tc4), and the `show-at` cutoff
(49,999 `Cons _ 0`, then `Cons _ _ _)`).

Points I am unsure of:

- The 2.6 class names describe the classes loosely: "bytes (mutation at
  unique)" includes pure reads such as `bytes-get` and `bytes-cmp`.
- The [P] that `-imm` stores are GC-safe when both words are immediates
  is still unchecked against the OCaml runtime sources.
- Whether the theorem shape proposed in item 6 ("values some spec run
  gives, for the same `slot-eq` and world answers") is the right one is
  itself a proposal, not a finding.

## Third review notes

A third adversarial review read the brief, CLAUDE.md, and all of
DESIGN.md, opened the cited lines, and re-ran `deep.sl` under
`slc --interpret`, `04-deep-fn.sl` built by slc, `slot_eq_share.sl` in
all four modes, `order.sl`, `ord2.sl`, `share.ml`, `argorder.ml`,
`tc3.ml`, `tc4.ml`, and `04-tc-direct.ml`. All [T] results held.

1. 2.5 said a cell write is emitted as `r.fi <- arg`, so slc mutates
   only through the field syntax. A store marked `(imm o n)` (§37) is
   emitted as `Array.unsafe_set (of_any cell : int array) k ...` on the
   constructor's block (`emit.sl:863-868`, `:876`); slc compiling
   `std/immediate.sl tests/cell_imm.sl` emits five. So the barrier
   bypass is in emitted code too, not only in the FFI and its templates
   (`ffi_templates.txt:51-52`). Summary, 2.5, O2's list, the trusted
   base, and section 6 updated.
2. 2.3 and section 5 said the `show-at` defect contradicts
   `self/README.md:254-258`. That sentence is about "the interpreter and
   the generated printer", the emitted one (`README:363-367`);
   `README:369-370` names `elab.sl`'s compile-time printer separately.
   Reworded: the README is silent on the defect.
3. 2.1's [P] said the interpreter "would need fuel even with more steps",
   which contradicts F2 (no fuel, the work spread over bounded steps).
   Reworded to "inside one step". Also added that `--interpret` turns the
   interpreted program's `Continue` steps into slc's (`interp.sl:95-114`).
4. 2.3's [P] said the only fuel a theorem must face is the interpreter's
   and `show-at`'s. It left out `heap-strs-fuel`, whose zero case cuts a
   request's string list short silently (`eval.sl:1020`), and the
   unrefuted zero cases of `str-split-fuel` and the sugar budget, which
   would be proof obligations. Reworded.
5. 2.6 said two built-ins make the semantics nondeterministic. §65's
   `read-file` also answers from the host, like `world-do`. Added there
   and to the trusted base's oracle.
6. Decision 5 cited `MANUAL.md:157-158` for the §31 crash; the sentence
   is at 158-159.
7. Rough edge 1 did not cite §61, which takes a body's statements to run
   in written order ("The write stores `h` before the call: left to the
   invocation, that store would follow the call"). Added. Its [P] about a
   diverging argument now notes that §17 means levels to rule divergence
   out ("Termination rests on levels"), unsettled here.
8. 2.5 named the tuple bindings `tup_a0`; the emitted names are
   `tupN_a0`, `N` a depth. The paragraph also said "two tests" twice.
9. 2.1 and section 5 cited `elab-main.sl:505-586` for the macro
   expander; 505 is inside an earlier function, and the expander runs
   from `env-expand` at 509 to `splice-call` at 629.
10. 2.1's list of files embedded into slc left out `lib/specials.txt`
    and `lib/prelude.sl` (`bootstrap.sh:26`).
11. The summary labelled "Under §42 each one is an agreement axiom" [C];
    it is a reading, now [P].
12. `show-typed` also feeds `entry-value` (`elab.sl:4890`). Added.
13. Section 6's "Today's emitted code does not depend on it" was stated
    flatly in a list of unverified claims; now hedged to the two tests
    and the atom invariant.

Re-checked and found right: the file sizes and the 12 files, `Code`'s 17
constructors at `core.sl:604-622`, the 20 `"internal:` sites, the 103
FFI functions, 7 extern types, and 21 request kinds, `show-at`'s cutoff
(49,999 `Cons _ 0`, then `Cons _ _ _)`), the emitted printer printing all
100003 elements (also under an 8 MB stack), `(BTrue)` native and
`(BFalse)` under `--byte`, `--interpret`, and the reference, the
`mini/` citations and sizes, the §15, §29, §42, §45, §62, §67, §69,
and §72 quotations, and the lib and template line numbers.

Points I am unsure of:

- Whether `README:254-258`'s "1000000 or 100000" and the interpreter's
  10^9 default (`MANUAL.md:162`, `core.sl:3614`) disagree; I did not
  settle which fuel the README's 1000000 names.
- Whether `Array.unsafe_set` through an `int array` cast on a variant
  block is as GC-safe as on an array when both words are immediates; it
  is the same [P] as for the `-imm` operations, unchecked against the
  runtime sources.

## Fourth review notes

A fourth adversarial review read the brief, CLAUDE.md, and all of
DESIGN.md, opened the cited lines, and re-ran `order.sl`, `ord2.sl`,
`slot_eq_share.sl` in all four modes, `share.ml`, `argorder.ml`,
`tc3.ml`, `tc4.ml`, `04-tc-direct.ml`, `deep.sl` under
`slc --interpret`, `04-deep-fn.sl` built by slc, and the `imm` stores
of `std/immediate.sl tests/cell_imm.sl`. All [T] results held.
`proto/review4/04_deep_interp_tail.txt` keeps the end of the
`--interpret` output.

1. The 2.3 row on macro expansions said the elaborator group's first
   `subterm` parameter "is this budget". It is a separate bound: it
   starts at the same limit for each top-level form
   (`elab-main.sl:3379-3391`) and loses one per expansion along a
   nesting path, while §62's per-run count is `env-expansions`, checked
   at `:560`. Of the cited checks, `:586` is `splice-go`'s own counter
   (started at `:593`), and `764`/`779` are the `let-match` lines whose
   zero cases are at `:766`/`:781`; the list also left out five sites.
   Rewritten; 2.1's `splice-go` range is `577-590`, not `577-586`.
2. F1 said failed attempts under doubling step fuel cost "at most about
   as much as the last one". With the last attempt using `W > 2^(k-1)`
   steps, the failed ones use at most `2^k - 1 < 2W`. Corrected to "less
   than twice".
3. Rough edge 4 said DESIGN.md does not say whether two separately
   built immutable values may share one word. §33 fixes the word of a
   value with no non-erased field "however the value was built", so
   those do. The gap is narrowed to values with a non-erased field and
   extern values (the `String`s of `slot_eq_share.sl`).
4. Rough edge 5 said DESIGN.md does not say whether the evaluator runs
   the models or the implementations. §42 describes the prototype
   running the implementations unless `--no-extern` "runs the models
   instead", and §24/§29 make an extern type's `Matchable` the FFI's
   wrapper. What DESIGN.md leaves open is which of the two is the
   meaning. Reworded.
5. 2.3 cited `README:363-367` for "the generated printer" being the
   emitted one; `README:143-146` says so directly ("a generated printer
   per type for a final function's result"). Added. The third review's
   open point is settled: `README:254-258`'s "1000000" matches no
   interpreter or printer fuel in `self/` (the interpreter's default is
   10^9, `core.sl:3614`; the only 1000000 is `heap-strs-fuel`), and the
   same sentence's "returns an error value" does not hold for
   `show-fuel`'s zero case, which emits `show_any` (`?`). Both added to
   section 5's README list.
6. `self/README.md:385-386` places the sugar budget as the group's
   "first `subterm` parameter"; in `elab-expr-demand`
   (`elab-main.sl:752`) the first is `fuel` and `sugar` is the fourth.
   Added to section 5's README list.
7. R3 listed `mini/`'s language as lacking "multiplicities, slots,
   macros, or run position". MINIMAL.md also removes `Matchable`,
   literals, `extern`, and the `_` sugar, which bears on how far `mini/`
   is from the full language. Added.
8. The summary said ocamlopt "shares equal immutable constants"; one
   tuple test shows that it can. Hedged to "can share".
9. Section 5's README bullet said the `show-at` defect was reproduced in
   "all three reviews"; it is four now.

Re-checked and found right: the 12 files and their line counts, the
lemma-line heuristic (1,084), `Code`'s 17 constructors at
`core.sl:604-622`, the 20 `"internal:` sites, `show-at`'s cutoff (49,999
`Cons _ 0`, then `Cons _ _ _)`) and the slc-built `04-deep-fn.sl`
printing all 100003 elements under an 8 MB stack, byte for byte as the
reference prints `04-deep-fn.sl` (re-run here, under 15 minutes), `(BTrue)` native and
`(BFalse)` under `--byte`, `--interpret`, and the reference, the five
`int array` stores, the `caml_apply20` `jmp` in `tc3.ml` and the direct
`jmp` in `04-tc-direct.ml`, `tc4.ml` overflowing a 1 MB stack, the
quotations from §15, §17, §19, §27, §29, §31, §36, §38, §42, §45, §54,
§61, §62, §66, §67, §69, and §72, the `mini/` citations, and the
`lib/ffi_core.ml`, `lib/ffi_templates.txt`, and `lib/prelude.sl` lines.

Points I am unsure of:

- Whether ocamlopt shares constants beyond tuples of immutable data,
  for example the mutable inline records emitted for ADT blocks; I did
  not test it, and I expect not, since OCaml does not share mutable
  blocks.
- The [P] that the `imm` and `-imm` stores are GC-safe when both words
  are immediates is still unchecked against the runtime sources (none
  are installed here).

## Fifth review notes

A fifth adversarial review read the brief, CLAUDE.md, and all of
DESIGN.md, opened the cited lines in `self/`, `lib/`, `mini/`,
`MANUAL.md`, `MINIMAL.md`, and `INTERNALS.md`, and re-ran `order.sl`,
`ord2.sl`, `slot_eq_share.sl` (native, `--byte`, `--interpret`, and the
reference), `share.ml`, `argorder.ml`, `tc3.ml`, `tc4.ml`,
`04-tc-direct.ml`, and the five `imm` stores of `tests/cell_imm.sl`. All
those [T] results held. `deep.sl` under `--interpret` was not re-run.

1. 2.5 said every call or constructor argument that is not a variable
   is let-bound. A literal is not: `ord2.sl`'s `(f a 1)` passes the
   top-level constant `a1560`. Reworded to "neither a variable nor a
   literal".
2. The open point on head-versus-argument order in slc's compiled code
   is settled for one test. `proto/review5/04_head_arg_compiled.sl`
   gives a head and an argument that crash differently; slc let-binds
   the head first, and both the native and the `--byte` build die in
   the head's `Array.make`, as the reference interpreter does; with the
   head made harmless they die in the argument's `Bytes.create`. Added
   to 2.5 and section 6, with §6's run-position wording and the gap
   inside a body.
3. Rough edge 1's [P] said order "may be" unobservable and named only a
   crashing and a diverging argument as a counterexample, which needs a
   divergence §17 may rule out. A world effect in one argument and a
   crash in another observe order with no divergence:
   `proto/review5/04_effect_vs_crash.sl` prints `effect ran` and then
   crashes, under slc's native build and the reference, and the other
   order, which §15 does not exclude, prints nothing (§42: the driver
   flushes "after every write"). Rewritten, and the question to the
   owner reworded.
4. Rough edge 4 said §33 makes separately built values with no
   non-erased field share one word. §33 fixes the word only for a
   tagged type or an untagged one not marked `extern`, "an unspecified
   word otherwise". It also left out §37's "a fresh block" (a `many`
   `cell-write`) and "a fresh copy" (a `many` invocation with a store).
   Both added; "DESIGN.md does not say" narrowed to "I found no
   sentence".
5. The 2.3 row on macro expansions listed seven zero-case sites of the
   per-path `fuel` as if they were all; there are about twenty. It also
   grouped `:511` with the run's count, while `:511` is `env-expand`'s
   check of the same per-path budget (`expand-one` passes `fuel` to
   `expand` and on to `env-expand`, `:754, 570, 564`), and it left out
   `run-toplevel`'s own counter (`main.sl:29`, checked at `:3375,
   3382`). Rewritten.
6. 2.5 said `bootstrap.sh`'s differential runs "would not show" the
   `slot-eq` sharing because they build with `--byte`. Its
   `native-compute` runs are built with ocamlopt (`elab-main.sl:38`)
   and compared with `--no-native`, so such a test could show it.
   Hedged.
7. The `-imm` paragraph's barrier claim had no test. ocamlopt 4.14.1
   compiles an `Array.unsafe_set` on an `int array` with no
   `caml_modify` and on an `Obj.t array` with it
   (`proto/review5/04_barrier.ml`, assembly read). Added as [T]; the
   safety condition stays [P].

Re-checked and found right: the 12 files and their line counts,
`bootstrap.sh:23, 26`, `release.sh:17`, `main.sl:187-191`,
`interp.sl:15, 95-114`, `Code`'s 17 constructors at `core.sl:604-622`
and `CApp` at `:611`, `core.sl:337, 3614`, the `elab-main.sl` lines for
the interpreter's errors, `native-run`, `native-batch`, the `hop-`
constants, `splice-go`, and the `Steps` functions, the 20 `"internal:`
sites, `elab.sl:984, 1659, 4680-4730, 4784, 4890`, the `eval.sl` and
`base.sl` lines, the `emit.sl` lines cited in 2.5, the `ffi_core.ml`,
`ffi_templates.txt`, and `prelude.sl` lines, 103 FFI functions and 7
extern types, 6 `extern at` functions, the `mini/` citations,
`MANUAL.md:154-166`, the reference's 6,909 lines, the README citations,
and the quotations from §6, §15, §27, §29, §31, §33, §36, §37, §42,
§45, §62, §67, §69, and §72. The README's "Not modelled: ... macros"
is stale under `--no-extern` too: the reference expands `std/macro.sl`'s
`and` with and without it.

Points I am unsure of:

- Whether `README:254-258`'s "the generated printer" means the emitted
  OCaml printers or `show-type`, which generates them with the `show-fuel`
  budget; the emitted printers take no fuel, so the sentence's "take a
  `Nat`" fits only the generator. Either way it does not name `show-at`,
  so 2.3's "silent" stands.
- `slc --interpret` on `04_head_arg_compiled.sl` was killed for lack of
  memory here, so its order on this test is not shown; 00-summary
  cites other tests for it.
- The [P] that the `imm` stores are GC-safe when both words are
  immediates is still unchecked against the runtime sources.

## Coordinator notes

1. 2.5's barrier paragraph said no safety argument for skipping
   `caml_modify` was found or checked, and section 6 listed the bypass
   as unchecked on 4.14 and OCaml 5; the reviews' unsure points say the
   same. 08 now supplies that argument for OCaml 4.14.1 on amd64 without
   flambda, from the runtime sources and stress tests, under its
   conditions, and finds that the reference interpreter's `-imm` blits
   fail them (BUGS.md 26). The summary, 2.5, and section 6 now point to
   08, and section 6 keeps OCaml 5, flambda, arm64, and systhreads as
   unchecked. From 08 §1, §7, and §8.

## Round 6 review notes

A sixth adversarial review read the brief, CLAUDE.md, and all of
DESIGN.md, opened the cited lines, and re-ran `deep.sl` under
`slc --interpret` (49,999 `Cons _ 0`, then `Cons _ _ _)`, as stated),
`04_head_arg_compiled.sl` (native and `--byte`, both
`Invalid_argument("Array.make")`; with `h` made 1, `Bytes.create`; the
reference also `Array.make`), `04_effect_vs_crash.sl` (native,
`--byte`, and the reference all print `effect ran` and then crash),
`04_barrier.ml` (assembly as stated), `argorder.ml`, and `ord2.sl`'s
emission. It also checked 2.5's barrier paragraph and the Coordinator
note against 08 and the OCaml 4.14.1 runtime sources.

1. 2.5 said skipping `caml_modify` is safe "only" when both words are
   immediates. Both words immediate is sufficient, not necessary: the
   4.14.1 runtime's comment at `memory.c:606-608` asks for the barrier
   only unless the old value "is not a shared block and the value being
   written is not a young block", and `caml_modify` (`:617-658`) does
   nothing else. Reworded.
2. 2.3 and section 5 said flatly that `self/README.md:254-258` does not
   cover `show-at`, so the README is silent on the defect. The
   sentence's "the generated printer" takes a decreasing `Nat` with a
   fuel of "100000", which fits `show-at`'s depth and `show-fuel`, and
   not the emitted printers, which take none; the fifth review left this
   open. Both places now say the README is either silent or
   contradicted.
3. 2.5 said `==` answers `ESome` for two values "the spec allocated
   separately", while the same paragraph and rough edge 4 say DESIGN.md
   does not settle whether separately built values may share a word.
   Now "the program built separately".
4. Rough edge 1 said evaluation order "is observable without any
   divergence". The example observes it only through a real run's §31
   crash; the spec's run, with "unlimited stack and heap", would not
   crash there, so both orders give it the same output. Qualified. Its
   "§61 does take the statements of a body to run in written order"
   generalized from one statement and one call; hedged.
5. The 2.6 table called the array class "`-imm` barrier-free", but
   `lib/ffi.ml:102, 107` map `array-swap-imm` and `array-place-imm` to
   the barriered `swap` and `place`; only `ffi_core.ml`'s functions, the
   templates, and the reference's blits skip the barrier. Qualified, and
   the summary now names `lib/ffi_core.ml` and its templates rather than
   "the `-imm` FFI operations".
6. 2.6 said `world-do` is specified "by DESIGN.md directly"; §42 makes
   `lib/prelude.sl` "the reference for the requests and their answers".
   Added.
7. Rough edge 2 cited `MANUAL.md:162-164` for the refusal of a crashed
   run-position form; it is at 163-165. The 2.3 row's `MANUAL.md:154-162`
   left out the default at 163. The speed comment is
   `ffi_core.ml:315-317`, which 2.5 cited once as 315-316. Corrected.
8. 2.5 printed slc's emission for `04_head_arg_compiled.sl` as `v1`,
   `v2`; the real names are generated (`v42144___42144__`). Marked as
   shortened. §29's "the elaborator's own binders for its head,
   arguments and scrutinee (§15)" was added beside the gap on head
   order, since it binds the head too and orders nothing.
9. Section 5's "reproduced in all four reviews": the fifth did not
   re-run it and this one did. Reworded.

Re-checked and found right: the 12 files and 18,652 lines, the
reference's 6,909 lines, the 827 lines of OCaml runtime, `mini/`'s 6,849
lines and its `elab.sl`/`elabfn.sl` sizes, the `elab-main.sl` lines for
`eval`, `apply`, `run-code`, `env-expand`, `splice-go`, `splice-call`,
and the expansion-limit messages, `elab.sl:4680-4730, 4784, 4890`,
`interp.sl:15, 95-114`, `main.sl:187-191`, `eval.sl:1018, 1055, 1146,
1159`, `base.sl:100-109, 157-161, 181-182`, `release.sh:17`,
`bootstrap.sh:23, 26`, the `ffi_core.ml`, `ffi_templates.txt`, and
`prelude.sl` lines in 2.5, the self/README lines cited, and the
quotations from §6, §15, §27, §29, §31, §33, §42, §45, §61, §62, §67,
and §72.

Points I am unsure of:

- `mini/elab.sl:1241` is cited for `Fails`; the type starts at 1239,
  and 1241 is its constructor, which names `ElabProgram`.
- Whether the theorem shapes in 2.6 and decision 5 also need to range
  over evaluation orders (rough edge 1), as they range over `slot-eq`
  and world answers; nothing here settles it.

## Round 7 review notes

A seventh adversarial review read the brief, CLAUDE.md, all of
DESIGN.md, and SOUNDNESS.md, opened the cited lines, and re-ran slc's
output for `order.sl` and `ord2.sl`, `deep.sl` under `slc --interpret`
(49,999 `Cons _ 0`, then `Cons _ _ _)`), `04-deep-fn.sl` built by slc
(all 100003 elements, 8 MB stack), `slot_eq_share.sl` (slc native,
`--byte`, and `--interpret`, and the reference interpreted and built
natively), `share.ml`, `argorder.ml`, `tc3.ml`, `tc4.ml`, and
`04-tc-direct.ml` (1 MB stack), `04_barrier.ml` (assembly), the five
`imm` stores of `tests/cell_imm.sl`, and `04_head_arg_compiled.sl`
(also with a small `h`) and `04_effect_vs_crash.sl` under the
reference (interpreted, `--no-extern`, and built natively and with
`--byte`), `slc --interpret`, and slc's native and `--byte` builds. All
[T] results held; item 4 qualifies one.

1. Reported by 01's reviewer through the coordinator, and confirmed:
   the 2.3 row on macro expansions gave the zero case as "refusal, as
   §62 requires". §62 says only "At most 10000 expansions run in one
   run, every file on the command line included", and a grep of
   DESIGN.md finds nothing on what happens past the limit. Now:
   refusal ("more than 10000 macro expansions"), with §62 stating the
   limit but not what happens past it.
2. 2.5 said of head-before-argument order "Only this one test, inside
   a function body, was run", under a bold lead that stated the order
   in general, and section 6 said "one test". 02 §2.2's two world-write
   tests, added in round 7 and re-run here, show the same order under
   the reference, `slc --interpret`, and slc's native and `--byte`
   builds; slc's OCaml for both binds the head first. 2.5, section 6,
   rough edge 1, and the evidence list now include them, and the lead
   is scoped to the tests run.
3. Rough edge 2 cited `MANUAL.md:163-165` for the refusal of a crashed
   run-position form; the sentence is at 162-164. MANUAL.md is
   unchanged since Nov 5, so the round 6 note that moved the cite from
   162-164, and its "default at 163" (which is at 162), were off by
   one. Fixed. Added that on a host stack overflow in run position
   both implementations die instead, with no message naming the file
   or the form (`proto/review7/02_deep_runpos.sl`).
4. The summary and 2.5 said `slot_eq_share.sl` answers `ENone` under
   "the reference". The reference's interpreter does; its native build
   prints `(BTrue)`, as slc's does. Qualified.
5. The 2.3 row gave `run-toplevel`'s checks as `:3375, 3382` right
   after `main.sl:29`, which reads as `main.sl` (191 lines); they are
   `elab-main.sl:3375, 3382`. Fixed.

Re-checked and found right: the 12 files and 18,652 lines, the per-file
counts, the 20 `"internal:` sites, 827 lines of OCaml runtime, the
reference's 6,909 lines, `mini/`'s 6,849 lines and its `elab.sl` and
`elabfn.sl` sizes, `Code` at `core.sl:604-622`, `core.sl:337, 3614`,
`main.sl:27-30, 187-191`, `elab-main.sl:38, 40-60, 119-131, 158-445,
185-187, 509-629, 752, 3375-3391`, `elab.sl:4680-4682, 4717, 4730,
4784, 4890`, `interp.sl:15`, `eval.sl:1018-1025, 1055, 1146, 1159`,
`base.sl:157-161, 181-182`, the `emit.sl` lines of 2.3 and 2.5, the
`ffi_core.ml`, `ffi.ml`, and `ffi_templates.txt` lines, `release.sh:17`,
`bootstrap.sh:23, 26`, the self/README lines cited, the `mini/` lines
of 2.4, and the quotations from §6, §15, §27, §29, §31, §42, §45, §62,
§67, and §72.

Points I am unsure of:

- `slc --interpret` on `04_head_arg_compiled.sl`, under a 6 GB memory
  cap, dies with "Stack overflow" whatever `h` is, so that test still
  does not show the interpreter's order (the fifth review's unsure
  point); 02's world-write tests do.
- Under `--no-extern` the reference crashes on the 2^60 literal of
  `04_head_arg_compiled.sl` and `04_effect_vs_crash.sl` before running
  anything (02, Round 7 review notes), so those runs say nothing about
  order.
