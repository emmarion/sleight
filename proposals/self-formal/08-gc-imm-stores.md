# 08. Are the barrier-free `imm` stores GC-safe?

A Claude agent wrote this as a reading of the OCaml runtime and of
Sleight's FFI and emitter. It is not a decision, and nothing in it is
approved. Where it and DESIGN.md disagree, DESIGN.md is right.

Tags: **[D]** DESIGN.md, quoted or paraphrased. **[S]** OCaml or Zarith
source, read at the release tag that matches the installed version, or,
for 5.4.1, in the source package its compilers were built from.
**[C]** compiled or run here. **[A]** my own reading or argument.
Repository files are at commit 5fba336. Test sources are in
`proto/gc/`, and binaries and outputs are in the session scratchpad,
which is not kept. Toolchain: OCaml 4.14.1, amd64, `flambda: false`,
`naked_pointers: true`, `flat_float_array: true`, and Zarith 1.13. The
installed `caml/{memory,address_class,major_gc,minor_gc}.h` are
byte-identical to the 4.14.1 tag's `runtime/caml/` headers. §6 also
reports runs with compilers built from Ubuntu's source packages
(`ocaml_4.14.1.orig.tar.xz`, `ocaml_5.4.1.orig.tar.xz`): 4.14.1 with
flambda, 5.4.1 with and without flambda, all amd64, each with Zarith
(1.13 for 4.14.1, 1.14 for 5.4.1) built against it, and a 5.4.1 cross
compiler for arm64 whose programs ran under `qemu-aarch64-static`.
`toolchain.sh` and `arm64.sh` in `proto/gc/` build the tests with one
of these compilers and run them; they do not build the compilers.

## 1. Summary

- [A] On 4.14.1, the two kinds of store this note examines look
  GC-safe when the overwritten word and the stored word are both immediates. These are
  the FFI's `-imm` operations and slc's `(imm o n)` cell stores.
  `caml_modify` does something only when the old word is a block or the
  new word is a young block. The runtime's own comment states the same
  condition as the one that permits skipping it. Marking, minor
  collection, and compaction all ignore immediate fields.
- [C] Positive stress runs passed with every collection type and with
  the debug runtime's heap check at each major cycle and compaction.
  Each run made 2,000,000 operations, over 5,000 heap checks ran in all,
  and no run
  failed. The negative controls have teeth. A barrier-free store of a
  young pointer was corrupted in 10,000 of 10,000 trials. A
  barrier-free overwrite of a pointer during marking freed a live block
  in 20 of 20 trials, and the debug runtime stopped with an assertion
  failure.
- [C] **One path breaks the premise.** The tree-walking interpreter's
  `array-blit-imm`, `array-blit-many-imm` and `array-move-imm`
  (`lib/ffi.ml:89, 117-119`) call `Ffi_core.array_blit_imm`, which is a
  raw `memmove`, on a `Value.value array`. That array's elements are
  blocks (`VWord of Z.t`, `lib/value.ml:22`), not immediates. A
  reproducer that makes the same call corrupted 80,000 of 80,000
  elements. A Sleight program, `proto/bugs/blit_imm_interp.sl`, also
  breaks the reference interpreter through `array-blit-imm`: it
  segfaults, or with `OCAMLRUNPARAM=s=4k` stops with "not an extern
  integer" (§6). `--build` crashes the same way, because the program's
  final call runs in run position in that interpreter.
  `proto/review6/08_blit_many_imm_interp.sl`, the same program through
  `array-blit-many-imm`, fails in the same two ways, and
  `proto/bugs/move_imm_interp.sl`, through `array-move-imm`, segfaults
  in every run tried, with the default minor heap, with `s=4k`, and
  under `--build`. The
  interpreter's `-swap-imm` and `-place-imm` are mapped to the
  barriered `swap` and `place` (`lib/ffi.ml:102, 107`), so they are not
  affected. slc's evaluator maps all three `-imm` blits to its plain
  `array-blit` (`self/core.sl:482`, used at `self/eval.sl:555`), and
  `slc --interpret` runs the same program correctly.
- [A] For compiled code, the conditions are as follows. `Imm` must
  really mean "the compiled word is an immediate". Every read of a field
  that an `imm` store can change must be a mutable load. The program
  must run on one domain, or else OCaml 5's memory model needs a
  separate check. OCaml 5's `write_barrier` reads the same way (§4).
- [C] The stress tests and the young-pointer negative control behave
  the same with 4.14.1 under flambda and with 5.4.1, with and without
  flambda, the stress tests including variants with three extra
  systhreads and, on 5.4.1, three extra domains; the marking negative
  control, which reads 4.14's header colours, behaves the same on
  4.14.1 under flambda. So do the stress test without Zarith and the
  young-pointer control on arm64 under emulation (§6).

## 2. Citations checked

- [C] `lib/ffi_core.ml:235-239` is `array_swap_imm`, and `:241` is
  `array_place_imm`. Both use `Array.unsafe_set (cast a : int array)`.
  `:315-317` is the speed comment, `:318` is `blit_words` (that is,
  `caml_blit_bytes`), `:319` is `array_blit_imm`, and `:320-321` are its
  aliases.
- [C] `lib/ffi_templates.txt:51-52` are the `array-place-imm` and
  `array-swap-imm` templates, also through `int array`.
  `lib/ffi_templates.ml` has no `imm` text.
- [C] `self/emit.sl:863-868` is `imm-stores`, which emits
  `Array.unsafe_set (of_any cell : int array) k (of_any n : int)`. At
  `:870-878`, `cell-write-rope` uses it at `:876`. When the shape is
  wide, `k` is the field index plus 1. The OCaml extractor has the same
  store at `lib/extract.ml:187-192`, gated on `!V.use_externs`.
- [C] slc's output for `tests/cell_imm.sl` has five such stores, in
  three functions. The cell type is emitted as
  `K5_0 of { mutable f0 : Obj.t; mutable f1 : Obj.t }`, and every field
  `emit.sl` declares is `mutable` (`emit.sl:291`).

## 3. What the 4.14.1 runtime does

- [S] The contract is at `runtime/memory.c:606-608`: "You must use
  [caml_modify] to change a field of an existing shared block, unless
  you are sure the value being overwritten is not a shared block and the
  value being written is not a young block."
- [S] `caml_modify` (`memory.c:617-658`) does nothing beyond the plain
  store when `fp` is young. Otherwise it saves `old` and stores. If
  `Is_block(old)` (`:644`) and `old` is young, it returns (`:648`). If
  `old` is an old block, it calls `caml_darken(old)` while
  `caml_gc_phase == Phase_mark` (`:651`). Then, if `val` is a young
  block, it adds `fp` to the remembered set (`:654-655`). So the barrier
  is a deletion barrier, which darkens the old value, in the
  snapshot-at-the-beginning style, together with a generational
  remembered set. It has no insertion barrier. Blocks allocated during
  marking and cleaning, and during sweeping above the sweep pointer,
  are coloured black (`memory.c:452-454, 482-484`).
- [S] A minor collection's roots for old-to-young pointers are only the
  remembered set (`minor_gc.c:371-374`). Its other roots are the local
  and global roots.
- [S] The marking loop pushes only fields with `Is_major_block(v)`
  (`major_gc.c:717`, macro at `:636-641`). `caml_darken` acts only on a
  block (`:281-283`). A block turns black when it is darkened and
  pushed (`:301` in `caml_darken`, `:483` in `mark_ephe_darken`, for an
  ephemeron's data) or when it leaves the prefetch buffer to be
  scanned (`:671`), before its fields are scanned. A range left
  unscanned at the end of a slice waits on the mark stack (`:736-751`).
- [S] The debug runtime runs `caml_heap_check` at the start of every
  major cycle (`major_gc.c:414-416` calls `gc_ctrl.c:264-267`) and
  before every compaction (`compact.c:147`). That check walks the major
  heap and asserts that each field of a live block that points into the
  major heap points to a valid, non-free (`!= Caml_blue`) head (`gc_ctrl.c:55-117`; the
  assertion is at `:64`). After a minor collection, the debug runtime
  fills the minor heap with `Debug_free_minor` (`minor_gc.c:441-449`).
- [S] `caml_blit_bytes` is one `memmove` (`str.c:363-368`). The FFI
  declares it `[@@noalloc]`, so no collection runs during the copy.

## 4. The two hazards, with both words immediate

- [A] **(a) A missed minor root.** This needs a young block as the new
  word. When the new word is an immediate, `caml_modify` would not touch
  the remembered set either (`memory.c:654`), so skipping it changes
  nothing.
- [A] **(b) A premature free during marking.** This needs an old block
  as the old word, so that the deletion barrier has something to
  darken. When the old word is an immediate, `caml_modify` would not
  darken anything (`:644`). Under SATB, the only reachability a store
  can take away is reachability through the old word, and an immediate
  carries none.
- [A] **Concurrent views of the field.** In 4.14 the marker and the
  compactor do not run concurrently with the mutator. A marker that
  reads the field before or after the store sees an immediate either
  way, and an immediate is skipped (`major_gc.c:717`). Compaction
  inverts only block fields. For the `memmove` in `blit_imm`, a torn
  word could only mix bytes of immediates, and its low byte, which
  holds the tag bit, would still come from an immediate. I mention this
  only for OCaml 5's concurrent markers. In 4.14 nothing reads the
  field during the copy.
- [C] **How an `int array` store is compiled** (`proto/gc/kinds.ml`,
  `-dcmm`). A store through `(… : int array)` on an array or on a cell
  becomes a plain `(store int …)`, with no `Double_array_tag` test and
  no call. `Obj.t array` gets the tag-254 test and `caml_modify`. The
  FFI's `word array` (`type word = ..`) and a mutable record field each
  get `caml_modify` with no tag test. This matches
  `asmcomp/cmm_helpers.ml:742-744` (`int_array_set`) and `:2414-2432`
  (`arrayset_unsafe`) [S]. A cell is never a float array (its tag is a
  constructor tag), and per `ffi_core.ml:207-209` no host float is a
  language value, so skipping the tag test seems not to matter.
- [S] **Aliasing.** ocamlopt 4.14 without flambda does no type-based
  alias analysis. CSEgen discards every mutable-load equation after any
  non-initialising store (`CSEgen.ml:247-251, 336-341`). Loads of
  immutable fields survive a store, so a field that an `imm` store
  writes must never be read as immutable. Array loads and the
  `mutable` fields slc emits meet this. [C] A match that binds the fields of such a record
  also reads them with `load_mut` (`proto/review6/08_match_loads.ml`,
  `-dcmm`).
- [C] **flambda.** With 4.14.1 and 5.4.1 built with flambda, at `-O3`,
  `kinds.ml` compiles as without flambda (`-dcmm`): the two `int array`
  stores are plain `(store int …)`, `Obj.t array` gets the tag-254 test
  and `caml_modify`, and the `word array` and record-field stores get
  `caml_modify`. `08_match_loads.ml` reads the fields with `load_mut`.
  That flambda never moves a load of a field that an `imm` store writes
  across the store is not shown beyond these shapes.
- [S] **OCaml 5** (5.2.0 tag). `write_barrier` (`runtime/memory.c:178-199`)
  has the same two tests, `Is_block(old_val)` and
  `Is_block_and_young(new_val)`. With immediates, `caml_modify`
  (`:204-`) reduces to an acquire fence and a release store.
  `int_array_set` is still a plain `Assignment` store
  (`asmcomp/cmm_helpers.ml:765-767`). So on one domain the reasoning
  looks unchanged, and across domains the `imm` store gets the memory
  model of an ordinary `int array` store. I take that to be harmless
  because an immediate publishes no block, but I have not checked it.
  5.4.1 reads the same: `write_barrier` at `runtime/memory.c:183-203`,
  `caml_modify` at `:209-230`, `int_array_set` a plain `Assignment`
  store at `asmcomp/cmm_helpers.ml:776-778`, and `caml_blit_bytes` a
  `memmove` at `runtime/str.c:366-371` [S]. [C] On 5.4.1, `kinds.ml`
  and `08_match_loads.ml` compile as on 4.14.1 (`-dcmm`). The
  multi-domain runs of §6 are one schedule each, not a check of the
  memory model.

## 5. Can a non-immediate word reach these stores?

- [S/C] **`ImmNat`** (`prelude.sl:1448`) is for `n < u62-modulus` = 2^62
  (`prelude.sl:362`). Zarith 1.13's `ml_z_reduce` (`caml_z.c:405-423`)
  returns `Val_long` whenever the magnitude fits in `Z_MAX_INT`, which
  is `max_int` = 2^62-1. [C] `proto/gc/zarith_small.ml` checked 17
  constructions through large intermediates (string parsing, shifts,
  `div`, `rem`, `gcd`, `sqrt`, `of_int64`, `of_float`) and 1,000,000
  random reductions. Every value below 2^62 was immediate, and 2^62 was
  boxed. The FFI's start-up check (`ffi_core.ml:27`) tests only
  `Z.of_int max_int`. [C] It gives the same result with Zarith 1.14
  under 5.4.1, with and without flambda, and with 1.13 under 4.14.1
  with flambda.
- [D/A] **`ImmVacant`.** `vacant-slot`'s word is that of `Nat` 0 (§33),
  which is `Z.zero`, an immediate. **`ImmPlaced` and `ImmFromSlot`**
  hold because a `(Placed s A v)` is represented as the word of `v`
  (§66). **`ImmCoerce`** holds because `Coercible` means the same word
  (§33). `std/immediate.sl` builds every proof it gives from these.
- [A] The proofs are erased and are trusted as any other erased proof
  is, such as the `Nth` proofs that let `unsafe_get` skip its bounds
  check. Whether DESIGN.md's `Type : Type` with no positivity rule (§10)
  admits a terminating erased proof of a false `Imm` is outside this
  note. That question applies to every erased proof, not only `Imm`.
- [C] **Representation modes.** slc has no `--no-extern`
  (`self/main.sl:82`). With `--no-templates`, extern types still go
  through the FFI's runtime views (`MANUAL.md:65-66`), so `Nat` stays
  `Z.t`. The OCaml extractor emits `imm` stores only under
  `use_externs` (`extract.ml:188`). Under `--no-extern`, the `-imm`
  externs run their models, and the models call no FFI code.
- [C] **The interpreter's `blit_imm`** is the exception described in
  §1. In the interpreter, an `Imm` proof still describes the compiled
  word, but the array holds `Value.value` blocks, so both hazards apply.
  `proto/gc/interp_blit.ml` blits young `VWord`s into an old
  `Value.value array` through `Ffi_core.array_blit_imm`, which is the
  call at `ffi.ml:89`, and then runs a minor collection.
  `tests/array_blit_imm.sl`, `array_move_imm.sl` and `array_imm_nat.sl`
  still pass in the interpreter with `OCAMLRUNPARAM=s=4k,o=1`. Their
  arrays are small and short-lived, so I take that as no evidence
  either way. `proto/bugs/blit_imm_interp.sl` arranges the hazard from
  Sleight: it makes an old destination array, blits freshly computed
  `U62`s into it with `array-blit-imm`, allocates, and reads them back
  (§6). It uses `u62-modulus-many`, so it needs externs, as
  `tests/array_imm_nat.sl` does.

## 6. Experiments

The stress tests, the negative controls, `interp_blit.ml` and the
Sleight reproducer ran with the normal runtime and with
`-runtime-variant d`; `kinds.ml` is only compiled.
The six configurations of the two stress tests are those two runtimes,
each with `OCAMLRUNPARAM` unset, `s=4k`, and `s=4k,o=1` (`stress.ml`) or
`s=4k,o=20` (`slc_cells_driver.ml`). `s` is the minor heap in words.
Values below 4k are clamped to `Minor_heap_min`, 4096 words
(`gc_ctrl.c:398`, `caml/config.h:210`) [S], and `s=256` gave the same
counts as `s=4k` [C].

| Test | What it does | Result |
|---|---|---|
| `stress.ml` (links `sleight.cmxa`) | 48 arrays, half node pointers and half ints, plus 256 cells, all promoted by a full major collection before the first operation. 2,000,000 random ops: `array_swap_imm`, `array_place_imm`, `array_blit_imm`, and the emitted cell-store shape. Barriered pointer stores and garbage are mixed in, with `major_slice`, `full_major` and `compact` on a schedule. Shadow arrays check every word. | All 6 configurations ok. Up to 8,113 minor and 2,049 major collections, and 3 compactions. The three debug runs made 2,479 heap checks (32, 393 and 2,054, counted as the debug runtime's `### OCaml runtime: heap check ###` lines) and none failed. |
| `slc_cells_driver.ml` + `build_slc_cells.sh` | slc's own output for `tests/cell_imm.sl`, with its last line replaced by a driver. The driver runs `swap-in`, `write-in` and `fresh-in` 2,000,000 times on 512 cells beside pointer-holding boxes, under the same collection schedule. | All 6 configurations ok. Up to 5,461 minor and 1,389 major collections, and 8 compactions. The three debug runs made 2,678 heap checks (45, 1,235 and 1,398), and none failed. |
| `neg_young.ml` | Stores a young pointer into an old array through `int array`, then runs a minor collection and allocation. | Without the barrier: 10,000 of 10,000 corrupted (normal and debug). With `caml_modify`: 0. |
| `neg_mark.ml` | Reads header colours to find the window in which `a` is black and `x` is white, while `x`'s only reference sits in `b`'s still-unscanned tail. It then moves `x` into `a` and overwrites `b`'s slot. | Without the barrier: `x` freed while still referenced in 20 of 20 windows. The debug runtime fails `gc_ctrl.c:64` (`Color_hd != Caml_blue`). With `caml_modify`: 0 of 20. In `imm` mode (only immediate-over-immediate stores in the same window, across all of `b` and `a`): 0 of 20. |
| `interp_blit.ml` | The interpreter's `blit_imm` call on `Value.value` arrays. | 80,000 of 80,000 elements wrong (normal and debug). |
| `../bugs/blit_imm_interp.sl`, run as `bin/main.exe std/immediate.sl …` | 1,000 trials. Each makes a 3-element `Copy U62` array, allocates (`churn 2000`) so that it is promoted, blits two freshly computed `U62`s into it with `array-blit-imm`, allocates again, reads them back, and counts mismatches. The control replaces the call with `array-blit` and drops the two `ImmAll` arguments. | Segfault (exit 139) in 3 of 3 runs, and with the debug runtime too. With `OCAMLRUNPARAM=s=4k`: "runtime error: not an extern integer: _" (exit 1) in 3 of 3 runs. A single trial with `churn 2000` also segfaults. The control prints `0` in every configuration. `slc --interpret` prints `0`, with or without `s=4k`. |
| `../review6/08_blit_many_imm_interp.sl` | The same program with a `many` source array, through `array-blit-many-imm`. | Segfault (exit 139) in 2 of 2 runs with the normal runtime; with `s=4k`, "not an extern integer: _". Its control (`array-blit-many`) prints `0`, and so does `slc --interpret`. Not run with the debug runtime. |
| `kinds.ml` | `-dcmm` | Described in §4. |
| `zarith_small.ml` | Described in §5. | No boxed value below 2^62. |
| `stress.ml`, `slc_cells_driver.ml` (built from slc's output for `tests/cell_imm.sl`), on 4.14.1 with flambda (`-O3`), 5.4.1, and 5.4.1 with flambda (`-O3`) | The six configurations above on each compiler. On 5.4.1, the debug runs add `V=1`, which walks the heap from the roots at the end of every major cycle and, in the debug runtime, asserts that each reachable block is outside the minor heap and has the new cycle's unmarked status, so that a reachable block the collector judged dead fails it (`runtime/shared_heap.c:884-931`, called from `major_gc.c:1617-1618` on each domain). | All ok. On 4.14.1 with flambda the debug runs printed, for `stress.ml` with `OCAMLRUNPARAM` unset, `s=4k`, and `s=4k,o=1`, 32, 405, and 2,056 heap checks (an earlier build printed 393 for `s=4k`, with 389 major collections against 401), and for `slc_cells_driver.ml` 48, 1,304, and 1,399. On 5.4.1 a rerun of `stress.ml`'s debug build with `s=4k,V=1,v=0x800` logged 215 verifications for its 215 major collections. |
| The same two with `helpers_thr.ml` (three systhreads that allocate and yield) on all three compilers, and with `helpers_dom.ml` (three domains that allocate and call `Gc.major_slice`) on the two 5.4.1 compilers | Normal runtime with `OCAMLRUNPARAM` unset and `s=4k`; debug runtime with `s=4k` (and `V=1` on 5.4.1). | All ok. These counts depend on scheduling and vary between runs. The domains raise the collection counts: three runs of `stress.ml` with `s=4k` on 5.4.1 made 67,250, 31,698, and 97,124 minor and 2,429, 1,164, and 3,626 major collections, against 7,245 and 215 without them. With domains, each domain logs a verification at the end of each major cycle, so two debug runs logged 1,755 for 439 major collections and 1,943 for 486. |
| `neg_young.ml` on the three compilers; `neg_mark.ml` on 4.14.1 with flambda | Normal and debug runtime. | `neg_young`: 10,000 of 10,000 without the barrier and 0 with it, everywhere. `neg_mark`: 20 of 20 freed without the barrier, 0 with it, and 0 in `imm` mode; the debug runtime fails `gc_ctrl.c:64` without the barrier. |
| `stress_noz.ml` (`stress.ml` with `noz_ops.ml`'s copies of Ffi_core's three `-imm` operations, taking `int` indices, in place of Zarith), its systhreads and domains variants, and `neg_young.ml`, built by the 5.4.1 arm64 cross compiler and run under `qemu-aarch64-static` (`arm64.sh`) | The six `stress.ml` configurations, debug with `V=1`; the variants as above. | All ok, with 43, 230, and 14,021 verifications in the three debug runs, one per major collection, the same in each of three runs of the script. With systhreads, the three runs logged 745, 936, and 1,131, one per major collection, and with domains 2,375, 2,448, and 2,315, about four per major collection; these vary with scheduling. `neg_young`: 10,000 of 10,000 without the barrier and 0 with it, normal and debug. |
| `../bugs/move_imm_interp.sl`, run as `bin/main.exe std/immediate.sl …` | `blit_imm_interp.sl`'s design through `array-move-imm`: 1,000 trials, each moving two placed `U62`s from a fresh array into an older array of `Vacant` slots. The control uses `array-move` and drops the two `ImmAll` arguments. | Segfault (exit 139) in 3 of 3 runs, and in 3 of 3 with `s=4k`. `--build` also segfaults (exit 139, 3 of 3) and writes no binary. The control prints `0`; so does `slc --interpret`, with or without `s=4k`. Smaller variants print `0` or stop, some with "not an extern integer: _" or "out of memory", never with another value (BUGS.md 26). Not run with the debug runtime. |

## 7. Conclusion and its conditions

[A] I read the compiled-code stores, the `-imm` FFI operations and
slc's `(imm o n)` stores, as GC-safe on OCaml 4.14.1 under these
conditions:

1. Both the overwritten word and the stored word are immediates in the
   compiled representation. In compiled code this rests on the
   soundness of the `Imm` proofs and on Zarith's small-integer
   canonical form.
2. Every OCaml read of a field that an `imm` store can change is a
   mutable load.
3. The target is not a flat float array. No language value is a host
   float, so that seems to hold.
4. For `blit_imm`, every word in the source range and in the
   overwritten destination range is immediate (`ImmAll` on both
   sides).
5. On OCaml 5, the same reasoning applies to one domain. With three
   other domains allocating and collecting, the stress tests pass (§6),
   which is evidence from the schedules of a few runs, not an analysis
   of the memory model.

[A] With these conditions, the stores also look GC-safe on 5.4.1, with
or without flambda, and on 4.14.1 with flambda, for one domain: the
runtime sources read the same (§4), and the runs of §6 agree.

The reference interpreter's `array-blit-imm`, `array-blit-many-imm` and
`array-move-imm` fail conditions 1 and 4, since their elements are
boxed `Value.value`s, and the OCaml-level reproducer and the Sleight reproducers
`proto/bugs/blit_imm_interp.sl`,
`proto/review6/08_blit_many_imm_interp.sl`, and
`proto/bugs/move_imm_interp.sl` all break. As I read §27 and §62, this
also reaches a program built with `--build` wherever such a call runs
at compile time, in run position or in a macro's expansion, since the
reference interpreter evaluates those. Only the run-position case was
observed (§1). Whether and how
to change that is the owner's call. One option would be to map them to
the barriered `blit`, as `-swap-imm` and `-place-imm` already are.

## 8. Unverified

- A Sleight-level stress program using `array-swap-imm`. The emitted
  cell stores were driven from OCaml, and the `-imm` FFI functions were
  called directly.
- arm64 hardware. The arm64 runs used `qemu-aarch64-static` on an
  amd64 host, which runs arm64 code but, as I understand qemu's user
  mode, not with arm64's weaker memory ordering. slc's cell driver,
  which needs Zarith, was not built for arm64.
- A mark-phase negative control on OCaml 5. `neg_mark.ml` reads 4.14's
  header colours and ran only on the 4.14.1 builds.
- OCaml versions other than 4.14.1 and 5.4.1; 5.2.0's sources were read,
  not run.
- Whether `Imm` proofs can be forged through the logic (§10).
- Whether other emitted shapes, such as wide-tagged or `Slots`
  records, have any immutable field that an `imm` store could reach. I
  checked only `emit.sl:291` and `tests/cell_imm.sl`'s output.

## Review notes

An adversarial review by a Claude agent, at commit 0246a1c. None of the
files this note cites changed between 5fba336 and 0246a1c. The OCaml
sources were re-read at the GitHub tags 4.14.1 and 5.2.0, and Zarith's
`caml_z.c` at `release-1.13`.

Errors and changes:

1. §1, §5, §6, §7 and §8 said the interpreter's `blit_imm` bug was not
   reproduced from Sleight. It now is:
   `proto/bugs/blit_imm_interp.sl` segfaults the reference interpreter
   (exit 139, 3 of 3 runs, normal and debug runtime), and with
   `OCAMLRUNPARAM=s=4k` it stops with "runtime error: not an extern
   integer: _" (exit 1, 3 of 3). A control that uses `array-blit`
   prints `0` in every configuration. `main.exe --build` on the same
   file also segfaults, before anything is compiled. `slc --interpret`
   prints `0`, because `ext-twin` maps the `-imm` blits to
   `ExArrayBlit` (`self/core.sl:482`). The text now says so.
2. §3 said a block turns black "when its scan starts" at `:301` and
   `:671`. At `:301`, and at `:483`, it turns black when it is darkened
   and pushed, before any scan. Only `:671` is at the start of a scan.
   Reworded, with the mark-stack hand-off cited (`:736-751`).
3. §3 said blocks allocated during marking and cleaning are black. They
   are also black when allocated during sweeping above the sweep
   pointer (`memory.c:452-454`). Added.
4. §6 said values of `s` below 4k "seem to be clamped". The clamp is in
   the source: `norm_minsize` (`gc_ctrl.c:398`) raises it to
   `Minor_heap_min`, 4096 words (`caml/config.h:210`). Now cited.
5. §6 did not say what the six stress configurations were. Reruns match
   the recorded counts with `s=4k,o=1` for `stress.ml` (8,113 minor,
   2,049 major, 3 compactions) and `s=4k,o=20` for
   `slc_cells_driver.ml` (5,461 minor, 1,389 major, 8 compactions), so
   the text now names those, as my best reading of what was run.
6. §7 said the interpreter's blits "meet none of" the conditions. They
   fail conditions 1 and 4; 2, 3 and 5 are not what breaks them.
   Reworded, and the compile-time reach of the bug added.

Checked and unchanged: every `memory.c`, `major_gc.c`, `minor_gc.c`,
`gc_ctrl.c` and `str.c` line cited in §3; the comment at
`memory.c:606-608`; `cmm_helpers.ml:742-744, 2414-2432` and
`CSEgen.ml:247-251, 336-341` at 4.14.1; `write_barrier` at 5.2.0
`memory.c:178-199` and `int_array_set` at `cmm_helpers.ml:765-767`;
`ml_z_reduce` at `caml_z.c:405-423` with `Z_MAX_INT` = 2^62-1; every
repository line in §2 and §5; the `-dcmm` output of `kinds.ml` (`int
array` gives `(store int …)`, `Obj.t array` the tag-254 test and
`caml_modify`, `word array` and the record field `caml_modify` alone);
the five `int array` stores in three functions of slc's output for
`tests/cell_imm.sl`, and its `K5_0` type. Reruns: `neg_young` 10,000 of
10,000 without the barrier and 0 with it; `neg_mark` 20 of 20, 0 and 0,
with the debug runtime failing at `gc_ctrl.c:64`; `interp_blit` 80,000
of 80,000; `zarith_small` 0 of 1,000,000 boxed and 2^62 boxed; both
stress tests ok in all six configurations, normal and debug.

Unsure:

- The count of 3,298 heap checks was not re-counted. A heap check runs
  at the start of each major cycle in the debug runtime, and my rerun
  of `stress.ml` with `s=4k,o=20` printed 1,212 of them for 1,208
  major collections, so the figure is plausible but unverified.
- §4's statement that ocamlopt 4.14 without flambda does no type-based
  alias analysis rests on reading `CSEgen.ml`, not on a search of the
  whole backend.
- The reproducer could not be run under `--no-extern`, which segfaulted
  even for the control, probably because `u62-modulus-many` then
  builds 2^62 in the unary model. So whether the models' cell writes are sound under GC
  was not exercised by it, although `lib/eval.ml:47-55` stores them
  through an ordinary `value array` assignment.
- OCaml 5, flambda, arm64 and systhreads remain untested, as §8 says.

Outcome of the reproduction attempt: reproduced. A Sleight program run
by `_build/default/bin/main.exe std/immediate.sl
proposals/self-formal/proto/bugs/blit_imm_interp.sl` crashes through
`array-blit-imm`, deterministically, and the same program with
`array-blit` does not. The values blitted are below 2^62, so their
`Z.t` is an immediate, but the interpreter's array holds `VWord`
blocks around them, and those blocks are what the raw `memmove`
copies without a barrier.

## Round 6 review notes

A sixth adversarial review, at commit 10bd85d; no file under `lib/`,
`self/`, `std/` or `tests/` changed since 5fba336. The OCaml sources
were re-read from fresh clones of the 4.14.1 and 5.2.0 tags and
Zarith's `release-1.13`, and the installed headers compared again
(byte-identical). Reruns: `blit_imm_interp.sl` (exit 139 twice; "not an
extern integer: _" with `s=4k`; one trial also segfaults; the control
prints `0`; `slc --interpret` prints `0`; `--build` exits 139),
`neg_young`, `neg_mark` (normal and debug), `interp_blit`,
`zarith_small`, `kinds.ml` under `-dcmm`, and both stress tests in all
six configurations, normal and debug.

1. §6 said `stress.ml`'s debug runs made 3,298 heap checks, and §1 "over
   3,200 in all". Counting the debug runtime's `### OCaml runtime: heap
   check ###` lines, `stress.ml` makes 32, 393 and 2,054 (2,479), and
   `slc_cells_driver.ml` 45, 1,235 and 1,398 (2,678), 5,157 together;
   the collection counts match those stated. Both places corrected.
2. §3 said the debug heap check runs at the start of every major cycle;
   it also runs before every compaction (`compact.c:147`), which is part
   of the counts above. It also said the check walks "every block" and
   checks "each pointer field"; `check_block` (`gc_ctrl.c:82-117`)
   checks live blocks, and only fields that point into the major heap.
   Reworded.
3. §3 cited `major_gc.c:483` beside `:301` for a block turning black
   when darkened; 483 is in `mark_ephe_darken`, the ephemeron-data
   path. Said so.
4. §8 listed `array-blit-many-imm` as untried from Sleight. The new
   `proto/review6/08_blit_many_imm_interp.sl`, the reproducer with a
   `many` source, segfaults the reference (2 of 2) and stops with "not
   an extern integer: _" under `s=4k`; its `array-blit-many` control and
   `slc --interpret` print `0`. Added to §1, §6, and §7; §8 keeps only
   `array-move-imm`.
5. §2 said the ranges `315-320` contain every cited line; `:321` is
   outside. Corrected.
6. §1 said "the two places in the brief", a brief the reader does not
   have. Now "the two kinds of store this note examines".
7. §6 said "All of these ran" with both runtimes, which included
   `kinds.ml`, which is only compiled. Narrowed.
8. §4's condition that every read of an `imm`-written field is a mutable
   load was argued for array loads and `mutable` fields only. A
   `-dcmm` check (`proto/review6/08_match_loads.ml`) shows a match that
   binds such a record's fields reads them with `load_mut` too. Added.

Checked and unchanged: `memory.c:452-454, 482-484, 606-608, 617-658`
(with `:644, 648, 651, 654-655`); `minor_gc.c:371-374, 441-449`;
`major_gc.c:281-283, 301, 414-416, 636-641, 671, 717, 736-751`;
`gc_ctrl.c:64, 264-267, 398`; `config.h:210`; `str.c:363-368`;
`cmm_helpers.ml:742-744, 2414-2432` and `CSEgen.ml:247-251, 336-341` at
4.14.1; 5.2.0's `memory.c:178-199, 204-225` and
`cmm_helpers.ml:765-767`; `caml_z.c:405-423` with `Z_MAX_INT` =
2^62-1; every repository line in §1, §2 and §5; the five `int array`
stores in three functions and the `K5_0` type.

Unsure:

- The blit reproducers were not run against a debug build of
  `main.exe`, so §6's "and with the debug runtime too" rests on the
  earlier runs.
- `proto/gc/zarith_small.ml`'s header comment mentions "Sleight's own
  Nat operations", which the file does not exercise; §5 does not rely
  on them.

## Round 7 coordinator notes

1. §8 listed runs on OCaml 5, with flambda, on arm64, and with
   systhreads as unverified, and `array-move-imm` from Sleight as
   untried. The compilers were built from Ubuntu's source packages,
   since GitHub archives were not reachable from the session. On
   4.14.1 with flambda, 5.4.1, and 5.4.1 with flambda, the two stress
   tests pass in all six configurations, with systhreads and (5.4.1)
   domains variants, and the negative controls keep their teeth;
   `kinds.ml`, `08_match_loads.ml`, and `zarith_small.ml` give the
   same results as on 4.14.1. On arm64, under qemu's user mode, the
   stress test without Zarith and `neg_young.ml` behave the same.
   `proto/bugs/move_imm_interp.sl` crashes the reference through
   `array-move-imm` (BUGS.md 26). Added to the header, §1, §4, §5, §6,
   §7, and §8; `toolchain.sh`, `arm64.sh`, `noz_ops.ml`, and the two
   helpers are new in `proto/gc/`.

