# 08. Are the barrier-free `imm` stores GC-safe?

A Claude agent wrote this as a reading of the OCaml runtime and of
Sleight's FFI and emitter. It is not a decision, and nothing in it is
approved. Where it and DESIGN.md disagree, DESIGN.md is right.

Tags: **[D]** DESIGN.md, quoted or paraphrased. **[S]** OCaml or Zarith
source, read at the release tag that matches the installed version.
**[C]** compiled or run here. **[A]** my own reading or argument.
Repository files are at commit 5fba336. Test sources are in
`proto/gc/`, and binaries and outputs are in the session scratchpad,
which is not kept. Toolchain: OCaml 4.14.1, amd64, `flambda: false`,
`naked_pointers: true`, `flat_float_array: true`, and Zarith 1.13. The
installed `caml/{memory,address_class,major_gc,minor_gc}.h` are
byte-identical to the 4.14.1 tag's `runtime/caml/` headers.

## 1. Summary

- [A] On 4.14.1, the two places in the brief look GC-safe when the
  overwritten word and the stored word are both immediates. These are
  the FFI's `-imm` operations and slc's `(imm o n)` cell stores.
  `caml_modify` does something only when the old word is a block or the
  new word is a young block. The runtime's own comment states the same
  condition as the one that permits skipping it. Marking, minor
  collection, and compaction all ignore immediate fields.
- [C] Positive stress runs passed with every collection type and with
  the debug runtime's heap check at each major cycle. Each run made
  2,000,000 operations, over 3,200 heap checks ran in all, and no run
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
  elements. The interpreter's `-swap-imm` and `-place-imm` are mapped
  to the barriered `swap` and `place` (`lib/ffi.ml:102, 107`), so they
  are not affected. I did not reproduce this end to end from a Sleight
  program.
- [A] For compiled code, the conditions are as follows. `Imm` must
  really mean "the compiled word is an immediate". Every read of a field
  that an `imm` store can change must be a mutable load. The program
  must run on one domain, or else OCaml 5's memory model needs a
  separate check. OCaml 5's `write_barrier` reads the same way, but I
  did not run anything on OCaml 5 or with flambda.

## 2. Citations checked

- [C] `lib/ffi_core.ml:235-239` is `array_swap_imm`, and `:241` is
  `array_place_imm`. Both use `Array.unsafe_set (cast a : int array)`.
  `:315-317` is the speed comment, `:318` is `blit_words` (that is,
  `caml_blit_bytes`), `:319` is `array_blit_imm`, and `:320-321` are its
  aliases. The brief's ranges `223-241` and `315-320` contain all of
  these.
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
  marking and cleaning are coloured black (`memory.c:452-454, 482-484`).
- [S] A minor collection's roots for old-to-young pointers are only the
  remembered set (`minor_gc.c:371-374`). Its other roots are the local
  and global roots.
- [S] The marking loop pushes only fields with `Is_major_block(v)`
  (`major_gc.c:717`, macro at `:636-641`). `caml_darken` acts only on a
  block (`:281-283`). A block turns black when its scan starts
  (`:301`, `:671`), and the rest of its range waits on the mark stack.
- [S] The debug runtime runs `caml_heap_check` at the start of every
  major cycle (`major_gc.c:414-416` calls `gc_ctrl.c:264-267`). That
  check walks every block and asserts that each pointer field points to
  a valid, non-free (`!= Caml_blue`) head (`gc_ctrl.c:55-117`; the
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
  `mutable` fields slc emits meet this.
- [A] **flambda.** This is not installed, so I tested nothing. I expect
  the array kind to be fixed at type-checking, as without flambda, and
  flambda 1 not to reorder mutable loads across stores, but I have not
  checked either.
- [S] **OCaml 5** (5.2.0 tag). `write_barrier` (`runtime/memory.c:178-199`)
  has the same two tests, `Is_block(old_val)` and
  `Is_block_and_young(new_val)`. With immediates, `caml_modify`
  (`:204-`) reduces to an acquire fence and a release store.
  `int_array_set` is still a plain `Assignment` store
  (`asmcomp/cmm_helpers.ml:765-767`). So on one domain the reasoning
  looks unchanged, and across domains the `imm` store gets the memory
  model of an ordinary `int array` store. I take that to be harmless
  because an immediate publishes no block, but I have not checked it.

## 5. Can a non-immediate word reach these stores?

- [S/C] **`ImmNat`** (`prelude.sl:1448`) is for `n < u62-modulus` = 2^62
  (`prelude.sl:362`). Zarith 1.13's `ml_z_reduce` (`caml_z.c:405-423`)
  returns `Val_long` whenever the magnitude fits in `Z_MAX_INT`, which
  is `max_int` = 2^62-1. [C] `proto/gc/zarith_small.ml` checked 17
  constructions through large intermediates (string parsing, shifts,
  `div`, `rem`, `gcd`, `sqrt`, `of_int64`, `of_float`) and 1,000,000
  random reductions. Every value below 2^62 was immediate, and 2^62 was
  boxed. The FFI's start-up check (`ffi_core.ml:27`) tests only
  `Z.of_int max_int`.
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
  either way.

## 6. Experiments

All of these ran with the normal runtime and with `-runtime-variant d`.
`s` is the minor heap in words. Values below 4k seem to be clamped,
because `s=256` gave the same minor-collection counts as `s=4k`.

| Test | What it does | Result |
|---|---|---|
| `stress.ml` (links `sleight.cmxa`) | 48 old and young arrays, half node pointers and half ints, plus 256 cells. 2,000,000 random ops: `array_swap_imm`, `array_place_imm`, `array_blit_imm`, and the emitted cell-store shape. Barriered pointer stores and garbage are mixed in, with `major_slice`, `full_major` and `compact` on a schedule. Shadow arrays check every word. | All 6 configurations ok. Up to 8,113 minor and 2,049 major collections, and 3 compactions. The debug runs made 3,298 heap checks and none failed. |
| `slc_cells_driver.ml` + `build_slc_cells.sh` | slc's own output for `tests/cell_imm.sl`, with its last line replaced by a driver. The driver runs `swap-in`, `write-in` and `fresh-in` 2,000,000 times on 512 cells beside pointer-holding boxes, under the same collection schedule. | All 6 configurations ok. Up to 5,461 minor and 1,389 major collections, and 8 compactions. |
| `neg_young.ml` | Stores a young pointer into an old array through `int array`, then runs a minor collection and allocation. | Without the barrier: 10,000 of 10,000 corrupted (normal and debug). With `caml_modify`: 0. |
| `neg_mark.ml` | Reads header colours to find the window in which `a` is black and `x` is white, while `x`'s only reference sits in `b`'s still-unscanned tail. It then moves `x` into `a` and overwrites `b`'s slot. | Without the barrier: `x` freed while still referenced in 20 of 20 windows. The debug runtime fails `gc_ctrl.c:64` (`Color_hd != Caml_blue`). With `caml_modify`: 0 of 20. In `imm` mode (only immediate-over-immediate stores in the same window, across all of `b` and `a`): 0 of 20. |
| `interp_blit.ml` | The interpreter's `blit_imm` call on `Value.value` arrays. | 80,000 of 80,000 elements wrong (normal and debug). |
| `kinds.ml` | `-dcmm` | Described in §4. |
| `zarith_small.ml` | Described in §5. | No boxed value below 2^62. |

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
5. On OCaml 5, the same reasoning applies to one domain, and
   multi-domain use has not been looked at.

The interpreter's `array-blit-imm`, `array-blit-many-imm` and
`array-move-imm` meet none of these, since their elements are boxed
`Value.value`s, and the OCaml-level reproducer breaks. Whether and how
to change that is the owner's call. One option would be to map them to
the barriered `blit`, as `-swap-imm` and `-place-imm` already are.

## 8. Unverified

- A Sleight program that trips the interpreter's `blit_imm` end to
  end. I did not write one.
- A Sleight-level stress program using `array-swap-imm`. The emitted
  cell stores were driven from OCaml, and the `-imm` FFI functions were
  called directly.
- Any run on OCaml 5, with flambda, on arm64, or with systhreads.
- Whether `Imm` proofs can be forged through the logic (§10).
- Whether other emitted shapes, such as wide-tagged or `Slots`
  records, have any immutable field that an `imm` store could reach. I
  checked only `emit.sl:291` and `tests/cell_imm.sl`'s output.
