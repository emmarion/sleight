# Writing Sleight that extracts to fast OCaml

How to shape a program's runtime part so that the OCaml both extractors
write (`--extract` and slc) does what hand-written OCaml would. The
observations come from reading extracted code and the `ocamlopt -S` output
on OCaml 4.14.1 without flambda, at `-inline 50`, against hand-written
OCaml equivalents. Other compilers may differ.

## Use the externs

In hot code, each arithmetic step, comparison, zero test, element access,
store and copy should be a call to one of the prelude's externs, not a
`match` or a `Succ` on a `Nat`, or a recursion over one. Most externs extract
to a single OCaml operation; the same thing in plain Sleight runs as written.
The list below covers only the cases found so far, so for anything else
search `lib/prelude.sl`'s `extern` declarations, reading their signatures
for the facts they hand back. `lib/ffi_templates.txt` shows the OCaml each
one extracts to.

- `u62-*` for arithmetic, bit operations and comparisons. A `Nat` may be
  a bignum, so its own operations check which it is; the `u62-*` forms take
  erased proofs that operands and results are below 2^62, and work on a
  native int: most are one OCaml operator, `u62-divmod` is two,
  `u62-popcount` a short run of bit arithmetic, and `u62-bit-length` and
  `u62-trailing-zeros` a non-allocating call into Zarith. A `Succ` checks
  `Obj.is_int` and `max_int`; a match on a `Nat` checks `Obj.is_int` and
  computes the predecessor even when unused. Numeral operands appear to be
  constant-folded, so `u62-div p 3` compiles to a multiply. ocamlopt does
  not know the operand is non-negative, though, so `u62-div p 4` keeps a
  sign fix-up around its shift; `u62-shr p 2` is a single shift.
- `nat-zero-dec` for zero tests: one compare, no bound proof, and `IsSucc m`
  gives the `(Succ m)` shape `u62-dec` needs.
- `u62-lt-dec` as a loop's bound test, with the termination measure erased
  (below).
- An `Array` or `Bytes` in place of a `List` for data that is indexed,
  updated or bulk-copied. A `Cons` extracts to a three-word block, one
  pointer to follow per element. An array is one word per element in one
  block, with an unchecked load per access, and its index list is erased,
  so the `Nth` and `SetNth` proofs cost nothing at runtime.
- `array-get`, `array-pluck` and the other array and `Bytes` accesses: one
  unchecked load or store each, the proofs standing in for bounds checks.
- `bytes-get16`, `bytes-get32`, `bytes-set16`, `bytes-set32`, the reads'
  `-many` forms and `str-get16`/`str-get32` for a little-endian number of
  two or four bytes, in place of two or four byte accesses and the
  arithmetic joining them. In one check of the `ocamlopt -S` output, a 16-bit read was one
  `movzwq`, and a 32-bit read one `movl` with a sign-extend and a mask, with
  no boxed `int32`.
- `str-get`, `str-get16` and `str-get32` to read a `String`, in place of a
  match on `SCons`, which allocates a fresh slice for the rest of the string
  at every character. In one measurement, walking 10^8 characters by match
  took about 3.4 ns and 4 allocated words per character, against about
  0.7 ns for a hand-written OCaml loop of loads.
- `u62-popcount`, `u62-trailing-zeros` and `u62-bit-length` (leading zeros
  are 62 minus the bit length), in place of a loop over `u62-bit-test`. In
  one measurement, summing `u62-popcount` over 10^7 values took about 4 ns
  per iteration against about 200 ns for a 63-step `u62-bit-test` loop.
- `bytes-fill` for a run of one byte, in place of a `bytes-set` loop: it is
  `Bytes.fill`, which measured about 0.02 ns per byte against about 1.4 for
  the loop.
- `bytes-cmp`, `bytes-cmp-unique-many` and `bytes-cmp-many` to compare two
  byte ranges, with `cmp-eq` for equality, in place of a `bytes-get-many`
  loop. Two whole buffers go to `Bytes.compare`; other ranges are compared
  eight bytes at a time in OCaml, which measured about 0.2 ns per byte,
  against about 0.04 for `Bytes.compare` and 1.7 for the loop.

## Let proofs do the work

What a program proves is erased: erased parameters, results, `let`s and
fields; `at` parameters and returns; newtype wrappers, `coerce` and
placings; calls of at-functions such as `array-unpluck`. A proof can
therefore stand in for a runtime check or a runtime value.

- A loop's termination measure can be erased: `(subterm erased (Nat) k)`,
  with `u62-lt-dec` as the bound test. This compiled to the same machine
  code as the hand-written loop; recursing on a `subterm many (Nat)` was
  about 1.6× slower.
- Bounds proofs make every array and `Bytes` access unchecked.
- A type whose non-phantom constructors have only erased fields, such as
  `Dec`, `Cmp` or `ErasedMaybe`, is an immediate, so a decider that answers
  one allocates nothing. Where a match on a templated decider's call is the
  final form of its expression, both extractors put the branches in the
  template's own tests. Elsewhere, as in a `let`'s right-hand side, the
  answer is built as a constant and matched again.
- An existential row marked `newtype` over an inner array costs nothing, so
  an array of arrays is two loads: `array-pluck`, access, `array-unpluck`.

## Mutate instead of allocating

A `unique` value can be updated in place, so hot code need allocate no more
than hand-written OCaml does.

- Arrays: `array-place`, `array-swap` and their `-imm` forms store in place.
- Records: a unique destructure, then a cell invocation that skips (`(at)`)
  the unchanged stores (§37, §38), updates the block in place.
- Mutable globals: a parameter `(unique (Array A xs) a at g)`, `g` a
  top-level unique binder, returned `at a`, is neither passed nor returned;
  the body reads the global `g`. A `def-fns` cannot capture `g` itself, and
  a `def-unique` closure can be called once.
- Results returned `at` a parameter cost nothing, while two non-`at`
  results allocate a tuple, even when inlined, as hand-written OCaml does
  (the `u62-divmod` template does not).
- Lists built front to back: in destination-passing style (DESIGN.md §61),
  the helper writes the head into a vacant cell before a `tail` call fills
  the rest, then invokes the cell with every store skipped. Per element:
  one allocation, two stores, constant stack.
- To build a fresh block, apply its constructor: `cell-alloc` then stores
  first fills the block with the vacant word.

## Avoid the write barrier

OCaml's write barrier, `caml_modify`, runs on a store into an existing
block unless the compiler knows the value is an immediate. Extracted code
holds every value as `Obj.t`, so the knowledge has to come from a proof.

- `array-place-imm` and `array-swap-imm` skip it, given `Imm` proofs for the
  old and the new element; `array-place` and `array-swap` pay it on every
  store. `(imm o n)` does the same for a cell store (§37).
- `array-blit-imm`, `array-blit-many-imm` and `array-move-imm` copy
  immediates with a `memmove`, where `Array.blit` pays the barrier per
  element when the destination is in the major heap.
- A store of a pointer pays it, as in hand-written OCaml.

## As in OCaml

A first-class `Fn` call is an unknown OCaml
application. A local `def-fns` is an OCaml local closure; to call it from
the body it is defined in, give it a level minted before the enclosing
function.

## Known gaps

- No byte search: finding a byte in `Bytes` is a `bytes-get-many` loop, at
  about 1.7 ns per byte in one measurement, where memchr would be about
  0.03.
- `bytes-cmp` on ranges other than two whole buffers runs at about a fifth
  of memcmp's speed, since OCaml's runtime compares only whole buffers.
