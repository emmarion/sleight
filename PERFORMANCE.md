# Writing Sleight that extracts to fast OCaml

How to shape a program's runtime part so that the OCaml both extractors
write (`--extract` and slc) does what hand-written OCaml would. The
observations come from reading extracted code and the `ocamlopt -S` output
on OCaml 4.14.1 without flambda, at `-inline 50`, against hand-written
OCaml equivalents. Other compilers may differ.

## Use the externs

In hot code, each arithmetic step, comparison, zero test, element access,
store and copy should be a call to one of the prelude's externs, not a
`match` or a `Succ` on a `Nat`, or a recursion over one. Externs extract to
single OCaml operations; the same thing in plain Sleight runs as written.
The list below covers only the cases found so far, so for anything else
search `lib/prelude.sl`'s `extern` declarations, reading their signatures
for the facts they hand back. `lib/ffi_templates.txt` shows the OCaml each
one extracts to.

- `u62-*` for arithmetic, bit operations and comparisons. A `Nat` may be
  a bignum, so its own operations check which it is; the `u62-*` forms take
  erased proofs that operands and results are below 2^62, and each is one
  OCaml operator on a native int. A `Succ` checks `Obj.is_int` and
  `max_int`; a match on a `Nat` checks `Obj.is_int` and computes the
  predecessor even when unused. Numeral operands appear to be
  constant-folded, so `u62-div p 3` compiles to a multiply. ocamlopt does
  not know the operand is non-negative, though, so `u62-div p 4` keeps a
  sign fix-up around its shift; `u62-shr p 2` is a single shift.
- `nat-zero-dec` for zero tests: one compare, no bound proof, and `IsSucc m`
  gives the `(Succ m)` shape `u62-dec` needs.
- `u62-lt-dec` as a loop's bound test, with the termination measure erased
  (below).
- `array-get`, `array-pluck` and the other array and `Bytes` accesses: one
  unchecked load or store each, the proofs standing in for bounds checks.

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
- To build a fresh block, apply its constructor: `cell-alloc` then stores
  first fills the block with the vacant word.

## Avoid the write barrier

OCaml's write barrier, `caml_modify`, runs on a store into an existing
block unless the compiler knows the value is an immediate. Extracted code
holds every value as `Obj.t`, so the knowledge has to come from a proof.

- `array-place-imm` and `array-swap-imm` skip it, given `Imm` proofs for the
  old and the new element; `array-place` and `array-swap` pay it on every
  store. `(imm o n)` does the same for a cell store (§37).
- `array-blit-imm` copies immediates with a `memmove`, where `Array.blit`
  pays the barrier per element when the destination is in the major heap.
- A store of a pointer pays it, as in hand-written OCaml.

## As in OCaml

A first-class `Fn` call is an unknown OCaml
application. A local `def-fns` is an OCaml local closure; to call it from
the body it is defined in, give it a level minted before the enclosing
function.

## Known gaps

- No 16-bit access to `Bytes`: two byte operations stand in for
  `%caml_bytes_get16u`/`set16u`.
- Under slc, `slot-eq` allocates a block when it answers `Some`; the
  reference extractor shares a static one. Either way it costs a few
  instructions more than OCaml's `==`.
