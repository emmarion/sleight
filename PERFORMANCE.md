# Writing Sleight that extracts to fast OCaml

How to shape a program's runtime part so that the OCaml both extractors
write (`--extract` and slc) does what hand-written OCaml would. The
observations come from reading extracted code and the `ocamlopt -S` output
on OCaml 4.14.1 without flambda, at `-inline 50`, against hand-written
OCaml equivalents. Other compilers may differ.

## What is free

Erased parameters, results, `let`s and fields; `at` parameters and returns;
newtype wrappers (`MkCopy`, `MkU62`, `MkU8`), `coerce` and placings; calls of
at-functions such as `array-unpluck`. Numerals used as operands appear to be
constant-folded by ocamlopt, so `u62-div p 3` compiles to a multiply.

## Do this

- **Arithmetic and tests through `u62-*`.** Each is one OCaml operator. A
  `Succ` on a `Nat` checks `Obj.is_int` and `max_int`; a match on a `Nat`
  checks `Obj.is_int` and computes the predecessor even when it is unused.
- **Zero tests with `nat-zero-dec`.** One compare, no bound proof, and
  `IsSucc m` gives the `(Succ m)` shape `u62-dec` needs.
- **Loops on an erased measure.** `(subterm erased (Nat) k)` with a
  `u62-lt-dec` test compiled to the same machine code as the hand-written
  loop; recursing on a `subterm many (Nat)` was about 1.6× slower.
- **`-imm` stores into arrays of immediates.** `array-place` and
  `array-swap` go through `caml_modify`; the `-imm` forms do not. The same
  holds for `(imm o n)` on a cell store (§37).
- **Mutable globals through `at`.** A parameter `(unique (Array A xs) a at g)`,
  `g` a top-level unique binder, returned `at a`, is neither passed nor
  returned: the body reads the global `g`. A `def-fns` cannot capture `g`
  itself, and a `def-unique` closure can be called once.
- **Arrays of arrays through a newtype row.** An existential `Row` marked
  `newtype` over the inner array, then `array-pluck`, access, `array-unpluck`:
  two loads.
- **In-place record updates through cells** (§37, §38): a unique destructure,
  then an invocation that skips (`(at)`) the unchanged stores.
- **Build blocks by constructor application.** `cell-alloc` then stores
  first fills the block with the vacant word, then stores each pointer
  field through `caml_modify` unless it is marked `imm`.
- **`array-blit-imm` for immediates.** It is a `memmove`; `Array.blit`
  calls `caml_modify` per element when the destination is in the major heap.

## Costs that match OCaml's

A function returning two non-`at` values allocates a tuple, even when
inlined, as hand-written OCaml does. The `u62-divmod` template does not.
A first-class `Fn` call is an unknown OCaml application. A local `def-fns`
is an OCaml local closure; to call it from the body it is defined in, give
it a level minted before the enclosing function.

## Known gaps

- No 16-bit access to `Bytes`: two byte operations stand in for
  `%caml_bytes_get16u`/`set16u`.
- Under slc, `slot-eq` allocates a block when it answers `Some`; the
  reference extractor shares a static one. Either way it costs a few
  instructions more than OCaml's `==`.
