# An all-array Skelet #1 runner: plan

This is the plan for replacing the lists of the Skelet #1 runner
(`bb/sk1.sl`, `bb/sk1a.sl`) with arrays. It changes neither the language
nor the prelude. The claims about cost below are expectations from
reading code and from one profile, not measurements of this design.

## 1. Generic infrastructure

### 1a. Growable vector, used as a stack

- A tag/count pair is built from two vectors: one over `Bytes` for tags,
  one over `Array (Copy A)` for counts. The two are written separately,
  kept parallel line for line; there are no macros. The `Array` version
  is generic in `A`.
- The type is indexed by its logical list `xs` only; neither capacity
  nor layout appears in it.
- Stack orientation: logical position 0 is the physical top, so push and
  pop work at the array's end. The reversal is internal to the vector.
- Operations, stated in list terms: read by logical index, push
  (`Cons`), pop, update the first element, length, and drop a prefix
  given by a `Cat` fact.
- Doubling is internal: a write past capacity allocates twice the size
  and copies. Callers and proofs do not see it.
- The record is updated in place through its cell, so an operation does
  not allocate.

### 1b. Scratch

- One scratch tag/count pair for the whole run.
- Its contents go onto a vector by one tail-recursive per-cell copy, not
  a blit: `array-blit` and `bytes-blit` take their source at `many`, and
  a shared scratch could not be used at `unique` again (DESIGN.md §15,
  §16).
- Whether the scratch is a ring or another stack vector (1a) is open
  (section 3).

### 1c. Proofs

- Outside the wrappers everything is about lists, so the `Lz`, `Zk`,
  `Swin`, `Dn`, `Kt`, `Lp` and `Chk` proofs are reused unchanged.
- Reversal, modular indexing and doubling are proved inside the wrappers.
- Chunk boundaries are positions in the right vector's list, related by
  `Cat` facts.
- The list lemmas (`Nth`, `SetNth`, `Agr`) are generic over `(List A)`
  and shared by the `Bytes` and `Array` versions.

### 1d. No per-cell or per-step allocation

- Passes are tail-recursive and carry their state as arguments, rather
  than returning a result record at every level.
- `lstep` is merged into `lrun`, so the runner state travels as tail-call
  arguments.

## 2. Skelet #1 specifics

### 2a. State

- Left vector: the left tape, nearest cell on top.
- Right vector: the tape right of the head, far end at index 0, reading
  up: deepest chunk, ..., `D`, top chunk, `D`, window.
- Chunk metadata vector: per chunk its boundary, pending strides and
  capacity, mirroring the erased `Zk`.
- Scratch (1b).

### 2b. Operations

- Stride: one tail-recursive pass reading the window from the right
  vector's top down and writing its output downward into the scratch,
  merging into the scratch's last cell where a push merges; then the
  window is dropped from the right vector and the scratch is copied onto
  it.
- Fold: move the window/stack boundary and push a metadata entry; the
  new chunk's capacity is found by a scan. No copy.
- Pop with no pending strides: move the boundary back. No copy.
- Pop with pending strides: write the old window (under 5 cells), `D`
  and the chunk's stride output into the scratch, truncate the right
  vector to the chunk's start, and copy the scratch onto it.
- Simple steps: rule rewriting at the heads of the left vector and of the
  right vector's top; cells move between them by pop and push.

### 2c. Outer machine

`try-uni`, `cyc-of`, `tstep`, `cld-of`, the whole-tape `tstride`, and
forcing work on the vectors, so the tape is never converted to lists.
Making the uni step lazy is a separate question.

### 2d. Unchanged

The lazy-stride algorithm, the `Lz` log, the capacity heuristic, the
skip of known-failing strides, the fold and chunk constants, and the
force/enter logic. Only their data representation changes.

## 3. Open questions

1. Whether the scratch is a ring written downward or a second stack
   vector. A ring was planned so that its contents could be blitted;
   with a per-cell copy, a stack vector whose pops come out in the right
   order may serve as well.
2. If a ring: how hard its modular-index proofs are.
3. A stride's output appears, from reading `sw-of`, to be at most
   `3 * (input length) + 1` cells; this is not proven, and matters only
   if the scratch needs reserving.
4. Whether doubling copies with a blit, which is possible there because
   the old array is discarded, and whether `caml_array_blit` uses
   `memmove` or the write barrier for an array in the major heap.

## 4. Measuring

Compare against the list runner (about 10.5 s user for the job in one
measurement) with `bench/sk1.sh`, always at `--inline 25`, and run the
full BB(5) check (`bench/sk1.sh -f`) before relying on a result.
