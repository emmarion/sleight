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
- The scratch is a stack that grows downward: its top is at the lowest
  occupied physical index, so the occupied range holds its logical list
  in order. A stride pushes its output onto it near end first, so that
  range is already in the order the right vector needs above its top,
  and one `bytes-blit` and one `array-blit`, which take their source at
  `unique`, copy it there.
- Doubling copies the old contents to the high end of the new arrays.

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

1. Copying counts without the write barrier. In callgrind profiles of
   this job, `caml_array_blit` on the counts arrays appears to call
   `caml_modify` per element. The `-imm` blits avoid that but need
   `ImmAll` evidence for both runs, and counts at or above 2^62 occur in
   this job, so an array-wide all-immediate flag (branch
   `claude/sk1-immflag`) is cleared too early to help. Open: a
   per-element copy that skips the barrier where both words are
   immediates.

## 4. Measuring

Compare against the list runner (about 10.5 s user for the job in one
measurement) with `bench/sk1.sh`, always at `--inline 25`, and run the
full BB(5) check (`bench/sk1.sh -f`) before relying on a result.
