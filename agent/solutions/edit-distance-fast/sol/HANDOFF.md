# Edit-distance-fast handoff — complete and revalidated

## Status

**The task is solved.** `work/distance.sl` defines `edit-distance-fast` and proves the required goal with:

```
(qed (MkEditDistance _ edit-distance-fast))
```

This session revalidated the carried-over implementation. No implementation or test changes were needed; only the latest benchmark timing in `work/README.md` was updated. Latest `check`:

```
compile: ok, no warnings
edit-distance-fast/spec.sl:131:1: note: proved `(goal many (EditDistance))`
work/distance.sl:66:1: note: by this `qed`
```

The task benchmark and both regression programs compile with `warn_unused: true` with **no warnings**, and all exit 0. Searching work/ found no `;! suppress`. There are no scratch/ dependencies.

All mandatory performance conditions are met:

* Exactly three allocations per nonempty-input call: three reusable row arrays. Zero allocations when either input is empty.
* No per-cell or per-row allocations, confirmed by benchmark counters and generated OCaml inspection.
* All solution array writes use `array-place-imm`, extracting to writes on int arrays.
* All solution runtime arithmetic/comparisons use u62 primitives.
* All solution runtime recursion is tail recursion.

There is **no required remaining implementation work**. Optional improvements such as a symmetry proof to use the shorter column dimension are not unfinished requirements. `work/README.md` documents the completed implementation.

## Exact compile order

Use this list for `check`, or as the common prefix for `sl`:

```
std/nat.sl
std/list.sl
std/macro.sl
std/tactics.sl
edit-distance-fast/spec.sl
work/literals.sl
work/arith.sl
work/cost.sl
work/least.sl
work/cell.sl
work/bounds.sl
work/suffix.sl
work/text.sl
work/boundary.sl
work/row.sl
work/initial-row.sl
work/swap.sl
work/build-row.sl
work/distance.sl
```

`work/files.txt` lists the solution portion, starting at literals.sl. Supply paths explicitly; it is not an include file.

For a runtime program, append exactly one of:

* `edit-distance-fast/perf.sl`: task benchmark;
* `work/test-distance.sl`: 10 end-to-end expected-value regressions;
* `work/test-kernel.sl`: exhaustive byte costs and component/initializer tests.

Use `warn_unused: true`. To inspect extraction, append a runtime program and set `ocaml` to a scratch path. Without a runtime caller, unreachable functions are omitted.

## This session's evidence

### Task benchmark

Compiled the full prefix plus perf.sl, `warn_unused: true`:

* compile: ok, no warnings;
* run: exit 0;
* 1.51 s wall clock, 1.49 s CPU, 29 MB peak memory.

Timed results (identical to the previous session):

```
random-distance 3670
long-short-distance 39200
short-long-distance 39200
near-equal-distance 103
case-only-distance 1168
all-bytes-distance 5801
minor-words 0
promoted-words 0
major-words 95436
minor-gcs 0
major-gcs 0
```

The 95,436 words are exactly the 18 arrays, including headers:

```
3 * (2802 + 402 + 20002 + 3002 + 2802 + 2802) = 95436
```

Each target contributes target length + 1 cells + 1 header word, times three arrays. There are no additional timed allocations.

### Regressions

`work/test-distance.sl`: no warnings, exit 0, prints `ok: 10 edit-distance regressions`. Covers empty inputs, equal strings, ASCII case substitution, insertion/deletion, adjacent swap, kitten/sitting, and CA/ABC in both directions. CA/ABC costs 6 (optimal string alignment), not unrestricted swap-then-insert cost 4.

`work/test-kernel.sl`: no warnings, exit 0. Exhausts all 65,536 byte pairs through ed-subst-sum (sum 130508), checks singleton case substitution (1), swap (2), initial row length 20,000 (head 40000), empty initial row (head 0), arithmetic at max-array-length-1 (largest boundary 36028797018963966), and real Text/Bytes access. Only its two explicit arrays are allocated.

### Extracted code inspection

Compiled perf.sl with `ocaml: "scratch/extracted.ml"`, no warnings, and inspected all solution runtime functions (lines 700–744):

* Integer arithmetic/comparisons directly on ints;
* `Bytes.unsafe_get` / `Char.code` for byte reads;
* `Array.unsafe_get` for row reads;
* `Array.unsafe_set` on int arrays for writes;
* Tail self-calls in initializer, inner row loop, outer distance loop;
* No runtime proof/list/Option objects or tuple allocation;
* Inner row loop returns unit; row wrapper returns only the new immediate boundary;
* Three explicit `Array.make` allocations in total per nonempty call;
* `Array.make` uses one-time `Z.to_int` on the size, but there is no general-Nat arithmetic in loops.

Scratch captures and generated code do not persist. Reproduce with the compile order above. No new permanent tests/source files were necessary this session.

## Algorithm and proof architecture

The arrays store suffix distances, iterating right-to-left over both inputs. Source is the row dimension, target is the column dimension (target length + 1). Rows rotate through three unique arrays so that the old row and old-old row are available for substitution/deletion and adjacent swap. It computes **optimal string alignment**, not unrestricted Damerau–Levenshtein distance.

### Foundation

* `EdSuffix A whole i rest`: dropping i elements leaves rest. Erased next/prev/end/Nth/length lemmas never copy input tails at runtime.
* `EdRow xs ys cells`: every target suffix has its Dist from xs in the corresponding cell. Contents are directly `List (Copy U62)`; all cells also have `d < ed-value-limit = 2^60` bounds.
* `ed-dist-small`: derives the uniform 2^60 bound from Dist and input suffix length/fits proofs. Actual distances are below 2^56 for valid Texts.
* `ed-row-get`: reads one live Nat plus erased Dist/bound, forwarding the unique array without a runtime tuple.
* `ed-array-before`: writes one immediate at j before the completed suffix at j+1, extending the erased suffix invariant.
* `ed-step3` / `ed-step4`: certified local recurrence kernels, using three ordinary candidates and either a no-swap proof or a formed +2 swap candidate.
* `ed-initial-row`: right-to-left tail initializer for the empty-source row. No target byte reads at runtime.

### Cached histories (`swap.sl`)

`EdHead rest byte present` is erased: false forces rest=[], true forces rest=byte::tail. The live cached byte and Bool are immediates.

`EdPrevious xs ys cells byte present` is erased: false forces xs=[] and imposes no row constraint on the dummy old-old buffer; true forces xs=byte::tail and carries `EdRow tail ys cells`.

`ed-select-cell` uses these histories and flags:

1. Missing source/target lookahead gives SwapNoLeft/SwapNoRight.
2. Compare current source x to target lookahead y2; inequality gives SwapNoFirst.
3. Compare source lookahead x2 to current target y; inequality gives SwapNoSecond.
4. Both equal: read old-old row at i+1, where i is the boundary column and new column is j=i-1; form +2, SwapYes, use step4.

Other cases use step3. No live Option/list swap candidate is built.

### Row loop (`build-row.sl`)

`ed-build-row` adds 2 to the cached source-vs-empty boundary, forms DistDelete, writes the final column, and starts `ed-build-row-loop`.

The inner tail loop tracks the target suffix at boundary i, completed output row suffix, previous-row diagonal a, current-row right neighbor e, cached target lookahead, and histories for the two previous rows.

At j=i-1, obtain the new erased suffix via suffix-prev, read byte y with bytes-get-many/Nth, read previous row at j for b, select the certified new distance d, derive its small bound erased, write at j, extend EdRowCons, and tail-call caching b and d. At i=0 the full row proof follows from EdSuffixHere.

### Outer loop (`distance.sl`)

`ed-distance-loop` decrements its source offset, reads the new source byte, obtains its suffix length/fits proof erased, builds a row, then rotates:

* output buffer becomes new previous row;
* old previous row becomes old-old row;
* old old-old row becomes next output buffer.

At source offset 0, final row column 0 is the answer. Array outputs are optimized away by unique-state forwarding. The public wrapper reads lengths using Bytes.length, returns doubled length immediately when either input is empty, otherwise allocates the three arrays and runs the outer loop. MkText unwrap is free (newtype).

## Source map / useful conventions

* `literals.sl`: static Add 32 91 123 for ASCII folding bounds.
* `arith.sl`: erased addition monotonicity/associativity and Double-to-Add.
* `cost.sl`: immediate ed-fold, ed-byte-eq, ed-cost and their proofs.
* `least.sl`: minimum proofs and immediate min3/min4.
* `cell.sl`: immediate +2 / substitution sums / local DistStep kernels.
* `bounds.sl`: distance <= 2*(length xs + length ys), hence 2^60 bound.
* `suffix.sl`: generic erased suffix relation and array suffix preservation.
* `text.sl`: constant-time Text length with proofs.
* `boundary.sl`: empty-string Dist and immediate doubled length.
* `row.sl`: EdRow and array access/update helpers.
* `initial-row.sl`: tail initialization and suffix/length fit helpers.
* `swap.sl`, `build-row.sl`, `distance.sl`: full algorithm as above.

Library conventions: array-make/array-get take A=U62 (Copy is wrapped internally), while array-place-imm takes A=Copy U62 and a MkCopy/MkU62 value. Prove literal bounds directly against named moduli (e.g. u8-modulus), not an unrelated opaque numeral 256. Large Double constants use numeral-of, not enormous unary proofs.
