# Certified longest palindrome

`longest-palindrome-manacher` in `palindrome_manacher.sl` implements Manacher's
algorithm and has this interface:

```sl
(many (List (Nat)) xs) ->
(many (Nat) n) (erased (LongestPalindrome xs n) correct)
```

`LongestPalindrome` is the unchanged relation in `palindrome_relations.sl`:
there is a palindrome of length `n`, and every greater window length is ruled
out. The empty input returns zero. `longest-palindrome` in
`palindrome_naive.sl` is the earlier O(n^4) reference solution.

## Run

From the repository root, after the dependencies in the main README are installed:

```sh
dune build
dune exec bin/main.exe -- \
  self/base.sl pal/palindrome_relations.sl pal/palindrome_naive.sl \
  pal/palindrome_lemmas.sl pal/palindrome_centers.sl pal/palindrome_seed.sl \
  pal/palindrome_manacher.sl tests/palindrome_manacher.sl
```

The order matters: `self/base.sl` supplies the immutable `IdMap` trie and also
has names such as `Length` and `Concat` that the palindrome specification
subsequently shadows. The 27 examples run as a nullary function, including
when extracted. `dune test` includes them with and without externs and in the
three extraction modes supported by the test runner.

For a fast standalone program, use an existing `slc` built as described in
`self/README.md`:

```sh
mkdir -p _build/pal-fast
_build/self/slc -- lib/prelude.sl \
  self/base.sl pal/palindrome_relations.sl pal/palindrome_naive.sl \
  pal/palindrome_lemmas.sl pal/palindrome_centers.sl pal/palindrome_seed.sl \
  pal/palindrome_manacher.sl pal/manacher_main.sl > _build/pal-fast/manacher.ml
ocamlfind ocamlopt -w -a -package zarith,unix -linkpkg \
  _build/pal-fast/manacher.ml -o _build/pal-fast/manacher
python3 pal/check_manacher.py _build/pal-fast/manacher --large
```

`ocamlc` can replace `ocamlopt`. To exercise the bytecode build with a small
stack, run `OCAMLRUNPARAM=l=65536 python3 pal/check_manacher.py
_build/pal-fast/manacher --large` (as one shell command). The 100,000-element
cases exercise the tail-recursive input conversion, scan, and expansion.

The driver reads all of stdin, including any
newlines, as bytes. Send EOF to finish input. Without `slc`, the reference
compiler accepts the same file list (omit `lib/prelude.sl`) followed by
`--extract _build/pal-fast/manacher.ml`.

## Algorithm and cost

At position `i`, even and odd centers each keep a rightmost palindrome `[L,R)`
and a map of previous radii. A radius `k` counts matching *pairs*, so the
current interval is `[i-k, i+extra+k)`, where `extra` is zero or one.
Inside `[L,R)`, the mirror is `L+R-i-extra` and the seed radius is the smaller
of its cached radius and `R-i-extra`. Expansion starts beyond that seed.

The index stores every cut of the input as a reversed prefix and a shared
suffix. Two trie lookups retrieve the lists at the seed boundaries; each
subsequent expansion compares their heads and advances in constant time.
No list prefix is copied or traversed to skip a seed. There are separate
radius maps and rightmost intervals for even and odd centers.

For each parity, a mirror radius shorter than the boundary permits no
successful expansion: its terminating mismatch reflects across the outer
palindrome. Otherwise successful expansion advances the rightmost boundary.
Consequently each parity has at most `n` successful expansions, plus one
terminating call per center. The two passes together make at most `4n`
expansion calls. Trie operations cost O(log n), giving **O(n log n) time**
with constant-cost element comparisons and machine-sized index arithmetic.
Persistent updates allocate O(n log n) nodes in total. The input conversion,
cut-index construction, expansion, and center scan use explicit `tail`
markers. Their runtime walks use constant stack; trie operations still use
O(log n) stack. Live algorithm data occupies O(n) space. Arbitrary-precision Nat operations add their bit costs. Running with
`--no-extern` uses unary source arithmetic and is not covered by this bound.

Numeric guards expose coordinate equalities and bounds to the proof checker.
For maps constructed by the scan, the Manacher invariant makes these guards
succeed whenever a seed is reused. The helpers also remain correct for
arbitrary supplied caches: an unavailable or unsuitable seed causes direct
expansion from radius zero. That general fallback does not have a linear
expansion guarantee for arbitrary external cache values.

## Proof

All certificates and proof computations are erased; the function does not
run the naive solver to certify its answer.

- `palindrome_lemmas.sl` proves list decomposition, reversal, range uniqueness,
  and reflection: a palindrome inside another palindrome appears reflected
  at the opposite location. It also connects witnesses to the specification.
- `palindrome_seed.sl` trims a cached palindrome, locates its reflected span,
  and proves that it supplies a common prefix of the two outward-facing
  lists. Unique cuts identify the runtime lists obtained from the trie with
  the proof's endpoints. These steps justify skipping the seed.
- `man-expand` produces `PalLcp`: the exact number of equal pairs, with a
  mismatch or exhausted list at its end. `fp-center-range` reconstructs a
  located palindrome for caching; `fp-center-witness` proves it occurs in
  the original input.
- `palindrome_centers.sl` bounds every palindrome by the exact radius at its
  center. The scan carries a maximum witness and an erased history of center bounds;
  `fp-centers-spec` builds the original `LongestPalindrome` certificate,
  including the chain excluding every longer length.

These are constructive SL proofs checked by both compilers, using the
prelude and original specification without new axioms or extern declarations.
Erased prefix and center histories preserve the certificates when expansion
and scanning advance their accumulators in tail position. Functional
correctness and the explicit tail-call markers are machine checked. The complexity argument above is
an algorithmic argument, not an SL cost proof.
