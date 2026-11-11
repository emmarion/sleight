# Higman's lemma in Sleight

This directory holds constructive proofs of Higman's lemma, written in
Sleight by Claude sessions: one for a two-letter alphabet, and one for
any fixed finite alphabet, which a macro writes out for each size k.
[NOTICE.md](NOTICE.md) credits the ideas they use.

## What is proved

`spec.sl` sets the goal `(goal many (Higman))`. A `Higman` holds a
factory. Given only the level `M` of a sequence, it returns a level `L`
and a search at `L`. Given a relation `G` and a sequence
`f : (Fn M (many (Nat) i) -> (many (List (Bool)) w) (erased (G i w) g))`,
the search returns indices `i < j`, two words `u` and `w` with `G i u`
and `G j w`, and a proof `(Emb u w)` that `u` is a subsequence of `w`.

A type holds no call (DESIGN.md §9), so the statement cannot name
`(f i)`. `G` ties each word to its index instead: when `G` is the graph
of `f`, `u` and `w` are `f`'s words at `i` and `j`. The search can get a
`G` proof only from `f`. The goal is `many`, so the search is a program that
can be run. On the sequences tried in this session, it found a good pair
in under a second.

The proof uses no axioms and no `native-compute`. It appears to rest only
on the compilers' type checking. `spec.sl` depends on the prelude alone.

## Checking

Build the compilers as the top-level [README.md](../README.md) says,
then, from the repository root:

```sh
higman/check.sh slc
higman/check.sh ref
```

Each prints `--goal proved: PASS`. In single runs on a cloud VM, each
took under a second. For k letters, see below.

## How the proof goes

Let `w0 = f 0`, of length `m`. A word `v` that does not embed `w0` has
the shape `d₁^e₁ c₁ d₂^e₂ c₂ … c_k d_{k+1}^e_{k+1}`, where `w0 = c₁…c_m`,
`k < m` and `dᵢ` is the letter other than `cᵢ` (`Av` in `words.sl`).
Two such words with exponent vectors `e ≤ e'`, compared pointwise and of
equal length, embed (`av-mono`). So the search reads `f 1, f 2, …`.
It stops when one of them embeds `w0`, or when the exponent vectors of
two of them are pointwise ordered, which is Dickson's lemma.

The Dickson search (`dickson.sl`) keeps the points not above any point
seen so far as a forest of boxes (`forest.sl`). Each coordinate of a box
is fixed or free. A new point lands in a leaf box, which is split into
the boxes that miss its upward closure (`Pieces` in `box.sl`), each with
one free coordinate fewer. If the point instead lies above a point
stored at a split node, the search has found its pair. The measure is
the vector counting leaves by their number of free coordinates, most
first (`measure.sl`). A split lowers it lexicographically, at the
position of the split leaf's degree.

`lexrun.sl` turns a step function that lowers such a vector into a
terminating loop. The vector's length is `m+1`, known only at run time,
and lexicographic order on vectors of every length reaches ω^ω. The loop
is one function with two `subterm` parameters. One is the number of
positions after the current one, which decreases when it runs the rest
of the vector. The other is the value at the current position, which
decreases when a step lowers that position. A step that lowers an
earlier position returns to the caller that owns it.

## Any finite alphabet

`kspec.sl` states `(HigmanK k)`: the same factory as `Higman`, over
words of naturals below `k`, the sequence also returning a proof
`(Letters k w)` that its word uses only those letters. `k3.sl` holds the
goal `(goal many (HigmanK 3))` behind `(def-higman 3)`, and so on;
`k2.sl` to `k5.sl` are here, and in this session k = 2 to 7 passed. From
the repository root:

```sh
higman/check.sh slc 3
higman/check.sh ref 3
```

Each took under two seconds in single runs on a cloud VM.

There is one proof per k, not one for every k. Schmitz and Schnoebelen
(NOTICE.md) bound bad sequences of words over k letters, with
primitive-recursive control, by functions at level ω^(k−1) of the fast
growing hierarchy, and as this session understands the literature that
bound is tight. A single proof for every k would then let a program
read k and compute at level ω^ω, which README.md's statement of
Sleight's strength, that it computes exactly the multiply recursive
functions, appears to rule out.

The search keeps a forest of boxes as before, now over words: a box is
a list of letters and blocks Γ*, Γ an alphabet held as a mask
(`sre.sl`), and a point in it is a parse of its word, one word per
block. A new word that does not lie above a split node's word, block by
block, lies in one of the boxes that replace one block Γ* by the words
of Γ* avoiding that block of the stored word, all of whose blocks have
alphabets one letter smaller (`Shapes`, `Pcs`). A leaf's rank counts its
blocks by alphabet size, most letters first (`kforest.sl`), and a split
lowers it lexicographically. The forest's measure is the multiset of
its leaves' ranks, held as a list of ranks and counts in decreasing
order (`dm.sl`). A split removes one rank and adds lower ones.

`dm-factory` turns a step that lowers such a multiset into a
terminating loop. Its frame for one rank of the list recurses on the
rank's k+1 entries and its count, all `subterm` parameters, so its
signature depends on k. `kgen.sl` writes it out: `def-higman` builds its
text for the given k, reads it into `Raw` with a small reader, and
splices it in, with `hk` and `kn` bound to k and k+1. `ksearch.sl`
holds the rest of the search, for whatever k is bound.
