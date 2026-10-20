# Sleight

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23361871.svg)](https://doi.org/10.5281/zenodo.23361871)

Sleight is a programming language with s-expression syntax, restricted
dependent types, a multiplicity on every binder (`erased`, `many` or
`unique`), and a termination check with no escape. Its proofs erase
before the code runs, a `unique` binder is the only reference to its
value, so the value can be updated in place, and the compiler checks
the performance claims a program makes, such as that a call is a tail
call or that a coercion costs nothing. [DESIGN.md](DESIGN.md) is the
specification; it gives the language three aims besides its design: to
match the dynamism of Kernel, John Shutt's Lisp dialect, while still
compiling cleanly with static types; to support LLMs writing code in
it; and to let a certified program be written so that it could run
fast.

This file was written by a Claude session at the owner's request. Where
it and DESIGN.md disagree, DESIGN.md is right.

## An example

[`tests/tutorial_vec.sl`](tests/tutorial_vec.sl), a test in this repository:

```scheme
(def-adts $ (Vec : (Type A) ((Nat) n) -> Type)
  enum
  (many VNil : (erased Type A) -> (Vec A (Zero)))
  (many VCons : (erased Type A) (erased (Nat) n) (many A head) (many (Vec A n) rest)
     -> (Vec A (Succ n))))

(def-fns _ $ (many vhead : (erased Type A) (erased (Nat) n) (many (Vec A (Succ n)) v) ->
    (many A x))
  (let-match many v (VCons _ _ hd _))
  hd)

(vhead _ _ $ VCons _ _ 10 $ VCons _ _ 20 $ VNil (Nat))
```

It prints `10`. `Vec` is a vector indexed by its length. `vhead` takes
a vector whose length is `(Succ n)`; `VNil` would need `(Succ n)` to
equal `(Zero)`, two distinct constructors of one type, so that case is
refuted and needs no branch (DESIGN.md §7, §8, §27). The index `n` is
`erased`, so a `VCons` cell holds its element and its tail and no
length (§14). Every binder states its multiplicity; nothing is inferred
from usage (§13). [TUTORIAL.md](TUTORIAL.md) continues from here, each
of its programs a test.

## What is here

Three implementations, and proofs about one of them.

| | Written in | Role |
|---|---|---|
| The reference interpreter and compiler, [`lib/`](lib/) and [`bin/`](bin/) | OCaml | defines the behavior; interprets a program, or extracts it to standalone OCaml |
| slc, [`self/`](self/) | Sleight | compiles Sleight to OCaml; bootstrapped through the reference, it compiles itself and its output compiles itself again to identical output |
| The Lean model, [`lean/`](lean/) | Lean 4 | a checker and evaluator for a fragment of the language, with machine-checked theorems about them |

Over a thousand programs under [`tests/`](tests/) are the shared test
suite: `dune test` runs each through the reference, interpreted and
extracted, and [`self/bootstrap.sh`](self/bootstrap.sh) compiles each
with slc and requires it to behave as the reference does, so a
disagreement is a bug in one of them. The
Lean model's theorems say that the evaluator is total with no fuel,
that a checked program runs to a value of its type (`checked_runs`),
that no checked program proves `False` (`no_false`), that skipping the
erased code does not change the result (`eval_sound`), and that running
with in-place updates agrees with that (`machine_main`). They rest on
Lean's own three axioms and no `sorry`. [`lean/README.md`](lean/README.md)
says what the fragment leaves out, and [SOUNDNESS.md](SOUNDNESS.md)
argues the rest of the language, in particular `Type : Type` with no
positivity requirement (§10), does not undo this.

Certified programs written in the language: [`pal/`](pal/), the longest
palindrome by Manacher's algorithm; [`heapsort/`](heapsort/), an
in-place heap sort certified against [`agent/tasks/heapsort-fast/spec.sl`](agent/tasks/heapsort-fast/spec.sl)
and timed against OCaml and Lean; [`msort/`](msort/), an in-place merge
sort on unique lists certified against [`msort/spec.sl`](msort/spec.sl).
[`mini/`](mini/) writes the semantics of the fragment of
[MINIMAL.md](MINIMAL.md) as relations in the language itself.

[`agent/`](agent/) runs LLM agents on Sleight programming tasks over many
sessions; the heap sort above was written that way. The October 14,
2026 talk ([`talk/slides.md`](talk/slides.md), PDF at
https://doi.org/10.5281/zenodo.23367392) reports how the models did.

## What might be new

The talk lists these as what might be new. The list is the talk's; this
repository has not checked it against the literature.

- First-class levels for termination, with `Type : Type` and no
  positivity check.
- Stack depth known at compile time, even through function pointers.
- Erasure and uniqueness on every binder, with location as a separate
  fact (`at`).
- Proofs about overwritten memory.
- Kernel-style special forms, compiled and dependently typed.
- Performance claims checked at compile time.

## Trying it

On Debian or Ubuntu:

```sh
apt-get install -y ocaml ocaml-dune ocaml-findlib libzarith-ocaml-dev python3 time
dune build
dune exec bin/main.exe -- tests/tutorial_color.sl
```

Then [TUTORIAL.md](TUTORIAL.md). [MANUAL.md](MANUAL.md) has every
command line, flag and test directive, the format of the compilers'
messages, how a program runs, and the layout of the source. Sleight
files end in `.sl`; GitHub shows them as Scheme.

## Reading

- [DESIGN.md](DESIGN.md), the specification, cited by section number
  from everything else here. [OPEN.md](OPEN.md) lists the questions it
  does not answer; [SPEC-REVIEW.md](SPEC-REVIEW.md) the open points a
  review found in it.
- [EXAMPLES.md](EXAMPLES.md), the tests worth reading first.
- [SOUNDNESS.md](SOUNDNESS.md), why `Type : Type` with no positivity
  requirement appears sound here, and what that assumes.
- [ASSUMPTIONS.md](ASSUMPTIONS.md), the choices the implementations make
  where the specification is silent. [BUGS.md](BUGS.md), defects found
  in them. [WARNINGS.md](WARNINGS.md), the warnings they emit.
  [TOOLING-WISHLIST.md](TOOLING-WISHLIST.md), friction met while writing
  programs. [INTERNALS.md](INTERNALS.md), the contract between the
  prelude and the compilers.
- [`lib/prelude.sl`](lib/prelude.sl), the prelude, and [`std/`](std/),
  the source libraries.

## How this repository is made

One person designs the language; LLM agents, at the owner's request,
write the implementations, the proofs and the notes. DESIGN.md holds
only wording the owner confirmed, and every other file opens by saying
who wrote it and how far to trust it: a claim a file makes that its
tests or proofs do not make is a mistake in that file. [CLAUDE.md](CLAUDE.md)
is the working agreement the sessions follow.

## Citing and license

[CITATION.cff](CITATION.cff) has the citation; the code is at
https://doi.org/10.5281/zenodo.23361871 and the talk's slides at
https://doi.org/10.5281/zenodo.23367392. Apache-2.0, see [LICENSE](LICENSE).
