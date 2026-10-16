# Slots as words

A plan for the Lean development in `lean/`. It covers `cell-same`,
at-matches on a union newtype, `slot-eq` and mutation, which a session
found to rest on one fact of the design that the Lean model lacks. The
reading of the design below is a session's, which the owner agreed to
in chat as the basis. The owner chose shape 1 (a heap in the full
semantics) and stage 1 landing on its own first; the details of each
stage are a session's proposals.

## The fact everything rests on

- DESIGN.md section 38: "At runtime, the value of a slot is a word,
  either a pointer or an immediate."
- Section 35: the word of `(slot-of x)` "is the word of `x`".
- Section 36: an entry written `at v` has "its target's word"; the
  writers listed there (a forwarding `let`, a newtype's destructure and
  construction, `coerce`, `share`, a `unique` `cell-write`, `at`
  returns and parameters, the `at` entries of a match, and others) are
  the only ways two slots become equal.

Read together: two entries whose slots canonicalize to one atom have
one word. These features use that at run time:

| Feature | What it relies on |
|---|---|
| at-matches (section 40), skipped at-function calls (section 39) | an `at` entry is read back from its target's word, so nothing dispatches |
| `cell-same` (section 68) | two cells at one slot are one block, so the `JMEq` holds |
| `slot-eq` (section 67) | compares two slots' words |
| placement: `(at)` before an argument, `placed-slot` (sections 37, 42) | the slot really holds that word |

## The Lean model today

`(Slot)` is a built-in type with one constructor, `vacant-slot`, so
every slot has the same value and "same slot" carries no information
at run time. The reader, not the core, decides which entry has which
slot; the core sees slot entries and checks `at` promises by canonical
identity. The full and stripped runs (`eval`, `RunS`) are value-only;
the machine run (`RunM`) has a heap with addresses and writes a cell
in place at `unique`, and `machine_sound` relates it to `eval`.

So a rule that concludes something about values from slot equality
cannot be proved. That is why, as far as a session can tell:

- An at-match on a union newtype with several real branches is refused
  by the core (`tests/at_match_union.sl`): the stripped run holds a
  newtype as its field and has nothing to choose a branch by, where
  the design reads the `at` entry back from its target.
- `cell-same` is not implemented, and the prelude leaves out the
  functions built on it.

The model also has something the design does not. `Prim.atomEq` proves
`Eq (Slot) a b` for any two slots, which `slot-self` and the reader's
slot copies (`lean/README.md`, slots item) use. It is sound only
because every slot has one value; with slots as words it would be
false, since `slot-eq` must be able to answer that two slots differ
and section 38 has slot facts come from forcing alone.

## Why a heap

A `unique` write alone does not seem to need one: uniqueness keeps the
change unobservable, which is the argument `machine_sound` already
makes for the machine's in-place writes. What needs locations is
identity: `cell-same`, reading an `at` entry back, and `slot-eq`. A
token per cell does not cover it, because an invocation `(u a ...)`
creates its value at `u` (section 37), so a constructed value's
identity is its cell's. Values that carry locations amount to a heap.

## Two shapes

1. **A heap in the full semantics.** `eval` gets addresses and a heap,
   as `RunM` has; a block's value is its address and its contents live
   in the heap; value typing (`VTys`) is about contents at a heap.
   The most faithful, and the largest change: `eval`, the stripped run,
   the machine and the proofs between them, and the value argument of
   `no_false`.
2. **`eval` stays value-level; the invariant is proved on `RunM`.**
   Smaller, but `cell-same` returns a typed `JMEq` that `eval` itself
   must produce, so `eval` would need some way to learn whether two
   cells are one, for example from `RunM` the way it takes the
   `world-do` oracle's answers. A session sees no clean version of this
   yet, and leans toward shape 1.

## The invariant

For live non-erased entries, slots that canonicalize to one atom have
one word. It would be proved once, at the semantics that has words,
and the features follow from it:

- an at-match: the run that dispatches may still dispatch; a run that
  cannot reads the `at` entry back from its target, and the invariant
  says the two agree;
- `cell-same`: one slot, so one block, so `JMRefl`;
- `slot-eq`: a comparison of words;
- mutation: a `unique` write changes a block's contents, not its
  identity; a `many` write makes a fresh block.

## Stages

1. The core tracks slots: each entry's slot is known to the core, which
   applies section 36's writers itself; slot equality is a forced fact,
   not an `Eq` proof. `Prim.atomEq` and the reader's slot copies go.
   Expected to be a refactor that keeps today's semantics.
2. Words and the invariant, in whichever shape is chosen.
3. At-matches on a union newtype (`tests/at_match_union.sl`).
4. `cell-same`, and the prelude functions built on it.
5. Mutation, as the design has it.

`slot-eq` is left out: the reference compilers refuse it too ("names
no primitive the compilers implement").

## Stage 1 in detail, as a session proposes it

Today (from a read of the code): the core has no notion of which entry
a slot belongs to. The reader mints a slot entry when one is first
needed (`slotM`, `Prim.atom`), records owner and slot in its own state
(`slots`, `links`, `renames`), and passes slots to the core as hidden
telescope entries (`Tm.fn`'s mask, `is` entries) and as `Chk.is`
checks; the core compares them by canonical identity. `Prim.atomEq`
proves any two slots equal, and `VTy.atom_inv` (Sound.lean) is the
lemma that makes that sound.

What section 35 asks is that `(slot-of x)` be "resolved by the binder
of `x`, never through the `is` rule of `x`". The core canonicalizes
with one map of rules over variables (`Ctx.σ`), which would rewrite
`x` inside a slot term, so a slot cannot simply be a term over `x`.

Two representations a session sees:

- **A. A slot term former.** A new `Tm` constructor for "the slot of
  this variable", typed `(Slot)`, erased exactly when the variable is.
  `Ctx` gets a second map, of slot facts, which canonicalization uses
  for slot terms and nothing else; `Ctx.σ` never rewrites inside one.
  A telescope entry carries its `at` target, which binds the slot fact
  as the entry is bound, in place of the hidden entries and `Tm.fn`'s
  mask. Section 36's writers become core rules that add slot facts.
  `Prim.atom`, `Prim.atomEq`, the reader's slot minting and the slot
  copies go; `slot-self` becomes a core statement adding the fact that
  `x`'s slot is `x`.
- **B. Automatic slot entries, as section 35 words it.** Every binding
  makes two entries, the variable and its slot, with the core keeping
  the pairing. Closer to the design's wording, but it doubles the
  entries every rule and proof indexes, and the slot entries still
  need rules kept apart from `is` rules.

A session leans toward A. Its cost is mostly mechanical: a new `Tm`
constructor reaches every structural function and lemma over terms.

In stage 1 a slot term still evaluates to `vacant-slot`'s value, so
the run semantics stay as they are and the slot facts are sound for
the same reason `Prim.atomEq` is today; stage 2 gives slots their
words.

## Cost, as a session estimates it

Larger than anything in `lean/` so far: stage 1 reworks the reader's
and the core's slot handling, and stage 2 threads an invariant through
the run proofs, in shape 1 after reworking `eval` itself.

## Where the work happens

The work is on the long-term branch `claude/slots`, with a sub-branch
per stage (`claude/slots-1-core`, and so on), merged into
`claude/slots` as each stage is done. The branch may fall behind
`main`'s results meanwhile, for example while stage 1 drops
`Prim.atomEq` and the slot copies; it returns to `main` once it is
back to the parity `main` had when the work began.
