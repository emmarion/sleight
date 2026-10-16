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
at run time. On this branch the core tracks which entry is at which
slot (stage 1, below) and checks `at` promises by canonical identity
of slots; on `main` the reader decides it and the core sees slot
entries. The full and stripped runs (`eval`, `RunS`) are value-only;
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
`Eq (Slot) a b` for any two slots on `main`, where `slot-self` and the
reader's slot copies use it; on this branch it is narrowed to
`placed-slot`'s equation (`Prim.placedSlot`). It is sound only
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
  Section 36's writers become core rules that add slot facts.
  `Prim.atom`, `Prim.atomEq`, the reader's slot minting and the slot
  copies go; `slot-self` becomes a core statement adding the fact that
  `x`'s slot is `x`. A telescope entry written `at v` keeps today's
  encoding, a hidden erased `is` entry before it naming `v`'s slot and
  flagged in `Tm.fn`'s mask, which the core now reads: opening the
  telescope records that the entry's slot is the hidden entry, and a
  call checks each hidden argument against the following argument's
  slot. The mask also records which entries are written `at`, which
  section 36 reads from the signature as written. The owner accepted
  this encoding on the condition that it allows complete consistency
  with the design; a session found nothing in sections 35 and 36 that
  it cannot express, and any such case is to be raised rather than
  worked around.
- **B. Automatic slot entries, as section 35 words it.** Every binding
  makes two entries, the variable and its slot, with the core keeping
  the pairing. Closer to the design's wording, but it doubles the
  entries every rule and proof indexes, and the slot entries still
  need rules kept apart from `is` rules.

The owner chose A. As a session refines it: a slot is a second sort
of variable, `Tm.sfv i` (the slot of free variable `i`) and `Tm.sbv k`
(the slot of bound variable `k`), rather than a former applied to a
term. `Tm.subst`, and so canonicalization by `is` rules, rewrites only
`fv`, which keeps slots out of reach of `is` rules; slot facts are a
second substitution, over `sfv`, that canonicalization also applies.
Instantiating a telescope maps `sbv k` to the slot of the argument:
`sfv j` for `fv j`, and at run time the value's slot. So no value is
ever inside a slot term, and `canonBy_sound` keeps its shape with a
second hypothesis for slot facts. The cost is mostly mechanical: two
new `Tm` constructors reach every structural function and lemma over
terms.

Progress on stage 1, on `claude/slots-1-core`:

- Done, in the core: `sfv`/`sbv`, typed `(Slot)` and run-time exactly
  when their entry is; slot facts in `Ctx` (`ς`), applied by
  canonicalization and never reached by `is` rules. Equating two slots
  is a union: the old root is pointed at the new slot value and the
  `ς` and `σ` values that mention it are rewritten (`Ctx.withSlot`,
  `Ctx.bindSlot`), so canonicalization stays one pass. The writers of
  section 36 as a session reads them:
  - the hidden `at` entry, after the entry it belongs to and flagged
    `sl`, records that entry's slot, in telescopes the checker opens
    (`TeleOK` included) and in calls; the checker requires each such
    hidden argument or result to be the slot of the variable before it;
  - a forwarding `Prim.tm`, `coerce`, `place` or `unplace`, and an
    application of a newtype constructor (through `Prog.unwrap`), put
    their entry at their source's slot; `vacant-slot` is its own slot;
  - a destructure of a newtype puts its non-erased field at the
    scrutinee (`Ctx.ntSlot`, in `Ctx.branch`);
  - a pending mark (`reuse` or `write` at `unique` on a variable, or
    `cellOf`) puts the next constructor or `axm` entry at the mark's
    target, as the machine's pending mark does (`Ctx.pd`,
    `Ctx.markPd`); `Chk.slotAt` does the same where the machine has no
    pending mark: the cell binder of a `many` or erased destructure, and
    an invocation that is not at `unique` and, at `many`, skips every
    store (section 37; the owner confirmed that such a `many`
    invocation is at the cell);
  - `world-do`'s world result is at its world argument
    (`Ctx.pushWdo`);
  - `slot-self` (`Chk.slf`);
  - forcing in a match branch and in `open-adt`: after unification,
    the pairs left over that involve a slot are made equal
    (`Ctx.forceSlots`, `Ctx.opnCtx`);
  - the delegate annotation, when the block is pushed (`Ctx.deleSlots`).
- Done, in the reader: slots are core terms (`(slot-of x)` is
  `sfv x`); slot minting, the slot copies, the retry for them and the
  `fresh-slot` and `slot-eq` forms are gone; a lifted constructor
  signature abstracts the slots it mentions with the variables.
  `prove-predates` takes `(slot-of x)`, or an entry whose value is the
  slot of an entry older than the level.
- `Prim.atom` is gone. `Prim.atomEq` is now `Prim.placedSlot`, which
  proves only that a box's slot is the slot its `Placed` type names
  (`Ctx.placedAt`); in stage 1 that is sound because every slot has
  one value, and stage 2 is to justify it from where a placed value is.
- Not yet:
  - the machine side of the `many` invocation that skips every store:
    the core records it at the cell, the machine builds a fresh block;
    stage 2 is to make the machine reuse the cell's block.

In stage 1 a slot term still evaluates to `vacant-slot`'s value, so
the run semantics stay as they are and the slot facts are sound for
the same reason `Prim.atomEq` is today; stage 2 gives slots their
words.

## Stage 2: what it must deliver, and an open question

A session's reading of what stages 3 and 4 need from stage 2:

- `cell-same` (section 68) takes two cells at `many` whose slots are
  equal and yields `JMEq T1 u1 T2 u2`. Today a cell evaluates to a
  token (`Prim.axm`), so the two values agree, but the two types need
  not: `Ti` is `(Cell Ci ...)`, and nothing in the value semantics says
  that two cells at one slot have one constructor and one field slots.
  Stage 2 has to make "at one slot" mean "one block", so the types
  agree.
- An at-match on a union newtype (section 40) has its `at` entries
  read back from their targets' words rather than chosen by dispatch.

The difficulty a session sees: "one slot, one block" holds only of
live entries. A unique `cell-write` puts its result at its input's
slot, and the input, consumed, held the block's old contents; a
`many` cell is never written in place, but a cell at `many` and one at
`unique` at the same slot cannot both be live only because of the uses
discipline (section 15), not because of typing. In the Lean model the
uses discipline is checked by the uses pass (`Minimal/Uses.lean`) and
relied on only by the machine proofs (`MachineRun.lean`,
`MachineSound.lean`, `MachineAsm.lean`, with their ownership frames);
`eval`'s soundness (`Sound.lean`) is proved for every typing derivation,
uses or not.

So a session sees two ways to carry out shape 1, and would like the
owner to choose before the work starts:

- **2a. `eval` gets a heap, and its soundness takes on uses.** Values
  in the environment become words, constructed values are blocks, a
  cell is its block's address, a slot term evaluates to its entry's
  word, and a unique write updates a block in place. `EnvOK` then
  holds only for live entries, so `Sound.lean` takes the uses pass's
  output as a hypothesis and inherits much of the machine proofs'
  ownership reasoning; the machine proofs would shrink, since `eval`
  and `RunM` would then both have heaps.
- **2b. `eval` gets a heap of versions and stays uses-free; `cell-same`
  is proved where uses are known.** A unique write makes a new version
  of a block at the same address, so every old entry keeps its value
  and `EnvOK` keeps holding for all entries; a slot is an address. The
  facts that need liveness, such as two `many` cells at one slot being
  one version, are proved alongside the machine proofs, which already
  carry ownership, and `eval`'s result for `cell-same` is justified
  there.

In either, `Prog.build` of a slot term gives its entry's word instead
of `vacant-slot`, and the machine's `many` invocation that skips every
store returns the cell's block, as the owner confirmed (section 37).
Both are larger than stage 1; 2a moves the most proof.

The owner chose 2a, to be done on its own branch, `claude/slots-2a`.
The steps below are a session's proposal for carrying it out:

1. A heap run beside `eval`, `evalH`, with words in its environment and
   blocks in its heap, and no write in place yet: every constructed
   value is a fresh block, a match decodes its scrutinee, and a slot
   term still evaluates to `vacant-slot`. A theorem that decoding
   `evalH`'s results gives `eval`'s, under the heap's growth only.
   Nothing else changes, so `main`'s results stay.
2. Writes in place: a `unique` invocation, `cell-write` and reuse write
   their cell's block, as `RunM` does. The theorem of step 1 then holds
   only for live entries, and takes the uses pass's result as a
   hypothesis, with ownership frames carried over from the machine
   proofs.
3. Words for slots: a slot term evaluates to its entry's word, and the
   invariant (entries whose slots canonicalize to one term have one
   word) is proved with the writers, for live entries.
4. Typing soundness moves to `evalH`: `checked_runs` and `no_false`
   become statements about `evalH`, with the uses pass's result as a
   hypothesis, and `eval` stays only as far as the stripped run and
   the machine proofs still need it. The machine's `many` invocation
   that skips every store returns the cell's block.
5. Stages 3 and 4 then build on step 3's invariant.

Step 1 is in place: `Minimal/EvalH.lean` defines `evalH`, and
`Minimal/EvalHSound.lean` proves `evalH_sim` and `evalH_main` (decoding
`evalH`'s result gives `eval`'s, error for error, with the heap only
growing). Both take as hypotheses that the program holds no `ptr` term
(`Prog.PtrFree`, `Core.ptrFree`); that the reader's output satisfies
them is believed but not proved.

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
