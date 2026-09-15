# Performance notes: slc and the reference

Notes from a session the owner asked to investigate the performance of
`slc`, using slc itself as the measuring stick. Everything here is that
session's measurement and reading, on one machine on one day; nothing
here is a design decision, and section 6 is a list of proposals for the
owner, not a plan. Times are wall-clock, single runs unless a range is
given, and vary by a few percent between runs.

## 1. Method

The measuring stick is slc compiling its own sources (the prelude and
the nine `self/*.sl` files, about ten thousand lines) as a native binary
extracted by the reference. The original binary, built from the sources
before any change, was kept and run on every later version of the
sources, so that a speedup in the compiler could be told apart from a
speedup in the code it emits: the pinned compiler measures the sources'
own cost, the new compiler built by the pinned one measures the
algorithmic change, and the new compiler built by itself measures both.

Every change was checked the same way: the reference elaborates and
extracts the sources (so the reference's type checker is the arbiter of
the proofs), `self/bootstrap.sh` compiles every test with the result and
compares against the reference (175 programs run, 103 refused with the
expected message), slc compiled by slc compiles slc again to the same
bytes (the fixpoint), and, for the changes to slc's own algorithms, the
pinned, the previous and the new compiler emit byte-identical OCaml for
the new sources. `dune test` was run after each change to `lib/`.

Profiles are `perf record -e cpu-clock` on the native binaries, flat and
with DWARF call graphs; counts come from a copy of the extracted OCaml
with counters wrapped around the functions in question.

## 2. Results

| Measurement | Before | After |
|---|---|---|
| slc compiling its own sources, native | 3.4s | 0.7s |
| Reference elaborating and extracting slc's sources | 30.9s | 3.7s to 4.7s |
| Reference running slc under interpretation on one small test | 39.5s | 9.5s |
| `self/bootstrap.sh`, whole script | about 110s | about 60s |
| Peak memory of the self-compile | 41 MB | 39 MB |

The four commits, in order, with the self-compile after each:

1. The fact table's rules list made erased: 3.4s to 2.2s.
2. The objects in scope indexed by head and constructor: 2.2s to 0.85s.
3. The reference's scope given a name map and an object list: slc
   unchanged; the reference 30.9s to 4.7s.
4. Both emitters return the scrutinee where every arm rebuilds its own
   constructor: 0.85s to 0.7s.

## 3. What the profiles showed

**slc.** Before any change, about sixty percent of the self-compile was
in the fact table: the trie lookup `facts-lookup` 37%, `append-rule`
11%, `find-rule` 9.5%, `canon` and its helpers 6%, and a sixth of the
run in the garbage collector, mostly from the same functions. The call
graph put nearly all of the trie lookups under four functions:
`listed` (section 19's rule that two atoms conflict when one Matchable
in scope lists both), `matchable-heading` (the Matchable a type
constructor heads, read for both atoms of a refutation),
`find-matchable-in` and `agree` (a match's Matchable and the ambiguity
check). Each walked every object in scope and canonicalized each
object's whole Matchable type. Counted: 3.4 thousand calls of `listed`,
6.8 thousand of `matchable-heading`, 2.2 thousand each of the other
two, over objects lists of up to 199 entries; 2.0 million of the 2.15
million `type-of` calls, and so about 12 million of the 12.9 million
trie lookups, came from these scans.

The rules list was the other cost. It exists so that canonicalization
can terminate by proof: a chase follows a rule and continues among the
rules appended after it, the suffix being a subterm. `append-rule`
copied the list on every binding (60 thousand appends, 28.6 million
cells, the list reaching 1153 rules) and `find-rule` scanned it for the
key's rule (98 thousand scans, 40.5 million cells), though the rule's
term was already in the trie.

**The reference.** Elaborating slc's sources put 33% in `Map.find`, 13%
in `caml_apply2` and 10% in `Int.compare`, which the call graph traced
to `Env.lookup`, called from `special_of` for every head and `var` for
every name: it found a name by walking the whole scope list, reading
the entry map once per entry. Section 19's scans (`listed`,
`matchable_of`, `matchables`, `newtype_of`) walked the same list,
canonicalizing every entry's type, not only the objects'.

## 4. The changes

**The rules list is erased** (`self/core.sl`, commit 1). The chase
reads the rule's term from the trie's `LRuled`; `find-rule` became an
erased function that follows the `MemRule` proof to the suffix after
the rule, returning the same `Prefix`, `Ord`, `Guard` and `Subterm`
evidence as before; `canon` and its family take the suffix as a
`subterm erased` parameter; the table's list and `append-rule` are
erased. The proofs are unchanged in substance, the reference accepts
them, and the compiled compiler no longer builds or walks the list.
The session's reading is that DESIGN.md's permission for subterm
decrease through an erased argument (section 7) was always enough here
and the value-level list was a choice of the earlier session.

**Objects indexed by raw head and constructor** (`self/core.sl`,
`self/elab.sl`, commit 2). `Objects` holds the list beside two id-maps,
from a declared head and from a declared constructor to the objects
whose Matchable type names it; the four functions read their candidates
from the maps and run the same predicates in the order the scan met
them. Why the session reads this as exact: an object's canonical type
differs from its declared one only through a rule on an id the declared
type mentions, so the table carries a `dirty` flag, set when a rule is
minted on an indexed id (`rule-into`, told by its callers in `unify`)
or when an object registers with one already ruled, and while it is set
the four fall back to the full scan. The flag is never set while slc
compiles itself, and the candidate lists total a few thousand entries
where the scans visited two million. `find-newtype` and
`find-coercible`, rarely called, still scan. This argument is the
session's and not machine-checked; a test that sets the flag would be
worth having (section 7).

**The reference's scope is a record** (`lib/env.ml`, `lib/elab.ml`,
commit 3): the id list, the innermost entry of each name, and the
entries a Matchable or Newtype search may find, which the session took
to be those typed by a Matchable, a Newtype or a variable (a variable's
type may be ruled to a Matchable later, so it stays in the set and the
scans read the same entries as before). `bind` pushes onto all three;
every place that restores an outer scope wholesale is unchanged, which
is what keeps the three in step. The extraction of slc is byte for byte
what the unchanged reference produced.

**Identity re-matches** (`lib/extract.ml`, `self/emit.sl`, commit 4).
A match on a plain type, with no `else`, whose every arm rebuilds the
arm's own constructor from its fields in order, emits the scrutinee.
This is the shape a GADT-indexed result takes when a recursive call
returns it under different indices: `facts-lookup` and `idmap-get` did
it at every level of the trie, allocating a copy per level. Hand
patching the nine such matches in the extracted slc gave 0.89s to
0.71s, which the emitter change reproduces. 22 arms of that shape
remain in slc's output, in matches where only some arms rebuild.

## 5. What remains, at 0.7s

The flat profile is spread out now: the trie lookup 18%, `idmap-get`
11% (from `name-of`, `has-meta` and `env-keyed`), the garbage collector
about 30% in total, name maps 3%, the reader 9% of the stack,
`show-term` and `name-of` 5% (messages built for contradictions that
are the expected outcome of refuting a branch), and the output rope's
`flatten`, `append` and `leaves` about 7%. Nothing above 20%.

## 6. Proposals, for the owner

None of these are applied. They are ordered by the session's estimate
of value against risk.

1. **GC parameters for extracted programs** (runner). The minor heap
   default is small for these allocation patterns: before the changes
   `OCAMLRUNPARAM=s=4M` took the self-compile from 3.5s to 2.9s, and
   after them `s=4M,o=200` takes it from 0.93s to 0.79s; the reference
   gains about 10% from `s=4M,i=8M`. Where to set it is the owner's:
   a `Gc.set` in the emitted preamble would have to be written by both
   back-ends, since `lib/extract.ml` is the emitter's specification,
   or `self/bootstrap.sh` could export the variable, or it could be left
   to whoever runs the binary.

2. **More of the constructor reuse in the emitters** (extraction). Where
   only some arms rebuild, a `let`-bound scrutinee returned from those
   arms would cover the remaining 22; the untagged case, a tuple
   unpacked and repacked, is the same shape. DESIGN.md section 38's
   `coerce` with `coercible-ctor` is the source-level way to say the
   same thing at zero cost; a reader may prefer the emitter to find it.

3. **The Matchable record as a keyed map** (design, later). Section
   19's rule as written costs a scan of ambient scope; the index above
   is exact under a flag. proposals/matchable-newtype-opening.md's
   assertion at open time makes the record of opened objects a map by
   canonical head and constructor as a matter of definition, with the
   merge of two groups standing where the flag stands now; the index
   was shaped so it can become that record.

4. **Termination evidence should be erased** (a pattern, not a change).
   The rules list shows the cost of carrying a measure at runtime when
   the language allows `subterm erased`. `self/README.md` says the
   canonicalization proofs are all erased; after commit 1 that is true
   of the list too. The interpreter's and the printer's `Nat` fuel are
   the remaining value-level measures, by that README's own account.

5. **Bootstrap parallelism** (script). Of the sixty seconds,
   `ocamlopt` on 250 test programs is now most; the loop is
   embarrassingly parallel and a `-P` over the tests would cut the
   script to the reference's part.

6. **The reference's remaining costs** (`lib/`). `canon` reads the fact
   map once per variable (`Map.find` 21%); `special_of` canonicalizes
   the head's type on every form where a comparison of the raw fact
   would refuse most heads first; heap growth to 285 MB shows as
   kernel page clearing (18%), which the session did not trace. The
   same head-and-constructor index as slc's would apply to its scans if
   they ever matter again.

7. **FFI** (small, measured only by the profile). The `Half` view runs
   through an identity call and a template test at every trie level;
   the tries are about seventeen levels deep for slc's ids, so a
   lookup is seventeen such steps. An extern id-map would be the large
   change and would alter the erasure story of the proofs over the
   tries; the session does not recommend it on these numbers.
   `str-cat` copies on every concatenation (`append`, 2.3%), which the
   output rope already mostly avoids.

## 7. Caveats and open items

- The exactness arguments in section 4 are the session's; DESIGN.md's
  semantics are the arbiter, and the reference is the checked path.
- `tests/matchable_alias_branch.sl` is the one test that sets the
  `dirty` flag: a branch equates two declared types of one shape and
  their Matchables, and a match inside it finds the Matchable through
  the alias. Counted with an instrumented build, five queries there are
  answered by the fallback scan; slc's own compile never takes it, so
  the fallback is otherwise unexercised.
- slc and the reference already differed, before this session, on one
  corner the index touches: an object whose declared type is a
  variable later ruled to a Matchable type is found by the reference's
  scan and never registered as an object by slc. Recorded, not
  resolved.
- The profiles are of one input, slc's own sources; other programs
  spend their time differently, and the tests are too small to measure.
