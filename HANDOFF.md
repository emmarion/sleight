# Handoff: per-shape extraction, then the slc emitter port

Written by a Claude session for the next one, on branch
`claude/lean-coq-sl-proof-compare-azv36i`. The decisions below are the
owner's, made in chat; the readings of the code and the numbers are this
session's, checked where it says so. As elsewhere in this repo, a claim
the tests do not make is a mistake in this file.

## The task, in order

1. **Move `lib/extract.ml` to one OCaml type per *shape* of non-erased
   ADT** (the owner's choice, over keeping one type per ADT).
2. **Then port `self/emit.sl` to the reference scheme** so it agrees with
   `lib/extract.ml`: per-shape variant types with `Obj.t` fields, direct
   curried closures, bare zarith values. The owner's standing decision,
   quoted in chat: "the reference extractor is then the spec for slc's
   emitter, the two back-ends are meant to agree anyway, and slc reaches
   whatever the reference reaches. The typed-output property is gone."
   Doing 1 before 2 is what avoids porting slc twice.

## Decisions already in force (do not relitigate)

- **Interpretation is the checked path; extraction is the opted-in
  performance path.** `lib/eval.ml` raises on a reached absurd or a
  missing branch. Extracted matches elide the arms the elaborator
  refuted and emit no default; a wrong refutation would misdispatch
  silently there. Recorded in ASSUMPTIONS 63.
- **DESIGN.md section 38's representation paragraph** now states the
  tagged and untagged field-less cases apart (commit `f80d1ff`, the
  owner's confirmed wording). Any further DESIGN.md edit needs the exact
  wording confirmed first (CLAUDE.md rule 12).
- **`Value.matching` carries `live`**: the discriminants of a match's
  real branches plus the constructors its `else` stands for (section
  12: those whose forced unification did not contradict). The
  interpreter ignores it; the extractor keys its narrowing on it.

## What landed this session (all on the branch, all pushed)

| commit | change | gate |
|---|---|---|
| `2984516` | `heap.sl` `double-le-inv` as one call to its sibling (−9); `base.sl` `char-zero` as `#\x00` (−3) | bootstrap |
| `ce6e519` | `core.sl` `sp-eq` compares inside the band the tag selects; removes a latent collision two `ExprK` constructors away (−3) | 46×46 differential + bootstrap |
| `1cb992c` | `extract.ml`: refuted arms elided via phantom-index GADT copies; dead catch-alls dropped | `dune test` + bootstrap |
| `9952195` | `live` on `Value.matching`; narrowing also when an `else` is present | `dune test` + bootstrap |
| `e259b62` | ASSUMPTIONS 63 updated | docs |
| `f80d1ff` | DESIGN.md section 38 wording | docs |

Gates at the last run: `dune test` 249 tests, 0 failures (each test
extracted and compared with the interpreter); `self/bootstrap.sh` 151
matched, 98 refused with the expected message, 0 failed, fixpoint
`slc2.ml == slc3.ml`. Bootstrap takes about 3m15s; `dune test` about
3m. `dune exec bin/main.exe -- self/base.sl self/heap.sl self/reader.sl
self/core.sl self/eval.sl self/elab.sl <file>` elaborates the compiler
sources in ~22s, useful as a fast check before the gates.

## Step 1: per-shape types in `lib/extract.ml`

**Shape.** Section 38 defines representation by shape and nothing
finer: whether the type is tagged (an enum with more than one
non-phantom constructor), and the sequence of `many`-field arities of
its non-phantom constructors in declaration order. Extern types keep
their own OCaml types (`Z.t`, `Ffi_core.slice`) and do not merge.
Untagged types are their one constructor's tuple (or `unit`). The key
must be over non-phantom constructors only, matching the runtime tag
(`lib/elab.ml` `tagged`, line ~137; `lib/value.ml` `construct`).

**Numbers** (this session, from `_build/self/slc.ml`, the reference
extraction of slc): 178 ADT type declarations collapse to 47 shapes, 36
tagged; 42 of the 178 share the two-constant shape (`K | K`), 17 share
three constants, 7 share `K | K of Obj.t`, 5 share `K | K of Obj.t *
Obj.t`. Narrowing copies then become per (shape, live set) rather than
per (ADT, live set).

**Runtime layout does not change.** OCaml lays a variant out by
constant-vs-block and position among the constants or among the
blocks, in declaration order; every type of one shape has the same
layout by definition, so only the OCaml type name at a coercion site
changes and values stay bit-identical. `coerce` becomes an identity at
the OCaml type level rather than a same-layout cast. The differential
test and the fixpoint are what would catch drift.

**Where the code is** (`lib/extract.ml`, names rather than lines since
lines moved this session):
- `type_name cx` (`named cx "t"`) and `con`/`des` (`numbered cx`) are
  per ADT today; they need to become per shape, with a shape→name table
  on `cx` (the record is `type cx = { ... }` near the top; `collect`
  builds it, search `shows = ref []`).
- `let types cx` renders `type tN = ...` declarations and the `con_N`/
  `des_N` functions; `fields_type` there is the per-constructor arity.
- `ctor c` gives the emitted constructor name; under per-shape it must
  be positional within the shape (`K0`, `K1`, ...) so two ADTs of one
  shape share constructors. The descriptor records (`cname`) keep the
  SL name for printing and must not change.
- `narrow cx a present` and `let narrows cx` (added in `1cb992c`)
  build the phantom-index copies; key them by shape.
- The `V.CMatch` case (`| Tagged ->` branch) coerces the scrutinee to
  `type_name cx a` or `yes <narrow>`; that becomes the shape's name.
- `emit`'s final `concat` fixes file order: preamble, `type yes = Yes_
  and no = No_`, `narrows cx`, `types cx`, driver, shows, bodies. The
  narrow copies come *before* the base types deliberately, so base
  constructors are the last definition and win default name
  resolution; only an annotated match picks a narrowed one.

**Gotchas met this session, all verified:**
- A copy that changes a constant constructor's arity (e.g. `C of void`
  to refute it) renumbers the constants after it; `Obj.magic` then
  dispatches wrong, and it segfaulted. Keep every constructor's arity.
- OCaml does not use an empty payload type for exhaustiveness on its
  own; GADT index refutation it does use. That is why the copies are
  phantom-indexed rather than `void`-payloaded.
- The extracted preamble is `[@@@warning "-a"]`, so a non-exhaustive
  match is silent at compile time; it raises `Match_failure` at run
  time.
- A match with every branch refuted reaches the extractor as
  `V.CAbsurd`, not a `CMatch` with no branches (ASSUMPTIONS 35); the
  `_ -> .` path in the extractor is insurance.
- A top-level call is evaluated at elaboration and embedded as data, so
  emitted function bodies are not exercised by it; to run one at
  runtime end the file with a thunk (`(def-fns _ $ many main : ->
  (many (Nat) r) ...)` then `main`).
- `dune exec` takes the build lock; while a gate runs in the background
  use `_build/default/bin/main.exe` directly.

## Step 2: port `self/emit.sl` to the reference scheme

`self/README.md`'s "Choices" section documents the current scheme:
one uniform `type v = Tag of int * v list | Tup of v list | Nat of Z.t
| Str of slice | Fn of (v list -> v) | ...`, every call `app f [args]`,
matches on `Tag (i, fields)` ending in `| _ -> absurd ()` (728 of them
in `slc3.ml`). That section must be rewritten when the scheme changes.

Files: `self/emit.sl` (529 lines, the emitter), `self/runtime.ml` (56,
the runtime every compiled program starts with; `type v`, `app`,
`tuple`, `untuple`, `absurd`, `run_io`), `self/header.sl` (generated
from `runtime.ml` + `lib/ffi_core.ml` by `self/gen_header.py`;
regenerate after editing either; `bootstrap.sh` does so
unconditionally). `self/core.sl` holds the post-erasure `Code` type,
whose match node needs a `live` field mirroring `Value.matching`;
`self/elab.sl` must populate it the way `lib/elab.ml` does (search
`V.CMatch` there: `real` plus `reachable` for a match, the single
constructor for a let-match); `self/eval.sl` ignores it.

Under per-shape the port is smaller than per-ADT would have been: 47
types rather than 178, and closer in spirit to the uniform type slc
has now. Direct curried closures and bare zarith are independent of
the type scheme and come with the reference scheme regardless.

Validation is `self/bootstrap.sh`: the 151/98 comparison against the
interpreter and the fixpoint. Expect `slc3.ml`'s `| _ -> absurd ()`
count to fall to the guards on the first-class (`Held`) and extern
paths, as the reference's did (1094 → 101).

## Noted this session, not acted on

Each is a finding with evidence, left for the owner; none is decided.
- `self/core.sl:2756-2757` `nat-adt`/`str-adt`: unused by grep.
- `self/core.sl:2277-2283`: the seven built-in ids are predicted from
  `make-builtins`'s bind order, correlated by a comment only;
  `coercible-id` feeds every `bind`, so a misalignment misclassifies
  rather than fails. Having `make-builtins` return the ids fixes it.
- `self/runtime.ml` hard-codes the prelude's `IO`/`Maybe`/`Result`/
  `List` constructor indices; `lib/extract.ml` reads names; nothing in
  `self/` checks the coupling. A name-order check in `emit.sl` would.
- The FFI's value-level conventions (`Bin`'s bijective digits, `Nat`'s
  Peano shape, `String`'s cons shape, `Rope`'s flatten) are duplicated
  by `self/eval.sl:47-82`, `lib/ffi_core.ml` and the prelude; a few
  top-level `let` + `comptime-match` lines pin them, with a wrapper
  enum whose payload is `many` so the mismatch message names both
  values. Verified pattern, not added.
- DESIGN.md section 39's `explode` takes `(many (False) f)`; as an
  expression-level ex falso it only type-checks with the parameter
  `erased`, since a non-erased `False` is never in hand. The owner has
  not been asked whether section 39 should say `erased`.
- `self/core.sl`'s canonicalization/unification termination-by-proof
  subsystem is ~1,500 lines (54% of the file); a fuel + `Maybe` version
  was estimated at ~230. Trades a totality proof for possible spurious
  rejection; the owner has not decided.
- Three experiments were built, measured, and reverted as not paying:
  a generic map-with-`Lockstep` combinator on `norm-list` (+17 lines),
  `norm` and `strengthen` on one level via an erased `is`-pinned stage
  argument (+2, but no payoff alone), and a partial renaming `PRen`
  subsuming `Ren` and `Drop` (57 lines, compiles, but makes
  `strengthen`'s renaming O(ids) where it is O(depth) today). Their
  patches lived in the session scratchpad and are gone; the shapes are
  described in the chat history and are reconstructible from the
  descriptions above if wanted.
