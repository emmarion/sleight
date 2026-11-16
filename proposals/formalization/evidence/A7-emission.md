## Ten-line summary

1. The report file was NOT written: my Write tool refuses report files from subagents ("Subagents should return findings as text"), and I did not route around it. The full report is below; please save it to `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/reports/A7-emission.md` if you want the file.
2. The last IR (`Code ctx ms` plus the store's `Block`s) is not low level: emit.sl (1516 lines, 48 decisions listed) chooses the OCaml encoding, the match compilation, the call kinds, and the static-data layout.
3. The emitted OCaml only has meaning at OCaml's run-time representation level (one word serves as constant constructor, `()`, and small `Z.t`), so a faithful "mini-OCaml" model is an untyped word-and-block machine, i.e. a low-IR semantics.
4. `slot-eq` answers differ between the evaluator, a bytecode build, and a native build of the same emitted file (ocamlopt merges equal immutable constants). Any "output's run matches spec's run" theorem must leave `slot-eq` free or pin it.
5. Arguments are let-bound by the elaborator (0 compound arguments in 17,469 emitted call and construction sites); `values` entries are bound left to right by emit.sl; an argument nested in a later `values` entry runs before earlier entries. The reference extractor uses `let ... and ...` there instead.
6. 834 lines of fixed OCaml header plus 82 templates stay trusted under every cut point; slc itself only runs through this output path.
7. `native-compute` brings back one decimal constructor index per function from a binary built by whatever `ocamlfind` is first on `PATH`; nothing cross-checks it.
8. `bootstrap.sh` compares bytecode builds and `--interpret` against the reference on printed output; native code is only exercised by slc's own build.
9. `--interpret` shares `eval`/`apply` with compile time, is bounded by fuel (default 10^9, depth-like), and never touches emit.sl for the user's program.
10. Scratch directory: `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A7/`. Nothing in `/home/user/sleight` was touched.

---

# A7: census of slc's output path (emission)

`$A7` below is `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A7/`.

Tags: `[QUOTE file:line]` exact text (line breaks inside a quotation are joined with one space); `[RAN]` a command I ran, with its output; `[READ file:lines]` what I read in that code; `[INFERENCE]` reasoning not verified; `[UNKNOWN]` not determined. `self/`, `lib/`, READMEs, ASSUMPTIONS.md, and code comments were written by earlier sessions; nothing quoted from them is the owner's decision or the language's definition. Only DESIGN.md is cited as the specification.

Read in full: `self/emit.sl`, `self/heap.sl`, `self/interp.sl`, `self/main.sl`, `self/header.sl`, `self/runtime.ml`, `self/bootstrap.sh`, `self/release.sh`, `self/README.md`, `lib/ffi_core.ml`, `lib/driver_core.ml`, `lib/ffi_templates.txt`, `lib/extract.ml`, and all of DESIGN.md. Read in part only: `self/core.sl`, `self/eval.sl`, `self/elab.sl`, `self/elab-main.sl` (the ranges cited).

## 0. Findings that bear on the decision, most important first

**F1. The last internal representation is not low level; emit.sl is where a Sleight value gets its OCaml form.** [READ self/core.sl:604-635, self/emit.sl:1-1516] Emission consumes post-erasure `Code ctx ms` (held in `Func`/`Group` values inside the store's `BGroup` blocks) together with the store's `Block`s. `Code` is a scoped functional IR: a constructor application is `CApp` on a constructor value, a match names an `Adt` and binds fields by position, closures are implicit, and there is no explicit tag test, load, or allocation except in the four cell forms. The facts that fix a representation (`tagged`, `nt`, `ext`, `shape`, `index`, `arity`) travel as data on `Ctor`/`Adt`, and emit.sl turns them into OCaml.

**F2. The emitted OCaml has a meaning only at the level of OCaml's run-time representation, not of typed OCaml.** [RAN, section 3] Every value is `Obj.t` behind `%identity` casts, and one word is used as a constant constructor, as `()`, and as a small `Z.t` at once (a fieldless constructor is returned as a `Nat` with no code). [INFERENCE] So a "modelled subset of OCaml" faithful to these programs has to be an untyped word-and-block machine, which is the same object as the semantics of a low-level IR. OCaml promises nothing for such programs: [QUOTE `git show 0bbc5e4`, commit message] "`type word = Imm | Ptr of int` made OxCaml record that exact shape for every word-typed value, and flambda2 then trusted it on function parameters and on lets bound through a branch (in a small test, K1 matched as K0 and 7 + 1 gave 1)."

**F3. `slot-eq` gives different answers in the evaluator, in a bytecode build, and in a native build of the same emitted file.** [RAN, section 2.4] For two separately built equal strings held as compile-time data, the reference interpreter, `slc --interpret`, and the emitted file built with `ocamlc` answer `ENone`; the same file built with `ocamlopt` answers `ESome`, because ocamlopt 4.14.1 merges the two equal immutable constants. [QUOTE DESIGN.md:3044-3046, §67] "`ESome` proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it, and which one a call answers may differ between runs." [INFERENCE] A theorem "the output's run matches the spec's run" cannot be an equality of runs if the spec's run gives `slot-eq` a determined answer (as the handoff's address model B would); it has to leave the answer free or fix how the output must answer. That is the owner's question.

**F4. Evaluation order is fixed before emission for calls and constructions, and by emission for `values`.** [RAN, section 2.3] In 12,212 direct calls, 43 calls through a function value, 145 `world-do`s, and 5,069 block constructions in the emitted code of 593 tests and of slc itself, every argument was a name, `()`, or a literal: the elaborator let-binds arguments first. The `Code` type does not enforce that. The entries of a multi-entry `values` are bound by emit.sl, left to right, and an argument nested in a later entry runs before the earlier entries. The reference extractor binds the same entries with `let ... and ...`. [RAN `grep -n -i -E "left to right|left-to-right|right to left|evaluation order|order of evaluation|evaluated|in the order|order written" DESIGN.md`] Hits at lines 631, 699, 1307, 1844, 1878, 1895 only; none states an order among the sub-expressions of one form (699 is the termination order), so DESIGN.md is silent on it, as the handoff says.

**F5. 834 lines of fixed OCaml and 82 templates are trusted under every cut point considered.** [RAN, section 4.1] Every emitted program starts with the same 834-line, 43,781-byte header (`lib/ffi_core.ml`, `lib/driver_core.ml`, `self/runtime.ml`). `lib/ffi_templates.txt` adds 82 OCaml fragments that emit.sl splices into program code. [READ] Both use far more of OCaml than program-specific code does (exceptions, `Hashtbl`, `Unix`, `Gc`, `Obj.magic`, `unsafe_*` primitives, optional arguments).

**F6. slc itself reaches a machine only through this output path.** [READ self/bootstrap.sh:139,162,168-169; self/release.sh:20-22] slc runs after being extracted to OCaml by `lib/extract.ml` or by slc. [INFERENCE] So a theorem about slc, including about its `--interpret` evaluator, is a theorem about a Sleight program, and executing it trusts emission of that one program (or the reference interpreter in `lib/`).

**F7. `native-compute` brings back one decimal constructor index per function, printed by a binary that slc builds by running whatever `ocamlfind` is first on `PATH`.** [RAN, section 6]

**F8. Sizes.** [RAN] emit.sl is 1516 lines (1222 non-blank, non-comment). Program-specific output has a median of 20 lines over 593 tests; slc's own output is 8,805 lines after the header. [INFERENCE] About a tenth of emit.sl is decision-free text assembly (section 5b).

## 1. The last internal representation

### 1.1 Definitions

[QUOTE self/core.sl:604-635]

```scheme
  ((Code : ((List $ List $ Nat) ctx) ((List $ Multiplicity) ms) -> Type)
    enum
    (many CVar : (erased (List $ List $ Nat) ctx) (many (Nat) id) (many (Mem id ctx) p) -> (Code ctx many-one))
    (many CConst : (erased (List $ List $ Nat) ctx) (many (Nat) id) -> (Code ctx many-one))
    (many CValue : (erased (List $ List $ Nat) ctx) (many (Block (Ref Block (HEmpty Block))) v) -> (Code ctx many-one))
    (many CErased : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) -> (Code ctx ms))
    (many CValues : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ms cs) pk) -> (Code ctx ms))
    (many CApp : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (Code ctx many-one) f) (many (List $ Code ctx many-one) args) (many (CC) cc) -> (Code ctx ms))
    (many CLet : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (erased (List $ Multiplicity) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (many (Code ctx ms) rhs) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (Code ctx ns))
    (many CLetRec : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (erased (List $ Nat) gids) (many (Group gids ctx) g) (many (Code (Cons (List (Nat)) gids ctx) ns) rest) -> (Code ctx ns))
    (many CMatch : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (many (Code ctx many-one) scrut) (many (Shape ctx) shape) (many (List $ Branch ctx ns) branches) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) dflt) (many (List $ Nat) live) -> (Code ctx ns))
    (many CCellAlloc : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (List $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellWrite : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Code ctx many-one) cell) (many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (List $ Nat) imms) -> (Code ctx many-one))
    (many CCellCopy : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Code ctx many-one) cell) (many (List $ Pair (Nat) $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellRead : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Nat) index) (many (Code ctx many-one) cell) -> (Code ctx many-one))
    (many CWorldDo : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) req) -> (Code ctx many-one))
    (many CPrim : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (Sp) prim) (many (List $ Code ctx many-one) args) -> (Code ctx ms))
    (many CAbsurd : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) -> (Code ctx ms))
    (many CError : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (String) msg) -> (Code ctx ms)))
  ((CC : -> Type)
    enum
    (many CCPlain : -> (CC)) (many CCTail : -> (CC)) (many CCDelegate : -> (CC)) (many CCCtor : -> (CC)) (many CCTag : -> (CC)) (many CCNoTail : -> (CC))
    ; a same-level call in a non-erased position carrying no mark, where the tail-position check warns
    (many CCSame : (many (Loc) site) (many (String) callee) -> (CC)))
  ((Shape : ((List $ List $ Nat) ctx) -> Type)
    enum
    (many ShKnown : (erased (List $ List $ Nat) ctx) (many (Adt) adt) -> (Shape ctx))
    (many ShHeld : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) c) (many (Adt) adt) -> (Shape ctx))
    (many ShNone : (erased (List $ List $ Nat) ctx) -> (Shape ctx)))
  ((Branch : ((List $ List $ Nat) ctx) ((List $ Multiplicity) ns) -> Type)
    enum
    (many MkBranch : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (many (Nat) disc) (many (List $ Nat) ids) (many (Code (Cons (List (Nat)) ids ctx) ns) body) -> (Branch ctx ns))))
```

[QUOTE self/core.sl:6] `(let ((many many-one)) $ Cons _ (Many) $ Nil _)`. [READ self/core.sl:9-15] `Picked A ms xs` says `xs` holds one item per non-erased entry of `ms`. [READ self/core.sl:365-373] `Mem id ctx` is a path to a frame (`MHere`/`MThere`) and a place in it (`At`: `AtHere`/`AtThere`).

[QUOTE self/core.sl:560-578, 581-585, 587-589, 593-599] (comment lines between them omitted)

```scheme
  ((Adt : -> Type)
    enum
    (many MkAdt : (many (String) name) (many (Bool) tagged) (many (List $ Ctor) ctors) (many (Maybe $ ExtType) ext) (many (Bool) nt) -> (Adt)))
  ((Ctor : -> Type)
    enum
    (many MkCtor : (many (String) name) (many (Nat) id) (many (Nat) index) (many (Nat) arity) (many (Bool) tagged) (many (Maybe $ ExtType) ext) (many (List $ Nat) shape) (many (Bool) nt) -> (Ctor)))
  ((Block : (Type R) -> Type)
    enum
    (many BArray : (erased Type R) (many (Nat) len) (many (IdMap R) elems) -> (Block R))
    (many BSlots : (erased Type R) (many (Nat) count) (many (IdMap R) keys) (many (IdMap $ Nat) ids) -> (Block R))
    (many BTag : (erased Type R) (many (Ctor) c) (many (List R) fields) -> (Block R))
    (many BTup : (erased Type R) (many (List R) fields) -> (Block R))
    (many BExt : (erased Type R) (many (Payload) p) -> (Block R))
    (many BCtorFn : (erased Type R) (many (Ctor) c) -> (Block R))
    (many BMat : (erased Type R) (many (Adt) adt) -> (Block R))
    (many BGroup : (erased Type R) (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Group gids ctx) g) (many (Frames R ctx) env) -> (Block R))
    (many BFn : (erased Type R) (many R group) (many (Nat) member) (many (Nat) id) -> (Block R))
    (many BToken : (erased Type R) -> (Block R))
    (many BError : (erased Type R) (many (String) msg) -> (Block R)))
  ((Frames : (Type R) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many FrNil : (erased Type R) -> (Frames R (Nil (List (Nat)))))
    (many FrVals : (erased Type R) (erased (List $ List $ Nat) ctx) (many (List $ Nat) f) (many (List R) vs) (erased (Lockstep (Nat) R f vs) lk) (many (Frames R ctx) rest) -> (Frames R (Cons (List (Nat)) f ctx)))
    (many FrGroup : (erased Type R) (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (many R group) (many (Group gids ctx) members) (many (Frames R ctx) rest) -> (Frames R (Cons (List (Nat)) gids ctx))))
  ((Group : ((List $ Nat) gids) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many MkGroup : (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (many (List $ Pair (Nat) $ Func gids ctx) fns) (erased (Lockstep (Nat) (Pair (Nat) $ Func gids ctx) gids fns) lk) -> (Group gids ctx)))
  ((Impl : -> Type)
    enum
    (many MkImpl : (many (SomeExtern) e) (many (List $ Ctor) cs) -> (Impl)))
  ((Func : ((List $ Nat) gids) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many MkFunc : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) rets) (many (String) name) (many (Nat) id) (many (List $ Nat) params) (many (Code (Cons (List (Nat)) params (Cons (List (Nat)) gids ctx)) rets) body) (many (Maybe $ Impl) impl) (many (Bool) top) -> (Func gids ctx))
    (many MkAlias : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (String) name) (many (Nat) id) (many (Code (Cons (List (Nat)) gids ctx) many-one) target) -> (Func gids ctx)))
```

[READ self/core.sl:544-551] `Payload`: `PNat n`, `PHalf n`, `PStr s`, `PBytes s`, `PRaw file syn`, `PHandle id reading mult shown`.

[QUOTE self/heap.sl:41-47, 56-58, 61-69] The store:

```scheme
  ((Hist : ((TyCtor (Type R) -> Type) B) -> Type)
    enum
    (many HEmpty : (erased (TyCtor (Type R) -> Type) B) -> (Hist B))
    (many HAdd : (erased (TyCtor (Type R) -> Type) B) (many (Hist B) rest) (many (Value B rest) v) -> (Hist B)))
  ((Value : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum
    (many MkValue : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Nat) pos) (erased (Len B l pos) lp) (many (B (Ref B l)) body) -> (Value B l)))
  ((Ref : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum newtype
    (many MkRef : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s) (many (Value B s) v) (erased (Suffix B l (HAdd B s v)) p) -> (Ref B l))))
  ((StoredBody : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum newtype
    (many MkStoredBody : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
      (erased (Hist B) s) (many (B (Ref B s)) body) (erased (Suffix B l s) sf) -> (StoredBody B l)))
  ((Store : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum
    (many MkStore : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
      (many (Nat) next) (erased (Len B l next) ln)
      (many (IdMap $ StoredBody B l) writes) -> (Store B l))))
```

[READ self/heap.sl:163-207] A `Ref` is a newtype over the `Value` it names, which carries its stamp `pos` and its body as allocated. The store holds the next stamp and a map `writes` from stamp to the current body of each overwritten block; `store-read` looks in `writes` first and otherwise returns the body carried by the reference; `store-write` replaces a body at the same stamp.

[READ self/core.sl:2333-2339, 2373-2374] An entry is `MkEInfo ... (State l) ...` with `SSettled v minter` (a `Ref Block l`) or `SHypothetical`. `env-store` returns what emission takes from the environment: the `Store Block hl`, the entries `IdMap (EInfo hl)`, and the finals `List (Pair (Ref Block hl) Term)`.

### 1.2 What each constructor means

[READ self/core.sl:604-635; self/elab-main.sl:159-333 (the evaluator's case for each); self/emit.sl:902-981 (the emitter's case for each)]

| Constructor | Meaning |
|---|---|
| `CVar id p` | a variable bound by an enclosing frame, by path |
| `CConst id` | a `Settled` entry by id; the evaluator reads its value from the store, the emitter prints its block's name |
| `CValue v` | a closed block embedded in the code (a constructor function, a `Matchable`, a handle), allocated when reached |
| `CErased ms` | stand-in for erased values; evaluator allocates a `BToken`, emitter prints `(to_any ())` |
| `CValues ms cs pk` | several values; `cs` are the codes of the non-erased entries |
| `CApp ms f args cc` | apply the value of `f` (a function or a constructor function) to `args`; `cc` is a calling-convention mark |
| `CLet ms ns ids pk rhs rest` | bind the non-erased results of `rhs` to `ids` (a new frame) in `rest` |
| `CLetRec ns gids g rest` | a group of mutually recursive functions (a new frame) in `rest` |
| `CMatch ns scrut shape branches dflt live` | a match; `shape` says how the discriminant is found (`ShKnown adt`, `ShHeld code adt` through a held `Matchable`, `ShNone` no dispatch); each `MkBranch disc ids body` binds the fields; `dflt` is the `else`; `live` the discriminants that can occur |
| `CCellAlloc ctor slots` | allocate a block of `ctor` with the given words |
| `CCellWrite ctor cell slots imms` | store words into fields of `cell` in place and return it; `imms` lists field indices marked `imm` |
| `CCellCopy ctor cell slots` | a fresh block: `cell`'s fields with the listed ones replaced |
| `CCellRead ctor index cell` | load one field |
| `CWorldDo req` | perform a `Request` |
| `CPrim ms prim args` | a primitive form (`slot-eq`, `settled-*`, the macro-world forms) |
| `CAbsurd ms` | code the checker refuted |
| `CError ms msg` | an internal-error placeholder |

Blocks [READ self/core.sl:566-578; self/emit.sl:1023-1035, 1268-1283]: `BTag` a constructor's block; `BTup` a tuple; `BExt` an extern value by payload; `BArray`, `BSlots` the extern array and slot table; `BCtorFn` a constructor as a value; `BMat` a `Matchable`; `BGroup` a function group closed over its frames; `BFn` one function of a group; `BToken` the token of an erased value; `BError` an error value.

### 1.3 Is it low level?

Already decided before emission [READ self/elab-main.sl:690-698, 1141-1158, 2368-2434, 2859; self/elab.sl:51-86, 1479-1482, 1640-1648, 3841-4044, 4206-4222]:

- Erasure: erased positions are gone or `CErased`; `at` parameters and returns are removed (`at-renames`, `project-code`, self/elab-main.sl:2382-2397).
- Scoping: variables are paths into frames; `Settled` entries are `CConst`.
- Argument binding: non-variable arguments are hoisted into `CLet`s (`Hoisted`/`StmtCode`, self/elab.sl:51-86; `hoist-argument`, self/elab-main.sl:690-698). This is the elaborator's convention, not a property of the `Code` type, whose `CApp` takes arbitrary codes.
- Normalization: `normalize = norm . distribute . norm` (self/elab.sl:4043-4044) resolves renaming lets, drops constant lets, floats lets out of right-hand sides, and pushes a `let` through a match; `check-marks` (self/elab.sl:4206-4222) validates `tail`/`delegate` on the result, and that result is the body stored in `MkFunc` (self/elab-main.sl:2397, 2433).
- `delegate`: the function is `MkAlias` with its target (self/elab-main.sl:2434). An at-function's body is replaced by a dummy (2429-2431).
- Two representation steps: applying a newtype's wrapping constructor is just its field's code, and applying an untagged fieldless constructor is the `vacant-slot` constant (self/elab-main.sl:1149-1157).
- The representation facts on `Ctor`/`Adt`: `tagged` is "enum with more than one non-phantom constructor" (`tagged-of`, self/elab.sl:1479-1482); `shape` the non-erased arities of the non-phantom constructors (`mint-adt`/`ctor-records`, self/elab.sl:1640-1648).
- Cells: allocation, in-place stores with field indices, copies, and loads are explicit nodes.
- A match's `live` set (self/elab-main.sl:2859).

Left abstract, so emission chooses:

- How a constructor's value, a tagged or untagged type, a `Matchable`, a constructor function, a function value, and an extern value are written in the target.
- How `CMatch` becomes a dispatch: `Code` has no tag test or field load.
- Whether a `CApp` is a block construction, a direct call, an extern's inline code, or a call through a value; emission does not read `cc` ([READ self/emit.sl:909] it is matched with `_`).
- Closures: `CLetRec` and `BGroup` keep nested functions with free variables.
- Compile-time data: the store is a graph; nothing before emission lays it out.

[QUOTE DESIGN.md:1459-1468, §33] "**Representation.** Coercion is free only if the representations coincide, so the following is a requirement on the implementation. Values have a uniform representation: every value is one word, either an immediate or a pointer to a block, whatever its type. So a `Cons` block holds a `(Meters)` and a `(Nat)` in the same way, and the field of a wrapper may be existentially typed. A value is the tuple of its constructor's non-erased fields; a single field is stored bare. A value carries a tag only when its type is an enum with more than one non-phantom constructor. A block's tag counts only the constructors with fields." [INFERENCE] So the abstract representation (word, block, tag, newtype as its field, hollow value as `vacant-slot`'s word) is part of the specification; what emit.sl adds is its encoding in OCaml.

## 2. Every decision emission makes

Classes: (i) representation, (ii) control, (iii) ordering, (iv) data, (v) driver and printing, (vi) FFI glue and templates. Line numbers are in `self/emit.sl` unless a file is named; every row is [READ self/emit.sl at those lines].

### 2.1 The table

| # | Lines | Class | Decision |
|---|---|---|---|
| 1 | 1-2, 613-622 | naming | `v<id>_<sanitized name>` for a binder, `a<stamp>` for a store block, `<name>_a<stamp>` for a function of a group block |
| 2 | 12-15 | (i) | a `Nat` literal below 2^62 is `(to_any n)`, an OCaml int; larger is `(to_any (Z.of_string "n"))` |
| 3 | 44-48, 56-60 | (i) | several values: none is `(to_any ())`, one is bare, more is an OCaml tuple taken apart by `let (a, b) = (of_any e : Obj.t * Obj.t)` |
| 4 | 62-87 | (i) | a function takes `(x : Obj.t)` parameters, or `()` for none; a function value is the OCaml closure cast to `Obj.t`; a call through a value casts it to `Obj.t -> ... -> Obj.t` at the call's arity (`dyn-call`, 83-84) |
| 5 | 190-245, 260-261, 1040-1066 | (i) | one OCaml variant type per shape (list of constructor arities), shared by every ADT of that shape, named `t<i>` by first sight; constructors `K<i>_<j>` |
| 6 | 283-304, 1140-1154 | (i) | a constructor with fields is an OCaml constructor over an inline record of `mutable f<k> : Obj.t`; a fieldless one is a constant constructor |
| 7 | 263-274, 299-304, 1150-1153 | (i) | a shape with more than 244 constructors that have fields is "wide": one constructor `K<i>_w` over `{ d : int; mutable f0 ...}`, discriminant in `d`, fields padded |
| 8 | 443-450 | (i) | `plain-build`: a newtype constructor's value is its field; a tagged type's is `(to_any (K { ... }))`; an untagged non-newtype's is a block of a one-constructor shape |
| 9 | 452-459 | (i), (vi) | an extern type's constructor is its `build` template, or `(con_T (to_any (K {...})))` through the FFI's view |
| 10 | 461-463 | (i) | a constructor as a value is a curried OCaml function that builds |
| 11 | 545-548 | (i) | a `Matchable` at run time is `m_plain` (the identity) for a plain type; for an extern type a function unwrapping the value into the shape its constructors describe |
| 12 | 907, 1034, 1244 | (i) | an erased value, a token, and a blank field are all `(to_any ())` |
| 13 | 729-752 | (ii) | `head-of`: a `CApp`'s head is a constructor (build), a function with an OCaml name (direct call), or anything else (call through the value); decided by lookup: a `CVar` in the frames' names, a `CConst` in the store (`env-block`), a `CValue` by its block |
| 14 | 585-611, 1008 | (ii) | a `delegate`-bodied function (`MkAlias`) gets no definition; its name is its target's |
| 15 | 909-920 | (ii) | `CApp`: build, or direct call `(f a b)`, or the callee's `fn` template inlined, or `dyn-call`. The `cc` mark is ignored: a tail call is whatever OCaml makes of a call in that position |
| 16 | 476-501 | (ii) | `dispatch-rope`: extern type with a `match` template: the template; extern without: `des_T` first; tagged: `match (of_any s : t<i>) with \| K.. -> ..`, or on the narrowed copy `yes t<i>_n<j>` when `live` leaves constructors out; `else` is `\| _ -> ..`; no arms and no default is `\| _ -> .`; untagged non-newtype: a one-constructor `match`; newtype: `let field = scrutinee in body` |
| 17 | 247-258, 276-278, 1156-1167 | (ii) | narrowing: a GADT copy of the shape per (shape, sorted live set), each constructor indexed `yes` if live, `no` if not; used only when some constructor is not live and the shape is not wide |
| 18 | 491 | (ii) | a wide shape always gets a default arm, `(absurd ())` when the match has none |
| 19 | 470-471, 945, 980-981 | (ii) | a match with no shape and no default, and `CAbsurd`, are `(absurd ())`; `CError` is `(failwith "msg")` |
| 20 | 943-948 | (ii) | a match through a held `Matchable` applies its value to the scrutinee, cast to `Obj.t -> Obj.t`, then dispatches as for a known type |
| 21 | 427-441 | (ii), (iii) | a templated match binds its scrutinee to a name unless the printed scrutinee is already a name, and binds a default used by more than one arm once as a thunk `let x<d>_d () = ...` |
| 22 | 885-897, 921-932, 405-423 | (ii), (vi) | fusing: `let x = (extern call)` followed by a match on `x` of the extern's result type becomes one template instance whose outcomes are the match's arms |
| 23 | 933-938 | (ii) | `CLetRec` is a local `let rec ... and ...`; closure conversion is left to OCaml |
| 24 | 950-958, 802-852 | (i), (ii) | cells: `cell-alloc` is a plain build; `cell-write` is `let c = cell in (match (of_any c : ty) with K r -> r.f0 <- a; r.f2 <- b); c`; a copy rebuilds from the old fields; a read is `r.f<k>` |
| 25 | 854-868, 874-876 | (i) | a store marked `imm` is `Array.unsafe_set (of_any cell : int array) k (of_any v : int)`: a raw word store, at index k+1 in a wide shape |
| 26 | 964-969 | (i) | `slot-eq a b` is `(if a == b then <ESome> else <ENone>)`: OCaml physical equality |
| 27 | 970-979 | (i), (vi) | handle primitives read a handle as the OCaml tuple `int * Ffi_core.reading * Ffi_core.mult * Obj.t` |
| 28 | 959 | (v) | `world-do` is `(driver.Driver_core.perform world req)` |
| 29 | 350-369, 181-188 | (iii) | `bind-args`/`values-rope`: each entry of a multi-entry `values`, and each template argument, that is not already a name is bound first by `let a = e1 in let b = e2 in`, left to right. "Is a name" is tested on the printed text (`rope-is-name`) |
| 30 | 870-878, 846-852 | (iii) | `cell-write`: the cell is bound first, then the items left to right, then the stores in item order separated by `;` |
| 31 | 1173-1227, 1496-1510 | (iv) | what is emitted: the blocks reachable from the finals and from the `Settled` constants that emitted code names, each once (seen set keyed by stamp) |
| 32 | 1239-1241, 1511-1513 | (iv) | blocks are emitted in stamp order |
| 33 | 1246-1257, 1268-1283 | (iv) | three passes: every `BTag`, `BArray`, `BSlots` block first as a blank skeleton, then every other block as a definition, then the fills (`bf.f<k> <- a<n>`, `Array.unsafe_set`, `Ffi_core.slots_add`) |
| 34 | 1259-1266 | (iv) | fills go into functions `fill_<k>` of at most 100 statements, each `[@inline never]`, each called once ([UNKNOWN] why; emit.sl gives no reason) |
| 35 | 1229-1237, 701-727, 1033 | (iv), (ii) | a compile-time closure: its group block is a top-level `let rec` whose free variables are the names of the blocks it closed over; a function value (`BFn`) is `(to_any <member name>)` |
| 36 | 657-661, 695-699 | (iv) | a `Settled` constant in code is the name of its block |
| 37 | 550-555, 663-693 | (iv) | payloads: a `String` is `(to_any (("text", 0, n) : Ffi_core.slice))`, `Bytes` is `Bytes.of_string "..."`, a `Raw` tree and a handle are written out as `Ffi_core` constructors |
| 38 | 6-7 | (iv) | an OCaml string literal is written with the Sleight literal's escaping (`lit-string` of self/escape.sl) |
| 39 | 505-533, 1285-1328 | (v) | the driver record: 35 fields (34 builds and dispatches over the prelude's `Nat`, `U8`, `Char`, `String`, `List`, `Pair`, `Maybe`, `Result`, `Unit`, `EntryKind`, `Change`, `Usage`, `Exited`, `ExecJob`, `ExecResults`, `Request`, `Program`, `Stopwatch`, found by name in the prelude's scope, plus `apply`); then `Driver_core.start` with the confinement flags |
| 40 | 4, 1330-1455 | (v) | a printer per type for a final value: `show-type` canonicalizes the type, unifies each constructor's return type with it to find the live constructors and field types (1416-1435, using the elaborator's `open-tele` and `unify-force`), memoizes by type, and on exhausting its fuel of 100000 uses `show_any`, which prints `?` (`self/runtime.ml:18`) |
| 41 | 1362-1369 | (v) | `Slot` prints `_`; `Nat`, `Char`, `String` print through `Z.to_string`, `Ffi_core.lit_char`, `Ffi_core.lit_string` |
| 42 | 1457-1479; self/elab.sl:5125-5139 | (v) | a final: a `Program` is `exit (driver.run_program world a)`; a `String -> String` function is `driver.run_main world a`; a function of no parameters is applied and printed; a constructor prints `_`; anything else is printed by its printer |
| 43 | 1465-1468 | (v) | a `native-compute` function: `if Sys.argv.(1) = "<i>" then` apply it and `print_int` its constructor's index |
| 44 | 100-179, 1504 | (vi) | the template language: lines `match T:`, `build T i:`, `fn F:` with holes `{s}`, `{bI}`, `{fI.J}`, `{aI}`, `{tK}`; parsed when a program is emitted; `--no-templates` drops them |
| 45 | 328-347, 388-395 | (vi) | filling: holes become names, temporaries `x<depth>_t<k>`, arguments `x<depth>_a<i>`; depth is the number of enclosing frames |
| 46 | 765-798 | (vi) | an extern function without a template is `(to_any (Ffi_core.<name> <views> (of_any p) ...))`; `flatten`, `list-to-array`, `array-new` get extra labelled arguments built from the prelude's types |
| 47 | 1011-1020 | (vi) | a function with an FFI implementation has the FFI call as its body, whatever its model's code is |
| 48 | 1171, 1502-1516 | all | output order: header, type declarations (narrowed copies first), driver, skeletons, definitions, fills, finals |

### 2.2 Representation and control, as emitted

[RAN `/home/user/sleight/_build/release/slc /home/user/sleight/tests/cell_append.sl > $A7/cell_append.ml`, exit 0] DESIGN.md §61's append: the narrowed type, the stores, the recursive call in tail position, and `(to_any ())` returned because the only return is `at cell`:

```ocaml
type _ t0_n0 = K0_0 : no t0_n0 | K0_1 : { mutable f0 : Obj.t; mutable f1 : Obj.t } -> yes t0_n0
let a4 : Obj.t = (to_any ())
let rec v42038_append_into_a1555 (v42042_cell : Obj.t) (v42044_h : Obj.t) (v42046_xs : Obj.t) (v42048_ys : Obj.t) : Obj.t = (match (of_any v42046_xs : t0) with | K0_1 { f0 = v42054_hd; f1 = v42056_tl } -> (let v42060_next = (to_any (K0_1 { f0 = a4; f1 = a4 })) in (let v42070_cell2 = (let cell4 = v42042_cell in (match (of_any cell4 : yes t0_n0) with K0_1 cell4_r -> cell4_r.f0 <- v42044_h; cell4_r.f1 <- v42060_next); cell4) in (v42038_append_into_a1555 v42060_next v42054_hd v42056_tl v42048_ys))) | K0_0 -> (let v42112___42112__ = (let cell3 = v42042_cell in (match (of_any cell3 : yes t0_n0) with K0_1 cell3_r -> cell3_r.f0 <- v42044_h; cell3_r.f1 <- v42048_ys); cell3) in (to_any ())) )
```

[RAN `ocamlfind ocamlopt -dlambda -c narrow.ml` in `$A7/build`, OCaml 4.14.1] Source (`t0`, `t0_n0`, `to_any`, `of_any` declared as in emitted code):

```ocaml
let narrowed (x : Obj.t) : Obj.t = (match (of_any x : yes t0_n0) with | K0_1 { f0 = a; f1 = b } -> a )
let plain_nonexhaustive (x : Obj.t) : Obj.t = (match (of_any x : t0) with | K0_1 { f0 = a; f1 = b } -> a )
let store_then_use (x : Obj.t) (y : Obj.t) : Obj.t = (match (of_any x : t0) with | K0_1 { f0 = a; f1 = b } -> (let c = x in (match (of_any c : yes t0_n0) with K0_1 r -> r.f0 <- y); a) | K0_0 -> x)
let const_block () : Obj.t = (to_any (K0_1 { f0 = (to_any ()); f1 = (to_any ()) }))
```

Output (the four functions; the rest of the dump omitted):

```
  (let (narrowed/373 = (function x/375 (field 0 x/375)))
    (plain_nonexhaustive/378 =
       (function x/380
         (if (isint x/380)
           (raise
             (makeblock 0 (global Match_failure/18!) [0: "narrow.ml" 8 46]))
           (field 0 x/380))))
    (store_then_use/388 =
       (function x/390 y/391
         (if (isint x/390) x/390
           (let (a/392 =o (field 0 x/390))
             (seq (setfield_ptr 0 x/390 y/391) a/392)))))
  (let (const_block/399 = (function param/401[int] (makemutable 0 0 0)))
```

So: the narrowed match is a bare `(field 0 x)` with no test; the same match on the plain shape tests and raises `Match_failure`; a field bound by a pattern is read before the body's store; a block of a mutable inline record is `makemutable`, built again at every evaluation even with constant fields, and the casts leave no trace.

[RAN, corpus of section 4] A match through a held `Matchable` (`tests/held_union.sl`):

```ocaml
let rec v42052_g_a1560 (v42060_m : Obj.t) (v42064_x : Obj.t) : Obj.t = (match (of_any ((of_any v42060_m : Obj.t -> Obj.t) v42064_x) : t11) with K11_0 { f0 = v42074_n } -> v42074_n)
```

[RAN] A wide shape (`tests/wide_cells.sl`): `and t11 = K11_0 | K11_w of { d : int; mutable f0 : Obj.t; mutable f1 : Obj.t }`, matched as `K11_w { d = 246; f0 = v51541_a; f1 = v51543_b }`, with `| _ -> absurd ()` added to its cell stores.

### 2.3 Ordering: the probe

[RAN] `$A7/order.sl` is accepted by both implementations and gives the same value everywhere: `/home/user/sleight/_build/default/bin/main.exe order.sl` prints `(MkTri 15 24 43)`; `slc --interpret order.sl` prints `(MkTri 15 24 43)`; `slc order.sl > order.ml` built with `ocamlfind ocamlopt -package zarith,unix -linkpkg` prints `(MkTri 15 24 43)`. Source (the functions of interest; `Tri` has constructor `MkTri` with three `many (Nat)` fields, `inc` is `(Succ n)`, `add3` is `(nat-add a (nat-add b c))`):

```scheme
(def-fns _ $ (many nested : (many (Nat) n) -> (many (Nat) r))
  (add3 (inc n) (inc (inc n)) (add3 n (inc n) n)))
(def-fns _ $ (many two : (many (Nat) n) -> (many (Nat) a) (many (Nat) b))
  (values (inc n) (add3 n n (inc n))))
(def-fns _ $ (many build : (many (Nat) x) (many (Nat) y) (many (Nat) z) -> (many (Tri) r))
  (let ((unique cell)) (cell-alloc MkTri))
  (let ((unique cell2)) (cell-write unique cell (MkTri (slot-of x) (slot-of y) _)))
  (share (cell2 (at) x (at) y z)))
(def-fns _ $ (many bump : (unique (Tri) t) -> (unique (Tri) r at t))
  (match unique t _
    ((MkTri a b c u) (u (inc a) (at) b (add3 a b c)))))
```

Emitted (`$A7/order.ml` lines 858, 860, 862, 864, 867; each complete):

```ocaml
let rec v42086_nested_a1565 (v42088_n : Obj.t) : Obj.t = (let v42102___42102__ = (v42036_inc_a1559 v42088_n) in (let v42112___42112__ = (v42036_inc_a1559 v42088_n) in (let v42118___42118__ = (v42036_inc_a1559 v42112___42112__) in (let v42132___42132__ = (v42036_inc_a1559 v42088_n) in (let v42138___42138__ = (v42053_add3_a1562 v42088_n v42132___42132__ v42088_n) in (v42053_add3_a1562 v42102___42102__ v42118___42118__ v42138___42138__))))))
let rec v42153_two_a1568 (v42155_n : Obj.t) : Obj.t = (let v42175___42175__ = (v42036_inc_a1559 v42155_n) in (let tup3_a0 = (v42036_inc_a1559 v42155_n) in let tup3_a1 = (v42053_add3_a1562 v42155_n v42155_n v42175___42175__) in (to_any (tup3_a0, tup3_a1))))
let rec v42193_build_a1571 (v42195_x : Obj.t) (v42197_y : Obj.t) (v42199_z : Obj.t) : Obj.t = (let v42203_cell = (to_any (K9_0 { f0 = a4; f1 = a4; f2 = a4 })) in (let v42213_cell2 = (let cell3 = v42203_cell in (match (of_any cell3 : t9) with K9_0 cell3_r -> cell3_r.f0 <- v42195_x; cell3_r.f1 <- v42197_y); cell3) in (let cell4 = v42213_cell2 in (match (of_any cell4 : t9) with K9_0 cell4_r -> cell4_r.f2 <- v42199_z); cell4)))
let rec v42232_bump_a1574 (v42234_t : Obj.t) : Obj.t = (match (of_any v42234_t : t9) with K9_0 { f0 = v42238_a; f1 = v42240_b; f2 = v42242_c } -> (let v42260___42260__ = (v42036_inc_a1559 v42238_a) in (let v42272___42272__ = (v42053_add3_a1562 v42238_a v42240_b v42242_c) in (let v42278___42278__ = (let cell5 = v42234_t in (match (of_any cell5 : t9) with K9_0 cell5_r -> cell5_r.f0 <- v42260___42260__; cell5_r.f2 <- v42272___42272__); cell5) in (to_any ())))))
let rec v42288_run_a1579 () : Obj.t = (let (v42298_p, v42300_q) = (of_any (v42153_two_a1568 a1576) : Obj.t * Obj.t) in (let v42314___42314__ = (v42086_nested_a1565 v42298_p) in (let v42324___42324__ = (v42036_inc_a1559 v42300_q) in (let v42330___42330__ = (v42036_inc_a1559 v42324___42324__) in (let v42332_t = (to_any (K9_0 { f0 = v42314___42314__; f1 = v42300_q; f2 = v42330___42330__ })) in (let _ = (v42232_bump_a1574 v42332_t) in (match (of_any v42332_t : t9) with K9_0 { f0 = v42344_a; f1 = v42346_b; f2 = v42348_c } -> (let v42362___42362__ = (v42086_nested_a1565 v42346_b) in (let v42374___42374__ = (v42053_add3_a1562 v42344_a v42346_b v42348_c) in (v42193_build_a1571 v42344_a v42362___42362__ v42374___42374__))))))))))
```

- [RAN] Nested calls in argument position (`nested`): every non-variable argument is bound by a `let` before the call, innermost first, left to right; the final call's arguments are names.
- [RAN] Multi-entry `values` (`two`): the argument `(inc n)` nested in the second entry is bound first (`v42175___42175__`), before the first entry is evaluated (`tup3_a0`); then the entries run left to right. [QUOTE DESIGN.md:655-661, §15] "Every argument to a constructor, a function or a cell behaves as if it were first bound to an anonymous variable. An argument that is already a variable is not rebound. That binding is a statement (§27) placed just before the statement or final form that contains the call, so its entry stays in scope, anonymously, for the rest of the expression around it, as the entries of a `let`'s right-hand-side statements do." [INFERENCE] The emitted order is the reading of §15 that the handoff mentions under its proposal A.
- [RAN] `cell-write` with several items (`build`): the cell is bound to `cell3`, then `cell3_r.f0 <- x; cell3_r.f1 <- y` in item order. The invocation with two `(at)` skips is the same form with the one remaining store.
- [RAN] In-place `unique` update (`bump`): fields bound by the pattern, new values computed and bound, then stored into the scrutinee's own block; the function returns `(to_any ())` and the caller (`run`) continues with its own binder (`let _ = (v42232_bump_a1574 v42332_t) in (match (of_any v42332_t : t9) ...`).

[RAN `python3 -I atoms.py corpus` and `python3 -I atoms.py selfdir` in `$A7`; the script parses every parenthesised application in function definitions after line 834 and classifies each argument] 593 tests: 969 direct calls, 33 calls through a value, 103 `world-do`s, 821 record constructions, none with a compound argument. slc's own output: 11,243 direct calls, 10 calls through a value, 42 `world-do`s, 4,248 record constructions, none compound. (The script also flags 17 FFI calls in the tests; each is a template body ending in `; to_any ()` that my parser mis-split.)

[READ self/elab-main.sl:178-191, 251-269, 335-343, 359-372] The compile-time evaluator's order within one node: `CApp` evaluates the head, then the arguments left to right (`eval-list`), then applies; `CValues` evaluates entries left to right (`eval-picked`); `CCellWrite` evaluates the cell, then the items left to right, then writes.

[RAN `$A7/build/order_ml.ml`, built with `ocamlfind ocamlopt` and `ocamlfind ocamlc`, OCaml 4.14.1; each test prints "1" and "2" from two sub-expressions] Native and bytecode gave the same output:

```
application: 21
tuple: 21
inline record: 21
let-and: 12
let-in-let: 12
physical equality: 21
sequence: 12
```

[INFERENCE] So wherever emit.sl prints sub-codes directly into an application, a tuple, a record, or `==` (rows 3, 4, 8, 15, 24, 26), OCaml would run them right to left, the opposite of the evaluator. That did not happen in any program I compiled because the sub-codes are names; it rests on the elaborator's hoisting, which I did not read in full (`check-args`) and which no type states.

[RAN `/home/user/sleight/_build/default/bin/main.exe order.sl --extract ref-order.ml` in `$A7`, exit 0] The reference extractor emits for `two`:

```ocaml
let rec v40844_two (v40846_n : Obj.t) : Obj.t = (let v40864 = (v40730_inc v40846_n) in (let x155_a0 = (v40730_inc v40846_n) and x155_a1 = (v40746_add3 v40846_n v40846_n v40864) in (to_any (x155_a0, x155_a1))))
```

[READ lib/extract.ml:129-134] Its `bind_args` joins bindings with `" and "`. So the two emitters differ: slc fixes the order of `values` entries and template arguments with nested `let`s; the reference leaves it to OCaml's treatment of `let ... and ...`. [READ self/emit.sl:362-364; lib/extract.ml:397-399] Both comments give the reason for binding at all as an ocamlopt failure (`Selection.size_expr`, ocaml/ocaml issue 15154), not evaluation order.

### 2.4 Data: the probe

[RAN] `$A7/data.sl`, compiled with `slc data.sl > data.ml`. Source, in part:

```scheme
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-adts $ (Two : -> Type) enum (many MkTwo : (many (Box) a) (many (Box) b) -> (Two)))
(let ((many shared-box)) (MkBox 7))
(let ((many two)) (MkTwo shared-box shared-box))
(let ((many other)) (MkTwo (MkBox 7) (MkBox 7)))
(let ((many greeting)) "hello")
(let ((many greeting2)) (str-append "hel" "lo"))
(def-fns _ $ (many make-adder : (many (Nat) k) -> (erased (Level) L) (many (Fn L (many (Nat) n) -> (many (Nat) m)) f))
  (def-fns _ $ (many adder : (many (Nat) n) -> (many (Nat) m)) (nat-add n k))
  (values (level-of adder) adder))
(let ((erased AL) (many add7)) (make-adder 7))
(def-fns _ $ (many same-str : (many (String) x) (many (String) y) -> (many (Nat) r))
  (match many (slot-eq (slot-of x) (slot-of y)) _ ((ESome _ _) 1) ((ENone _) 0)))
```

`run` returns the list of: `same a b` (fields of `two`), `same c d` (fields of `other`), `same-str greeting greeting2`, `(add7 1)`, and a large number. Emitted (`$A7/data.ml`, selected complete lines):

```ocaml
let a1565 : Obj.t = (to_any (K11_0 { f0 = (to_any ()) }))
let a1566 : Obj.t = (to_any (K5_0 { f0 = (to_any ()); f1 = (to_any ()) }))
let a1567 : Obj.t = (to_any (K11_0 { f0 = (to_any ()) }))
let a1568 : Obj.t = (to_any (K11_0 { f0 = (to_any ()) }))
let a1569 : Obj.t = (to_any (K5_0 { f0 = (to_any ()); f1 = (to_any ()) }))
let a1570 : Obj.t = (to_any (("hello", 0, 5) : Ffi_core.slice))
let a1573 : Obj.t = (to_any (("hello", 0, 5) : Ffi_core.slice))
let rec v42107_make_adder_a1578 (v42109_k : Obj.t) : Obj.t = (let rec v42117_adder (v42119_n : Obj.t) : Obj.t = (v2193_add_a310 v42119_n v42109_k) in (to_any v42117_adder))
let rec v42117_adder_a1580 (v42119_n : Obj.t) : Obj.t = (v2193_add_a310 v42119_n a1562)
let rec v42157_same_a1589 (v42159_x : Obj.t) (v42161_y : Obj.t) : Obj.t = (let v42173___42173__ = (if v42159_x == v42161_y then (to_any (K4_1)) else (to_any (K4_0))) in (match (of_any v42173___42173__ : t4) with | K4_1 -> a1584 | K4_0 -> a1586 ))
  (match (of_any a1566 : t5) with K5_0 bf -> bf.f0 <- a1565);
  (match (of_any a1566 : t5) with K5_0 bf -> bf.f1 <- a1565);
  (match (of_any a1569 : t5) with K5_0 bf -> bf.f0 <- a1567);
  (match (of_any a1569 : t5) with K5_0 bf -> bf.f1 <- a1568)
```

(the last four are inside `let[@inline never] fill_0 () = ...`, followed by `let () = fill_0 ()`.)

- [RAN] Sharing is preserved for constructor blocks: `two` (`a1566`) gets `a1565` in both fields; `other` (`a1569`) gets two distinct blocks. One top-level `let` per store block.
- [RAN] Mutable blocks are emitted as a blank mutable record and filled afterwards; 2.2 shows such a record is a fresh allocation; skeleton-then-fill is what closes cycles.
- [RAN] A compile-time closure (`add7`) is its own top-level function `v42117_adder_a1580` with the captured `k` replaced by the global `a1562`; the generic nested `adder` stays inside `make-adder`.
- [RAN] Identity of immutable blocks is not preserved by native code. Commands: `main.exe data.sl`; `slc --interpret data.sl`; `ocamlfind ocamlc -package zarith,unix -linkpkg data.ml -o data.byte && ./data.byte`; `ocamlfind ocamlopt -package zarith,unix -linkpkg data.ml -o data.exe && ./data.exe`. Outputs:

```
reference interpreter:   (Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 8 $ Cons _ 99999999999999999999999999 $ Nil _)
slc --interpret:         (Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 8 $ Cons _ 99999999999999999999999999 $ Nil _)
data.ml via ocamlc:      (Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 8 $ Cons _ 99999999999999999999999999 $ Nil _)
data.ml via ocamlopt:    (Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 8 $ Cons _ 99999999999999999999999999 $ Nil _)
```

  The third element is `slot-eq` of `greeting` and `greeting2`, two store blocks (`a1570`, `a1573`) emitted as the same constant.
- [READ self/eval.sl:804-809] The evaluator's `slot-eq` compares the two references' stamps. [READ self/eval.sl:383-394, 447-448] There every value is a block with its own stamp, including a `Nat` and a fieldless constructor of a tagged type, so [INFERENCE] the evaluator answers `ENone` for two separately computed equal small numbers where emitted code, comparing equal OCaml immediates with `==`, answers `ESome`. I did not run that case.
- [QUOTE DESIGN.md:1696-1698, §36] "Neither does canonical equality: two separately built cells with equal contents are `is`-equal and are two blocks." [RAN] That holds in emitted code for constructor blocks (second element `0` in all four runs). I found nothing in DESIGN.md about the identity of two equal extern values such as strings.

### 2.5 Driver and finals, as emitted

[RAN `slc /home/user/sleight/tests/io_echo.sl > $A7/io_echo.ml`] A `Program`: the final value is a skeleton filled with the start continuation, and the driver loops over it:

```ocaml
let a1570 : Obj.t = (to_any (K2_1 { f0 = (to_any ()) }))
  (match (of_any a1570 : yes t2_n0) with K2_1 bf -> bf.f0 <- a1569)
let () = exit (driver.run_program world a1570)
```

In the same file `world-do` is `(driver.Driver_core.perform world v42073___42073__)` bound by a `let`, and the `def-unique` continuation is a local closure, `(let rec v42135_again () : Obj.t = (v42063_echo_a1566 ()) in ...`.

[READ lib/driver_core.ml:402-405] `run_program` is `let rec loop v = match o.step v with Exit code -> u8 code | Continue k -> loop (o.apply k [])` inside `try ... with Halt code -> code`. [QUOTE DESIGN.md:1993-1994, §42] "The driver flushes after every write. It never recurses, so an unbounded interaction is the driver's loop over total functions."

[RAN, section 4] Of 593 compiled tests, 448 have no function definitions in their program-specific part: the whole program ran at compile time, and the output is data, a printer, and one `print_final`.

## 3. What the emitted OCaml relies on

| Reliance | Where | Evidence |
|---|---|---|
| Casts are free and invisible: `to_any`, `of_any`, `cast` are `external ... = "%identity"` | every value; `lib/ffi_core.ml:1-5`; `open Ffi_core.Cast` (`self/header.sl:6`) | [READ]; [RAN] no trace in the `-dlambda` output of 2.2 |
| The optimizer does not turn a cast value's claimed type against its real representation | everywhere | The git-log line "Emitted casts that flambda2 can see through" is commit 0bbc5e4. [QUOTE its message] "Under OxCaml, Obj.repr, Obj.obj and Obj.magic are the primitive %obj_magic, which flambda2 treats as an opaque identity (oxcaml PRs #862 and #3044). Nearly every value of an emitted program crosses one, so flambda2 knew almost nothing about them", and "%identity is safe under flambda2 only where the value really has the representation its use implies. A read-only audit and the checks below found two exceptions, both handled here": `address` ("With %identity flambda2 folded it to 0 wherever it could see the block, which silently made every slots lookup a linear scan") and `type word = Imm \| Ptr of int` (quoted in F2). [RAN `git show --stat 0bbc5e4`] it changed `ASSUMPTIONS.md`, `lib/extract.ml`, `lib/ffi_core.ml`, `lib/ffi_templates.txt`, `self/emit.sl`, `self/header.sl`, `self/runtime.ml` (243 insertions, 233 deletions). [RAN `ocamlfind ocamlopt -config`] this machine: 4.14.1, `flambda: false`, so I could not reproduce any of it |
| A constant constructor is an immediate equal to its position among the constant constructors; `()` is 0; a `Z.t` below 2^62 is the same immediate | `coercible-tag`, `vacant-slot`, hollow values | [RAN `tests/coercible_tag.sl` compiled] `((Red) (coerce c (coercible-tag (Shared) Red)))` is emitted as `\| K11_0 -> v42101_c`: the constructor's word returned as a `Nat`; `a4`, which is `(to_any ())`, is passed to `add` as a number in the same file. [QUOTE DESIGN.md:1476-1478, §33] "`vacant-slot`'s word is that of `Nat` 0. With externs on, the extern `Nat`'s FFI must meet this for these numbers." [READ lib/ffi_core.ml:27] a start-up check that `Sys.int_size = 63` and `Z.of_int max_int` is an immediate |
| A constructor with fields is a block whose tag is its position among the constructors with fields | every tagged match | [INFERENCE] OCaml's documented layout; it coincides with [QUOTE DESIGN.md:1467-1468] "A block's tag counts only the constructors with fields." |
| Two differently declared types with the same constructor arities in the same order have the same layout | shapes shared between ADTs; the narrowed copy against its shape; `Ffi_core.nat`, `str`, ... against the program's shape (`des_T`/`con_T`); `Driver_core.request`, `step` | [RAN `slc --no-templates loop.sl`] `(match (of_any (des_Nat v42028_n) : t1) with \| K1_0 -> ... \| K1_1 { f0 = v42034_k } -> ...`: an `'v Ffi_core.nat = Zero \| Succ of 'v` read as `t1 = K1_0 \| K1_1 of { mutable f0 : Obj.t }` |
| Mutable inline records: a construction allocates afresh every time and is never shared or folded | every `K { ... }`, `cell-alloc`, static skeletons | [RAN] `(makemutable 0 0 0)` in 2.2 |
| A field bound by a pattern is read when the arm is entered | in-place update after a destructure (`bump`) | [RAN] `(let (a =o (field 0 x)) (seq (setfield_ptr 0 x y) a))` in 2.2, 4.14.1 only |
| An inline record is consecutive words, field k at word k | `imm` stores: `Array.unsafe_set (of_any cell7 : int array) 0 (of_any v61290_n : int)` | [RAN] 28 such stores in the corpus (`array_imm`, `cell_imm`, `vec_std_imm`, `vec_std_get_truncate`); [READ emit.sl:863-868] index k+1 in a wide shape |
| Skipping the write barrier is safe when old and new words are immediates | the same stores; `array-place-imm`, `array-swap-imm`, `Ffi_core.array_blit_imm` (`lib/ffi_core.ml:315-321`) | [INFERENCE] a property of OCaml's collector, outside any model of values; the evidence that the words are immediates is the program's `Imm` proofs (DESIGN.md §37, §44) |
| Physical equality `==` | `slot-eq` (emit.sl:969); template tests against `Z.zero` (`lib/ffi_templates.txt:8,11,20`) | [RAN] 2.4: the answer depends on how OCaml shares immutable constants |
| GADT refinement removes the dispatch on refuted constructors | `(match (of_any x : yes t0_n14) with \| K0_1 {...} -> ...)` | [RAN] 2.2. In slc's own output 245 narrowed types are declared; 35 uses are in function code and 1,064 in fill statements; in the 593 tests, 42 uses in function code (19 files) and 740 in fills. [READ self/elab-main.sl:206, 233-235, 390] the evaluator ignores `live` and reports "no branch for discriminant"; emitted code would read fields of whatever arrived. [QUOTE self/README.md:242-244] "A wrong refutation would misdispatch silently here, as ASSUMPTIONS 63 records for the reference; the interpreter is the checked path." |
| All warnings are off, so a missing arm is not reported | header line 1, `[@@@warning "-a"]` (`self/header.sl:4`) | [READ] |
| Evaluation order of application arguments, tuple components, record fields, `==` operands | 2.3 | [RAN] right to left on 4.14.1; not exercised because the sub-terms are names |
| `let x = e1 in e2` and `e1; e2` run `e1` first | all sequencing | [RAN] 2.3 |
| A call in tail position is a jump | every `tail`-marked call; emit.sl ignores the mark | [QUOTE DESIGN.md:819-821, §19] "`(tail (f ...))` asserts that the call compiles to a tail call. `(notail (f ...))` asserts the opposite. A claim the compiler cannot honour is an error." [RAN `$A7/loop.sl`] three million `tail` calls complete in the emitted program. [RAN `$A7/build/tn74.ml`, `tn75.ml` with `ocamlfind ocamlopt -S`] with 74 parameters a tail-position call to another function is `jmp camlTn74__k_268@PLT`; with 75 it is `call camlTn75__k_268@PLT`. So on ocamlopt 4.14.1/amd64 the claim would not be honoured for a call of more than 74 non-erased arguments. (My test programs still ran to completion because ocamlopt inlined one function into the other; the evidence is the instruction, not a stack overflow.) |
| Closures and currying | function values; `Driver_core.apply` applies one argument at a time (emit.sl:1321) | [READ] |
| `Z.t` (zarith) arithmetic, small values being OCaml ints | `Nat`; templates use `Obj.is_int` and `int` arithmetic on `Z.t` values | [READ lib/ffi_templates.txt:8-21; lib/ffi_core.ml:96-123]; [RAN `ocamlfind list`] zarith 1.13 |
| No float is ever a value | arrays typed `Ffi_core.word array` | [READ lib/ffi_core.ml:207-210, a session's comment] |
| Strings are never mutated after `Bytes.unsafe_to_string` | `bytes-str`, `append`, `flatten` | [READ lib/ffi_core.ml:148, 173, 260] |
| Collector behaviour: addresses change only at minor collections and compactions | `Slots` (`lib/ffi_core.ml:323-389`) hashes block addresses | [READ] |
| Sleight's string-literal escapes mean the same in an OCaml literal | every emitted string (emit.sl:6-7) | [READ]; not tested byte by byte |
| Names do not collide | `v<id>_...`, `a<n>`, `x<d>_t<k>`, `tup<d>_a<i>`, `cell<d>`, `copy<d>`, `bf`, `held`, `v`, `f<k>` | [QUOTE self/emit.sl:310-312] "the prefix of this instantiation's temporaries (the nesting depth, distinct along any path since a body sits in tail position and every other hole is a name)"; [INFERENCE] I did not check that argument |

[RAN `grep -n -i -E "OCaml|ocamlopt|flambda|Obj\.|Z\.t|zarith" DESIGN.md`] No hits: DESIGN.md never mentions OCaml; the target is the implementations' choice.

## 4. How big would a "mini-OCaml" model be?

### 4.1 The fixed header

[RAN] `head -834 f.ml | md5sum` gives the same digest (`0bd6fabf8959...`) for all ten probe outputs, slc's own output, and the file slc handed to `ocamlfind` during a `native-compute`. [READ self/header.sl:3-6] Three preamble lines, `lib/ffi_core.ml` (398), two lines, `lib/driver_core.ml` (408), two lines, `self/runtime.ml` (21): 834 lines; [RAN] 43,781 bytes.

[RAN, each `slc tests/X.sl > X.ml`, exit 0]

| Test | Total lines | Header | Program-specific |
|---|---|---|---|
| `tests/list.sl` | 851 | 834 | 17 |
| `tests/cell_append.sl` | 864 | 834 | 30 |
| `tests/io_echo.sl` (has a `def-unique` closure) | 868 | 834 | 34 |
| `tests/slot_eq.sl` | 868 | 834 | 34 |
| `tests/array_swap.sl` | 863 | 834 | 29 |
| `tests/unique_closure.sl` | 851 | 834 | 17 |

`tests/slot_eq.sl` runs entirely at compile time, so its output contains no `==`; `$A7/data.sl` is the probe that shows `slot-eq` emitted.

### 4.2 The corpus

[RAN `ls /home/user/sleight/tests/*.sl | xargs -P 2 -L 1 $A7/one.sh`; results in `$A7/corpus-results.txt`] Of 1,337 files in `tests/`, 740 carry an `; error:` directive and 4 a `; goal: open|proved` directive and were skipped; the other 593 compiled with exit 0 (`slc --no-native`, honouring each test's `needs`, `prelude`, `fn-same`, `eval-fuel`, `flags`, and `comptime-unconfine` directives). Plus slc compiling its own 15 sources: [RAN `slc --no-native std/list.sl std/macro.sl self/base.sl ... self/main.sl > $A7/slc-self.ml`] 5.22 s wall, 217,444 KB maximum resident set, 9,639 lines, 3,758,994 bytes.

[RAN `python3 -I census2.py corpus` and `... selfdir`] Program-specific output by section:

| Section | 593 tests: lines | 593 tests: bytes | slc: lines | slc: bytes |
|---|---|---|---|---|
| type declarations | 6,863 (42.2%) | 895,864 (19.5%) | 318 | 358,745 |
| driver record, `world`, `print_final` | 1,758 (10.8%) | 2,795,220 (60.7%) | 3 | 4,770 |
| static blocks `let a<n> : Obj.t = ...` | 3,579 (22.0%) | 202,019 (4.4%) | 5,084 | 573,945 |
| fills | 1,355 (8.3%) | 77,611 (1.7%) | 1,524 | 105,663 |
| function definitions | 755 (4.6%) | 413,901 (9.0%) | 1,875 | 2,672,042 |
| generated printers | 1,202 (7.4%) | 188,082 (4.1%) | 0 | 0 |
| finals | 768 (4.7%) | 31,185 (0.7%) | 1 | 48 |

Per test, program-specific non-blank lines: minimum 0, median 20, mean 27.5, maximum 188. 145 of the 593 have any function definition; 538 have a printer; 28 end in `exit (driver.run_program ...)`, 5 in `driver.run_main`, and 111 apply a thunk.

### 4.3 The syntactic forms that occur

[RAN `python3 -I census.py alldir` plus pattern counts, over all 594 files after line 834, string literals masked]

Keywords that occur: `let`, `rec`, `and`, `in`, `fun`, `match`, `with`, `if`, `then`, `else`, `type`, `of`, `mutable`, `true`, `false`, and the integer operators `mod`, `land`, `lor`, `lxor`, `lsl`, `lsr`, `asr`. Never as code: `try`, `exception`, `while`, `for`, `function`, `when`, `as`, `begin`, `end`, `module`, `open`, `lazy`, `assert`. No `:=`, `!`, `::`, array literal, character literal, or float literal.

Top-level forms:

1. `type t0 = K0_0 | K0_1 of { mutable f0 : Obj.t; ... } and t1 = ...` (and the wide form with `d : int`).
2. `type _ t0_n0 = K0_0 : no t0_n0 | K0_1 : { ... } -> yes t0_n0` (GADT with a phantom index).
3. `let a<n> : Obj.t = e`.
4. `let rec f (x : Obj.t) ... : Obj.t = e and g ...`, with `()` for no parameters.
5. `let[@inline never] fill_k () = e; e; ...` and `let () = fill_k ()`.
6. `let driver = Driver_core.make ~str_of_host:(fun ...) ... { Driver_core.zero = e; ... }`, `let world = Driver_core.start [...] [...] None true true world`, `let print_final = Driver_core.print world`.
7. `let rec show_0 (v : Obj.t) : string = e and show_1 ...`.
8. `let () = print_final (...)`, `let () = exit (driver.run_program world a)`, `let () = driver.run_main world a`, and, only in a `native-compute` file, `let () = if Sys.argv.(1) = "0" then let v = ... in match ... -> print_int 0 | ...`.

Expression forms:

1. Names, `()`, integer literals (decimal; hexadecimal in one template), string literals.
2. Casts with a type annotation: `(to_any e)`, `(of_any e : T)`, `T` being a shape, `yes t_n`, `int`, `Z.t`, `bytes`, `int array`, `Ffi_core.word array`, `Ffi_core.slice`, a tuple of `Obj.t`, the handle tuple, or an arrow `Obj.t -> ... -> Obj.t` or `unit -> Obj.t`.
3. `let x = e in e`; `let (x, y) = e in e`; `let _ = e in e`; `let rec f ps : Obj.t = e and ... in e`; inside templates only, `let t0 () = e and t1 () = e in e` and `let a = e and b = e in e`.
4. Application of a named function, of a cast value, and of header functions, some with labelled arguments whose values are `fun v -> match ...`.
5. `fun (x : Obj.t) ... -> e`, `fun () -> e`, `fun held -> e`.
6. A constant constructor; a constructor over a record `K { f0 = e; ... }`; a tuple; header constructors (`Some`, `None`, `Driver_core.WriteOut (...)`, `Ffi_core.Atom (...)`, `Ffi_core.At { file = ...; ... }`); list literals.
7. `match e with | p -> e | ... | _ -> e`; patterns: a constant constructor, a constructor over a record pattern binding fields to names or `_`, a constructor binding its whole record (`K0_1 r`), a wide pattern with an integer-literal field (`d = 246`), tuples, `_`, header constructors.
8. `r.f0` and `r.f0 <- e`; sequence `e; e`.
9. `if e then e else e` with `==`, `=`, `<`, `&&`, and integer arithmetic.
10. `(absurd ())`. `failwith "..."` can be emitted (emit.sl:589, 659, 661, 962-981, 1032, 1035) but occurs in none of the 594 files; `| _ -> .` (emit.sl:494) occurs in none either.

Host functions named in program-specific code: [RAN] 82 template lines (3 `match`, 7 `build`, 72 `fn`) naming 49 distinct functions and types of `Z`, `String`, `Bytes`, `Array`, `Char`, `Obj`, and `Ffi_core`; emit.sl's own strings name `Z.of_string`, `Z.to_string`, `Z.to_int`, `Bytes.of_string`, `Array.make`, `Array.unsafe_set`, `String.sub`, `String.length`, `List.iter`, `List.fold_left`, and `Ffi_core`/`Driver_core` names; the 103 extern functions of slc's table (self/core.sl:508-529) are called as `Ffi_core.<name>` when they have no template.

### 4.4 What a formal semantics of that subset would need

All [INFERENCE], resting on sections 2 to 4.3; checkable by writing the model for the listed forms and running the corpus through an evaluator of it.

1. **Values, untyped.** A word is a 63-bit immediate or a pointer. The casts erase every type, and the same immediate is read as `unit`, a constant constructor, a small `Z.t`, and an `int`.
2. **Heap objects.** Mutable blocks with a tag and word fields; immutable tuples; closures; byte strings and mutable byte buffers; word arrays; big integers; the `Slots` table as an abstract object. Allocation of a mutable block gives a fresh address; for immutable objects the model must allow two equal ones to be one object or two (2.4).
3. **A layout function** from a type declaration to tags: constant constructors numbered among themselves, constructors with fields among themselves, an inline record as the block's fields in order. Types are otherwise irrelevant at run time; a match on a narrowed type can be modelled as undefined on a constructor that is not live.
4. **Evaluation order.** `let` and `;` in order. For applications, tuples, records, and `==`, either nondeterminism or a restriction of the modelled subset to atomic operands, which is what the emitted code already is. `let ... and ...` in templates needs the same treatment.
5. **Functions.** Top-level and local `let rec` groups, closures over local variables, application at exact arity. Partial application occurs only in the header (`Driver_core.apply`).
6. **Exceptions.** None in program-specific code: `absurd ()` and `failwith` end the run. The header uses real handlers (`Halt`, `Unix_error`, `Sys_error`).
7. **Modules.** Only qualified names into the two header modules and the standard library.
8. **Primitives.** About 50 standard-library and zarith functions used by templates, each needing a specification, plus about 100 `Ffi_core` functions and the driver. [QUOTE DESIGN.md:1951-1955, §42] "An `extern` implementation must agree with its model: except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31)." So each primitive's specification already exists as its prelude model; a model of the output would add the statement of that agreement at the representation level, per primitive.
9. **Stack and tail calls.** [QUOTE DESIGN.md:1319-1323, §31] "Evaluation is eager. The semantics is that of a machine with unlimited stack and heap. A real run may crash where the host cannot represent what is asked of it. A crash produces no value, never a different one. How a crash is reported is not specified; it need not be a runtime error." A model with an unbounded stack needs no tail-call rule to get the right values; the `tail` assertion is a claim about cost that such a model does not express.
10. **I/O.** `driver.Driver_core.perform world req` as an external transition labelled by the request and its answer.

Not coverable by any model of values and heap: that the OCaml compiler in use implements the model for programs that cast freely; the collector-dependent parts (`imm` stores, `Slots`); resource limits.

## 5. Alternative cut points

In every case the header (834 lines), the 82 templates, the OCaml compiler and run-time system, zarith, and the operating system stay trusted unless stated. The elaborator, which produces the `Code` and the store, is outside this report.

### (a) Stop at post-erasure `Code` plus the compile-time store

Types at the cut: what `env-store` returns (self/core.sl:2373-2374): a `Store Block hs`, entries `IdMap (EInfo hs)` (each `SSettled` with its `Ref Block hs`), and finals `List (Pair (Ref Block hs) Term)`; the code is the `Group`s inside `BGroup` blocks. The statement proved would be about the spec's run of the finals over that store.

Trusted after it: all of `self/emit.sl` (the 48 rows of 2.1), plus what it calls from the elaborator for printers (`canon-env`, `open-tele`, `unify-force`, `ctor-type`).

[INFERENCE] The risk that stays is concentrated in rows 13 to 22 and 31 to 35: a wrong head resolution, shape, or narrowing, a missing fill, or a block emitted twice would give a program that compiles and computes something else. Rows that fail loudly (a missing shape prints `tmissing`, emit.sl:217-218, which OCaml rejects) matter less.

### (b) Stop at a new lower IR, then print without deciding

[INFERENCE throughout; nothing here exists in the repository, and the IR is my sketch, not a design the owner has seen.]

A lower IR whose nodes are the forms of 4.3, with atoms where OCaml's order is unspecified:

```
atom  ::= local name | global a<n> | () | integer
exp   ::= atom
        | let x = exp in exp | let (x1 .. xn) = atom in exp | let rec funs in exp
        | call-known f atoms | call-value atom atoms
        | block shape ctor atoms            ; fresh mutable block with that tag
        | const shape ctor                  ; immediate
        | tuple atoms
        | switch atom shape live [(ctor, binders, exp)] default?
        | load atom shape ctor k | store atom shape ctor [(k, atom)] | store-imm ...
        | same-word atom atom exp exp
        | prim p atoms [(outcome, binders, exp)]      ; an extern, by template or FFI call
        | perform atom | absurd | fail text
top   ::= skeleton a<n> shape ctor arity | array-skeleton | slots-skeleton
        | define a<n> exp | funs | fill a<n> k atom | final kind a<n>
```

Decisions that could move into a verified pass from `Code` and store to this IR:

- (i) rows 2 to 12 and 24 to 27: functions of `Ctor`, `Adt`, and `live`.
- (ii) rows 13 to 23: head resolution, aliases, match lowering, default sharing, fusing.
- (iii) rows 29 and 30, decided on structure (is this an atom) instead of on printed text.
- (iv) rows 31 to 37: the reachability walk, the order, the skeleton/definition/fill split. The statement to prove is that the emitted static heap is isomorphic to the reachable part of the store.
- (v) row 39 can be produced as ordinary lowered builds and dispatches; row 42 is a case analysis on the final's type. Row 40, the printers, is type-directed generation using the elaborator's unifier; it could instead be generated as `Code` by the elaborator and lowered like any function. I did not check how hard that is.

What would stay in the printer: one fixed OCaml phrase per IR node, the type declarations from the shape table, names, and string escaping. Trusted: that printer; that OCaml gives each phrase the IR's meaning (section 3's reliances, one per node); the template texts; the header.

How much of emit.sl is which. [RAN] Code lines per region (non-blank, non-comment; total 1,222 of 1,516):

```
   1-  87    65   text helpers: names, tuples, lambdas, params
  88-  95     3   Narrow decl
  96- 188    77   templates: types and parser
 190- 278    66   Decls table, shape/ctor/narrow naming, live-key, wide, narrowed
 280- 304    19   record fields, pattern-rope
 306- 441   108   template filling, bind-args, values-rope, fused arms, templated dispatch
 443- 463    18   builds
 465- 501    31   dispatch
 503- 548    36   driver arm kinds, ctor-arms, matchable-rope
 550- 555     5   z/spot ropes
 557- 636    63   names: frames to OCaml names, aliases, member names
 638- 699    54   addr ropes, handles, const-rope, syn-rope, payload-rope
 701- 727    24   captured frames by name
 729- 752    19   call heads
 754- 798    35   prelude lookups, ffi view/extra/call
 802- 878    64   cells
 880- 897    17   let-rope, fusing
 899-1035   124   emit-code and friends, block-rope
1037-1136    84   collect-*: declarations a program needs
1140-1171    28   type declarations printed
1173-1227    44   reachability walk
1229-1283    46   block-let, stores, fill-chunks, emit-blocks
1285-1328    36   driver record
1330-1455   103   generated printers
1457-1516    53   finals, collect-prelude, emit-program
```

[INFERENCE] My classification: about 117 lines are text assembly with no case analysis on the IR (1-87, 280-304, 550-555, 1140-1171); 185 the template parser and filler; 228 the driver arms, driver record, printers, and finals; 174 the declaration walk, reachability walk, and data layout; 515 representation and control lowering and naming. In a split design I would expect a printer of 250 to 350 lines and a lowering pass about the size of today's emit.sl, since each case still has to be written, building a node instead of a rope.

### (c) Stop at a modelled OCaml subset

The model is 4.4's; the pass is (b)'s with the IR renamed to an OCaml abstract syntax; the printer prints that syntax.

Trusted after it: the printer; that real OCaml implements the model on these programs; the header; and the template texts, unless each of the 82 templates is written in the modelled syntax and proved against its prelude model.

[INFERENCE] The difference from (b) is more in name than in assurance. Because the emitted programs are type-unsafe by construction (F2), a faithful model is a word-and-block machine with OCaml's layout rules, which is what (b)'s IR semantics is. Calling it OCaml adds an obligation the project cannot discharge (that ocamlopt and flambda respect it), and the flambda2 quotation is a recorded case of that obligation failing. What (c) adds over (b) is modelling what (b)'s printer phrases take for granted: the layout function and the order rules (items 3 and 4 of 4.4), a small part of the whole.

### (d) `--interpret`

[READ self/interp.sl:13-16, 98-157; self/main.sl:84-86, 145-157; self/elab-main.sl:159-446]

- Shared with compile time: the same `eval` and `apply` (self/elab-main.sl:159, 402). At compile time `run-code` calls `eval` with the `compile-time` performer (self/eval.sl:1532-1533, built from `no-world` and `no-prim`; [INFERENCE from the macro counterpart at 1535-1538] it answers a `world-do` with an error block). Under `--interpret`, `interp-finals` handles each final by kind: a `Program` goes to `interp-program`, which reads `Exit`/`Continue` from the store and for `Continue` returns one step of slc's own `Program` whose continuation calls `apply` on the program's continuation with a performer running each request through `perform-request` (self/eval.sl:1064) on slc's own world; a thunk or a `String -> String` function is applied with `apply`; results are printed by the compile-time printer `show-at` (self/elab.sl:4680), not by generated OCaml printers.
- The user's program never goes through emit.sl. Extern functions run as the evaluator's own implementations (`apply-extern`, self/eval.sl:547), a third implementation beside the prelude models and `lib/ffi_core.ml`.
- Fuel: [READ self/core.sl:3614] default 1000000000. [QUOTE MANUAL.md:154-157] "`--eval-fuel n` bounds the evaluator. An application spends one unit of fuel, a call to a function interpreted from its body one more, and each gives its units back when it returns, so `n` bounds how deeply applications nest, a tail call nesting inside the call it replaces." [RAN `$A7/loop.sl`, three million `tail` calls] `slc --interpret loop.sl` prints `3000000` in 0.98 s; `slc --interpret --eval-fuel 4000000 loop.sl` prints `slc: runtime error: out of fuel`; the emitted program prints `3000000`. [READ self/interp.sl:109, 113] each `Continue` step starts again from the full fuel.
- What a certified evaluator would give this mode: [INFERENCE] if `eval`/`apply` were proved to agree with the spec's run on post-erasure code, `slc --interpret p.sl` would agree with the spec on `p`, given a correct elaborator, correct `perform-request` and `apply-extern`, and a correct execution of slc itself. The last condition is where emission returns (F6). So `--interpret` does not remove emission and OCaml from what is trusted; it reduces the emitted programs that must be right from every user program to slc, one fixed program that the bootstrap fixpoint and the tests exercise.
- The evaluator's run is not the emitted program's run on `slot-eq` (F3), and it stops on fuel where the emitted program does not.

How `self/bootstrap.sh` compares the paths today [READ self/bootstrap.sh:1-182; not run]:

- Line 139: the reference extracts slc to a native binary (`$REF --warnings-as-errors --warn-unused $SL --extract "$B/slc.ml" --build "$B/slc"`).
- For each test without an `; error:` directive (`check_test`, 45-130): the reference interpreter runs the files with the test's stdin, arguments, and environment (101); slc builds the test with `--byte --build` (114), to bytecode, and the result is run (122); line 125 requires `cmp -s` equality of stdout, of stderr (slc's messages then the program's), and of the exit code.
- Repeated with `--no-templates` for tests named `extern_*`, `thunk_*`, `main_*`, `char*`, `nat_*`, `bytes_*` (144), with `--no-native` for tests containing `native-compute` (145), and with `slc --interpret` for every test (108-111, 146).
- A test with an `; error:` directive must be refused with a message containing the directive's text (70-88).
- Lines 162-181: slc compiles slc; the result is built with `ocamlfind ocamlopt` and compiles slc again; the two OCaml outputs must be identical.

[INFERENCE] Two limits of that check as evidence for cut (a): the per-test comparison builds bytecode, so native code generation is exercised only by slc's own build, and 2.4 shows a program whose bytecode and native builds differ; and the comparison is on printed output, so it sees a wrong value only if it is printed.

## 6. `native-compute`

[QUOTE DESIGN.md:3149-3156, §72] "The form means `(values (f1) … (fn))`, and each result is `Settled` as its call's would be (§29). It is how a program asks for run-position calls to be run by compiled code rather than by the evaluator, as a final `Fn` is (§27). The compiled run hands back only the constructor, so its erased fields take the tokens of §5. It may crash where the evaluator would not, and the other way round (§31). A program that cannot be compiled is an error at the form, and a run that crashes is an error at its argument."

[QUOTE DESIGN.md:1305-1309, §29] "Every fact derived from a stored value, that is, a `comptime-match` and everything that follows from the fields it binds, relies on the evaluator having evaluated correctly. A stored value that `native-compute` produced relies on its compiled run in the same way (§72)."

How slc does it [READ self/elab-main.sl:24-60, 77-145, 706-733, 861-878; self/emit.sl:1463-1468]:

1. `native-head` checks each argument: a `Settled` `many` function of no parameters and one `many` return not written `at`, whose type's opened `Matchable` is an enum none of whose constructors has a non-erased field.
2. `native-batch` calls `emit-program` on the environment as it stands, with the functions' blocks as the finals and their return types' `Adt`s as `natives` (self/elab-main.sl:123). For such a final, `final-rope` emits a line that tests `Sys.argv.(1)`, applies the function, and prints its constructor's index.
3. `native-run` runs `mktemp -d`, writes `main.ml` there, runs `ocamlfind ocamlopt [-inline n] -package zarith,unix -linkpkg main.ml -o <dir>/main` in that directory, then one `Exec` request with one job per function, `<dir>/main <k>`, with slc's own environment; then deletes the directory.
4. `native-answers` requires exit code 0 and parses each job's standard output with `str-nat`; `native-cids` maps the number to a constructor with `list-nth (adt-ctors adt) i` and reports an error if there is none.
5. The call's code becomes `CApp` of that constructor to no arguments (self/elab-main.sl:730-733), so the stored value is that fieldless constructor. Under `--no-native` the functions are called in the evaluator (870-871).

[RAN `PATH=$A7/wrap:$PATH /home/user/sleight/_build/release/slc tests/native_compute_several.sl`, where `$A7/wrap/ocamlfind` copies `main.ml` aside, logs its arguments, and runs `/usr/bin/ocamlfind`; exit 0, 0.73 s] The log line: `cwd=/tmp/tmp.d44JqtifDj args=ocamlopt -package zarith,unix -linkpkg main.ml -o /tmp/tmp.d44JqtifDj/main`. The captured file has the same 834-line header and ends with one line per function, the first two being:

```ocaml
let () = if Sys.argv.(1) = "0" then let v = (of_any a1562 : unit -> Obj.t) () in (match (of_any v : t11) with | K11_0 -> print_int 0 | K11_1 -> print_int 1 | K11_2 -> print_int 2 )
let () = if Sys.argv.(1) = "1" then let v = (of_any a1572 : unit -> Obj.t) () in (match (of_any v : t4) with | K4_0 -> print_int 0 | K4_1 -> print_int 1 )
```

What crosses back into the elaborator: per function, an exit code and a string of decimal digits on standard output, turned into one constructor of a known enum. No heap value crosses.

What a compile-time fact from a native run therefore trusts ([INFERENCE] from the steps above, except where tagged):

- emit.sl on the whole program so far, and the header: the same things a final program trusts.
- The OCaml native compiler and zarith as found at that moment. [RAN] slc ran my wrapper, so it runs the first `ocamlfind` on `PATH`; `PATH` and the toolchain installation are part of it.
- The temporary directory, where source and binary sit between writing and running.
- Process execution and output capture in `lib/driver_core.ml:183-253`, as run by slc's own driver.
- The number-to-constructor step: the printed index is `ctor-index` and the lookup is by position in `adt-ctors`; [READ self/core.sl:557-559, a session's comment] those are "the non-phantom ones at their discriminants", so the two agree if that comment is right. I verified it no further than the test's expected output.
- Nothing checks the answer against the evaluator. The erased fields of the answered constructor (for example the `Lt` proof inside a `Yes`) are tokens, so a wrong digit yields a `Settled` whose `comptime-match` mints a proof of something false.

[RAN `grep -rl native-compute --include=*.sl .`] Outside `tests/` and slc's own sources, it is used in `bb/` (eight files) and `fourcolor/native.sl`. [READ lib/extract.ml:683-704] The reference does the same with its own emitter.

## 7. Places where the sources disagree

- [QUOTE self/README.md:85-91] "`heap.sl` — a store for the compile-time interpreter, parametric in its block type: addresses below a bound, carried as their bijective spelling with erased `Numeral` and `Lt` proofs, widened by a `coerce`; and a Braun tree of blocks sized by its count (the LSB-first trie on the spelling), whose `alloc` and `deref` the session reads as total by the size alone, the lemmas over the prelude's `Double` and `Numeral` doing the work." versus [QUOTE self/heap.sl:1-4] "the compile-time store: a value is stamped with its position in an erased ghost history, and refers to other values directly rather than through an address. The history makes position -> value a function (suffix-unique below), which is what lets the emitter name a value it has already written." The code (1.1) is the second.
- [QUOTE self/README.md:255-257] "Those two take a `Nat` that decreases along the call stack (not a step count), so a fuel of 1000000 or 100000 bounds depth, not work" versus [READ self/core.sl:3614] an initial evaluator fuel of 1000000000.
- [QUOTE self/README.md:212-214] "**The reference extractor's scheme, by the owner's decision** that `lib/extract.ml` is the specification of this emitter and the two back-ends agree" versus 2.3: the two differ in how they bind `values` entries and template arguments. I report the README's sentence as a session's statement; I cannot confirm the owner's decision it cites.
- [QUOTE ASSUMPTIONS.md:219-222] "The interpreter still raises on a reached absurd, extraction being the path that trusts the checker (the owner's reading: interpretation is the checked path, extraction is opted into for speed)." An ASSUMPTIONS.md entry attributing a view to the owner; under CLAUDE.md rule 14 that file records sessions' choices, so I do not treat it as the owner's decision.

## 8. Things I am least sure of

1. **That arguments are always atoms.** The evidence is empirical (17,469 sites, none compound) plus a partial reading of the hoisting code. I did not read `check-args` or the cell and primitive paths in full, and the `Code` type permits compound arguments. A counterexample would make emitted order differ from the evaluator's.
2. **My reading of OCaml's behaviour.** Layout, `=o` bindings, `makemutable`, constant sharing, evaluation order, and the 74-argument limit were observed on OCaml 4.14.1 without flambda on amd64 only. The flambda2 statements are quotations from a commit message.
3. **The tail-call experiment** shows `jmp` against `call` in the assembly, not an actual stack overflow; ocamlopt inlined one of my two functions despite `[@@inline never]`.
4. **The split of emit.sl into decisions and printing** (5b): line counts per region are measured; the classification and the size estimates are judgement.
5. **Whether the constant sharing of 2.4 is permitted.** §67 allows answers to differ between runs and allows `ENone` always; whether `ESome` for two separately built equal strings is acceptable is the owner's to say. I found only §36's sentence about cells on block identity.
6. **The second `slot-eq` difference** (two equal small numbers: evaluator `ENone`, emitted `ESome`) is inferred from code, not run.
7. **Name hygiene** of generated temporaries rests on a session's comment (emit.sl:310-312) that I did not check.
8. **Completeness of the decision table.** emit.sl calls into `self/elab.sl`, `self/eval.sl`, and `self/core.sl` (`type-adt`, `ctor-type`, `open-tele`, `unify-force`, `prelude-adt`, `env-block`, `at-constant`), read only where cited; decisions made inside those calls are not in the table.
9. **`native-compute`'s index agreement** rests on a comment in core.sl and passing tests.
10. **Not looked at:** how the reference interpreter in `lib/` evaluates; `dune test`; whether the 593 tests reach every case of `emit-code` (they never produced `failwith` or `| _ -> .`).

## Appendix: scratch files

All under `$A7`. Probes: `order.sl`, `data.sl`, `loop.sl`, with outputs `order.ml`, `data.ml`, `build/loop.ml`, `loop-notempl.ml`, `ref-order.ml`. Corpus: `one.sh`, `corpus/` (593 `.ml` files and their stderr), `corpus-results.txt`, `slc-self.ml`, `selfdir/`, `alldir/`. Scripts: `census.py`, `census2.py`, `atoms.py`. OCaml experiments in `build/`: `narrow.ml`, `narrow.lambda.txt`, `order_ml.ml`, `order_ml.out.txt`, `tn8.ml` to `tn80.ml` with `.s` files, `data.exe`, `data.byte`. `native-compute` capture: `wrap/ocamlfind`, `native/main.0.ml`, `native/calls.log`, `native/several.ml`. Toolchain [RAN `ocamlfind ocamlopt -config`]: 4.14.1, amd64, linux, `flambda: false`; zarith 1.13. Git, read-only [RAN `git -C /home/user/sleight log --oneline | grep -i -E "flambda|cast|Obj"`]: `0bbc5e4 Emitted casts that flambda2 can see through; word records no shape` and `916f1d8 release.sh: compile with -O3 under flambda2 as well as flambda`. No background process was left running. One side effect outside the scratch directory: slc's own `mktemp -d` created and deleted `/tmp/tmp.d44JqtifDj` during the `native-compute` run.