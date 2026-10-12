# Macros: design notes

Notes from a design session with the owner on a simple macro system and its
reflection forms. Nothing here is in DESIGN.md yet; the owner chose to write
DESIGN.md's wording last. Each item says whether the owner decided it
("Decided") or a session proposed it and the owner has not reviewed it
("Proposed"). Claims about soundness are the session's reasoning, not the
owner's, and are hedged accordingly.

## 1. Built-ins

Bound before any file is read, beside `Slot` and `Sharing` (DESIGN.md §42).

```scheme
(def-adts $ (Mult : -> Type)
  enum
  (many MErased : -> (Mult))
  (many MMany : -> (Mult))
  (many MUnique : -> (Mult)))

(def-adts $ (JMEq : (Type A) (A a) (Type B) (B b) -> Type)
  enum
  (many JMRefl : (erased Type A) (erased A a) -> (JMEq A a A a)))

Settled      : (TyCtor ((Mult) m) (Type T) (T t) -> Type)
MacroWorld : (TyCtor -> Type)
Gensym     : (TyCtor ((Nat) n) ((String) s) -> Type)
```

- `Mult`: Decided that it is a new ADT rather than `Sharing`. Its name and
  its constructors' names are open (they must not clash with `Sharing`'s
  `Unique` or with the annotation tokens).
- `JMEq`: Decided. It is in the source prelude.
- `Settled`: Decided that it is opaque and not an ADT, like `Slot`: no
  constructors, no `Matchable`, not erased by kind. A handle
  `(Settled m T t)` denotes `t`, held at multiplicity `m`. Decided that its
  run-time value may be a term rather than an entry id, that an `MMany`
  handle carries the value it denotes, and that a handle denotes a term.
  A session found, in the reference over the tests, that a `Settled`
  entry's minted type mentions only entries bound at run position;
  nothing has shown that it always holds.
- `MacroWorld`: Decided (named by the owner, in place of "Table"). Opaque
  (`def-opaque`, INTERNALS.md section 1), declared in the prelude. It is a
  handle on the elaborator's program store (section 4), passed `unique`
  to a macro and returned `at` itself.
- `Gensym`: Decided. Opaque (`def-opaque`), declared in the prelude: a
  witness that `n` was minted, with text `s`. Nothing produces one but
  `gensym`, which returns it erased.

## 2. Prelude types

```scheme
(def-adts $ (Pos : -> Type)
  enum
  (many MkPos : (many (String) file) (many (Nat) line) (many (Nat) col) -> (Pos)))

(def-adts $ (Symbol : -> Type)
  enum
  (many SName : (many (String) s) -> (Symbol))
  (many SGen : (many (Nat) n) (many (String) s) (erased (Gensym n s) g) -> (Symbol)))

(def-adts
  ((Atom : -> Type)
    enum extern
    (many AName : (many (Symbol) y) -> (Atom))
    (many ASettled : (erased (Mult) m) (erased Type A) (erased A a) (many (Settled m A a) c) -> (Atom)))
  ((Raw : -> Type)
    enum extern
    (many RAtom : (many (Pos) pos) (many (Atom) a) -> (Raw))
    (many RWild : (many (Pos) pos) -> (Raw))
    (many RList : (many (Pos) pos) (many (List $ Raw) items) -> (Raw)))
  ((Macro : -> Type)
    enum newtype
    (many MkMacro : (erased (Level) L)
       (many (Fn L (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
                 (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out)) f)
       -> (Macro))))
```

- `Pos`, `Symbol`, `Atom`, `Raw`, `Macro`: Decided, as written.
- `Atom` and `Raw` are `extern`: Decided. The intent is that their
  representation is the reader's own syntax tree, so a macro's arguments and
  output are passed without copying; copying would let nested expansions
  cost exponentially more than the macros' own work.
- `ASettled` is itself the existential over `m`, `A` and `a` (Decided; an
  earlier separate `SomeConst` wrapper was dropped).
- `RWild` is a `_` (Decided). A raw name `#"_"` is an `AName`, never an
  `RWild` (DESIGN.md §1).
- `Atom` has no literal constructors for now (Decided: deferred). A macro
  gets a literal by interning it (section 3).
`symbol-eq : (many (Symbol) x) (many (Symbol) y) -> (many (Maybe (Eq (Symbol) x y)) r)`
is ordinary prelude code (Decided that equality returns a proof): `str-cmp`
for names; for gensyms, `nat-cmp` on the ids and then `gensym-unique` in the
`CEq` branch. A session checked this with the current checker against
stand-ins for `Gensym` and `gensym-unique`; without the `gensym-unique` step
the `Refl` does not check, which suggests the axiom is exactly what the
gensym case needs.

## 3. Special forms

### Handles

```scheme
(settled-of m x)  : (many (Settled m' T t) h)
    ; x a Settled entry; T its minted type; t its minted is; m erased: any entry;
    ; many: x declared many; unique: x declared unique; m' the matching Mult
(settled-type c)     : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
                     (many (Settled (MErased) Type T) h)
(settled-mult c)     : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
                     (many m is r)
(settled-value c)    : (erased Type T) (erased T t) (many (Settled (MMany) T t) c) -> (many t is v)
```

All Decided. Decided: a handle denotes `x`'s minted `is` at `x`'s minted
type (DESIGN.md §5, §29), as head dispatch reads the minted type (§6). There
is no `settled-value` for erased handles (it would only rename the handle's own
erased index) and none for unique handles (a macro's read would happen
outside the elaborator's use accounting, possibly after the value was
consumed and mutated in place). A `constant-slot` form was considered and
dropped. Decided: `settled-type` does not canonicalize the type it
returns; `settled-eq` does, where it compares. Only `settled-eq` and the
splicing of a `RawSettled` read the term a handle denotes, and both happen
during an expansion, so an extracted program need not hold it.

### The macro world

```scheme
(settled-eq ma A a mb B b mw p q) : (erased (Mult) ma) (erased Type A) (erased A a)
                        (erased (Mult) mb) (erased Type B) (erased B b)
                        (unique (MacroWorld) mw) (many (Settled ma A a) p) (many (Settled mb B b) q) ->
                        (unique mw is mw2 at mw) (many (Maybe (JMEq A a B b)) r)
(gensym mw s)         : (unique (MacroWorld) mw) (many (String) s) ->
                        (unique (MacroWorld) mw2 at mw) (many (Nat) n) (erased (Gensym n s) g)
(gensym-unique n s t a b) : (erased (Nat) n) (erased (String) s) (erased (String) t)
                        (erased (Gensym n s) a) (erased (Gensym n t) b) ->
                        (erased (JMEq (Gensym n s) a (Gensym n t) b) e)
(intern-nat mw n)     : (unique (MacroWorld) mw) (many (Nat) n) ->
                        (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (Nat) n) h)
(intern-char mw c)    : (unique (MacroWorld) mw) (many (Char) c) ->
                        (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (Char) c) h)
(intern-string mw s)  : (unique (MacroWorld) mw) (many (String) s) ->
                        (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (String) s) h)
(read-file mw path)   : (unique (MacroWorld) mw) (many (String) path) ->
                        (unique (MacroWorld) mw2 at mw) (many (Result (String)) r)
    ; read-file is jailed: after resolving symlinks, the path must lie in the directory, or a
    ; subdirectory, of at least one of the program's source files; any other path answers Fail
```

- `settled-eq`: Decided, with its erased parameters written out as `def-prim`
  needs. Decided: it answers `Just` exactly when the checker at run level,
  given the current table, would consider the two handles' terms
  equivalent: the facts are those of the innermost run position enclosing
  the call, never branch-forced ones, so that a `Just` stays true wherever
  the macro's output goes and a call expands the same way in every branch.
  A session's reading is that this has `settled-eq` enter the facts of every
  literal the two terms mention, as the checker does where a literal is
  written.
- `gensym`, `gensym-unique`: Decided. Both are constructors of `Special`
  whose signatures the prelude gives with `def-prim` (INTERNALS.md
  section 2). `gensym-unique` is the one axiom; it is meant to rest on the
  counter minting each `n` once, with one text.
- `intern-nat`, `intern-char`, `intern-string`: Decided, as written.
- `read-file` and its jail: Decided.

## 4. Rules

1. Expansion (Decided). A `Macro` head dispatches as a special form does
   (DESIGN.md §6) and expands in statement, final, expression and type
   positions. In statement position each item of the result is a
   statement; in final position the last item is the final form and the
   rest are statements before it; anywhere else the result must be exactly
   one item. Arguments arrive unexpanded and unresolved; the head is not
   passed. Expansion is limited to 10000 expansions.
2. Arguments (Proposed). A source name arrives as `(AName (SName s))`; a
   source literal as an `MMany` handle to its interned entry.
3. Names (Decided). A name resolves exactly. `SName s` is the source's own
   name `s`, and any `s` can be written raw (DESIGN.md section 1); `SGen n s
   g` is identified by `n` alone, no source spelling stands for it, and a
   message shows it as `__g` and `n` and `_`, followed by `s` spelled as a
   name is spelled (README.md): `__g1_tmp`, or `__g1_#"a b"` where `s` is
   not a plain name.
4. Handles. Decided: a handle keeps the multiplicity it was made with, the
   `m` of `(settled-of m x)`. Where it is spliced, it is checked as if `x`
   had been written there with that multiplicity. So an `MErased` handle may
   appear only in erased positions, an `MMany` handle is used at many, and an
   `MUnique` handle is used at unique, which consumes it. Decided: a handle
   cannot be used as a binder, any more than anything else that is not a
   name can. Decided: a spliced `ASettled` is a reference to the term it
   denotes, bypassing scope, as a variable reference is to its entry; its
   multiplicity, as above, decides where it may stand.
5. The macro world (Decided). It is the elaborator's program store: the
   run-position entries with their values and facts, the literal table, the
   gensym counter and the expansion count. It is threaded sequentially
   through all of elaboration, carried out of every scope where uses are
   carried now, and passed along rather than joined. Proposed: it never
   escapes an expansion, having no constructor and being no entry.
6. Threading (Decided). A helper that takes a macro world returns it `at`
   its parameter.
7. Supply. Only the expander supplies a macro world.

## 5. Soundness, as a session argues it

- A macro is untrusted: its output is elaborated and checked like source,
  so reflection should only be able to steer what it generates.
- `settled-eq` answers `Just` only from facts that hold unconditionally.
- A handle denotes its index because only built-in forms create handles.
- A gensym cannot be forged: building an `SGen` at `many` needs an erased
  `Gensym` witness, and only `gensym` makes one.

The owner suspects this section holds of the language as it stands.

## 6. Open questions

1. The names of `Mult` and its constructors, and `Settled`.
3. Whether the macro world resolves names at the call site; if so it must
   also carry the call site's scope.
5. `read-file`: what a relative path is relative to, which files count as
   the program's source files, whether reads also obey `--confine-dir`, and
   how symlinks are resolved.
7. Literal constructors in `Atom`: deferred.

## 7. What implementing it would involve

- `lib/`: `Atom` and `Raw` extern over the reader's tree; names as
  structured symbols in `Term` and `Env`, keying the scope; `Env.t` split
  into a scoped part and a threaded program store.
- `self/`: its own `Pos` and `Raw` renamed (Decided), so the prelude's do
  not clash with them; a decreasing budget around expansion, since its
  elaborator's structural recursion on raws (ASSUMPTIONS.md 96) does not
  cover a macro's output; its interpreter serving a macro's `read-file`
  with its world, and calling back into its elaborator for macro-world
  operations.
- Decided: the macro-world forms of section 3 are elaborated through the
  same code as a call, as `world-do` is: the argument checking that calls
  and constructor applications share, then a call's return handling.


## 8. What the compilers implement now

The source prelude declares the following, which both compilers implement.

```scheme
(def-adts $ (Pos : -> Type)
  enum
  (many NoPos : -> (Pos))
  (many MkPos : (many (String) file) (many (Nat) line) (many (Nat) col) -> (Pos)))

(def-adts $ (JMEq : (Type A) (A a) (Type B) (B b) -> Type)
  enum
  (many JMRefl : (erased Type A) (erased A a) -> (JMEq A a A a)))

(def-opaque $ (Gensym : ((Nat) n) ((String) s) -> Type))
(def-opaque $ (MacroWorld : -> Type))

(def-adts $ (Mult : -> Type)
  enum
  (many MErased : -> (Mult))
  (many MMany : -> (Mult))
  (many MUnique : -> (Mult)))

(def-opaque $ (Settled : ((Mult) m) (Type T) (T t) -> Type))

(def-prim $ (many gensym : (unique (MacroWorld) mw) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Nat) n) (erased (Gensym n s) g)))

(def-prim $ (erased gensym-unique : (erased (Nat) n) (erased (String) s) (erased (String) t)
    (erased (Gensym n s) a) (erased (Gensym n t) b) ->
    (erased (JMEq (Gensym n s) a (Gensym n t) b) e)))

(def-prim $ (many settled-type : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
    (many (Settled (MErased) Type T) h)))

(def-prim $ (many settled-erase : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
    (many (Settled (MErased) T t) h)))

(def-prim $ (many settled-eq : (erased (Mult) ma) (erased Type A) (erased A a)
    (erased (Mult) mb) (erased Type B) (erased B b)
    (unique (MacroWorld) mw) (many (Settled ma A a) p) (many (Settled mb B b) q) ->
    (unique mw is mw2 at mw) (many (Maybe (JMEq A a B b)) r)))

(def-prim $ (many settled-mult : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) ->
    (many m is r)))

(def-prim $ (many settled-value : (erased Type T) (erased T t) (many (Settled (MMany) T t) c) -> (many t is v)))

(def-prim $ (many intern-nat : (unique (MacroWorld) mw) (many (Nat) n) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (Nat) n) h)))

(def-prim $ (many intern-char : (unique (MacroWorld) mw) (many (Char) c) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (Char) c) h)))

(def-prim $ (many intern-string : (unique (MacroWorld) mw) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Settled (MMany) (String) s) h)))

(def-adts $ (Symbol : -> Type)
  enum
  (many SName : (many (String) s) -> (Symbol))
  (many SGen : (many (Nat) n) (many (String) s) (erased (Gensym n s) g) -> (Symbol)))

(def-adts $ (Resolution : -> Type)
  enum
  (many RSettled : (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) h) -> (Resolution))
  (many RHypothetical : -> (Resolution))
  (many RUnbound : -> (Resolution)))

(def-prim $ (many resolve : (unique (MacroWorld) mw) (many (Symbol) s) ->
    (unique mw is mw2 at mw) (many (Resolution) r)))

(def-adts $ (Raw : -> Type)
  enum extern
  (many RawSymbol : (many (Pos) pos) (many (Symbol) s) -> (Raw))
  (many RawWild : (many (Pos) pos) -> (Raw))
  (many RawList : (many (Pos) pos) (many (List $ Raw) items) -> (Raw))
  (many RawSettled : (many (Pos) pos) (erased (Mult) m) (erased Type A) (erased A a) (many (Settled m A a) c) -> (Raw)))

(def-adts $ (Macro : -> Type)
  enum newtype
  (many MkMacro : (erased (Level) L)
     (many (Fn L (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
               (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out)) f)
     -> (Macro)))
```

A call splices its result into telescopes, `let` binders and their
entries, `match` and `let-match` branches, `def-adts` constructors,
arguments and `values` entries, besides the positions of section 4.1;
at most 10000 expansions run in one run. `gensym` counts from 1 over the
whole run, every file included. An unbound gensym gets no "nearest in
scope" hint. `(settled-of m x)` makes a handle (section 3), and
`RawSettled` puts one in a macro's output, where it stands for its entry
directly. A handle names the entry its `Settled` was minted at and how it
reads that entry: `MintedIs`, standing for the entry's minted `is`, or
`MintedType`, standing for its minted type. `settled-type` turns a
`MintedIs` handle into the `MintedType` handle on the same entry.
`settled-erase` makes the `MErased` handle on the same entry and reading.
`settled-mult`, `settled-value`, `settled-type` and `settled-erase` read a
handle anywhere, not only during an expansion, and an `MMany` handle
carries its value into an extracted program. The `intern-` forms,
`settled-eq` and `resolve` run only in an expansion, the one place a macro
world exists. The `intern-` forms intern the literal where they run.
`settled-eq` compares the terms the two handles stand for and their types,
canonically, against the facts of the innermost enclosing run position,
into which it first enters the declaration facts of the literals it needs.
`resolve` looks a name up in the scope at the macro call form: a `Settled`
entry answers `RSettled` with a `MintedIs` handle at the entry's declared
multiplicity, any other bound entry `RHypothetical`, and a name not in
scope `RUnbound`; the lookup is not a reference to the entry.

The reader's tree keeps its literal nodes, but each top-level form of the
source has its literals interned, and replaced by `MMany` handles to their
entries, just before it is elaborated, so a literal reaches a macro as a
`RawSettled` and `Raw` has no literal constructor. A macro builds a literal
by interning it. A handle to a literal is treated as the literal wherever
the elaborator words a refusal, and is shown canonically.
