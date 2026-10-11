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

Const      : (TyCtor ((Mult) m) (Type T) (T t) -> Type)
MacroWorld : (TyCtor -> Type)
Gensym     : (TyCtor ((Nat) n) ((String) s) -> Type)
```

- `Mult`: Decided that it is a new ADT rather than `Sharing`. Its name and
  its constructors' names are open (they must not clash with `Sharing`'s
  `Unique` or with the annotation tokens).
- `JMEq`: Decided. It is in the source prelude.
- `Const`: Decided that it is opaque and not an ADT, like `Slot`: no
  constructors, no `Matchable`, not erased by kind. A handle
  `(Const m T t)` denotes `t`, held at multiplicity `m`. Decided that its
  run-time value may be a term rather than an entry id, and that an `MMany`
  handle carries the value it denotes; proposed that the rest is a closed
  term over run-position entries.
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
    (many AConst : (erased (Mult) m) (erased Type A) (erased A a) (many (Const m A a) c) -> (Atom)))
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
- `AConst` is itself the existential over `m`, `A` and `a` (Decided; an
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
(constant-of m x)  : (many (Const m' T t) h)
    ; x a Const entry; T its minted type; t its minted is; m erased: any entry;
    ; many: x declared many; unique: x declared unique; m' the matching Mult
(constant-type c)  : (erased (Mult) m) (erased Type T) (erased T t) (many (Const m T t) c) ->
                     (many (Const (MErased) Type T) h)
(const-mult c)     : (erased (Mult) m) (erased Type T) (erased T t) (many (Const m T t) c) ->
                     (many m is r)
(const-value c)    : (erased Type T) (erased T t) (many (Const (MMany) T t) c) -> (many t is v)
```

All Decided. Decided: a handle denotes `x`'s minted `is` at `x`'s minted
type (DESIGN.md §5, §29), as head dispatch reads the minted type (§6). There
is no `const-value` for erased handles (it would only rename the handle's own
erased index) and none for unique handles (a macro's read would happen
outside the elaborator's use accounting, possibly after the value was
consumed and mutated in place). A `constant-slot` form was considered and
dropped.

### The macro world

```scheme
(const-eq mw p q)     : (unique (MacroWorld) mw) (many (Const ma A a) p) (many (Const mb B b) q) ->
                        (unique mw is mw2 at mw) (many (Maybe (JMEq A a B b)) r)
(gensym mw s)         : (unique (MacroWorld) mw) (many (String) s) ->
                        (unique (MacroWorld) mw2 at mw) (many (Nat) n) (erased (Gensym n s) g)
(gensym-unique n s t a b) : (erased (Nat) n) (erased (String) s) (erased (String) t)
                        (erased (Gensym n s) a) (erased (Gensym n t) b) ->
                        (erased (JMEq (Gensym n s) a (Gensym n t) b) e)
(intern-nat mw n)     : (unique (MacroWorld) mw) (many (Nat) n) ->
                        (unique (MacroWorld) mw2 at mw) (many (Const (MMany) (Nat) n) h)
(intern-char mw c)    : (unique (MacroWorld) mw) (many (Char) c) ->
                        (unique (MacroWorld) mw2 at mw) (many (Const (MMany) (Char) c) h)
(intern-string mw s)  : (unique (MacroWorld) mw) (many (String) s) ->
                        (unique (MacroWorld) mw2 at mw) (many (Const (MMany) (String) s) h)
(read-file mw path)   : (unique (MacroWorld) mw) (many (String) path) ->
                        (unique (MacroWorld) mw2 at mw) (many (Result (String)) r)
    ; read-file is jailed: after resolving symlinks, the path must lie in the directory, or a
    ; subdirectory, of at least one of the program's source files; any other path answers Fail
```

- `const-eq`: Decided. Proposed: it answers from run-position facts only,
  never branch-forced ones, so that a `Just` stays true wherever the
  macro's output goes and a call expands the same way in every branch.
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
   `m` of `(constant-of m x)`. Where it is spliced, it is checked as if `x`
   had been written there with that multiplicity. So an `MErased` handle may
   appear only in erased positions, an `MMany` handle is used at many, and an
   `MUnique` handle is used at unique, which consumes it. Decided: a handle
   cannot be used as a binder, any more than anything else that is not a
   name can. Proposed: an `AConst` resolves to its term directly, bypassing
   scope; in a non-erased position it must be an entry.
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
- `const-eq` answers `Just` only from facts that hold unconditionally.
- A handle denotes its index because only built-in forms create handles.
- A gensym cannot be forged: building an `SGen` at `many` needs an erased
  `Gensym` witness, and only `gensym` makes one.

The owner suspects this section holds of the language as it stands.

## 6. Open questions

1. The names of `Mult` and its constructors, and `Const`.
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

(def-opaque $ (Const : ((Mult) m) (Type T) (T t) -> Type))

(def-prim $ (many gensym : (unique (MacroWorld) mw) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Nat) n) (erased (Gensym n s) g)))

(def-prim $ (erased gensym-unique : (erased (Nat) n) (erased (String) s) (erased (String) t)
    (erased (Gensym n s) a) (erased (Gensym n t) b) ->
    (erased (JMEq (Gensym n s) a (Gensym n t) b) e)))

(def-prim $ (many const-mult : (erased (Mult) m) (erased Type T) (erased T t) (many (Const m T t) c) ->
    (many m is r)))

(def-prim $ (many const-value : (erased Type T) (erased T t) (many (Const (MMany) T t) c) -> (many t is v)))

(def-prim $ (many intern-nat : (unique (MacroWorld) mw) (many (Nat) n) ->
    (unique (MacroWorld) mw2 at mw) (many (Const (MMany) (Nat) n) h)))

(def-prim $ (many intern-char : (unique (MacroWorld) mw) (many (Char) c) ->
    (unique (MacroWorld) mw2 at mw) (many (Const (MMany) (Char) c) h)))

(def-prim $ (many intern-string : (unique (MacroWorld) mw) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Const (MMany) (String) s) h)))

(def-adts $ (Raw : -> Type)
  enum extern
  (many RawName : (many (Pos) pos) (many (String) name) -> (Raw))
  (many RawNat : (many (Pos) pos) (many (Nat) n) -> (Raw))
  (many RawChar : (many (Pos) pos) (many (Char) c) -> (Raw))
  (many RawStr : (many (Pos) pos) (many (String) s) -> (Raw))
  (many RawWild : (many (Pos) pos) -> (Raw))
  (many RawList : (many (Pos) pos) (many (List $ Raw) items) -> (Raw))
  (many RawGen : (many (Pos) pos) (many (Nat) n) (many (String) s) (erased (Gensym n s) g) -> (Raw))
  (many RawConst : (many (Pos) pos) (erased (Mult) m) (erased Type A) (erased A a) (many (Const m A a) c) -> (Raw)))

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
scope" hint. `(constant-of m x)` makes a handle (section 3), and
`RawConst` puts one in a macro's output, where it stands for its entry
directly. `const-mult` and `const-value` read a handle anywhere, not only
during an expansion, and an `MMany` handle carries its value into an
extracted program. The `intern-` forms run only in an expansion, the one
place a macro world exists. `constant-type` and `const-eq` are not
implemented, and a literal in a macro's arguments still arrives as
`RawNat`, `RawChar` or `RawStr`.
