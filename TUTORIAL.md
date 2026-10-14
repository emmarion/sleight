# A short tour of Sleight

The language is specified in [DESIGN.md](DESIGN.md); [README.md](README.md)
describes the implementations and their command lines.

This tutorial was written by a Claude session, not by the owner.
DESIGN.md is the specification. Where the two disagree, DESIGN.md is right
and this file is wrong. Each program below is a test in [`tests/`](tests/),
named under its listing, so `dune test` and
[`self/bootstrap.sh`](self/bootstrap.sh) check it. The prose around the
programs is a session's reading of DESIGN.md, and any part of it could be
wrong. The section numbers (§) point to the DESIGN.md text it is based on.

## 0. Running a program

```sh
dune build
dune exec bin/main.exe -- tests/tutorial_color.sl
```

A file is a list of statements, optionally followed by one final
expression, which the driver prints (§27). Each top-level form runs as
soon as it has been checked, before the next one is read (§27, §29), so
the top level behaves like a REPL that checks types.

## 1. S-expressions, and `$`

The syntax is s-expressions (§1). The one addition is `$`. It opens a
list that closes where the enclosing list closes (§2), so

```scheme
(Cons _ 1 $ Cons _ 2 $ Nil (Nat))
```

is `(Cons _ 1 (Cons _ 2 (Nil (Nat))))`. `;` starts a comment.

## 2. Data types

```scheme
(def-adts $ (Color : -> Type)
  enum
  (many Red : -> (Color))
  (many Green : -> (Color))
  (many Blue : -> (Color)))

(def-fns _ $ (many next : (many (Color) c) -> (many (Color) d))
  (match many c _
    ((Red) (Green))
    ((Green) (Blue))
    ((Blue) (Red))))

(next $ next (Red))
```

[`tests/tutorial_color.sl`](tests/tutorial_color.sl) prints `(Blue)`.

Some things to notice:

- `def-adts` declares a type constructor, `Color : -> Type`, and its value
  constructors. Each constructor has a signature that ends in its own
  type (§21).
- `enum` means a value carries a runtime tag. The alternative, `union`,
  has an erased tag, so a runtime match on one may have only one real
  branch (§21).
- The word `many` appears all over. It is a **multiplicity**, and every
  binder has to state one (§13). See section 4.
- `def-fns _ $ (...)` defines functions. The `_` is the function's
  **level** (section 3). The signature is
  `name : params -> returns`, and both sides are telescopes of
  `(mult Type name)` entries, with the type before the name (§3).
- `(match many c _ branch ...)` matches `c` at multiplicity `many`. The
  `_` is the result annotation, which can be left out when the position
  already says what is wanted, as a function body's final expression does
  (§26, §47).
- Constructors are applied like functions, so a nullary one is written
  `(Red)`.

The prelude ([`lib/prelude.sl`](lib/prelude.sl)) already has `Nat`, `Bool`, `Maybe`,
`List`, `Pair`, `String` and more (§42). Numerals such as `42` are `Nat`s
(§45).

## 3. Recursion, and why every function has a level

There is no general recursion. Each function has a **level**, and a
function may call (§17):

- a function at a strictly lower level, or
- a function at its own level, but only with a smaller argument in a
  parameter marked `subterm` (§17, §19).

Together these make every call decrease, so every function terminates.

```scheme
(def-fns _ $ (many sum : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) 0)
    ((Cons _ hd tl) (nat-add hd $ notail $ sum tl))))

(sum $ Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Nil (Nat))
```

[`tests/tutorial_sum.sl`](tests/tutorial_sum.sl) prints `6`.

- `xs` is marked `subterm`. In the `Cons` branch, `tl` is a strict
  subterm of `xs`, so `sum tl` is allowed.
- In full, the recursive call carries a proof: `(sum (subterm p) tl)`,
  where `p` comes from `(prove-subterm tl xs)` (§18, §56). Written bare,
  the elaborator builds that proof itself (§48). It does the same for
  `nat-add`, which is at the prelude's `nat-lvl`. That level is lower
  than `sum`'s, so the call gets `(predates _)` (§19, §48).
- `_` as the level makes a fresh level just above the block (§46). A
  level made later is higher, so `sum` can call anything defined before
  it.
- The top level has no level, and it may call anything with no proof
  (§20).
- `notail` claims that the call is *not* a tail call. `tail` claims that
  it is. A claim the compiler cannot honour is an error (§19). The
  compiler warns about an unmarked same-level call, which is why `notail`
  is written here.

Leave the decrease out and the call is refused:

```scheme
(def-fns _ $ (many loop : (subterm many (Nat) n) -> (many (Nat) m))
  (notail $ loop n))
```

```
error: same-level call to `loop` decreases no subterm argument
```

([`tests/tutorial_loop_bad.sl`](tests/tutorial_loop_bad.sl))

### Higher-order functions

A function value's type records its level: `(Fn L params -> returns)`
(§11). So whoever calls `f` must be above `f`'s level:

```scheme
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(def-fns _ $ (many twice : (many (Fn (level-of inc) (many (Nat) x) -> (many (Nat) y)) f)
    (many (Nat) n) -> (many (Nat) m))
  (f $ f n))

(twice inc 5)
```

[`tests/tutorial_twice.sl`](tests/tutorial_twice.sl) prints `7`. The type of `f` names a level that
existed before `twice`'s was made. If you try to abstract over the level
as a parameter, it fails, because the parameter did not exist when
`twice`'s level was made (§18, §57):

```scheme
(def-fns _ $ (many twice : (erased (Level) L) (many (Fn L (many (Nat) x) -> (many (Nat) y)) f)
    (many (Nat) n) -> (many (Nat) m))
  (f $ f n))
```

```
error: `L` was not in scope when level `(level-of twice)` was minted
```

([`tests/tutorial_level_bad.sl`](tests/tutorial_level_bad.sl)) The way to get a level-polymorphic `map`
is a *factory* function. It takes the level, makes a new level above it
inside its own body, and returns the `map` defined there. §57 and §58
show this, and [`tests/map.sl`](tests/map.sl) runs it.

## 4. Multiplicities: `erased`, `many`, `unique`

Every binder states one of three multiplicities (§13, §14):

- `erased`: exists only for the type checker and is gone at runtime.
  Types, proofs and levels are erased.
- `many`: an ordinary runtime value that can be used any number of times.
- `unique`: a runtime value that has to be used exactly once, or only
  through `share` (section 7).

Erasure is never inferred. It is fixed at each binder, and the checker
enforces it locally (§14):

```scheme
(def-fns _ $ (many oops : (erased (Nat) n) -> (many (Nat) m))
  n)
```

```
error: `n`, declared `erased`, used in a non-erased position
```

([`tests/tutorial_erased_bad.sl`](tests/tutorial_erased_bad.sl)) This is why `List`'s constructors take an
`(erased Type A)` first: the element type is an argument, but it costs
nothing at runtime. In a call, an erased argument that the other
arguments determine can be written `_` (§50). That is why
`(Cons _ 1 ...)` above needs no `(Nat)`.

## 5. Dependent types, and branches that can't happen

Types can be indexed by values. A vector indexed by its length:

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

[`tests/tutorial_vec.sl`](tests/tutorial_vec.sl) prints `10`.

- The index `n` is erased, so the length costs nothing at runtime.
- `let-match` takes a value apart and binds its fields for the rest of
  the body. It is allowed only when exactly one constructor survives
  (§27). `VNil` would need `(Succ n)` to equal `(Zero)`. Those are two
  distinct constructors of one type, so that branch is refuted (§7, §8),
  and `vhead` needs no case for the empty vector.
- In a `match`, a refuted constructor needs no branch either. One can
  still be written as `(absurd C)` for documentation (§21).

Types are checked by *canonicalizing and comparing* (§9). The checker
never runs your code to compare types (§29). It knows only what
constructors, `is` facts and matches tell it.

## 6. Proofs as values

The prelude's arithmetic returns its own specification. `sub` subtracts
exactly. It needs an erased proof that `b ≤ a`, and it returns an erased
`(Add b c a)` with the result (§42):

```
sub : (many (Nat) a) (subterm many (Nat) b) (erased (Lt b (Succ a)) le) ->
      (many (Nat) c) (erased (Add b c a) p)
```

Proofs are ordinary data of erased types, such as the prelude's `Lt`,
and they are passed and returned like any other value. Here is truncated
subtraction, which gets its proof by deciding the comparison:

```scheme
(def-fns _ $ (many monus : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec a b) (No _ _ q) ((Yes _ _ _) 0))
  (let ((many c) (erased _)) (sub a b q))
  c)

(MkPair _ _ (monus 3 10) (monus 10 3))
```

[`tests/tutorial_monus.sl`](tests/tutorial_monus.sl) prints `(MkPair _ _ 0 7)`. (Erased fields print
as `_`.)

- `lt-dec` returns `(Dec a b)`: either `Yes` with an `(Lt a b)`, or `No`
  with an `(Lt b (Succ a))`.
- This `let-match` has an extra branch. The `Yes` case returns `0`
  straight away, and the `No` case continues with the rest of the body,
  holding `q` (§52).
- A function can return several values. `let` binds them one by one, here
  `c` and an erased proof that is dropped (§26).

Without the proof, the call is refused. A proof argument can't be
inferred from nothing:

```scheme
(def-fns _ $ (many bad-sub : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let ((many c) (erased _)) (sub a b _))
  c)
```

```
error: argument 3, `le`, of `sub` is `_` and cannot be inferred
```

([`tests/tutorial_sub_bad.sl`](tests/tutorial_sub_bad.sl))

### Proof by running code

The top level runs as it goes, so a proposition the prelude can decide
can be proved by computing it there and asserting the outcome with
`comptime-match` (§28):

```scheme
(let ((many d)) (lt-dec 10 3))
(comptime-match many d (No _ _ q))
(let ((many c) (erased p)) (sub 10 3 q))
c
```

[`tests/tutorial_reflect.sl`](tests/tutorial_reflect.sl) prints `7`. `comptime-match` fails to compile
unless `d` really is a `No`, and it binds that `No`'s proof `q` for the
code after it. A hand-built `U8` gets its bound proof this way (§42).

## 7. Unique values and updates in place

A `unique` binder is the only reference to its value, so the value can
be overwritten instead of copied (§13, §15). When a `unique` value is
destructured at `unique`, the pattern can name one more binder, the
**cell** the value occupied. Applying the cell like a constructor builds
the new value in that same memory (§23, §37):

```scheme
(def-adts $ (Counter : -> Type)
  enum
  (many MkCounter : (many (Nat) n) -> (Counter)))

(def-fns _ $ (many bump : (unique (Counter) c) -> (unique (Counter) d at c))
  (match unique c _
    ((MkCounter n cell) (cell (nat-add n 1)))))

(let ((unique c0)) (MkCounter 0))
(let ((unique c1)) (bump c0))
(let ((unique c2)) (bump c1))
(share c2)
```

[`tests/tutorial_counter.sl`](tests/tutorial_counter.sl) prints `(MkCounter 2)`.

- `(unique (Counter) d at c)` promises that the result is at the same
  address as the argument (§36). The checker checks that promise.
- The uniqueness is a property of the binder, not of the type: `Counter`
  is an ordinary type, and the same value could be built at `many`
  (§13).
- `share` turns a unique value into a `many` one. You have to write it
  out, and after it the value can never be used as unique again (§16).
  The final value here is printed at `many`, so it is written
  `(share c2)` (§27).

The checker counts uses on each path through the code (§15):

```scheme
(def-fns _ $ (many twice : (unique (Counter) c) -> (unique (Counter) d) (unique (Counter) e))
  (values c c))
```

```
error: unique value `c` has conflicting non-erased uses
```

([`tests/tutorial_unique_bad.sl`](tests/tutorial_unique_bad.sl)) The prelude's arrays and byte buffers
use the same machinery, and so does the destination-passing `append` of
§61 ([`tests/cell_append.sl`](tests/cell_append.sl)).

## 8. Newtypes and free coercions

A type marked `newtype` is represented exactly as its one runtime field
(§21, §33). Rewrapping is free, but you need an erased proof that it is
safe:

```scheme
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let ((many m)) (MkMeters 42))
(let-match many m (MkMeters n))
(coerce m (coercible-sym (coercible-wrap (Shared) MkMeters n)))
```

[`tests/tutorial_newtype.sl`](tests/tutorial_newtype.sl) prints `42`. `coercible-wrap` proves that `n`
can be wrapped as `(MkMeters n)`, and `coercible-sym` reverses that proof
into unwrapping. `coerce` applies the proof at no runtime cost (§33).
The point is that this works through containers: §60 turns a
`(List (Meters))` into a `(List (Nat))` with an erased recursive proof
and one `coerce` that compiles to nothing ([`tests/coerce.sl`](tests/coerce.sl)).

## 9. Talking to the world

A final expression of type `String -> String` is run on standard input,
and its result is written to standard output (§27):

```scheme
(def-fns _ $ (many main : (many (String) in) -> (many (String) out))
  (str-append "Hello, " $ str-append in "!\n"))

main
```

```sh
printf world | dune exec bin/main.exe -- tests/tutorial_hello.sl
Hello, world!
```

([`tests/tutorial_hello.sl`](tests/tutorial_hello.sl)) For real interaction, the final value is a
`(Program L)`. A step is a unique continuation that takes the unique
`World`, performs requests with `world-do`, and returns the next step
or `Exit` (§42):

```scheme
(def-lvl P)
(let ((many d)) (lt-dec 0 u8-modulus))
(comptime-match many d (Yes _ _ p))
(let ((many ok)) (MkU8 0 p))

(def-unique P $ (unique start : (unique (World) w) ->
    (unique (World) w2 at w) (unique (Program P) next))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut "Hello, world!\n")))
  (values w1 (Exit P ok)))

(Continue P start)
```

([`tests/tutorial_program.sl`](tests/tutorial_program.sl)) The first four lines build the exit code.
A `U8` carries a proof that it is below 256, which is obtained here by
reflection as in section 6. `def-unique` defines a function that may be
called only once (§32), and that is what lets the driver hand each step
the one `World`. [`tests/io_echo.sl`](tests/io_echo.sl) loops over input lines.

## Where next

- [EXAMPLES.md](EXAMPLES.md) lists the tests that show the features working together.
- [DESIGN.md](DESIGN.md) §55 to §61 are worked examples. §62 to §65 cover macros,
  which are ordinary functions over syntax, run during elaboration.
- [`std/`](std/) holds more lemmas and proof tactics.
- `(dump-context)` stops the checker and shows everything it knows at
  that point ([README.md](README.md)). It helps when a proof won't go through.
