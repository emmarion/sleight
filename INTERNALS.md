# Internals

This file describes the forms that declare what the compilers supply.
Only the source prelude may write them, or a program run with
`--no-prelude`, which takes on the prelude's role. DESIGN.md is the
specification of the language a program is written in; this file is
the contract between the prelude and the compilers. Its sections are
cited by number.

## 1. Opaque types

`(def-opaque (T : params -> Type) ...)` binds each `T` as a type
constructor with no constructors and no `Matchable`, like `Level` or
`World` (DESIGN.md §8): it is never opened, so it is neither matchable
nor empty.

## 2. Primitives

`(def-prim (m p : params -> returns) ...)` gives a signature to `p`,
which must be the name of a constructor of `Special` that the
compilers implement as a primitive; `m` is `many` or `erased`.
`Special` is unchanged by it: `p` is a nullary constructor of
`Special` from the start, like `let`, and using it before its
`def-prim` is an error. A call of a primitive is elaborated as a call
is, with no level and so no `predates` or `subterm` annotation, and
runs the compilers' implementation; a primitive whose returns are all
erased is an axiom and has none. Declaring a primitive the compilers
do not implement, a second time, or with a non-erased return when the
compilers have no implementation of it, is an error. Whatever a
primitive promises, a callback included, is the prelude's promise.
The primitives are `gensym` and `gensym-unique` (MACROS.md).
A `def-prim` entry is written like a `def-fns` header and a
`def-opaque` entry like a `def-adts` header alone. A primitive's
parameters may not be marked `subterm`. A primitive declared `erased`
has every return erased where it is called. A primitive's call that an
extracted program reaches is a crash.
