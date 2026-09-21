# B1. Discriminant-free values print differently in the interpreter and extracted code

Status: resolved. The owner decided the rendering in chat; ASSUMPTIONS
184 records it and the implementation follows. Kept as the record of what
was found.

## The rule

Neither DESIGN.md nor UNIQUE.md says what a value of a type with no
runtime discriminant, a `union` or a newtype with several constructors,
prints as. Section 16 says the top level's value is "simply the value a
REPL would print"; ASSUMPTIONS 66 and 154 describe the printer for tagged
types and literals.

## The observation

Three answers exist today. The interpreter's typed printer renders the
first unrefuted candidate; when that candidate's arity does not match the
value's it raises, and the untyped fallback prints whatever the block's
constructor record says. The extracted program (after F8) always renders
the first candidate. The self-hosted compiler does the same as the
extracted program.

| program | interpreter | extracted |
|---|---|---|
| `union`, both constructors one field, value `UB` | `1` | `1` |
| `union`, constructors of arity 0 and 1, value `UB` | `(UB (Succ (Zero)))` | `_` |
| F9's cycle program | `(UC1 (ACons <cycle> (ANil)))` | `_` |
| `MaybeUninit` | `_` | `_` |

The interpreter's apparently better answer in the second row is an
accident of the fallback, and in the first row it silently prints the
wrong constructor's rendering. A union carries no tag, so no extracted
program can do better than a fixed choice.

## Reproducer

```scheme
(def-adts $ U : -> Type union
  (many UA : -> (U))
  (many UB : (many (Nat) n) -> (U)))
(UB (Succ (Zero)))
```

## Candidate resolutions, none chosen

Always the first unrefuted candidate, which is what F8 and self do;
always `"?"` for a discriminant-free type with several candidates; or the
newtype's field alone. Whichever is chosen, the interpreter's typed
printer and `Value.show` should give one answer so no test can depend on
the fallback.

## Resolution

The owner chose none of the three candidates below. The rule decided
instead (ASSUMPTIONS 184) is that the constructor is read off the
Matchable and never by refuting candidates: a tagged enum by its tag, a
type with exactly one non-phantom constructor by that constructor, and a
union with two or more by nothing -- it prints `_`. So the divergence
cannot recur, there being no candidate list whose length the two back
ends could treat differently, and the untyped `Value.show` fall-through
the interpreter reached is gone, every case of the rule having an answer.

A second divergence of the same shape turned up while settling this and
is covered by the same rule: a non-erased field of existentially
quantified type, `(many MkDyn : (erased Type A) (many A value) -> (Dyn))`
with `(MkDyn _ 5)`, printed `(Succ (Succ (Succ (Succ (Succ (Zero))))))`
in the interpreter, through that same fall-through and spelling the
zarith word as its Peano model for want of a type, and `?` extracted. It
now prints `(MkDyn _ _)` in both.
