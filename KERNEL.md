# Kernel and elaborator

DESIGN.md records the language; this file records how the implementation
is split.

## The boundary

The kernel is the trusted core: nothing enters the scope environment (§3)
that is not well-typed and terminating, whatever the elaborator hands it
— type preservation, §§7–8's level/subterm decrease, §23's erasure
conservativity. Logical consistency is the goal (§10), resting on that
termination check and §5's ban on computation in types rather than on
universe stratification or positivity. What the kernel cannot guarantee
is that the core it accepts means what the source said.

The reader, macro expander, elaborator, eraser, interpreter and code
generation are untrusted. So `Raw` and §27's `Special` registry are not
kernel types, and §9's macro-expansion limit belongs to the elaborator.

## The compile-time round-trip

§16's run-position statements and §9's macros need values only running
code can produce, so checking is a dialogue: the kernel checks a
statement and computes its type, returning runnable code with erased
positions removed; the interpreter runs that code outside the kernel;
the resulting values come back to be stored (§3) and embedded as
constants.

Round-trips nest: elaborating a statement can hit a macro, itself a
round-trip, or a nested statement in run position, run before the code
after it is checked and so before the enclosing statement's own trip.

The dialogue runs both ways: besides sending checked code out to the
interpreter, the elaborator reads stored values back out of the scope
environment — head dispatch (§4) needs the actual `Special` or `Macro`
value of a `Const`, non-erased head. A statement's boundary erasures
are declared on its binders (§9, §34), so nothing about a statement's
erasure depends on code after it.

In v1 a macro is `List Raw -> Raw` (§9), so expanding one is that
round-trip with result type `Raw`.

## Interpreter trust

The interpreter is untrusted for *semantics* but currently trusted for
*facts*: every fact born from a stored value (`comptime-match`, and
anything downstream of a value it bound) assumes the interpreter
evaluated correctly. The assumption is not free. Consider

```scheme
(def-adts $ Maybe : -> Type
  enum
  (many T : -> (Maybe))
  (many F : (erased (False) f) -> (Maybe)))
```

An honest program can only ever build `(T)`. A lying interpreter
returns the `F` tag — and the erased proof field costs nothing to
forge, because erased positions are stripped before it runs: there are
no bytes to be wrong. A `comptime-match` asserting `F` then births a
`(False)` token into scope, and consistency (§10) is gone. Erasure
makes the forgery undetectable by construction, so §10's goal
ultimately requires closing this: a small reference evaluator inside
the kernel (the language is total, pure, and eager, so this is a
modest recursive function over constructor trees) used as the arbiter
for fact-bearing round trips. Recorded as a v2 obligation, load-bearing
for §10, not merely an optimization concern.
