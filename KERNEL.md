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

## The comptime round-trip

§16's `comptime` and §9's macros need values only running code can
produce, so checking is a dialogue: the kernel checks a comptime
expression and computes its type, returning runnable code with erased
positions removed; the interpreter runs that code outside the kernel;
the resulting values come back to be stored (§3) and embedded as
constants.

Round-trips nest: elaborating a comptime expression can hit a macro,
itself a round-trip.

In v1 a macro is `List Raw -> Raw` (§9), so expanding one is that
round-trip with result type `Raw`.
