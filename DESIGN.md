# Language design notes

Design decisions here come directly from the repo owner. This file is a
running record, added to as design sessions happen.

## 1. Syntax

Scheme syntax (s-expressions).

## 2. `$` for closing-paren reduction

Borrowed from Haskell's `$`. A `$` acts as an open parenthesis *and* an
automatic closing parenthesis: it closes right where the form it opens
would otherwise need an explicit `)`. Parentheses are balanced in valid
source even if `$` is ignored/stripped out. Used aggressively, `$` could
in principle reduce any run of closing parens down to at most one — that
may be more than we actually want stylistically, to be decided.

## 3. Scope environment

The scope environment is a list of variables (shadowing allowed). Each
variable is in exactly one of three states:

- **comptime**: has a stored type, a stored *value*, and an "is"
  statement (a canonicalization/rewrite rule introduced via matching on
  a dependent type).
- **dynamic**: has a stored type and an "is" statement, but no stored
  value.
- **inacc** (inaccessible): same shape as dynamic (type + "is"
  statement), but the variable cannot be accessed at all — the
  motivating case is a dynamic variable from an enclosing scope becoming
  inaccessible inside a comptime block.

## 4. Orthogonality: Kernel-level dynamism with static types

Goal: match Kernel's level of dynamism while still supporting clean
compilation with static types. The mechanism for reconciling these is
analyzing the *constantness* of the head of an s-expression:

- Macros and special forms are first-class values — they can be passed
  around at runtime like any other value.
- To actually *invoke* something as a macro/special form (as opposed to
  merely holding it as a value), the head of the s-expression must be
  constant-known.
- Constant-known-ness is relative to where you are: something can be
  dynamic while evaluating inside a comptime block, yet become
  constant-known once evaluation leaves that block.

## 5. Restricted dependent types

Dependent types are supported, but restricted: a type may never involve
function invocation. A type can only be built from:

1. variable references,
2. application of a type constructor,
3. application of a value constructor.

The same restriction applies to "is" statements (the
canonicalization/rewrite rules from §3). The intended consequence of this
restriction is a simple type-checking rule: canonicalize, then compare
for identity.

## 6. Erasure

Erasure follows Idris 2's approach, living on the binding — i.e. the 0/ω
multiplicity distinction from Idris 2's quantitative type theory.
Linear/unique types are punted on for now.
