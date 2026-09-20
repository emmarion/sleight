# B2. `array-new` beyond the host's limits escapes as an OCaml exception

Status: open defect, BUGS.md 2. Severity: crash, low.

## The rule

DESIGN.md section 41 and ASSUMPTIONS 168 say nothing about a length the
host cannot allocate. Every other failure the driver reports goes through
`Program.explain`.

## The observation

`Ffi_core.array_new` does `Z.to_int n` then `Array.make`, unguarded.
Neither `Z.Overflow` nor `Invalid_argument` is an `Eval.Runtime` or an
`Env.Error`, so the exception escapes the driver in the interpreter and,
since the extracted program calls `Ffi_core` directly, there too.

## Reproducer

```scheme
(let (unique a) (erased all) (array-new (Nat) 100000000000000000))
(let (many s) (SlotHolds a))
s
```

`Fatal error: exception Invalid_argument("Array.make")`; with a larger
literal, `Z.Overflow`.

## Why no fix

Catching it in `lib/ffi.ml` alone would make the interpreter and the
extracted program disagree, and what such a call should do, a reported
runtime failure, an exit code, or an out-of-range refusal by the model, is
undecided. The stripped model, `n` `ACons` constructions, would simply run
out of memory.
