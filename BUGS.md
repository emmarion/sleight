# Bugs

Defects found in the implementation, for the owner to get to. Written by
Claude sessions; each entry says how it was reproduced, and nothing here
is a design decision. Remove an entry when it is fixed.

1. **`array-new` beyond the host's limits escapes as an OCaml exception.**
   `(array-new (Nat) 100000000000000000)` dies with
   `Fatal error: exception Invalid_argument("Array.make")`, and a larger
   literal with `Z.Overflow`, in the interpreter and the extracted
   program alike: `Ffi_core.array_new` guards neither `Z.to_int` nor
   `Array.make`, and neither exception is one `Program.explain` reports.
   What such a call should do is undecided (ASSUMPTIONS 183).

2. **A `tail` mark is refused in a function whose returns are all
   erased.** With `g : (unique (Nat) x) -> (unique (Nat) r at x)`, the
   body `(let (unique y) (tail (g x))) (Zero)` of a function returning
   `(erased (Nat) e)` is refused as not in tail position: `project_code`
   short-circuits on an empty list of kept results, so the trailing erased
   code never becomes `(values)` for `check_marks` to fold. Such a
   function is only ever called erased, so nothing runs wrongly.
