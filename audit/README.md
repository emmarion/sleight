# Audit of the uniqueness implementation

One file per item found when the implementation of UNIQUE.md, commits
`8091d86..73dae6b` by Codex/Astra, was checked against DESIGN.md and
UNIQUE.md section by section with adversarial programs, in the
interpreter, the extracted OCaml and the self-hosted compiler. Written by
a Claude session; each file says what the spec says, what was observed,
how to reproduce it, and what was done. Nothing here is a design
decision; where a fix rests on a reading, the file says so and names the
alternative. ASSUMPTIONS 182 and 183 and BUGS.md carry the same items in
summary.

Fixed in `fa5747a`, each with a test under `tests/`:

- F1. An `at` return reconstructed from an erased binder's word
- F2. Self `let-match many` hands a unique-labelled field out at unique
- F3. A newtype application in an erased position refused as a non-variable location
- F4. `coercible-of` fetches the newest anonymous proof, shadowing the delegate proof
- F5. A size-zero position treated as erased (a reading)
- F6. A type former's head recorded as a use, inconsistently (a reading)
- F7. A zero-binder `let` inside a body drops its right-hand side's code
- F8. The extractor asserts false printing a union or newtype value
- F9. The untyped printer overflows the stack on a cycle through a slot word

Defects. B2 and B3 are also in BUGS.md; B1's entry was removed from there
when it was fixed, as was its file here:

- FIXED B1. Discriminant-free values print differently in the interpreter and extracted code
- B2. `array-new` beyond the host's limits escapes as an OCaml exception
- B3. `tail` refused in a function whose returns are all erased

Open questions for the owner, also in ASSUMPTIONS 183:

- Q1. `comptime-match many` on a unique Const cannot write its `share`
- Q2. An erased-position `unique` match mints `SlotHolds` over erased binders
- Q3. Structural Matchable marks prevent abstracting over extern and non-extern
- Q4. `coercible-wrap (Unique)` over a many-labelled field mints unique aliases
- Q5. Slot-indexed user types reach U10's class merge, U15's deferred question
- Q6. U13's text as written needs two repairs to elaborate

Minor observations, not acted on:

- M1. `matchable-of` records no use of the Matchable entry
- M2. `read_special`'s share branch lacks the erased-position guard
- M3. ML and self give different messages for some refusals
- M4. The phantom-with-unique-field warning text says "many field"
- M5. `_` not accepted as a `Cell` slot in a type
- M6. `at_equal` structural in ML, variable-only in self
- M7. Stale comments say "many fields" where the code counts non-erased
- M8. `Ffi.claim_fn` never checks an implementation's result count
- M9. `--no-templates` is a vacuous check for arrays
- M10. Stripped-extern `array-new` is quadratic
- M11. An extern's signature is elaborated outside the extern body's cell context
- M12. `coerce` via the sym of a delegate proof mints a unique alias of a shared Fn

What was checked and found correct is not itemised here; the coverage
was every rule of U1 to U14 that could be turned into a program, roughly
two hundred probes, with no way found in the reference implementation to
hold two live non-erased references to one block, pass a false `at`
promise, read an `Uninit` word, or mutate a shared cell.
