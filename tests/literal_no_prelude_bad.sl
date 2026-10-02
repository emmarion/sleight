; prelude: none
; A numeral denotes the prelude's own Nat (LITERALS.md), so without the prelude it is refused at the literal,
; even where the program declares a Nat of its own.
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(let ((many x)) 0)
x
; error: tests/literal_no_prelude_bad.sl:5:17: error: a numeral needs the prelude's `Nat`, which `--no-prelude` leaves out
