; prelude: none
; A string literal denotes the prelude's String (DESIGN.md section 45), so without the prelude it is refused at the literal.
(def-adts $ (Unit : -> Type) enum (many MkUnit : -> (Unit)))
(let ((many u)) (MkUnit))
"ab"
; error: tests/literal_no_prelude_string_bad.sl:5:1: error: a string literal needs the prelude's `String`, which `--no-prelude` leaves out
