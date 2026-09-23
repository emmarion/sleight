; error: constructor `TB` has 0 branches
; error: #\a is a character literal, whose code is opaque to the checker
; A character literal is transparent down to its code, a numeral (LITERALS.md), so the note names the
; character as written rather than its code.

(def-adts ((Tag : ((Char) c) -> Type)
  enum
  (many TA : -> (Tag #\a))
  (many TB : -> (Tag #\b))))
(def-lvl X)
(def-fns X $ (many only-a : (many (Tag #\a) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((TA) (Zero))))
(only-a (TA))
