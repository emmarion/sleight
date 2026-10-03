; error: not of newtype shape
; A non-phantom union constructor with two many fields cannot be marked newtype.

(def-adts
  ((Both : ((Bool) tag) -> Type)
    union newtype
    (many BL : (many (Nat) n) (many (Nat) m) -> (Both (BTrue)))
    (many BR : (many (Bool) b) -> (Both (BFalse)))))
