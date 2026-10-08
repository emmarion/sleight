; error: not of newtype shape
; A union newtype's non-phantom constructor must hold a non-erased field (section 21).

(def-adts
  ((Opt : ((Bool) k) -> Type)
    union newtype
    (many Wrapped : (many (Nat) x) -> (Opt (BTrue)))
    (many Nothing : -> (Opt (BFalse)))))
