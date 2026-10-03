; error: has no opened newtype
; A union newtype's fieldless constructor is not a wrapping constructor (section 38).

(def-adts
  ((Opt : ((Bool) k) -> Type)
    union newtype
    (many Wrapped : (many (Nat) x) -> (Opt (BTrue)))
    (many Nothing : -> (Opt (BFalse)))))

(coercible-wrap (Shared) Nothing)
