; error: has no Newtype in scope
; A phantom constructor with a many field is not the newtype's wrapper, so no Newtype names it (section 38): no non-erased
; value is headed by it, and wrapping through it would let coerce produce one, whose match would reach absurd code.

(def-adts $ T : -> Type
  enum newtype
  (many MkT : (many (Nat) n) -> (T))
  (erased Ghost : (many (Nat) n) -> (T)))

(let (many one) (Succ (Zero)))
(let (many (T) g) (coerce one (coercible-wrap Ghost one)))
(match many g (((Nat) r))
  (absurd MkT)
  ((Ghost n) n))
