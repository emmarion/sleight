; error: has no opened newtype `Matchable`
; warns: tests/wrap_phantom_bad.sl:7:3: warning: phantom constructor `Ghost` has a non-erased field

(def-adts $ (T : -> Type)
  enum newtype
  (many MkT : (many (Nat) n) -> (T))
  (erased Ghost : (many (Nat) n) -> (T)))

(let ((many one)) (Succ (Zero)))
(let ((many (T) g)) (coerce one (coercible-wrap (Shared) Ghost one)))
(match many g (((Nat) r))
  (absurd MkT)
  ((Ghost n) n))
