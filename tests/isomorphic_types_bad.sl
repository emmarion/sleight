; error: not refuted
; Two declared types of identical shape are not told apart: nothing but a signature or a Matchable
; distinguishes atoms, and Bit's and Bool's unify, so the branch must be written out (ASSUMPTIONS 89).
(def-adts $ (Shape : (Type T) -> Type)
  enum
  (many IsBit : -> (Shape (Bit)))
  (many IsBool : -> (Shape (Bool))))
(def-lvl X)
(def-fns X $ (many f : (many (Shape (Bit)) s) -> (many (Nat) n))
  (match many s (((Nat) r))
    ((IsBit) (Zero))
    (absurd IsBool)))
(f (IsBit))
