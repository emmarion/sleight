; expect: (Zero)
; Two declared types are told apart by their Matchables alone: Succ carries a field and neither of Bool's
; constructors does, so the two constructor lists cannot unify and the IsBool branch is refuted (ASSUMPTIONS 89).
(def-adts $ Bool : -> Type enum (many True : -> (Bool)) (many False : -> (Bool)))
(def-adts $ Shape : (Type T) -> Type
  enum
  (many IsNat : -> (Shape (Nat)))
  (many IsBool : -> (Shape (Bool))))
(def-lvl X)
(def-fns X $ many f : (many (Shape (Nat)) s) -> (many (Nat) n)
  (match many s (((Nat) r))
    ((IsNat) (Zero))
    (absurd IsBool)))
(f (IsNat))
