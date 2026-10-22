; prelude: none
; error: unbound name `MErased`
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(def-adts $ (Pair : -> Type) enum (many MkPair : (many (Nat) a) (many (Nat) b) -> (Pair)))
(def-prim $ (many settled-mult : (many (Nat) x) -> (many (Pair) r)))
(def-fns _ $ (many main : -> (many (Nat) r))
  (let-match many (settled-mult (Zero)) (MkPair a b))
  b)
main
