; prelude: none
; error: unbound name `RSettled`
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)))
(def-prim $ (many resolve : (many (Nat) x) -> (many (Nat) r)))
(def-fns _ $ (many main : -> (many (Nat) r)) (resolve (Zero)))
main
