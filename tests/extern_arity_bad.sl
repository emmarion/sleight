; prelude: none
; error: the extern implementation of `add` takes 2 arguments, its model 3
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(def-fns _ $ (many extern add : (many (Nat) a) (many (Nat) b) -> (many (Nat) r)) a)
(def-fns _ $ (many extern add : (many (Nat) a) (many (Nat) b) (many (Nat) c) -> (many (Nat) r)) a)
(Zero)
