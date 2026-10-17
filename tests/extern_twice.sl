; prelude: none
; error: already bound
; error: note: the declaration that bound it
; An FFI implementation backs one declaration per program (ASSUMPTIONS 42).
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(def-fns _ $ (many extern add : (many (Nat) a) (many (Nat) _b) -> (many (Nat) c)) a)
(def-fns _ $ (many extern add : (many (Nat) a) (many (Nat) b) -> (many (Nat) c)) a)
