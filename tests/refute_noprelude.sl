; prelude: none
; expect: _

(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) n) -> (Nat)))
(def-adts $ (Eq : (Type A) (A a) (A b) -> Type) enum (many Refl : (erased Type A) (erased A a) -> (Eq A a a)))

(def-lvl X)

(def-fns X $ (many absurd zero-not-succ : (erased (Nat) a) (many (Eq (Nat) (Zero) (Succ a)) p) -> (many (Nat) n))
  p)

zero-not-succ
