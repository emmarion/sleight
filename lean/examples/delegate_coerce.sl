(def-adts $ (U : -> Type) enum (many MkU : -> (U)))

(def-fns _ $ (many inc : (many (Nat) n) (erased (U) u) -> (many (Nat) m) (erased (U) w))
  (values (Succ n) u))

(def-fns _ $ (many inc-noted at inc : (erased (Nat) note) (many (Nat) n) -> (many (Nat) m))
  (let ((many m) (erased _)) (delegate (inc n (MkU))))
  m)

(let ((erased d)) (delegate-of inc-noted))
(let ((erased ig)) (coercible-of d))
(let ((many inc2)) (coerce inc-noted ig))
(let ((many a) (erased _)) (inc2 5 (MkU)))
(let ((many b)) (inc-noted 0 a))
b
