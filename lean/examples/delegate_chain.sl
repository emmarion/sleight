(def-adts $ (U : -> Type) enum (many MkU : -> (U)))

(def-fns _ $ (many inc : (many (Nat) n) (erased (U) u) -> (many (Nat) m) (erased (U) w))
  (values (Succ n) u))

(def-fns _ $ (many inc1 at inc : (erased (U) u) (many (Nat) n) -> (many (Nat) m))
  (let ((many m) (erased _)) (delegate (inc n u)))
  m)

(def-fns _ $ (many inc2 at inc1 : (many (Nat) n) (erased (Nat) note) -> (many (Nat) m))
  (delegate (inc1 (MkU) n)))

(def-fns _ $ (many twice : (many (Nat) n) -> (many (Nat) m))
  (let ((many a)) (inc2 n 0))
  (inc2 a 1))

(let ((erased ig)) (coercible-of (delegate-of inc2)))
(let ((many f)) (coerce inc2 ig))
(let ((many a)) (f (MkU) 3))
(twice a)
