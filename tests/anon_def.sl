; expect: 1
(def-adts $ (T : -> Type)
  enum
  (many _ : -> (T))
  (many B : -> (T)))
(def-fns _ $ (many _ : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many f : (many (T) t) -> (many (Nat) m))
  (match many t _
    ((B) 1)
    (else 0)))
(f (B))
