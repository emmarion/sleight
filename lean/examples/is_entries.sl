(def-adts
  ((Add : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many AddZ : (many (Nat) b) -> (Add (Zero) b b))
    (many AddS : (many (Nat) a) (many (Nat) b) (many (Nat) c) (many (Add a b c) p) -> (Add (Succ a) b (Succ c)))))
(def-adts
  ((Two : ((Nat) a) -> Type)
    enum
    (many MkTwo : (many (Nat) a) (many (Succ (Succ a)) is s) -> (Two a))))
(def-lvl L)
(def-fns L $ (many reify : (many (Nat) a) (many (Nat) b) (many (Nat) c) (many (Add a b c) p) -> (many c is d))
  c)
(def-fns L $ (many pred2 : (many (Nat) a) (many (Two a) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((MkTwo x s)
      (match many s (((Nat) r))
        ((Succ k) k)))))
(let ((many d)) (reify (Succ (Zero)) (Zero) (Succ (Zero)) (AddS (Zero) (Zero) (Zero) (AddZ (Zero)))))
(let ((many (Succ (Zero)) is e)) d)
(Cons (Nat) e (Cons (Nat) (pred2 (Zero) (MkTwo (Zero) (Succ (Succ (Zero))))) (Nil (Nat))))
