; DESIGN.md sections 21 and 25: absurd functions and branches
(def-adts
  ((False : -> Type)
    enum))
(def-adts
  ((Le : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many LeZ : (many (Nat) b) -> (Le (Zero) b))
    (many LeS : (many (Nat) a) (many (Nat) b) (many (Le a b) p) -> (Le (Succ a) (Succ b)))))
(def-fns _ $ (many absurd explode : (erased Type A) (many (False) f) -> (many A a))
  f)
(def-fns _ $ (many pred : (many (Nat) n) (many (Le (Succ (Zero)) n) p) -> (many (Nat) r))
  (match many p (((Nat) r))
    (absurd LeZ)
    ((LeS a b q) b)))
(def-fns _ $ (many zero-or : (many (Nat) n) (many (False) f) -> (many (Nat) r))
  (match many n (((Nat) r))
    ((Zero) (Zero))
    (absurd (Succ k)
      f)))
(pred (Succ (Succ (Zero))) (LeS (Zero) (Succ (Zero)) (LeZ (Succ (Zero)))))
