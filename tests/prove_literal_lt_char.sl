; expect: 0

(def-adts ((Tag : ((Char) c) -> Type)
  enum
  (many TA : -> (Tag #\a))
  (many TB : -> (Tag #\b))))
(def-lvl X)
(def-fns X $ (many only-a : (many (Tag #\a) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB) (lt-asym 97 97 (prove-literal-lt 97 98) (lt-succ 97)))))
(only-a (TA))
