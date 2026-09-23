; expect: 0
; distinct takes character literals as it takes numerals, through their codes, and refutes a branch that
; equates two different ones.

(def-adts ((Tag : ((Char) c) -> Type)
  enum
  (many TA : -> (Tag #\a))
  (many TB : -> (Tag #\b))))
(def-lvl X)
(def-fns X $ (many only-a : (many (Tag #\a) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB) (distinct #\a #\b))))
(only-a (TA))
