; expect: 0
; prove-literal-lt takes numerals only; a character literal's code is its numeral's entry, so the codes'
; numerals state the order of two characters, and refute a branch that equates them.

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
