; expect: 0
; distinct refutes a branch that has equated two literals, through the prelude's numeral-inj: a Nat has
; one bijective base-2 spelling, so two spellings for one Nat contradict. Its cost is the spellings'
; depth, not the difference between the numbers (ASSUMPTIONS 54 keeps a test's numerals small).

(def-adts (Tag : ((Nat) n) -> Type
  enum
  (many TA : -> (Tag 3))
  (many TB : -> (Tag 1000))))

(def-lvl X)
(def-fns X $ many only-a : (many (Tag 3) t) -> (many (Nat) r)
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB) (distinct 3 1000))))

(only-a (TA))
