; expect: 0
; prove-literal-lt gives an erased Lt between two numerals, whatever the facts in force: here a branch has
; equated the two, so the proof is an Lt from 3 to itself, which lt-asym refutes. Its proof is asserted,
; as a numeral's Numeral proof is (ASSUMPTIONS 54 keeps a test's numerals small).

(def-adts ((Tag : ((Nat) n) -> Type)
  enum
  (many TA : -> (Tag 3))
  (many TB : -> (Tag 1000))))

(def-lvl X)
(def-fns X $ (many only-a : (many (Tag 3) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB) (lt-asym 3 3 (prove-literal-lt 3 1000) (lt-succ 3)))))

(let ((erased (Lt 3 4) q)) (prove-literal-lt 3 4))
(only-a (TA))
