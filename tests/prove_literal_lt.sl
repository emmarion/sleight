; expect: 0

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
