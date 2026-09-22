; error: at most one else

(def-lvl X)

(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    (else (Zero))
    (else (Zero))))

(f (Zero))
