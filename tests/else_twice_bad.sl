; error: at most one else
; error: tests/else_twice_bad.sl:8:5: note: the first else branch

(def-lvl X)

(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    (else (Zero))
    (else (Zero))))

(f (Zero))
