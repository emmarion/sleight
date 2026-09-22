; needs: list
; expect: 0
; Branches refute through a chain of let aliases.

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((many a)) n)
  (let ((many b)) a)
  (match many n (((Nat) r))
    ((Zero)
      (match many b (((Nat) r))
        ((Zero) (Zero))
        (absurd Succ)))
    ((Succ k)
      (match many b (((Nat) r))
        (absurd Zero)
        ((Succ j) j)))))
(f (Zero))
