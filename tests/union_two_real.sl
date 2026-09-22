; needs: list
; error: only one real branch

(def-adts
  ((U : -> Type)
    union
    (many A : (many (Nat) n) -> (U))
    (many B : (many (Nat) m) -> (U))))

(def-lvl X)

(def-fns X $ (many pick : (many (U) u) -> (many (Nat) n))
  (match many u (((Nat) r))
    ((A n) n)
    ((B m) m)))
