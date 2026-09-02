; needs: list
; error: type mismatch

(def-adts
  (Sing : ((Nat) n) -> Type
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-lvl X)
(def-fns X $ many one-sing : -> (erased (Nat) n) (many (Sing n) s)
  (values (Zero) (SSucc (Zero) (SZero))))
