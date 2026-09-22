; needs: list
; expect: 0
; An erased match in a non-erased position: the one real branch, no runtime dispatch.

(def-adts
  ((Unit : -> Type)
    enum
    (many U : -> (Unit))))

(def-lvl X)

(def-fns X $ (many zero-of : (erased (Unit) u) -> (many (Nat) n))
  (match erased u (((Nat) r))
    ((U) (Zero))))

(zero-of (U))
