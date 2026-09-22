; needs: list vec
; error: type mismatch

(def-lvl V)
(def-fns V $ (many vtail-bad : (erased (Nat) n) (many (Vec (Nat) n) v) -> (many (Vec (Nat) n) r))
  (match many v (((Vec (Nat) n) r))
    ((VNil a) (VNil (Nat)))
    ((VCons a m x xs) xs)))
