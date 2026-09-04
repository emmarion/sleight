; needs: list nat_add
; error: type mismatch
; The reused telescope must relate the proof to the parameters in order.

(def-fns _ $ many add2 : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Add a b c) p)
  (match many a _
    ((Zero) (values b (AddZero b)))
    ((Succ k)
      (let (many c) (erased q) (add2 (subterm _) k b))
      (values (Succ c) (AddSucc k k c q)))))
