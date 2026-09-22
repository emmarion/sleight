; needs: list
; error: is not refuted

(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) m) (many A x) (many (Vec A m) xs) ->
       (Vec A (Succ m)))))

(def-lvl L)

(def-fns L $ (many head : (erased Type A) (erased (Nat) n) (many (Vec A n) v) ->
    (many (Nat) x))
  (match many v (((Nat) r))
    (absurd VNil)
    ((VCons a m x xs) (Zero))))
