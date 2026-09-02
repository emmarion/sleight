; needs: list
; error: is refuted

(def-adts
  (Vec : (Type A) ((Nat) n) -> Type
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) m) (many A x) (many (Vec A m) xs) ->
       (Vec A (Succ m)))))

(def-lvl L)

(def-fns L $ many head : (erased Type A) (erased (Nat) n) (many (Vec A (Succ n)) v) ->
    (many A x)
  (match many v ((A r))
    ((VNil a) a)
    ((VCons a m x xs) x)))
