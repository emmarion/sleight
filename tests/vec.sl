; needs: list
; expect: 1
; A length-indexed vector: head needs the VNil branch refuted automatically.

(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) m) (many A x) (many (Vec A m) xs)
       -> (Vec A (Succ m)))))

(def-lvl L)

(def-fns L $ (many head : (erased Type A) (erased (Nat) n) (many (Vec A (Succ n)) v) ->
    (many A x))
  (match many v ((A r))
    (absurd VNil)
    ((VCons a m x xs) x)))

(let ((many vec-v)) (VCons (Nat) (Zero) (Succ (Zero)) (VNil (Nat))))

(head (Nat) (Zero) vec-v)
