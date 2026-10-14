; expect: 10
(def-adts $ (Vec : (Type A) ((Nat) n) -> Type)
  enum
  (many VNil : (erased Type A) -> (Vec A (Zero)))
  (many VCons : (erased Type A) (erased (Nat) n) (many A head) (many (Vec A n) rest)
     -> (Vec A (Succ n))))

(def-fns _ $ (many vhead : (erased Type A) (erased (Nat) n) (many (Vec A (Succ n)) v) ->
    (many A x))
  (let-match many v (VCons _ _ hd _))
  hd)

(vhead _ _ $ VCons _ _ 10 $ VCons _ _ 20 $ VNil (Nat))
