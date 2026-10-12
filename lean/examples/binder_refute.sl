(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (many (Nat) n) (many A x) (many (Vec A n) xs) -> (Vec A (Succ n)))))
(def-adts
  ((W : (Type F) -> Type)
    enum
    (many MkW : (erased (Level) l) (many (Nat) k) -> (W (Fn l (many (Nat) x) -> (many (Vec (Nat) k) y))))))
(def-lvl L)
(def-lvl M)
(def-fns M $ (many never : (erased Type A) (many (W (Fn L (many (Nat) x) -> (many (Vec (Nat) x) y))) w) -> (many A r))
  (match many w ((A r))))
(Zero)
