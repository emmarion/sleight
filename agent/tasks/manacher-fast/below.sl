(def-adts
  ((AllBelow : ((List (Nat)) xs) ((Nat) m) -> Type)
    enum
    (many BelowNil : (erased (Nat) m) -> (AllBelow (Nil (Nat)) m))
    (many BelowCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Nat) m)
        (erased (Lt x m) p) (erased (AllBelow xs m) rest) -> (AllBelow (Cons (Nat) x xs) m))))
