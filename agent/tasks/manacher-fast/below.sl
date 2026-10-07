(def-adts
  ((AllBelow : ((List (Nat)) xs) ((Nat) m) -> Type)
    enum
    (many BelowNil : (erased (Nat) m) -> (AllBelow (Nil (Nat)) m))
    (many BelowCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Nat) m)
        (erased (Lt x m) p) (erased (AllBelow xs m) rest) -> (AllBelow (Cons (Nat) x xs) m))))

(def-adts
  ((Copies : ((List (Nat)) xs) ((List (Copy (Nat))) cs) -> Type)
    enum
    (many CopiesNil : -> (Copies (Nil (Nat)) (Nil (Copy (Nat)))))
    (many CopiesCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Copy (Nat))) cs)
        (erased (Copies xs cs) rest) -> (Copies (Cons (Nat) x xs) (Cons (Copy (Nat)) (MkCopy (Nat) x) cs)))))
