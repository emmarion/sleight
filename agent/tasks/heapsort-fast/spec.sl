(def-adts
  ((AllBelow : ((List (Nat)) xs) ((Nat) m) -> Type)
    enum
    (many BelowNil : (erased (Nat) m) -> (AllBelow (Nil (Nat)) m))
    (many BelowCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Nat) m)
        (erased (Lt x m) p) (erased (AllBelow xs m) rest) -> (AllBelow (Cons (Nat) x xs) m))))

(def-adts
  ((Ascending : ((List (Nat)) xs) -> Type)
    enum
    (many AscNil : -> (Ascending (Nil (Nat))))
    (many AscOne : (erased (Nat) x) -> (Ascending (Cons (Nat) x (Nil (Nat)))))
    (many AscCons : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) rest)
        (erased (Lt x (Succ y)) le) (erased (Ascending (Cons (Nat) y rest)) a)
        -> (Ascending (Cons (Nat) x (Cons (Nat) y rest))))))

(def-adts
  ((Permutation : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many PNil : -> (Permutation (Nil (Nat)) (Nil (Nat))))
    (many PSkip : (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (Permutation xs ys) p)
        -> (Permutation (Cons (Nat) x xs) (Cons (Nat) x ys)))
    (many PSwap : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) l)
        -> (Permutation (Cons (Nat) x (Cons (Nat) y l)) (Cons (Nat) y (Cons (Nat) x l))))
    (many PTrans : (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (List (Nat)) zs)
        (erased (Permutation xs ys) p) (erased (Permutation ys zs) q)
        -> (Permutation xs zs))))

(def-adts
  ((SortedPerm : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many MkSortedPerm : (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (Ascending ys) sorted) (erased (Permutation xs ys) perm)
        -> (SortedPerm xs ys))))

(def-adts
  ((Copies : ((List (Nat)) xs) ((List (Copy (Nat))) cs) -> Type)
    enum
    (many CopiesNil : -> (Copies (Nil (Nat)) (Nil (Copy (Nat)))))
    (many CopiesCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Copy (Nat))) cs)
        (erased (Copies xs cs) rest) -> (Copies (Cons (Nat) x xs) (Cons (Copy (Nat)) (MkCopy (Nat) x) cs)))))
