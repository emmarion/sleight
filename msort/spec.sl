(def-adts $ (ULst : -> Type)
  enum
  (many UNil : -> (ULst))
  (many UCons : (many (U62) head) (unique (ULst) rest) -> (ULst)))

(def-adts
  ((LeU : ((U62) x) ((U62) y) -> Type)
    enum
    (many MkLeU : (erased (Nat) a) (erased (Lt a u62-modulus) pa) (erased (Nat) b) (erased (Lt b u62-modulus) pb)
       (erased (Lt a (Succ b)) l) -> (LeU (MkU62 a pa) (MkU62 b pb)))))

(def-adts
  ((LeHead : ((U62) x) ((ULst) xs) -> Type)
    enum
    (many LHNil : (erased (U62) x) -> (LeHead x (UNil)))
    (many LHCons : (erased (U62) x) (erased (U62) y) (erased (ULst) ys) (erased (LeU x y) l) -> (LeHead x (UCons y ys)))))

(def-adts
  ((SortedU : ((ULst) xs) -> Type)
    enum
    (many SortNil : -> (SortedU (UNil)))
    (many SortCons : (erased (U62) x) (erased (ULst) xs) (erased (LeHead x xs) h) (erased (SortedU xs) s)
       -> (SortedU (UCons x xs)))))

(def-adts
  ((PermU : ((ULst) a) ((ULst) b) -> Type)
    enum
    (many PNil : -> (PermU (UNil) (UNil)))
    (many PSkip : (erased (U62) x) (erased (ULst) a) (erased (ULst) b) (erased (PermU a b) p)
       -> (PermU (UCons x a) (UCons x b)))
    (many PSwap : (erased (U62) x) (erased (U62) y) (erased (ULst) a)
       -> (PermU (UCons x (UCons y a)) (UCons y (UCons x a))))
    (many PTrans : (erased (ULst) a) (erased (ULst) b) (erased (ULst) c) (erased (PermU a b) p) (erased (PermU b c) q)
       -> (PermU a c))))
