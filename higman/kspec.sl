(def-adts $ (Letters : ((Nat) k) ((List (Nat)) w) -> Type)
  enum
  (many LetNil : (erased (Nat) k) -> (Letters k (Nil (Nat))))
  (many LetCons : (erased (Nat) k a) (erased (List (Nat)) w) (erased (Lt a k) l) (erased (Letters k w) r) -> (Letters k (Cons (Nat) a w))))

(def-adts $ (EmbN : ((List (Nat)) u) ((List (Nat)) w) -> Type)
  enum
  (many ENNil : (erased (List (Nat)) w) -> (EmbN (Nil (Nat)) w))
  (many ENSkip : (erased (Nat) c) (erased (List (Nat)) u w) (erased (EmbN u w) e) -> (EmbN u (Cons (Nat) c w)))
  (many ENKeep : (erased (Nat) c) (erased (List (Nat)) u w) (erased (EmbN u w) e) -> (EmbN (Cons (Nat) c u) (Cons (Nat) c w))))

; G i w : w is the sequence's word at index i.
(def-adts $ (GoodK : ((TyCtor ((Nat) i) ((List (Nat)) w) -> Type) G) -> Type)
  enum
  (many MkGoodK : (erased (TyCtor ((Nat) i) ((List (Nat)) w) -> Type) G) (many (Nat) i j) (erased (Lt i j) l)
     (many (List (Nat)) u w) (erased (G i u) gu) (erased (G j w) gw) (erased (EmbN u w) e) -> (GoodK G)))

; k : the alphabet is 0 ... k-1; M : the level of the sequence; L : the level of the search the factory builds for it.
(def-adts $ (HigmanK : ((Nat) k) -> Type)
  enum
  (many MkHigmanK : (erased (Nat) k) (erased (Level) K)
     (many (Fn K (erased (Level) M) ->
               (erased (Level) L)
               (many (Fn L (erased (TyCtor ((Nat) i) ((List (Nat)) w) -> Type) G)
                         (many (Fn M (many (Nat) i) -> (many (List (Nat)) w) (erased (G i w) g) (erased (Letters k w) lw)) f)
                         -> (many (GoodK G) r)) search))
           factory)
     -> (HigmanK k)))
