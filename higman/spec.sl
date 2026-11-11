(def-adts $ (Emb : ((List (Bool)) u) ((List (Bool)) w) -> Type)
  enum
  (many EmbNil : (erased (List (Bool)) w) -> (Emb (Nil (Bool)) w))
  (many EmbSkip : (erased (Bool) c) (erased (List (Bool)) u w) (erased (Emb u w) e) -> (Emb u (Cons (Bool) c w)))
  (many EmbKeep : (erased (Bool) c) (erased (List (Bool)) u w) (erased (Emb u w) e) -> (Emb (Cons (Bool) c u) (Cons (Bool) c w))))

; G i w : w is the sequence's word at index i.
(def-adts $ (Good : ((TyCtor ((Nat) i) ((List (Bool)) w) -> Type) G) -> Type)
  enum
  (many MkGood : (erased (TyCtor ((Nat) i) ((List (Bool)) w) -> Type) G) (many (Nat) i j) (erased (Lt i j) l)
     (many (List (Bool)) u w) (erased (G i u) gu) (erased (G j w) gw) (erased (Emb u w) e) -> (Good G)))

; M : the level of the sequence; L : the level of the search the factory builds for it.
(def-adts $ (Higman : -> Type)
  enum
  (many MkHigman : (erased (Level) K)
     (many (Fn K (erased (Level) M) ->
               (erased (Level) L)
               (many (Fn L (erased (TyCtor ((Nat) i) ((List (Bool)) w) -> Type) G)
                         (many (Fn M (many (Nat) i) -> (many (List (Bool)) w) (erased (G i w) g)) f)
                         -> (many (Good G) r)) search))
           factory)
     -> (Higman)))

(goal many (Higman))
