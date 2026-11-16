(def-adts $ (Entry : -> Type)
  enum
  (many MkEntry : (many (Nat) s a) (erased (Runs s a) p) -> (Entry)))

(def-adts $ (Outcome : ((Tree) t) ((Nat) g) -> Type)
  enum
  (many Done : (erased (Tree) t) (erased (Nat) g) (many (Nat) v g2) (many (List (Entry)) rest used) (erased (Elab t g v g2) p) -> (Outcome t g))
  (many Need : (erased (Tree) t) (erased (Nat) g) (many (Nat) s) (many (List (Entry)) used) -> (Outcome t g)))

(def-fns _ $ (many elab : (subterm many (Tree) t) (many (Nat) g) (many (List (Entry)) log used) -> (many (Outcome t g) r))
  (match many t _
    ((TLeaf n) (Done _ _ n g log used (ELeaf n g)))
    ((TGen) (Done _ _ g (Succ g) log used (EGen g)))
    ((TNode l r)
      (let-match many (notail $ elab l g log used) (Done _ _ a g1 log1 used1 pa) ((Need _ _ s u) (Need _ _ s u)))
      (let-match many (notail $ elab r g1 log1 used1) (Done _ _ b g2 log2 used2 pb) ((Need _ _ s u) (Need _ _ s u)))
      (let ((many c) (erased pc)) (add a b))
      (Done _ _ c g2 log2 used2 (ENode l r g a g1 b g2 c pa pb pc)))
    ((TRun s)
      (let-match many log (Cons _ e rest) ((Nil _) (Need _ _ s used)))
      (let-match many e (MkEntry s2 a p))
      (let-match many (nat-eq s2 s) (Equal _ _ _) ((Unequal _ _ _ _ _) (Need _ _ s used)))
      (Done _ _ a g rest (Cons _ e used) (ERun s a g p)))
    ((TIf c th el)
      (let-match many (notail $ elab c g log used) (Done _ _ v g1 log1 used1 pc) ((Need _ _ s u) (Need _ _ s u)))
      (match many (nat-zero-dec v) _
        ((IsZero)
          (let-match many (notail $ elab th g1 log1 used1) (Done _ _ b g2 log2 used2 pt) ((Need _ _ s u) (Need _ _ s u)))
          (Done _ _ b g2 log2 used2 (EIfZero c th el g g1 b g2 pc pt)))
        ((IsSucc m)
          (let-match many (notail $ elab el g1 log1 used1) (Done _ _ b g2 log2 used2 pe) ((Need _ _ s u) (Need _ _ s u)))
          (Done _ _ b g2 log2 used2 (EIfSucc c th el g m g1 b g2 pc pe)))))))

(def-fns _ $ (many rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (tail $ rev-onto A rest (Cons A x acc)))
