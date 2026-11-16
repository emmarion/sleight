(def-fns _ $ (many lets : (subterm many (List (Code)) cs) (many (Code) last) -> (many (Code) c))
  (let-match many cs (Cons _ x rest) ((Nil _) last))
  (CLet x (notail $ lets rest last)))

(def-fns _ $ (many cell : (many (Atom) hd) (many (Atom) tl) -> (many (Code) c))
  (CDo (ICon 0 (Cons _ hd $ Cons _ tl $ Nil _))))

(def-fns _ $ (many store : (many (Nat) target) (many (Nat) i) (many (Nat) v) -> (many (Code) c))
  (CDo (IWrite (AVar target) i (AVar v))))

(def-fns _ $ (many var : (many (Nat) i) -> (many (Code) c))
  (CDo (IAtom (AVar i))))

(def-fns _ $ (many read-list : (subterm many (Nat) fuel) (many (Heap) h) (many (Word) w) -> (many (List (Nat)) xs))
  (let-match many fuel (Succ f) ((Zero) (Nil _)))
  (let-match many w (WAddr p) ((WImm _) (Nil _)))
  (let-match many (lookup-dec h p) (LkHit _ _ blk _) ((LkMiss _ _ _) (Nil _)))
  (let-match many blk (MkBlock _ fs))
  (let-match many fs (Cons _ hd rest) ((Nil _) (Nil _)))
  (let-match many rest (Cons _ tl _) ((Nil _) (Nil _)))
  (let-match many hd (WImm n) ((WAddr _) (Nil _)))
  (Cons _ n (notail $ read-list f h tl)))

(let ((many nil)) (AImm 0))
