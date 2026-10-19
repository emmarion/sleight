; expect: (Cons _ 4096 $ Cons _ 4096 $ Cons _ 1606938044258990275541962092341162602522202993782792835301376 $ Nil _)
; externs: only
(def-adts $ (N : -> Type) enum
  (many Z : -> (N))
  (many S : (many (N) p) -> (N)))

(def-adts $ (Tree : -> Type) enum
  (many Leaf : (many (N) v) -> (Tree))
  (many Node : (many (Tree) l) (many (Tree) r) -> (Tree)))

(def-fns _ $ (many at same-n : (subterm many (N) a) (many (N) b at a) ->
    (many (ErasedOr (Eq (N) a b)) r at vacant-slot))
  (match many a _
    ((Z u1)
      (let-match many b (S _ u2) ((Z) (EONonErased _ (Refl (N) a))))
      (let ((many s)) (cell-same u1 u2))
      (match many s (at (((ErasedOr (Eq (N) a b)) r at vacant-slot)))
        (absurd (EONonErased _ j) j)
        ((EOErased _) (EOErased _))))
    ((S a1 u1)
      (match many b _
        ((S b1 u2)
          (let ((many s)) (cell-same u1 u2))
          (let-match many s (EONonErased _ j) ((EOErased _) (EOErased _)))
          (let-match erased j (JMRefl _ _))
          (let ((many e)) (same-n a1 b1))
          (let-match many e (EONonErased _ ea) ((EOErased _) (EOErased _)))
          (let-match erased ea (Refl _ _))
          (EONonErased _ (Refl (N) a)))
        ((Z u2)
          (let ((many s)) (cell-same u1 u2))
          (match many s (at (((ErasedOr (Eq (N) a b)) r at vacant-slot)))
            (absurd (EONonErased _ j) j)
            ((EOErased _) (EOErased _))))))))

(def-fns _ $ (many at same-tree : (subterm many (Tree) a) (many (Tree) b at a) ->
    (many (ErasedOr (Eq (Tree) a b)) r at vacant-slot))
  (match many a _
    ((Leaf v1 u1)
      (match many b _
        ((Leaf v2 u2)
          (let ((many s)) (cell-same u1 u2))
          (let-match many s (EONonErased _ j) ((EOErased _) (EOErased _)))
          (let-match erased j (JMRefl _ _))
          (let ((many e)) (same-n v1 v2))
          (let-match many e (EONonErased _ ev) ((EOErased _) (EOErased _)))
          (let-match erased ev (Refl _ _))
          (EONonErased _ (Refl (Tree) a)))
        ((Node _ _ u2)
          (let ((many s)) (cell-same u1 u2))
          (match many s (at (((ErasedOr (Eq (Tree) a b)) r at vacant-slot)))
            (absurd (EONonErased _ j) j)
            ((EOErased _) (EOErased _))))))
    ((Node l1 r1 u1)
      (match many b _
        ((Node l2 r2 u2)
          (let ((many s)) (cell-same u1 u2))
          (let-match many s (EONonErased _ j) ((EOErased _) (EOErased _)))
          (let-match erased j (JMRefl _ _))
          (let ((many el)) (same-tree l1 l2))
          (let-match many el (EONonErased _ pl) ((EOErased _) (EOErased _)))
          (let-match erased pl (Refl _ _))
          (let ((many er)) (same-tree r1 r2))
          (let-match many er (EONonErased _ pr) ((EOErased _) (EOErased _)))
          (let-match erased pr (Refl _ _))
          (EONonErased _ (Refl (Tree) a)))
        ((Leaf _ u2)
          (let ((many s)) (cell-same u1 u2))
          (match many s (at (((ErasedOr (Eq (Tree) a b)) r at vacant-slot)))
            (absurd (EONonErased _ j) j)
            ((EOErased _) (EOErased _))))))))

(def-adts $ (Val : ((N) v) ((Nat) n) -> Type) enum
  (many VZ : -> (Val (Z) (Zero)))
  (many VS : (erased (N) v) (erased (Nat) n) (erased (Val v n) p) -> (Val (S v) (Succ n))))

(def-adts $ (TreeSum : ((Tree) t) ((Nat) n) -> Type) enum
  (many SLeaf : (erased (N) v) (erased (Nat) n) (erased (Val v n) p) -> (TreeSum (Leaf v) n))
  (many SNode : (erased (Tree) l) (erased (Tree) r) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (erased (TreeSum l a) pl) (erased (TreeSum r b) pr) (erased (Add a b c) p) -> (TreeSum (Node l r) c)))

(def-fns _ $ (many value : (subterm many (N) v) -> (many (Nat) n) (erased (Val v n) p))
  (let-match many v (S w) ((Z) (values (Zero) (VZ))))
  (let ((many m) (erased q)) (notail (value w)))
  (values (Succ m) (VS w m q)))

(def-fns _ $ (many leaf-sum : (many (N) v) -> (many (Nat) n) (erased (TreeSum (Leaf v) n) p))
  (let ((many n) (erased q)) (value v))
  (values n (SLeaf v n q)))

(def-fns _ $ (many node-sum : (erased (Tree) l) (erased (Tree) r)
    (many (Nat) a) (erased (TreeSum l a) pa) (many (Nat) b) (erased (TreeSum r b) pb) ->
    (many (Nat) c) (erased (TreeSum (Node l r) c) p))
  (let ((many c) (erased q)) (add a b))
  (values c (SNode l r a b c pa pb q)))

(def-fns _ $ (many naive-sum : (subterm many (Tree) t) -> (many (Nat) n) (erased (TreeSum t n) p))
  (let-match many t (Node l r) ((Leaf v) (leaf-sum v)))
  (let ((many a) (erased pa)) (notail (naive-sum l)))
  (let ((many b) (erased pb)) (notail (naive-sum r)))
  (node-sum l r a pa b pb))

(def-adts $ (Memo : -> Type) enum
  (many MkMemo : (many (Tree) t) (many (Nat) n) (erased (TreeSum t n) p) -> (Memo)))

(def-adts $ (Found : ((Tree) t) -> Type) enum
  (many Hit : (erased (Tree) t) (many (Nat) n) (erased (TreeSum t n) p) -> (Found t))
  (many Miss : (erased (Tree) t) -> (Found t)))

(def-fns _ $ (many lookup : (many (Tree) q) (subterm many (List (Memo)) m) -> (many (Found q) f))
  (let-match many m (Cons _ e rest) ((Nil _) (Miss q)))
  (let-match many e (MkMemo t n p))
  (let-match many (slot-eq (slot-of t) (slot-of q)) (Some _ se) ((None _) (tail (lookup q rest))))
  (let-match erased se (Refl _ _))
  (let-match many (same-tree t q) (EONonErased _ tq) ((EOErased _) (lookup q rest)))
  (let-match erased tq (Refl _ _))
  (Hit q n p))

(def-fns _ $ (many go : (subterm many (Tree) t) (many (List (Memo)) m) ->
    (many (Nat) n) (erased (TreeSum t n) p) (many (List (Memo)) m2))
  (let-match many (lookup t m) (Miss _) ((Hit _ n p) (values n p m)))
  (let ((many n) (erased p) (many m2))
    (match many t (((Nat) n) ((TreeSum t n) p) ((List (Memo)) m2))
      ((Leaf v) (let ((many k) (erased q)) (leaf-sum v)) (values k q m))
      ((Node l r)
        (let ((many a) (erased pa) (many m1)) (notail (go l m)))
        (let ((many b) (erased pb) (many m2)) (notail (go r m1)))
        (let ((many c) (erased pc)) (node-sum l r a pa b pb))
        (values c pc m2))))
  (values n p (Cons _ (MkMemo t n p) m2)))

(def-fns _ $ (many dag-sum : (many (Tree) t) -> (many (Nat) n) (erased (TreeSum t n) p))
  (let ((many n) (erased p) (erased _)) (go t (Nil _)))
  (values n p))

(def-fns _ $ (many tower : (subterm many (Nat) k) -> (many (Tree) t))
  (let-match many k (Succ j) ((Zero) (Leaf (S (Z)))))
  (let ((many s)) (notail (tower j)))
  (Node s s))

(def-fns _ $ (many run : -> (many (List (Nat)) out))
  (let ((many a) (erased _)) (naive-sum (tower 12)))
  (let ((many b) (erased _)) (dag-sum (tower 12)))
  (let ((many c) (erased _)) (dag-sum (tower 200)))
  (Cons _ a $ Cons _ b $ Cons _ c $ Nil _))

run
