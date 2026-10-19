; expect: (Cons _ 4096 $ Cons _ 4096 $ Cons _ 1606938044258990275541962092341162602522202993782792835301376 $ Cons _ 40002 $ Nil _)
; externs: only
; needs: ../std/list
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

(let ((erased TI)) (SlotItem (Tree)))

(def-adts $ (Memo : -> Type) enum
  (many MkMemo : (erased (Tree) t) (many (Nat) n) (erased (TreeSum t n) p) -> (Memo)))

(let ((erased Entry)) (Copy (Maybe (Memo))))

(def-adts $ (EntryOk : ((List TI) xs) ((Nat) i) (Entry m) -> Type) enum
  (many OkNone : (erased (List TI) xs) (erased (Nat) i) -> (EntryOk xs i (MkCopy _ (None (Memo)))))
  (many OkSome : (erased (List TI) xs) (erased (Nat) i) (erased (Slot) s) (erased (Tree) t)
    (erased (Placed s (Tree) t) pt) (erased (Nat) n) (erased (TreeSum t n) p) (erased (NthLast TI xs i (MkSlotItem _ s t pt)) nl)
    -> (EntryOk xs i (MkCopy _ (Some _ (MkMemo t n p))))))

(def-adts $ (Good : ((List TI) xs) ((Nat) j) ((List Entry) cs) -> Type) enum
  (many GoodNil : (erased (List TI) xs) (erased (Nat) j) -> (Good xs j (Nil Entry)))
  (many GoodCons : (erased (List TI) xs) (erased (Nat) j) (erased Entry m) (erased (List Entry) rest)
    (erased (EntryOk xs j m) ok) (erased (Good xs (Succ j) rest) g) -> (Good xs j (Cons Entry m rest))))

(def-fns _ $ (erased good-repeat : (erased (List TI) xs) (erased (Nat) j k) (erased (List Entry) cs)
    (subterm erased (Repeat Entry k (MkCopy _ (None (Memo))) cs) rp) -> (erased (Good xs j cs) g))
  (let-match erased rp (RepeatCons _ k1 _ rest rp1) ((RepeatNil _ _) (GoodNil xs j)))
  (GoodCons xs j _ rest (OkNone xs j) (good-repeat xs (Succ j) k1 rest rp1)))

(def-fns _ $ (erased good-nth : (erased (List TI) xs) (erased (Nat) j i r) (erased (List Entry) cs) (erased Entry m)
    (subterm erased (Nth Entry cs i m) nth) (erased (Good xs j cs) g) (erased (Add i j r) ad) -> (erased (EntryOk xs r m) ok))
  (let-match erased g (GoodCons _ _ _ rest ok g1) (absurd (GoodNil _ _) nth))
  (let-match erased nth (NthThere _ _ _ i1 _ nth1) ((NthHere _ _ _) (let-match erased ad (AddZero _)) ok))
  (let-match erased ad (AddSucc _ _ r1 ad1))
  (good-nth xs (Succ j) i1 r rest m nth1 g1 (add-succ-right i1 j r1 ad1)))

(def-fns _ $ (erased good-set : (erased (List TI) xs) (erased (Nat) j i r) (erased (List Entry) cs ys) (erased Entry y)
    (subterm erased (SetNth Entry cs i y ys) sp) (erased (Good xs j cs) g) (erased (Add i j r) ad) (erased (EntryOk xs r y) ok) ->
    (erased (Good xs j ys) g2))
  (let-match erased g (GoodCons _ _ m1 rest ok1 g1) (absurd (GoodNil _ _) sp))
  (let-match erased sp (SetThere _ _ _ i1 _ rest2 sp1)
    ((SetHere _ _ _ _) (let-match erased ad (AddZero _)) (GoodCons xs j y rest ok g1)))
  (let-match erased ad (AddSucc _ _ r1 ad1))
  (GoodCons xs j m1 rest2 ok1 (good-set xs (Succ j) i1 r rest rest2 y sp1 g1 (add-succ-right i1 j r1 ad1) ok)))

(def-adts $ (Found : ((Tree) t) -> Type) enum
  (many Hit : (erased (Tree) t) (many (Nat) n) (erased (TreeSum t n) p) -> (Found t))
  (many Miss : (erased (Tree) t) -> (Found t)))

(def-fns _ $ (many visit : (erased (List TI) xs) (subterm many (Tree) t) (unique (Slots (Tree) xs) seen) ->
    (erased (List TI) ys) (unique (Slots (Tree) ys) seen2 at seen))
  (let ((erased xs1) (many r) (unique s1)) (slots-intern _ _ seen _ _ (place-at-many _ t)))
  (let-match many r (SlotAdded _ _ _ _ _ _ _) ((SlotExisting _ _ _ _ _ _ _) (values xs1 s1)))
  (let-match many t (Node l rt) ((Leaf _) (values xs1 s1)))
  (let ((erased _) (unique s2)) (notail $ visit _ l s1))
  (tail $ visit _ rt s2))

(def-fns _ $ (many lookup : (erased (List TI) xs) (erased (Nat) k) (erased (Length TI xs k) lx)
    (erased (List Entry) cs) (erased (Length Entry cs k) lc) (erased (Good xs (Zero) cs) gd)
    (many (Tree) q) (erased Type U) (many U x at q) (many (SlotFind (Tree) xs (slot-of q) U x) f)
    (unique (Array Entry cs) a) ->
    (many (Found q) h) (unique a is a2 at a))
  (let-match many f (SlotFound _ _ _ _ _ i nl) ((SlotMissing _ _ _) (values (Miss q) a)))
  (let ((erased e) (erased nth)) (nth-exists _ cs k i lc (nth-last-lt _ xs i k _ nl lx)))
  (let-match erased e (MkCopy _ m))
  (let ((many v) (unique a1)) (array-get _ cs a i m nth))
  (let-match many v (Some _ en) ((None _) (values (Miss q) a1)))
  (let-match many en (MkMemo _ n p))
  (let-match erased (good-nth xs (Zero) i i cs e nth gd (add-zero-right i)) (OkSome _ _ _ _ _ _ _ nls))
  (let-match erased (nth-last-fn _ xs i _ _ nls nl) (Refl _ _))
  (let-match many (same-tree q x) (EONonErased _ tq) ((EOErased _) (values (Miss q) a1)))
  (let-match erased tq (Refl _ _))
  (values (Hit q n p) a1))

(def-fns _ $ (many store : (erased (List TI) xs) (erased (Nat) k) (erased (Length TI xs k) lx)
    (erased (List Entry) cs) (erased (Length Entry cs k) lc) (erased (Good xs (Zero) cs) gd)
    (many (Tree) q) (erased Type U) (many U x at q) (many (SlotFind (Tree) xs (slot-of q) U x) f)
    (many (Nat) n) (erased (TreeSum q n) p)
    (unique (Array Entry cs) a) ->
    (erased (List Entry) cs2) (unique (Array Entry cs2) a2 at a)
    (erased (Length Entry cs2 k) lc2) (erased (Good xs (Zero) cs2) gd2))
  (let-match many f (SlotFound _ _ _ _ pf i nl) ((SlotMissing _ _ _) (values cs a lc gd)))
  (let-match many (same-tree q x) (EONonErased _ tq) ((EOErased _) (values cs a lc gd)))
  (let-match erased tq (Refl _ _))
  (let ((erased e) (erased nth)) (nth-exists _ cs k i lc (nth-last-lt _ xs i k _ nl lx)))
  (let ((erased cs2) (unique a2) (erased sp))
    (array-place _ cs a i (MkCopy _ (Some _ (MkMemo q n p))) e nth))
  (values cs2 a2 (setnth-length _ cs i k _ cs2 sp lc)
    (good-set xs (Zero) i i cs cs2 _ sp gd (add-zero-right i) (OkSome xs i _ q pf n p nl))))

(def-fns _ $ (many go : (erased (List TI) xs) (erased (Nat) k) (erased (Length TI xs k) lx)
    (subterm many (Tree) t) (unique (Slots (Tree) xs) tb)
    (erased (List Entry) cs) (erased (Length Entry cs k) lc) (erased (Good xs (Zero) cs) gd)
    (unique (Array Entry cs) a) ->
    (many (Nat) n) (erased (TreeSum t n) p) (unique (Slots (Tree) xs) tb2 at tb)
    (erased (List Entry) cs2) (erased (Length Entry cs2 k) lc2) (erased (Good xs (Zero) cs2) gd2)
    (unique (Array Entry cs2) a2 at a))
  (let ((erased _) (many fx) (many f) (unique tb1)) (slots-find _ _ tb (slot-of t)))
  (let ((many h) (unique a1)) (lookup _ k lx _ lc gd t _ fx f a))
  (let-match many h (Miss _) ((Hit _ n p) (values n p tb1 cs lc gd a1)))
  (let ((many n) (erased p) (unique tb2) (erased _) (erased lc2) (erased gd2) (unique a2))
    (match many t (((Nat) n) ((TreeSum t n) p) ((Slots (Tree) xs) tb2 at tb)
        ((List Entry) cs2) ((Length Entry cs2 k) lc2) ((Good xs (Zero) cs2) gd2) ((Array Entry cs2) a2 at a))
      ((Leaf v) (let ((many s) (erased q)) (leaf-sum v)) (values s q tb1 cs lc gd a1))
      ((Node l r)
        (let ((many x) (erased px) (unique tb3) (erased _) (erased lc3) (erased gd3) (unique a3))
          (notail (go _ k lx l tb1 _ lc gd a1)))
        (let ((many y) (erased py) (unique tb4) (erased cs4) (erased lc4) (erased gd4) (unique a4))
          (notail (go _ k lx r tb3 _ lc3 gd3 a3)))
        (let ((many c) (erased pc)) (node-sum l r x px y py))
        (values c pc tb4 cs4 lc4 gd4 a4))))
  (let ((erased cs3) (unique a3) (erased lc3) (erased gd3)) (store _ k lx _ lc2 gd2 t _ fx f n p a2))
  (values n p tb2 cs3 lc3 gd3 a3))

(def-fns _ $ (many dag-sum : (many (Tree) t) -> (many (Nat) n) (erased (TreeSum t n) p))
  (let ((unique s0)) (slots-new (Tree)))
  (let ((erased xs) (unique s1)) (visit _ t s0))
  (let ((many k) (erased lx) (unique s2)) (slots-length _ _ s1))
  (let ((erased cs) (unique a) (erased rp)) (array-make _ k (None (Memo))))
  (let ((many n) (erased p) (unique _) (erased _) (erased _) (erased _) (unique _))
    (go _ k lx t s2 cs (repeat-length _ k _ cs rp) (good-repeat xs (Zero) k cs rp) a))
  (values n p))

(def-fns _ $ (many tower : (subterm many (Nat) k) -> (many (Tree) t))
  (let-match many k (Succ j) ((Zero) (Leaf (S (Z)))))
  (let ((many s)) (notail (tower j)))
  (Node s s))

(def-fns _ $ (many comb : (many (Tree) b) (subterm many (Nat) k) -> (many (Tree) t))
  (let-match many k (Succ j) ((Zero) b))
  (let ((many s)) (notail $ comb b j))
  (Node s b))

(def-fns _ $ (many run : -> (many (List (Nat)) out))
  (let ((many a) (erased _)) (naive-sum (tower 12)))
  (let ((many b) (erased _)) (dag-sum (tower 12)))
  (let ((many c) (erased _)) (dag-sum (tower 200)))
  (let ((many leaf)) (Leaf (S (Z))))
  (let ((many d) (erased _)) (dag-sum (comb (Node leaf leaf) 20000)))
  (Cons _ a $ Cons _ b $ Cons _ c $ Cons _ d $ Nil _))

run
