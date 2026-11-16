(def-adts
  ((LookupDec : ((Heap) h) ((Nat) a) -> Type)
    enum
    (many LkHit : (erased (Heap) h) (erased (Nat) a) (many (Block) blk) (erased (Lookup h a blk) p) -> (LookupDec h a))
    (many LkMiss : (erased (Heap) h) (erased (Nat) a) (erased (Fresh h a) p) -> (LookupDec h a))))

(def-fns _ $ (many lookup-dec : (subterm many (Heap) h) (many (Nat) a) -> (many (LookupDec h a) r))
  (let-match many h (HCons b other rest) ((HNil) (LkMiss _ _ $ FreshNil a)))
  (let-match many (nat-dec a b) (NDDiff _ _ n) ((NDSame _) (LkHit _ _ other $ LkHere a other rest)))
  (match many (notail $ lookup-dec rest a) _
    ((LkHit _ _ blk p) (LkHit _ _ blk $ LkThere a b blk other rest n p))
    ((LkMiss _ _ p) (LkMiss _ _ $ FreshCons a b other rest n p))))

(def-fns _ $ (many update : (subterm many (Heap) h) (many (Nat) a) (many (Block) blk) (erased (Block) old) (erased (Lookup h a old) lk) ->
    (many (Heap) h2) (erased (Update h a blk h2) p))
  (let-match many h (HCons b other rest) (absurd (HNil) lk))
  (let-match many (nat-dec a b) (NDDiff _ _ n) ((NDSame _) (values (HCons a blk rest) (UpHere a other blk rest))))
  (let-match erased lk (LkThere _ _ _ _ _ _ p) (absurd (LkHere _ _ _) (neq-irrefl a n)))
  (let ((many rest2) (erased q)) (notail $ update rest a blk old p))
  (values (HCons b other rest2) (UpThere a b blk other rest rest2 n q)))

(def-adts
  ((Below : ((Heap) h) ((Nat) n) -> Type)
    enum
    (many BelowNil : (erased (Nat) n) -> (Below (HNil) n))
    (many BelowCons : (erased (Nat) a) (erased (Block) blk) (erased (Heap) rest) (erased (Nat) n)
       (erased (Lt a n) lt) (erased (Below rest n) p) -> (Below (HCons a blk rest) n))))

(def-fns _ $ (erased below-fresh : (erased (Heap) h) (erased (Nat) n) (subterm erased (Below h n) p) -> (erased (Fresh h n) f))
  (match erased p _
    ((BelowNil _) (FreshNil n))
    ((BelowCons a blk rest _ lt q) (FreshCons n a blk rest (NeqGt n a lt) (below-fresh rest n q)))))

(def-fns _ $ (erased below-succ : (erased (Heap) h) (erased (Nat) n) (subterm erased (Below h n) p) -> (erased (Below h (Succ n)) q))
  (match erased p _
    ((BelowNil _) (BelowNil (Succ n)))
    ((BelowCons a blk rest _ lt q) (BelowCons a blk rest (Succ n) (lt-weaken a n lt) (below-succ rest n q)))))

(def-fns _ $ (erased below-update : (erased (Heap) h) (erased (Nat) n) (erased (Nat) a) (erased (Block) blk) (erased (Heap) h2)
    (erased (Below h n) p) (subterm erased (Update h a blk h2) u) -> (erased (Below h2 n) q))
  (match erased u _
    ((UpHere _ old _ rest) (let-match erased p (BelowCons _ _ _ _ lt q)) (BelowCons a blk rest n lt q))
    ((UpThere _ b _ other rest rest2 ne u2)
      (let-match erased p (BelowCons _ _ _ _ lt q))
      (BelowCons b other rest2 n lt (below-update rest n a blk rest2 q u2)))))

(def-fns _ $ (many alloc : (many (Heap) h) (many (Nat) next) (erased (Below h next) inv) (many (Block) blk) ->
    (many (HCons next blk h) is h2) (many (Succ next) is next2) (erased (Below h2 next2) inv2) (erased (Alloc h next blk h2) d))
  (values (HCons next blk h) (Succ next)
    (BelowCons next blk h (Succ next) (lt-succ next) (below-succ h next inv))
    (MkAlloc h next blk (below-fresh h next inv))))
