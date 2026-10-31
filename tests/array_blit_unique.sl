; expect: (MkPair _ _ (Cons _ 1 $ Cons _ 2 $ Nil _) $ Cons _ 0 $ Cons _ 1 $ Cons _ 2 $ Nil _)
(def-fns _ $ (many to-list : (erased (List (Copy (Nat))) xs) (subterm many (Array (Copy (Nat)) xs) a) -> (many (List (Nat)) r))
  (let-match many a (ACons _ _ h t) ((ANil _) (Nil _)))
  (let-match many h (MkCopy _ v))
  (Cons _ v (notail $ to-list _ t)))
(def-fns _ $ (many blit-test : -> (many (Pair (List (Nat)) (List (Nat))) r))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ 1) $ Cons _ (MkCopy _ 2) $ Nil _)))
  (let ((unique d)) (list-to-array _ (Cons _ (MkCopy _ 0) $ Cons _ (MkCopy _ 0) $ Cons _ (MkCopy _ 0) $ Nil _)))
  (let ((erased _) (unique r) (unique a2) (erased _))
    (array-blit _ _ _ _ _ a (Zero) d (Succ (Zero)) (Succ (Succ (Zero)))
      (SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (SpliceThere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)))
  (MkPair _ _ (to-list _ (share a2)) (to-list _ (share r))))
blit-test
; warns: tests/array_blit_unique.sl:3:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1309:1: note: `;! warn` for `Array` is here
