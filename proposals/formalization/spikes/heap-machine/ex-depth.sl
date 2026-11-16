(def-fns _ $ (many depth : (subterm many (Stack) k) -> (many (Nat) n))
  (match many k _ ((KNil) 0) ((KLet _ _ rest) (Succ (notail $ depth rest)))))

(def-fns _ $ (many control-depth : (many (Control) c) -> (many (Nat) n))
  (match many c _ ((KRun _ _ k) (depth k)) ((KRet _ k) (depth k))))

(def-fns _ $ (many larger : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many (lt-dec a b) _ ((Yes _ _ _ _ _) b) ((No _ _ _ _ _) a)))

(def-fns _ $ (many max-depth : (subterm many (Nat) fuel) (many (List (Code)) fns) (many (Heap) h) (many (Nat) next) (erased (Below h next) inv)
    (many (Control) c) (many (Nat) best) (many (Nat) count) -> (many (Nat) deepest) (many (Nat) taken))
  (let-match many fuel (Succ f) ((Zero) (values best count)))
  (let-match many (step fns h next inv c) (StepOk _ _ _ h1 next1 inv1 c1 _ _) (else (values best count)))
  (tail $ max-depth f fns h1 next1 inv1 c1 (larger best (control-depth c1)) (Succ count)))

(def-fns _ $ (many cells : (subterm many (Nat) n) (many (Atom) tl) (many (List (Code)) after) -> (many (List (Code)) cs))
  (let-match many n (Succ m) ((Zero) after))
  (Cons _ (cell (AImm n) tl) (notail $ cells m (AVar 0) after)))

(def-fns _ $ (many append-program : (many (Nat) n) -> (many (Code) c))
  (lets (cells n nil (Cons _ (cell (AImm 99) nil) (Nil _))) (CCall 1 (Cons _ (AVar 1) $ Cons _ (AVar 0) $ Nil _))))

(def-fns _ $ (many measure : (many (Nat) n) -> (many (Pair (Nat) (Nat)) r))
  (let ((many deepest) (many taken)) (max-depth 2000 fns-b (HNil) 0 (BelowNil 0) (KRun (Nil _) (append-program n) (KNil)) 0 0))
  (MkPair _ _ deepest taken))

(Cons _ (measure 2) $ Cons _ (measure 8) $ Cons _ (measure 32) $ Nil _)
