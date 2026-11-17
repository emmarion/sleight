(let ((many m62)) (u62-modulus-many))
(let ((erased p0)) (prove-literal-lt 0 m62))

(def-fns _ $ (many to-u62 : (many (Nat) k) -> (many (Copy (U62)) u))
  (match many (nat-fits-u62 k) _
    ((Yes _ _ _ _ p) (MkCopy _ (MkU62 k p)))
    ((No _ _ _ _ _) (MkCopy _ (MkU62 0 p0)))))

(def-fns _ $ (many churn : (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _
    ((Zero) (Zero))
    ((Succ m) (churn m))))

(def-fns _ $ (many read : (many (Copy (U62)) c) -> (many (Nat) n))
  (let-match many c (MkCopy _ u))
  (let-match many u (MkU62 n _))
  n)

(def-fns _ $ (many miss : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (match many (nat-eq a b) _
    ((Equal _ _ _) (Zero))
    ((Unequal _ _ _ _ _) (Succ (Zero)))))

(def-fns _ $ (many trial : (many (Nat) k) (many (Nat) work) -> (many (Nat) bad))
  (let ((unique d)) (list-to-array _ (Cons _ (to-u62 0) $ Cons _ (to-u62 0) $ Cons _ (to-u62 0) $ Nil _)))
  (let ((many _)) (churn work))
  (let ((unique s)) (list-to-array _ (Cons _ (to-u62 (Succ k)) $ Cons _ (to-u62 (Succ (Succ k))) $ Nil _)))
  (let ((erased _) (unique r) (unique _) (erased p))
    (array-blit-imm _ _ _ _ _ s (Zero) d (Succ (Zero)) (Succ (Succ (Zero)))
      (SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (SpliceThere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (imm-all-of _ (ImmCopy _ (ImmU62)) _) (imm-all-of _ (ImmCopy _ (ImmU62)) _)))
  (let-match erased p (SpliceThere _ _ _ _ _ _ _ p1))
  (let-match erased p1 (SpliceHere _ _ _ _ _ _ _ p2))
  (let-match erased p2 (SpliceHere _ _ _ _ _ _ _ p3))
  (let-match erased p3 (SpliceNil _ _))
  (let ((many _)) (churn work))
  (let ((many dst)) (share r))
  (let ((many x)) (read (array-get-many _ _ dst (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _)))))
  (let ((many y)) (read (array-get-many _ _ dst (Succ (Succ (Zero))) _ (NthThere _ _ _ _ _ (NthThere _ _ _ _ _ (NthHere _ _ _))))))
  (let ((many b1)) (miss x (Succ k)))
  (let ((many b2)) (miss y (Succ (Succ k))))
  (let ((many t) (erased _)) (add b1 b2))
  t)

(def-fns _ $ (many run : (subterm many (Nat) n) (many (Nat) work) (many (Nat) acc) -> (many (Nat) bad))
  (match many n _
    ((Zero) acc)
    ((Succ m)
      (let ((many b)) (trial n work))
      (let ((many acc2) (erased _)) (add b acc))
      (run m work acc2))))

(run 1000 2000 0)
