(let ((many m62)) (u62-modulus-many))
(let ((erased p0)) (prove-literal-lt 0 m62))

(def-fns _ $ (many to-u62 : (many (Nat) k) -> (unique (U62) u))
  (match many (nat-fits-u62 k) _
    ((Yes _ _ _ _ p) (MkU62 k p))
    ((No _ _ _ _ _) (MkU62 0 p0))))

(def-fns _ $ (many churn : (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many n (Succ m) ((Zero) (Zero)))
  (tail (churn m)))

(def-fns _ $ (many miss : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (match many (nat-eq a b) _
    ((Equal _ _ _) (Zero))
    ((Unequal _ _ _ _ _) (Succ (Zero)))))

;! suppress warn ACons
;! suppress warn Array
(def-fns _ $ (many trial : (many (Nat) k) (many (Nat) work) -> (many (Nat) bad))
  (let ((unique dst))
    (ACons _ _ (Vacant _ vacant-slot) (ACons _ _ (Vacant _ vacant-slot)
      (ACons _ _ (Vacant _ vacant-slot) (ANil (MaybeUninit (USlotItem (U62))))))))
  (let ((many _)) (churn work))
  (let ((unique a)) (to-u62 (Succ k)))
  (let ((unique b)) (to-u62 (Succ (Succ k))))
  (let ((unique src))
    (ACons _ _ (Init _ (MkUSlotItem _ _ _ (place-at _ a)))
      (ACons _ _ (Init _ (MkUSlotItem _ _ _ (place-at _ b))) (ANil (MaybeUninit (USlotItem (U62)))))))
  (let ((erased _) (erased _) (erased _) (unique r) (unique _) (erased p) (erased _) (erased _))
    (array-move-imm _ _ _ _ _ src (Zero) dst (Succ (Zero)) (Succ (Succ (Zero)))
      (SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (SpliceThere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (imm-all-of _ (ImmMaybe _ (ImmUSlot _ (ImmU62))) _) (imm-all-of _ (ImmMaybe _ (ImmUSlot _ (ImmU62))) _)))
  (let-match erased p (SpliceThere _ _ _ _ _ _ _ p1))
  (let-match erased p1 (SpliceHere _ _ _ _ _ _ _ p2))
  (let-match erased p2 (SpliceHere _ _ _ _ _ _ _ p3))
  (let-match erased p3 (SpliceNil _ _))
  (let ((many _)) (churn work))
  (let-match unique r (ACons _ _ _ r1))
  (let-match unique r1 (ACons _ _ e1 r2))
  (let-match unique r2 (ACons _ _ e2 _))
  (let-match unique e1 (Init _ i1))
  (let-match unique e2 (Init _ i2))
  (let-match unique i1 (MkUSlotItem _ _ _ pa))
  (let-match unique i2 (MkUSlotItem _ _ _ pb))
  (let ((unique ua)) (unplace-at _ _ _ pa))
  (let ((unique ub)) (unplace-at _ _ _ pb))
  (let-match unique ua (MkU62 x _))
  (let-match unique ub (MkU62 y _))
  (let ((many b1)) (miss x (Succ k)))
  (let ((many b2)) (miss y (Succ (Succ k))))
  (let ((many t) (erased _)) (add b1 b2))
  t)
;! restore warn Array
;! restore warn ACons

(def-fns _ $ (many run : (subterm many (Nat) n) (many (Nat) work) (many (Nat) acc) -> (many (Nat) bad))
  (let-match many n (Succ m) ((Zero) acc))
  (let ((many b)) (trial n work))
  (let ((many acc2) (erased _)) (add b acc))
  (tail (run m work acc2)))

(run 1000 2000 0)
