; Accepted (round-7 review of 06): a four-input wrapper serves pick, and a wrapper whose relation parameter has
; Nth's dependent signature serves nth-p and also the prelude's NthLast. Needs std/list.sl, spec.sl and
; machine.sl first.
(def-adts $ (Out4 : (Type T1) (T1 a1) (Type T2) (T2 a2) (Type T3) (T3 a3) (Type T4) (T4 a4) (Type W)
    ((TyCtor (T1 b1) (T2 b2) (T3 b3) (T4 b4) (W w) -> Type) R) -> Type)
  enum
  (many Found4 : (erased Type T1) (erased T1 a1) (erased Type T2) (erased T2 a2) (erased Type T3) (erased T3 a3)
     (erased Type T4) (erased T4 a4) (erased Type W) (erased (TyCtor (T1 b1) (T2 b2) (T3 b3) (T4 b4) (W w) -> Type) R)
     (many W x) (erased (R a1 a2 a3 a4 x) p) -> (Out4 T1 a1 T2 a2 T3 a3 T4 a4 W R))
  (many Missing4 : (erased Type T1) (erased T1 a1) (erased Type T2) (erased T2 a2) (erased Type T3) (erased T3 a3)
     (erased Type T4) (erased T4 a4) (erased Type W) (erased (TyCtor (T1 b1) (T2 b2) (T3 b3) (T4 b4) (W w) -> Type) R)
     -> (Out4 T1 a1 T2 a2 T3 a3 T4 a4 W R)))
(def-fns _ $ (many pick2 : (many (Mem) m) (many (Nat) x) (many (Cmd) c1 c2) -> (many (Out4 (Mem) m (Nat) x (Cmd) c1 (Cmd) c2 (Cmd) Pick) r))
  (let-match many (pick m x c1 c2) (Picked _ _ _ _ c p) ((PickNo _ _ _ _) (Missing4 _ _ _ _ _ _ _ _ _ _)))
  (Found4 _ _ _ _ _ _ _ _ _ _ c p))
(def-adts $ (OutL : (Type A) ((List A) xs) ((Nat) i) ((TyCtor (Type B) ((List B) ys) ((Nat) j) (B y) -> Type) R) -> Type)
  enum
  (many FoundL : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (TyCtor (Type B) ((List B) ys) ((Nat) j) (B y) -> Type) R)
     (many A x) (erased (R A xs i x) p) -> (OutL A xs i R))
  (many MissingL : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (TyCtor (Type B) ((List B) ys) ((Nat) j) (B y) -> Type) R)
     -> (OutL A xs i R)))
(def-fns _ $ (many nth-p2 : (erased Type A) (many (List A) xs) (many (Nat) i) -> (many (OutL A xs i Nth) r))
  (let-match many (nth-p _ xs i) (NthOk _ _ _ x p) ((NthNo _ _ _) (MissingL _ _ _ _)))
  (FoundL _ _ _ _ x p))
(def-fns _ $ (erased last-one : (erased Type A) (erased A x) -> (erased (OutL A (Cons A x (Nil A)) (Zero) NthLast) r))
  (FoundL _ _ _ _ x (NthLastHere _ x (Nil A) (Zero) (LengthNil _))))
(let ((many m)) (MkMem (Cons _ (VNum (Succ (Zero))) $ Nil _) (Nil _)))
(comptime-match many (nth-p2 _ (Cons _ 5 $ Nil _) (Zero)) (FoundL _ _ _ _ v p))
(pick2 m (Zero) (CSkip) (COp $ OSet (Zero) 7))
