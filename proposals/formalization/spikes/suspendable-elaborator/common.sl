(def-adts $ (Tree : -> Type)
  enum
  (many TLeaf : (many (Nat) n) -> (Tree))
  (many TGen : -> (Tree))
  (many TNode : (many (Tree) l) (many (Tree) r) -> (Tree))
  (many TRun : (many (Nat) start) -> (Tree))
  (many TIf : (many (Tree) c) (many (Tree) th) (many (Tree) el) -> (Tree)))

(let ((many three)) (Succ $ Succ $ Succ $ Zero))

(def-adts
  ((Step : ((Nat) n) ((Nat) n2) -> Type)
    enum
    (many StepEven : (erased (Nat) m d) (erased (Double m d) dd) -> (Step (Succ (Succ d)) (Succ m)))
    (many StepOdd : (erased (Nat) m d t) (erased (Double (Succ m) d) dd) (erased (Mul three (Succ d) t) mm) -> (Step (Succ d) (Succ t))))
  ((Runs : ((Nat) s) ((Nat) a) -> Type)
    enum
    (many RunsHalt : -> (Runs (Succ (Zero)) (Zero)))
    (many RunsStep : (erased (Nat) s s2 a) (erased (Step s s2) st) (erased (Runs s2 a) r) -> (Runs s (Succ a))))
  ((Reach : ((Nat) s) ((Nat) n) ((Nat) k) -> Type)
    enum
    (many ReachRefl : (erased (Nat) s) -> (Reach s s (Zero)))
    (many ReachStep : (erased (Nat) s n n2 k) (erased (Reach s n k) r) (erased (Step n n2) st) -> (Reach s n2 (Succ k)))))

(def-fns _ $ (erased reach-runs : (erased (Nat) s n k a t) (subterm erased (Reach s n k) r) (erased (Runs n a) q) (erased (Add k a t) ad) -> (erased (Runs s t) out))
  (match erased r _
    ((ReachRefl _) (let-match erased ad (AddZero _)) q)
    ((ReachStep _ n1 _ k1 r1 st)
      (let-match erased ad (AddSucc _ _ c ad1))
      (reach-runs s n1 k1 (Succ a) (Succ c) r1 (RunsStep n1 n a st q) (add-succ-right k1 a c ad1)))))

(def-adts $ (Stepped : ((Nat) n) -> Type)
  enum
  (many Halted : -> (Stepped (Succ (Zero))))
  (many Stuck : -> (Stepped (Zero)))
  (many Next : (erased (Nat) n) (many (Nat) n2) (erased (Step n n2) st) -> (Stepped n)))

(def-fns _ $ (many step : (many (Nat) n) -> (many (Stepped n) r))
  (let-match many (nat-halve n) (H1 m d dd)
    ((HZ) (Stuck))
    ((H2 m2 d2 dd2) (Next _ (Succ m2) (StepEven m2 d2 dd2))))
  (let-match many (nat-zero-dec m) (IsSucc m1) ((IsZero) (let-match erased dd (D0)) (Halted)))
  (let ((many t) (erased mm)) (mul three n))
  (Next _ (Succ t) (StepOdd m1 d t dd mm)))

(def-adts $ (Elab : ((Tree) t) ((Nat) g) ((Nat) v) ((Nat) g2) -> Type)
  enum
  (many ELeaf : (erased (Nat) n g) -> (Elab (TLeaf n) g n g))
  (many EGen : (erased (Nat) g) -> (Elab (TGen) g g (Succ g)))
  (many ENode : (erased (Tree) l r) (erased (Nat) g a g1 b g2 c) (erased (Elab l g a g1) pa) (erased (Elab r g1 b g2) pb) (erased (Add a b c) pc) -> (Elab (TNode l r) g c g2))
  (many ERun : (erased (Nat) s a g) (erased (Runs s a) p) -> (Elab (TRun s) g a g))
  (many EIfZero : (erased (Tree) c th el) (erased (Nat) g g1 b g2) (erased (Elab c g (Zero) g1) pc) (erased (Elab th g1 b g2) pt) -> (Elab (TIf c th el) g b g2))
  (many EIfSucc : (erased (Tree) c th el) (erased (Nat) g m g1 b g2) (erased (Elab c g (Succ m) g1) pc) (erased (Elab el g1 b g2) pe) -> (Elab (TIf c th el) g b g2)))

(def-fns _ $ (many leaf : (many (Nat) start) -> (many (Tree) t))
  (match many (nat-zero-dec start) _
    ((IsZero) (TGen))
    ((IsSucc _) (TRun start))))

(def-fns _ $ (many chain : (subterm many (Nat) k) (many (Nat) start) -> (many (Tree) t))
  (let-match many k (Succ k1) ((Zero) (TGen)))
  (TNode (leaf start) $ notail $ chain k1 start))

(def-fns _ $ (many balanced : (subterm many (Nat) depth) (many (Nat) start) -> (many (Tree) t))
  (let-match many depth (Succ d) ((Zero) (leaf start)))
  (let ((many half)) (notail $ balanced d start))
  (TNode half half))
