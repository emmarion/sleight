(def-adts $ (QStepL : ((List (Nat)) e n) ((Nat) x y) -> Type)
  enum
  (many MkQStepL : (erased (List (Nat)) e n) (erased (Nat) x a b y) (erased (Nth (Nat) n x a) pa) (erased (Nth (Nat) e a b) pb)
      (erased (Nth (Nat) n b y) py) -> (QStepL e n x y)))

(def-adts $ (QStepR : ((List (Nat)) e n) ((Nat) x y) -> Type)
  enum
  (many MkQStepR : (erased (List (Nat)) e n) (erased (Nat) x a y) (erased (Nth (Nat) e x a) pa) (erased (Nth (Nat) n a y) py)
      -> (QStepR e n x y)))

(def-adts $ (FitQ : ((List (Nat)) e n ks) ((Nat) x) ((Qn) q) -> Type)
  enum
  (many FQ0 : (erased (List (Nat)) e n ks) (erased (Nat) x) -> (FitQ e n ks x (Qask0)))
  (many FQ1 : (erased (List (Nat)) e n ks) (erased (Nat) x qa) (erased (Nth (Nat) ks x qa) pa) -> (FitQ e n ks x (Qask1 qa)))
  (many FQL : (erased (List (Nat)) e n ks) (erased (Nat) x qa y) (erased (Qn) q) (erased (Nth (Nat) ks x qa) pa) (erased (QStepL e n x y) s)
      (erased (FitQ e n ks y q) r) -> (FitQ e n ks x (QaskL qa q)))
  (many FQR : (erased (List (Nat)) e n ks) (erased (Nat) x qa y) (erased (Qn) q) (erased (Nth (Nat) ks x qa) pa) (erased (QStepR e n x y) s)
      (erased (FitQ e n ks y q) r) -> (FitQ e n ks x (QaskR qa q)))
  (many FQLR : (erased (List (Nat)) e n ks) (erased (Nat) x qa yl yr) (erased (Qn) ql qr) (erased (Nth (Nat) ks x qa) pa)
      (erased (QStepL e n x yl) sl) (erased (FitQ e n ks yl ql) rl) (erased (QStepR e n x yr) sr) (erased (FitQ e n ks yr qr) rr)
      -> (FitQ e n ks x (QaskLR qa ql qr)))
  (many FQLL : (erased (List (Nat)) e n ks) (erased (Nat) x qa xl c c2 y) (erased (Qn) q) (erased (QStepL e n x xl) s1)
      (erased (Nth (Nat) n xl c) pc) (erased (Nth (Nat) e c c2) pc2) (erased (Nth (Nat) ks c2 qa) pa) (erased (QStepL e n xl y) s2)
      (erased (FitQ e n ks y q) r) -> (FitQ e n ks x (QaskLL qa q)))
  (many FQRR : (erased (List (Nat)) e n ks) (erased (Nat) x qa xr y) (erased (Qn) q) (erased (QStepR e n x xr) s1)
      (erased (Nth (Nat) ks xr qa) pa) (erased (QStepR e n xr y) s2) (erased (FitQ e n ks y q) r) -> (FitQ e n ks x (QaskRR qa q))))

(def-adts $ (QGet : ((Nat) a) ((Qzt) t u) -> Type)
  enum
  (many QG5 : (erased (Qzt) t5 t6 t7 t8) -> (QGet 5 (QztNode t5 t6 t7 t8) t5))
  (many QG6 : (erased (Qzt) t5 t6 t7 t8) -> (QGet 6 (QztNode t5 t6 t7 t8) t6))
  (many QG7 : (erased (Qzt) t5 t6 t7 t8) -> (QGet 7 (QztNode t5 t6 t7 t8) t7))
  (many QG8 : (erased (Qzt) t5 t6 t7 t8) -> (QGet 8 (QztNode t5 t6 t7 t8) t8))
  (many QG9 : (erased (Qzt) t58 t9 t10 t11) -> (QGet 9 (QztHub t58 t9 t10 t11) t9))
  (many QG10 : (erased (Qzt) t58 t9 t10 t11) -> (QGet 10 (QztHub t58 t9 t10 t11) t10))
  (many QG11 : (erased (Qzt) t58 t9 t10 t11) -> (QGet 11 (QztHub t58 t9 t10 t11) t11))
  (many QGLo : (erased (Nat) a) (erased (Qzt) t58 t9 t10 t11 u) (erased (Lt a 9) l) (erased (QGet a t58 u) g)
      -> (QGet a (QztHub t58 t9 t10 t11) u)))

(def-adts $ (QLeaf : ((Qzt) t) ((Qn) q1 q2 q3) -> Type)
  enum
  (many QLHere : (erased (Qn) q1 q2 q3) (erased (Qzt) t) -> (QLeaf (QztLeaf q1 q2 q3 t) q1 q2 q3))
  (many QLThere : (erased (Qn) q1 q2 q3 r1 r2 r3) (erased (Qzt) t) (erased (QLeaf t q1 q2 q3) l) -> (QLeaf (QztLeaf r1 r2 r3 t) q1 q2 q3)))

(def-adts $ (QztFit : ((List (Nat)) e n ks) ((Qzt) qt) ((Nat) x1) -> Type)
  enum
  (many MkQztFit : (erased (List (Nat)) e n ks) (erased (Qzt) qt t1 t2 t3) (erased (Nat) x1 x2 x3 a1 a2 a3 z1 z2 z3) (erased (Qn) q1 q2 q3)
      (erased (Nth (Nat) n x1 x2) p2) (erased (Nth (Nat) n x2 x3) p3) (erased (Nth (Nat) ks x1 a1) k1) (erased (Nth (Nat) ks x2 a2) k2)
      (erased (Nth (Nat) ks x3 a3) k3) (erased (QGet a1 qt t1) g1) (erased (QGet a2 t1 t2) g2) (erased (QGet a3 t2 t3) g3)
      (erased (QLeaf t3 q1 q2 q3) lf) (erased (QStepR e n x1 z1) s1) (erased (FitQ e n ks z1 q1) f1) (erased (QStepR e n x2 z2) s2)
      (erased (FitQ e n ks z2 q2) f2) (erased (QStepR e n x3 z3) s3) (erased (FitQ e n ks z3 q3) f3) -> (QztFit e n ks qt x1)))

(def-adts $ (HasFit : ((Nat) d) ((List (Nat)) e n ks) ((Qzt) qt) -> Type)
  enum
  (many MkHasFit : (erased (Nat) d x) (erased (List (Nat)) e n ks) (erased (Qzt) qt) (erased (Lt x d) lx) (erased (QztFit e n ks qt x) r)
      -> (HasFit d e n ks qt)))
