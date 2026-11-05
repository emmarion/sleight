; c is red4's int for the colour e: 0 for C0, the digit d plus one otherwise.
(def-adts $ (ColN : ((Col) e) ((Nat) c) -> Type)
  enum
  (many ColZ : -> (ColN (C0) (Zero)))
  (many ColS : (erased (Nat) d) (erased (Col) e) (erased (CD d e) cd) -> (ColN e (Succ d))))

(def-fns _ $ (erased r4k-coln : (erased (Col) e) -> (erased (Nat) c) (erased (Coercible (Shared) (Col) e (Shared) (Nat) c) p) (erased (ColN e c) n))
  (let-match erased r4-e0 (Refl _ _))
  (let-match erased r4-one (Refl _ _))
  (let-match erased r4-e2 (Refl _ _))
  (let-match erased r4-e3 (Refl _ _))
  (match erased e _
    ((C0) (values 0 (coercible-tag (Shared) C0) (ColZ)))
    ((C1) (values 1 (coercible-tag (Shared) C1) (ColS (Zero) (C1) (Cd0))))
    ((C2) (values 2 (coercible-tag (Shared) C2) (ColS (Succ (Zero)) (C2) (Cd1))))
    ((C3) (values 3 (coercible-tag (Shared) C3) (ColS (Succ (Succ (Zero))) (C3) (Cd2))))))

(def-fns _ $ (erased r4k-coln-lt : (erased (Col) e) (erased (Nat) c) (erased (ColN e c) n) -> (erased (Lt c 4) l))
  (let-match erased r4-e4s (Refl _ _))
  (let ((erased z3)) (Succ (Succ (Succ (Zero)))))
  (let-match erased n (ColS _ _ cd) ((ColZ) (LtZ z3)))
  (match erased cd _
    ((Cd0) (LtS (Zero) z3 (LtZ (Succ (Succ (Zero))))))
    ((Cd1) (LtS (Succ (Zero)) z3 (LtS (Zero) (Succ (Succ (Zero))) (LtZ (Succ (Zero))))))
    ((Cd2) (LtS (Succ (Succ (Zero))) z3 (LtS (Succ (Zero)) (Succ (Succ (Zero))) (LtS (Zero) (Succ (Zero)) (LtZ (Zero))))))))

; x, 3p plus the digit d of e, is p's child of colour e.
(def-fns _ $ (erased r4k-kid : (erased (Nat) p q x d) (erased (Col) e) (erased (CD d e) cd) (erased (Thrice p q) tq) (erased (Add q d x) ad) -> (erased (Kid p e x) k))
  (let ((erased a0)) (add-zero-right q))
  (match erased cd _
    ((Cd0) (let-match erased (add-fn q (Zero) x q ad a0) (Refl _ _)) (Ki1 p q tq))
    ((Cd1) (let-match erased (add-fn q _ x _ ad (add-succ-right q _ _ a0)) (Refl _ _)) (Ki2 p q tq))
    ((Cd2) (let-match erased (add-fn q _ x _ ad (add-succ-right q _ _ (add-succ-right q _ _ a0))) (Refl _ _)) (Ki3 p q tq))))

(def-fns _ $ (erased r4k-sel0 : (erased (List Cnt) vs) (erased (Nat) j p) (erased (Ctree) t) (erased (Tally vs j p t) b) -> (erased (CtSel t (C0) (CEmpty)) s))
  (match erased b _
    ((TaL _ _ _ _ _ _ k) (match erased k (((CtSel t (C0) (CEmpty)) s)) ((HE _) (SelE (C0))) ((HL lf _) (SelL lf (C0)))))
    ((TaN _ _ _ _ t1 t2 t3 _ _ _ _ _ cn) (match erased cn (((CtSel t (C0) (CEmpty)) s)) ((CnE) (SelE (C0))) ((CnN _ _ _ _) (SelN0 t1 t2 t3))))))

(def-fns _ $ (erased r4k-sel-leaf : (erased (List Cnt) vs) (erased (Nat) p) (erased (Ctree) t) (erased (Col) e) (erased (Tally vs (Zero) p t) b) -> (erased (CtSel t e (CEmpty)) s))
  (let-match erased b (TaL _ _ _ _ _ _ k))
  (match erased k (((CtSel t e (CEmpty)) s)) ((HE _) (SelE e)) ((HL lf _) (SelL lf e))))

; red4's kempe_flat result for h: None, the Kempe tree kt being empty, or Some uc, uc holding the counts of kt.
(def-adts $ (R4Out : ((Nat) h) ((Ctree) kt) -> Type)
  enum
  (many R4None : (erased (Nat) h) -> (R4Out h (CEmpty)))
  (many R4Some : (erased (Nat) h N) (erased (Ctree) kt) (erased (List Cnt) vs) (many (Bytes vs) uc) (erased (Sz cnt-w vs N) zv) (erased (Tally vs (Succ h) (Zero) kt) tb)
      (erased (Lt (Succ h) 17) hl) -> (R4Out h kt)))

; red4's go k p of flat_look: the count in t of the colours l after the prefix p of k colours, j to go.
(def-fns _ $ (many r4-look-go : (many (Nat) h) (erased (Lt (Succ h) 17) hl) (erased (List Cnt) vs) (many (Bytes vs) uc) (erased (Nat) N) (erased (Sz cnt-w vs N) zv)
    (many (Nat) k p) (subterm many (List (Col)) l) (erased (Nat) j) (erased (Add k j (Succ h)) ad) (erased (Ctree) t) (erased (Tally vs j p t) b)
    -> (many (Nat) n) (erased (CtSub t l n) s))
  (let-match erased r4-e0 (Refl _ _))
  (let-match erased r4-e3 (Refl _ _))
  (let-match erased r4-e4s (Refl _ _))
  (let ((erased hb)) (lt-trans (Succ h) 17 u62-modulus hl r4-17-u62))
  (let ((erased kb)) (lt-le-trans k (Succ (Succ h)) u62-modulus (add-le-left k j (Succ h) ad) (LtS _ _ hb)))
  (let-match many l (Cons _ e l1)
    ((Nil _)
      (match many (u62-eq k (u62-inc h hb) kb hb) _
        ((Equal _ _ _)
          (let-match erased (add-cancel (Succ h) j (Zero) (Succ h) ad (add-zero-right (Succ h))) (Refl _ _))
          (let-match erased b (TaL _ _ n _ x r _))
          (values (cnt-get-many vs uc N zv p n x) (SubNil t n r)))
        ((Unequal _ _ _ _ ap)
          (let-match erased j (Succ _) (absurd (Zero) (let-match erased (add-fn k (Zero) (Succ h) k ad (add-zero-right k)) (Refl _ _)) (apart-irrefl k ap)))
          (let-match erased b (TaN _ _ _ _ t1 t2 t3 _ _ _ _ _ cn))
          (values 0 (SubNil t 0 (match erased cn (((CtRoot t (Zero)) r)) ((CnE) (RootE)) ((CnN _ _ _ _) (RootN t1 t2 t3)))))))))
  (let ((erased c) (erased cp) (erased cn)) (r4k-coln e))
  (let ((many cv)) (coerce e cp))
  (let ((erased cl)) (r4k-coln-lt e c cn))
  (let ((erased cb)) (lt-trans c 4 u62-modulus cl r4-four-u62))
  (let-match many (nat-zero-dec cv) (IsSucc d)
    ((IsZero) (let-match erased cn (ColZ)) (values 0 (SubCons t (CEmpty) (C0) l1 0 (r4k-sel0 vs j p t b) (empty-sub l1)))))
  (let-match many (u62-lt-dec 3 cv r4-three-u62 cb) (No _ _ _ _ _) (absurd (Yes _ _ _ _ l3) (lt-irrefl 3 (lt-le-trans 3 c 3 l3 cl))))
  (let ((erased h62)) (lt-succ-left h u62-modulus hb))
  (let-match many (u62-lt-dec h k h62 kb) (No _ _ _ _ le)
    ((Yes _ _ _ _ hk)
      (let-match erased j (Zero)
        (absurd (Succ j1)
          (let ((erased c1) (erased ec) (erased a1)) (add-succ-right-inv k j1 (Succ h) ad))
          (let-match erased ec (Refl _ _))
          (lt-irrefl h (lt-le-trans h k h hk (add-le-left k j1 h a1)))))
      (values 0 (SubCons t (CEmpty) e l1 0 (r4k-sel-leaf vs p t e b) (empty-sub l1)))))
  (let-match erased j (Succ j1)
    (absurd (Zero)
      (let-match erased (add-fn k (Zero) (Succ h) k ad (add-zero-right k)) (Refl _ _))
      (lt-irrefl (Succ h) (le-lt-succ (Succ h) h le))))
  (let-match erased cn (ColS _ _ cd))
  (let-match erased b (TaN _ _ _ q _ _ _ _ tq _ _ _ _))
  (let ((erased x) (erased ax)) (add q d))
  (let ((erased u) (erased bu) (erased sl)) (tally-down vs j1 p x t e b (r4k-kid p q x d e cd tq ax)))
  (let ((erased Nb)) (sz-u62 cnt-w vs N zv))
  (let ((erased xb)) (lt-trans x N u62-modulus (tally-lt vs j1 x N u bu zv) Nb))
  (let ((erased sb)) (lt-le-trans (Succ x) (Succ N) u62-modulus (LtS x N (tally-lt vs j1 x N u bu zv)) (LtS N u62-modulus Nb)))
  (let ((erased pb)) (lt-trans p N u62-modulus (tally-lt vs (Succ j1) p N t b zv) Nb))
  (let ((erased qb)) (lt-le-trans q (Succ x) u62-modulus (add-le-left q d x ax) (LtS x u62-modulus xb)))
  (let ((many s1)) (u62-add (r4-x3 p q tq pb qb) cv (Succ x) (add-succ-right q d x ax) sb))
  (let ((many k1)) (u62-inc k (lt-le-trans (Succ k) (Succ (Succ h)) u62-modulus (LtS k (Succ h) (le-lt-succ k h le)) (LtS (Succ h) u62-modulus hb))))
  (let ((many n) (erased s2)) (tail $ r4-look-go h hl vs uc N zv k1 (u62-dec x s1 sb) l1 j1 (add-shift k j1 (Succ h) ad) u bu))
  (values n (SubCons t u e l1 n sl s2)))

; red4's flat_look h o, applied to the colours l.
(def-fns _ $ (many r4-flat-look : (many (Nat) h) (erased (Ctree) kt) (many (R4Out h kt) o) (many (List (Col)) l) -> (many (Nat) n) (erased (CtSub kt l n) s))
  (let-match erased r4-e0 (Refl _ _))
  (match many o _
    ((R4None _) (values 0 (empty-sub l)))
    ((R4Some _ N _ vs uc zv tb hl) (tail $ r4-look-go h hl vs uc N zv 0 0 l (Succ h) (AddZero (Succ h)) kt tb))))

; Two readings of node g's word agree on its part sel.
(def-fns _ $ (erased r4k-fld-at : (erased (List (Copy (Nat))) xs) (erased (Nat) g w b cm ftr fu f w1 b1 cm1 ftr1 fu1 f1) (erased (Bool) sel) (erased (WElt xs g w) x)
    (erased (NWd w b cm ftr fu) d) (erased (Fld sel ftr fu f) fd) (erased (WElt xs g w1) x1) (erased (NWd w1 b1 cm1 ftr1 fu1) d1) (erased (Fld sel ftr1 fu1 f1) fd1)
    -> (erased (Eq (Nat) f f1) e))
  (let-match erased (welt-fn xs g w w1 x x1) (Refl _ _))
  (let ((erased e1) (erased _) (erased _)) (nwd-fn w b cm ftr fu b1 cm1 ftr1 fu1 d d1))
  (let-match erased e1 (Refl _ _))
  (let-match erased (r4g-nwd-fu w b cm ftr fu b1 cm1 ftr1 fu1 d d1) (Refl _ _))
  (r4g-fld-fn sel ftr fu f f1 fd fd1))

; A node whose part sel is 0 holds the empty tree there.
(def-fns _ $ (erased r4k-np0 : (erased (List (Copy (Nat))) xs) (erased (Nat) j g w b cm ftr fu) (erased (Gtree) c u) (erased (Bool) sel) (erased (NPart xs j g c sel u) np)
    (erased (WElt xs g w) x) (erased (NWd w b cm ftr fu) d) (erased (Fld sel ftr fu (Zero)) fd) -> (erased (Eq (Gtree) u (GEmpty)) e))
  (match erased np _
    ((NpE _ _ _ _ _ _ _ _ _ _ _ _ _) (Refl _ u))
    ((NpL _ _ wa ba ma fa ua f _ _ _ xa da fa1 lm)
      (let-match erased (r4k-fld-at xs g w b cm ftr fu (Zero) wa ba ma fa ua f sel x d fd xa da fa1) (Refl _ _))
      (leafm0 u lm))
    ((NpN _ _ _ wa ba ma fa ua _ _ _ _ _ _ _ _ _ xa da fa1 _ _ _ _)
      (match erased (r4k-fld-at xs g w b cm ftr fu (Zero) wa ba ma fa ua (Succ (Zero)) sel x d fd xa da fa1) (((Eq (Gtree) u (GEmpty)) e))))))

; red4's killed flag kd: once set, the Kempe tree is empty; while clear, uc and ul hold ctu, and the node words laid out from s0 hold gtr and gtu.
(def-adts $ (Kld : ((Bool) kd) ((Nat) h) ((Gtree) s0) ((List Cnt) vs) ((List (U8)) us) ((List (Copy (Nat))) xs) ((Ctree) ctu) ((Gtree) gtr gtu) -> Type)
  enum
  (many KlY : (erased (Nat) h) (erased (Gtree) s0) (erased (List Cnt) vs) (erased (List (U8)) us) (erased (List (Copy (Nat))) xs)
      -> (Kld (BTrue) h s0 vs us xs (CEmpty) (GEmpty) (GEmpty)))
  (many KlN : (erased (Nat) h) (erased (Gtree) s0) (erased (List Cnt) vs) (erased (List (U8)) us) (erased (List (Copy (Nat))) xs) (erased (Ctree) ctu)
      (erased (Gtree) gtr gtu) (erased (Tally vs (Succ h) (Zero) ctu) tb) (erased (Lc us h (Zero) ctu) lc) (erased (NPart xs h (Zero) s0 (BTrue) gtr) pt)
      (erased (NPart xs h (Zero) s0 (BFalse) gtu) pu) -> (Kld (BFalse) h s0 vs us xs ctu gtr gtu)))

; red4's finished (): true when ctu or gtr is empty, or when gu is, which kills; false otherwise, the root word's gtr part not 0.
(def-adts $ (FinR : ((Bool) kd) ((List (Copy (Nat))) xs) ((Ctree) ctu) ((Gtree) gtr gtu) -> Type)
  enum
  (many FrCtu : (erased (Bool) kd) (erased (List (Copy (Nat))) xs) (erased (Gtree) gtr gtu) -> (FinR kd xs (CEmpty) gtr gtu))
  (many FrGtr : (erased (List (Copy (Nat))) xs) (erased (Ctree) ctu) (erased (Gtree) gtu) -> (FinR (BFalse) xs ctu (GEmpty) gtu))
  (many FrKill : (erased (List (Copy (Nat))) xs) (erased (Ctree) ctu) (erased (Gtree) gtr) -> (FinR (BFalse) xs ctu gtr (GEmpty)))
  (many FrGo : (erased (List (Copy (Nat))) xs) (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (erased (Nat) w b cm ftr fu) (erased (WElt xs (Zero) w) x)
      (erased (NWd w b cm ftr fu) d) (erased (Apart (Nat) Lt ftr (Zero)) fz) -> (FinR (BFalse) xs ctu gtr gtu)))

; red4's if !killed || gb ul 0 = 0 then None else Some uc, ending kempe_flat.
(def-fns _ $ (many r4k-out : (many (Bool) kd) (many (Nat) h) (erased (Lt (Succ h) 17) hl) (erased (Nat) N len) (erased (Gtree) s0) (erased (List Cnt) vs) (unique (Bytes vs) uc)
    (erased (Sz cnt-w vs N) zv) (erased (List (U8)) us) (unique (Bytes us) ul) (erased (Sz flag-w us len) zu) (erased (Lt (Zero) len) lp) (erased (List (Copy (Nat))) xs)
    (erased (Ctree) ctu) (erased (Gtree) gtr gtu) (erased (Kld kd h s0 vs us xs ctu gtr gtu) kl) -> (many (R4Out h ctu) r))
  (let-match erased r4-e0 (Refl _ _))
  (let-match many kd (BFalse) ((BTrue) (let-match erased kl (KlY _ _ _ _ _)) (R4None h)))
  (let-match erased kl (KlN _ _ _ _ _ _ _ _ tb lc _ _))
  (let ((unique _) (many v) (erased x) (erased vb)) (r4-flag us ul len zu 0 lp))
  (let-match many (u62-eq v (Zero) vb u62-modulus-pos) (Unequal _ _ _ _ _)
    ((Equal _ _ _) (let-match erased (lc-zero us h (Zero) ctu lc x (tally-canon vs (Succ h) (Zero) ctu tb)) (Refl _ _)) (R4None h)))
  (R4Some h N ctu vs (share uc) zv tb hl))

; The states a walk from nothing over parts of ctr reaches.
(def-adts $ (Rch : ((Nat) h) ((Ctree) ctr c) ((List (Nat)) T) -> Type)
  enum
  (many RchZ : (erased (Nat) h) (erased (Ctree) ctr) -> (Rch h ctr (CEmpty) (Nil (Nat))))
  (many RchW : (erased (Nat) h p) (erased (Ctree) ctr y c c2) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (erased (Rch h ctr c T) r)
      (erased (LW h ctr y pre p c T c2 T2) w) -> (Rch h ctr c2 T2)))

(def-fns _ $ (erased r4k-rch-bit : (erased (Nat) h ti) (erased (Ctree) ctr c) (erased (List (Nat)) T) (erased (List (Col)) tp) (subterm erased (Rch h ctr c T) r)
    (erased (RIdx tp ti) ri) (erased (Length (Col) tp (Succ h)) le) -> (erased (Bit) b) (erased (Ctree) x) (erased (CtAt c tp x) a) (erased (Lf x b) l) (erased (MemB ti T b) m))
  (let-match erased r (RchW _ p _ y c0 _ T0 _ pre r0 w) ((RchZ _ _) (values (Bit0) (CEmpty) (r4c-ctat-e tp) (LfE) (MbN ti (Nil _) (NotInNil ti)))))
  (let ((erased b0) (erased x0) (erased a0) (erased l0) (erased m0)) (r4k-rch-bit h ti ctr c0 T0 tp r0 ri le))
  (r4c-lw-bit h p ti ctr y c0 c x0 T0 T pre tp b0 w ri le a0 l0 m0))

(def-fns _ $ (erased r4k-lw-in : (erased (Nat) h p x) (erased (Ctree) ctr y c c2) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (subterm erased (LW h ctr y pre p c T c2 T2) w)
    (erased (In x T) i) -> (erased (In x T2) r))
  (let-match erased w (LwN _ _ y1 y2 y3 _ _ q _ _ c1 cb _ _ T1 Tb _ w1 w2 w3)
    ((LwE _ _ _ _ _ _) i)
    ((LwL _ _ _ _ _ _ _ _ _ _ _ _ ad) (match erased ad (((In x T2) r)) ((CadHas _ _ _ _ _ _) i) ((CadNew _ _ _ _ _ _ _) (InThere x p T i)))))
  (r4k-lw-in h (Succ (Succ q)) x ctr y3 cb c2 Tb T2 (Cons _ (C3) pre) w3
    (r4k-lw-in h (Succ q) x ctr y2 c1 cb T1 Tb (Cons _ (C2) pre) w2 (r4k-lw-in h q x ctr y1 c c1 T T1 (Cons _ (C1) pre) w1 i))))

(def-fns _ $ (erased r4k-mi1-grow : (erased (Nat) h p i) (erased (Ctree) ctr y c c2 u) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (erased (MI1 T i u) m)
    (erased (LW h ctr y pre p c T c2 T2) w) -> (erased (MI1 T2 i u) r))
  (match erased m _ ((Mi1E _ _) (Mi1E T2 i)) ((Mi1In _ _ _ q) (Mi1In T2 i u (r4k-lw-in h p i ctr y c c2 T T2 pre w q)))))

(def-fns _ $ (erased r4k-mi-grow : (erased (Nat) h p j n) (erased (Ctree) ctr y c c2 t) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (subterm erased (MI T j n t) m)
    (erased (LW h ctr y pre p c T c2 T2) w) -> (erased (MI T2 j n t) r))
  (match erased m _
    ((MiL _ _ qp _ t1 t2 t3 tp s1 s2 s3 m1 m2 m3)
      (MiL T2 n qp t t1 t2 t3 tp s1 s2 s3 (r4k-mi1-grow h p qp ctr y c c2 t1 T T2 pre m1 w) (r4k-mi1-grow h p (Succ qp) ctr y c c2 t2 T T2 pre m2 w)
        (r4k-mi1-grow h p (Succ (Succ qp)) ctr y c c2 t3 T T2 pre m3 w)))
    ((MiN _ j1 _ qp _ t1 t2 t3 tp s1 s2 s3 m1 m2 m3)
      (MiN T2 j1 n qp t t1 t2 t3 tp s1 s2 s3 (r4k-mi-grow h p j1 qp ctr y c c2 t1 T T2 pre m1 w) (r4k-mi-grow h p j1 (Succ qp) ctr y c c2 t2 T T2 pre m2 w)
        (r4k-mi-grow h p j1 (Succ (Succ qp)) ctr y c c2 t3 T T2 pre m3 w)))))

(def-fns _ $ (erased r4k-mi-empty : (erased (List (Nat)) R) (subterm erased (Nat) j) (erased (Nat) p) -> (erased (MI R j p (CEmpty)) r))
  (let ((erased qp) (erased tp)) (thrice-exists p))
  (let ((erased E)) (CEmpty))
  (match erased j _
    ((Zero) (MiL R p qp E E E E tp (SelE (C1)) (SelE (C2)) (SelE (C3)) (Mi1E R qp) (Mi1E R (Succ qp)) (Mi1E R (Succ (Succ qp)))))
    ((Succ j1) (MiN R j1 p qp E E E E tp (SelE (C1)) (SelE (C2)) (SelE (C3)) (r4k-mi-empty R j1 qp) (r4k-mi-empty R j1 (Succ qp)) (r4k-mi-empty R j1 (Succ (Succ qp)))))))

(def-fns _ $ (erased r4k-lw-mi1 : (erased (Nat) h p) (erased (Ctree) ctr y c c2) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (erased (LW h ctr y pre p c T c2 T2) w)
    (erased (CtH (Zero) y) hy) (erased (Rch h ctr c T) rc) -> (erased (MI1 T2 p y) r))
  (let-match erased w (LwL _ _ lf _ _ _ _ _ _ ri le _ ad) ((LwE _ _ _ _ _ _) (Mi1E T2 p)) (absurd (LwN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hy))
  (let-match erased ad (CadHas _ lf2 _ _ _ ah) ((CadNew _ _ _ _ _ _ _) (Mi1In T2 p y (InHere p T))))
  (let ((erased b0) (erased x0) (erased a0) (erased l0) (erased m0)) (r4k-rch-bit h p ctr c T pre rc ri le))
  (let-match erased (ctat-fn c x0 (CLeaf lf2) pre a0 ah) (Refl _ _))
  (let-match erased l0 (LfL _))
  (let-match erased m0 (MbY _ _ i))
  (Mi1In T2 p y i))

; The walk over y, of j + 1 more colours, leaves each trace of y in T2.
(def-fns _ $ (erased r4k-lw-mi : (erased (Nat) h j p) (erased (Ctree) ctr y c c2) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (subterm erased (LW h ctr y pre p c T c2 T2) w)
    (erased (CtH (Succ j) y) hy) (erased (Rch h ctr c T) rc) -> (erased (MI T2 j p y) m))
  (let-match erased w (LwN _ _ y1 y2 y3 _ _ q tq _ c1 cb _ _ T1 Tb _ w1 w2 w3) ((LwE _ _ _ _ _ _) (r4k-mi-empty T j p)) (absurd (LwL _ _ _ _ _ _ _ _ _ _ _ _ _) hy))
  (let-match erased hy (HN _ _ _ _ h1 h2 h3))
  (let ((erased p1) (erased p2) (erased p3)) (values (Cons _ (C1) pre) (Cons _ (C2) pre) (Cons _ (C3) pre)))
  (let ((erased r1)) (RchW h q ctr y1 c c1 T T1 p1 rc w1))
  (let ((erased r2)) (RchW h (Succ q) ctr y2 c1 cb T1 Tb p2 r1 w2))
  (let ((erased s1) (erased s2) (erased s3)) (values (SelN1 y1 y2 y3) (SelN2 y1 y2 y3) (SelN3 y1 y2 y3)))
  (match erased j _
    ((Zero)
      (MiL T2 p q y y1 y2 y3 tq s1 s2 s3
        (r4k-mi1-grow h (Succ (Succ q)) q ctr y3 cb c2 y1 Tb T2 p3 (r4k-mi1-grow h (Succ q) q ctr y2 c1 cb y1 T1 Tb p2 (r4k-lw-mi1 h q ctr y1 c c1 T T1 p1 w1 h1 rc) w2) w3)
        (r4k-mi1-grow h (Succ (Succ q)) (Succ q) ctr y3 cb c2 y2 Tb T2 p3 (r4k-lw-mi1 h (Succ q) ctr y2 c1 cb T1 Tb p2 w2 h2 r1) w3)
        (r4k-lw-mi1 h (Succ (Succ q)) ctr y3 cb c2 Tb T2 p3 w3 h3 r2)))
    ((Succ j1)
      (MiN T2 j1 p q y y1 y2 y3 tq s1 s2 s3
        (r4k-mi-grow h (Succ (Succ q)) j1 q ctr y3 cb c2 y1 Tb T2 p3 (r4k-mi-grow h (Succ q) j1 q ctr y2 c1 cb y1 T1 Tb p2 (r4k-lw-mi h j1 q ctr y1 c c1 T T1 p1 w1 h1 rc) w2) w3)
        (r4k-mi-grow h (Succ (Succ q)) j1 (Succ q) ctr y3 cb c2 y2 Tb T2 p3 (r4k-lw-mi h j1 (Succ q) ctr y2 c1 cb T1 Tb p2 w2 h2 r1) w3)
        (r4k-lw-mi h j1 (Succ (Succ q)) ctr y3 cb c2 Tb T2 p3 w3 h3 r2)))))

; The walk keeps celems listing distinct traces of the trie and of ctr.
(def-fns _ $ (erased r4k-lw-am : (erased (Nat) h p) (erased (Ctree) ctr y c c2) (erased (List (Nat)) T T2) (erased (List (Col)) pre) (subterm erased (LW h ctr y pre p c T c2 T2) w)
    (erased (AMc h c T) am) (erased (Distinct T) dt) (erased (AMc h ctr T) ar) -> (erased (AMc h c2 T2) am2) (erased (Distinct T2) dt2) (erased (AMc h ctr T2) ar2))
  (let-match erased w (LwN _ _ y1 y2 y3 _ _ q _ _ c1 cb _ _ T1 Tb _ w1 w2 w3)
    ((LwE _ _ _ _ _ _) (values am dt ar))
    ((LwL _ _ lf _ _ _ _ _ _ ri le a ad)
      (values (r4c-am-cad h p c c2 T T2 pre am ad ri le) (r4c-dist-cad h p c c2 T T2 pre dt am ad ri le)
        (match erased ad (((AMc h ctr T2) r)) ((CadHas _ _ _ _ _ _) ar) ((CadNew _ _ _ _ _ _ _) (AmCons h p ctr lf T pre ri le a ar))))))
  (let ((erased am1) (erased dt1) (erased ar1)) (r4k-lw-am h q ctr y1 c c1 T T1 (Cons _ (C1) pre) w1 am dt ar))
  (let ((erased am2) (erased dt2) (erased ar2)) (r4k-lw-am h (Succ q) ctr y2 c1 cb T1 Tb (Cons _ (C2) pre) w2 am1 dt1 ar1))
  (r4k-lw-am h (Succ (Succ q)) ctr y3 cb c2 Tb T2 (Cons _ (C3) pre) w3 am2 dt2 ar2))

(def-fns _ $ (erased r4k-ix-lt : (erased (Nat) h N x k j) (erased (List (Col)) pre) (erased (RIdx pre x) ri) (erased (Length (Col) pre k) le) (erased (Add k j (Succ h)) ad)
    (erased (Pw3 (Succ h) (Succ (Zero)) N) pw) -> (erased (Lt x N) r))
  (let ((erased W) (erased pk)) (pw3-c k (Succ (Zero))))
  (let ((erased Y) (erased pj)) (pw3-c j W))
  (let-match erased (pw3-fn (Succ (Zero)) Y N (Succ h) (pw3-cat j (Succ h) (Succ (Zero)) W Y k pk pj ad) pw) (Refl _ _))
  (lt-le-trans x W N (r4c-ridx-lt x k W pre ri le pk) (pw3-le j W Y pj)))

; The Kempe loop's state before a G round, as red4's arrays hold it: KR with gtr empty and CR; ctu in uc and ul; gu as gtu in the node words xs of len nodes laid
; out from s0, whose nonzero gtr parts are in the hits buffer Hs; the ctr trie cs and celems T holding ctr.
(def-adts $ (KgI : ((Nat) h N o len) ((Ctree) c0 r0) ((Gtree) g0 s0) ((List (Copy (Nat))) xs) ((List Cnt) vs) ((List (U8)) us cs) ((List (Nat)) Hs T) -> Type)
  enum
  (many MkKgI : (erased (Nat) h N o len) (erased (Ctree) c0 r0) (erased (Gtree) g0 s0) (erased (List (Copy (Nat))) xs) (erased (List Cnt) vs) (erased (List (U8)) us cs)
      (erased (List (Nat)) Hs T) (erased (Ctree) ctu ctr c) (erased (Gtree) gtu) (erased (Length (Copy (Nat)) xs len) lx) (erased (Lt len u62-modulus) lnb)
      (erased (AllCu xs) au) (erased (NLay xs h (Zero) s0) ly) (erased (Nat) ilo ihi) (erased (Bool) z) (erased (NIv xs h (Zero) s0 ilo ihi z) iv) (erased (NPart xs h (Zero) s0 (BFalse) gtu) pu) (erased (AllLt Hs len) al) (erased (Distinct Hs) dt)
      (erased (HAll xs (Zero) Hs) ha) (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr) (erased (CR h c0 r0 g0 ctr) cr) (erased (Tally vs (Succ h) (Zero) ctu) tb)
      (erased (Lc us h (Zero) ctu) lc) (erased (Sz cnt-w vs N) zv) (erased (Sz flag-w us o) zu) (erased (Sz flag-w cs o) zc) (erased (Ca cs h (Zero) c) f)
      (erased (SameSet c ctr) ss) (erased (MI T h (Zero) c) mi) (erased (AMc h c T) am) (erased (Distinct T) dc) -> (KgI h N o len c0 r0 g0 s0 xs vs us cs Hs T)))

; The Kempe loop's state after it, as the arrays and red4's killed flag kd hold it: KR, with Kld relating kd, the arrays and ctu, gtr and gtu.
(def-adts $ (KdI : ((Nat) h N o len) ((Ctree) c0 r0) ((Gtree) g0 s0) ((Bool) kd) ((List (Copy (Nat))) xs) ((List Cnt) vs) ((List (U8)) us cs) ((List (Nat)) Hs T) -> Type)
  enum
  (many MkKdI : (erased (Nat) h N o len) (erased (Ctree) c0 r0) (erased (Gtree) g0 s0) (erased (Bool) kd) (erased (List (Copy (Nat))) xs) (erased (List Cnt) vs)
      (erased (List (U8)) us cs) (erased (List (Nat)) Hs T) (erased (Ctree) ctu c) (erased (Gtree) gtr gtu) (erased (Length (Copy (Nat)) xs len) lx)
      (erased (Lt len u62-modulus) lnb) (erased (AllCu xs) au) (erased (NLay xs h (Zero) s0) ly) (erased (Nat) ilo ihi) (erased (Bool) z) (erased (NIv xs h (Zero) s0 ilo ihi z) iv) (erased (AllLt Hs len) al) (erased (Distinct Hs) dt)
      (erased (HAll xs (Zero) Hs) ha) (erased (KR h c0 r0 g0 ctu gtr gtu) kr) (erased (Kld kd h s0 vs us xs ctu gtr gtu) kl) (erased (Sz cnt-w vs N) zv)
      (erased (Sz flag-w us o) zu) (erased (Sz flag-w cs o) zc) (erased (Ca cs h (Zero) c) f) (erased (MI T h (Zero) c) mi) (erased (AMc h c T) am) (erased (Distinct T) dc)
      -> (KdI h N o len c0 r0 g0 s0 kd xs vs us cs Hs T)))

; What red4's if not (finished ()) then s_round () leaves: finished with the state as it was, finished and killed, or a state for the next ktc.
(def-adts $ (StepR : ((Nat) h N o len) ((Ctree) c0 r0) ((Gtree) g0 s0) ((Bool) kd) ((List (Copy (Nat))) xs) ((List Cnt) vs) ((List (U8)) us cs) ((List (Nat)) Hs T) -> Type)
  enum
  (many KsDone : (erased (Nat) h N o len) (erased (Ctree) c0 r0) (erased (Gtree) g0 s0) (erased (Bool) kd) (erased (List (Copy (Nat))) xs) (erased (List Cnt) vs)
      (erased (List (U8)) us cs) (erased (List (Nat)) Hs T) (erased (KdI h N o len c0 r0 g0 s0 kd xs vs us cs Hs T) k) -> (StepR h N o len c0 r0 g0 s0 kd xs vs us cs Hs T))
  (many KsKill : (erased (Nat) h N o len) (erased (Ctree) c0 r0) (erased (Gtree) g0 s0) (erased (Bool) kd) (erased (List (Copy (Nat))) xs) (erased (List Cnt) vs)
      (erased (List (U8)) us cs) (erased (List (Nat)) Hs T) (erased (KdI h N o len c0 r0 g0 s0 (BTrue) xs vs us cs Hs T) k) -> (StepR h N o len c0 r0 g0 s0 kd xs vs us cs Hs T))
  (many KsGo : (erased (Nat) h N o len) (erased (Ctree) c0 r0) (erased (Gtree) g0 s0) (erased (Bool) kd) (erased (List (Copy (Nat))) xs) (erased (List Cnt) vs)
      (erased (List (U8)) us cs) (erased (List (Nat)) Hs T) (erased (KgI h N o len c0 r0 g0 s0 xs vs us cs Hs T) g) -> (StepR h N o len c0 r0 g0 s0 kd xs vs us cs Hs T)))



; No node word has a part of gtr, so the hits buffer may start empty.
(def-fns _ $ (erased r4k-gz-hall : (erased (List (Copy (Nat))) xs) (erased (Nat) i) (subterm erased (GzA xs) g) -> (erased (HAll xs i (Nil (Nat))) r))
  (let-match erased g (GzCons w b cm fu xs1 d g1) ((GzNil) (HalNil i (Nil _))))
  (HalCons w i b cm (Zero) fu xs1 (Nil _) d (ZiZ i (Nil _)) (r4k-gz-hall xs1 (Succ i) g1)))

