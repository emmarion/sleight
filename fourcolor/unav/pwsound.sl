; Soundness of pwalk.sl's evidence: a dart with positive dscore whose face fits a part of the walk exactly has an
; obligation of the walk fitting exactly at some dart. Load after hubsound.sl.

(def-fns _ $ (erased map-hit-ext : (erased (Nat) d) (erased (List (Nat)) e f ks) (erased (List (List (Sub))) o o2) (erased (MapHit d e f ks o) h)
    (erased (Ext o o2) x) -> (erased (MapHit d e f ks o2) r))
  (let-match erased h (MkMapHit _ z _ _ _ q _ lz m ex))
  (MkMapHit d z e f ks q o2 lz (mem-ext q o o2 m x) ex))

(def-fns _ $ (erased exact-sub-at : (erased (List (Nat)) e f ks) (erased (Nat) y m) (erased (List (Sub)) p q) (erased (ExactAt e f ks y p) x)
    (erased (Pw (Sub) (Sub) SubSub p q) s) (erased (Length (Sub) p m) lp) (erased (Length (Sub) q m) lq) -> (erased (ExactAt e f ks y q) r))
  (let-match erased x (MkExactAt _ _ _ _ a os _ pa ob ex))
  (let-match erased ex (MkExact _ _ m2 fo lo lp2))
  (let-match erased (length-fn _ p m2 m lp2 lp) (Refl _ _))
  (MkExactAt e f ks y a os q pa ob (MkExact os q m2 (fit-sub os p q fo s) lo lq)))

(def-fns _ $ (erased absurd exact-dis-at : (erased (List (Nat)) e f ks) (erased (Nat) y) (erased (List (Sub)) p q) (erased (ExactAt e f ks y p) x)
    (erased (ExactAt e f ks y q) x2) (erased (Ex (Sub) (Sub) SubDis p q) dj) -> (erased (False) r))
  (let-match erased x (MkExactAt _ _ _ _ a os _ pa ob ex))
  (let-match erased x2 (MkExactAt _ _ _ _ a2 os2 _ pa2 ob2 ex2))
  (let-match erased (nth-fn _ ks y a a2 pa pa2) (Refl _ _))
  (let-match erased (obs-fn e f ks y a os os2 ob ob2) (Refl _ _))
  (let-match erased ex (MkExact _ _ _ fo _ _))
  (let-match erased ex2 (MkExact _ _ _ fo2 _ _))
  (fit-bad os q fo2 (fit-dis os p q fo dj)))

(def-fns _ $ (erased exact-len : (erased (List (Nat)) e f ks) (erased (Nat) y) (erased (List (Sub)) p) (erased (ExactAt e f ks y p) x)
    -> (erased (Nat) a) (erased (Nth (Nat) ks y a) pa) (erased (Length (Sub) p a) l))
  (let-match erased x (MkExactAt _ _ _ _ a os _ pa ob ex))
  (let-match erased ex (MkExact _ _ m fo lo lp))
  (let-match erased (length-fn _ os a m (obs-len e f ks y a os ob) lo) (Refl _ _))
  (values a pa lp))

(def-fns _ $ (erased fsum-snoc : (erased (Nat) d) (erased (List (Nat)) f fi g) (erased (HPerm d f fi) pf) (erased (Nat) x k s z c) (erased (Lt x d) lx)
    (subterm erased (FSum f g x k s) p) (erased (Iter f k x z) it) (erased (Nth (Nat) g z c) pc) -> (erased (Nat) s2) (erased (FSum f g x (Succ k) s2) r)
    (erased (Add s c s2) a))
  (let-match erased p (FSS _ _ _ y k1 c0 s1 _ pc0 py p1 a0)
    ((FSZ _ _ _)
      (let-match erased it (ItZ _ _))
      (let ((erased y) (erased py) (erased _)) (perm-nth d x f fi pf lx))
      (values c (FSS f g x y (Zero) c (Zero) c pc py (FSZ f g y) (add-zero-right c)) (AddZero c))))
  (let-match erased it (ItS _ _ _ y2 _ py2 it1))
  (let-match erased (nth-fn _ f x y y2 py py2) (Refl _ _))
  (let ((erased y3) (erased py3) (erased ly3)) (perm-nth d x f fi pf lx))
  (let-match erased (nth-fn _ f x y y3 py py3) (Refl _ _))
  (let ((erased s3) (erased r1) (erased a1)) (fsum-snoc d f fi g pf y k1 s1 z c ly3 p1 it1 pc))
  (let ((erased s2) (erased a2)) (add c0 s3))
  (let ((erased ab) (erased b1) (erased b2)) (plus-assoc-r c0 s1 c s3 s2 a2 a1))
  (let-match erased (add-fn c0 s1 ab s b1 a0) (Refl _ _))
  (values s2 (FSS f g x y (Succ k1) c0 s3 s2 pc0 py r1 a2) b2))

(def-fns _ $ (erased fsum-rot : (erased (Nat) d) (erased (List (Nat)) f fi g) (erased (HPerm d f fi) pf) (erased (Nat) x x1 a s) (erased (Lt x1 d) lx1)
    (erased (FSum f g x a s) p) (erased (Iter f a x x) cy) (erased (Nth (Nat) f x x1) px) -> (erased (FSum f g x1 a s) r))
  (let-match erased p (FSS _ _ _ y a1 c s1 _ pc py p1 ad) ((FSZ _ _ _) (FSZ f g x1)))
  (let-match erased (nth-fn _ f x y x1 py px) (Refl _ _))
  (let-match erased cy (ItS _ _ _ y2 _ py2 it1))
  (let-match erased (nth-fn _ f x y y2 py py2) (Refl _ _))
  (let ((erased s2) (erased r) (erased a2)) (fsum-snoc d f fi g pf y a1 s1 x c lx1 p1 it1 pc))
  (let-match erased (add-fn c s1 s2 s (add-comm s1 c s2 a2) ad) (Refl _ _))
  r)

; dscore_cface: the dscore is the same along a face.
(def-fns _ $ (erased dscore-step : (erased (Nat) d x x1 pos neg) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs) (erased (Geo d e n f ks) g)
    (erased (Lt x d) lx) (erased (DScore d e n f ks drs x pos neg) ds) (erased (Nth (Nat) f x x1) px)
    -> (erased (Lt x1 d) lx1) (erased (DScore d e n f ks drs x1 pos neg) r))
  (let-match erased ds (MkDScore _ _ a t c60 sp sn _ _ _ _ _ _ ids cs cse _ io dl rc pa fp fn m60 mt ap an))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ ol _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased y1) (erased py1) (erased ly1) (erased pa1)) (face-step d x a e n f ks h ol lx pa))
  (let-match erased (nth-fn _ f x y1 x1 py1 px) (Refl _ _))
  (let ((erased cy)) (face-cycle d x a f ks ol lx pa))
  (values ly1 (MkDScore d x1 a t c60 sp sn pos neg e n f ks ids cs cse drs io dl rc pa1
    (fsum-rot d f fi cse pf x x1 a sp ly1 fp cy px) (fsum-rot d f fi cs pf x x1 a sn ly1 fn cy px) m60 mt ap an)))

(def-fns _ $ (erased dscore-iter : (erased (Nat) d x z k pos neg) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs) (erased (Geo d e n f ks) g)
    (erased (Lt x d) lx) (erased (DScore d e n f ks drs x pos neg) ds) (subterm erased (Iter f k x z) it) -> (erased (DScore d e n f ks drs z pos neg) r))
  (let-match erased it (ItS _ k1 _ y _ py it1) ((ItZ _ _) ds))
  (let ((erased ly) (erased ds1)) (dscore-step d x y pos neg e n f ks drs g lx ds py))
  (dscore-iter d y z k1 pos neg e n f ks drs g ly ds1 it1))

; What the walk's evidence gives a dart y of positive dscore fitting its part exactly: an obligation fitting exactly at
; some dart, or, from a PRed, a dart of positive dscore fitting the obligation exactly, or, from a PCut, one fitting a part
; of the cut list exactly.
(def-adts $ (PresHit : ((Nat) d) ((List (Nat)) e n f ks) ((List (List (Sub))) drs ct out) -> Type)
  enum
  (many PHMap : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs ct out) (erased (MapHit d e f ks out) h)
      -> (PresHit d e n f ks drs ct out))
  (many PHPos : (erased (Nat) d z pos neg) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs ct out) (erased (List (Sub)) q) (erased (Lt z d) lz)
      (erased (DScore d e n f ks drs z pos neg) ds) (erased (Lt neg pos) lt) (erased (ExactAt e f ks z q) x) (erased (Mem (List (Sub)) q out) m)
      -> (PresHit d e n f ks drs ct out))
  (many PHCut : (erased (Nat) d z pos neg) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs ct out) (erased (List (Sub)) q) (erased (Lt z d) lz)
      (erased (DScore d e n f ks drs z pos neg) ds) (erased (Lt neg pos) lt) (erased (ExactAt e f ks z q) x) (erased (Mem (List (Sub)) q ct) m)
      -> (PresHit d e n f ks drs ct out)))

(def-fns _ $ (erased preshit-ext : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs ct o o2) (erased (PresHit d e n f ks drs ct o) h)
    (erased (Ext o o2) x) -> (erased (PresHit d e n f ks drs ct o2) r))
  (match erased h _
    ((PHMap _ _ _ _ _ _ _ _ mh) (PHMap d e n f ks drs ct o2 (map-hit-ext d e f ks o o2 mh x)))
    ((PHPos _ z pos neg _ _ _ _ _ _ _ q lz ds lt ex m) (PHPos d z pos neg e n f ks drs ct o2 q lz ds lt ex (mem-ext q o o2 m x)))
    ((PHCut _ z pos neg _ _ _ _ _ _ _ q lz ds lt ex m) (PHCut d z pos neg e n f ks drs ct o2 q lz ds lt ex m))))

(def-fns _ $ (erased preshit-map : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs o) (erased (PresHit d e n f ks drs (Nil (List (Sub))) o) h)
    -> (erased (MapHit d e f ks o) r))
  (match erased h _
    ((PHMap _ _ _ _ _ _ _ _ mh) mh)
    ((PHPos _ z pos neg _ _ _ _ _ _ _ q lz ds lt ex m) (MkMapHit d z e f ks q o lz m ex))
    (absurd (PHCut _ z pos neg _ _ _ _ _ _ _ q lz ds lt ex m) m)))

(def-fns _
  ((erased pres-sound : (erased (Nat) d nhub) (erased (List (Nat)) e n f ks ws) (erased (List (List (Sub))) drs rt rs ct) (erased (Geo d e n f ks) g)
      (erased (OfSize nhub drs rs) sz) (erased (Iota d ws) iw) (erased (TgtAll e n f ks drs rt nhub ws) ta) (erased (Nat) y pos neg)
      (erased (List (List (Sub))) out) (erased (List (Sub)) p) (erased (Lt y d) ly) (erased (DScore d e n f ks drs y pos neg) ds) (erased (Lt neg pos) lt)
      (erased (ExactAt e f ks y p) x) (subterm erased (Pres nhub rt rs ct p out) dp) -> (erased (PresHit d e n f ks drs ct out) r))
    (match erased dp _
      ((PRed _ _ _ _ _ _ m) (PHPos d y pos neg e n f ks drs ct out p ly ds lt x m))
      ((PCut _ _ _ _ _ _ c)
        (let-match erased c (MkCutAt _ h _ m mh sb lp lh))
        (PHCut d y pos neg e n f ks drs ct out h ly ds lt (exact-sub-at e f ks y m p h x sb lp lh) mh))
      ((PHub _ _ _ _ acc o _ _ hc l cv ix w e1)
        (PHMap d e n f ks drs ct out (map-hit-ext d e f ks o out (hub-sound d y nhub pos neg e n f ks ws drs rt rs acc o p hc g ly ds lt x l sz iw ta cv ix w) e1)))
      ((PSplit _ k _ _ _ o1 o2 _ _ ql qh pl pr w s dl dr e1 e2)
        (match erased (exact-split-at d y k e n f ks p ql qh g x w) _
          ((OrL _ _ xl)
            (match erased s _
              ((SelL _ _) (preshit-ext d e n f ks drs ct o1 out (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg o1 ql ly ds lt xl dl) e1))
              ((SelR _ _) (preshit-ext d e n f ks drs ct o2 out (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg o2 ql ly ds lt xl dr) e2))))
          ((OrR _ _ xh)
            (match erased s _
              ((SelL _ _) (preshit-ext d e n f ks drs ct o2 out (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg o2 qh ly ds lt xh dr) e2))
              ((SelR _ _) (preshit-ext d e n f ks drs ct o1 out (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg o1 qh ly ds lt xh dl) e1))))))
      ((PSim _ k m _ _ _ o1 o2 _ _ p2 pe0 pe ro lk lp le sb fe de e1 e2)
        (let ((erased a) (erased pa) (erased la)) (exact-len e f ks y p x))
        (let-match erased (length-fn _ p a m la lp) (Refl _ _))
        (let ((erased z) (erased it) (erased lz) (erased x2)) (exact-rot-at d y a k e n f ks p p2 g ly pa lk x ro))
        (let ((erased a2) (erased pa2) (erased la2)) (exact-len e f ks z p2 x2))
        (let-match erased g (MkGeo _ _ _ _ _ h _ _ ol _))
        (let ((erased z3) (erased it3) (erased _) (erased pa3)) (face-walk d y a e n f ks h ol k ly pa))
        (let-match erased (iter-fn f k y z3 z it3 it) (Refl _ _))
        (let-match erased (nth-fn _ ks z a2 a pa2 pa3) (Refl _ _))
        (let ((erased x3)) (exact-sub-at e f ks z a p2 pe0 x2 sb la2 le))
        (let ((erased ds2)) (dscore-iter d y z k pos neg e n f ks drs g ly ds it))
        (match erased (forced-sound d nhub e n f ks ws drs rt rs ct g sz iw ta z pos neg o1 pe0 pe lz ds2 lt x3 fe) _
          ((OrL _ _ hh) (preshit-ext d e n f ks drs ct o1 out hh e1))
          ((OrR _ _ x4) (preshit-ext d e n f ks drs ct o2 out (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta z pos neg o2 pe lz ds2 lt x4 de) e2))))))
  ((erased forced-sound : (erased (Nat) d nhub) (erased (List (Nat)) e n f ks ws) (erased (List (List (Sub))) drs rt rs ct) (erased (Geo d e n f ks) g)
      (erased (OfSize nhub drs rs) sz) (erased (Iota d ws) iw) (erased (TgtAll e n f ks drs rt nhub ws) ta) (erased (Nat) y pos neg)
      (erased (List (List (Sub))) o) (erased (List (Sub)) p0 p) (erased (Lt y d) ly) (erased (DScore d e n f ks drs y pos neg) ds) (erased (Lt neg pos) lt)
      (erased (ExactAt e f ks y p0) x) (subterm erased (Forced nhub rt rs ct p0 p o) fd) -> (erased (Or (PresHit d e n f ks drs ct o) (ExactAt e f ks y p)) r))
    (match erased fd _
      ((FRoot _ _ _ _ _ _) (OrR _ _ x))
      ((FLeft _ k m _ _ _ _ q0 q ql qh _ other _ f1 w s sb dj lc l0)
        (let ((erased x0)) (exact-sub-at e f ks y m p0 q0 x sb lc l0))
        (let-match erased (forced-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg o q0 q ly ds lt x0 f1) (OrR _ _ xq)
          ((OrL _ _ hh) (OrL _ _ hh)))
        (match erased (exact-split-at d y k e n f ks q ql qh g xq w) _
          ((OrL _ _ xl) (match erased s _ ((SelL _ _) (OrR _ _ xl)) (absurd (SelR _ _) (exact-dis-at e f ks y p0 ql x xl dj))))
          ((OrR _ _ xh) (match erased s _ (absurd (SelL _ _) (exact-dis-at e f ks y p0 qh x xh dj)) ((SelR _ _) (OrR _ _ xh))))))
      ((FRight _ k _ _ _ _ ol q0 q ql qh pl _ f1 w s dl e1)
        (let-match erased (forced-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg o p0 q ly ds lt x f1) (OrR _ _ xq)
          ((OrL _ _ hh) (OrL _ _ hh)))
        (match erased (exact-split-at d y k e n f ks q ql qh g xq w) _
          ((OrL _ _ xl)
            (match erased s _
              ((SelL _ _) (OrL _ _ (preshit-ext d e n f ks drs ct ol o (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg ol ql ly ds lt xl dl) e1)))
              ((SelR _ _) (OrR _ _ xl))))
          ((OrR _ _ xh)
            (match erased s _
              ((SelL _ _) (OrR _ _ xh))
              ((SelR _ _) (OrL _ _ (preshit-ext d e n f ks drs ct ol o (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw ta y pos neg ol qh ly ds lt xh dl) e1))))))))))
