(let ((many p3) (erased dl3)) (defs l3))
(let ((erased ex3)) (defl-ext l3 p3 dl3))

(sk-family Sk3 MkSk3 sk3-of ()
  (c-hole (2 DR "0" TV "10" TV) (1 DR "01" TV "0" TV))
  (c-sw0 (1 DR "" TV "111" TV) (1 DR "011" TV "" TV))
  (c-sw1 (1 DR "" TV "0111" TV) (1 DR "0111" TV "" TV))
  (c-turn (1 DR "0111" TV "00" TV) (2 DL "1" TV "00111" TV))
  (c-desc (2 DR "1" TV "10" TV) (2 DL "1" TV "00" TV))
  (c-merge (1 DR "0110" TV "00" TV) (1 DR "01" TV "0111" TV))
  (c-gadget (2 DR "00" TV "1000111" TV) (1 DR "00111" TV "0111" TV))
  (c-turn1 (1 DR "0111" TV "100" TV) (2 DL "1" TV "001111" TV))
  (c-merge1 (1 DR "0110" TV "100" TV) (1 DR "01" TV "01111" TV))
  (c-end11 (1 DR "" TV "110000" TV) (2 DL "1" TV "00011" TV))
  (c-end011 (1 DR "" TV "0110000" TV) (2 DL "1" TV "000011" TV)))
(comptime-match many (sk3-of p3) (ROk _ sg3))

(let ((erased n2)) (Succ (Succ (Zero))))
(let ((erased n3)) (Succ n2))

(def-adts
  ((Xb : ((List (Tk)) X) ((List (Bool)) r x) -> Type)
    enum
    (many XbN : (erased (List (Bool)) r) -> (Xb (Nil (Tk)) r r))
    (many XbP : (erased (List (Tk)) X) (erased (List (Bool)) r x) (erased (Xb X r x) p) -> (Xb (Cons (Tk) (Tp) X) r (bits "0" x)))
    (many XbZ : (erased (List (Tk)) X) (erased (List (Bool)) r x) (erased (Xb X r x) p) -> (Xb (Cons (Tk) (T0) X) r (bits "111" x)))
    (many XbO : (erased (List (Tk)) X) (erased (List (Bool)) r x) (erased (Xb X r x) p) -> (Xb (Cons (Tk) (T1) X) r (bits "0111" x)))))

(def-adts
  ((Tb : ((Tt) T) ((List (Bool)) r x) -> Type)
    enum
    (many TbE : (erased (List (Bool)) r) -> (Tb (TtE) r r))
    (many Tb1 : (erased (List (Bool)) r) -> (Tb (Tt1) r (bits "1" r)))
    (many Tb11 : (erased (List (Bool)) r) -> (Tb (Tt11) r (bits "11" r)))
    (many Tb011 : (erased (List (Bool)) r) -> (Tb (Tt011) r (bits "011" r)))
    (many Tb0011 : (erased (List (Bool)) r) -> (Tb (Tt0011) r (bits "0011" r)))))

(def-adts
  ((Ls : ((List (Bool)) l) ((List (Nat)) K) ((List (Bool)) x) -> Type)
    enum
    (many LsN : (erased (List (Bool)) l) -> (Ls l (Nil (Nat)) l))
    (many LsC : (erased (List (Bool)) l y z) (erased (Nat) t) (erased (List (Nat)) K) (erased (Ls l K y) p) (erased (Rp (BTrue) t y z) q)
       -> (Ls l (Cons (Nat) t K) (bits "0" z)))))

(def-adts
  ((Po : ((List (Tk)) W) -> Type)
    enum
    (many PoP : (erased (List (Tk)) W) -> (Po (Cons (Tk) (Tp) W)))
    (many Po1 : (erased (List (Tk)) W) -> (Po (Cons (Tk) (T1) W)))))

(def-adts
  ((Cf : ((Bool) h) ((List (Bool)) l) ((List (Nat)) K) ((List (Tk)) W) ((List (Bool)) r) ((Tc) e) -> Type)
    enum
    (many CfB : (erased (List (Bool)) l r x y) (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (Ls l K x) ls) (erased (Xb W r y) xb)
       -> (Cf (BFalse) l K W r (MkTc 1 (DR) x y)))
    (many CfH : (erased (List (Bool)) l r x y) (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (Ls l K x) ls) (erased (Xb W r y) xb)
       -> (Cf (BTrue) l K W r (MkTc 2 (DR) x (bits "10" y))))))

(def-adts
  ((So : ((List (Bool)) l r) ((SRes) s) ((Tc) e) -> Type)
    enum
    (many SoT : (erased (List (Bool)) l r) (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (Tc) e) (erased (Cf (BTrue) l K W r e) cf) (erased (Po W) po)
       -> (So l r (STurn K W) e))
    (many SoE : (erased (List (Bool)) l r) (erased (List (Nat)) K) (erased (Tc) e) (erased (Cf (BFalse) l K (Nil (Tk)) r e) cf)
       -> (So l r (SEnd K) e))))

(def-adts
  ((Go : ((Tc) e e2) -> Type)
    enum
    (many MkGo : (erased (Tc) e e2) (erased (Bool) g) (erased (Reach p3 e e2 g) r) -> (Go e e2))))

(def-fns _ $ (erased go-cat : (erased (Tc) e1 e2 e3) (erased (Go e1 e2) a) (erased (Go e2 e3) b) -> (erased (Go e1 e3) c))
  (let-match erased a (MkGo _ _ g1 r1))
  (let-match erased b (MkGo _ _ g2 r2))
  (let ((erased g) (erased o) (erased r)) (reach-cat p3 e1 e2 e3 g1 g2 r1 r2))
  (MkGo e1 e3 g r))

(def-fns _ $ (erased go-refl : (erased (Tc) e) -> (erased (Go e e) c))
  (MkGo e e (BFalse) (reach-refl p3 e)))

(def-fns _ $ (erased go : (erased (Tc) e e2) (erased (Reach p3 e e2 (BTrue)) r) -> (erased (Go e e2) c))
  (MkGo e e2 (BTrue) r))

(def-fns _ $ (erased asc-r : (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) -> (erased (AsC (MkTc q (DR) l (Cons (Bool) h r)) (MkConf q l h r)) a))
  (MkAsC q (DR) l (Cons (Bool) h r) (Cons (Bool) h r) l r l r h (OrR _ l (Cons (Bool) h r)) (PullCons h r) (OrR _ l r)))

(def-fns _ $ (erased go-dl : (erased (Tc) e) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h)
    (erased (Reach p3 e (MkTc q (DL) (Cons (Bool) h l) r) (BTrue)) rc) -> (erased (Go e (MkTc q (DR) l (Cons (Bool) h r))) c))
  (let-match erased rc (MkRc _ _ _ _ c c2 a a2 xr))
  (let-match erased (as-fn _ c2 _ a2 (MkAsC q (DL) (Cons (Bool) h l) r (Cons (Bool) h l) r l l r h (OrL _ (Cons (Bool) h l) r) (PullCons h l) (OrL _ l r)))
    (Refl _ _))
  (MkGo e _ (BTrue) (MkRc p3 e _ (BTrue) c c2 a (asc-r q l r h) xr)))

(def-fns _ $ (erased rp2 : (erased (Bool) b) (erased (List (Bool)) t) -> (erased (Rp b n2 t (Cons (Bool) b (Cons (Bool) b t))) p))
  (RpS b _ t _ (RpS b (Zero) t t (RpZ b t))))

(def-fns _ $ (erased rp3 : (erased (Bool) b) (erased (List (Bool)) t) -> (erased (Rp b n3 t (Cons (Bool) b (Cons (Bool) b (Cons (Bool) b t)))) p))
  (RpS b n2 t _ (rp2 b t)))

(def-fns _ $ (erased rp-snoc : (erased (Bool) b) (erased (Nat) n) (erased (List (Bool)) t x) (subterm erased (Rp b n (Cons (Bool) b t) x) p)
    -> (erased (Rp b (Succ n) t x) q))
  (match erased p _
    ((RpZ _ _) (RpS b (Zero) t t (RpZ b t)))
    ((RpS _ n1 _ x1 p1) (RpS b (Succ n1) t x1 (rp-snoc b n1 t x1 p1)))))

(def-fns _ $ (erased ls-2 : (erased (List (Bool)) l x) (erased (List (Nat)) K) (erased (Ls l K x) ls) -> (erased (Ls l (Cons (Nat) n2 K) (bits "011" x)) r))
  (LsC l x _ n2 K ls (rp2 _ x)))

(def-fns _ $ (erased ls-3 : (erased (List (Bool)) l x) (erased (List (Nat)) K) (erased (Ls l K x) ls) -> (erased (Ls l (Cons (Nat) n3 K) (bits "0111" x)) r))
  (LsC l x _ n3 K ls (rp3 _ x)))

(def-fns _ $ (erased ls-inc : (erased (List (Bool)) l z) (erased (Nat) t) (erased (List (Nat)) K) (erased (Ls l (Cons (Nat) t K) (bits "0" z)) ls)
    -> (erased (Ls l (Cons (Nat) (Succ t) K) (bits "01" z)) r))
  (let-match erased ls (LsC _ y _ _ _ ls1 p))
  (LsC l y (bits "1" z) (Succ t) K ls1 (RpS (BTrue) t y z p)))

(def-fns _ $ (erased desc : (erased (Nat) m) (erased (List (Bool)) x z w) (subterm erased (Rp (BTrue) m x z) p) ->
    (erased (List (Bool)) y) (erased (Rp (BFalse) m w y) q) (erased (Go (MkTc 2 (DR) z (bits "10" w)) (MkTc 2 (DR) x (bits "10" y))) c))
  (let-match erased p (RpS _ m1 _ z1 p1) ((RpZ _ _) (values w (RpZ _ w) (go-refl _))))
  (let ((erased y) (erased q) (erased c)) (desc m1 x z1 (bits "0" w) p1))
  (values y (rp-snoc _ m1 w y q) (go-cat _ _ _ (go-dl _ _ _ _ _ (c-desc p3 sg3 z1 w)) c)))

(def-fns _ $ (erased cends : (erased (Tt) T) (erased (Plain T) pl) (erased (List (Bool)) v a b z1 z2) (erased (Tb T (bits "00" v) a) ta) (erased (Tb T v b) tb) ->
    (erased (Go (MkTc 1 (DR) (bits "0111" z1) a) (MkTc 2 (DR) z1 (bits "100111" b))) ct)
    (erased (Go (MkTc 1 (DR) (bits "0110" z2) a) (MkTc 1 (DR) (bits "01" z2) (bits "0111" b))) cm))
  (match erased pl _
    ((PlE) (let-match erased ta (TbE _)) (let-match erased tb (TbE _))
      (values (go-dl _ _ _ _ _ (c-turn p3 sg3 z1 v)) (go _ _ (c-merge p3 sg3 z2 v))))
    ((Pl1) (let-match erased ta (Tb1 _)) (let-match erased tb (Tb1 _))
      (values (go-dl _ _ _ _ _ (c-turn1 p3 sg3 z1 v)) (go _ _ (c-merge1 p3 sg3 z2 v))))))

(def-fns _ $ (erased tpr-xb : (erased (Nat) m) (erased (List (Tk)) X W) (erased (List (Bool)) r u y) (subterm erased (TpR m X W) tp)
    (erased (Xb X r u) xb) (erased (Rp (BFalse) m u y) rp) -> (erased (Xb W r y) q))
  (match erased tp _
    ((TpZ _) (let-match erased rp (RpZ _ _)) xb)
    ((TpS m1 _ W1 tp1) (let-match erased rp (RpS _ _ _ y1 rp1)) (XbP W1 r y1 (tpr-xb m1 X W1 r u y1 tp1 xb rp1)))))

(def-fns _ $ (erased po-tpr : (erased (Nat) m) (erased (List (Tk)) X W) (erased (TpR m (Cons (Tk) (T1) X) W) tp) -> (erased (Po W) po))
  (match erased tp _
    ((TpZ _) (Po1 X))
    ((TpS m1 _ W1 _) (PoP W1))))

(def-fns _ $ (erased tturn : (erased (Tt) T) (erased (Plain T) pl) (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) X W)
    (erased (List (Bool)) l x v a b r) (erased (Ls l (Cons (Nat) (Succ (Succ (Succ m))) K) x) ls)
    (erased (Tb T (bits "00" v) a) ta) (erased (Tb T v b) tb) (erased (Xb X r b) xb) (erased (TpR m (Cons (Tk) (T1) X) W) tp) ->
    (erased (Tc) e2) (erased (Cf (BTrue) l K W r e2) cf) (erased (Po W) po) (erased (Go (MkTc 1 (DR) x a) e2) c))
  (let-match erased ls (LsC _ x1 _ _ _ ls1 q))
  (let-match erased q (RpS _ _ _ _ q1))
  (let-match erased q1 (RpS _ _ _ _ q2))
  (let-match erased q2 (RpS _ _ _ z q3))
  (let ((erased y) (erased rp) (erased c)) (desc m x1 z (bits "0111" b) q3))
  (let ((erased ct) (erased _)) (cends T pl v a b z z ta tb))
  (values (MkTc 2 (DR) x1 (bits "10" y)) (CfH l r x1 y K W ls1 (tpr-xb m _ W r _ y tp (XbO X r b xb) rp)) (po-tpr m X W tp) (go-cat _ _ _ ct c)))

(def-fns _ $ (erased merge : (erased (Tt) T) (erased (Plain T) pl) (erased (Nat) s) (erased (List (Nat)) K)
    (erased (List (Bool)) l x v a b) (erased (Ls l (Cons (Nat) n2 (Cons (Nat) s K)) x) ls)
    (erased (Tb T (bits "00" v) a) ta) (erased (Tb T v b) tb) ->
    (erased (List (Bool)) x2) (erased (Ls l (Cons (Nat) n3 (Cons (Nat) (Succ s) K)) x2) ls2) (erased (Go (MkTc 1 (DR) x a) (MkTc 1 (DR) x2 b)) c))
  (let-match erased ls (LsC _ x1 _ _ _ ls1 q))
  (let-match erased q (RpS _ _ _ _ q1))
  (let-match erased q1 (RpS _ _ _ _ q2))
  (let-match erased q2 (RpZ _ _))
  (let-match erased ls1 (LsC _ _ z _ _ _ _))
  (let ((erased _) (erased cm)) (cends T pl v a b z z ta tb))
  (values (bits "0111" (bits "01" z)) (ls-3 _ _ _ (ls-inc l z s K ls1)) (go-cat _ _ _ cm (go _ _ (c-sw1 p3 sg3 (bits "01" z) b)))))

(def-fns _ $ (erased tl0-xb : (erased (List (Tk)) W W1) (erased (List (Bool)) r y) (erased (Tl0 W W1) tl) (erased (Xb W r y) xb) (erased (Po W) po) ->
    (erased (List (Bool)) v) (erased (Xb W1 r v) xv) (erased (Eq (List (Bool)) y (bits "0" v)) e))
  (match erased tl _
    (absurd (Tl0N) po)
    ((Tl0P R) (let-match erased xb (XbP _ _ v xv)) (values v xv (Refl _ y)))
    ((Tl01 R) (let-match erased xb (XbO _ _ v0 xv)) (values (bits "111" v0) (XbZ R r v0 xv) (Refl _ y)))))

(def-fns _ $ (erased pre : (erased (List (Bool)) l r) (erased (List (Nat)) K) (erased (List (Tk)) W W1) (erased (Tc) e)
    (erased (Cf (BFalse) l K (Cons (Tk) (Tp) W) r e) cf) (erased (Tl0 W W1) tl) (erased (Po W) po) ->
    (erased (List (Bool)) x v) (erased (Ls l K x) ls) (erased (Xb W1 r v) xv) (erased (Eq (Tc) e (MkTc 1 (DR) x (bits "00" v))) eq))
  (let-match erased cf (CfB _ _ x y _ _ ls xb))
  (let-match erased xb (XbP _ _ y1 xb1))
  (let ((erased v) (erased xv) (erased ev)) (tl0-xb W W1 r y1 tl xb1 po))
  (let-match erased ev (Refl _ _))
  (values x v ls xv (Refl _ e)))

(def-fns _ $ (erased st-turn : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) W W1 W2) (erased (List (Bool)) l r) (erased (Tc) e)
    (erased (Cf (BFalse) l (Cons (Nat) (Succ (Succ (Succ m))) K) (Cons (Tk) (Tp) W) r e) cf) (erased (Tl0 W W1) tl) (erased (Po W) po)
    (erased (TpR m (Cons (Tk) (T1) W1) W2) tp) ->
    (erased (Tc) e2) (erased (Cf (BTrue) l K W2 r e2) cf2) (erased (Po W2) po2) (erased (Go e e2) c))
  (let ((erased x) (erased v) (erased ls) (erased xv) (erased eq)) (pre l r _ W W1 e cf tl po))
  (let-match erased eq (Refl _ _))
  (tturn (TtE) (PlE) m K W1 W2 l x v _ v r ls (TbE _) (TbE v) xv tp))

(def-fns _ $ (erased st-merge : (erased (Nat) s) (erased (List (Nat)) K) (erased (List (Tk)) W W1) (erased (List (Bool)) l r) (erased (Tc) e)
    (erased (Cf (BFalse) l (Cons (Nat) n2 (Cons (Nat) s K)) (Cons (Tk) (Tp) W) r e) cf) (erased (Tl0 W W1) tl) (erased (Po W) po) ->
    (erased (Tc) e2) (erased (Cf (BFalse) l (Cons (Nat) n3 (Cons (Nat) (Succ s) K)) W1 r e2) cf2) (erased (Go e e2) c))
  (let ((erased x) (erased v) (erased ls) (erased xv) (erased eq)) (pre l r _ W W1 e cf tl po))
  (let-match erased eq (Refl _ _))
  (let ((erased x2) (erased ls2) (erased c)) (merge (TtE) (PlE) s K l x v _ v ls (TbE _) (TbE v)))
  (values (MkTc 1 (DR) x2 v) (CfB l r x2 v _ W1 ls2 xv) c))

(def-fns _ $ (erased hole : (erased (Nat) t) (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (List (Bool)) l r) (erased (Tc) e)
    (erased (Cf (BTrue) l (Cons (Nat) t K) W r e) cf) ->
    (erased (Tc) e2) (erased (Cf (BFalse) l (Cons (Nat) (Succ t) K) (Cons (Tk) (Tp) W) r e2) cf2) (erased (Go e e2) c))
  (let-match erased cf (CfH _ _ x y _ _ ls xb))
  (let-match erased ls (LsC _ _ z _ _ _ _))
  (values (MkTc 1 (DR) (bits "01" z) (bits "0" y)) (CfB l r _ _ _ _ (ls-inc l z t K ls) (XbP W r y xb)) (go _ _ (c-hole p3 sg3 z y))))

(def-adts
  ((Pk : ((Tk) k) ((Nat) t) -> Type)
    enum
    (many PkZ : -> (Pk (T0) n2))
    (many PkO : -> (Pk (T1) n3))))

(def-fns _ $ (erased sw-push : (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (List (Bool)) l r) (erased (Tc) e) (erased (Tk) k) (erased (Nat) t)
    (erased (Pk k t) sh) (erased (Cf (BFalse) l K (Cons (Tk) k W) r e) cf) ->
    (erased (Tc) e2) (erased (Cf (BFalse) l (Cons (Nat) t K) W r e2) cf2) (erased (Go e e2) c))
  (let-match erased cf (CfB _ _ x y _ _ ls xb))
  (match erased sh _
    ((PkO) (let-match erased xb (XbO _ _ y1 xb1))
      (values (MkTc 1 (DR) (bits "0111" x) y1) (CfB l r _ _ _ W (ls-3 l x K ls) xb1) (go _ _ (c-sw1 p3 sg3 x y1))))
    ((PkZ) (let-match erased xb (XbZ _ _ y1 xb1))
      (values (MkTc 1 (DR) (bits "011" x) y1) (CfB l r _ _ _ W (ls-2 l x K ls) xb1) (go _ _ (c-sw0 p3 sg3 x y1))))))

(def-fns _ $ (erased sw-ok : (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (SRes) s) (subterm erased (Sw K W s) sw)
    (erased (List (Bool)) l r) (erased (Tc) e) (erased (Cf (BFalse) l K W r e) cf) ->
    (erased (Tc) e2) (erased (So l r s e2) so) (erased (Go e e2) c))
  (match erased sw _
    ((SwEnd _) (values e (SoE l r K e cf) (go-refl e)))
    ((SwT0 _ R _ sw1)
      (let ((erased e1) (erased cf1) (erased c1)) (sw-push K R l r e _ _ (PkZ) cf))
      (let ((erased e2) (erased so) (erased c2)) (sw-ok _ R s sw1 l r e1 cf1))
      (values e2 so (go-cat _ _ _ c1 c2)))
    ((SwT1 _ R _ sw1)
      (let ((erased e1) (erased cf1) (erased c1)) (sw-push K R l r e _ _ (PkO) cf))
      (let ((erased e2) (erased so) (erased c2)) (sw-ok _ R s sw1 l r e1 cf1))
      (values e2 so (go-cat _ _ _ c1 c2)))
    ((SwP0 _ R _ sw1)
      (let-match erased cf (CfB _ _ x y _ _ ls xb))
      (let-match erased xb (XbP _ _ _ xb1))
      (let-match erased xb1 (XbZ _ _ y1 xb2))
      (let ((erased e1) (erased cf1) (erased c1)) (sw-push K R l r e _ _ (PkO) (CfB l r x _ K _ ls (XbO R r y1 xb2))))
      (let ((erased e2) (erased so) (erased c2)) (sw-ok _ R s sw1 l r e1 cf1))
      (values e2 so (go-cat _ _ _ c1 c2)))
    ((SwP1T m K1 R W2 tp)
      (let ((erased e2) (erased cf2) (erased po2) (erased c)) (st-turn m K1 _ _ W2 l r e cf (Tl01 R) (Po1 R) tp))
      (values e2 (SoT l r K1 W2 e2 cf2 po2) c))
    ((SwPPT m K1 R W2 tp)
      (let ((erased e2) (erased cf2) (erased po2) (erased c)) (st-turn m K1 _ _ W2 l r e cf (Tl0P R) (PoP R) tp))
      (values e2 (SoT l r K1 W2 e2 cf2 po2) c))
    ((SwP1M s1 K1 R _ sw1)
      (let ((erased e1) (erased cf1) (erased c1)) (st-merge s1 K1 _ _ l r e cf (Tl01 R) (Po1 R)))
      (let ((erased e3) (erased cf3) (erased c3)) (sw-push _ R l r e1 _ _ (PkZ) cf1))
      (let ((erased e2) (erased so) (erased c2)) (sw-ok _ R s sw1 l r e3 cf3))
      (values e2 so (go-cat _ _ _ c1 (go-cat _ _ _ c3 c2))))
    ((SwPPM s1 K1 R _ sw1)
      (let ((erased e1) (erased cf1) (erased c1)) (st-merge s1 K1 _ _ l r e cf (Tl0P R) (PoP R)))
      (let ((erased e2) (erased so) (erased c2)) (sw-ok _ R s sw1 l r e1 cf1))
      (values e2 so (go-cat _ _ _ c1 c2)))))

(def-fns _ $ (erased wk-ok : (erased (List (Nat)) K) (erased (List (Tk)) W Y) (subterm erased (Wk K W Y) wk) (erased (List (Bool)) l r) (erased (Tc) e)
    (erased (Cf (BTrue) l K W r e) cf) (erased (Po W) po) ->
    (erased (List (Bool)) y) (erased (Xb Y r y) xb) (erased (Go e (MkTc 2 (DR) l (bits "10" y))) c))
  (let-match erased wk (WkC m K1 _ W1 W2 _ tl tp wk1)
    ((WkN _) (let-match erased cf (CfH _ _ _ y _ _ ls xb)) (let-match erased ls (LsN _)) (values y xb (go-refl e))))
  (let ((erased e1) (erased cf1) (erased c1)) (hole _ K1 W l r e cf))
  (let ((erased e2) (erased cf2) (erased po2) (erased c2)) (st-turn m K1 W W1 W2 l r e1 cf1 tl po tp))
  (let ((erased y) (erased xb) (erased c3)) (wk-ok K1 W2 Y wk1 l r e2 cf2 po2))
  (values y xb (go-cat _ _ _ c1 (go-cat _ _ _ c2 c3))))

(def-fns _ $ (erased tb-ex : (erased (Tt) T) (erased (Plain T) pl) (erased (List (Bool)) r) -> (erased (List (Bool)) b) (erased (Tb T r b) tb))
  (match erased pl _
    ((PlE) (values r (TbE r)))
    ((Pl1) (values (bits "1" r) (Tb1 r)))))

(def-fns _ $ (erased e11 : (erased (List (Bool)) l x r) (erased (List (Nat)) K) (erased (Ls l K x) ls) ->
    (erased (Tc) e2) (erased (Cf (BTrue) l K (Cons (Tk) (Tp) (Nil (Tk))) (bits "011" r) e2) cf) (erased (Go (MkTc 1 (DR) x (bits "110000" r)) e2) c))
  (values (MkTc 2 (DR) x (bits "100011" r)) (CfH l (bits "011" r) x _ K _ ls (XbP _ _ _ (XbN _))) (go-dl _ _ _ _ _ (c-end11 p3 sg3 x r))))

(def-fns _ $ (erased en-ok : (erased (List (Nat)) K K2) (erased (Tt) T T2) (erased (List (Tk)) W2) (erased (Nat) c) (erased (En K T K2 W2 T2 c) en)
    (erased (List (Bool)) l x r rc u) (erased (Ls l K x) ls) (erased (Rp (BFalse) c r rc) rp) (erased (Tb T rc u) tb) ->
    (erased (List (Bool)) u2) (erased (Tb T2 r u2) tb2) (erased (Tc) e2) (erased (Cf (BTrue) l K2 W2 u2 e2) cf) (erased (Po W2) po)
    (erased (Go (MkTc 1 (DR) x u) e2) g))
  (match erased en _
    ((En11 _)
      (let-match erased tb (Tb11 _))
      (let-match erased (rp-fn _ _ r rc _ rp (RpS _ n3 r _ (rp3 _ r))) (Refl _ _))
      (let ((erased e2) (erased cf) (erased g)) (e11 l x r K ls))
      (values (bits "011" r) (Tb011 r) e2 cf (PoP _) g))
    ((En011 _)
      (let-match erased tb (Tb011 _))
      (let-match erased (rp-fn _ _ r rc _ rp (RpS _ n3 r _ (rp3 _ r))) (Refl _ _))
      (values (bits "0011" r) (Tb0011 r) (MkTc 2 (DR) x (bits "1000011" r)) (CfH l _ x _ K _ ls (XbP _ _ _ (XbN _))) (PoP _)
        (go-dl _ _ _ _ _ (c-end011 p3 sg3 x r))))
    ((EnTP _ pl m K1 W tp)
      (let-match erased (rp-fn _ _ r rc _ rp (rp2 _ r)) (Refl _ _))
      (let ((erased u2) (erased tb2)) (tb-ex T pl r))
      (let ((erased e2) (erased cf) (erased po) (erased g)) (tturn T pl m K1 (Nil (Tk)) W l x r u u2 u2 ls tb tb2 (XbN u2) tp))
      (values u2 tb2 e2 cf po g))
    ((EnT4 m K1 W tp)
      (let-match erased rp (RpZ _ _))
      (let-match erased tb (Tb0011 _))
      (let ((erased e2) (erased cf) (erased po) (erased g))
        (tturn (TtE) (PlE) m K1 (Nil (Tk)) W l x (bits "11" r) u _ _ ls (TbE _) (TbE _) (XbN (bits "11" r)) tp))
      (values (bits "11" r) (Tb11 r) e2 cf po g))
    ((EnMP _ pl s K1)
      (let-match erased (rp-fn _ _ r rc _ rp (RpS _ n3 r _ (rp3 _ r))) (Refl _ _))
      (let ((erased b) (erased tbb)) (tb-ex T pl (bits "00" r)))
      (let ((erased x2) (erased ls2) (erased g1)) (merge T pl s K1 l x (bits "00" r) u b ls tb tbb))
      (let ((erased u2) (erased tb2)) (tb-ex T pl r))
      (let ((erased e2) (erased cf) (erased po) (erased g2))
        (tturn T pl (Zero) (Cons (Nat) (Succ s) K1) (Nil (Tk)) _ l x2 r b u2 u2 ls2 tbb tb2 (XbN u2) (TpZ _)))
      (values u2 tb2 e2 cf po (go-cat _ _ _ g1 g2)))
    ((EnM4 s K1)
      (let-match erased (rp-fn _ _ r rc _ rp (RpS _ n3 r _ (rp3 _ r))) (Refl _ _))
      (let-match erased tb (Tb0011 _))
      (let ((erased x2) (erased ls2) (erased g1)) (merge (TtE) (PlE) s K1 l x (bits "110000" r) u _ ls (TbE _) (TbE _)))
      (let ((erased e2) (erased cf) (erased g2)) (e11 l x2 r _ ls2))
      (values (bits "011" r) (Tb011 r) e2 cf (PoP _) (go-cat _ _ _ g1 g2)))))

(def-fns _ $ (erased gadget : (erased (List (Bool)) x0 u xr) (erased (List (Tk)) W) (erased (Xb (Cons (Tk) (Tp) (Cons (Tk) (T1) W)) u xr) xb) ->
    (erased (Tc) e1) (erased (Cf (BFalse) (bits "00111" x0) (Cons (Nat) n3 (Nil (Nat))) W u e1) cf)
    (erased (Go (MkTc 2 (DR) (bits "00" x0) (bits "10" xr)) e1) g))
  (let-match erased xb (XbP _ _ _ xb1))
  (let-match erased xb1 (XbO _ _ yw xbw))
  (values (MkTc 1 (DR) (bits "0111" (bits "00111" x0)) yw) (CfB _ u _ yw _ W (ls-3 _ _ _ (LsN (bits "00111" x0))) xbw)
    (go-cat _ _ _ (go _ _ (c-gadget p3 sg3 x0 yw)) (go _ _ (c-sw1 p3 sg3 (bits "00111" x0) yw)))))

(def-fns _ $ (erased rd-go : (erased (List (Tk)) X Y) (erased (Tt) T T2) (erased (Nat) c) (erased (Rd X T Y T2 c) rd)
    (erased (List (Bool)) x0 r rc u xr) (erased (Rp (BFalse) c r rc) pc) (erased (Tb T rc u) tb) (erased (Xb X u xr) xb) ->
    (erased (List (Bool)) u2 yr) (erased (Tb T2 r u2) tb2) (erased (Xb Y u2 yr) yb)
    (erased (Go (MkTc 2 (DR) (bits "00" x0) (bits "10" xr)) (MkTc 2 (DR) (bits "00111" x0) (bits "10" yr))) g))
  (match erased rd _
    ((RdT W W2 _ K _ sw wk)
      (let-match erased pc (RpZ _ _))
      (let ((erased e1) (erased cf1) (erased g1)) (gadget x0 u xr W xb))
      (let ((erased e2) (erased so) (erased g2)) (sw-ok _ W _ sw _ u e1 cf1))
      (let-match erased so (SoT _ _ _ _ _ cf2 po))
      (let ((erased yr) (erased yb) (erased g3)) (wk-ok K W2 Y wk _ u e2 cf2 po))
      (values u yr tb yb (go-cat _ _ _ g1 (go-cat _ _ _ g2 g3))))
    ((RdE W W2 _ K K2 _ _ _ sw en wk)
      (let ((erased e1) (erased cf1) (erased g1)) (gadget x0 u xr W xb))
      (let ((erased e2) (erased so) (erased g2)) (sw-ok _ W _ sw _ u e1 cf1))
      (let-match erased so (SoE _ _ _ _ cf2))
      (let-match erased cf2 (CfB _ _ x2 _ _ _ ls2 xb2))
      (let-match erased xb2 (XbN _))
      (let ((erased u2) (erased tb2) (erased e3) (erased cf3) (erased po) (erased g3)) (en-ok K K2 T T2 W2 c en _ x2 r rc u ls2 pc tb))
      (let ((erased yr) (erased yb) (erased g4)) (wk-ok K2 W2 Y wk _ u2 e3 cf3 po))
      (values u2 yr tb2 yb (go-cat _ _ _ g1 (go-cat _ _ _ g2 (go-cat _ _ _ g3 g4)))))))

(def-fns _ $ (erased xrun-run : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Conf) c d) (erased (Bool) g)
    (subterm erased (XRun p c d g) xr) -> (erased (Nat) t) (erased (Run m c t d) r))
  (let-match erased xr (XRS _ _ c1 _ g1 st xr1) ((XR0 _ _) (values (Zero) (RNil m c))))
  (let ((erased t1) (erased r1)) (xrun-run p m ex c1 d g1 xr1))
  (run-cat m c c1 d (Succ (Zero)) t1 (RSnoc m c c c1 (Zero) (RNil m c) (pstep-stp p m ex c c1 st)) r1))

(def-fns _ $ (erased go-run : (erased (Nat) q q2) (erased (List (Bool)) a b a2 b2) (erased (Bool) h h2)
    (erased (Go (MkTc q (DR) a (Cons (Bool) h b)) (MkTc q2 (DR) a2 (Cons (Bool) h2 b2))) g) ->
    (erased (Nat) t) (erased (Run l3 (MkConf q a h b) t (MkConf q2 a2 h2 b2)) r))
  (let-match erased g (MkGo _ _ f rc))
  (let-match erased rc (MkRc _ _ _ _ c c2 ac ac2 xr))
  (let-match erased (as-fn _ c _ ac (asc-r q a b h)) (Refl _ _))
  (let-match erased (as-fn _ c2 _ ac2 (asc-r q2 a2 b2 h2)) (Refl _ _))
  (xrun-run p3 l3 ex3 _ _ f xr))

(def-fns _ $ (erased round-run : (erased (List (Tk)) X Y) (erased (Tt) T T2) (erased (Nat) c n) (erased (Rd X T Y T2 c) rd)
    (erased (List (Bool)) lz r x0 rc u xr) (erased (Rp (BTrue) n lz x0) p0) (erased (Rp (BFalse) c r rc) pc) (erased (Tb T rc u) tb) (erased (Xb X u xr) xb) ->
    (erased (List (Bool)) x3 u2 yr) (erased (Rp (BTrue) (Succ (Succ (Succ n))) lz x3) p1) (erased (Tb T2 r u2) tb2) (erased (Xb Y u2 yr) yb)
    (erased (Nat) t) (erased (Run l3 (MkConf 2 (bits "00" x0) (BTrue) (bits "0" xr)) t (MkConf 2 (bits "00" x3) (BTrue) (bits "0" yr))) run))
  (let ((erased u2) (erased yr) (erased tb2) (erased yb) (erased g)) (rd-go X Y T T2 c rd x0 r rc u xr pc tb xb))
  (let ((erased t) (erased run)) (go-run 2 2 _ _ _ _ _ _ g))
  (values (bits "111" x0) u2 yr (RpS _ _ _ _ (RpS _ _ _ _ (RpS _ n lz x0 p0))) tb2 yb t run))

(def-adts
  ((Rl : ((List (Tk)) X) ((Nat) z n) -> Type)
    enum
    (many RlN : (erased (Nat) z) -> (Rl (Nil (Tk)) z z))
    (many RlP : (erased (List (Tk)) X) (erased (Nat) z n) (erased (Rl X z n) p) -> (Rl (Cons (Tk) (Tp) X) z (Succ n)))
    (many RlZ : (erased (List (Tk)) X) (erased (Nat) z n) (erased (Rl X z n) p) -> (Rl (Cons (Tk) (T0) X) z (Succ (Succ (Succ n)))))
    (many RlO : (erased (List (Tk)) X) (erased (Nat) z n) (erased (Rl X z n) p) -> (Rl (Cons (Tk) (T1) X) z (Succ (Succ (Succ (Succ n))))))))

(def-adts
  ((Tn : ((Tt) T) ((Nat) z n) -> Type)
    enum
    (many TwE : (erased (Nat) z) -> (Tn (TtE) z z))
    (many Tw1 : (erased (Nat) z) -> (Tn (Tt1) z (Succ z)))
    (many Tw11 : (erased (Nat) z) -> (Tn (Tt11) z (Succ (Succ z))))
    (many Tw011 : (erased (Nat) z) -> (Tn (Tt011) z (Succ (Succ (Succ z)))))
    (many Tw0011 : (erased (Nat) z) -> (Tn (Tt0011) z (Succ (Succ (Succ (Succ z))))))))

(def-adts
  ((Kc : ((List (Nat)) K) ((Nat) z n) -> Type)
    enum
    (many KcN : (erased (Nat) z) -> (Kc (Nil (Nat)) z z))
    (many KcC : (erased (Nat) t z a n) (erased (List (Nat)) K) (erased (Add t (Succ z) a) ad) (erased (Kc K a n) p) -> (Kc (Cons (Nat) t K) z n))))

(def-adts
  ((Sc : ((Nat) z n) ((SRes) s) -> Type)
    enum
    (many ScT : (erased (Nat) z n u) (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (Rl W (Succ (Succ z)) u) rl) (erased (Kc K u n) kc)
       (erased (Po W) po) -> (Sc z n (STurn K W)))
    (many ScE : (erased (Nat) z n) (erased (List (Nat)) K) (erased (Kc K z n) kc) -> (Sc z n (SEnd K)))))

(def-fns _ $ (erased add2 : (erased (Nat) x) -> (erased (Add n2 x (Succ (Succ x))) p))
  (AddSucc _ x _ (AddSucc _ x _ (AddZero x))))

(def-fns _ $ (erased add3 : (erased (Nat) x) -> (erased (Add n3 x (Succ (Succ (Succ x)))) p))
  (AddSucc _ x _ (add2 x)))

(def-fns _ $ (erased rl-ss : (erased (List (Tk)) X) (erased (Nat) z n) (subterm erased (Rl X z n) rl) -> (erased (Rl X (Succ z) (Succ n)) r))
  (match erased rl _
    ((RlN _) (RlN (Succ z)))
    ((RlP X1 _ n1 p) (RlP X1 (Succ z) (Succ n1) (rl-ss X1 z n1 p)))
    ((RlZ X1 _ n1 p) (RlZ X1 (Succ z) (Succ n1) (rl-ss X1 z n1 p)))
    ((RlO X1 _ n1 p) (RlO X1 (Succ z) (Succ n1) (rl-ss X1 z n1 p)))))

(def-fns _ $ (erased rl-tpr : (erased (Nat) m) (erased (List (Tk)) X W) (erased (Nat) z u) (subterm erased (TpR m X W) tp) (erased (Rl X z u) rl) ->
    (erased (Nat) u2) (erased (Rl W z u2) rl2) (erased (Add m u u2) ad))
  (let-match erased tp (TpS m1 _ W1 tp1) ((TpZ _) (values u rl (AddZero u))))
  (let ((erased u1) (erased r1) (erased a1)) (rl-tpr m1 X W1 z u tp1 rl))
  (values (Succ u1) (RlP W1 z u1 r1) (AddSucc m1 u u1 a1)))

(def-fns _ $ (erased tl0-rl : (erased (List (Tk)) W W1) (erased (Nat) z u) (erased (Tl0 W W1) tl) (erased (Rl W z u) rl) (erased (Po W) po) ->
    (erased (Nat) u1) (erased (Rl W1 z u1) r1) (erased (Eq (Nat) u (Succ u1)) e))
  (match erased tl _
    (absurd (Tl0N) po)
    ((Tl0P R) (let-match erased rl (RlP _ _ u1 r1)) (values u1 r1 (Refl _ u)))
    ((Tl01 R) (let-match erased rl (RlO _ _ n1 r1)) (values (Succ (Succ (Succ n1))) (RlZ R z n1 r1) (Refl _ u)))))

(def-fns _ $ (erased kc-turn : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) X W) (erased (Nat) z u n)
    (erased (Kc (Cons (Nat) (Succ (Succ m)) K) u n) kc) (erased (TpR m X W) tp) (erased (Rl X z (Succ (Succ (Succ u)))) rl) ->
    (erased (Nat) u2) (erased (Rl W z u2) rl2) (erased (Kc K u2 n) kc2))
  (let-match erased kc (KcC _ _ a _ _ ad kc1))
  (let-match erased ad (AddSucc _ _ a1 ad1))
  (let-match erased ad1 (AddSucc _ _ a2 ad2))
  (let ((erased u2) (erased rl2) (erased ad3)) (rl-tpr m X W z _ tp rl))
  (let-match erased (add-fn m _ u2 _ ad3 (add-succ-right m _ _ (add-succ-right m _ _ ad2))) (Refl _ _))
  (values u2 rl2 kc1))

(def-fns _ $ (erased kc-hole : (erased (Nat) t u n) (erased (List (Nat)) K) (erased (Kc (Cons (Nat) (Succ t) K) u n) kc) -> (erased (Kc (Cons (Nat) t K) (Succ u) n) r))
  (let-match erased kc (KcC _ _ a _ _ ad kc1))
  (let-match erased ad (AddSucc _ _ a1 ad1))
  (KcC t (Succ u) a n K (add-succ-right t _ _ ad1) kc1))

(def-fns _ $ (erased kc-merge : (erased (Nat) s w n) (erased (List (Nat)) K) (erased (Kc (Cons (Nat) n2 (Cons (Nat) s K)) (Succ (Succ w)) n) kc) ->
    (erased (Kc (Cons (Nat) n3 (Cons (Nat) (Succ s) K)) w n) r))
  (let-match erased kc (KcC _ _ a _ _ ad kc1))
  (let-match erased (add-fn n2 _ a _ ad (add2 _)) (Refl _ _))
  (let-match erased kc1 (KcC _ _ b _ _ ad1 kc2))
  (let ((erased b1) (erased eb) (erased ad2)) (add-succ-right-inv s _ b ad1))
  (let-match erased eb (Refl _ _))
  (KcC n3 w _ n _ (add3 _) (KcC (Succ s) _ b n K (AddSucc s _ b1 ad2) kc2)))

(def-fns _ $ (erased cnt-turn : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) W W1 W2) (erased (Nat) z u n)
    (erased (Kc (Cons (Nat) (Succ (Succ (Succ m))) K) u n) kc) (erased (Rl (Cons (Tk) (Tp) W) z u) rl) (erased (Tl0 W W1) tl) (erased (Po W) po)
    (erased (TpR m (Cons (Tk) (T1) W1) W2) tp) -> (erased (Sc z n (STurn K W2)) sc))
  (let-match erased rl (RlP _ _ u0 r0))
  (let ((erased u1) (erased r1) (erased e)) (tl0-rl W W1 z u0 tl r0 po))
  (let-match erased e (Refl _ _))
  (let ((erased u2) (erased rl2) (erased kc2))
    (kc-turn m K _ W2 (Succ (Succ z)) _ n (kc-hole _ _ n K kc) tp (RlO W1 _ _ (rl-ss W1 _ _ (rl-ss W1 z u1 r1)))))
  (ScT z n u2 K W2 rl2 kc2 (po-tpr m W1 W2 tp)))

(def-fns _ $ (erased cnt-merge : (erased (Nat) s) (erased (List (Nat)) K) (erased (List (Tk)) W W1) (erased (Nat) z u n)
    (erased (Kc (Cons (Nat) n2 (Cons (Nat) s K)) u n) kc) (erased (Rl (Cons (Tk) (Tp) W) z u) rl) (erased (Tl0 W W1) tl) (erased (Po W) po) ->
    (erased (Nat) u1) (erased (Rl W1 z u1) r1) (erased (Kc (Cons (Nat) n3 (Cons (Nat) (Succ s) K)) u1 n) kc1))
  (let-match erased rl (RlP _ _ u0 r0))
  (let ((erased u1) (erased r1) (erased e)) (tl0-rl W W1 z u0 tl r0 po))
  (let-match erased e (Refl _ _))
  (values u1 r1 (kc-merge s u1 n K kc)))

(def-fns _ $ (erased sw-cnt : (erased (List (Nat)) K) (erased (List (Tk)) W) (erased (SRes) s) (subterm erased (Sw K W s) sw)
    (erased (Nat) z u n) (erased (Rl W z u) rl) (erased (Kc K u n) kc) -> (erased (Sc z n s) sc))
  (match erased sw _
    ((SwEnd _) (let-match erased rl (RlN _)) (ScE z n K kc))
    ((SwT0 _ R _ sw1) (let-match erased rl (RlZ _ _ u1 r1)) (sw-cnt _ R s sw1 z u1 n r1 (KcC n2 u1 u n K (add2 _) kc)))
    ((SwT1 _ R _ sw1) (let-match erased rl (RlO _ _ u1 r1)) (sw-cnt _ R s sw1 z u1 n r1 (KcC n3 u1 u n K (add3 _) kc)))
    ((SwP0 _ R _ sw1)
      (let-match erased rl (RlP _ _ _ r0))
      (let-match erased r0 (RlZ _ _ u1 r1))
      (sw-cnt _ R s sw1 z u1 n r1 (KcC n3 u1 u n K (add3 _) kc)))
    ((SwP1T m K1 R W2 tp) (cnt-turn m K1 _ _ W2 z u n kc rl (Tl01 R) (Po1 R) tp))
    ((SwPPT m K1 R W2 tp) (cnt-turn m K1 _ _ W2 z u n kc rl (Tl0P R) (PoP R) tp))
    ((SwP1M s1 K1 R _ sw1)
      (let ((erased u1) (erased r1) (erased kc1)) (cnt-merge s1 K1 _ _ z u n kc rl (Tl01 R) (Po1 R)))
      (let-match erased r1 (RlZ _ _ uR rR))
      (sw-cnt _ R s sw1 z uR n rR (KcC n2 uR u1 n _ (add2 _) kc1)))
    ((SwPPM s1 K1 R _ sw1)
      (let ((erased u1) (erased r1) (erased kc1)) (cnt-merge s1 K1 _ _ z u n kc rl (Tl0P R) (PoP R)))
      (sw-cnt _ R s sw1 z u1 n r1 kc1))))

(def-fns _ $ (erased wk-cnt : (erased (List (Nat)) K) (erased (List (Tk)) W Y) (subterm erased (Wk K W Y) wk) (erased (Nat) z u n)
    (erased (Rl W z u) rl) (erased (Kc K u n) kc) (erased (Po W) po) -> (erased (Rl Y z n) r))
  (let-match erased wk (WkC m K1 _ W1 W2 _ tl tp wk1) ((WkN _) (let-match erased kc (KcN _)) rl))
  (let ((erased u1) (erased r1) (erased e)) (tl0-rl W W1 z u tl rl po))
  (let-match erased e (Refl _ _))
  (let ((erased u2) (erased rl2) (erased kc2)) (kc-turn m K1 _ W2 z _ n kc tp (RlO W1 z u1 r1)))
  (wk-cnt K1 W2 Y wk1 z u2 n rl2 kc2 (po-tpr m W1 W2 tp)))

(def-fns _ $ (erased tn-p2 : (erased (Tt) T) (erased (Plain T) pl) (erased (Nat) z a) (erased (Tn T (Succ (Succ z)) a) tw) ->
    (erased (Nat) a2) (erased (Tn T z a2) tw2) (erased (Eq (Nat) a (Succ (Succ a2))) e))
  (match erased pl _
    ((PlE) (let-match erased tw (TwE _)) (values z (TwE z) (Refl _ a)))
    ((Pl1) (let-match erased tw (Tw1 _)) (values (Succ z) (Tw1 z) (Refl _ a)))))

(def-fns _ $ (erased en-cnt : (erased (List (Nat)) K K2) (erased (Tt) T T2) (erased (List (Tk)) W2) (erased (Nat) c) (erased (En K T K2 W2 T2 c) en)
    (erased (Nat) a n) (erased (Tn T c a) tw) (erased (Kc K a n) kc) ->
    (erased (Nat) t2) (erased (Tn T2 n2 t2) tw2) (erased (Nat) u) (erased (Rl W2 t2 u) rl) (erased (Kc K2 u n) kc2) (erased (Po W2) po))
  (match erased en _
    ((En11 _) (let-match erased tw (Tw11 _))
      (values (Succ (Succ (Succ n2))) (Tw011 n2) (Succ (Succ (Succ (Succ n2)))) (RlP _ _ _ (RlN _)) kc (PoP _)))
    ((En011 _) (let-match erased tw (Tw011 _))
      (values (Succ (Succ (Succ (Succ n2)))) (Tw0011 n2) (Succ (Succ (Succ (Succ (Succ n2))))) (RlP _ _ _ (RlN _)) kc (PoP _)))
    ((EnTP _ pl m K1 W tp)
      (let ((erased u2) (erased rl2) (erased kc2)) (kc-turn m K1 _ W a _ n (kc-hole _ a n K1 kc) tp (RlO _ a a (RlN a))))
      (values a tw u2 rl2 kc2 (po-tpr m _ W tp)))
    ((EnT4 m K1 W tp)
      (let-match erased tw (Tw0011 _))
      (let ((erased u2) (erased rl2) (erased kc2)) (kc-turn m K1 _ W a _ n (kc-hole _ a n K1 kc) tp (RlO _ a a (RlN a))))
      (values a (Tw11 n2) u2 rl2 kc2 (po-tpr m _ W tp)))
    ((EnMP _ pl s K1)
      (let ((erased a2) (erased tw2) (erased e)) (tn-p2 T pl n2 a tw))
      (let-match erased e (Refl _ _))
      (let ((erased u2) (erased rl2) (erased kc2))
        (kc-turn (Zero) _ _ _ a2 _ n (kc-hole _ a2 n _ (kc-merge s a2 n K1 kc)) (TpZ _) (RlO _ a2 a2 (RlN a2))))
      (values a2 tw2 u2 rl2 kc2 (Po1 _)))
    ((EnM4 s K1) (let-match erased tw (Tw0011 _))
      (values (Succ (Succ (Succ n2))) (Tw011 n2) (Succ (Succ (Succ (Succ n2)))) (RlP _ _ _ (RlN _)) (kc-merge s _ n K1 kc) (PoP _)))))

(def-fns _ $ (erased tn-ss : (erased (Tt) T) (erased (Nat) z n) (erased (Tn T z n) tw) -> (erased (Tn T (Succ z) (Succ n)) r))
  (match erased tw _
    ((TwE _) (TwE (Succ z)))
    ((Tw1 _) (Tw1 (Succ z)))
    ((Tw11 _) (Tw11 (Succ z)))
    ((Tw011 _) (Tw011 (Succ z)))
    ((Tw0011 _) (Tw0011 (Succ z)))))

(def-fns _ $ (erased rd-cnt : (erased (List (Tk)) X Y) (erased (Tt) T T2) (erased (Nat) c) (erased (Rd X T Y T2 c) rd)
    (erased (Nat) z n) (erased (Tn T c z) tw) (erased (Rl X z n) rl) -> (erased (Nat) t3) (erased (Tn T2 n3 t3) tw3) (erased (Rl Y t3 n) r))
  (match erased rd _
    ((RdT W W2 _ K _ sw wk)
      (let-match erased rl (RlP _ _ _ r1))
      (let-match erased r1 (RlO _ _ uW rW))
      (let-match erased (sw-cnt _ W _ sw z uW _ rW (KcC n3 uW _ _ _ (add3 _) (KcN _))) (ScT _ _ u _ _ rl2 kc2 po))
      (values (Succ (Succ (Succ z))) (tn-ss T _ _ (tn-ss T _ _ (tn-ss T _ _ tw))) (rl-ss Y _ _ (wk-cnt K W2 Y wk _ u _ rl2 kc2 po))))
    ((RdE W W2 _ K K2 _ _ _ sw en wk)
      (let-match erased rl (RlP _ _ _ r1))
      (let-match erased r1 (RlO _ _ uW rW))
      (let-match erased (sw-cnt _ W _ sw z uW _ rW (KcC n3 uW _ _ _ (add3 _) (KcN _))) (ScE _ _ _ kc1))
      (let ((erased t2) (erased tw2) (erased u) (erased rl2) (erased kc2) (erased po)) (en-cnt K K2 T T2 W2 c en z _ tw kc1))
      (values (Succ t2) (tn-ss T2 _ _ tw2) (rl-ss Y _ _ (wk-cnt K2 W2 Y wk t2 u _ rl2 kc2 po))))))

(def-fns _ $ (erased tn-ex : (erased (Tt) T) (erased (Nat) z) -> (erased (Nat) n) (erased (Tn T z n) tw))
  (match erased T _
    ((TtE) (values z (TwE z)))
    ((Tt1) (values (Succ z) (Tw1 z)))
    ((Tt11) (values (Succ (Succ z)) (Tw11 z)))
    ((Tt011) (values (Succ (Succ (Succ z))) (Tw011 z)))
    ((Tt0011) (values (Succ (Succ (Succ (Succ z)))) (Tw0011 z)))))

(def-fns _ $ (erased tn-add : (erased (Tt) T) (erased (Nat) z n b) (erased (Tn T z n) tw) (erased (Tn T (Zero) b) wb) -> (erased (Add b z n) ad))
  (match erased tw _
    ((TwE _) (let-match erased wb (TwE _)) (AddZero z))
    ((Tw1 _) (let-match erased wb (Tw1 _)) (AddSucc _ z _ (AddZero z)))
    ((Tw11 _) (let-match erased wb (Tw11 _)) (add2 z))
    ((Tw011 _) (let-match erased wb (Tw011 _)) (add3 z))
    ((Tw0011 _) (let-match erased wb (Tw0011 _)) (AddSucc _ z _ (add3 z)))))

(def-fns _ $ (erased rl-sh : (erased (List (Tk)) X) (erased (Nat) a z) (subterm erased (Rl X (Zero) a) ra) -> (erased (Nat) n) (erased (Rl X z n) rl) (erased (Add a z n) ad))
  (match erased ra _
    ((RlN _) (values z (RlN z) (AddZero z)))
    ((RlP X1 _ a1 p) (let ((erased n1) (erased r1) (erased d1)) (rl-sh X1 a1 z p))
      (values (Succ n1) (RlP X1 z n1 r1) (AddSucc a1 z n1 d1)))
    ((RlZ X1 _ a1 p) (let ((erased n1) (erased r1) (erased d1)) (rl-sh X1 a1 z p))
      (values (Succ (Succ (Succ n1))) (RlZ X1 z n1 r1) (AddSucc _ z _ (AddSucc _ z _ (AddSucc a1 z n1 d1)))))
    ((RlO X1 _ a1 p) (let ((erased n1) (erased r1) (erased d1)) (rl-sh X1 a1 z p))
      (values (Succ (Succ (Succ (Succ n1)))) (RlO X1 z n1 r1) (AddSucc _ z _ (AddSucc _ z _ (AddSucc _ z _ (AddSucc a1 z n1 d1))))))))

(def-fns _ $ (erased rl-fn : (erased (List (Tk)) X) (erased (Nat) z n k) (subterm erased (Rl X z n) p) (erased (Rl X z k) q) -> (erased (Eq (Nat) n k) e))
  (match erased p _
    ((RlN _) (let-match erased q (RlN _)) (Refl _ n))
    ((RlP X1 _ n1 p1) (let-match erased q (RlP _ _ j1 q1)) (let-match erased (rl-fn X1 z n1 j1 p1 q1) (Refl _ _)) (Refl _ n))
    ((RlZ X1 _ n1 p1) (let-match erased q (RlZ _ _ j1 q1)) (let-match erased (rl-fn X1 z n1 j1 p1 q1) (Refl _ _)) (Refl _ n))
    ((RlO X1 _ n1 p1) (let-match erased q (RlO _ _ j1 q1)) (let-match erased (rl-fn X1 z n1 j1 p1 q1) (Refl _ _)) (Refl _ n))))

(def-fns _ $ (erased rd-cells : (erased (List (Tk)) X Y) (erased (Tt) T T2) (erased (Nat) c) (erased (Rd X T Y T2 c) rd)
    (erased (Nat) a b a2 b2) (erased (Rl X (Zero) a) ra) (erased (Tn T (Zero) b) wb) (erased (Rl Y (Zero) a2) ra2) (erased (Tn T2 (Zero) b2) wb2) ->
    (erased (Nat) s u v) (erased (Add a b u) q1) (erased (Add u c s) q2) (erased (Add a2 b2 v) q3) (erased (Add v n3 s) q4))
  (let ((erased tc) (erased wc)) (tn-ex T c))
  (let ((erased s) (erased rx) (erased ax)) (rl-sh X a tc ra))
  (let ((erased t3) (erased w3) (erased ry)) (rd-cnt X Y T T2 c rd tc s wc rx))
  (let ((erased s2) (erased ry2) (erased ay)) (rl-sh Y a2 t3 ra2))
  (let-match erased (rl-fn Y t3 s s2 ry ry2) (Refl _ _))
  (let ((erased u) (erased q1) (erased q2)) (add-al a b c tc s (tn-add T c tc b wc wb) ax))
  (let ((erased v) (erased q3) (erased q4)) (add-al a2 b2 n3 t3 s (tn-add T2 n3 t3 b2 w3 wb2) ay))
  (values s u v q1 q2 q3 q4))
