; converse_part of part.v certified, and fitp_converse: a rule fitting exactly at a dart y makes its converse fit the
; dart t with face^2 t = edge (face^2 y), the hub across the third spoke; from it the target bound TgtAll of
; hubsound.sl. Load after pwsound.sl.

(unary 3 2)

; Through a composite: h (g (p x)) = x when gp = g . p and h . gp is the identity.
(def-fns _ $ (erased resp3 : (erased (Nat) d x a b) (erased (List (Nat)) g p h gp ids) (erased (Respects g p gp) r1) (erased (Respects h gp ids) r2)
    (erased (Iota d ids) io) (erased (Length (Nat) p d) lp) (erased (Lt x d) lx) (erased (Nth (Nat) p x a) pa) (erased (Nth (Nat) g a b) pb)
    -> (erased (Nth (Nat) h b x) r))
  (let ((erased b2) (erased pb2)) (nth-exists _ gp d x (respects-length g p gp d r1 lp) lx))
  (let-match erased (nth-fn _ g a b2 b (respects-nth g p gp x a b2 r1 pa pb2) pb) (Refl _ _))
  (respects-nth h gp ids x b x r2 pb2 (iota-nth d x ids io lx)))

(def-fns _ $ (erased nfe : (erased (Nat) d x a b) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Lt x d) lx)
    (erased (Nth (Nat) e x a) pa) (erased (Nth (Nat) f a b) pb) -> (erased (Nth (Nat) n b x) r))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased le) (erased _) (erased _)) (hyper-lengths d e n f h))
  (resp3 d x a b f e n fe ids cfe ke io le lx pa pb))

(def-fns _ $ (erased fen : (erased (Nat) d x a b) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Lt x d) lx)
    (erased (Nth (Nat) n x a) pa) (erased (Nth (Nat) e a b) pb) -> (erased (Nth (Nat) f b x) r))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased _) (erased ln) (erased _)) (hyper-lengths d e n f h))
  (resp3 d x a b e n f en ids cen kn io ln lx pa pb))

(def-fns _ $ (erased enf : (erased (Nat) d x a b) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Lt x d) lx)
    (erased (Nth (Nat) f x a) pa) (erased (Nth (Nat) n a b) pb) -> (erased (Nth (Nat) e b x) r))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased _) (erased _) (erased lf)) (hyper-lengths d e n f h))
  (resp3 d x a b n f e nf ids cnf kf io lf lx pa pb))

(def-fns _ $ (erased img-lt : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) (erased (Lt x d) lx) (erased (Nth (Nat) p x y) px)
    -> (erased (Lt y d) r))
  (let ((erased y2) (erased py2) (erased ly2)) (perm-nth d x p q pm lx))
  (let-match erased (nth-fn _ p x y y2 px py2) (Refl _ _))
  ly2)

(def-fns _ $ (erased img-lt-inv : (erased (Nat) d u s) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) (erased (Lt s d) ls) (erased (Nth (Nat) p u s) pu)
    -> (erased (Lt u d) r))
  (img-lt d s u q p (perm-sym d p q pm) ls (perm-inv d u s p q pm pu)))

; The one local fact of plain cubic maps used here: for a hub dart x with spokes s = edge x and s1 = edge (face x),
; the dart u before s along its face has edge u = face s1.
(def-fns _ $ (erased g2 : (erased (Nat) d x x1 s s1 u) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Lt x d) lx)
    (erased (Nth (Nat) f x x1) p1) (erased (Nth (Nat) e x s) ps) (erased (Nth (Nat) e x1 s1) ps1) (erased (Nth (Nat) f u s) pu)
    -> (erased (Nat) v) (erased (Nth (Nat) e u v) r1) (erased (Nth (Nat) f s1 v) r2))
  (let-match erased g (MkGeo _ _ _ _ _ h pl cu _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased lx1)) (img-lt d x x1 f fi pf lx p1))
  (let ((erased c) (erased pc) (erased lc)) (perm-nth d x1 n ni pn lx1))
  (let ((erased pc1) (erased _)) (plain-eq d c x e pl lc (enf d x x1 c e n f h lx p1 pc)))
  (let-match erased (nth-fn _ e x c s pc1 ps) (Refl _ _))
  (let ((erased c2) (erased pc2) (erased pc3) (erased _) (erased _)) (cubic-eq d x1 s n cu lx1 pc))
  (let ((erased ls)) (img-lt d x s e nf pe lx ps))
  (let ((erased lc2)) (img-lt d s c2 n ni pn ls pc2))
  (let ((erased b) (erased pb) (erased _)) (perm-nth d c2 e nf pe lc2))
  (let-match erased (perm-inj d b u s f fi pf (fen d s c2 b e n f h ls pc2 pb) pu) (Refl _ _))
  (let ((erased pu2) (erased _)) (plain-eq d c2 u e pl lc2 pb))
  (let ((erased ls1)) (img-lt d x1 s1 e nf pe lx1 ps1))
  (let ((erased gg) (erased pg) (erased _)) (perm-nth d s1 f fi pf ls1))
  (let-match erased (perm-inj d gg c2 x1 n ni pn (nfe d x1 s1 gg e n f h lx1 ps1 pg) pc3) (Refl _ _))
  (values c2 pu2 pg))

; Two steps back from the spoke s: edge t = face (edge (face^2 s1)).
(def-fns _ $ (erased g1 : (erased (Nat) d x x1 s s1 t u0) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Lt x d) lx)
    (erased (Nth (Nat) f x x1) p1) (erased (Nth (Nat) e x s) ps) (erased (Nth (Nat) e x1 s1) ps1) (erased (Nth (Nat) f t u0) pt) (erased (Nth (Nat) f u0 s) pu)
    -> (erased (Nat) a w v vv) (erased (Nth (Nat) f s1 a) r1) (erased (Nth (Nat) f a w) r2) (erased (Nth (Nat) e w v) r3) (erased (Nth (Nat) e t vv) r4)
    (erased (Nth (Nat) f v vv) r5))
  (let-match erased g (MkGeo _ _ _ _ _ h pl _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased a) (erased q1) (erased q2)) (g2 d x x1 s s1 u0 e n f ks g lx p1 ps ps1 pu))
  (let ((erased lx1)) (img-lt d x x1 f fi pf lx p1))
  (let ((erased ls1)) (img-lt d x1 s1 e nf pe lx1 ps1))
  (let ((erased la)) (img-lt d s1 a f fi pf ls1 q2))
  (let ((erased w) (erased pw) (erased lw)) (perm-nth d a f fi pf la))
  (let ((erased v) (erased pv) (erased _)) (perm-nth d w e nf pe lw))
  (let ((erased q3) (erased _)) (plain-eq d u0 a e pl (img-lt-inv d u0 s f fi pf (img-lt d x s e nf pe lx ps) pu) q1))
  (let ((erased vv) (erased q4) (erased q5)) (g2 d a w u0 v t e n f ks g la pw q3 pv pt))
  (values a w v vv q2 pw pv q4 q5))

; One step on from the spoke s = edge x: face (edge (face s)) = edge v for the hub dart v before x.
(def-fns _ $ (erased g3 : (erased (Nat) d x s v0 w0) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Lt x d) lx)
    (erased (Nth (Nat) e x s) ps) (erased (Nth (Nat) f v0 x) pv) (erased (Nth (Nat) e v0 w0) pw)
    -> (erased (Nat) a c) (erased (Nth (Nat) f s a) r1) (erased (Nth (Nat) e a c) r2) (erased (Nth (Nat) f c w0) r3))
  (let-match erased g (MkGeo _ _ _ _ _ h pl _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased lv)) (img-lt-inv d v0 x f fi pf lx pv))
  (let ((erased lw)) (img-lt d v0 w0 e nf pe lv pw))
  (let ((erased u) (erased pu) (erased lu)) (perm-nth d w0 fi f (perm-sym d f fi pf) lw))
  (let ((erased pu2)) (perm-inv d w0 u fi f (perm-sym d f fi pf) pu))
  (let ((erased a) (erased q1) (erased q2)) (g2 d v0 x w0 s u e n f ks g lv pv pw ps pu2))
  (let ((erased q3) (erased _)) (plain-eq d u a e pl lu q1))
  (values a u q2 q3 pu2))

(def-fns _ $ (erased arity-same : (erased (Nat) d w v k a b) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Lt w d) lw)
    (erased (Nth (Nat) ks w a) pa) (erased (Iter f k w v) it) (erased (Nth (Nat) ks v b) pb) -> (erased (Eq (Nat) a b) r))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ ol _))
  (let ((erased v2) (erased it2) (erased _) (erased pa2)) (face-walk d w a e n f ks h ol k lw pa))
  (let-match erased (iter-fn f k w v2 v it2 it) (Refl _ _))
  (nth-fn _ ks v a b pa2 pb))

(def-fns _ $ (erased one-step : (erased (List (Nat)) f) (erased (Nat) x y) (erased (Nth (Nat) f x y) p) -> (erased (Iter f 1 x y) r))
  (ItS f (Zero) x y y p (ItZ f y)))

(def-fns _ $ (erased cyc-back : (erased (Nat) d v z z2 k j a) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Lt v d) lv)
    (erased (Nth (Nat) ks v a) pa) (erased (Iter f k v z) p1) (erased (Iter f j z z2) p2) (erased (Add k j a) ad) -> (erased (Eq (Nat) z2 v) r))
  (let-match erased g (MkGeo _ _ _ _ _ _ _ _ ol _))
  (iter-fn f a v z2 v (iter-add f k j a v z z2 p1 p2 ad) (face-cycle d v a f ks ol lv pa)))

(def-fns _ $ (erased two-step : (erased (List (Nat)) f) (erased (Nat) x y z) (erased (Nth (Nat) f x y) p) (erased (Nth (Nat) f y z) q) -> (erased (Iter f 2 x z) r))
  (ItS f 1 x y z p (one-step f y z q)))

(def-fns _ $ (erased iter-lt : (erased (Nat) d k x z) (erased (List (Nat)) f fi) (erased (HPerm d f fi) pf) (erased (Lt x d) lx) (subterm erased (Iter f k x z) it)
    -> (erased (Lt z d) r))
  (let-match erased it (ItS _ k1 _ y _ py it1) ((ItZ _ _) lx))
  (iter-lt d k1 y z f fi pf (img-lt d x y f fi pf lx py) it1))

; A sector with its darts: spoke z = edge y, w = face^2 z, hat dart u = edge w, and z3 = face^3 z.
(def-adts $ (SecD : ((List (Nat)) e f ks) ((Nat) y z w u z3) ((Sec) o) -> Type)
  enum
  (many MkSecD : (erased (List (Nat)) e f ks) (erased (Nat) y z a w u h z3 m) (erased (List (Nat)) fs) (erased (Nth (Nat) e y z) pz)
      (erased (Nth (Nat) ks z a) pa) (erased (Iter f 2 z w) pw) (erased (Nth (Nat) e w u) pu) (erased (Nth (Nat) ks u h) ph) (erased (Iter f 3 z z3) p3)
      (erased (Monus a 5 m) mo) (erased (FansAt e f ks z3 m fs) pfs) -> (SecD e f ks y z w u z3 (MkSec a h fs))))

(def-fns _ $ (erased sec-d : (erased (List (Nat)) e f ks) (erased (Nat) y) (erased (Sec) o) (erased (SecAt e f ks y o) so)
    -> (erased (Nat) z w u z3) (erased (SecD e f ks y z w u z3 o) r))
  (let-match erased so (MkSecAt _ _ _ _ z a w u h z3 m fs pz pa pw pu ph p3 mo pfs))
  (values z w u z3 (MkSecD e f ks y z a w u h z3 m fs pz pa pw pu ph p3 mo pfs)))

(def-fns _ $ (erased iter3 : (erased (List (Nat)) f) (erased (Nat) x a c) (erased (Nth (Nat) f x a) p) (erased (Iter f 2 a c) q) -> (erased (Iter f 3 x c) r))
  (ItS f 2 x a c p q))

; face^3 z is the image of face^2 z.
(def-fns _ $ (erased f3-next : (erased (List (Nat)) f) (erased (Nat) z w z3) (erased (Iter f 2 z w) pw) (erased (Iter f 3 z z3) p3) -> (erased (Nth (Nat) f w z3) r))
  (let-match erased pw (ItS _ _ _ b1 _ pb1 pw1))
  (let-match erased pw1 (ItS _ _ _ b2 _ pb2 pw2))
  (let-match erased pw2 (ItZ _ _))
  (let-match erased p3 (ItS _ _ _ c1 _ pc1 p31))
  (let-match erased (nth-fn _ f z b1 c1 pb1 pc1) (Refl _ _))
  (let-match erased p31 (ItS _ _ _ c2 _ pc2 p32))
  (let-match erased (nth-fn _ f b1 b2 c2 pb2 pc2) (Refl _ _))
  (let-match erased p32 (ItS _ _ _ c3 _ pc3 p33))
  (let-match erased p33 (ItZ _ _))
  pc3)

; The target's first spoke: the hat face of the rule's fourth sector.
(def-fns _ $ (erased tsec0 : (erased (Nat) d y2 y3 s2 t t1 sg wt ut zt sp w3 hd z3 a0 h0 aa hh) (erased (List (Nat)) e n f ks fs0 ff) (erased (Geo d e n f ks) g)
    (erased (Lt y2 d) ly) (erased (Nth (Nat) f y2 y3) p23) (erased (Nth (Nat) e y2 s2) ps2) (erased (Nth (Nat) f t t1) pt) (erased (Nth (Nat) f t1 s2) pt1)
    (erased (SecD e f ks t sg wt ut zt (MkSec a0 h0 fs0)) st) (erased (SecD e f ks y3 sp w3 hd z3 (MkSec aa hh ff)) s3) -> (erased (Eq (Nat) hh a0) r))
  (let-match erased st (MkSecD _ _ _ _ _ _ _ _ _ _ _ _ psg pa0 _ _ _ _ _ _))
  (let-match erased s3 (MkSecD _ _ _ _ _ _ _ _ _ _ _ _ psp _ pw3 phd ph3 _ _ _))
  (let ((erased a) (erased w) (erased v) (erased vv) (erased q1) (erased q2) (erased q3) (erased q4) (erased q5)) (g1 d y2 y3 s2 sp t t1 e n f ks g ly p23 ps2 psp pt pt1))
  (let-match erased (iter-fn f 2 sp w w3 (two-step f sp a w q1 q2) pw3) (Refl _ _))
  (let-match erased (nth-fn _ e w v hd q3 phd) (Refl _ _))
  (let-match erased (nth-fn _ e t vv sg q4 psg) (Refl _ _))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased lsp)) (img-lt d y3 sp e nf pe (img-lt d y2 y3 f fi pf ly p23) psp))
  (let ((erased lhd)) (img-lt d w v e nf pe (iter-lt d 2 sp w f fi pf lsp pw3) q3))
  (arity-same d v vv 1 hh a0 e n f ks g lhd ph3 (one-step f v vv q5) pa0))

; The target's second sector: its spoke face is the rule's fourth spoke face, entered one dart on; so its w is the
; rule's z3 there.
(def-fns _ $ (erased tsec1 : (erased (Nat) d y2 y3 s2 t1 sg wt ut zt sp w3 hd z3 a1 h1 aa hh) (erased (List (Nat)) e n f ks fs1 ff) (erased (Geo d e n f ks) g)
    (erased (Lt y2 d) ly) (erased (Nth (Nat) f y2 y3) p23) (erased (Nth (Nat) e y2 s2) ps2) (erased (Nth (Nat) f t1 s2) pt1)
    (erased (SecD e f ks t1 sg wt ut zt (MkSec a1 h1 fs1)) st) (erased (SecD e f ks y3 sp w3 hd z3 (MkSec aa hh ff)) s3)
    -> (erased (Eq (Nat) aa a1) r) (erased (Nth (Nat) f sp sg) q0) (erased (Eq (Nat) wt z3) q1) (erased (Nth (Nat) f z3 zt) q2))
  (let-match erased st (MkSecD _ _ _ _ _ _ _ _ _ _ _ _ psg pa1 pwt _ _ pzt _ _))
  (let-match erased s3 (MkSecD _ _ _ _ _ _ _ _ _ _ _ _ psp pa _ _ _ p3r _ _))
  (let ((erased v) (erased q1) (erased q2)) (g2 d y2 y3 s2 sp t1 e n f ks g ly p23 ps2 psp pt1))
  (let-match erased (nth-fn _ e t1 v sg q1 psg) (Refl _ _))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased lsp)) (img-lt d y3 sp e nf pe (img-lt d y2 y3 f fi pf ly p23) psp))
  (let ((erased e1)) (arity-same d sp sg 1 aa a1 e n f ks g lsp pa (one-step f sp sg q2) pa1))
  (let-match erased (iter-fn f 3 sp wt z3 (iter3 f sp sg wt q2 pwt) p3r) (Refl _ _))
  (let ((erased q3)) (f3-next f sg wt zt pwt pzt))
  (values e1 q2 (Refl _ wt) q3))
