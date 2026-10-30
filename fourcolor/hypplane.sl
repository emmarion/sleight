; Every plane map of map.sl is a planar bridgeless hypermap, with edge e, face nd and node e . nd^-1.

; c . (b . a) = (c . b) . a.
(def-fns _ $ (erased respects-assoc-inv : (erased (List (Nat)) a b c ba cb ls) (subterm erased (Respects b a ba) r1)
    (erased (Respects cb a ls) r2) (erased (Respects c b cb) r3) -> (erased (Respects c ba ls) r))
  (let-match erased r1 (RespCons _ a1 ba1 j w p r11) ((RespNil _) (let-match erased r2 (RespNil _)) (RespNil c)))
  (let-match erased r2 (RespCons _ _ ls1 _ m q r21))
  (RespCons c ba1 ls1 w m (respects-nth c b cb j w m r3 p q) (respects-assoc-inv a1 b c ba1 cb ls1 r11 r21 r3)))

(def-fns _ $ (erased respects-id-left : (erased (Nat) d) (erased (List (Nat)) ids xs) (erased (Iota d ids) io) (subterm erased (Under xs d) u)
    -> (erased (Respects ids xs xs) r))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (RespNil ids)))
  (RespCons ids xs1 xs1 x x (iota-nth d x ids io lx) (respects-id-left d ids xs1 io u1)))

(def-fns _ $ (erased zip-respects : (erased (List (Nat)) xs ys p) (erased (List (Bond)) g) (subterm erased (Zip xs ys g) z) (erased (Fun p g) f)
    -> (erased (Respects p xs ys) r))
  (let-match erased z (ZipCons xs1 ys1 g1 x y z1) ((ZipNil) (RespNil p)))
  (let-match erased f (FunCons _ _ _ _ px f1))
  (RespCons p xs1 ys1 x y px (zip-respects xs1 ys1 p g1 z1 f1)))

(def-fns _ $ (erased respects-id-right : (erased (Nat) d) (erased (List (Nat)) ids p) (erased (Iota d ids) io) (erased (Length (Nat) p d) lp)
    -> (erased (Respects p ids p) r))
  (let ((erased g) (erased z)) (zip-exists ids p d (iota-length d ids io) lp))
  (zip-respects ids p p g z (graph-fun d p g (MkGraph d p ids g io lp z))))

(def-fns _ $ (erased respects-under : (erased (List (Nat)) lab xs ls) (erased (Nat) d) (subterm erased (Respects lab xs ls) rp)
    (erased (Length (Nat) lab d) ll) -> (erased (Under xs d) r))
  (let-match erased rp (RespCons _ xs1 ls1 j v p rp1) ((RespNil _) (UnderNil d)))
  (UnderCons xs1 j d (nth-lt-length _ lab j d v p ll) (respects-under lab xs1 ls1 d rp1 ll)))

(def-fns _ $ (erased perm-under : (erased (Nat) d) (erased (List (Nat)) p q) (erased (Perm d p q) pm) -> (erased (Under p d) r))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (respects-under q p ids d qp (respects-length-inv p q ids d pq (iota-length d ids io))))

; With e an involution and ndi the inverse of nd, e, e . ndi and nd form a hypermap.
(def-fns _ $ (erased hyper-of : (erased (Nat) d) (erased (List (Nat)) e nd ndi nn) (erased (Perm d e e) pe) (erased (Perm d nd ndi) pn)
    (erased (Respects e ndi nn) rn) -> (erased (Hypermap d e nn nd) h))
  (let-match erased pe (MkPerm _ _ _ ids io le ee _))
  (let-match erased pn (MkPerm _ _ _ ids2 io2 lnd ndind ndndi))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased ue)) (perm-under d e e pe))
  (let ((erased lndi)) (respects-length-inv nd ndi ids d ndndi (iota-length d ids io)))
  (let ((erased lnn)) (respects-length e ndi nn d rn lndi))
  (let ((erased fe) (erased cfe)) (respects-exists nd e d ue lnd))
  (let ((erased ndie)) (respects-assoc-inv e nd ndi fe ids e cfe (respects-id-left d ids e io ue) ndind))
  (let ((erased ndiu)) (perm-under d ndi nd (perm-sym d nd ndi pn)))
  (let ((erased enn)) (respects-assoc-inv ndi e e nn ids ndi rn (respects-id-left d ids ndi io ndiu) ee))
  (MkHypermap d e nn nd ids fe ndi e io cfe (respects-assoc fe ndi e e nn ids d ndie ee rn lnn lndi)
    enn ndndi (respects-assoc nd ndi e ids nn e d ndind (respects-id-right d ids e io le) rn lnn lndi) ee))

; 2 kc + d = ke + kn + kf.
(def-adts $ (Euler : ((Nat) kc d ke kn kf) -> Type)
  enum
  (many MkEuler : (erased (Nat) kc d ke kn kf c2 s s1) (erased (Double kc c2) dc) (erased (Add c2 d s) a) (erased (Add ke kn s1) a1)
      (erased (Add s1 kf s) a2) -> (Euler kc d ke kn kf)))

(def-fns _ $ (erased add-succ2 : (erased (Nat) a b c) (erased (Add a b c) p) -> (erased (Add (Succ a) (Succ b) (Succ (Succ c))) r))
  (AddSucc a (Succ b) (Succ c) (add-succ-right a b c p)))

(def-fns _ $ (erased euler-isolated : (erased (Nat) kc d ke kn kf) (erased (Euler kc d ke kn kf) eu)
    -> (erased (Euler (Succ kc) (Succ (Succ d)) (Succ ke) (Succ kn) (Succ (Succ kf))) r))
  (let-match erased eu (MkEuler _ _ _ _ _ c2 s s1 dc a a1 a2))
  (MkEuler (Succ kc) (Succ (Succ d)) (Succ ke) (Succ kn) (Succ (Succ kf)) (Succ (Succ c2)) (Succ (Succ (Succ (Succ s)))) (Succ (Succ s1))
    (DS kc c2 dc) (add-succ2 (Succ c2) (Succ d) (Succ (Succ s)) (add-succ2 c2 d s a)) (add-succ2 ke kn s1 a1)
    (add-succ2 (Succ s1) (Succ kf) (Succ (Succ s)) (add-succ2 s1 kf s a2))))

(def-fns _ $ (erased euler-pendant : (erased (Nat) kc d ke kn kf) (erased (Euler kc d ke kn kf) eu)
    -> (erased (Euler kc (Succ (Succ d)) (Succ ke) kn (Succ kf)) r))
  (let-match erased eu (MkEuler _ _ _ _ _ c2 s s1 dc a a1 a2))
  (MkEuler kc (Succ (Succ d)) (Succ ke) kn (Succ kf) c2 (Succ (Succ s)) (Succ s1) dc
    (add-succ-right c2 (Succ d) (Succ s) (add-succ-right c2 d s a)) (AddSucc ke kn s1 a1) (add-succ2 s1 kf s a2)))

(def-fns _ $ (erased euler-face : (erased (Nat) kc d ke kn kf) (erased (Euler kc d ke kn kf) eu)
    -> (erased (Euler kc (Succ (Succ d)) (Succ ke) (Succ kn) kf) r))
  (let-match erased eu (MkEuler _ _ _ _ _ c2 s s1 dc a a1 a2))
  (MkEuler kc (Succ (Succ d)) (Succ ke) (Succ kn) kf c2 (Succ (Succ s)) (Succ (Succ s1)) dc
    (add-succ-right c2 (Succ d) (Succ s) (add-succ-right c2 d s a)) (add-succ2 ke kn s1 a1) (AddSucc (Succ s1) kf (Succ s) (AddSucc s1 kf s a2))))

(def-fns _ $ (erased add-succ-left2 : (erased (Nat) a b c) (erased (Add (Succ (Succ a)) b c) p) -> (erased (Add a (Succ (Succ b)) c) r))
  (let-match erased p (AddSucc _ _ c1 p1))
  (let-match erased p1 (AddSucc _ _ c2 p2))
  (add-succ-right a (Succ b) (Succ c2) (add-succ-right a b c2 p2)))

(def-fns _ $ (erased euler-apart : (erased (Nat) kc d ke kn kf) (erased (Euler (Succ kc) d ke (Succ kn) kf) eu)
    -> (erased (Euler kc (Succ (Succ d)) (Succ ke) kn kf) r))
  (let-match erased eu (MkEuler _ _ _ _ _ c2 s s1 dc a a1 a2))
  (let-match erased dc (DS _ c0 dc0))
  (let ((erased s0) (erased e1) (erased a0)) (add-succ-right-inv ke kn s1 a1))
  (let-match erased e1 (Refl _ _))
  (MkEuler kc (Succ (Succ d)) (Succ ke) kn kf c0 s s1 dc0 (add-succ-left2 c0 d s a) (AddSucc ke kn s0 a0) a2))
