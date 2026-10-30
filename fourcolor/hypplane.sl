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

(def-fns _ $ (erased setnth-over : (erased (List (Nat)) xs ys zs) (erased (Nat) i y z) (subterm erased (SetNth (Nat) xs i y ys) p)
    (erased (SetNth (Nat) xs i z zs) q) -> (erased (SetNth (Nat) ys i z zs) r))
  (let-match erased p (SetThere _ x rest i1 _ rest2 p1) ((SetHere _ x _ rest) (let-match erased q (SetHere _ _ _ _)) (SetHere _ y z rest)))
  (let-match erased q (SetThere _ _ _ _ _ rest3 q1))
  (SetThere _ x rest2 i1 z rest3 (setnth-over rest rest2 rest3 i1 y z p1 q1)))

(def-fns _ $ (erased setnth-snoc : (erased (List (Nat)) ys zs ys2 zs2) (erased (Nat) i z a) (subterm erased (SetNth (Nat) ys i z zs) p)
    (erased (Snoc (Nat) ys a ys2) sy) (erased (Snoc (Nat) zs a zs2) sz) -> (erased (SetNth (Nat) ys2 i z zs2) r))
  (match erased p _
    ((SetHere _ x _ rest)
      (let-match erased sy (SnocCons _ _ _ _ rest2 sy1))
      (let-match erased sz (SnocCons _ _ _ _ rest3 sz1))
      (let-match erased (snoc-fn _ rest rest2 rest3 a sy1 sz1) (Refl _ _))
      (SetHere _ x z rest2))
    ((SetThere _ x rest i1 _ rest2 p1)
      (let-match erased sy (SnocCons _ _ _ _ rest3 sy1))
      (let-match erased sz (SnocCons _ _ _ _ rest4 sz1))
      (SetThere _ x rest3 i1 z rest4 (setnth-snoc rest rest2 rest3 rest4 i1 z a p1 sy1 sz1)))))

(def-fns _ $ (erased setnth-reorder : (erased (List (Nat)) xs ys zs ws) (erased (Nat) i j y z) (erased (SetNth (Nat) xs i y ys) p)
    (erased (SetNth (Nat) ys j z zs) q) (erased (SetNth (Nat) xs j z ws) s) (erased (Apart (Nat) Lt i j) ne) -> (erased (SetNth (Nat) ws i y zs) r))
  (let ((erased (List (Nat)) vs) (erased (SetNth (Nat) xs j z vs) s2) (erased (SetNth (Nat) vs i y zs) t)) (match erased ne _
    ((ApLt _ _ _ _ l) (setnth-commute-lt _ xs i j y z ys zs p q l))
    ((ApGt _ _ _ _ l) (setnth-commute-gt _ xs i j y z ys zs p q l))))
  (let-match erased (setnth-fn _ xs j z vs ws s2 s) (Refl _ _))
  t)

; Composing with lab after changing xs at i changes the composite at i.
(def-fns _ $ (erased respects-setnth2 : (erased (List (Nat)) lab xs xs2 ls) (erased (Nat) i y l) (erased (Respects lab xs ls) rp)
    (subterm erased (SetNth (Nat) xs i y xs2) s) (erased (Nth (Nat) lab y l) py)
    -> (erased (List (Nat)) ls2) (erased (SetNth (Nat) ls i l ls2) s2) (erased (Respects lab xs2 ls2) r))
  (let-match erased rp (RespCons _ xs1 ls1 j v p rp1) (absurd (RespNil _) s))
  (let-match erased s (SetThere _ _ _ i1 _ xs3 s1)
    ((SetHere _ _ _ _) (values (Cons _ l ls1) (SetHere _ v l ls1) (RespCons lab xs1 ls1 y l py rp1))))
  (let ((erased ls3) (erased s3) (erased r3)) (respects-setnth2 lab xs1 xs3 ls1 i1 y l rp1 s1 py))
  (values (Cons _ v ls3) (SetThere _ v ls1 i1 l ls3 s3) (RespCons lab xs3 ls3 j v p r3)))

; Composing with lab after an insertion into xs.
(def-fns _ $ (erased respects-insert2 : (erased (List (Nat)) lab xs xs2 ls) (erased (Nat) c x lx d) (erased (Respects lab xs ls) rp)
    (erased (Insert xs c x xs2) ins) (erased (Nth (Nat) lab x lx) px) (erased (Length (Nat) xs d) lxs)
    -> (erased (Nat) lc) (erased (Nth (Nat) ls c lc) pc) (erased (List (Nat)) ls1 ls2) (erased (SetNth (Nat) ls c lx ls1) s1)
    (erased (Snoc (Nat) ls1 lc ls2) s2) (erased (Respects lab xs2 ls2) r))
  (let-match erased ins (MkInsert _ xs1 _ _ _ w pw sx qx))
  (let ((erased lls)) (respects-length lab xs ls d rp lxs))
  (let ((erased lc) (erased pc)) (nth-exists _ ls d c lls (nth-lt-length _ xs c d w pw lxs)))
  (let ((erased ls1) (erased s1) (erased r1)) (respects-setnth2 lab xs xs1 ls c x lx rp sx px))
  (let ((erased ls2) (erased s2)) (snoc-exists _ ls1 lc))
  (values lc pc ls1 ls2 s1 s2 (respects-snoc lab xs1 xs2 ls1 ls2 w lc r1 (respects-nth lab xs ls c w lc rp pw pc) qx s2)))

(def-fns _ $ (erased perm-length : (erased (Nat) d) (erased (List (Nat)) p q) (erased (Perm d p q) pm) -> (erased (Length (Nat) p d) l))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  lp)

(def-fns _ $ (erased graph-exists : (erased (Nat) d) (erased (List (Nat)) p) (erased (Length (Nat) p d) lp)
    -> (erased (List (Bond)) g) (erased (Graph d p g) gr))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased g) (erased z)) (zip-exists ids p d (iota-length d ids io) lp))
  (values g (MkGraph d p ids g io lp z)))

(def-fns _ $ (erased graph-snoc : (erased (Nat) d y) (erased (List (Nat)) p p2) (erased (List (Bond)) g) (erased (Graph d p g) gr)
    (erased (Snoc (Nat) p y p2) s) -> (erased (List (Bond)) g2) (erased (Snoc (Bond) g (MkBond d y) g2) sg) (erased (Graph (Succ d) p2 g2) gr2))
  (let-match erased gr (MkGraph _ _ ids _ io lp z))
  (let ((erased ids2) (erased si)) (snoc-exists _ ids d))
  (let ((erased g2) (erased sg) (erased z2)) (zip-snoc ids ids2 p p2 g d y z si s))
  (values g2 sg (MkGraph (Succ d) p2 ids2 g2 (IotaS d ids ids2 io si) (snoc-length _ p p2 y d s lp) z2)))

; Each bond x-y of g has a labelling constant along nd that tells x from y.
(def-adts $ (Loopless : ((List (Nat)) nd) ((List (Bond)) g) -> Type)
  enum
  (many LoopNil : (erased (List (Nat)) nd) -> (Loopless nd (Nil (Bond))))
  (many LoopCons : (erased (List (Nat)) nd lab) (erased (List (Bond)) g) (erased (Nat) x y) (erased (Separates lab nd x y) s)
      (erased (Loopless nd g) rest) -> (Loopless nd (Cons (Bond) (MkBond x y) g))))

(def-fns _ $ (erased separates-insert : (erased (List (Nat)) lab nd nd2) (erased (Nat) x y a n) (erased (Separates lab nd x y) s)
    (erased (Insert nd a n nd2) ins) (erased (Length (Nat) nd n) ln) -> (erased (List (Nat)) lab2) (erased (Separates lab2 nd2 x y) r))
  (let-match erased s (MkSeparates _ _ _ _ l1 l2 rp p1 p2 ne))
  (let ((erased ll)) (respects-length lab nd lab n rp ln))
  (let-match erased ins (MkInsert _ _ _ _ _ c pc _ _))
  (let ((erased la) (erased pa)) (nth-exists _ lab n a ll (nth-lt-length _ nd a n c pc ln)))
  (let ((erased lab2) (erased sl)) (snoc-exists _ lab la))
  (values lab2 (MkSeparates lab2 nd2 x y l1 l2 (respects-insert lab lab2 nd nd2 a n n la rp ins ll pa sl)
    (snoc-old _ lab lab2 la l1 x sl p1) (snoc-old _ lab lab2 la l2 y sl p2) ne)))

(def-fns _ $ (erased separates-fix : (erased (List (Nat)) lab nd nd2) (erased (Nat) x y n) (erased (Separates lab nd x y) s)
    (erased (Snoc (Nat) nd n nd2) sn) (erased (Length (Nat) nd n) ln) -> (erased (List (Nat)) lab2) (erased (Separates lab2 nd2 x y) r))
  (let-match erased s (MkSeparates _ _ _ _ l1 l2 rp p1 p2 ne))
  (let ((erased ll)) (respects-length lab nd lab n rp ln))
  (let ((erased lab2) (erased sl)) (snoc-exists _ lab (Zero)))
  (values lab2 (MkSeparates lab2 nd2 x y l1 l2 (respects-new lab lab2 nd nd2 n (Zero) rp sn ll sl)
    (snoc-old _ lab lab2 (Zero) l1 x sl p1) (snoc-old _ lab lab2 (Zero) l2 y sl p2) ne)))

(def-fns _ $ (erased loop-insert : (erased (List (Nat)) nd nd2) (erased (List (Bond)) g) (erased (Nat) a n) (subterm erased (Loopless nd g) lo)
    (erased (Insert nd a n nd2) ins) (erased (Length (Nat) nd n) ln) -> (erased (Loopless nd2 g) r))
  (let-match erased lo (LoopCons _ lab g1 x y s lo1) ((LoopNil _) (LoopNil nd2)))
  (let ((erased lab2) (erased s2)) (separates-insert lab nd nd2 x y a n s ins ln))
  (LoopCons nd2 lab2 g1 x y s2 (loop-insert nd nd2 g1 a n lo1 ins ln)))

(def-fns _ $ (erased loop-fix : (erased (List (Nat)) nd nd2) (erased (List (Bond)) g) (erased (Nat) n) (subterm erased (Loopless nd g) lo)
    (erased (Snoc (Nat) nd n nd2) sn) (erased (Length (Nat) nd n) ln) -> (erased (Loopless nd2 g) r))
  (let-match erased lo (LoopCons _ lab g1 x y s lo1) ((LoopNil _) (LoopNil nd2)))
  (let ((erased lab2) (erased s2)) (separates-fix lab nd nd2 x y n s sn ln))
  (LoopCons nd2 lab2 g1 x y s2 (loop-fix nd nd2 g1 n lo1 sn ln)))

(def-fns _ $ (erased loop-snoc : (erased (List (Nat)) nd lab) (erased (List (Bond)) g g2) (erased (Nat) x y) (subterm erased (Loopless nd g) lo)
    (erased (Separates lab nd x y) s) (erased (Snoc (Bond) g (MkBond x y) g2) sg) -> (erased (Loopless nd g2) r))
  (let-match erased sg (SnocCons _ b0 _ g1 g3 sg1) ((SnocNil _ _) (LoopCons nd lab _ x y s (LoopNil nd))))
  (let-match erased lo (LoopCons _ lab1 _ x1 y1 s1 lo1))
  (LoopCons nd lab1 g3 x1 y1 s1 (loop-snoc nd lab g1 g3 x y lo1 s sg1)))

(def-fns _ $ (erased separates-sym : (erased (List (Nat)) lab nd) (erased (Nat) x y) (erased (Separates lab nd x y) s) -> (erased (Separates lab nd y x) r))
  (let-match erased s (MkSeparates _ _ _ _ l1 l2 rp p1 p2 ne))
  (MkSeparates lab nd y x l2 l1 rp p2 p1 (apart-sym l1 l2 ne)))

; The two new bonds of a new edge n-(n+1), told apart by lab.
(def-fns _ $ (erased loop-grow : (erased (List (Nat)) nd lab) (erased (List (Bond)) g g1 g2) (erased (Nat) n) (erased (Loopless nd g) lo)
    (erased (Separates lab nd n (Succ n)) s) (erased (Snoc (Bond) g (MkBond n (Succ n)) g1) s1) (erased (Snoc (Bond) g1 (MkBond (Succ n) n) g2) s2)
    -> (erased (Loopless nd g2) r))
  (loop-snoc nd lab g1 g2 (Succ n) n (loop-snoc nd lab g g1 n (Succ n) lo s s1) (separates-sym lab nd n (Succ n) s) s2))

(def-fns _ $ (erased zeros-resp : (erased (List (Nat)) zs xs) (erased (Nat) n m) (erased (Repeat (Nat) n (Zero) zs) rz) (subterm erased (Under xs n) u)
    (erased (Length (Nat) xs m) lx) -> (erased (List (Nat)) ws) (erased (Repeat (Nat) m (Zero) ws) rw) (erased (Respects zs xs ws) r))
  (let-match erased u (UnderCons xs1 x _ lt u1) ((UnderNil _) (let-match erased lx (LengthNil _)) (values (Nil _) (RepeatNil _ (Zero)) (RespNil zs))))
  (let-match erased lx (LengthCons _ _ _ m1 lx1))
  (let ((erased ws1) (erased rw1) (erased r1)) (zeros-resp zs xs1 n m1 rz u1 lx1))
  (values (Cons _ (Zero) ws1) (RepeatCons _ m1 (Zero) ws1 rw1) (RespCons zs xs1 ws1 x (Zero) (repeat-nth _ n x (Zero) zs rz lt) r1)))

; A labelling with every dart 0, constant along a permutation.
(def-fns _ $ (erased zeros-perm : (erased (Nat) d) (erased (List (Nat)) p q) (erased (Perm d p q) pm)
    -> (erased (List (Nat)) zs) (erased (Respects zs p zs) r) (erased (Length (Nat) zs d) lz) (erased (Repeat (Nat) d (Zero) zs) rz))
  (let ((erased zs) (erased rz)) (repeat-exists _ d (Zero)))
  (let ((erased ws) (erased rw) (erased r)) (zeros-resp zs p d d rz (perm-under d p q pm) (perm-length d p q pm)))
  (let-match erased (repeat-fn _ d (Zero) ws zs rw rz) (Refl _ _))
  (values zs r (repeat-length _ d (Zero) zs rz) rz))

; The classes of the edge and face links of a grown map, from those of the old links and some new bonds ex.
(def-fns _ $ (erased comps-equiv : (erased (Nat) d k) (erased (List (Bond)) ge gnd gc ge2 gnd2 gc2 ex x) (erased (Classes x d k) cs)
    (erased (Cat ex gc x) cx) (erased (Cat ge gnd gc) cg) (erased (Cat ge2 gnd2 gc2) cg2) (erased (Spans ge2 ge) se) (erased (Spans gnd2 gnd) sn)
    (erased (Spans gc2 ex) sx) (erased (Spans x ge2) te) (erased (Spans x gnd2) tn) (erased (Below gc2 d) bg) -> (erased (Classes gc2 d k) r))
  (classes-equiv x gc2 d k cs
    (spans-cat gc2 ex gc x cx sx (spans-cat gc2 ge gnd gc cg (spans-lift-l ge2 gnd2 gc2 ge se cg2) (spans-lift-r ge2 gnd2 gc2 gnd sn cg2)))
    (spans-cat x ge2 gnd2 gc2 cg2 te tn) bg))

(def-fns _ $ (erased spans-old : (erased (List (Bond)) ge gnd gc ex x) (erased (Cat ge gnd gc) cg) (erased (Cat ex gc x) cx)
    -> (erased (Spans x ge) se) (erased (Spans x gnd) sn))
  (values (spans-lift-r ex gc x ge (spans-lift-l ge gnd gc ge (spans-self ge) cg) cx)
    (spans-lift-r ex gc x gnd (spans-lift-r ge gnd gc gnd (spans-self gnd) cg) cx)))

; A face walk of map.sl from a to b is a walk back along e . ndi from b to a.
(def-fns _ $ (erased fr-path : (erased (Nat) d a b) (erased (List (Nat)) e nd ndi nn) (subterm erased (FaceReach e nd a b) fr)
    (erased (Perm d e e) pe) (erased (Perm d nd ndi) pn) (erased (Respects e ndi nn) rn) -> (erased (List (Nat)) xs) (erased (Path nn (Nil (Nat)) b a xs) r))
  (let-match erased fr (FRStep _ _ _ q c _ pq pc fr1) ((FRHere _ _ _) (values (Nil _) (PathHere nn _ a))))
  (let ((erased xs1) (erased w1)) (fr-path d c b e nd ndi nn fr1 pe pn rn))
  (let ((erased lc)) (perm-val d q c nd ndi pn pc))
  (let ((erased lnn)) (respects-length e ndi nn d rn (perm-length d ndi nd (perm-sym d nd ndi pn))))
  (let ((erased w) (erased pw)) (nth-exists _ nn d c lnn lc))
  (let-match erased (nth-fn _ e q w a (respects-nth e ndi nn c q w rn (perm-inv d q c nd ndi pn pc) pw) (perm-inv d a q e e pe pq)) (Refl _ _))
  (let ((erased xs2) (erased sn) (erased w2)) (path-snoc nn _ xs1 b c a w1 pw (NotInNil c)))
  (values xs2 w2))

(def-fns _ $ (erased fr-conn : (erased (Nat) d a b) (erased (List (Nat)) e nd) (erased (List (Bond)) ge gnd gc) (subterm erased (FaceReach e nd a b) fr)
    (erased (Graph d e ge) pe) (erased (Graph d nd gnd) pn) (erased (Cat ge gnd gc) cg) -> (erased (Conn gc a b) r))
  (let-match erased fr (FRStep _ _ _ q c _ pq pc fr1) ((FRHere _ _ _) (ConnHere gc a)))
  (ConnStep gc a q b (adj-cat-l ge gnd gc a q (graph-adj d a q e ge pe pq) cg)
    (ConnStep gc q c b (adj-cat-r ge gnd gc q c (graph-adj d q c nd gnd pn pc) cg) (fr-conn d c b e nd ge gnd gc fr1 pe pn cg))))

(def-fns _ $ (erased path-insert : (erased (List (Nat)) p p2 s xs) (erased (Nat) x y a d) (subterm erased (Path p s x y xs) w)
    (erased (Insert p a d p2) ins) (erased (Length (Nat) p d) lp) -> (erased (List (Nat)) ys) (erased (Path p2 (Nil (Nat)) x y ys) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ px out w1) ((PathHere _ _ _) (values (Nil _) (PathHere p2 _ x))))
  (let ((erased ys1) (erased v1)) (path-insert p p2 s xs1 z y a d w1 ins lp))
  (match erased (nat-eq x a) _
    ((Equal _ _ _)
      (values (Cons _ x (Cons _ d ys1)) (PathStep p2 _ _ x d y (insert-at p p2 x d ins) (NotInNil x)
        (PathStep p2 _ ys1 d z y (insert-new p p2 x d d z ins lp px) (NotInNil d) v1))))
    ((Unequal _ _ _ _ ne) (values (Cons _ x ys1) (PathStep p2 _ ys1 x z y (insert-other p p2 a d x z ins px ne) (NotInNil x) v1)))))

; A labelling constant along e and nd is constant along e . ndi.
(def-fns _ $ (erased const-nn : (erased (List (Nat)) lab e nd ids lab0 nn0 ndi0) (erased (Nat) d) (subterm erased (Respects e ndi0 nn0) rn)
    (erased (Respects nd ndi0 ids) rd) (erased (Respects lab ids lab0) rl) (erased (Respects lab e lab) le) (erased (Respects lab nd lab) ln)
    (erased (Length (Nat) lab d) ll) -> (erased (Respects lab nn0 lab0) r))
  (let-match erased rn (RespCons _ ndi1 nn1 u w p1 rn1) ((RespNil _) (let-match erased rd (RespNil _)) (let-match erased rl (RespNil _)) (RespNil lab)))
  (let-match erased rd (RespCons _ _ ids1 _ i p2 rd1))
  (let-match erased rl (RespCons _ _ lab1 _ l p3 rl1))
  (let ((erased l2) (erased pu)) (nth-exists _ lab d u ll (nth-lt-length _ nd u d i p2 (respects-length-inv lab nd lab d ln ll))))
  (let-match erased (nth-fn _ lab i l2 l (respects-nth lab nd lab u i l2 ln p2 pu) p3) (Refl _ _))
  (RespCons lab nn1 lab1 w l (respects-nth lab e lab u w l le p1 pu) (const-nn lab e nd ids1 lab1 nn1 ndi1 d rn1 rd1 rl1 le ln ll)))

(def-fns _ $ (erased const-cat : (erased (List (Nat)) lab) (erased (List (Bond)) g h gh) (subterm erased (Cat g h gh) c) (erased (Const lab g) cl)
    (erased (Const lab h) ch) -> (erased (Const lab gh) r))
  (let-match erased c (CatCons g1 _ gh1 b c1) ((CatNil _) ch))
  (let-match erased cl (ConstCons _ _ x y l px py cl1))
  (ConstCons lab gh1 x y l px py (const-cat lab g1 h gh1 c1 cl1 ch)))

; What PlaneMap keeps: e an involution, nd a permutation with inverse ndi, nn = e . ndi, the orbit counts of the three,
; the count of classes of the edge and face links, Euler's equation, and every edge link told apart along nd.
(def-adts $ (PlaneInv : ((List (Nat)) e nd) -> Type)
  enum
  (many MkPlaneInv : (erased (List (Nat)) e nd ndi nn) (erased (Nat) d ke kn kf kc) (erased (List (Bond)) ge gnd gc)
      (erased (Perm d e e) pe) (erased (Perm d nd ndi) pn) (erased (Respects e ndi nn) rn)
      (erased (Orbits d e ke) oe) (erased (Orbits d nn kn) on) (erased (Orbits d nd kf) of)
      (erased (Graph d e ge) gre) (erased (Graph d nd gnd) grn) (erased (Cat ge gnd gc) cg) (erased (Classes gc d kc) cc)
      (erased (Euler kc d ke kn kf) eu) (erased (Loopless nd ge) lo) -> (PlaneInv e nd)))

(def-fns _ $ (erased plane-nil : -> (erased (PlaneInv (Nil (Nat)) (Nil (Nat))) r))
  (let ((erased pm)) (MkPerm (Zero) (Nil (Nat)) (Nil (Nat)) (Nil (Nat)) (IotaZ) (LengthNil _) (RespNil _) (RespNil _)))
  (let ((erased gr)) (MkGraph (Zero) (Nil (Nat)) (Nil (Nat)) (Nil (Bond)) (IotaZ) (LengthNil _) (ZipNil)))
  (let ((erased ob)) (MkOrbits (Zero) (Zero) (Nil (Nat)) (Nil (Bond)) gr (classes-nil (Zero))))
  (MkPlaneInv _ _ _ _ (Zero) (Zero) (Zero) (Zero) (Zero) _ _ _ pm pm (RespNil _) ob ob ob gr gr (CatNil _) (classes-nil (Zero))
    (MkEuler (Zero) (Zero) (Zero) (Zero) (Zero) (Zero) (Zero) (Zero) (D0) (AddZero (Zero)) (AddZero (Zero)) (AddZero (Zero)))
    (LoopNil _)))

; The new edge n-(n+1) of a growth: its graph, Euler-free facts about nn's growth, and spans of the edge links.
(def-fns _ $ (erased edge-graphs : (erased (Nat) n) (erased (List (Nat)) e0 e2) (erased (List (Bond)) ge) (erased (Graph n e0 ge) gre)
    (erased (EdgeGrow e0 n e2) gw)
    -> (erased (List (Bond)) geA ge2) (erased (Snoc (Bond) ge (MkBond n (Succ n)) geA) sA) (erased (Snoc (Bond) geA (MkBond (Succ n) n) ge2) s2)
    (erased (Graph (Succ (Succ n)) e2 ge2) gre2) (erased (Spans ge2 ge) old))
  (let-match erased gw (MkEdgeGrow _ e1 _ _ len s1 s2))
  (let ((erased geA) (erased sgA) (erased greA)) (graph-snoc n (Succ n) e0 e1 ge gre s1))
  (let ((erased ge2) (erased sg2) (erased gre2)) (graph-snoc (Succ n) n e1 e2 geA greA s2))
  (values geA ge2 sgA sg2 gre2 (spans-snoc geA ge2 ge _ (spans-snoc ge geA ge _ (spans-self ge) sgA) sg2)))

; Every new edge link is joined in any graph that joins n and n+1 and spans the old ones.
(def-fns _ $ (erased edge-new : (erased (Nat) n) (erased (List (Bond)) x ge geA ge2) (erased (Snoc (Bond) ge (MkBond n (Succ n)) geA) sA)
    (erased (Snoc (Bond) geA (MkBond (Succ n) n) ge2) s2) (erased (Spans x ge) sp) (erased (Conn x n (Succ n)) c) -> (erased (Spans x ge2) r))
  (spans-snoc-inv x geA ge2 (Succ n) n s2 (spans-snoc-inv x ge geA n (Succ n) sA sp c) (conn-sym x n (Succ n) c)))

(def-fns _ $ (erased plane-isolated : (erased (List (Nat)) e0 nd0 e2 nd1 nd2) (erased (Nat) n) (erased (PlaneInv e0 nd0) iv)
    (erased (EdgeGrow e0 n e2) gw) (erased (Snoc (Nat) nd0 n nd1) sn1) (erased (Snoc (Nat) nd1 (Succ n) nd2) sn2) -> (erased (PlaneInv e2 nd2) r))
  (let-match erased iv (MkPlaneInv _ _ ndi nn d ke kn kf kc ge gnd gc pe pn rn oe on of gre grn cg cc eu lo))
  (let-match erased gw (MkEdgeGrow _ e1 _ _ len s1 s2))
  (let-match erased (length-fn _ e0 d n (perm-length d e0 e0 pe) len) (Refl _ _))
  (let ((erased ln)) (perm-length n nd0 ndi pn))
  (let ((erased lnn)) (respects-length e0 ndi nn n rn (perm-length n ndi nd0 (perm-sym n nd0 ndi pn))))
  (let ((erased ndi1) (erased si1)) (snoc-exists _ ndi n))
  (let ((erased ndi2) (erased si2)) (snoc-exists _ ndi1 (Succ n)))
  (let ((erased pn2)) (perm-fix (Succ n) nd1 ndi1 nd2 ndi2 (perm-fix n nd0 ndi nd1 ndi1 pn sn1 si1) sn2 si2))
  (let ((erased pe2)) (perm-grow n e0 e2 pe gw))
  (let ((erased rn1)) (respects-lab e1 e2 ndi nn n (respects-lab e0 e1 ndi nn (Succ n) rn s1) s2))
  (let ((erased nnA) (erased sa)) (snoc-exists _ nn (Succ n)))
  (let ((erased nnB) (erased sb)) (snoc-exists _ nnA n))
  (let ((erased rn2)) (respects-snoc e2 ndi1 ndi2 nnA nnB (Succ n) n
    (respects-snoc e2 ndi ndi1 nn nnA n (Succ n) rn1 (edge-low e0 e2 n gw) si1 sa) (edge-high e0 e2 n gw) si2 sb))
  (let ((erased geA) (erased ge2) (erased sgA) (erased sg2) (erased gre2) (erased olde)) (edge-graphs n e0 e2 ge gre gw))
  (let ((erased gndA) (erased snA) (erased grnA)) (graph-snoc n n nd0 nd1 gnd grn sn1))
  (let ((erased gnd2) (erased snB) (erased grn2)) (graph-snoc (Succ n) (Succ n) nd1 nd2 gndA grnA sn2))
  (let ((erased gc2) (erased cg2)) (cat-exists ge2 gnd2))
  (let ((erased bc)) (classes-below gc n kc cc))
  (let ((erased l0)) (lt-weaken n (Succ n) (lt-succ n)))
  (let ((erased l1)) (lt-succ (Succ n)))
  (let ((erased k1) (erased e1q) (erased csx)) (classes-link-merge gc (Succ (Succ n)) (Succ (Succ kc)) n (Succ n)
    (classes-grow gc (Succ n) (Succ kc) (classes-grow gc n kc cc))
    (shut-sep (Succ (Succ n)) n (Succ n) (Cons _ (Succ n) (Nil _)) gc (below-shut gc (Succ n) (below-succ gc n bc))
      (below-succ gc (Succ n) (below-succ gc n bc)) (NotInCons n (Succ n) _ (ApLt _ _ n (Succ n) (lt-succ n)) (NotInNil n)) (InHere (Succ n) _) l0 l1)
    l0 l1))
  (let-match erased e1q (Refl _ _))
  (let ((erased x)) (Cons (Bond) (MkBond n (Succ n)) gc))
  (let ((erased cx)) (CatCons (Nil (Bond)) gc gc (MkBond n (Succ n)) (CatNil gc)))
  (let ((erased sxe) (erased sxn)) (spans-old ge gnd gc _ x cg cx))
  (let ((erased cxn)) (conn-adj x n (Succ n) (AdjFwd gc n (Succ n))))
  (let ((erased zs) (erased rz) (erased lz) (erased rpz)) (zeros-perm n nd0 ndi pn))
  (let ((erased lab1) (erased sl1)) (snoc-exists _ zs (Zero)))
  (let ((erased lab2) (erased sl2)) (snoc-exists _ lab1 (Succ (Zero))))
  (let ((erased rl2)) (respects-new lab1 lab2 nd1 nd2 (Succ n) (Succ (Zero)) (respects-new zs lab1 nd0 nd1 n (Zero) rz sn1 lz sl1) sn2
    (snoc-length _ zs lab1 (Zero) n sl1 lz) sl2))
  (MkPlaneInv e2 nd2 ndi2 nnB (Succ (Succ n)) (Succ ke) (Succ kn) (Succ (Succ kf)) (Succ kc) ge2 gnd2 gc2 pe2 pn2 rn2
    (orbits-grow n ke e0 e2 oe gw) (orbits-grow n kn nn nnB on (MkEdgeGrow nn nnA nnB n lnn sa sb))
    (orbits-fix (Succ n) (Succ kf) nd1 nd2 (orbits-fix n kf nd0 nd1 of sn1) sn2) gre2 grn2 cg2
    (comps-equiv (Succ (Succ n)) (Succ kc) ge gnd gc ge2 gnd2 gc2 _ x csx cx cg cg2 olde
      (spans-snoc gndA gnd2 gnd _ (spans-snoc gnd gndA gnd _ (spans-self gnd) snA) snB)
      (SpansCons gc2 _ n (Succ n) (conn-adj gc2 n (Succ n) (adj-cat-l ge2 gnd2 gc2 n (Succ n)
        (graph-adj (Succ (Succ n)) n (Succ n) e2 ge2 gre2 (edge-low e0 e2 n gw)) cg2)) (SpansNil gc2))
      (edge-new n x ge geA ge2 sgA sg2 sxe cxn)
      (spans-snoc-inv x gndA gnd2 (Succ n) (Succ n) snB (spans-snoc-inv x gnd gndA n n snA sxn (ConnHere x n)) (ConnHere x (Succ n)))
      (below-cat ge2 gnd2 gc2 (Succ (Succ n)) cg2 (graph-below (Succ (Succ n)) e2 e2 ge2 (graph-fun (Succ (Succ n)) e2 ge2 gre2) pe2)
        (graph-below (Succ (Succ n)) nd2 ndi2 gnd2 (graph-fun (Succ (Succ n)) nd2 gnd2 grn2) pn2)))
    (euler-isolated kc n ke kn kf eu)
    (loop-grow nd2 lab2 ge geA ge2 n (loop-fix nd1 nd2 ge (Succ n) (loop-fix nd0 nd1 ge n lo sn1 ln) sn2 (snoc-length _ nd0 nd1 n n sn1 ln))
      (MkSeparates lab2 nd2 n (Succ n) (Zero) (Succ (Zero)) rl2 (snoc-old _ lab1 lab2 (Succ (Zero)) (Zero) n sl2 (snoc-new _ zs lab1 (Zero) n sl1 lz))
        (snoc-new _ lab1 lab2 (Succ (Zero)) (Succ n) sl2 (snoc-length _ zs lab1 (Zero) n sl1 lz)) (ApLt _ _ (Zero) (Succ (Zero)) (LtZ (Zero))))
      sgA sg2)))
