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
