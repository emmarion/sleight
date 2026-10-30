; Sewing a disk map and a remainder map along their rings into a map that they patch, after sew.v. The disk darts keep their
; numbers, and the remainder darts off the ring follow them. Load after patch.sl.

; x is the image under h1 of a dart moved by p1 to the dart whose image is y, or the same under h2 and p2 from a dart off b2.
(def-adts $ (CMapAt : ((List (Nat)) h1 p1 h2 p2 b2) ((Nat) x y) -> Type)
  enum
  (many CML : (erased (List (Nat)) h1 p1 h2 p2 b2) (erased (Nat) x y x1 y1) (erased (Nth (Nat) h1 x1 x) hx) (erased (Nth (Nat) p1 x1 y1) px)
      (erased (Nth (Nat) h1 y1 y) hy) -> (CMapAt h1 p1 h2 p2 b2 x y))
  (many CMR : (erased (List (Nat)) h1 p1 h2 p2 b2) (erased (Nat) x y x2 y2) (erased (Nth (Nat) h2 x2 x) hx) (erased (NotIn x2 b2) out)
      (erased (Nth (Nat) p2 x2 y2) px) (erased (Nth (Nat) h2 y2 y) hy) -> (CMapAt h1 p1 h2 p2 b2 x y)))

(def-adts $ (CMap : ((List (Nat)) h1 p1 h2 p2 b2 xs ys) -> Type)
  enum
  (many CMNil : (erased (List (Nat)) h1 p1 h2 p2 b2) -> (CMap h1 p1 h2 p2 b2 (Nil (Nat)) (Nil (Nat))))
  (many CMCons : (erased (List (Nat)) h1 p1 h2 p2 b2 xs ys) (erased (Nat) x y) (erased (CMapAt h1 p1 h2 p2 b2 x y) p)
      (erased (CMap h1 p1 h2 p2 b2 xs ys) rest) -> (CMap h1 p1 h2 p2 b2 (Cons (Nat) x xs) (Cons (Nat) y ys))))

; No image under h2 of a dart of xs off b2 is an image under h1.
(def-adts $ (CDisj : ((List (Nat)) h1 h2 b2 xs) -> Type)
  enum
  (many DjNil : (erased (List (Nat)) h1 h2 b2) -> (CDisj h1 h2 b2 (Nil (Nat))))
  (many DjIn : (erased (List (Nat)) h1 h2 b2 xs) (erased (Nat) x) (erased (In x b2) ib) (erased (CDisj h1 h2 b2 xs) rest) -> (CDisj h1 h2 b2 (Cons (Nat) x xs)))
  (many DjOut : (erased (List (Nat)) h1 h2 b2 xs) (erased (Nat) x z) (erased (Nth (Nat) h2 x z) hz) (erased (NotIn z h1) out) (erased (CDisj h1 h2 b2 xs) rest)
      -> (CDisj h1 h2 b2 (Cons (Nat) x xs))))

(def-fns _ $ (erased absurd disj-at : (erased (List (Nat)) h1 h2 b2 xs) (erased (Nat) x x1 x2) (subterm erased (CDisj h1 h2 b2 xs) dj) (erased (In x2 xs) ix)
    (erased (Nth (Nat) h1 x1 x) p1) (erased (Nth (Nat) h2 x2 x) p2) (erased (NotIn x2 b2) out) -> (erased (False) r))
  (match erased dj _
    (absurd (DjNil _ _ _) ix)
    (absurd (DjIn _ _ _ xs1 y ib dj1)
      (match erased ix _
        (absurd (InHere _ _) (apart-irrefl x2 (notin-in x2 x2 b2 out ib)))
        (absurd (InThere _ _ _ ix1) (disj-at h1 h2 b2 xs1 x x1 x2 dj1 ix1 p1 p2 out))))
    (absurd (DjOut _ _ _ xs1 y z hz o dj1)
      (match erased ix _
        (absurd (InHere _ _) (let-match erased (nth-fn _ h2 x2 z x hz p2) (Refl _ _)) (apart-irrefl x (notin-in x x h1 o (nth-in h1 x1 x p1))))
        (absurd (InThere _ _ _ ix1) (disj-at h1 h2 b2 xs1 x x1 x2 dj1 ix1 p1 p2 out))))))

(def-fns _ $ (erased cmap-exists : (erased (Nat) k1 k2) (erased (List (Nat)) h1 p1 q1 h2 p2 q2 b2 xs) (subterm erased (Cover h1 h2 b2 xs) cv)
    (erased (HPerm k1 p1 q1) pm1) (erased (HPerm k2 p2 q2) pm2) (erased (Length (Nat) h1 k1) lh1) (erased (Length (Nat) h2 k2) lh2)
    -> (erased (List (Nat)) ys) (erased (CMap h1 p1 h2 p2 b2 xs ys) r))
  (match erased cv _
    ((CvNil _ _ _) (values (Nil _) (CMNil h1 p1 h2 p2 b2)))
    ((CvL _ _ _ xs1 x x1 px cv1)
      (let ((erased y1) (erased py) (erased ly)) (perm-nth k1 x1 p1 q1 pm1 (nth-lt-length _ h1 x1 k1 x px lh1)))
      (let ((erased y) (erased hy)) (nth-exists _ h1 k1 y1 lh1 ly))
      (let ((erased ys) (erased r)) (cmap-exists k1 k2 h1 p1 q1 h2 p2 q2 b2 xs1 cv1 pm1 pm2 lh1 lh2))
      (values (Cons _ y ys) (CMCons h1 p1 h2 p2 b2 xs1 ys x y (CML h1 p1 h2 p2 b2 x y x1 y1 px py hy) r)))
    ((CvR _ _ _ xs1 x x2 px out cv1)
      (let ((erased y2) (erased py) (erased ly)) (perm-nth k2 x2 p2 q2 pm2 (nth-lt-length _ h2 x2 k2 x px lh2)))
      (let ((erased y) (erased hy)) (nth-exists _ h2 k2 y2 lh2 ly))
      (let ((erased ys) (erased r)) (cmap-exists k1 k2 h1 p1 q1 h2 p2 q2 b2 xs1 cv1 pm1 pm2 lh1 lh2))
      (values (Cons _ y ys) (CMCons h1 p1 h2 p2 b2 xs1 ys x y (CMR h1 p1 h2 p2 b2 x y x2 y2 px out py hy) r)))))

(def-fns _ $ (erased cmap-nth : (erased (List (Nat)) h1 p1 h2 p2 b2 xs ys) (erased (Nat) i x) (subterm erased (CMap h1 p1 h2 p2 b2 xs ys) cm)
    (erased (Nth (Nat) xs i x) p) -> (erased (Nat) y) (erased (Nth (Nat) ys i y) q) (erased (CMapAt h1 p1 h2 p2 b2 x y) ca))
  (let-match erased cm (CMCons _ _ _ _ _ xs1 ys1 x1 y1 ca1 cm1) (absurd (CMNil _ _ _ _ _) p))
  (let-match erased p (NthThere _ _ _ i1 _ pn) ((NthHere _ _ _) (values y1 (NthHere _ y1 ys1) ca1)))
  (let ((erased y) (erased q) (erased ca)) (cmap-nth h1 p1 h2 p2 b2 xs1 ys1 i1 x cm1 pn))
  (values y (NthThere _ y1 ys1 i1 y q) ca))

(def-fns _ $ (erased cmap-length : (erased (List (Nat)) h1 p1 h2 p2 b2 xs ys) (erased (Nat) k) (subterm erased (CMap h1 p1 h2 p2 b2 xs ys) cm)
    (erased (Length (Nat) xs k) l) -> (erased (Length (Nat) ys k) r))
  (let-match erased cm (CMCons _ _ _ _ _ xs1 ys1 x y ca cm1) ((CMNil _ _ _ _ _) (let-match erased l (LengthNil _)) (LengthNil _)))
  (let-match erased l (LengthCons _ _ _ k1 l1))
  (LengthCons _ y ys1 k1 (cmap-length h1 p1 h2 p2 b2 xs1 ys1 k1 cm1 l1)))

; b is a cycle of p, or of its inverse q.
(def-adts $ (CycOf : ((List (Nat)) p q b) -> Type)
  enum
  (many CyP : (erased (List (Nat)) p q b) (erased (NCyc p b) nc) -> (CycOf p q b))
  (many CyQ : (erased (List (Nat)) p q b) (erased (NCyc q b) nc) -> (CycOf p q b)))

(def-fns _ $ (erased cyc-off : (erased (Nat) k x z) (erased (List (Nat)) p q b) (erased (HPerm k p q) pm) (erased (CycOf p q b) cy) (erased (NotIn x b) out)
    (erased (Nth (Nat) p x z) px) -> (erased (NotIn z b) r))
  (let-match erased cy (CyQ _ _ _ nc) ((CyP _ _ _ nc) (off-next k x z p q b pm nc out px)))
  (let-match erased (in-dec z b) (OrR _ _ oz)
    (absurd (OrL _ _ iz) (apart-irrefl x (notin-in x x b out (ncyc-next q b z x nc iz (perm-inv k x z p q pm px))))))
  oz)

; The map ys sends back what the map xs to zs sends, for q1 and q2 inverse to p1 and p2: zs . ys = xs.
(def-fns _ $ (erased cmap-inv : (erased (Nat) d k1 k2) (erased (List (Nat)) h1 p1 q1 h2 p2 q2 b2 ids id1 id2 xs ys zs)
    (subterm erased (CMap h1 p1 h2 p2 b2 xs ys) cp) (erased (CMap h1 q1 h2 q2 b2 ids zs) cq) (erased (Iota d ids) io)
    (erased (HPerm k1 p1 q1) pm1) (erased (Iota k1 id1) io1) (erased (Respects q1 p1 id1) qp1) (erased (HPerm k2 p2 q2) pm2) (erased (Iota k2 id2) io2)
    (erased (Respects q2 p2 id2) qp2) (erased (CycOf p2 q2 b2) cy) (erased (CDisj h1 h2 b2 id2) dj) (erased (Distinct h1) dh1) (erased (Distinct h2) dh2)
    (erased (Length (Nat) h1 k1) lh1) (erased (Length (Nat) h2 k2) lh2) (erased (Under h1 d) uh1) (erased (Under h2 d) uh2)
    -> (erased (Respects zs ys xs) r))
  (let-match erased cp (CMCons _ _ _ _ _ xs1 ys1 x y ca cp1) ((CMNil _ _ _ _ _) (RespNil zs)))
  (let ((erased rest)) (cmap-inv d k1 k2 h1 p1 q1 h2 p2 q2 b2 ids id1 id2 xs1 ys1 zs cp1 cq io pm1 io1 qp1 pm2 io2 qp2 cy dj dh1 dh2 lh1 lh2 uh1 uh2))
  (match erased ca _
    ((CML _ _ _ _ _ _ _ x1 y1 hx px hy)
      (let ((erased z) (erased pz) (erased cz)) (cmap-nth h1 q1 h2 q2 b2 ids zs y y cq (iota-nth d y ids io (under-nth h1 y1 y d uh1 hy))))
      (let ((erased ly1)) (nth-lt-length _ h1 y1 k1 y hy lh1))
      (let-match erased cz (CML _ _ _ _ _ _ _ y3 z1 hy3 qy hz)
        (absurd (CMR _ _ _ _ _ _ _ y2 z2 hy2 out2 qy hz)
          (disj-at h1 h2 b2 id2 y y1 y2 dj (iota-in k2 y2 id2 io2 (nth-lt-length _ h2 y2 k2 y hy2 lh2)) hy hy2 out2)))
      (let-match erased (distinct-nth h1 y3 y1 y dh1 hy3 hy) (Refl _ _))
      (let-match erased (nth-fn _ q1 y1 z1 x1 qy
        (respects-nth q1 p1 id1 x1 y1 x1 qp1 px (iota-nth k1 x1 id1 io1 (nth-lt-length _ h1 x1 k1 x hx lh1)))) (Refl _ _))
      (let-match erased (nth-fn _ h1 x1 z x hz hx) (Refl _ _))
      (RespCons zs ys1 xs1 y x pz rest))
    ((CMR _ _ _ _ _ _ _ x2 y2 hx out px hy)
      (let ((erased oy)) (cyc-off k2 x2 y2 p2 q2 b2 pm2 cy out px))
      (let ((erased z) (erased pz) (erased cz)) (cmap-nth h1 q1 h2 q2 b2 ids zs y y cq (iota-nth d y ids io (under-nth h2 y2 y d uh2 hy))))
      (let-match erased cz (CMR _ _ _ _ _ _ _ y3 z2 hy3 out3 qy hz)
        (absurd (CML _ _ _ _ _ _ _ y1 z1 hy1 qy hz)
          (disj-at h1 h2 b2 id2 y y1 y2 dj (iota-in k2 y2 id2 io2 (nth-lt-length _ h2 y2 k2 y hy lh2)) hy1 hy oy)))
      (let-match erased (distinct-nth h2 y3 y2 y dh2 hy3 hy) (Refl _ _))
      (let-match erased (nth-fn _ q2 y2 z2 x2 qy
        (respects-nth q2 p2 id2 x2 y2 x2 qp2 px (iota-nth k2 x2 id2 io2 (nth-lt-length _ h2 x2 k2 x hx lh2)))) (Refl _ _))
      (let-match erased (nth-fn _ h2 x2 z x hz hx) (Refl _ _))
      (RespCons zs ys1 xs1 y x pz rest))))

; The map built from p1 and p2 extends p1 along h1 ...
(def-fns _ $ (erased cmap-morph1 : (erased (Nat) d k1 k2) (erased (List (Nat)) h1 p1 q1 h2 p2 b2 ids id2 ps m) (erased (CMap h1 p1 h2 p2 b2 ids ps) cm)
    (erased (Iota d ids) io) (erased (HPerm k1 p1 q1) pm1) (erased (CDisj h1 h2 b2 id2) dj) (erased (Iota k2 id2) io2) (erased (Distinct h1) dh1)
    (erased (Length (Nat) h1 k1) lh1) (erased (Length (Nat) h2 k2) lh2) (erased (Under h1 d) uh1) (subterm erased (Under m k1) u)
    -> (erased (MorphOff h1 p1 ps (Nil (Nat)) m) r))
  (let-match erased u (UnderCons m1 x1 _ lx1 u1) ((UnderNil _) (MONil h1 p1 ps (Nil _))))
  (let ((erased x) (erased hx)) (nth-exists _ h1 k1 x1 lh1 lx1))
  (let ((erased y1) (erased py1) (erased ly1)) (perm-nth k1 x1 p1 q1 pm1 lx1))
  (let ((erased y) (erased hy)) (nth-exists _ h1 k1 y1 lh1 ly1))
  (let ((erased z) (erased pz) (erased ca)) (cmap-nth h1 p1 h2 p2 b2 ids ps x x cm (iota-nth d x ids io (under-nth h1 x1 x d uh1 hx))))
  (let-match erased ca (CML _ _ _ _ _ _ _ x3 y3 hx3 px3 hy3)
    (absurd (CMR _ _ _ _ _ _ _ x2 y2 hx2 out2 px2 hy2)
      (disj-at h1 h2 b2 id2 x x1 x2 dj (iota-in k2 x2 id2 io2 (nth-lt-length _ h2 x2 k2 x hx2 lh2)) hx hx2 out2)))
  (let-match erased (distinct-nth h1 x3 x1 x dh1 hx3 hx) (Refl _ _))
  (let-match erased (nth-fn _ p1 x1 y3 y1 px3 py1) (Refl _ _))
  (let-match erased (nth-fn _ h1 y1 z y hy3 hy) (Refl _ _))
  (MOAt h1 p1 ps (Nil _) m1 x1 y1 x y py1 hx hy pz (cmap-morph1 d k1 k2 h1 p1 q1 h2 p2 b2 ids id2 ps m1 cm io pm1 dj io2 dh1 lh1 lh2 uh1 u1)))

; ... and p2 along h2 off b2.
(def-fns _ $ (erased cmap-morph2 : (erased (Nat) d k1 k2) (erased (List (Nat)) h1 p1 h2 p2 q2 b2 ids id2 ps m) (erased (CMap h1 p1 h2 p2 b2 ids ps) cm)
    (erased (Iota d ids) io) (erased (HPerm k2 p2 q2) pm2) (erased (CDisj h1 h2 b2 id2) dj) (erased (Iota k2 id2) io2) (erased (Distinct h2) dh2)
    (erased (Length (Nat) h2 k2) lh2) (erased (Under h2 d) uh2) (subterm erased (Under m k2) u)
    -> (erased (MorphOff h2 p2 ps b2 m) r))
  (let-match erased u (UnderCons m1 x2 _ lx2 u1) ((UnderNil _) (MONil h2 p2 ps b2)))
  (let ((erased rest)) (cmap-morph2 d k1 k2 h1 p1 h2 p2 q2 b2 ids id2 ps m1 cm io pm2 dj io2 dh2 lh2 uh2 u1))
  (let-match erased (in-dec x2 b2) (OrR _ _ out) ((OrL _ _ ib) (MOSkip h2 p2 ps b2 m1 x2 ib rest)))
  (let ((erased x) (erased hx)) (nth-exists _ h2 k2 x2 lh2 lx2))
  (let ((erased y2) (erased py2) (erased ly2)) (perm-nth k2 x2 p2 q2 pm2 lx2))
  (let ((erased y) (erased hy)) (nth-exists _ h2 k2 y2 lh2 ly2))
  (let ((erased z) (erased pz) (erased ca)) (cmap-nth h1 p1 h2 p2 b2 ids ps x x cm (iota-nth d x ids io (under-nth h2 x2 x d uh2 hx))))
  (let-match erased ca (CMR _ _ _ _ _ _ _ x3 y3 hx3 out3 px3 hy3)
    (absurd (CML _ _ _ _ _ _ _ x1 y1 hx1 px1 hy1) (disj-at h1 h2 b2 id2 x x1 x2 dj (iota-in k2 x2 id2 io2 lx2) hx1 hx out)))
  (let-match erased (distinct-nth h2 x3 x2 x dh2 hx3 hx) (Refl _ _))
  (let-match erased (nth-fn _ p2 x2 y3 y2 px3 py2) (Refl _ _))
  (let-match erased (nth-fn _ h2 y2 z y hy3 hy) (Refl _ _))
  (MOAt h2 p2 ps b2 m1 x2 y2 x y py2 hx hy pz rest))

; A permutation of the whole map, h1 a morphism from p1 to it and h2 one from p2 off its cycle b2, when every dart is an image
; under h1 or under h2 off b2, and not both.
(def-fns _ $ (erased cmap-perm : (erased (Nat) d k1 k2) (erased (List (Nat)) h1 p1 q1 h2 p2 q2 b2 ids id1 id2) (erased (Cover h1 h2 b2 ids) cv)
    (erased (HPerm k1 p1 q1) pm1) (erased (HPerm k2 p2 q2) pm2) (erased (NCyc p2 b2) nc) (erased (CDisj h1 h2 b2 id2) dj) (erased (Iota d ids) io)
    (erased (Iota k1 id1) io1) (erased (Iota k2 id2) io2) (erased (Distinct h1) dh1) (erased (Distinct h2) dh2) (erased (Length (Nat) h1 k1) lh1)
    (erased (Length (Nat) h2 k2) lh2) (erased (Under h1 d) uh1) (erased (Under h2 d) uh2)
    -> (erased (List (Nat)) ps qs) (erased (HPerm d ps qs) pm) (erased (MorphOff h1 p1 ps (Nil (Nat)) id1) mo1) (erased (MorphOff h2 p2 ps b2 id2) mo2))
  (let ((erased ps) (erased cp)) (cmap-exists k1 k2 h1 p1 q1 h2 p2 q2 b2 ids cv pm1 pm2 lh1 lh2))
  (let ((erased qs) (erased cq)) (cmap-exists k1 k2 h1 q1 p1 h2 q2 p2 b2 ids cv (perm-sym k1 p1 q1 pm1) (perm-sym k2 p2 q2 pm2) lh1 lh2))
  (let ((erased pm1b)) pm1)
  (let-match erased pm1b (HMkPerm _ _ _ i1 j1 l1 qp1 pq1))
  (let-match erased (iota-fn k1 id1 i1 io1 j1) (Refl _ _))
  (let ((erased pm2b)) pm2)
  (let-match erased pm2b (HMkPerm _ _ _ i2 j2 l2 qp2 pq2))
  (let-match erased (iota-fn k2 id2 i2 io2 j2) (Refl _ _))
  (values ps qs
    (HMkPerm d ps qs ids io (cmap-length h1 p1 h2 p2 b2 ids ps d cp (iota-length d ids io))
      (cmap-inv d k1 k2 h1 p1 q1 h2 p2 q2 b2 ids id1 id2 ids ps qs cp cq io pm1 io1 qp1 pm2 io2 qp2 (CyP p2 q2 b2 nc) dj dh1 dh2 lh1 lh2 uh1 uh2)
      (cmap-inv d k1 k2 h1 q1 p1 h2 q2 p2 b2 ids id1 id2 ids qs ps cq cp io (perm-sym k1 p1 q1 pm1) io1 pq1 (perm-sym k2 p2 q2 pm2) io2 pq2
        (CyQ q2 p2 b2 nc) dj dh1 dh2 lh1 lh2 uh1 uh2))
    (cmap-morph1 d k1 k2 h1 p1 q1 h2 p2 b2 ids id2 ps id1 cp io pm1 dj io2 dh1 lh1 lh2 uh1 (perm-under k1 id1 id1 (perm-id k1 id1 io1)))
    (cmap-morph2 d k1 k2 h1 p1 h2 p2 q2 b2 ids id2 ps id2 cp io pm2 dj io2 dh2 lh2 uh2 (perm-under k2 id2 id2 (perm-id k2 id2 io2)))))

(def-fns _ $ (erased in2-in-left : (erased (List (Nat)) xs ys) (erased (Nat) x y) (subterm erased (In2 xs ys x y) i) -> (erased (In x xs) r))
  (match erased i _ ((I2Here _ _ xs1 _) (InHere x xs1)) ((I2There a _ _ _ xs1 ys1 i1) (InThere x a xs1 (in2-in-left xs1 ys1 x y i1)))))

(def-fns _ $ (erased in2-sym : (erased (List (Nat)) xs ys) (erased (Nat) x y) (subterm erased (In2 xs ys x y) i) -> (erased (In2 ys xs y x) r))
  (match erased i _ ((I2Here _ _ xs1 ys1) (I2Here y x ys1 xs1)) ((I2There a b _ _ xs1 ys1 i1) (I2There b a y x ys1 xs1 (in2-sym xs1 ys1 x y i1)))))

(def-fns _ $ (erased nth2-in2 : (erased (List (Nat)) xs ys) (erased (Nat) j x y) (subterm erased (Nth (Nat) xs j x) p) (erased (Nth (Nat) ys j y) q)
    -> (erased (In2 xs ys x y) r))
  (let-match erased p (NthThere _ a xs1 j1 _ p1) ((NthHere _ _ xs1) (let-match erased q (NthHere _ _ ys1)) (I2Here x y xs1 ys1)))
  (let-match erased q (NthThere _ b ys1 _ _ q1))
  (I2There a b x y xs1 ys1 (nth2-in2 xs1 ys1 j1 x y p1 q1)))

(def-fns _ $ (erased in2-fn : (erased (List (Nat)) xs ys) (erased (Nat) x v w) (erased (Distinct xs) dx) (subterm erased (In2 xs ys x v) p) (erased (In2 xs ys x w) q)
    -> (erased (Eq (Nat) v w) e))
  (let-match erased dx (DistCons _ xs1 out dx1) (absurd (DistNil) p))
  (match erased p _
    ((I2Here _ _ _ ys1)
      (let-match erased q (I2Here _ _ _ _) (absurd (I2There _ _ _ _ _ _ q1) (apart-irrefl x (notin-in x x xs1 out (in2-in-left xs1 ys1 x w q1)))))
      (Refl _ v))
    ((I2There a b _ _ _ ys1 p1)
      (let-match erased q (I2There _ _ _ _ _ _ q1) (absurd (I2Here _ _ _ _) (apart-irrefl x (notin-in x x xs1 out (in2-in-left xs1 ys1 x v p1)))))
      (in2-fn xs1 ys1 x v w dx1 p1 q1))))

(def-fns _ $ (erased in2-exists : (erased (List (Nat)) xs ys) (erased (Nat) x n) (subterm erased (In x xs) ix) (erased (Length (Nat) xs n) lx) (erased (Length (Nat) ys n) ly)
    -> (erased (Nat) y) (erased (In2 xs ys x y) r))
  (let ((erased j) (erased pj)) (in-nth x xs ix))
  (let ((erased y) (erased py)) (nth-exists _ ys n j ly (nth-lt-length _ xs j n x pj lx)))
  (values y (nth2-in2 xs ys j x y pj py)))

(def-fns _ $ (erased under-notin : (erased (List (Nat)) xs) (erased (Nat) b u) (subterm erased (Under xs b) ux) (erased (Lt b (Succ u)) l) -> (erased (NotIn u xs) r))
  (let-match erased ux (UnderCons xs1 y _ ly u1) ((UnderNil _) (NotInNil u)))
  (NotInCons u y xs1 (ApGt (Nat) Lt u y (lt-le-trans y b u ly l)) (under-notin xs1 b u u1 l)))

; v is the image of x: the dart at the position of x in rbd if x is on br, and otherwise a new dart from c up to c2.
(def-adts $ (HrAt : ((List (Nat)) br rbd) ((Nat) c c2 x v) -> Type)
  enum
  (many HARing : (erased (List (Nat)) br rbd) (erased (Nat) c c2 x v) (erased (In2 br rbd x v) i) -> (HrAt br rbd c c2 x v))
  (many HANew : (erased (List (Nat)) br rbd) (erased (Nat) c c2 x v) (erased (NotIn x br) out) (erased (Lt c (Succ v)) l1) (erased (Lt v c2) l2)
      -> (HrAt br rbd c c2 x v)))

; hs numbers the darts of xs off br from c up to c2, in order, and sends those on br along rbd.
(def-adts $ (HrB : ((List (Nat)) br rbd) ((Nat) c) ((List (Nat)) xs hs) ((Nat) c2) -> Type)
  enum
  (many HBNil : (erased (List (Nat)) br rbd) (erased (Nat) c) -> (HrB br rbd c (Nil (Nat)) (Nil (Nat)) c))
  (many HBRing : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 x v) (erased (In2 br rbd x v) i) (erased (HrB br rbd c xs hs c2) rest)
      -> (HrB br rbd c (Cons (Nat) x xs) (Cons (Nat) v hs) c2))
  (many HBNew : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 x) (erased (NotIn x br) out) (erased (HrB br rbd (Succ c) xs hs c2) rest)
      -> (HrB br rbd c (Cons (Nat) x xs) (Cons (Nat) c hs) c2)))

(def-fns _ $ (erased hrb-exists : (erased (List (Nat)) br rbd) (erased (Nat) c k) (subterm erased (List (Nat)) xs) (erased (Length (Nat) br k) lb)
    (erased (Length (Nat) rbd k) lr) -> (erased (List (Nat)) hs) (erased (Nat) c2) (erased (HrB br rbd c xs hs c2) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Nil _) c (HBNil br rbd c))))
  (match erased (in-dec x br) _
    ((OrL _ _ ix)
      (let ((erased v) (erased i)) (in2-exists br rbd x k ix lb lr))
      (let ((erased hs) (erased c2) (erased r)) (hrb-exists br rbd c k xs1 lb lr))
      (values (Cons _ v hs) c2 (HBRing br rbd xs1 hs c c2 x v i r)))
    ((OrR _ _ out)
      (let ((erased hs) (erased c2) (erased r)) (hrb-exists br rbd (Succ c) k xs1 lb lr))
      (values (Cons _ c hs) c2 (HBNew br rbd xs1 hs c c2 x out r)))))

(def-fns _ $ (erased hrb-le : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2) (subterm erased (HrB br rbd c xs hs c2) hb) -> (erased (Lt c (Succ c2)) r))
  (match erased hb _
    ((HBNil _ _ _) (lt-succ c))
    ((HBRing _ _ xs1 hs1 _ _ x v i rest) (hrb-le br rbd xs1 hs1 c c2 rest))
    ((HBNew _ _ xs1 hs1 _ _ x out rest) (lt-succ-left c (Succ c2) (hrb-le br rbd xs1 hs1 (Succ c) c2 rest)))))

(def-fns _ $ (erased hrb-length : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 n) (subterm erased (HrB br rbd c xs hs c2) hb) (erased (Length (Nat) xs n) l)
    -> (erased (Length (Nat) hs n) r))
  (match erased hb _
    ((HBNil _ _ _) (let-match erased l (LengthNil _)) (LengthNil _))
    ((HBRing _ _ xs1 hs1 _ _ x v i rest) (let-match erased l (LengthCons _ _ _ n1 l1)) (LengthCons _ v hs1 n1 (hrb-length br rbd xs1 hs1 c c2 n1 rest l1)))
    ((HBNew _ _ xs1 hs1 _ _ x out rest) (let-match erased l (LengthCons _ _ _ n1 l1)) (LengthCons _ c hs1 n1 (hrb-length br rbd xs1 hs1 (Succ c) c2 n1 rest l1)))))

(def-fns _ $ (erased hrb-nth : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 i x) (subterm erased (HrB br rbd c xs hs c2) hb) (erased (Nth (Nat) xs i x) p)
    -> (erased (Nat) v) (erased (Nth (Nat) hs i v) q) (erased (HrAt br rbd c c2 x v) ha))
  (match erased hb _
    (absurd (HBNil _ _ _) p)
    ((HBRing _ _ xs1 hs1 _ _ y v i1 rest)
      (let-match erased p (NthThere _ _ _ j _ p1) ((NthHere _ _ _) (values v (NthHere _ v hs1) (HARing br rbd c c2 x v i1))))
      (let ((erased w) (erased q) (erased ha)) (hrb-nth br rbd xs1 hs1 c c2 j x rest p1))
      (values w (NthThere _ v hs1 j w q) ha))
    ((HBNew _ _ xs1 hs1 _ _ y out rest)
      (let-match erased p (NthThere _ _ _ j _ p1)
        ((NthHere _ _ _) (values c (NthHere _ c hs1) (HANew br rbd c c2 x c out (lt-succ c) (lt-pred c c2 (hrb-le br rbd xs1 hs1 (Succ c) c2 rest))))))
      (let ((erased w) (erased q) (erased ha)) (hrb-nth br rbd xs1 hs1 (Succ c) c2 j x rest p1))
      (values w (NthThere _ c hs1 j w q)
        (match erased ha _
          ((HARing _ _ _ _ _ _ i2) (HARing br rbd c c2 x w i2))
          ((HANew _ _ _ _ _ _ o l1 l2) (HANew br rbd c c2 x w o (lt-succ-left c (Succ w) l1) l2)))))))

; Every number from c up to c2 is a new dart.
(def-fns _ $ (erased hrb-hit : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 v) (subterm erased (HrB br rbd c xs hs c2) hb) (erased (Lt c (Succ v)) l1)
    (erased (Lt v c2) l2) -> (erased (In v hs) r))
  (match erased hb _
    (absurd (HBNil _ _ _) (lt-irrefl v (lt-le-trans v c v l2 l1)))
    ((HBRing _ _ xs1 hs1 _ _ y w i rest) (InThere v w hs1 (hrb-hit br rbd xs1 hs1 c c2 v rest l1 l2)))
    ((HBNew _ _ xs1 hs1 _ _ y out rest)
      (let-match erased (nat-eq v c) (Unequal _ _ _ _ ne) ((Equal _ _ _) (InHere v hs1)))
      (let-match erased ne (ApGt _ _ _ _ lt) (absurd (ApLt _ _ _ _ gt) (lt-irrefl v (lt-le-trans v c v gt l1))))
      (InThere v c hs1 (hrb-hit br rbd xs1 hs1 (Succ c) c2 v rest (LtS c v lt) l2)))))

; u is off rbd, or the image under rbd of a dart off xs.
(def-adts $ (RingAvoid : ((List (Nat)) br rbd xs) ((Nat) u) -> Type)
  enum
  (many RAOff : (erased (List (Nat)) br rbd xs) (erased (Nat) u) (erased (NotIn u rbd) o) -> (RingAvoid br rbd xs u))
  (many RAAt : (erased (List (Nat)) br rbd xs) (erased (Nat) u x) (erased (In2 br rbd x u) i) (erased (NotIn x xs) o) -> (RingAvoid br rbd xs u)))

(def-fns _ $ (erased hrb-notin : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 u) (subterm erased (HrB br rbd c xs hs c2) hb) (erased (Lt u c) lu)
    (erased (RingAvoid br rbd xs u) ra) (erased (Distinct rbd) dr) -> (erased (NotIn u hs) r))
  (match erased hb _
    ((HBNil _ _ _) (NotInNil u))
    ((HBRing _ _ xs1 hs1 _ _ x v i rest)
      (let-match erased (nat-eq u v) (Unequal _ _ _ _ ne)
        (absurd (Equal _ _ _)
          (match erased ra _
            (absurd (RAOff _ _ _ _ o) (apart-irrefl u (notin-in u u rbd o (in2-in-left rbd br u x (in2-sym br rbd x u i)))))
            (absurd (RAAt _ _ _ _ x0 i0 o)
              (let-match erased (in2-fn rbd br u x0 x dr (in2-sym br rbd x0 u i0) (in2-sym br rbd x u i)) (Refl _ _))
              (apart-irrefl x0 (notin-in x0 x0 (Cons _ x xs1) o (InHere x0 xs1)))))))
      (NotInCons u v hs1 ne (hrb-notin br rbd xs1 hs1 c c2 u rest lu
        (match erased ra _
          ((RAOff _ _ _ _ o) (RAOff br rbd xs1 u o))
          ((RAAt _ _ _ _ x0 i0 o) (let-match erased o (NotInCons _ _ _ _ o1)) (RAAt br rbd xs1 u x0 i0 o1)))
        dr)))
    ((HBNew _ _ xs1 hs1 _ _ x out rest)
      (NotInCons u c hs1 (ApLt (Nat) Lt u c lu) (hrb-notin br rbd xs1 hs1 (Succ c) c2 u rest (lt-trans u c (Succ c) lu (lt-succ c))
        (match erased ra _
          ((RAOff _ _ _ _ o) (RAOff br rbd xs1 u o))
          ((RAAt _ _ _ _ x0 i0 o) (let-match erased o (NotInCons _ _ _ _ o1)) (RAAt br rbd xs1 u x0 i0 o1)))
        dr)))))

(def-fns _ $ (erased hrb-distinct : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 dd) (subterm erased (HrB br rbd c xs hs c2) hb) (erased (Distinct xs) dx)
    (erased (Under rbd dd) ur) (erased (Lt dd (Succ c)) ldc) (erased (Distinct rbd) dr) -> (erased (Distinct hs) r))
  (match erased hb _
    ((HBNil _ _ _) (DistNil))
    ((HBRing _ _ xs1 hs1 _ _ x v i rest)
      (let-match erased dx (DistCons _ _ ox dx1))
      (let ((erased lv)) (under-in rbd v dd ur (in2-in-left rbd br v x (in2-sym br rbd x v i))))
      (DistCons v hs1 (hrb-notin br rbd xs1 hs1 c c2 v rest (lt-le-trans v dd c lv ldc) (RAAt br rbd xs1 v x i ox) dr)
        (hrb-distinct br rbd xs1 hs1 c c2 dd rest dx1 ur ldc dr)))
    ((HBNew _ _ xs1 hs1 _ _ x out rest)
      (let-match erased dx (DistCons _ _ ox dx1))
      (DistCons c hs1 (hrb-notin br rbd xs1 hs1 (Succ c) c2 c rest (lt-succ c) (RAOff br rbd xs1 c (under-notin rbd dd c ur ldc)) dr)
        (hrb-distinct br rbd xs1 hs1 (Succ c) c2 dd rest dx1 ur (lt-trans dd (Succ c) (Succ (Succ c)) ldc (lt-succ (Succ c))) dr)))))

(def-fns _ $ (erased hrb-under : (erased (List (Nat)) br rbd xs hs) (erased (Nat) c c2 dd) (subterm erased (HrB br rbd c xs hs c2) hb) (erased (Under rbd dd) ur)
    (erased (Lt dd (Succ c)) ldc) -> (erased (Under hs c2) r))
  (match erased hb _
    ((HBNil _ _ _) (UnderNil c2))
    ((HBRing _ _ xs1 hs1 _ _ x v i rest)
      (UnderCons hs1 v c2 (lt-le-trans v dd c2 (under-in rbd v dd ur (in2-in-left rbd br v x (in2-sym br rbd x v i)))
          (le-trans dd c c2 ldc (hrb-le br rbd xs1 hs1 c c2 rest)))
        (hrb-under br rbd xs1 hs1 c c2 dd rest ur ldc)))
    ((HBNew _ _ xs1 hs1 _ _ x out rest)
      (UnderCons hs1 c c2 (lt-pred c c2 (hrb-le br rbd xs1 hs1 (Succ c) c2 rest))
        (hrb-under br rbd xs1 hs1 (Succ c) c2 dd rest ur (lt-trans dd (Succ c) (Succ (Succ c)) ldc (lt-succ (Succ c))))))))

; Each pair at one position of R and S is a pair at one position of A and B.
(def-adts $ (Sub2 : ((List (Nat)) A B R S) -> Type)
  enum
  (many S2Nil : (erased (List (Nat)) A B) -> (Sub2 A B (Nil (Nat)) (Nil (Nat))))
  (many S2Cons : (erased (List (Nat)) A B R S) (erased (Nat) x y) (erased (In2 A B x y) i) (erased (Sub2 A B R S) rest)
      -> (Sub2 A B (Cons (Nat) x R) (Cons (Nat) y S))))

(def-fns _ $ (erased sub2-lift : (erased (List (Nat)) A B R S) (erased (Nat) a b) (subterm erased (Sub2 A B R S) s) -> (erased (Sub2 (Cons (Nat) a A) (Cons (Nat) b B) R S) r))
  (let-match erased s (S2Cons _ _ R1 S1 x y i s1) ((S2Nil _ _) (S2Nil (Cons _ a A) (Cons _ b B))))
  (S2Cons (Cons _ a A) (Cons _ b B) R1 S1 x y (I2There a b x y A B i) (sub2-lift A B R1 S1 a b s1)))

(def-fns _ $ (erased sub2-self : (erased (List (Nat)) A B) (erased (Nat) n) (subterm erased (Length (Nat) A n) la) (erased (Length (Nat) B n) lb) -> (erased (Sub2 A B A B) r))
  (let-match erased la (LengthCons _ a A1 n1 la1) ((LengthNil _) (let-match erased lb (LengthNil _)) (S2Nil (Nil _) (Nil _))))
  (let-match erased lb (LengthCons _ b B1 _ lb1))
  (S2Cons A B A1 B1 a b (I2Here a b A1 B1) (sub2-lift A1 B1 A1 B1 a b (sub2-self A1 B1 n1 la1 lb1))))

; hs sends br along rbd.
(def-fns _ $ (erased hrb-resp : (erased (List (Nat)) br rbd idr hs R S) (erased (Nat) c c2 dr) (subterm erased (Sub2 br rbd R S) s) (erased (HrB br rbd c idr hs c2) hb)
    (erased (Iota dr idr) io) (erased (Under br dr) ub) (erased (Distinct br) db) -> (erased (Respects hs R S) r))
  (let-match erased s (S2Cons _ _ R1 S1 x v i s1) ((S2Nil _ _) (RespNil hs)))
  (let ((erased ix)) (in2-in-left br rbd x v i))
  (let ((erased w) (erased q) (erased ha)) (hrb-nth br rbd idr hs c c2 x x hb (iota-nth dr x idr io (under-in br x dr ub ix))))
  (let-match erased ha (HARing _ _ _ _ _ _ i2) (absurd (HANew _ _ _ _ _ _ out l1 l2) (apart-irrefl x (notin-in x x br out ix))))
  (let-match erased (in2-fn br rbd x w v db i2 i) (Refl _ _))
  (RespCons hs R1 S1 x w q (hrb-resp br rbd idr hs R1 S1 c c2 dr s1 hb io ub db)))
