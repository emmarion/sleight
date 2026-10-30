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
