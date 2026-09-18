; needs: ../self/base palindrome_relations palindrome palindrome_center
; expect: (Cons 0 (Cons 2 (Cons 4 (Cons 0 (Cons 2 (Cons 3 (Cons 3 (Cons 2 (Cons 1 (Cons 1 (Cons 1 (Cons 1 (Cons 1 (Cons 0 (Cons 1 (Cons 3 (Cons 4 (Cons 3 (Cons 8 (Nil))))))))))))))))))))

(def-fns _ $ erased revcat-unique : (erased (List (Nat)) l1) (erased (List (Nat)) r1)
    (erased (List (Nat)) l2) (erased (List (Nat)) r2) (erased (List (Nat)) xs)
    (erased (RevCat l1 r1 xs) a) (erased (RevCat l2 r2 xs) b)
    (erased (Nat) q) (subterm erased (Length (Nat) l1 q) p1)
    (erased (Length (Nat) l2 q) p2) ->
    (erased (Eq (List (Nat)) l1 l2) el) (erased (Eq (List (Nat)) r1 r2) er)
  (match erased p1 _
    ((LNil c1)
      (match erased p2 _
        ((LNil c2)
          (match erased a _
            ((RevFlat d1)
              (match erased b _
                ((RevFlat d2)
                  (values (Refl (List (Nat)) l1) (Refl (List (Nat)) r1)))))))))
    ((LCons c1 x1 t1 q1 pp1)
      (match erased p2 _
        ((LCons c2 x2 t2 q2 pp2)
          (match erased a _
            ((RevStep y1 m1 s1 xa aa)
              (match erased b _
                ((RevStep y2 m2 s2 xb bb)
                  (let (erased e1) (erased e2)
                    (revcat-unique t1 (Cons (Nat) x1 r1) t2 (Cons (Nat) x2 r2)
                                   xs aa bb q1 pp1 pp2))
                  (match erased e1 _
                    ((Refl u1 v1)
                      (match erased e2 _
                        ((Refl u2 v2)
                          (values (Refl (List (Nat)) l1)
                                  (Refl (List (Nat)) r1)))))))))))))))

(def-fns _ $ erased revcat-drop : (erased (List (Nat)) l1) (erased (List (Nat)) r1)
    (erased (List (Nat)) l2) (erased (List (Nat)) r2) (erased (List (Nat)) xs)
    (erased (RevCat l1 r1 xs) a) (erased (RevCat l2 r2 xs) b)
    (erased (Nat) p) (erased (Nat) q) (subterm erased (Nat) d)
    (erased (Length (Nat) l1 p) lp) (erased (Length (Nat) l2 q) lq)
    (erased (Add q d p) ad) -> (erased (Drop d l1 l2) dr)
  (match erased d _
    ((Zero)
      (match erased (add-fn q (Zero) p q ad (add-zero-right q)) _
        ((Refl t0 r0)
          (let (erased el) (erased er) (revcat-unique l1 r1 l2 r2 xs a b q lp lq))
          (match erased el _ ((Refl u v) (DropZero l1))))))
    ((Succ d1)
      (let (erased p1) (erased ep) (erased ad1) (add-succ-right-inv q d1 p ad))
      (match erased ep _
        ((Refl t1 r1a)
          (match erased lp _
            ((LCons c1 x1 t1b n1 pp1)
              (match erased a _
                ((RevStep y1 m1 s1 xa aa)
                  (DropSucc d1 x1 t1b l2
                    (revcat-drop t1b (Cons (Nat) x1 r1) l2 r2 xs aa b n1 q d1
                                 pp1 lq ad1)))))))))))

(def-fns _ $ erased revcat-add : (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (List (Nat)) xs) (subterm erased (RevCat l r xs) rc)
    (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (erased (Length (Nat) l a) la) (erased (Length (Nat) r b) lb)
    (erased (Length (Nat) xs c) lc) -> (erased (Add a b c) ad)
  (match erased rc _
    ((RevFlat z)
      (match erased la _
        ((LNil z1)
          (match erased (length-fn r b c lb lc) _ ((Refl t1 r1) (AddZero b))))))
    ((RevStep x l1 r1 xs1 p1)
      (match erased la _
        ((LCons z1 x1 t1 a1 la1)
          (add-unshift a1 b c
            (revcat-add l1 (Cons (Nat) x r1) xs p1 a1 (Succ b) c la1
                        (LCons (Nat) x r1 b lb) lc)))))))

(def-fns _ $ erased revcat-drop-r : (erased (List (Nat)) l1) (erased (List (Nat)) r1)
    (erased (List (Nat)) l2) (erased (List (Nat)) r2) (erased (List (Nat)) xs)
    (erased (RevCat l1 r1 xs) a) (erased (RevCat l2 r2 xs) b)
    (erased (Nat) p) (erased (Nat) q) (subterm erased (Nat) d)
    (erased (Length (Nat) l1 p) lp) (erased (Length (Nat) l2 q) lq)
    (erased (Add p d q) ad)
    (erased (Nat) cn) (erased (Length (Nat) xs cn) lxs) ->
    (erased (Drop d r1 r2) dr)
  (match erased d _
    ((Zero)
      (match erased (add-fn p (Zero) q p ad (add-zero-right p)) _
        ((Refl t0 r0)
          (let (erased el) (erased er) (revcat-unique l1 r1 l2 r2 xs a b p lp lq))
          (match erased er _ ((Refl u v) (DropZero r1))))))
    ((Succ d1)
      (match erased r1 _
        ((Nil z)
          (let (erased b2) (erased lr2) (list-length r2))
          (match erased
            (match erased (add-fn p (Zero) cn p
                            (revcat-add l1 r1 xs a p (Zero) cn lp (LNil (Nat)) lxs)
                            (add-zero-right p)) (((False) ff))
              ((Refl t1 r1x)
                (let (erased q1) (erased eq1) (erased ad1)
                  (add-succ-right-inv p d1 q ad))
                (match erased eq1 (((False) ff2))
                  ((Refl t2 r2x)
                    (lt-asym p q (add-le-left p d1 q1 ad1)
                      (add-le-left q b2 cn
                        (revcat-add l2 r2 xs b q b2 cn lq lr2 lxs)))))))
            _))
        ((Cons z c1 r1b)
          (DropSucc d1 c1 r1b r2
            (revcat-drop-r (Cons (Nat) c1 l1) r1b l2 r2 xs
                           (RevStep c1 l1 r1b xs a) b
                           (Succ p) q d1 (LCons (Nat) c1 l1 p lp) lq
                           (add-unshift p d1 q ad) cn lxs)))))))

(def-adts
  (DropAtR : ((List (Nat)) r1) ((Nat) d) -> Type
    enum
    (many FoundR : (erased (List (Nat)) r1) (erased (Nat) d)
        (many (List (Nat)) r2) (erased (Drop d r1 r2) dr) -> (DropAtR r1 d))
    (many NotFoundR : (erased (List (Nat)) r1) (erased (Nat) d) -> (DropAtR r1 d))))

(def-adts
  (Zip : ((List (Nat)) xs) -> Type
    enum
    (many MkZip : (erased (List (Nat)) xs) (many (List (Nat)) l) (many (List (Nat)) r)
        (many (Nat) q) (erased (RevCat l r xs) rc) (erased (Length (Nat) l q) lq) ->
       (Zip xs))))

(def-fns _ $ many build-states : (many (List (Nat)) l) (subterm many (List (Nat)) r)
    (many (Nat) q) (erased (List (Nat)) xs) (erased (RevCat l r xs) rc)
    (erased (Length (Nat) l q) lq) (many (IdMap (Zip xs)) acc) ->
    (many (IdMap (Zip xs)) out)
  (let (many acc1) (idmap-set (Zip xs) q (MkZip xs l r q rc lq) acc))
  (match many r _
    ((Nil a) acc1)
    ((Cons a c r1)
      (build-states (Cons (Nat) c l) r1 (Succ q) xs (RevStep c l r1 xs rc)
                    (LCons (Nat) c l q lq) acc1))))

(def-fns _ $ many states-of : (many (List (Nat)) xs) -> (many (IdMap (Zip xs)) m)
  (build-states (Nil (Nat)) xs (Zero) xs (RevFlat xs) (LNil (Nat)) (MEmpty (Zip xs))))

; The tail of l1 at depth d, fetched in O(log n) rather than walked, with the Drop
; that expansion needs. Fails only if the map lacks the key or holds a state whose
; own position disagrees, neither of which states-of produces.
(def-adts
  (DropAt : ((List (Nat)) l1) ((Nat) d) -> Type
    enum
    (many FoundAt : (erased (List (Nat)) l1) (erased (Nat) d)
        (many (List (Nat)) l2) (erased (Drop d l1 l2) dr) -> (DropAt l1 d))
    (many NotFound : (erased (List (Nat)) l1) (erased (Nat) d) -> (DropAt l1 d))))

(def-fns _ $ many drop-at : (erased (List (Nat)) xs) (many (IdMap (Zip xs)) m)
    (many (List (Nat)) l1) (many (List (Nat)) r1) (erased (RevCat l1 r1 xs) a)
    (many (Nat) p) (erased (Length (Nat) l1 p) lp)
    (many (Nat) q) (many (Nat) d) (erased (Add q d p) ad) ->
    (many (DropAt l1 d) out)
  (match many (idmap-get (Zip xs) q m) _
    ((Miss t k mm pr) (NotFound l1 d))
    ((Hit t k mm z pr)
      (let-match many z (MkZip zxs zl zr zq zrc zlq))
      (match many (nat-cmp zq q) _
        ((CEq ct cr cx)
          (FoundAt l1 d zl (revcat-drop l1 r1 zl zr xs a zrc p q d lp zlq ad)))
        ((CLt ct cr ca cb cp) (NotFound l1 d))
        ((CGt ct cr ca cb cp) (NotFound l1 d))))))

(def-fns _ $ erased mirror-sym : (erased (List (Nat)) a) (erased (List (Nat)) b)
    (erased (Nat) k) (subterm erased (Mirror a b k) m) -> (erased (Mirror b a k) m2)
  (match erased m _
    ((MirrorZ l0 r0) (MirrorZ b a))
    ((MirrorS x a1 b1 k1 m1) (MirrorS x b1 a1 k1 (mirror-sym a1 b1 k1 m1)))))

(def-fns _ $ erased mirror-trans : (erased (List (Nat)) a) (erased (List (Nat)) b)
    (erased (List (Nat)) c) (erased (Nat) k)
    (subterm erased (Mirror a b k) m1) (erased (Mirror b c k) m2) ->
    (erased (Mirror a c k) m3)
  (match erased m1 _
    ((MirrorZ l0 r0) (MirrorZ a c))
    ((MirrorS x a1 b1 k1 p1)
      (match erased m2 _
        ((MirrorS y b2 c1 k2 q1)
          (MirrorS x a1 c1 k1 (mirror-trans a1 b1 c1 k1 p1 q1)))))))

(def-fns _ $ erased mirror-pred : (erased (List (Nat)) a) (erased (List (Nat)) b)
    (erased (Nat) k) (subterm erased (Mirror a b (Succ k)) m) ->
    (erased (Mirror a b k) m2)
  (match erased m _
    ((MirrorS x a1 b1 k1 m1)
      (match erased k _
        ((Zero) (MirrorZ a b))
        ((Succ k2) (MirrorS x a1 b1 k2 (mirror-pred a1 b1 k2 m1)))))))

(def-fns _ $ erased mirror-weaken : (erased (List (Nat)) a) (erased (List (Nat)) b)
    (erased (Nat) j) (subterm erased (Nat) k) (erased (Mirror a b k) m)
    (erased (Lt j (Succ k)) le) -> (erased (Mirror a b j) m2)
  (match erased k _
    ((Zero)
      (match erased le _
        ((LtZ b1) m)
        (absurd (LtS a1 b1 p1) (match erased p1 (((False) f))))))
    ((Succ k1)
      (match erased (nat-cmp j (Succ k1)) _
        ((CEq t r x) m)
        ((CLt t r x y p) (mirror-weaken a b j k1 (mirror-pred a b k1 m) p))
        (absurd (CGt t r x y q) (lt-asym (Succ k1) j q le))))))

; Expansion resumed at a radius already known to hold, rather than from zero:
; the caller supplies the Mirror and the two tails at that depth, which is what
; drop-at fetches in log time.
(def-fns _ $ many expand-from : (erased (List (Nat)) l) (erased (List (Nat)) r)
    (many (Nat) k0) (erased (Mirror l r k0) m)
    (subterm many (List (Nat)) l0) (many (List (Nat)) r0)
    (erased (Drop k0 l l0) dl) (erased (Drop k0 r r0) dr) ->
    (many (Nat) k) (erased (Mirror l r k) mk)
    (erased (List (Nat)) l2) (erased (List (Nat)) r2)
    (erased (Drop k l l2) dl2) (erased (Drop k r r2) dr2) (erased (Stop l2 r2) st)
  (match many l0 _
    ((Nil a) (values k0 m l0 r0 dl dr (StopL r0)))
    ((Cons a x l1)
      (match many r0 _
        ((Nil b) (values k0 m l0 r0 dl dr (StopR l0)))
        ((Cons b y r1)
          (match many (nat-cmp x y) _
            ((CEq t rr x0)
              (expand-from l r (Succ k0)
                           (mirror-extend l r k0 m x l1 r1 dl dr)
                           (subterm (prove-subterm l1 l0)) l1 r1
                           (drop-succ k0 l x l1 dl) (drop-succ k0 r x r1 dr)))
            ((CLt t rr a0 b0 p0)
              (values k0 m l0 r0 dl dr (StopNe x y l1 r1 (ApartLt x y p0))))
            ((CGt t rr a0 b0 p0)
              (values k0 m l0 r0 dl dr (StopNe x y l1 r1 (ApartGt x y p0))))))))))

(def-fns _ $ many drop-at-r : (erased (List (Nat)) xs) (many (IdMap (Zip xs)) m)
    (many (List (Nat)) l1) (many (List (Nat)) r1) (erased (RevCat l1 r1 xs) a)
    (many (Nat) p) (erased (Length (Nat) l1 p) lp)
    (many (Nat) q) (many (Nat) d) (erased (Add p d q) ad)
    (erased (Nat) cn) (erased (Length (Nat) xs cn) lxs) ->
    (many (DropAtR r1 d) out)
  (match many (idmap-get (Zip xs) q m) _
    ((Miss t k mm pr) (NotFoundR r1 d))
    ((Hit t k mm z pr)
      (let-match many z (MkZip zxs zl zr zq zrc zlq))
      (match many (nat-cmp zq q) _
        ((CEq ct cr cx)
          (FoundR r1 d zr
                  (revcat-drop-r l1 r1 zl zr xs a zrc p q d lp zlq ad cn lxs)))
        ((CLt ct cr ca cb cp) (NotFoundR r1 d))
        ((CGt ct cr ca cb cp) (NotFoundR r1 d))))))

(def-fns _ $ many right-probe : (many (List (Nat)) xs) (many (Nat) d) -> (many (Nat) n)
  (let (many m) (states-of xs))
  (let (many cn) (erased lxs) (list-length xs))
  (match many (drop-at-r xs m (Nil (Nat)) xs (RevFlat xs) (Zero) (LNil (Nat))
                         d d (AddZero d) cn lxs)
               (((Nat) rr))
    ((NotFoundR a b) (Zero))
    ((FoundR a b r2 dr) (let (many k) (erased lk) (list-length r2)) k)))

(def-fns _ $ many depth-probe : (many (List (Nat)) xs) (many (Nat) p) (many (Nat) d) ->
    (many (Nat) n)
  (let (many m) (states-of xs))
  (match many (idmap-get (Zip xs) p m) (((Nat) rr))
    ((Miss t k mm pr) (Zero))
    ((Hit t k mm z pr)
      (let-match many z (MkZip zxs zl zr zq zrc zlq))
      (match many (lt-dec d (Succ zq)) (((Nat) rr2))
        ((No a b ge) (Zero))
        ((Yes a b le)
          (let (many q) (erased adq) (sub zq d le))
          (match many (drop-at xs m zl zr zrc zq zlq q d (add-comm d q zq adq))
                       (((Nat) rr3))
            ((NotFound a2 b2) (Zero))
            ((FoundAt a2 b2 l2 dr) (let (many kk) (erased lkk) (list-length l2)) kk)))))))

(def-fns _ $ erased mirror-cons : (erased (Nat) c) (erased (List (Nat)) a)
    (erased (List (Nat)) b) (erased (Nat) j) (erased (Mirror a b j) m) ->
    (erased (Mirror (Cons (Nat) c a) (Cons (Nat) c b) j) m2)
  (match erased j _
    ((Zero) (MirrorZ (Cons (Nat) c a) (Cons (Nat) c b)))
    ((Succ j1) (MirrorS c a b j1 (mirror-pred a b j1 m)))))

; The radii already computed, indexed by the zipper each was computed at, so the
; mirror centre reads them by walking left exactly as it walks.
(def-adts
  (RadList : ((List (Nat)) lm) ((List (Nat)) rm) -> Type
    enum
    (many RadNone : (erased (List (Nat)) lm) (erased (List (Nat)) rm) -> (RadList lm rm))
    (many RadSome : (erased (Nat) c) (erased (List (Nat)) lm1) (erased (List (Nat)) rm)
        (many (Nat) k) (erased (Mirror (Cons (Nat) c lm1) rm k) mk)
        (many (RadList lm1 (Cons (Nat) c rm)) rest) ->
       (RadList (Cons (Nat) c lm1) rm))))

; The enclosing palindrome, as a budget b and a mirror centre (lm, rm) whose own
; radii are to hand. invA and invB are the two reflections: everything right of
; the current centre matches everything left of the mirror centre to depth b, and
; vice versa. b is the old reach minus the distance walked, so a radius exceeding
; it is exactly a centre reaching further right than the enclosing palindrome.
(def-adts
  (Tracker : ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many NoTrack : (erased (List (Nat)) l) (erased (List (Nat)) r) -> (Tracker l r))
    (many MkTrack : (erased (List (Nat)) l) (erased (List (Nat)) r) (many (Nat) b)
        (erased (List (Nat)) lm) (erased (List (Nat)) rm)
        (erased (Mirror r lm b) invA) (erased (Mirror l rm b) invB)
        (many (RadList lm rm) rads) -> (Tracker l r))))

(def-fns _ $ many track-new : (many (List (Nat)) l) (many (List (Nat)) r) (many (Nat) k)
    (erased (Mirror l r k) mk) (many (RadList l r) rads) -> (many (Tracker l r) t)
  (MkTrack l r k l r (mirror-sym l r k mk) mk rads))

; The lower bound a centre inherits: the mirror centre's radius, clipped to the
; budget. Composing the two reflections with the mirror centre's own mirror is
; what carries it across, and costs nothing at runtime.
(def-fns _ $ many transport : (many (List (Nat)) l) (many (List (Nat)) r)
    (many (Tracker l r) t) -> (many (Nat) k0) (erased (Mirror l r k0) m0)
  (match many t _
    ((NoTrack a b) (values (Zero) (MirrorZ l r)))
    ((MkTrack a b budget lm rm invA invB rads)
      (match many rads _
        ((RadNone c d) (values (Zero) (MirrorZ l r)))
        ((RadSome c lm1 rm0 k mk rest)
          (let (many k0) (erased lek) (erased leb)
            (match many (nat-cmp k budget)
                         (((Nat) kk) ((Lt kk (Succ k)) e1) ((Lt kk (Succ budget)) e2))
              ((CLt t1 r1 a1 b1 p1) (values k (lt-succ k) (lt-weaken k budget p1)))
              ((CEq t1 r1 a1) (values k (lt-succ k) (lt-succ k)))
              ((CGt t1 r1 a1 b1 p1) (values budget (lt-weaken budget k p1) (lt-succ budget)))))
          (values k0
            (mirror-trans l rm r k0
              (mirror-weaken l rm k0 budget invB leb)
              (mirror-trans rm lm r k0
                (mirror-sym lm rm k0 (mirror-weaken lm rm k0 k mk lek))
                (mirror-sym r lm k0 (mirror-weaken r lm k0 budget invA leb))))))))))

; Walking the centre one place right walks the mirror centre one place left. The
; heads agree by invA, which is what lets both reflections be rebuilt one shorter.
(def-fns _ $ many track-step : (many (List (Nat)) l) (many (Nat) c) (many (List (Nat)) r1)
    (many (Tracker l (Cons (Nat) c r1)) t) ->
    (many (Tracker (Cons (Nat) c l) r1) t2)
  (match many t _
    ((NoTrack a b) (NoTrack (Cons (Nat) c l) r1))
    ((MkTrack a b budget lm rm invA invB rads)
      (match many budget _
        ((Zero) (NoTrack (Cons (Nat) c l) r1))
        ((Succ b1)
          (match erased invA (((Tracker (Cons (Nat) c l) r1) z))
            ((MirrorS x r2 lm1 b2 mA)
              (MkTrack (Cons (Nat) c l) r1 b1 lm1 (Cons (Nat) c rm)
                       mA
                       (mirror-cons c l rm b1
                         (mirror-weaken l rm b1 budget invB
                                        (lt-weaken b1 budget (lt-succ b1))))
                       (match many rads _
                         ((RadNone d1 d2) (RadNone lm1 (Cons (Nat) c rm)))
                         ((RadSome c2 lm2 rm2 k2 mk2 rest) rest))))))))))

(def-adts
  (RadListO : ((List (Nat)) lm) ((List (Nat)) rm) -> Type
    enum
    (many RadNoneO : (erased (List (Nat)) lm) (erased (List (Nat)) rm) ->
       (RadListO lm rm))
    (many RadSomeO : (erased (Nat) c) (erased (List (Nat)) lm1)
        (erased (List (Nat)) rm) (many (Nat) k) (erased (Mirror lm1 rm k) mk)
        (many (RadListO lm1 (Cons (Nat) c rm)) rest) ->
       (RadListO (Cons (Nat) c lm1) rm))))

(def-adts
  (TrackerO : ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many NoTrackO : (erased (List (Nat)) l) (erased (List (Nat)) r) -> (TrackerO l r))
    (many MkTrackO : (erased (List (Nat)) l) (erased (List (Nat)) r) (many (Nat) b)
        (erased (List (Nat)) lm) (erased (List (Nat)) rm)
        (erased (Mirror r lm b) invA) (erased (Mirror l rm b) invB)
        (many (RadListO lm rm) rads) -> (TrackerO l r))))

(def-fns _ $ many track-new-o : (many (List (Nat)) l) (many (Nat) c)
    (many (List (Nat)) r1) (many (Nat) k) (erased (Mirror l r1 k) mk)
    (many (RadListO (Cons (Nat) c l) r1) rads) ->
    (many (TrackerO l (Cons (Nat) c r1)) t)
  (MkTrackO l (Cons (Nat) c r1) k (Cons (Nat) c l) r1
            (mirror-cons c r1 l k (mirror-sym l r1 k mk)) mk rads))

(def-fns _ $ many transport-o : (many (List (Nat)) l) (many (Nat) c)
    (many (List (Nat)) r1) (many (TrackerO l (Cons (Nat) c r1)) t) ->
    (many (Nat) k0) (erased (Mirror l r1 k0) m0)
  (match many t _
    ((NoTrackO a b) (values (Zero) (MirrorZ l r1)))
    ((MkTrackO a b budget lm rm invA invB rads)
      (match many budget _
        ((Zero) (values (Zero) (MirrorZ l r1)))
        ((Succ b1)
          (match many rads _
            ((RadNoneO d1 d2) (values (Zero) (MirrorZ l r1)))
            ((RadSomeO cc lm1 rm0 k mk rest)
              (let (erased pa)
                (match erased invA (((Mirror r1 lm1 b1) z))
                  ((MirrorS x r2 lz b2 mA) mA)))
              (let (many k0) (erased lek) (erased leb)
                (match many (nat-cmp k b1)
                            (((Nat) kk) ((Lt kk (Succ k)) e1) ((Lt kk (Succ b1)) e2))
                  ((CLt t1 r2 a1 b2 p1) (values k (lt-succ k) (lt-weaken k b1 p1)))
                  ((CEq t1 r2 a1) (values k (lt-succ k) (lt-succ k)))
                  ((CGt t1 r2 a1 b2 p1)
                    (values b1 (lt-weaken b1 k p1) (lt-succ b1)))))
              (values k0
                (mirror-trans l rm r1 k0
                  (mirror-weaken l rm k0 budget invB
                                 (lt-weaken k0 budget (lt-le-trans k0 (Succ b1) budget leb (lt-succ budget))))
                  (mirror-trans rm lm1 r1 k0
                    (mirror-sym lm1 rm k0 (mirror-weaken lm1 rm k0 k mk lek))
                    (mirror-sym r1 lm1 k0
                                (mirror-weaken r1 lm1 k0 b1 pa leb))))))))))))

(def-fns _ $ many track-step-o : (many (List (Nat)) l) (many (Nat) c)
    (many (List (Nat)) r1) (many (TrackerO l (Cons (Nat) c r1)) t) ->
    (many (TrackerO (Cons (Nat) c l) r1) t2)
  (match many t _
    ((NoTrackO a b) (NoTrackO (Cons (Nat) c l) r1))
    ((MkTrackO a b budget lm rm invA invB rads)
      (match many budget _
        ((Zero) (NoTrackO (Cons (Nat) c l) r1))
        ((Succ b1)
          (match erased invA (((TrackerO (Cons (Nat) c l) r1) z))
            ((MirrorS x r2 lm1 b2 mA)
              (MkTrackO (Cons (Nat) c l) r1 b1 lm1 (Cons (Nat) c rm)
                        mA
                        (mirror-cons c l rm b1
                          (mirror-weaken l rm b1 budget invB
                                         (lt-weaken b1 budget (lt-succ b1))))
                        (match many rads _
                          ((RadNoneO d1 d2) (RadNoneO lm1 (Cons (Nat) c rm)))
                          ((RadSomeO c2 lm2 rm2 k2 mk2 rest) rest))))))))))

; The radii already found, packaged for a position that may have none before it.
(def-adts
  (Hist : ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many HistNil : (erased (List (Nat)) r) -> (Hist (Nil (Nat)) r))
    (many HistCons : (erased (Nat) c) (erased (List (Nat)) l1) (erased (List (Nat)) r)
        (many (RadList l1 (Cons (Nat) c r)) prev) ->
       (Hist (Cons (Nat) c l1) r))))

(def-fns _ $ many track-update : (many (List (Nat)) l) (many (Nat) c)
    (many (List (Nat)) r1) (many (Tracker l (Cons (Nat) c r1)) tr)
    (many (Nat) k) (erased (Mirror l (Cons (Nat) c r1) k) mk)
    (many (RadList l (Cons (Nat) c r1)) rl) ->
    (many (Tracker (Cons (Nat) c l) r1) t2)
  (match many tr _
    ((NoTrack a b)
      (track-step l c r1 (track-new l (Cons (Nat) c r1) k mk rl)))
    ((MkTrack a b budget lm rm invA invB rads)
      (match many (nat-cmp budget k) _
        ((CLt t1 r2 a1 b1 p1)
          (track-step l c r1 (track-new l (Cons (Nat) c r1) k mk rl)))
        ((CEq t1 r2 a1) (track-step l c r1 tr))
        ((CGt t1 r2 a1 b1 p1) (track-step l c r1 tr))))))

(def-fns _ $ many fetch : (erased (List (Nat)) xs) (many (IdMap (Zip xs)) states)
    (many (List (Nat)) l) (many (List (Nat)) rr)
    (many (List (Nat)) rl) (erased (RevCat l rl xs) rcl)
    (many (Nat) p) (erased (Length (Nat) l p) lp)
    (many (List (Nat)) lr) (erased (RevCat lr rr xs) rcr)
    (many (Nat) pr) (erased (Length (Nat) lr pr) lpr)
    (erased (Nat) cn) (erased (Length (Nat) xs cn) lxs)
    (many (Nat) k0) (erased (Mirror l rr k0) m0) ->
    (many (Nat) kk) (erased (Mirror l rr kk) mkk)
    (many (List (Nat)) l0) (many (List (Nat)) r0)
    (erased (Drop kk l l0) dl0) (erased (Drop kk rr r0) dr0)
  (match many (lt-dec k0 (Succ p))
              (((Nat) a1) ((Mirror l rr a1) a2) ((List (Nat)) a3) ((List (Nat)) a4)
               ((Drop a1 l a3) a5) ((Drop a1 rr a4) a6))
    ((No za zb ge) (values (Zero) (MirrorZ l rr) l rr (DropZero l) (DropZero rr)))
    ((Yes za zb le)
      (let (many q) (erased adq) (sub p k0 le))
      (let (many q2) (erased adq2) (add pr k0))
      (match many (drop-at xs states l rl rcl p lp q k0 (add-comm k0 q p adq))
                  (((Nat) b1) ((Mirror l rr b1) b2) ((List (Nat)) b3) ((List (Nat)) b4)
                   ((Drop b1 l b3) b5) ((Drop b1 rr b4) b6))
        ((NotFound wa wb)
          (values (Zero) (MirrorZ l rr) l rr (DropZero l) (DropZero rr)))
        ((FoundAt wa wb ll dll)
          (match many (drop-at-r xs states lr rr rcr pr lpr q2 k0 adq2 cn lxs)
                      (((Nat) c1) ((Mirror l rr c1) c2) ((List (Nat)) c3)
                       ((List (Nat)) c4) ((Drop c1 l c3) c5) ((Drop c1 rr c4) c6))
            ((NotFoundR va vb)
              (values (Zero) (MirrorZ l rr) l rr (DropZero l) (DropZero rr)))
            ((FoundR va vb rrr drr) (values k0 m0 ll rrr dll drr))))))))

(def-fns _ $ many manacher-even : (many (List (Nat)) l) (subterm many (List (Nat)) r)
    (erased (List (Nat)) xs) (erased (RevCat l r xs) rc)
    (many (IdMap (Zip xs)) states)
    (many (Nat) p) (erased (Length (Nat) l p) lp)
    (erased (Nat) cn) (erased (Length (Nat) xs cn) lxs)
    (many (Tracker l r) tr) (many (Hist l r) hist) ->
    (many (List (Nat)) out)
  (let (many k0) (erased m0) (transport l r tr))
  (let (many kk) (erased mkk) (many l0) (many r0) (erased dl0) (erased dr0)
    (fetch xs states l r r rc p lp l rc p lp cn lxs k0 m0))
  (let (many k) (erased mk) (erased l2) (erased r2) (erased dl2) (erased dr2) (erased st)
    (expand-from l r kk mkk l0 r0 dl0 dr0))
  (match many r _
    ((Nil a) (Cons (Nat) k (Nil (Nat))))
    ((Cons a c r1)
      (let (many rl)
        (match many hist (((RadList l r) z))
          ((HistNil h1) (RadNone l r))
          ((HistCons hc hl1 hr prev) (RadSome hc hl1 r k mk prev))))
      (Cons (Nat) k
        (manacher-even (Cons (Nat) c l) r1 xs (RevStep c l r1 xs rc) states
                       (Succ p) (LCons (Nat) c l p lp) cn lxs
                       (track-update l c r1 tr k mk rl)
                       (HistCons c l r1 rl))))))

(def-fns _ $ many manacher-radii : (many (List (Nat)) xs) -> (many (List (Nat)) out)
  (let (many m) (states-of xs))
  (let (many cn) (erased lxs) (list-length xs))
  (manacher-even (Nil (Nat)) xs xs (RevFlat xs) m (Zero) (LNil (Nat)) cn lxs
                 (NoTrack (Nil (Nat)) xs) (HistNil xs)))

(def-fns _ $ many naive-radii : (many (List (Nat)) l) (subterm many (List (Nat)) r) ->
    (many (List (Nat)) out)
  (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr) (erased st)
    (expand l r))
  (match many r _
    ((Nil a) (Cons (Nat) k (Nil (Nat))))
    ((Cons a c r1) (Cons (Nat) k (naive-radii (Cons (Nat) c l) r1)))))

(def-fns _ $ many track-update-o : (many (List (Nat)) l) (many (Nat) c)
    (many (List (Nat)) r1) (many (TrackerO l (Cons (Nat) c r1)) tr)
    (many (Nat) k) (erased (Mirror l r1 k) mk)
    (many (RadListO (Cons (Nat) c l) r1) rl) ->
    (many (TrackerO (Cons (Nat) c l) r1) t2)
  (match many tr _
    ((NoTrackO a b) (track-step-o l c r1 (track-new-o l c r1 k mk rl)))
    ((MkTrackO a b budget lm rm invA invB rads)
      (match many (nat-cmp budget k) _
        ((CLt t1 r2 a1 b1 p1) (track-step-o l c r1 (track-new-o l c r1 k mk rl)))
        ((CEq t1 r2 a1) (track-step-o l c r1 tr))
        ((CGt t1 r2 a1 b1 p1) (track-step-o l c r1 tr))))))

(def-fns _ $ many manacher-odd : (many (List (Nat)) l) (subterm many (List (Nat)) r)
    (erased (List (Nat)) xs) (erased (RevCat l r xs) rc)
    (many (IdMap (Zip xs)) states)
    (many (Nat) p) (erased (Length (Nat) l p) lp)
    (erased (Nat) cn) (erased (Length (Nat) xs cn) lxs)
    (many (TrackerO l r) tr) (many (RadListO l r) rads) ->
    (many (List (Nat)) out)
  (match many r _
    ((Nil a) (Nil (Nat)))
    ((Cons a c r1)
      (let (many k0) (erased m0) (transport-o l c r1 tr))
      (let (many kk) (erased mkk) (many l0) (many r0) (erased dl0) (erased dr0)
        (fetch xs states l r1 r rc p lp (Cons (Nat) c l) (RevStep c l r1 xs rc)
               (Succ p) (LCons (Nat) c l p lp) cn lxs k0 m0))
      (let (many k) (erased mk) (erased l2) (erased r2) (erased dl2) (erased dr2)
           (erased st) (expand-from l r1 kk mkk l0 r0 dl0 dr0))
      (let (many rl) (RadSomeO c l r1 k mk rads))
      (Cons (Nat) k
        (manacher-odd (Cons (Nat) c l) r1 xs (RevStep c l r1 xs rc) states
                      (Succ p) (LCons (Nat) c l p lp) cn lxs
                      (track-update-o l c r1 tr k mk rl) rl)))))

(def-fns _ $ many manacher-odd-radii : (many (List (Nat)) xs) ->
    (many (List (Nat)) out)
  (let (many m) (states-of xs))
  (let (many cn) (erased lxs) (list-length xs))
  (manacher-odd (Nil (Nat)) xs xs (RevFlat xs) m (Zero) (LNil (Nat)) cn lxs
                (NoTrackO (Nil (Nat)) xs) (RadNoneO (Nil (Nat)) xs)))

(def-fns _ $ many naive-odd : (many (List (Nat)) l) (subterm many (List (Nat)) r) ->
    (many (List (Nat)) out)
  (match many r _
    ((Nil a) (Nil (Nat)))
    ((Cons a c r1)
      (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr)
           (erased st) (expand l r1))
      (Cons (Nat) k (naive-odd (Cons (Nat) c l) r1)))))

(def-fns _ $ many centre-of : (many (List (Nat)) l) (many (List (Nat)) rm)
    (many (Nat) cn) (erased (List (Nat)) core) (erased (Palindrome (Nat) core) pc)
    (erased (Length (Nat) core cn) lc)
    (erased (List (Nat)) src) (erased (Concat (Nat) core rm src) cc)
    (erased (List (Nat)) xs) (erased (RevCat l src xs) rc)
    (many (Nat) k) (erased (Mirror l rm k) m)
    (erased (List (Nat)) le) (erased (List (Nat)) re)
    (erased (Drop k l le) dl) (erased (Drop k rm re) dr) (erased (Stop le re) st) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
    (erased (CentreBound l rm cn n) cb)
  (let (erased w) (erased pw) (erased n0) (erased lw) (erased d0) (erased dd0)
       (erased ad0) (erased src2) (erased r2) (erased cc2) (erased l2) (erased rc2)
       (mirror-wrap l rm k m core pc cn lc src cc xs rc))
  (let (many drt) (erased ddrt) (double k))
  (let (many nrt) (erased adrt) (add cn drt))
  (let (erased lw2) (fix-length w cn k d0 n0 drt nrt dd0 ad0 ddrt adrt lw))
  (values nrt (revcat-has l2 src2 xs rc2 nrt
                (HasHere src2 nrt w (concat-take w r2 src2 cc2 nrt lw2) pw))
              (MkCentreBound l rm cn nrt k le re dl dr st drt ddrt nrt adrt
                             (lt-succ nrt))))

(def-fns _ $ many manacher-walk : (many (List (Nat)) l) (subterm many (List (Nat)) r)
    (erased (List (Nat)) xs) (erased (RevCat l r xs) rc)
    (many (IdMap (Zip xs)) states)
    (many (Nat) p) (erased (Length (Nat) l p) lp)
    (erased (Nat) cn) (erased (Length (Nat) xs cn) lxs)
    (many (Tracker l r) te) (many (Hist l r) hist)
    (many (TrackerO l r) to) (many (RadListO l r) radso) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) h)
    (erased (AllBounded l r n) ab)
  (let (many k0e) (erased m0e) (transport l r te))
  (let (many kke) (erased mkke) (many l0e) (many r0e) (erased dl0e) (erased dr0e)
    (fetch xs states l r r rc p lp l rc p lp cn lxs k0e m0e))
  (let (many ke) (erased mke) (erased lee) (erased ree) (erased dle) (erased dre)
       (erased ste) (expand-from l r kke mkke l0e r0e dl0e dr0e))
  (let (many ne) (erased he) (erased cbe)
    (centre-of l r (Zero) (Nil (Nat)) (PalNil (Nat)) (LNil (Nat)) r (CatNil (Nat) r)
               xs rc ke mke lee ree dle dre ste))
  (match many r _
    ((Nil a) (values ne he (AllBEnd l ne cbe)))
    ((Cons a c r1)
      (let (many k0o) (erased m0o) (transport-o l c r1 to))
      (let (many kko) (erased mkko) (many l0o) (many r0o) (erased dl0o) (erased dr0o)
        (fetch xs states l r1 r rc p lp (Cons (Nat) c l) (RevStep c l r1 xs rc)
               (Succ p) (LCons (Nat) c l p lp) cn lxs k0o m0o))
      (let (many ko) (erased mko) (erased leo) (erased reo) (erased dlo) (erased dro)
           (erased sto) (expand-from l r1 kko mkko l0o r0o dl0o dr0o))
      (let (many no) (erased ho) (erased cbo)
        (centre-of l r1 (Succ (Zero)) (Cons (Nat) c (Nil (Nat))) (PalOne (Nat) c)
                   (LCons (Nat) c (Nil (Nat)) (Zero) (LNil (Nat)))
                   r (CatCons (Nat) c (Nil (Nat)) r1 r1 (CatNil (Nat) r1))
                   xs rc ko mko leo reo dlo dro sto))
      (let (many rle)
        (match many hist (((RadList l r) z))
          ((HistNil h1) (RadNone l r))
          ((HistCons hc hl1 hr prev) (RadSome hc hl1 r ke mke prev))))
      (let (many rlo) (RadSomeO c l r1 ko mko radso))
      (let (many nr) (erased hr) (erased abr)
        (manacher-walk (Cons (Nat) c l) r1 xs (RevStep c l r1 xs rc) states
                       (Succ p) (LCons (Nat) c l p lp) cn lxs
                       (track-update l c r1 te ke mke rle) (HistCons c l r1 rle)
                       (track-update-o l c r1 to ko mko rlo) rlo))
      (let (many n1) (erased h1) (erased be1) (erased be2) (pick xs ne he no ho))
      (let (many n) (erased h) (erased be3) (erased be4) (pick xs n1 h1 nr hr))
      (values n h
        (AllBStep l c r1 n
          (cb-weaken l r (Zero) ne n cbe (le-trans ne n1 n be1 be3))
          (cb-weaken l r1 (Succ (Zero)) no n cbo (le-trans no n1 n be2 be3))
          (allb-weaken (Cons (Nat) c l) r1 nr n abr be4))))))

(def-fns _ $ many longest-manacher : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) p)
  (let (many m) (states-of xs))
  (let (many len) (erased lxs) (list-length xs))
  (let (many n) (erased h) (erased ab)
    (manacher-walk (Nil (Nat)) xs xs (RevFlat xs) m (Zero) (LNil (Nat)) len lxs
                   (NoTrack (Nil (Nat)) xs) (HistNil xs)
                   (NoTrackO (Nil (Nat)) xs) (RadNoneO (Nil (Nat)) xs)))
  (let (erased nle)
    (match many (lt-dec len n) (((Lt n (Succ len)) z))
      (absurd (Yes a b p1) (has-short-absurd xs n h len lxs p1))
      ((No a b q) q)))
  (let (many c) (erased adc) (sub len n nle))
  (let (erased nl) (no-larger xs n ab len lxs n c adc (lt-succ n)))
  (let (erased xss) (erased ww) (erased ee) (has-windows xs n h))
  (values n (IsLongest xs n xss ww ee (nolarger-spec xs n nl))))

(def-fns _ $ many lm : (many (List (Nat)) xs) -> (many (Nat) n)
  (let (many n) (erased p) (longest-manacher xs))
  n)

(def-fns _ $ many nats-agree : (subterm many (List (Nat)) a) (many (List (Nat)) b) ->
    (many (Nat) r)
  (match many a _
    ((Nil z) (match many b _ ((Nil z2) 1) ((Cons z2 y ys) (Zero))))
    ((Cons z x xs)
      (match many b _
        ((Nil z2) (Zero))
        ((Cons z2 y ys)
          (match many (nat-cmp x y) _
            ((CEq t r w) (nats-agree xs ys))
            ((CLt t r w1 w2 w3) (Zero))
            ((CGt t r w1 w2 w3) (Zero))))))))

; The skipping search must agree with full expansion at every centre.
(def-fns _ $ many agree : (many (List (Nat)) xs) -> (many (Nat) r)
  (match many (nats-agree (manacher-radii xs) (naive-radii (Nil (Nat)) xs)) (((Nat) z))
    ((Zero) (Zero))
    ((Succ w) (nats-agree (manacher-odd-radii xs) (naive-odd (Nil (Nat)) xs)))))

(def-fns _ $ many radius-from : (many (List (Nat)) l) (many (List (Nat)) r) ->
    (many (Nat) k)
  (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr) (erased st)
    (expand-from l r (Zero) (MirrorZ l r) l r (DropZero l) (DropZero r)))
  k)

; The same expansion resumed one step in: l and r share a head, so Mirror l r 1
; and the two Drops are writable by hand, and the answer must not change.
(def-fns _ $ many radius-resumed : (many (Nat) x) (many (List (Nat)) l1)
    (many (List (Nat)) r1) -> (many (Nat) k)
  (let (many k) (erased m) (erased l2) (erased r2) (erased dl) (erased dr) (erased st)
    (expand-from (Cons (Nat) x l1) (Cons (Nat) x r1) (Succ (Zero))
                 (MirrorS x l1 r1 (Zero) (MirrorZ l1 r1))
                 l1 r1
                 (DropSucc (Zero) x l1 l1 (DropZero l1))
                 (DropSucc (Zero) x r1 r1 (DropZero r1))))
  k)

(let (many la) (Cons (Nat) 2 $ Cons (Nat) 1 $ Nil (Nat)))
(let (many ra) (Cons (Nat) 2 $ Cons (Nat) 1 $ Cons (Nat) 9 $ Nil (Nat)))
(let (many s) (Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 4 $ Nil (Nat)))
(Cons (Nat) (depth-probe s (Zero) (Zero))
  $ Cons (Nat) (depth-probe s (Succ (Succ (Succ (Zero)))) (Succ (Zero)))
  $ Cons (Nat) (depth-probe s (Succ (Succ (Succ (Succ (Zero))))) (Zero))
  $ Cons (Nat) (radius-from (Nil (Nat)) ra)
  $ Cons (Nat) (radius-from la ra)
  $ Cons (Nat) (radius-from (Cons (Nat) 3 la) (Cons (Nat) 3 ra))
  $ Cons (Nat) (radius-resumed 3 la ra)
  $ Cons (Nat) (right-probe s (Succ (Succ (Zero))))
  $ Cons (Nat) (agree s)
  $ Cons (Nat) (agree (Nil (Nat)))
  $ Cons (Nat) (agree $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Nil (Nat))
  $ Cons (Nat) (agree $ Cons (Nat) 4 $ Cons (Nat) 4 $ Cons (Nat) 1 $ Cons (Nat) 4 $ Cons (Nat) 4 $ Cons (Nat) 1 $ Cons (Nat) 4 $ Cons (Nat) 4 $ Nil (Nat))
  $ Cons (Nat) (agree $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 2 $ Cons (Nat) 1 $ Cons (Nat) 5 $ Nil (Nat))
  $ Cons (Nat) (lm (Nil (Nat)))
  $ Cons (Nat) (lm $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Nil (Nat))
  $ Cons (Nat) (lm $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 2 $ Cons (Nat) 5 $ Nil (Nat))
  $ Cons (Nat) (lm $ Cons (Nat) 9 $ Cons (Nat) 4 $ Cons (Nat) 5 $ Cons (Nat) 5 $ Cons (Nat) 4 $ Cons (Nat) 8 $ Nil (Nat))
  $ Cons (Nat) (lm $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Nil (Nat))
  $ Cons (Nat) (lm $ Cons (Nat) 4 $ Cons (Nat) 4 $ Cons (Nat) 1 $ Cons (Nat) 4 $ Cons (Nat) 4 $ Cons (Nat) 1 $ Cons (Nat) 4 $ Cons (Nat) 4 $ Nil (Nat))
  $ Nil (Nat))
