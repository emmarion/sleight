; needs: palindrome_relations palindrome palindrome_center ../self/base
; expect: (Cons 0 (Cons 2 (Cons 4 (Cons 0 (Cons 2 (Cons 3 (Cons 3 (Nil))))))))

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
            ((FoundAt a2 b2 l2 dr) (list-length (Nat) l2))))))))

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
  $ Nil (Nat))
