; needs: palindrome_relations palindrome palindrome_center ../self/base
; expect: (Cons 0 (Cons 2 (Cons 4 (Nil))))

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

(let (many s) (Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 4 $ Nil (Nat)))
(Cons (Nat) (depth-probe s (Zero) (Zero))
  $ Cons (Nat) (depth-probe s (Succ (Succ (Succ (Zero)))) (Succ (Zero)))
  $ Cons (Nat) (depth-probe s (Succ (Succ (Succ (Succ (Zero))))) (Zero))
  $ Nil (Nat))
