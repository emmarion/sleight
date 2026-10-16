; expect: (Cons _ (MkPair _ _ (BTrue) 0) $ Cons _ (MkPair _ _ (BTrue) 1) $ Cons _ (MkPair _ _ (BFalse) 0) $ Cons _ (MkPair _ _ (BTrue) 2) $ Cons _ (MkPair _ _ (BFalse) 1) $ Cons _ (MkPair _ _ (BFalse) 99) $ Cons _ (MkPair _ _ (BFalse) 3) $ Cons _ (MkPair _ _ (BFalse) 1) $ Cons _ (MkPair _ _ (BFalse) 0) $ Nil _)
; needs: ../std/list
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))

(def-fns _ $ (many tag : (erased (List (Slot)) xs) (erased (Slot) s) (erased (List (Slot)) ys) (many (SlotIntern xs s ys) r) ->
    (many (Pair (Bool) (Nat)) out))
  (match many r _ ((SlotExisting _ _ i _) (MkPair _ _ (BFalse) i)) ((SlotAdded _ _ i _) (MkPair _ _ (BTrue) i))))

(def-fns _ $ (many found : (erased (List (Slot)) xs) (erased (Slot) s) (many (SlotFind xs s) r) -> (many (Nat) out))
  (match many r _ ((SlotFound _ _ i _) i) ((SlotMissing _ _) 99)))

(def-adts $ (SuffixOf : (Type A) ((List A) xs) ((List A) ys) -> Type)
  enum
  (many SuffixOfRefl : (erased Type A) (erased (List A) xs) -> (SuffixOf A xs xs))
  (many SuffixOfCons : (erased Type A) (erased A y) (erased (List A) xs) (erased (List A) ys)
     (erased (SuffixOf A xs ys) p) -> (SuffixOf A xs (Cons A y ys))))

(def-fns _ $ (erased nth-last-suffix : (erased Type A) (erased (List A) xs) (erased (List A) ys) (erased (Nat) i) (erased A x)
    (erased (NthLast A xs i x) q) (subterm erased (SuffixOf A xs ys) p) -> (erased (NthLast A ys i x) r))
  (let-match erased p (SuffixOfCons _ y _ zs p1) ((SuffixOfRefl _ _) q))
  (NthLastThere _ y zs i x (nth-last-suffix _ xs zs i x q p1)))

(def-fns _ $ (erased nth-last-lt : (erased Type A) (erased (List A) xs) (erased (Nat) i n) (erased A x)
    (subterm erased (NthLast A xs i x) q) (erased (Length A xs n) p) -> (erased (Lt i n) r))
  (let-match erased p (LengthCons _ y rest k p1) (absurd (LengthNil _) q))
  (let-match erased q (NthLastThere _ _ _ _ _ q1)
    ((NthLastHere _ _ _ _ p2) (let-match erased (length-fn _ rest i k p2 p1) (Refl _ _)) (lt-succ i)))
  (lt-weaken i k (nth-last-lt _ rest i k x q1 p1)))

(def-fns _ $ (erased nth-last-fn : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A x y)
    (subterm erased (NthLast A xs i x) p) (erased (NthLast A xs i y) q) -> (erased (Eq A x y) e))
  (match erased p _
    ((NthLastHere _ _ rest n l1)
      (match erased q _
        ((NthLastHere _ _ _ _ _) (Refl _ x))
        (absurd (NthLastThere _ _ _ _ _ q1) (let ((erased l)) (nth-last-lt _ rest n n y q1 l1)) (lt-asym n n l (lt-weaken n n l)))))
    ((NthLastThere _ z rest k _ p1)
      (match erased q _
        (absurd (NthLastHere _ _ _ _ l2) (let ((erased l)) (nth-last-lt _ rest k k x p1 l2)) (lt-asym k k l (lt-weaken k k l)))
        ((NthLastThere _ _ _ _ _ q1) (nth-last-fn _ rest k x y p1 q1))))))

(def-fns _ $ (many recover : (many (Box) a) (many (Box) c) (many (Box) b) -> (many (Box) r at a) (many (Nat) hit))
  (let ((unique t0)) (slots-new))
  (let ((erased ys1) (many r1) (unique t1)) (slots-intern _ t0 (slot-of a)))
  (let-match many r1 (SlotAdded _ _ i n) (absurd (SlotExisting _ _ _ p) p))
  (let ((erased ys2) (many r2) (unique t2)) (slots-intern _ t1 (slot-of c)))
  (let ((erased pa)) (match erased r2 (((NthLast (Slot) ys2 i (slot-of a)) pa))
    ((SlotExisting _ _ _ _) (NthLastHere _ _ _ i n))
    ((SlotAdded _ _ _ _) (nth-last-suffix _ _ _ i _ (NthLastHere _ _ _ i n) (SuffixOfCons _ _ _ _ (SuffixOfRefl _ _))))))
  (let ((many f) (unique t3)) (slots-find _ t2 (slot-of b)))
  (let-match many f (SlotFound _ _ j q) ((SlotMissing _ _) (values a 0)))
  (let-match many (nat-cmp i j) (CEq _ _ _) (else (values a 0)))
  (let-match erased (nth-last-fn _ _ i _ _ pa q) (Refl _ _))
  (values b 1))

(def-fns _ $ (many run : -> (many (List (Pair (Bool) (Nat))) out))
  (let ((many a)) (MkBox 1))
  (let ((many b)) (MkBox 2))
  (let ((many c)) (MkBox 1))
  (let ((many d)) (MkBox 3))
  (let ((unique t0)) (slots-new))
  (let ((erased y1) (many r1) (unique t1)) (slots-intern _ t0 (slot-of a)))
  (let ((erased y2) (many r2) (unique t2)) (slots-intern _ t1 (slot-of b)))
  (let ((erased y3) (many r3) (unique t3)) (slots-intern _ t2 (slot-of a)))
  (let ((erased y4) (many r4) (unique t4)) (slots-intern _ t3 (slot-of c)))
  (let ((many f1) (unique t5)) (slots-find _ t4 (slot-of b)))
  (let ((many f2) (unique t6)) (slots-find _ t5 (slot-of d)))
  (let ((many len) (erased _) (unique t7)) (slots-length _ t6))
  (let ((many _) (many v1)) (recover a b a))
  (let ((many _) (many v2)) (recover a a b))
  (Cons _ (tag _ _ _ r1) $ Cons _ (tag _ _ _ r2) $ Cons _ (tag _ _ _ r3) $ Cons _ (tag _ _ _ r4)
    $ Cons _ (MkPair _ _ (BFalse) (found _ _ f1)) $ Cons _ (MkPair _ _ (BFalse) (found _ _ f2))
    $ Cons _ (MkPair _ _ (BFalse) len) $ Cons _ (MkPair _ _ (BFalse) v1) $ Cons _ (MkPair _ _ (BFalse) v2) $ Nil _))

run
