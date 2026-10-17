(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))

(def-fns _ $ (many found : (erased Type A) (erased (List (SlotItem A)) xs) (erased (Slot) s) (erased Type U) (erased U u)
    (many (SlotFind A xs s U u) r) -> (many (Nat) out))
  (match many r (((Nat) k)) ((SlotFound _ _ _ _ _ i _) i) ((SlotMissing _ _ _) 99)))

(def-fns _ $ (many same : (many (Slot) a) (many (Slot) b) -> (many (Bool) r))
  (match many (slot-eq a b) _ ((Some _ _) (BTrue)) ((None _) (BFalse))))

;! suppress warn MkSlots
;! suppress warn Slots
(def-fns _ $ (many run : -> (many (List (Nat)) out) (many (List (Bool)) heads))
  (let ((many a)) (MkBox 1))
  (let ((many b)) (MkBox 2))
  (let ((unique t0)) (MkSlots _ (Cons _ (MkSlotItem _ _ _ (place-at-many _ a)) $ Cons _ (MkSlotItem _ _ _ (place-at-many _ a)) $ Nil _)))
  (let ((erased _) (many _) (many f1) (unique t1)) (slots-find _ _ t0 (slot-of a)))
  (let ((erased _) (many r) (unique t2)) (slots-intern _ _ t1 _ _ (place-at-many _ a)))
  (let ((many i)) (match many r (((Nat) k)) ((SlotExisting _ _ _ _ _ i _) i) ((SlotAdded _ _ _ _ _ _ _) 99)))
  (let ((erased _) (many _) (unique t3)) (slots-intern _ _ t2 _ _ (place-at-many _ b)))
  (let ((many n) (erased _) (unique t4)) (slots-length _ _ t3))
  (let-match unique t4 (MkSlots _ ls))
  (let-match many ls (Cons _ h1 rest) ((Nil _) (values (Nil _) (Nil _))))
  (let-match many rest (Cons _ h2 _) ((Nil _) (values (Nil _) (Nil _))))
  (values (Cons _ (found _ _ _ _ _ f1) $ Cons _ i $ Cons _ n $ Nil _)
    (Cons _ (same (slot-of h1) (slot-of b)) $ Cons _ (same (slot-of h2) (slot-of a)) $ Nil _)))
;! restore warn Slots
;! restore warn MkSlots

(let ((many nums) (many heads)) (run))
(MkPair _ _ nums heads)
; expect: (MkPair _ _ (Cons _ 1 $ Cons _ 1 $ Cons _ 3 $ Nil _) $ Cons _ (BTrue) $ Cons _ (BTrue) $ Nil _)
