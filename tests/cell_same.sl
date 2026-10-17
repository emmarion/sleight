; expect: 7
(def-fns _ $ (many demo : (many (List (Nat)) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ h1 _ u1) ((Nil _) 0))
  (let-match many xs (Cons _ h2 _ u2))
  (let-match many (cell-same u1 u2) (EONonErased _ e) ((EOErased _) h1))
  (let-match erased e (JMRefl _ _))
  (let ((erased (Eq (Slot) (slot-of h1) (slot-of h2)) _)) (Refl (Slot) (slot-of h1)))
  h2)
(demo (Cons _ 7 (Nil _)))
