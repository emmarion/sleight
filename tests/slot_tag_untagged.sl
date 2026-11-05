; expect: (Cons _ 1 $ Cons _ 1 $ Nil _)
(def-adts $ (Mixed : -> Type) union
  (many Plain : -> (Mixed))
  (many Holds : (many (Nat) n) -> (Mixed)))

(def-fns _ $ (many at plain : -> (many (Mixed) m at vacant-slot))
  (Plain))

(def-fns _ $ (many built : -> (many (Mixed) m at vacant-slot))
  (let ((unique c)) (cell-alloc Plain))
  (share (c)))

(def-fns _ $ (erased tagged : (erased (Mixed) m) -> (erased (Mixed) r at vacant-slot))
  (let-match erased m (Plain) ((Holds _) (Plain)))
  (slot-tag m)
  m)

(def-fns _ $ (many vacant : (many (Mixed) m) -> (many (Nat) r))
  (match many (slot-eq (slot-of m) vacant-slot) _ ((ESome _ _) 1) ((ENone _) 0)))

(def-fns _ $ (many via : (many (ValCtor -> (Mixed)) k) -> (many (Nat) r))
  (vacant (k)))

(let ((many _)) (plain))
(let ((many _)) (built))
(Cons _ (vacant $ Plain) $ Cons _ (via Plain) $ Nil _)
