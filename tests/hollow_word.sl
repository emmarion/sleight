; expect: (Cons _ 1 $ Cons _ 1 $ Nil _)
(def-adts $ (Tok : -> Type) enum
  (many MkTok : (erased (Nat) n) -> (Tok)))

(def-fns _ $ (many vacant : (many (Tok) t) -> (many (Nat) r))
  (match many (slot-eq (slot-of t) vacant-slot) _ ((Some _ _) 1) ((None _) 0)))

(def-fns _ $ (many via : (many (ValCtor (erased (Nat) n) -> (Tok)) k) -> (many (Nat) r))
  (vacant (k 5)))

(def-fns _ $ (many rewritten : (erased (Nat) n) -> (many (Nat) r))
  (let ((unique c)) (cell-alloc MkTok))
  (let ((unique c2)) (cell-write unique c (MkTok)))
  (let ((unique c3)) (cell-write many (share c2) (MkTok)))
  (vacant (share (c3 n))))

(Cons _ (via MkTok) $ Cons _ (rewritten 0) $ Nil _)
