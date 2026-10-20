; expect: (Cons _ 1 $ Cons _ 1 $ Cons _ 1 $ Nil _)
(def-adts $ (C : -> Type) enum (many Ck : (many (Slot) f) -> (C)))
(def-fns _ $ (many vacant : (unique (Cell Ck vacant-slot) u) -> (many (Nat) r))
  (let ((many t)) (cell-match unique u (((Slot) r)) (Ck s) s))
  (match many (slot-eq t vacant-slot) _ ((Some _ _) 1) ((None _) 0)))
(let ((many at-compile)) (vacant (cell-alloc (Ck _))))
(def-fns _ $ (many main : -> (many (List (Nat)) r))
  (Cons _ at-compile $ Cons _ (vacant (cell-alloc (Ck _))) $ Cons _ (vacant (cell-alloc Ck)) $ Nil _))
main
