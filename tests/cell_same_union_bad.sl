; error: `cell-same` takes cells of an `enum`, and `U` is a `union`
(def-adts $ (U : -> Type) union (many A : -> (U)) (many B : -> (U)))
(def-fns _ $ (many run : -> (many (Nat) out))
  (let ((unique ca)) (cell-alloc A))
  (let ((unique cb)) (cell-alloc B))
  (let ((many va)) (share (ca)))
  (let ((many vb)) (share (cb)))
  (let-match many va (A ua))
  (let-match many vb (B ub))
  (let-match many (slot-eq (slot-of ua) (slot-of ub)) (Some _ e) ((None _) 0))
  (let-match erased e (Refl _ _))
  (let-match many (cell-same ua ub) (EONonErased _ j) ((EOErased _) 0))
  (match erased j (((Nat) r))))
run
