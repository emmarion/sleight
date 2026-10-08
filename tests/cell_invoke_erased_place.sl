; expect: 0
; An erased invocation that stores is at its cell, as the `unique` form is (section 14).
(def-fns _ $ (many g : (many (Cell Cons vacant-slot vacant-slot) a) (erased (List (Nat)) v at a) -> (many (Nat) r)) 0)
(def-fns _ $ (many f : (many (Nat) a) (many (List (Nat)) t) -> (many (Nat) r))
  (let ((unique c)) (cell-alloc Cons))
  (let ((erased v)) (c _ a t))
  (g (share c) v))
0
