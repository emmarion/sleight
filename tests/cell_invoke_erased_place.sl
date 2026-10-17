; expect: 0
; An erased invocation that stores is at its cell, as the `unique` form is (section 14).
(def-fns _ $ (many g : (many (Cell Cons vacant-slot vacant-slot) _a) (erased (List (Nat)) _v at _a) -> (many (Nat) r)) 0)
(def-fns _ $ (many f : (many (Nat) _a) (many (List (Nat)) _t) -> (many (Nat) r))
  (let ((unique c)) (cell-alloc Cons))
  (let ((erased v)) (c _ _a _t))
  (g (share c) v))
0
