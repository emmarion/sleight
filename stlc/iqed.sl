(def-fns _ $ (erased bounded-reductions : (erased (List (Ty)) g) (erased (Ty) a) (erased (Term g a) t) -> (erased (Nat) n) (erased (Bounded g a t n) b))
  (let ((erased e) (erased er)) (erase-ex g a t))
  (let ((erased d)) (typed-normalizes g e a (erase-typed g a t e er)))
  (let ((erased n) (erased h)) (height-ex e d))
  (def-fns _ $ (erased bound : (erased (Nat) k) (erased (Term g a) u) (erased (Reduction g a k t u) r) -> (erased (NatLe k n) le))
    (reduction-bound g a k t u r e er d n h))
  (values n (MkBounded g a t n (level-of bound) bound)))

(qed (MkBoundedReductions (level-of bounded-reductions) bounded-reductions))
