; The four colour theorem for drawings, from the four colour theorem for plane maps.
(def-adts $ (Reduction : -> Type)
  enum
  (many MkReduction : (erased (Level) F)
      (erased (Fn F (erased (Level) L)
          (erased (Fn L (erased (List (Nat)) e nd) (erased (PlaneMap e nd) m) -> (erased (List (Nat)) ks) (erased (Colored ks e nd ks) c)) colour)
          -> (erased (FourColor) r)) reduce)
      -> (Reduction)))

(def-fns _ $ (erased reduction : (erased (Level) L)
    (erased (Fn L (erased (List (Nat)) e nd) (erased (PlaneMap e nd) m) -> (erased (List (Nat)) ks) (erased (Colored ks e nd ks) c)) colour)
    -> (erased (FourColor) r))
  (part-a (level-of drawing-plan) drawing-plan L colour))

(goal erased (Reduction))
(qed (MkReduction (level-of reduction) reduction))
