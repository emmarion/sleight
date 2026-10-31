; The four colour theorem for drawings, from the four colour theorem for plane maps.

(def-fns _ $ (erased reduction : (erased (Level) L)
    (erased (Fn L (erased (List (Nat)) e nd) (erased (PlaneMap e nd) m) -> (erased (List (Nat)) ks) (erased (Colored ks e nd ks) c)) colour)
    -> (erased (FourColor) r))
  (part-a (level-of drawing-plan) drawing-plan L colour))
