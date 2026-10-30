; The four colour theorem for drawings, from the four colour theorem for plain cubic hypermaps.
(def-adts $ (CubicReduction : -> Type)
  enum
  (many MkCubicReduction : (erased (Level) F)
      (erased (Fn F (erased (Level) L)
          (erased (Fn L (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) pl)
              (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pe) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cn) ->
              (erased (List (Nat)) ks) (erased (FourColoring e f ks) c)) colour)
          -> (erased (FourColor) r)) reduce)
      -> (CubicReduction)))

(def-fns _ $ (erased cubic-reduction : (erased (Level) L)
    (erased (Fn L (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) pl)
        (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pe) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cn) ->
        (erased (List (Nat)) ks) (erased (FourColoring e f ks) c)) colour)
    -> (erased (FourColor) r))
  (let ((erased L2) (erased colour2)) (cube-reduction L colour))
  (hyp-reduction L2 colour2))
