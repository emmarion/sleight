(def-fns _ $ (erased four-color-from : (erased (Analysis) an) -> (erased (FourColor) r))
  (let ((erased _) (erased col)) (four-color-induct an))
  (def-fns _ $ (erased cubic-colour : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) pl)
      (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pe) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cn) ->
      (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
    (col d e n f (MkPbpp d e n f h pl b pe (cubic-precubic d n cn))))
  (cubic-reduction (level-of cubic-colour) cubic-colour))
