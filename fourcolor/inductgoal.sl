; FourColor from an Analysis, through CubicReduction. Load after reduce3.sl and induct.sl.
(def-adts $ (FourColorFrom : -> Type)
  enum
  (many MkFourColorFrom : (erased (Level) F) (erased (Fn F (erased (Analysis) an) -> (erased (FourColor) r)) fc) -> (FourColorFrom)))

(def-fns _ $ (erased four-color-from : (erased (Analysis) an) -> (erased (FourColor) r))
  (let ((erased D) (erased col)) (four-color-induct an))
  (def-fns _ $ (erased cubic-colour : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) pl)
      (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pe) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cn) ->
      (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
    (col d e n f (MkPbpp d e n f h pl b pe (cubic-precubic d n cn))))
  (cubic-reduction (level-of cubic-colour) cubic-colour))

(goal erased (FourColorFrom))
(qed (MkFourColorFrom (level-of four-color-from) four-color-from))
