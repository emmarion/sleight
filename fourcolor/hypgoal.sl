; Every plane map is a planar bridgeless hypermap, and its four-colourings are the Colored colourings of map.sl.
(def-adts $ (PlaneHypermaps : -> Type)
  enum
  (many MkPlaneHypermaps : (erased (Level) L)
      (erased (Fn L (erased (List (Nat)) e nd) (erased (PlaneMap e nd) m) ->
          (erased (Nat) d) (erased (List (Nat)) n) (erased (Hypermap d e n nd) h) (erased (Genus d e n nd (Zero)) pl)
          (erased (Bridgeless d e n nd) b)) thm)
      (erased (Level) L2)
      (erased (Fn L2 (erased (List (Nat)) ks e nd) (erased (Colored ks e nd ks) c) -> (erased (FourColoring e nd ks) r)) to)
      (erased (Level) L3)
      (erased (Fn L3 (erased (List (Nat)) ks e nd) (erased (FourColoring e nd ks) c) -> (erased (Colored ks e nd ks) r)) from)
      -> (PlaneHypermaps)))

(goal erased (PlaneHypermaps))
(qed (MkPlaneHypermaps (level-of plane-hypermap) plane-hypermap (level-of colored-coloring) colored-coloring
  (level-of coloring-colored) coloring-colored))
