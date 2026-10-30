; A four-colourable hypermap is bridgeless; a four-colouring is one of the map with edge and face inverted (so the dual's
; four-colourings are the map's colourings with node in place of face); one of the mirror is one of the map; whether a
; map has a four-colouring is decided.
(def-adts $ (HypColorings : -> Type)
  enum
  (many MkHypColorings : (erased (Level) L1)
      (erased (Fn L1 (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (FourColoring e f ks) c)
          -> (erased (Bridgeless d e n f) r)) bridgeless)
      (erased (Level) L2)
      (erased (Fn L2 (erased (Nat) d) (erased (List (Nat)) e f ei fi ks) (erased (Perm d e ei) pe) (erased (Perm d f fi) pf)
          (erased (FourColoring e f ks) c) -> (erased (FourColoring ei fi ks) r)) inv)
      (erased (Level) L3)
      (erased (Fn L3 (erased (Nat) d) (erased (List (Nat)) e n f fn fi ks) (erased (Hypermap d e n f) h) (erased (Respects f n fn) rfn)
          (erased (Perm d f fi) pf) (erased (FourColoring fn fi ks) c) -> (erased (FourColoring e f ks) r)) mirror)
      (erased (Level) L4)
      (erased (Fn L4 (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) -> (erased (ColorDec e f) r)) decide)
      -> (HypColorings)))

(goal erased (HypColorings))
(qed (MkHypColorings (level-of colorable-bridgeless) colorable-bridgeless (level-of coloring-inv) coloring-inv
  (level-of coloring-mirror) coloring-mirror (level-of decide-colorable) decide-colorable))
