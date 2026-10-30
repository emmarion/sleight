; A hypermap of genus 0 has no Moebius path (planar_Jordan), and so has the Jordan property of hypgeom.sl.
(def-adts $ (PlanarJordan : -> Type)
  enum
  (many MkPlanarJordan : (erased (Level) L1)
      (erased (Fn L1 (erased (Nat) d x) (erased (List (Nat)) e n f p) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
          (erased (Moebius n f x p) mb) -> (erased (False) r)) moebius)
      (erased (Level) L2)
      (erased (Fn L2 (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
          -> (erased (Jordan n f) j)) jordan)
      -> (PlanarJordan)))

(goal erased (PlanarJordan))
(qed (MkPlanarJordan (level-of planar-moebius) planar-moebius (level-of planar-jordan) planar-jordan))
