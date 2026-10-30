; A hypermap of genus 0 has no Moebius path (planar_Jordan), and so has the Jordan property of hypgeom.sl, and each of
; its edge cycles has a dart fixed by n or f or not on the edge cycle of its node image (Euler_tree); and WalkupE at a
; dart fixed by n, f or e, or not on the edge cycle of its node image, keeps the genus (genus_WalkupE_eq).
(def-adts $ (PlanarJordan : -> Type)
  enum
  (many MkPlanarJordan : (erased (Level) L1)
      (erased (Fn L1 (erased (Nat) d x) (erased (List (Nat)) e n f p) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
          (erased (Moebius n f x p) mb) -> (erased (False) r)) moebius)
      (erased (Level) L2)
      (erased (Fn L2 (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
          -> (erased (Jordan n f) j)) jordan)
      (erased (Level) L3)
      (erased (Fn L3 (erased (Nat) d x) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
          (erased (Lt x d) lx) -> (erased (Leaf e n f x) r)) tree)
      (erased (Level) L4)
      (erased (Fn L4 (erased (Nat) d gen z) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f gen) p)
          (erased (Lt z d) lz) (erased (Keeps e n f z) kp)
          -> (erased (List (Nat)) e2 n2 f2) (erased (Skip n z n2) skn) (erased (Skip f z f2) skf) (erased (Hypermap d e2 n2 f2) h2)
          (erased (Genus d e2 n2 f2 gen) p2)) walkup)
      -> (PlanarJordan)))

(goal erased (PlanarJordan))
(qed (MkPlanarJordan (level-of planar-moebius) planar-moebius (level-of planar-jordan) planar-jordan (level-of euler-tree) euler-tree
  (level-of genus-walkup-eq) genus-walkup-eq))
