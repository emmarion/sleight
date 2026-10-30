; Counting darts by orbits, and cubic_Euler: a connected map with two darts on each edge and three at each node has
; genus 0 exactly when 6 times its number of faces is the number of darts plus 12.
(def-adts $ (CubicEuler : -> Type)
  enum
  (many MkCubicEuler : (erased (Level) L1)
      (erased (Fn L1 (erased (Nat) d k c) (erased (List (Nat)) p q) (erased (Perm d p q) pm) (erased (Orbits d p k) ob)
          (erased (AllOrder d p c) ao) -> (erased (Mul k c d) r)) count)
      (erased (Level) L2)
      (erased (Fn L2 (erased (Nat) d kf) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
          (erased (AllOrder d e (Succ (Succ (Zero)))) plain) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cubic) (erased (Connected d e n f) cc)
          (erased (Genus d e n f (Zero)) p) (erased (Orbits d f kf) of)
          -> (erased (Nat) s) (erased (Mul kf (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) s) ma)
          (erased (Add d (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))))) s) ds)) to)
      (erased (Level) L3)
      (erased (Fn L3 (erased (Nat) d gen kf s) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
          (erased (AllOrder d e (Succ (Succ (Zero)))) plain) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cubic) (erased (Connected d e n f) cc)
          (erased (Genus d e n f gen) p) (erased (Orbits d f kf) of) (erased (Mul kf (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) s) ma)
          (erased (Add d (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))))) s) ds)
          -> (erased (Eq (Nat) gen (Zero)) r)) from)
      -> (CubicEuler)))

(goal erased (CubicEuler))
(qed (MkCubicEuler (level-of orbit-count) orbit-count (level-of cubic-planar) cubic-planar (level-of planar-cubic) planar-cubic))
