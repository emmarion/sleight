; Kempe_map of kempe.v: for a ring r of a planar map whose edge permutation is an involution and which is cubic off r,
; the ring traces are closed under colour permutations, and each matches a chromogram w with a certificate that every
; trace matching w is a ring trace too (Kempe_closed (ring_trace r)).
(def-adts $ (KempeMap : -> Type)
  enum
  (many MkKempeMap : (erased (Level) L1)
      (erased (Fn L1 (erased (List (Nat)) e f r) (erased (List (Col)) et et2) (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermT g et et2) pt)
          (erased (RingTrace e f r et) rt) -> (erased (RingTrace e f r et2) r2)) perm)
      (erased (Level) L2)
      (erased (Fn L2 (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (List (Col)) et) (erased (Hypermap d e n f) h)
          (erased (Genus d e n f (Zero)) g) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (QuasiCubic d n r) qc) (erased (NCyc n r) nc)
          (erased (Distinct r) ds) (erased (RingTrace e f r et) rt) -> (erased (List (Gsym)) w) (erased (MatchG (BS0) et w) m)
          (erased (KRing d e n f r w) kr)) gram)
      (erased (Level) L3)
      (erased (Fn L3 (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (List (Gsym)) w) (erased (List (Col)) et) (erased (KRing d e n f r w) kr)
          (erased (MatchG (BS0) et w) m) -> (erased (RingTrace e f r et) rt)) sound)
      -> (KempeMap)))

(goal erased (KempeMap))
(qed (MkKempeMap (level-of ring-trace-perm) ring-trace-perm (level-of kempe-map) kempe-map (level-of kempe-sound) kempe-sound))
