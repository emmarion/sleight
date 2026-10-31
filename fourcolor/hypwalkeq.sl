; The equality case of the Walkup genus (genus_WalkupE_eq of walkup.v), for the WalkupE that keeps z as a dart fixed by
; all three permutations: when z is fixed by n, f or e, or n z is not on the edge cycle of z, the genus is kept.

(def-fns _ $ (erased shut-cat : (erased (List (Nat)) s) (erased (List (Bond)) g h gh) (subterm erased (Cat g h gh) c) (erased (Shut s g) sg)
    (erased (Shut s h) sh) -> (erased (Shut s gh) r))
  (let-match erased c (CatCons g1 _ gh1 b c1) ((CatNil _) sh))
  (match erased sg _
    ((ShutIn _ _ x y px py rest) (ShutIn s gh1 x y px py (shut-cat s g1 h gh1 c1 rest sh)))
    ((ShutOut _ _ x y px py rest) (ShutOut s gh1 x y px py (shut-cat s g1 h gh1 c1 rest sh)))))
