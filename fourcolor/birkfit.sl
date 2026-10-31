(def-fns _ $ (erased bneed-smaller : (erased (Nat) d dd h m) (erased (List (Nat)) ed nd fd bd) (erased (List (Ctree)) ts) (erased (List (Mp)) ms)
    (subterm erased (BNeed d dd h m ed nd fd bd ts ms) bn) -> (erased (Smaller d ms) r))
  (let-match erased bn (BNCons _ _ _ _ d2 _ _ _ _ e2 n2 f2 _ _ ts1 ms1 _ h2 g2 b2 pl2 pc2 lt2 _ rest) ((BNNil _ _ _ _ _ _ _ _) (SmallerNil d)))
  (SmallerCons d d2 e2 n2 f2 ms1 (MkPbpp d2 e2 n2 f2 h2 g2 b2 pl2 pc2) lt2 (bneed-smaller d dd h m ed nd fd bd ts1 ms1 rest)))
