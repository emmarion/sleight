; Shared erased arithmetic. Numerals in the specification are opaque.
(unary 0)
(unary 1)
(unary 2)

(def-fns _ $ (erased ed-add-mono : (erased (Nat) k a b ka kb)
    (subterm erased (Add k a ka) pa) (erased (Add k b kb) pb) (erased (Lt a b) ab) ->
    (erased (Lt ka kb) q))
  (let-match erased pa (AddSucc k1 _ ka1 pa1)
    ((AddZero _) (let-match erased pb (AddZero _)) ab))
  (let-match erased pb (AddSucc _ _ kb1 pb1))
  (LtS ka1 kb1 (ed-add-mono k1 a b ka1 kb1 pa1 pb1 ab)))

(def-fns _ $ (erased ed-add-assoc : (erased (Nat) a b c ab bc abc)
    (subterm erased (Add a b ab) p) (erased (Add b c bc) q) (erased (Add ab c abc) r) ->
    (erased (Add a bc abc) s))
  (let-match erased p (AddSucc a1 _ ab1 p1)
    ((AddZero _) (let-match erased (add-fn b c bc abc q r) (Refl _ _)) (AddZero bc)))
  (let-match erased r (AddSucc _ _ abc1 r1))
  (AddSucc a1 bc abc1 (ed-add-assoc a1 b c ab1 bc abc1 p1 q r1)))

(def-fns _ $ (erased ed-double-add : (erased (Nat) a b) (subterm erased (Double a b) d) -> (erased (Add a a b) r))
  (let-match erased d (DS a1 b1 d1) ((D0) (AddZero 0)))
  (AddSucc a1 (Succ a1) (Succ b1) (add-succ-right a1 a1 b1 (ed-double-add a1 b1 d1))))
