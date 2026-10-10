; error: argument 3, `a`, of `array-copy`: type mismatch: expected `(Array (Copy __?1) __?2)`, got `(Array (Nat) xs)`
(def-fns _ $ (many copy-test : (erased (List (Nat)) xs) (many (Array (Nat) xs) a) -> (unique (Array (Nat) xs) r))
  (array-copy _ _ a))
