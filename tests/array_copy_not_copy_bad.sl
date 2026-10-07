; error: argument 3, `a`, of `array-copy`: type mismatch: expected `(Array (Copy _?1) _?2)`, got `(Array (Nat) xs)`
(def-fns _ $ (many copy-test : (erased (List (Nat)) xs) (many (Array (Nat) xs) a) -> (unique (Array (Nat) xs) r))
  (array-copy _ _ a))
