; error: tests/zero_size_erased_bad.sl:3:11: error: a `match` in an erased position is written `erased`
(def-fns _ $ (erased ghost : (many (List (Nat)) xs) -> (erased (Nat) r))
  (let () (match many xs () ((Nil a) (values)) ((Cons a h t) (values))))
  (Zero))
(Zero)
